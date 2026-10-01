'use strict';
/*
 * core.js —— 光阑换位置换群审计核心（无 DOM 依赖，可在 Window / Worker / Node 下复用）
 *
 * 约定
 *   端口集合 Ω = {0,...,n-1}，按端口标识排序；稳定基点顺序为 [0,1,...,n-1]。
 *   置换用长度 n 的数组表示，p[x] = x 的像。
 *   乘法约定：(a*b)[x] = b[a[x]]，即先执行 a 再执行 b，与操作依次执行的直觉一致。
 *   生成元词（因子词）为整数编号序列：k+1 表示第 k 个生成元，-(k+1) 表示其逆元；
 *   词中因子从左到右依次执行。
 *
 * 成员判定：确定性 Schreier–Sims 稳定子链
 *   G^(0) ≥ G^(1) ≥ ... ≥ G^(n) = {id}，G^(i) 为前 i 个基点的逐点稳定子。
 *   每层保存强生成元与基点轨道的横截代表；成员结论由横截代表逐层剥离复算，
 *   并对所得因子词做独立乘回校验。不枚举操作串、不使用随机搜索、不做有限深度回放。
 */

// ---------------- 基础置换运算 ----------------

function identity(n) {
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = i;
  return r;
}

function isPermutation(p, n) {
  if (!Array.isArray(p) || p.length !== n) return false;
  const seen = new Uint8Array(n);
  for (let i = 0; i < n; i++) {
    const v = p[i];
    if (!Number.isInteger(v) || v < 0 || v >= n || seen[v]) return false;
    seen[v] = 1;
  }
  return true;
}

function compose(a, b, n) {
  // a*b：先执行 a，再执行 b
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = b[a[i]];
  return r;
}

function invert(p, n) {
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[p[i]] = i;
  return r;
}

function equalPerm(a, b) {
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}

function isIdentity(p) {
  for (let i = 0; i < p.length; i++) if (p[i] !== i) return false;
  return true;
}

// ---------------- 因子词运算 ----------------

function concatWord(a, b) {
  const r = new Array(a.length + b.length);
  for (let i = 0; i < a.length; i++) r[i] = a[i];
  for (let i = 0; i < b.length; i++) r[a.length + i] = b[i];
  return r;
}

function invertWord(w) {
  const r = new Array(w.length);
  for (let i = 0; i < w.length; i++) r[w.length - 1 - i] = -w[i];
  return r;
}

// 按因子词从恒等开始依次乘回，得到词所表达的置换
function multiplyWord(word, generators, n) {
  let p = identity(n);
  for (const tok of word) {
    const g = generators[Math.abs(tok) - 1];
    p = compose(p, tok > 0 ? g : invert(g, n), n);
  }
  return p;
}

// ---------------- 输入解析与一次性全量校验 ----------------

function parsePortList(text) {
  const errors = [];
  const names = String(text == null ? '' : text)
    .split(/[\s,，;；]+/)
    .map((s) => s.trim())
    .filter((s) => s.length > 0);
  if (names.length < 2) errors.push('端口数量不足：至少需要 2 个稳定端口');
  if (names.length > 12) errors.push('端口数量超限：最多允许 12 个稳定端口');
  const seen = new Set();
  const dup = new Set();
  for (const nm of names) {
    if (seen.has(nm) && !dup.has(nm)) {
      dup.add(nm);
      errors.push('端口标识重复：“' + nm + '”');
    }
    seen.add(nm);
  }
  return { names: names.filter((nm, i) => names.indexOf(nm) === i), errors };
}

/*
 * 解析一段置换文本。支持：
 *   循环记号  (A B C)(D E)      —— A→B→C→A，D↔E；固定点写 (A)
 *   显式映射  A->B, B->C, C->A  —— 亦接受 → / => / : 作为分隔符
 *   无括号循环 A B C             —— 整行视为一个循环
 * 必须恰好覆盖全部端口各一次；未知端口、重复出现、缺失端口全部收集为错误。
 */
function parsePermText(text, names, indexByName) {
  const n = names.length;
  const raw = String(text == null ? '' : text).trim();
  const errors = [];
  if (!raw) return { perm: null, errors: ['置换内容为空'] };

  const normalized = raw.replace(/→/g, '->').replace(/=>/g, '->');
  const pairs = []; // [fromIdx, toIdx]
  let explicitMode = false;
  const unknown = (x) => errors.push('引用了不存在的端口：“' + x + '”');

  const addCycle = (tokens, label) => {
    const idxs = [];
    for (const tk of tokens) {
      if (!tk) continue;
      if (Object.prototype.hasOwnProperty.call(indexByName, tk)) {
        idxs.push(indexByName[tk]);
      } else {
        unknown(tk);
      }
    }
    if (idxs.length === 0) return;
    for (let i = 0; i < idxs.length; i++) {
      pairs.push([idxs[i], idxs[(i + 1) % idxs.length]]);
    }
  };

  if (normalized.includes('->') || normalized.includes(':')) {
    // 显式映射模式：必须显式给出每个端口的去向
    explicitMode = true;
    const chunks = normalized.split(/[,，;；\n\r]+/);
    for (const chunk of chunks) {
      const c = chunk.trim();
      if (!c) continue;
      const sep = c.includes('->') ? '->' : ':';
      const at = c.indexOf(sep);
      const lhs = c.slice(0, at).trim();
      const rhs = c.slice(at + sep.length).trim();
      if (!lhs || !rhs) {
        errors.push('无法解析的映射条目：“' + c + '”（应为 端口->端口）');
        continue;
      }
      const li = Object.prototype.hasOwnProperty.call(indexByName, lhs)
        ? indexByName[lhs]
        : -1;
      const ri = Object.prototype.hasOwnProperty.call(indexByName, rhs)
        ? indexByName[rhs]
        : -1;
      if (li === -1) unknown(lhs);
      if (ri === -1) unknown(rhs);
      if (li !== -1 && ri !== -1) pairs.push([li, ri]);
    }
  } else if (normalized.includes('(') || normalized.includes('（')) {
    // 循环记号模式
    const groups = normalized
      .replace(/[（]/g, '(')
      .replace(/[）]/g, ')')
      .match(/\(([^)]*)\)/g);
    if (!groups) {
      errors.push('无法解析的循环记号：“' + raw + '”');
    } else {
      const covered = groups.join('');
      const rest = normalized.replace(/\(([^)]*)\)/g, '').replace(/[()\s]/g, '');
      if (rest) errors.push('循环记号外存在无法识别的内容：“' + rest + '”');
      for (const g of groups) {
        const tokens = g
          .slice(1, -1)
          .split(/[\s,，]+/)
          .map((s) => s.trim())
          .filter(Boolean);
        addCycle(tokens);
      }
    }
  } else {
    // 整行视为一个空格/逗号分隔的循环
    const tokens = normalized
      .split(/[\s,，]+/)
      .map((s) => s.trim())
      .filter(Boolean);
    addCycle(tokens);
  }

  if (errors.length) return { perm: null, errors };

  // 组装并校验双射性与完整性（缺失端口）
  const perm = new Array(n).fill(-1);
  const lhsSeen = new Uint8Array(n);
  const rhsSeen = new Uint8Array(n);
  for (const [l, r] of pairs) {
    if (lhsSeen[l]) errors.push('端口 “' + names[l] + '” 的映射被重复定义（非双射）');
    if (rhsSeen[r]) errors.push('端口 “' + names[r] + '” 被多个源端口映射（非双射）');
    lhsSeen[l] = 1;
    rhsSeen[r] = 1;
    perm[l] = r;
  }
  for (let i = 0; i < n; i++) {
    if (!lhsSeen[i]) {
      if (explicitMode) {
        errors.push('缺失端口：未给出 “' + names[i] + '” 的去向');
      } else {
        // 循环记号：未出现的端口为固定点
        perm[i] = i;
        lhsSeen[i] = 1;
        rhsSeen[i] = 1;
      }
    }
  }
  if (errors.length) return { perm: null, errors };
  if (!isPermutation(perm, n)) {
    errors.push('映射不是端口集合上的双射');
    return { perm: null, errors };
  }
  return { perm, errors: [] };
}

/*
 * 解析校准编组（可选）。
 * 接受：
 *   - 数组：每项为 "A B C" 字符串或端口名数组；
 *   - 字符串：组间以 | / ; / ；/ 换行分隔，组内以空白/逗号分隔，
 *     例如 "A B | C D"。
 * 未提供或全部为空 => 未启用编组（enabled:false）。
 * 启用时必须构成端口集合的一个划分：未知端口、重复端口、空组全部收集为错误。
 */
function parseCalibrationGroups(raw, names, indexByName) {
  const items = [];
  if (Array.isArray(raw)) {
    for (const item of raw) {
      if (Array.isArray(item)) items.push(item.join(' '));
      else items.push(String(item == null ? '' : item));
    }
  } else if (raw != null && String(raw).trim() !== '') {
    items.push(...String(raw).split(/[|;；\n\r]+/));
  }
  const texts = items.map((s) => s.trim()).filter((s) => s.length > 0);
  if (texts.length === 0) return { enabled: false, groups: [], errors: [] };

  const errors = [];
  const groups = [];
  const used = new Uint8Array(names.length);
  texts.forEach((text, gi) => {
    const members = text
      .split(/[\s,，]+/)
      .map((s) => s.trim())
      .filter(Boolean);
    const idxs = [];
    if (members.length === 0) {
      errors.push({ scope: 'groups', index: gi, message: '校准组 ' + (gi + 1) + ' 为空' });
      return;
    }
    for (const m of members) {
      if (!Object.prototype.hasOwnProperty.call(indexByName, m)) {
        errors.push({
          scope: 'groups',
          index: gi,
          message: '校准组 ' + (gi + 1) + ' 引用了不存在的端口：“' + m + '”',
        });
        continue;
      }
      const k = indexByName[m];
      if (used[k]) {
        errors.push({
          scope: 'groups',
          index: gi,
          message: '端口 “' + m + '” 同时属于多个校准组（编组必须互斥且穷尽全部端口）',
        });
      } else {
        used[k] = 1;
      }
      idxs.push(k);
    }
    groups.push(idxs);
  });
  for (let i = 0; i < names.length; i++) {
    if (!used[i]) {
      errors.push({
        scope: 'groups',
        message: '端口 “' + names[i] + '” 不属于任何校准组（编组必须穷尽全部端口）',
      });
    }
  }
  if (errors.length) return { enabled: true, groups: [], errors };
  return { enabled: true, groups, errors: [] };
}

/*
 * 全量校验：端口、操作（具名置换）、目标、可选校准编组。
 * 所有错误一次性返回（重复操作名、缺失端口、非双射映射、非法目标、
 * 编组不构成划分等），调用方据此立即撤销旧结论。
 */
function validateInput(input) {
  const errors = [];
  const { names, errors: portErrors } = parsePortList(input.ports || '');
  for (const e of portErrors) errors.push({ scope: 'ports', message: e });

  const operations = Array.isArray(input.operations) ? input.operations : [];
  if (operations.length === 0) {
    errors.push({ scope: 'operations', message: '至少需要 1 个具名置换操作' });
  }
  if (operations.length > 8) {
    errors.push({ scope: 'operations', message: '具名置换操作数量超限：最多 8 个' });
  }

  const nameSet = new Set();
  const opNameSeen = new Set();
  for (const nm of names) nameSet.add(nm);
  const indexByName = {};
  names.forEach((nm, i) => {
    indexByName[nm] = i;
  });

  const ops = [];
  operations.forEach((op, idx) => {
    const label = '操作' + (idx + 1);
    const opName = String(op.name == null ? '' : op.name).trim();
    if (!opName) {
      errors.push({ scope: 'operation', index: idx, message: label + '缺少名称' });
    } else if (opNameSeen.has(opName)) {
      errors.push({
        scope: 'operation',
        index: idx,
        message: '操作名称重复：“' + opName + '”',
      });
    }
    opNameSeen.add(opName);
    if (names.length >= 2) {
      const { perm, errors: pErr } = parsePermText(op.mapping, names, indexByName);
      for (const e of pErr) {
        errors.push({
          scope: 'operation',
          index: idx,
          message: (opName ? '操作“' + opName + '”：' : label + '：') + e,
        });
      }
      ops.push({ name: opName, perm });
    } else {
      ops.push({ name: opName, perm: null });
    }
  });

  let target = null;
  const targetText = String(input.target == null ? '' : input.target).trim();
  if (!targetText) {
    errors.push({ scope: 'target', message: '非法目标：目标置换为空' });
  } else if (names.length >= 2) {
    const { perm, errors: tErr } = parsePermText(input.target, names, indexByName);
    for (const e of tErr) {
      errors.push({ scope: 'target', message: '非法目标：' + e });
    }
    target = perm;
  }

  // 可选校准编组；未提供时校准容差不启用，原有结论与因子链保持不变
  let groupsEnabled = false;
  let groups = [];
  if (names.length >= 2) {
    const g = parseCalibrationGroups(input.groups, names, indexByName);
    if (g.enabled) {
      groupsEnabled = true;
      for (const e of g.errors) errors.push(e);
      groups = g.groups;
    }
  }

  if (errors.length) {
    return { ok: false, errors, names: [], operations: [], target: null,
      groupsEnabled: false, groups: [] };
  }

  // 生成元按操作名排序，保证构造过程完全确定（端口标识亦已排序）
  const order = ops.map((_, i) => i).sort((a, b) =>
    ops[a].name < ops[b].name ? -1 : ops[a].name > ops[b].name ? 1 : a - b
  );
  const sortedOps = order.map((i) => ops[i]);
  return {
    ok: true,
    errors: [],
    names,
    operations: sortedOps,
    target,
    groupsEnabled,
    groups,
  };
}

// ---------------- 确定性 Schreier–Sims 稳定子链 ----------------

function createLevels(n) {
  const levels = [];
  for (let i = 0; i < n; i++) {
    const beta = new Array(n).fill(null);
    const word = new Array(n).fill(null);
    const inv = new Array(n).fill(null);
    beta[i] = identity(n);
    word[i] = [];
    inv[i] = identity(n);
    levels.push({ base: i, S: [], genWord: [], Skeys: new Set(), beta, word, inv });
  }
  return levels;
}

// 剥离（sift）：用各层横截代表逐层消去基点像。
// 返回 null 表示完全剥离（属于当前链）；否则返回残差及其首个无法归约的层级。
function sift(levels, n, p, word, startLevel) {
  let cur = p;
  let curWord = word.slice();
  for (let i = startLevel; i < n; i++) {
    const L = levels[i];
    const x = cur[i];
    if (x === i) continue; // 已固定该基点
    const t = L.beta[x];
    if (t == null) return { perm: cur, word: curWord, level: i };
    // 消去基点像：先执行 cur（基点 -> x），再执行 t^{-1}（x -> 基点）
    // 在本文件“先 a 后 b、(a*b)[i]=b[a[i]]”的约定下即 cur * t^{-1}
    cur = compose(cur, invert(t, n), n);
    curWord = concatWord(curWord, invertWord(L.word[x]));
  }
  return isIdentity(cur) ? null : { perm: cur, word: curWord, level: n };
}

/*
 * 确定性 Schreier–Sims 稳定子链。
 * isAllowed(level, point) 给定时构造“受限稳定子链”：第 level 层只发布满足
 * isAllowed(level, x) 的轨道点（横截代表），Schreier 闭包仅在两端点均已发布
 * 时生成残差——这是与（保持某条等价关系/分块结构的）子群求交的标准
 * Schreier–Sims 构造（集合稳定子链）。省略时退化为普通链，行为与原先一致。
 */
// 受限剥离：与 sift 相同，但仅使用满足 allowed 的已发布横截代表。
// 像点不在该层已发布轨道内即在该层阻塞（用于集合稳定子链构造）。
function siftRestricted(levels, n, p, word, startLevel, allowed) {
  let cur = p;
  let curWord = word.slice();
  for (let i = startLevel; i < n; i++) {
    const L = levels[i];
    const x = cur[i];
    if (x === i) continue; // 已固定该基点
    const t = L.beta[x];
    if (t == null || !allowed(i, x)) {
      return { perm: cur, word: curWord, level: i };
    }
    cur = compose(cur, invert(t, n), n);
    curWord = concatWord(curWord, invertWord(L.word[x]));
  }
  return isIdentity(cur) ? null : { perm: cur, word: curWord, level: n };
}

function buildChain(n, generators, genWords, isAllowed) {
  const allowed = typeof isAllowed === 'function' ? isAllowed : () => true;
  const levels = createLevels(n);

  // 受限链：撤下不允许发布的虚拟根点（该层等价为空轨道）
  for (let i = 0; i < n; i++) {
    if (!allowed(i, i)) {
      levels[i].beta[i] = null;
      levels[i].word[i] = null;
      levels[i].inv[i] = null;
    }
  }

  function published(i, x) {
    return levels[i].beta[x] != null && allowed(i, x);
  }

  // 扩展第 i 层横截轨道直到不动点；按点下标升序 BFS，代表元选择确定。
  // 受限模式下根点 i 仅在 allowed(i,i) 时发布；虚拟根不参与扩展与剥离。
  // S[i] 为 G^(i) 的生成元集合：包含落点在第 i 层及更深层的全部强生成元。
  function extendTransversal(i) {
    const L = levels[i];
    let added = 0;
    let changed = true;
    while (changed) {
      changed = false;
      for (let x = 0; x < n; x++) {
        if (!published(i, x)) continue;
        for (let gi = 0; gi < L.S.length; gi++) {
          const y = L.S[gi][x];
          if (L.beta[y] == null && allowed(i, y)) {
            const rep = compose(L.beta[x], L.S[gi], n);
            L.beta[y] = rep;
            L.word[y] = concatWord(L.word[x], L.genWord[gi]);
            L.inv[y] = invert(rep, n);
            added++;
            changed = true;
          }
        }
      }
    }
    return added;
  }

  // Schreier 生成元： beta(x) * g * beta(g(x))^{-1}（固定基点 i，属于 G^(i+1)）。
  // 受限链要求 x 与 g(x) 均为已发布轨道点，残差才保持本层分块结构。
  function makeSchreier(i, x, gi) {
    const L = levels[i];
    const g = L.S[gi];
    const y = g[x];
    if (!published(i, x) || !published(i, y)) return null;
    const perm = compose(compose(L.beta[x], g, n), L.inv[y], n);
    if (isIdentity(perm)) return null;
    const word = concatWord(
      concatWord(L.word[x], L.genWord[gi]),
      invertWord(L.word[y])
    );
    return { perm, word };
  }

  // 剥离残差 h 的首个非固定基点为 k：h ∈ G^(startLevel)…G^(k)，
  // 因此把它加入 startLevel..k 每一层的生成元集合（低层横截扩展需要它，
  // 即使它固定该层基点——经横截代表共轭后仍会扩展轨道）。
  function insertGenerator(g, word, startLevel) {
    const residual = siftRestricted(levels, n, g, word, startLevel, allowed);
    if (!residual) return false;
    if (residual.level >= n) return false; // 固定全部基点必为恒等
    const key = residual.perm.join(',');
    // 同一残差置换在不同闭包轮次可能再次出现；只在尚未收录它的层级加入
    let added = false;
    for (let j = startLevel; j <= residual.level; j++) {
      if (levels[j].Skeys.has(key + '@' + j)) continue;
      levels[j].Skeys.add(key + '@' + j);
      levels[j].S.push(residual.perm);
      levels[j].genWord.push(residual.word.slice());
      added = true;
    }
    return added;
  }

  // 初始生成元按（已排序的）录入顺序逐一插入，从第 0 层开始剥离
  for (let gi = 0; gi < generators.length; gi++) {
    insertGenerator(generators[gi], genWords[gi], 0);
  }

  // 确定性闭包：自低层向高层反复扩展轨道并剥离全部 Schreier 生成元，
  // Schreier 生成元固定本层基点，故从下一层（稳定子）开始剥离。
  // 直到没有新点、也没有新残差强生成元为止（有限群保证终止）。
  let progressed = true;
  while (progressed) {
    progressed = false;
    for (let i = 0; i < n; i++) {
      if (extendTransversal(i) > 0) progressed = true;
      const L = levels[i];
      for (let x = 0; x < n; x++) {
        if (!published(i, x)) continue;
        for (let gi = 0; gi < L.S.length; gi++) {
          const sch = makeSchreier(i, x, gi);
          if (!sch) continue;
          if (insertGenerator(sch.perm, sch.word, i + 1)) progressed = true;
        }
      }
    }
  }

  return levels;
}

// ---------------- 成员判定与因子链 / 不可归约证据 ----------------

function orbitPoints(level, n) {
  const pts = [];
  for (let x = 0; x < n; x++) {
    if (level.beta[x] != null) pts.push(x);
  }
  return pts;
}

function membership(names, operations, target) {
  const n = names.length;
  const generators = operations.map((o) => o.perm);
  const genWords = generators.map((_, i) => [i + 1]);
  const levels = buildChain(n, generators, genWords);

  let cur = target;
  const layerWords = []; // 每层所用横截代表的因子词
  const layers = []; // 逐层归约回放记录
  for (let i = 0; i < n; i++) {
    const L = levels[i];
    const x = cur[i];
    if (x === i) {
      layerWords.push([]);
      layers.push({
        level: i,
        base: i,
        image: i,
        moved: false,
        orbit: orbitPoints(L, n),
      });
      continue;
    }
    const rep = L.beta[x];
    if (rep == null) {
      // 首个无法继续归约的端口层：目标像点不在该基点轨道内
      return {
        member: false,
        reason: 'blocked',
        blockedLayer: i,
        evidence: {
          level: i,
          base: i,
          attemptedImage: x,
          orbit: orbitPoints(L, n),
          residual: cur.slice(),
        },
        chainSummary: summarizeChain(levels, n),
      };
    }
    layers.push({
      level: i,
      base: i,
      image: x,
      moved: true,
      repWord: L.word[x].slice(),
      orbit: orbitPoints(L, n),
    });
    layerWords.push(L.word[x].slice());
    // cur <- cur * t^{-1}：先执行 cur，再以横截代表之逆把基点像送回基点
    cur = compose(cur, invert(rep, n), n);
  }
  // target = t_{n-1} * … * t_1 * t_0，可执行因子链按层序反转后拼接
  const factorWord = [];
  for (let i = n - 1; i >= 0; i--) {
    for (const tok of layerWords[i]) factorWord.push(tok);
  }

  if (!isIdentity(cur)) {
    // 完备链下不会到达这里；作为防御性结论返回
    return {
      member: false,
      reason: 'residual',
      blockedLayer: n - 1,
      evidence: { level: n - 1, base: n - 1, attemptedImage: -1, orbit: [], residual: cur.slice() },
      chainSummary: summarizeChain(levels, n),
    };
  }

  // 独立复算：把横截代表拼出的因子词逐操作乘回，必须恰好等于目标
  const rebuilt = multiplyWord(factorWord, generators, n);
  if (!equalPerm(rebuilt, target)) {
    return {
      member: false,
      reason: 'verify-mismatch',
      blockedLayer: -1,
      evidence: { level: -1, base: -1, attemptedImage: -1, orbit: [], residual: rebuilt },
      chainSummary: summarizeChain(levels, n),
    };
  }

  return {
    member: true,
    reason: 'derivable',
    factorWord,
    layers,
    chainSummary: summarizeChain(levels, n),
  };
}

function summarizeChain(levels, n) {
  return levels.map((L, i) => ({
    level: i,
    base: i,
    orbitSize: orbitPoints(L, n).length,
    strongGeneratorCount: L.S.length,
  }));
}

// ---------------- 校准编组（分块）容差：分块传送子递归 ----------------
/*
 * 目标：判定目标接线 t 是否能在“每个校准组 B_j 内部任意重标”后由
 * 允许操作导出，即是否存在 g ∈ G 与逐块保持的重标置换 r（r(B_j)=B_j）
 * 使 g = r·t（先在组内重标 r，再执行操作链得到的接线与目标同构）。
 * 这等价于逐点块色条件
 *       b(g(x)) = b(t(x))  对所有端口 x 成立，
 * 即 g 与 t 把每个端口送入同一个校准组；组内具体差别由残余换位
 * r0 = t^{-1}·g（逐块保持）吸收，成功时按组返回 r0。
 *
 * 在既有稳定子链上的分块传送递归（Schreier 横截因子分解）：
 *   g = g_k·v，g_k = u_0·…·u_{k-1} 为已选横截代表前缀，v ∈ G^(k)。
 *   维护“剩余目标” t_k = g_k^{-1}·t（数组 t_k[x]=t[g_k^{-1}(x)] 的
 *   反向实现见下），条件化为 b(v(x)) = b(t_k(x))。
 *   第 k 层 u_k ∈ G^(k) 把基点 k 送到 x = u_k(k)，故端口 k 只能落入
 *   与其目标像 t_k(k) 相同的校准组：
 *       x ∈ Δ_k ∩ B_{b(t_k(k))}，
 *   Δ_k 为 G^(k) 在基点 k 的轨道（链第 k 层横截）。每层候选只是轨道
 *   点与一个块单元的集合交（≤ |B_j| ≤ n 个点），递归深度 n——
 *   不枚举群元素、不枚举组内全排列 Sym(B_j)、不以有限深度回放代替。
 *
 * 选中 u 后剩余目标更新为 t_{k+1}(z) = t_k(u^{-1}(z))。
 *
 * 集合稳定子剪枝（只使用既有链，不改动原链）：
 *   - 固定点校验：v ∈ G^(k) 固定基点 0..k-1，故这些点必须已与 t_k
 *     同块（b(x)=b(t_k(x))）；
 *   - 轨道-Hall 匹配：G^(k) 由第 k..n-1 层强生成元之并生成，预算其
 *     轨道连通分量；未处理点按目标块分组，逐块做二分完美匹配
 *     （源 y 只能匹配自身 G^(k)-轨道 ∩ B_{b(t_k(y))} 内的点）；
 *   - 失败状态记忆：同一层同一剩余目标不再重复搜索。
 *
 * 稳定裁决：候选落点按端口标识升序尝试；横截代表由按操作名 ASCII
 * 序排序的生成元经确定性 Schreier–Sims 闭包与横截 BFS 产生，因此
 * 多条等价链时输出唯一、可复算、可逐步回放。
 *
 * 不成立时定位回溯中最浅的失败端口层，并给出该层 G^(k) 轨道、
 * 目标校准组及其交集证据。
 */
function calibrationAudit(names, operations, target, groups) {
  const n = names.length;
  const generators = operations.map((o) => o.perm);
  const genWords = generators.map((_, i) => [i + 1]);
  // 既有稳定子链（G^(k) 的强生成元与横截在各层直接复用）
  const levels = buildChain(n, generators, genWords);

  // 源块标号 b(i)：端口 i 所属校准组
  const b = new Int8Array(n);
  for (let j = 0; j < groups.length; j++) {
    for (const x of groups[j]) b[x] = j;
  }

  // G^(k) 轨道连通分量：G^(k) 由第 k..n-1 层强生成元之并生成。
  const orbitLabels = [];
  for (let k = 0; k < n; k++) {
    const gens = [];
    for (let j = k; j < n; j++) for (const g of levels[j].S) gens.push(g);
    const label = new Int16Array(n).fill(-1);
    let component = 0;
    for (let s = 0; s < n; s++) {
      if (label[s] !== -1) continue;
      label[s] = component;
      const queue = [s];
      let head = 0;
      while (head < queue.length) {
        const z = queue[head++];
        for (const g of gens) {
          const w = g[z];
          if (label[w] === -1) {
            label[w] = component;
            queue.push(w);
          }
        }
      }
      component++;
    }
    orbitLabels.push(label);
  }

  const orbitOf = (k, y) => {
    const label = orbitLabels[k];
    const ly = label[y];
    const pts = [];
    for (let z = 0; z < n; z++) if (label[z] === ly) pts.push(z);
    return pts;
  };

  // 逐块完美匹配剪枝：未处理源点 y≥k 按其目标块 b(t_k(y)) 分组，
  // 必须能在同一校准组内、且在自身 G^(k)-轨道可达的点上各占一位。
  function feasible(k, tk) {
    for (let i = 0; i < k; i++) {
      if (b[i] !== b[tk[i]]) return false;
    }
    const reach = new Map();
    const reachable = (y) => {
      let list = reach.get(y);
      if (!list) {
        const j = b[tk[y]];
        list = [];
        for (const z of orbitOf(k, y)) if (b[z] === j) list.push(z);
        list.sort((p, q) => p - q);
        reach.set(y, list);
      }
      return list;
    };
    const matchZ = new Int16Array(n).fill(-1);
    const tryMatch = (y, seenZ) => {
      for (const z of reachable(y)) {
        if (seenZ[z]) continue;
        seenZ[z] = 1;
        if (matchZ[z] === -1 || tryMatch(matchZ[z], seenZ)) {
          matchZ[z] = y;
          return true;
        }
      }
      return false;
    };
    for (let y = k; y < n; y++) {
      if (!tryMatch(y, new Uint8Array(n))) return false;
    }
    return true;
  }

  const failed = new Set(); // 失败状态记忆：k|t_k
  const trail = new Array(n); // 成功路径上的逐层选择
  let firstBlocker = null; // 最浅失败层证据

  function recordBlocker(k, tk, note) {
    const j = b[tk[k]];
    const targetCell = groups[j].slice().sort((p, q) => p - q);
    const orbit = orbitPoints(levels[k], n);
    const allowed = orbit.filter((x) => b[x] === j);
    if (!firstBlocker || k < firstBlocker.level) {
      firstBlocker = {
        level: k,
        base: k,
        block: j,
        attemptedImage: tk[k],
        orbit,
        targetCell,
        allowedOrbit: allowed,
        // 当前前缀下仍需由 G^(k) 匹配的剩余目标 t_k
        residual: tk.slice(),
        note,
      };
    }
  }

  // 深度优先分块传送递归。
  //   k  : 当前端口层（基点）
  //   tk : 剩余目标置换数组 t_k
  //   gWord : 已积累前缀 g_k 的因子词
  function dfs(k, tk, gWord) {
    if (k === n) return { word: gWord };

    const memoKey = k + '|' + tk.join(',');
    if (failed.has(memoKey)) return null;

    if (!feasible(k, tk)) {
      recordBlocker(k, tk, 'fixed-point-or-matching');
      failed.add(memoKey);
      return null;
    }

    const L = levels[k];
    const j = b[tk[k]];
    // 候选落点：基点轨道 ∩ 目标校准组 B_j，按端口标识升序稳定裁决
    const candidates = [];
    for (let x = 0; x < n; x++) {
      if (L.beta[x] != null && b[x] === j) candidates.push(x);
    }

    for (const x of candidates) {
      const uWord = L.word[x];
      const uInv = L.inv[x];
      // t_{k+1}(z) = t_k(u^{-1}(z))
      const tkNext = new Array(n);
      for (let z = 0; z < n; z++) tkNext[z] = tk[uInv[z]];

      trail[k] = { level: k, base: k, block: j, chosenImage: x, repWord: uWord.slice() };
      const sol = dfs(k + 1, tkNext, concatWord(gWord, uWord));
      if (sol) return sol;
    }
    trail[k] = undefined;

    recordBlocker(k, tk, candidates.length === 0 ? 'empty-intersection' : 'exhausted');
    failed.add(memoKey);
    return null;
  }

  const groupSummary = groups.map((g, j) => ({
    block: j,
    members: g.slice().sort((p, q) => p - q),
    targetImage: g.map((x) => target[x]).sort((p, q) => p - q),
  }));

  const sol = dfs(0, target.slice(), []);

  if (!sol) {
    const blk = firstBlocker || {
      level: 0, base: 0, block: b[target[0]], orbit: orbitPoints(levels[0], n),
      targetCell: groups[b[target[0]]].slice(), allowedOrbit: [],
      residual: target.slice(), note: 'exhausted',
    };
    return {
      tolerable: false,
      member: false,
      reason: 'block-blocked',
      blockedLayer: blk.level,
      evidence: {
        level: blk.level,
        base: blk.base,
        block: blk.block,
        attemptedImage: blk.attemptedImage,
        orbit: blk.orbit,
        targetCell: blk.targetCell,
        allowedOrbit: blk.allowedOrbit,
        residual: blk.residual,
      },
      layers: trail.filter(Boolean),
      groupSummary,
      chainSummary: summarizeChain(levels, n),
    };
  }

  const factorWord = sol.word;
  const gPerm = multiplyWord(factorWord, generators, n);

  // 独立复算：操作链结果 g 与目标 t 必须逐点同块
  for (let x = 0; x < n; x++) {
    if (b[gPerm[x]] !== b[target[x]]) {
      return {
        tolerable: false,
        member: false,
        reason: 'verify-mismatch',
        blockedLayer: -1,
        evidence: { level: -1, base: -1, block: b[x], attemptedImage: gPerm[x],
          orbit: [], targetCell: [], allowedOrbit: [], residual: gPerm },
        layers: trail.filter(Boolean),
        groupSummary,
        chainSummary: summarizeChain(levels, n),
      };
    }
  }

  // 最终各组内残余换位 ρ：操作链执行后把 g(x) 校准到 t(x)，
  // 即 ρ[g(x)] = t(x)（g·ρ = t），ρ 逐校准组保持。
  const residual = new Array(n);
  for (let x = 0; x < n; x++) residual[gPerm[x]] = target[x];

  if (!equalPerm(compose(gPerm, residual, n), target)) {
    return {
      tolerable: false,
      member: false,
      reason: 'verify-mismatch',
      blockedLayer: -1,
      evidence: { level: -1, base: -1, block: -1, attemptedImage: -1,
        orbit: [], targetCell: [], allowedOrbit: [], residual },
      layers: trail.filter(Boolean),
      groupSummary,
      chainSummary: summarizeChain(levels, n),
    };
  }

  // 各组内残余换位（ρ 在该块上的限制）
  const residualByGroup = groups.map((g, j) => {
    const members = g.slice().sort((p, q) => p - q);
    return {
      block: j,
      members,
      mapping: members.map((x) => ({ from: x, to: residual[x] })),
    };
  });

  return {
    tolerable: true,
    member: true,
    reason: 'tolerable',
    factorWord,
    layers: trail.filter(Boolean),
    residual,
    residualByGroup,
    groupSummary,
    chainSummary: summarizeChain(levels, n),
  };
}

// 把因子词展开为可逐步回放的操作步骤，并给出每步后的端口排列
function expandFactorChain(names, operations, factorWord) {
  const n = names.length;
  const generators = operations.map((o) => o.perm);
  const state = identity(n);
  const steps = [
    {
      index: 0,
      operation: null,
      inverse: false,
      perm: state.slice(),
    },
  ];
  factorWord.forEach((tok, idx) => {
    const k = Math.abs(tok) - 1;
    const inverse = tok < 0;
    const g = inverse ? invert(generators[k], n) : generators[k];
    const next = compose(state, g, n);
    for (let i = 0; i < n; i++) state[i] = next[i];
    steps.push({
      index: idx + 1,
      operation: operations[k].name,
      inverse,
      perm: state.slice(),
    });
  });
  return steps;
}

// 供 UI 渲染：把内部置换转成 端口名 -> 端口名
function permToNames(perm, names) {
  return perm.map((v, i) => ({ from: names[i], to: v >= 0 ? names[v] : null }));
}

// 完整审计：校验 + 成员判定（启用校准编组时为分块容差判定）。
// 输入不合法时返回全部错误。编组/规程的任何改动都会产生新的输入对象，
// 旧结论由调用方（页面代次隔离）立即撤销，旧 Worker 回包不会覆盖。
function audit(input) {
  const v = validateInput(input);
  if (!v.ok) return { ok: false, errors: v.errors };

  let result;
  if (v.groupsEnabled) {
    result = calibrationAudit(v.names, v.operations, v.target, v.groups);
    result.calibrationEnabled = true;
    result.groups = v.groups.map((g) => g.map((x) => v.names[x]));
  } else {
    result = membership(v.names, v.operations, v.target);
    result.calibrationEnabled = false;
  }

  if (result.member) {
    result.steps = expandFactorChain(v.names, v.operations, result.factorWord);
  }
  result.names = v.names;
  result.operationNames = v.operations.map((o) => o.name);
  result.ok = true;
  if (result.evidence) {
    result.evidence.baseName = names_v(v, result.evidence.base);
    result.evidence.attemptedImageName = names_v(v, result.evidence.attemptedImage);
    result.evidence.orbitNames = result.evidence.orbit.map((x) => v.names[x]);
    if (Array.isArray(result.evidence.targetCell)) {
      result.evidence.targetCellNames = result.evidence.targetCell.map((x) => v.names[x]);
      result.evidence.allowedOrbitNames = result.evidence.allowedOrbit.map((x) => v.names[x]);
      result.evidence.groupName =
        result.evidence.block >= 0 ? result.groups[result.evidence.block] : null;
    }
    if (result.evidence.residual) {
      result.evidence.residualMapping = permToNames(result.evidence.residual, v.names);
    }
  }
  if (result.member && result.calibrationEnabled) {
    // 名称化的残余换位与逐块残余
    result.residualMapping = permToNames(result.residual, v.names);
    result.residualByGroup = result.residualByGroup.map((rg) => ({
      block: rg.block,
      group: rg.members.map((x) => v.names[x]),
      mapping: rg.mapping.map(({ from, to }) => ({
        from: v.names[from],
        to: v.names[to],
      })),
    }));
    result.groupSummary = result.groupSummary.map((gs) => ({
      block: gs.block,
      group: gs.members.map((x) => v.names[x]),
      targetImage: gs.targetImage.map((x) => v.names[x]),
    }));
  }
  return result;
}

function names_v(v, idx) {
  return idx >= 0 && idx < v.names.length ? v.names[idx] : null;
}

// 旧 Worker 回包防护：仅当回包代次与当前请求代次一致时结果才有效
function acceptIfCurrent(currentId, messageId, payload) {
  return currentId === messageId ? { accepted: true, payload } : { accepted: false };
}

// ---------------- 跨环境导出 ----------------

const api = {
  identity,
  isPermutation,
  compose,
  invert,
  equalPerm,
  isIdentity,
  parsePortList,
  parsePermText,
  validateInput,
  parseCalibrationGroups,
  buildChain,
  sift,
  membership,
  calibrationAudit,
  expandFactorChain,
  permToNames,
  multiplyWord,
  audit,
  acceptIfCurrent,
};

if (typeof module !== 'undefined' && module.exports) {
  module.exports = api;
}
if (typeof self !== 'undefined') {
  self.ApertureCore = api;
}
