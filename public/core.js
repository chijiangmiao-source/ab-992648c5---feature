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

// 因子词大小比较：先按操作名 ASCII 序，再按正操作 < 逆操作，最后按词长。
// 生成元在 validateInput 中已按操作名排序，故编号序即操作名 ASCII 序；
// 同时接收 nameOf 以便直接按名字比较（容差链上的因子词编号引用同一序）。
function compareWords(a, b) {
  const len = Math.min(a.length, b.length);
  for (let i = 0; i < len; i++) {
    const ga = Math.abs(a[i]);
    const gb = Math.abs(b[i]);
    if (ga !== gb) return ga < gb ? -1 : 1;
    const ia = a[i] < 0 ? 1 : 0;
    const ib = b[i] < 0 ? 1 : 0;
    if (ia !== ib) return ia - ib; // 正操作排在逆操作前
  }
  return a.length - b.length;
}

function minWord(a, b) {
  if (a == null) return b == null ? null : b.slice();
  if (b == null) return a.slice();
  return compareWords(a, b) <= 0 ? a.slice() : b.slice();
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
 * 解析校准编组文本：若干允许内部互换的端口校准组。
 * 组间以 ; ；或换行分隔，组内端口以空白/逗号分隔，亦可加括号：
 *   "A B; C D"  /  "(A B)(C D)"  /  "A,B\nC,D"
 * 未列出的端口各自成为单例块（不与任何端口互换）。
 * 未知端口、同一端口落入多个校准组、空组均收集为错误。
 * 返回 blockOf：端口下标 -> 块号（按组中首个端口下标升序编号，单例随后），
 * 以及 blocks：块 -> 端口下标数组（按端口标识排序）。
 */
function parseCalibrationGroups(text, names) {
  const n = names.length;
  const errors = [];
  const raw = String(text == null ? '' : text).trim();
  const indexByName = {};
  names.forEach((nm, i) => {
    indexByName[nm] = i;
  });
  const groups = [];
  if (raw) {
    // 括号形式 (A B)(C D) 视为组的分隔；统一替换后按 ; ；换行与 )( 边界切分
    const normalized = raw
      .replace(/[（]/g, '(')
      .replace(/[）]/g, ')')
      .replace(/\)\s*\(/g, ');(');
    const chunks = normalized.split(/[;；\n\r]+/);
    for (const chunk of chunks) {
      const tokens = chunk
        .replace(/[()]/g, ' ')
        .split(/[\s,，]+/)
        .map((s) => s.trim())
        .filter(Boolean);
      if (tokens.length === 0) continue;
      const idxs = [];
      const localSeen = new Set();
      for (const tk of tokens) {
        if (!Object.prototype.hasOwnProperty.call(indexByName, tk)) {
          errors.push('校准编组引用了不存在的端口：“' + tk + '”');
          continue;
        }
        const idx = indexByName[tk];
        if (localSeen.has(idx)) {
          errors.push('端口 “' + names[idx] + '” 在同一校准组内重复出现');
          continue;
        }
        localSeen.add(idx);
        idxs.push(idx);
      }
      if (idxs.length > 0) groups.push(idxs);
    }
  }

  const owner = new Int16Array(n).fill(-1);
  groups.forEach((grp, gi) => {
    for (const idx of grp) {
      if (owner[idx] !== -1) {
        errors.push(
          '端口 “' + names[idx] + '” 同时编入多个校准组（第 ' +
          (owner[idx] + 1) + ' 组与第 ' + (gi + 1) + ' 组）'
        );
      }
      owner[idx] = gi;
    }
  });
  if (errors.length) return { ok: false, errors };

  // 块编号：多端口校准组优先（按组内最小端口下标排序，保证确定性），
  // 未编组端口随后各自成为单例块（同样按端口下标排序）
  const multi = groups
    .filter((g) => g.length >= 2)
    .map((g) => g.slice().sort((a, b) => a - b))
    .sort((a, b) => a[0] - b[0]);
  const singletons = [];
  for (let i = 0; i < n; i++) {
    let inMulti = false;
    for (const g of multi) {
      if (g.includes(i)) {
        inMulti = true;
        break;
      }
    }
    if (!inMulti) singletons.push([i]);
  }
  const blocks = multi.concat(singletons);
  const blockOf = new Int16Array(n);
  blocks.forEach((blk, bi) => {
    for (const idx of blk) blockOf[idx] = bi;
  });
  return { ok: true, errors: [], blockOf, blocks, multiGroupCount: multi.length };
}

/*
 * 全量校验：端口、操作（具名置换）、目标。
 * 所有错误一次性返回（重复操作名、缺失端口、非双射映射、非法目标等），
 * 调用方据此立即撤销旧结论。
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

  // 校准编组：留空（或显式 enabled=false）表示未启用，原有可导出结论路径不变
  const groupsText = String(input.groups == null ? '' : input.groups).trim();
  const groupsEnabled = input.groupsEnabled !== false && groupsText.length > 0;
  let groupsInfo = null;
  if (groupsEnabled && names.length >= 2) {
    const gr = parseCalibrationGroups(groupsText, names);
    if (!gr.ok) {
      for (const e of gr.errors) errors.push({ scope: 'groups', message: e });
    } else {
      groupsInfo = {
        enabled: true,
        blockOf: Array.from(gr.blockOf),
        blocks: gr.blocks.map((b) => b.slice()),
        multiGroupCount: gr.multiGroupCount,
      };
    }
  }

  if (errors.length) return { ok: false, errors, names: [], operations: [], target: null, groups: null };

  // 生成元按操作名排序，保证构造过程完全确定（端口标识亦已排序）
  const order = ops.map((_, i) => i).sort((a, b) =>
    ops[a].name < ops[b].name ? -1 : ops[a].name > ops[b].name ? 1 : a - b
  );
  const sortedOps = order.map((i) => ops[i]);
  if (!groupsInfo) {
    // 未启用编组：每个端口自成一块的平凡划分（仅供摘要/回退使用，不改变判定路径）
    groupsInfo = {
      enabled: false,
      blockOf: names.map((_, i) => i),
      blocks: names.map((_, i) => [i]),
      multiGroupCount: 0,
    };
  }
  return {
    ok: true,
    errors: [],
    names,
    operations: sortedOps,
    target,
    groups: groupsInfo,
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

// Schreier–Sims 链构造器：同一套确定性闭包逻辑既用于全群 G，
// 也用于编组容差中的集合稳定子 K = G ∩ H（见 createColoredSolver）。
function createSimsBuilder(n) {
  const levels = createLevels(n);

  // 扩展第 i 层横截轨道直到不动点；按点下标升序 BFS，代表元选择确定。
  // S[i] 为 G^(i) 的生成元集合：包含落点在第 i 层及更深层的全部强生成元。
  function extendTransversal(i) {
    const L = levels[i];
    let added = 0;
    let changed = true;
    while (changed) {
      changed = false;
      for (let x = 0; x < n; x++) {
        if (L.beta[x] == null) continue;
        for (let gi = 0; gi < L.S.length; gi++) {
          const y = L.S[gi][x];
          if (L.beta[y] == null) {
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

  // Schreier 生成元： beta(x) * g * beta(g(x))^{-1}（固定基点 i，属于 G^(i+1)）
  function makeSchreier(i, x, gi) {
    const L = levels[i];
    const g = L.S[gi];
    const y = g[x];
    if (L.beta[x] == null || L.beta[y] == null) return null;
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
    const residual = sift(levels, n, g, word, startLevel);
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

  // 确定性闭包：自低层向高层反复扩展轨道并剥离全部 Schreier 生成元，
  // Schreier 生成元固定本层基点，故从下一层（稳定子）开始剥离。
  // 直到没有新点、也没有新残差强生成元为止（有限群保证终止）。
  function close() {
    let progressed = true;
    while (progressed) {
      progressed = false;
      for (let i = 0; i < n; i++) {
        if (extendTransversal(i) > 0) progressed = true;
        const L = levels[i];
        for (let x = 0; x < n; x++) {
          if (L.beta[x] == null) continue;
          for (let gi = 0; gi < L.S.length; gi++) {
            const sch = makeSchreier(i, x, gi);
            if (!sch) continue;
            if (insertGenerator(sch.perm, sch.word, i + 1)) progressed = true;
          }
        }
      }
    }
  }

  return { levels, insertGenerator, close };
}

function buildChain(n, generators, genWords) {
  // 初始生成元按（已排序的）录入顺序逐一插入，从第 0 层开始剥离
  const builder = createSimsBuilder(n);
  for (let gi = 0; gi < generators.length; gi++) {
    builder.insertGenerator(generators[gi], genWords[gi], 0);
  }
  builder.close();
  return builder.levels;
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

// ---------------- 校准编组容差：分块传送子 + 集合稳定子 ----------------
//
// 数学约定（乘法仍为“先 a 后 b”，(a*b)[x] = b[a[x]]）：
//   端口 Ω={0..n-1} 被划分成互不相交的校准组（块），未编组端口为单例块。
//   H = ∏_块 Sym(块)：组内任意重标。目标 t 容差可导出 ⇔ 存在 g∈G、ρ∈H 使 t = g·ρ
//   ⇔ 对每个端口 x：blockOf[g(x)] = blockOf[t(x)]（g 把每个端口送进其目标组）。
//
// 在既有 G 稳定子链上递归构造分块传送子（solveTolerance）与集合稳定子
// K = G ∩ H（buildSetStabilizerChain）：逐层把基点像限制到“目标组对应轨道”，
// 按 (层, 块色向量) memo 化；不枚举群元素、不枚举组内全排列、不以有限深度
// 回放代替；多解按操作名 ASCII 序（因子词字典序）稳定裁决。

/*
 * 容差求解（剥离式颜色递归，严格建立在既有 G 稳定子链之上）：
 *   目标：求 g∈G 与组内重标 ρ∈H=∏Sym(块)，使 t = g·ρ
 *   （(g·ρ)(x)=ρ(g(x))），等价条件 blockOf[g(x)] = blockOf[t(x)]。
 *
 *   剥离式递归 cur_{i+1}=cur_i·t_i^{-1}（t_i=β_i(y) 为第 i 层横截代表）
 *   天然刻画左陪集 h·g'∈H·G：对 t^{-1} 求解得 t^{-1}=h·g'（h 块保持），
 *   取 g=g'^{-1}、ρ=h^{-1} 即得 t=g·ρ。第 i 层允许像点满足
 *   blockOf[cur_i^{-1}(y)] = blockOf[i]，可行性只依赖颜色向量
 *   c[z]=blockOf[cur_i^{-1}(z)]（z≥i），转移 c'[w]=c[t_i(w)]。
 *   按 (层, 颜色向量) memo 化——不枚举群元素、不枚举组内全排列、不以有限
 *   深度回放代替；有限群 + 每层消去一个端口保证终止。
 *
 *   g 的执行词由 g' 词反序取逆得到；多解直接在 g 的因子词上按操作名 ASCII 序
 *   （编号序，正操作先于逆操作，再比词长）字典序稳定裁决。
 * 返回 { ok:true, word } 或 { ok:false, blocker }（最浅阻塞层 + 轨道/目标组证据）。
 */
function solveTolerance(n, levels, target, blockOf, blocks) {
  // 剥离对象 q = t^{-1}，cur_0 = q；颜色 c[z]=blockOf[cur^{-1}(z)]，
  // 故 c0[z] = blockOf[cur_0^{-1}(z)] = blockOf[t(z)]。
  const invTarget = invert(target, n);
  const c0 = new Int16Array(n);
  for (let z = 0; z < n; z++) c0[z] = blockOf[target[z]];

  const memo = new Map();
  let blocker = null;
  let blockerDepth = n + 1;

  function colorKey(i, c) {
    let s = i + ':';
    for (let z = i; z < n; z++) s += c[z] + ',';
    return s;
  }

  // cur 仅用于失败证据与 x0 判定的排列实例；可行性只依赖颜色向量 c
  function dfs(i, c, cur) {
    if (i === n) return [];
    const key = colorKey(i, c);
    if (memo.has(key)) return memo.get(key);
    memo.set(key, null); // 占位防御（每层严格消去一个端口，无环）

    const L = levels[i];
    const wantedBlock = blockOf[i];
    const candidates = [];
    for (let y = 0; y < n; y++) {
      if (L.beta[y] != null && c[y] === wantedBlock) candidates.push(y);
    }

    if (candidates.length === 0) {
      if (i < blockerDepth) {
        blockerDepth = i;
        // 该层 G 轨道各点当前对应的来源端口块（c[z] 即 blockOf[cur^{-1}(z)]）
        const gOrbit = orbitPoints(L, n);
        const invCur = invert(cur, n);
        blocker = {
          level: i,
          base: i,
          gOrbit,
          orbitBlockLanding: gOrbit.map((y) => c[y]),
          orbitSource: gOrbit.map((y) => invCur[y]),
          targetBlock: wantedBlock,
          targetBlockPorts: blocks[wantedBlock].slice(),
          residualImage: cur[i],
          residual: cur.slice(),
        };
      }
      return null;
    }

    let best = null;
    for (const y of candidates) {
      const rep = L.beta[y];
      // c'[w] = c[t_i(w)]，w≥i+1（t_i 固定 0..i-1，t_i(i)=y）
      const cNext = new Int16Array(n);
      for (let w = i + 1; w < n; w++) cNext[w] = c[rep[w]];
      const curNext = compose(cur, L.inv[y], n);
      const deeper = dfs(i + 1, cNext, curNext);
      if (deeper === null) continue;
      // g 词：本层代表之逆排在深层之前（g = g'^{-1} 的逐段反序取逆）
      const word = concatWord(invertWord(L.word[y]), deeper);
      if (best === null || compareWords(word, best) < 0) best = word;
    }
    if (best === null) return null; // 更深层阻塞，blocker 已记录
    memo.set(key, best);
    return best;
  }

  const word = dfs(0, c0, invTarget);
  if (word === null) return { ok: false, blocker };
  return { ok: true, word };
}

/*
 * 集合稳定子 K = G ∩ H（H=∏ Sym(块)）的确定性 Schreier–Sims 链。
 *
 * 完备构造（逐层递归，全部建立在既有 G 链之上，不枚举群元素）：
 *   对每层 i，在 G^(i) 内做一次块保持搜索：求 r∈G^(i) 使 r 保持每个块集合
 *   （即目标为恒等的容差搜索），并在第 i 层钉住基点像 y。
 *   对每个 y ∈ 轨道_G^(i)(i) ∩ 块(i) 都能得到一个 k∈K^(i)、k(i)=y 的传送子；
 *   它们保证 K^(i) 在该交点轨道上传递。所有这些元素按所属层插入同一 Sims
 *   构造器（startLevel=i），再跑标准 Schreier 闭包——种子与 Schreier 残差
 *   都是块保持元（K 是子群，乘积封闭），逐层横截恰好是各块内轨道。
 */
function buildSetStabilizerChain(n, generators, levels, blockOf, blocks) {
  const preservesBlocks = (p) => {
    for (let x = 0; x < n; x++) if (blockOf[p[x]] !== blockOf[x]) return false;
    return true;
  };

  const builder = createSimsBuilder(n);
  const reachableCounts = new Array(n).fill(0);

  for (let i = 0; i < n; i++) {
    const found = searchBlockPreserversAtLevel(n, generators, levels, blockOf, blocks, i);
    reachableCounts[i] = found.length; // 含基点自身（恒等传送子）
    for (const f of found) {
      if (!preservesBlocks(f.perm)) continue; // 防御性校验：理论上必然成立
      builder.insertGenerator(f.perm, f.word, i);
    }
  }
  builder.close();

  // 完备性校验：K^(i) 横截点数必须等于“钉住像点颜色递归”可达的同组点数。
  // 这些点各有块保持传送子入链（构造上即保证横截传递），故等式成立当且仅当
  // 该层集合稳定子轨道已被完整生成。
  const diagnostics = [];
  let complete = true;
  for (let i = 0; i < n; i++) {
    const orbitSize = orbitPoints(builder.levels[i], n).length;
    if (orbitSize !== reachableCounts[i]) complete = false;
    diagnostics.push({
      level: i,
      base: i,
      blockId: blockOf[i],
      orbitSize,
      reachableOrbitSize: reachableCounts[i],
      strongGeneratorCount: builder.levels[i].S.length,
    });
  }
  return { levels: builder.levels, diagnostics, complete };
}

/*
 * 在 G^(pinned) 内求一个块保持元素 r（对所有 x≥pinned 有 blockOf[r(x)]=blockOf[x]），
 * 并强制第 pinned 层基点像为指定同组点 wantedY。
 * 这是一次钉住目标点的定向递归：pinned 层候选只含 wantedY，其余层照常取
 * “落入当前块”的轨道交点。每次调用独立 memo；状态数上界为 n·(各层块像向量数)。
 */
/*
 * 在 G^(pinned) 内求块保持元素 k（blockOf[k(x)]=blockOf[x]），
 * 并强制 k(pinned)=wantedY（同块可达点）。与 solveTolerance 相同的剥离式
 * 颜色递归，目标为恒等（初始颜色 c[z]=blockOf[z]），仅在 pinned 层钉住 y。
 */
function preserverTo(n, generators, levels, blockOf, pinnedLevel, wantedY) {
  const c0 = new Int16Array(n);
  for (let z = 0; z < n; z++) c0[z] = blockOf[z];
  const memo = new Map();

  function colorKey(i, c) {
    let s = i + ':';
    for (let z = i; z < n; z++) s += c[z] + ',';
    return s;
  }

  function dfs(i, c, cur) {
    if (i === n) return [];
    const key = colorKey(i, c);
    if (memo.has(key)) return memo.get(key);
    memo.set(key, null);

    const L = levels[i];
    const wantedBlock = blockOf[i];
    let candidates;
    if (i === pinnedLevel) {
      if (L.beta[wantedY] == null || c[wantedY] !== wantedBlock) return null;
      candidates = [wantedY];
    } else {
      candidates = [];
      for (let y = 0; y < n; y++) {
        if (L.beta[y] != null && c[y] === wantedBlock) candidates.push(y);
      }
    }
    if (candidates.length === 0) return null;

    let best = null;
    for (const y of candidates) {
      const rep = L.beta[y];
      const cNext = new Int16Array(n);
      for (let w = i + 1; w < n; w++) cNext[w] = c[rep[w]];
      const curNext = compose(cur, L.inv[y], n);
      const suffix = dfs(i + 1, cNext, curNext);
      if (suffix === null) continue;
      // g' = t_{n-1}…t_i 本身即块保持元且 g'(pinned)=wantedY（非右陪集，
      // 无需取反；与 solveTolerance 的右陪场景不同）
      const word = concatWord(suffix, L.word[y]);
      if (best === null || compareWords(word, best) < 0) best = word;
    }
    if (best === null) return null;
    memo.set(key, best);
    return best;
  }

  const word = dfs(pinnedLevel, c0, identity(n));
  if (word === null) return null;
  return { y: wantedY, word, perm: multiplyWord(word, generators, n) };
}

function searchBlockPreserversAtLevel(n, generators, levels, blockOf, blocks, pinnedLevel) {
  const L = levels[pinnedLevel];
  const out = [];
  void blocks;
  // 每个可达同组像点各求一条最小传送子（按点下标升序，保证确定性）
  for (let y = 0; y < n; y++) {
    if (L.beta[y] == null) continue;
    if (blockOf[y] !== blockOf[pinnedLevel]) continue;
    const f = preserverTo(n, generators, levels, blockOf, pinnedLevel, y);
    if (f) out.push(f);
  }
  return out;
}

// ---------------- 容差成员判定：操作链 + 组内残余换位 ----------------

function membershipTolerance(names, operations, target, groups) {
  const n = names.length;
  const generators = operations.map((o) => o.perm);
  const genWords = generators.map((_, i) => [i + 1]);
  const levels = buildChain(n, generators, genWords);
  const blockOf = Int16Array.from(groups.blockOf);
  const blocks = groups.blocks;

  const sol = solveTolerance(n, levels, target, blockOf, blocks);
  const chainSummary = summarizeChain(levels, n);

  if (!sol.ok) {
    const b = sol.blocker;
    // 该层 G^(i) 轨道各点当前对应的来源块 c[y]=blockOf[cur^{-1}(y)]：
    // 仅当某轨道点来自基点所在组（目标组）时，横截代表才能把该端口送入目标编组。
    const orbitDetail = b.gOrbit.map((y, k) => ({
      point: y,
      source: b.orbitSource[k],
      blockId: b.orbitBlockLanding[k],
      inTargetBlock: b.orbitBlockLanding[k] === b.targetBlock,
    }));
    return {
      member: false,
      tolerance: true,
      reason: 'blocked-tolerance',
      blockedLayer: b.level,
      evidence: {
        level: b.level,
        base: b.level,
        attemptedImage: b.residualImage,
        orbit: b.gOrbit,
        orbitDetail,
        allowedOrbit: orbitDetail.filter((d) => d.inTargetBlock).map((d) => d.point),
        targetBlock: b.targetBlock,
        targetBlockPorts: b.targetBlockPorts,
        residual: b.residual,
      },
      chainSummary,
    };
  }

  // 独立复算：逐操作乘回实现词，必须逐端口把每个端口送入其目标组
  const g = multiplyWord(sol.word, generators, n);
  for (let x = 0; x < n; x++) {
    if (blockOf[g[x]] !== blockOf[target[x]]) {
      return {
        member: false,
        tolerance: true,
        reason: 'verify-mismatch',
        blockedLayer: -1,
        evidence: {
          level: -1, base: -1, attemptedImage: -1, orbit: [],
          targetBlock: -1, targetBlockPorts: [], residual: g,
        },
        chainSummary,
      };
    }
  }

  // 组内残余重标 h = g^{-1}·t ∈ H（每个块内部的置换）
  const residualRelabel = compose(invert(g, n), target, n);
  const residualByGroup = blocks.map((blk, bi) => ({
    blockId: bi,
    ports: blk.slice(),
    mapping: blk.map((x) => ({ from: x, to: residualRelabel[x] })),
    moved: blk.some((x) => residualRelabel[x] !== x),
  }));

  // 集合稳定子 K = G ∩ H（仅用于诊断与组内残余可达性旁证，不参与操作链裁决）
  const stab = buildSetStabilizerChain(n, generators, levels, blockOf, blocks);

  return {
    member: true,
    tolerance: true,
    reason: 'derivable-tolerance',
    factorWord: sol.word,
    residualRelabel,
    residualByGroup,
    setStabilizer: stab.diagnostics,
    setStabilizerComplete: stab.complete,
    chainSummary,
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

// 冻结当前输入摘要：任何输入改动都会使旧结论失效（UI 侧以代次隔离保证），
// 结论中附带本次计算所基于的端口、操作、目标与编组摘要。
function freezeSummary(v) {
  return {
    ports: v.names.slice(),
    operations: v.operations.map((o) => o.name),
    target: permToNames(v.target, v.names),
    groupsEnabled: v.groups.enabled,
    groups: v.groups.blocks
      .filter((blk) => blk.length >= 2)
      .map((blk) => blk.map((x) => v.names[x])),
  };
}

// 完整审计：校验 + 成员判定。输入不合法时返回全部错误。
function audit(input) {
  const v = validateInput(input);
  if (!v.ok) return { ok: false, errors: v.errors };

  const result = v.groups.enabled
    ? membershipTolerance(v.names, v.operations, v.target, v.groups)
    : membership(v.names, v.operations, v.target);

  if (result.member) {
    result.steps = expandFactorChain(v.names, v.operations, result.factorWord);
  }
  result.names = v.names;
  result.operationNames = v.operations.map((o) => o.name);
  result.groupsEnabled = v.groups.enabled;
  result.groupsSummary = v.groups.blocks
    .filter((blk) => blk.length >= 2)
    .map((blk) => blk.map((x) => v.names[x]));
  result.frozenInput = freezeSummary(v);
  result.ok = true;

  if (result.evidence) {
    result.evidence.baseName = names_v(v, result.evidence.base);
    result.evidence.attemptedImageName = names_v(v, result.evidence.attemptedImage);
    result.evidence.orbitNames = result.evidence.orbit.map((x) => v.names[x]);
    result.evidence.residualMapping = permToNames(result.evidence.residual, v.names);
    if (result.evidence.allowedOrbit) {
      result.evidence.allowedOrbitNames = result.evidence.allowedOrbit.map((x) => v.names[x]);
    }
    if (result.evidence.targetBlockPorts) {
      result.evidence.targetBlockPortNames = result.evidence.targetBlockPorts.map((x) => v.names[x]);
    }
    if (result.evidence.orbitDetail) {
      result.evidence.orbitDetail = result.evidence.orbitDetail.map((d) => ({
        pointName: v.names[d.point],
        sourceName: names_v(v, d.source),
        landsBlockId: d.blockId,
        inTargetBlock: d.inTargetBlock,
      }));
    }
  }

  if (result.member && result.tolerance) {
    // 组内残余换位解析为端口名
    result.residualRelabelNames = permToNames(result.residualRelabel, v.names);
    result.residualByGroup = result.residualByGroup.map((g) => ({
      blockId: g.blockId,
      ports: g.ports.map((x) => v.names[x]),
      moved: g.moved,
      mapping: g.mapping.map((m) => ({
        from: v.names[m.from],
        to: v.names[m.to],
      })),
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
  parseCalibrationGroups,
  validateInput,
  buildChain,
  sift,
  membership,
  membershipTolerance,
  solveTolerance,
  buildSetStabilizerChain,
  compareWords,
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
