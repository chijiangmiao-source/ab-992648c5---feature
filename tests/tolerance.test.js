'use strict';
/*
 * tolerance.test.js —— 校准编组容差审计测试：
 *   - 容差成功：操作链 + 组内残余换位，逐步回放终态为送达状态；
 *   - 容差失败：首个无法送入目标编组的端口层 + 允许轨道/目标组证据；
 *   - 未启用编组时结论与因子链与普通审计完全一致（回归）；
 *   - 编组校验错误一次性返回；修改编组旧结论失效；
 *   - 与暴力枚举对照（n≤4 全部生成元组 × 全部集合划分 × 全部目标）；
 *   - 集合稳定子阶对照、多链按操作名 ASCII 序稳定裁决、n=12 规模。
 */
const { test } = require('node:test');
const assert = require('node:assert/strict');
const C = require('../public/core.js');

function cyc(n, ...cycles) {
  const p = C.identity(n);
  for (const c of cycles) for (let i = 0; i < c.length; i++) p[c[i]] = c[(i + 1) % c.length];
  return p;
}
function auditWith(groups) {
  return C.audit({
    ports: 'A B C D',
    operations: [{ name: 'rotate', mapping: '(A B C D)' }],
    target: '(A C)',
    groups,
  });
}
function blocksOf(bo) {
  const m = new Map();
  bo.forEach((b, x) => { if (!m.has(b)) m.set(b, []); m.get(b).push(x); });
  return [...m.values()];
}
function allPerms(n) {
  const out = [];
  const rec = (p, used) => {
    if (p.length === n) return out.push(p.slice());
    for (let v = 0; v < n; v++) if (!used[v]) { used[v] = 1; p.push(v); rec(p, used); p.pop(); used[v] = 0; }
  };
  rec([], new Uint8Array(n));
  return out;
}
function bruteGroup(n, gens) {
  const id = C.identity(n);
  const seen = new Map([[id.join(','), id]]);
  const queue = [id];
  while (queue.length) {
    const cur = queue.shift();
    for (const g of gens) for (const h of [g, C.invert(g, n)]) {
      const ng = C.compose(cur, h, n);
      const k = ng.join(',');
      if (!seen.has(k)) { seen.set(k, ng); queue.push(ng); }
    }
  }
  return seen;
}
function allPartitions(n) {
  // n≤4 的全部集合划分（块色向量，按首现归一化）——Bell 数上界
  const raw = [];
  const rec = (i, cur, maxB) => {
    if (i === n) { raw.push(cur.slice()); return; }
    for (let b = 0; b <= maxB + 1 && b < n; b++) {
      cur.push(b);
      rec(i + 1, cur, Math.max(maxB, b));
      cur.pop();
    }
  };
  rec(0, [], -1);
  const norm = (a) => {
    const m = new Map();
    let id = 0;
    return Int16Array.from(a.map((x) => (m.has(x) ? m.get(x) : (m.set(x, id++), id - 1))));
  };
  const uniq = new Map();
  for (const a of raw) {
    const b = norm(a);
    uniq.set(b.join(','), b);
  }
  return [...uniq.values()];
}

// ---------- 容差成功 ----------

test('容差成功：C4 + 编组 {A B}{C D}，目标 (A C) 由 rotate³ 送达 + 组内残余', () => {
  const r = auditWith('A B; C D');
  assert.equal(r.ok, true);
  assert.equal(r.member, true);
  assert.equal(r.tolerance, true);
  assert.equal(r.reason, 'derivable-tolerance');
  assert.equal(r.groupsEnabled, true);
  // 逐步回放终态 = 操作链送达排列 g
  const last = r.steps[r.steps.length - 1].perm;
  const names = ['A', 'B', 'C', 'D'];
  const g = C.multiplyWord(r.factorWord, [cyc(4, [0, 1, 2, 3])], 4);
  assert.deepEqual(last, g);
  // g 把每个端口送入目标组：g(A)∈{C,D}, g(C)∈{A,B}
  const blockOf = new Int16Array([0, 0, 1, 1]);
  const t = cyc(4, [0, 2]);
  for (let x = 0; x < 4; x++) assert.equal(blockOf[g[x]], blockOf[t[x]]);
  // 组内残余 ρ = g^{-1}·t 必须逐块保持且非平凡
  const rho = C.compose(C.invert(g, 4), t, 4);
  for (let x = 0; x < 4; x++) assert.equal(blockOf[rho[x]], blockOf[x]);
  assert.ok(r.residualByGroup.some((grp) => grp.moved));
  // 集合稳定子链完备性已校验
  assert.equal(r.setStabilizerComplete, true);
  // 冻结摘要
  assert.deepEqual(r.frozenInput.ports, names);
  assert.deepEqual(r.frozenInput.groups, [['A', 'B'], ['C', 'D']]);
  assert.equal(r.frozenInput.groupsEnabled, true);
});

test('容差成功：操作链 g 与组内残余 ρ 恒满足 t = g·ρ（ρ 平凡时即精确实现）', () => {
  const r = C.audit({
    ports: 'A B C D',
    operations: [
      { name: 'rotate', mapping: '(A B C D)' },
      { name: 'swap_ab', mapping: '(A B)' },
    ],
    target: '(A B)',
    groups: 'A B; C D',
  });
  assert.equal(r.member, true);
  // (AB) 本身属于 H，ASCII 序最小的链是空操作 + 组内残余 (AB)
  assert.deepEqual(r.factorWord, []);
  assert.ok(r.residualByGroup.some((g) => g.moved));
  const last = r.steps[r.steps.length - 1].perm;
  const g = C.multiplyWord(r.factorWord, [cyc(4, [0, 1, 2, 3]), cyc(4, [0, 1])], 4);
  assert.deepEqual(last, g);
  const t = cyc(4, [0, 1]);
  const bo = new Int16Array([0, 0, 1, 1]);
  const rho = C.compose(C.invert(g, 4), t, 4);
  assert.deepEqual(C.compose(g, rho, 4), t);
  for (let x = 0; x < 4; x++) assert.equal(bo[rho[x]], bo[x]);
});

test('容差成功：目标不在 H 时残余与操作链都非平凡且 t = g·ρ', () => {
  const r = C.audit({
    ports: 'A B C D',
    operations: [
      { name: 'rotate', mapping: '(A B C D)' },
      { name: 'swap_ab', mapping: '(A B)' },
    ],
    target: '(B C)',
    groups: 'A B; C D',
  });
  assert.equal(r.member, true);
  assert.ok(r.factorWord.length > 0);
  const g = r.steps[r.steps.length - 1].perm;
  const t = cyc(4, [1, 2]);
  const bo = new Int16Array([0, 0, 1, 1]);
  const rho = C.compose(C.invert(g, 4), t, 4);
  assert.deepEqual(C.compose(g, rho, 4), t);
  for (let x = 0; x < 4; x++) assert.equal(bo[rho[x]], bo[x]);
});

test('容差成功：目标本身即组内重标时操作链为空（回放仅初始态）', () => {
  const r = C.audit({
    ports: 'A B C D',
    operations: [{ name: 'rotate', mapping: '(A B C D)' }],
    target: '(A B)',
    groups: 'A B; C D',
  });
  assert.equal(r.member, true);
  assert.deepEqual(r.factorWord, []);
  assert.equal(r.steps.length, 1);
  const moved = r.residualByGroup.filter((g) => g.moved);
  assert.equal(moved.length, 1);
});

// ---------- 容差失败 ----------

test('容差失败：C4 + {A B}{C D} 无法导出 (B C)，给出首阻塞层/允许轨道/目标组', () => {
  const r = C.audit({
    ports: 'A B C D',
    operations: [{ name: 'rotate', mapping: '(A B C D)' }],
    target: '(B C)',
    groups: 'A B; C D',
  });
  assert.equal(r.ok, true);
  assert.equal(r.member, false);
  assert.equal(r.tolerance, true);
  assert.equal(r.reason, 'blocked-tolerance');
  assert.ok(r.blockedLayer >= 1);
  const ev = r.evidence;
  // 允许轨道必须为空（C4 稳定子把唯一可达点送入错误组）
  assert.deepEqual(ev.allowedOrbit, []);
  assert.deepEqual(ev.allowedOrbitNames, []);
  // 目标组证据包含基点所在组端口
  assert.ok(ev.targetBlockPortNames.includes('B'));
  assert.ok(ev.targetBlockPortNames.includes('A'));
  // 全轨道证据非空且每行标注是否落入目标组
  assert.ok(ev.orbit.length >= 1);
  assert.ok(ev.orbitDetail.every((d) => typeof d.inTargetBlock === 'boolean'));
  assert.ok(ev.orbitDetail.every((d) => d.inTargetBlock === false));
});

test('容差失败与精确不可导出是不同结论（精确可达但组不容差不可能反例）', () => {
  // 无编组：(B C) 对 C4 精确不可导出；编组也不改变该结论，但 reason 不同
  const plain = C.audit({
    ports: 'A B C D',
    operations: [{ name: 'rotate', mapping: '(A B C D)' }],
    target: '(B C)',
  });
  assert.equal(plain.member, false);
  assert.equal(plain.tolerance, undefined);
  assert.equal(plain.reason, 'blocked');
  const tol = C.audit({
    ports: 'A B C D',
    operations: [{ name: 'rotate', mapping: '(A B C D)' }],
    target: '(B C)',
    groups: 'A B; C D',
  });
  assert.equal(tol.member, false);
  assert.equal(tol.reason, 'blocked-tolerance');
});

// ---------- 未启用编组：原结论与因子链保持不变 ----------

test('回归：编组留空时走普通审计，结论与因子链和无编组完全一致', () => {
  const base = {
    ports: 'A B C D',
    operations: [
      { name: 'rotate', mapping: '(A B C D)' },
      { name: 'swap_ab', mapping: '(A B)' },
    ],
    target: '(A C)(B D)',
  };
  const a = C.audit(base);
  const b = C.audit(Object.assign({}, base, { groups: '   ' }));
  assert.equal(a.member, true);
  assert.equal(b.tolerance, undefined);
  assert.deepEqual(b.factorWord, a.factorWord);
  assert.deepEqual(b.steps.map((s) => s.perm), a.steps.map((s) => s.perm));
  assert.equal(b.groupsEnabled, false);
  assert.deepEqual(b.frozenInput.groups, []);
});

test('回归：groupsEnabled=false 显式关闭时同样走普通路径', () => {
  const v = C.validateInput({
    ports: 'A B',
    operations: [{ name: 's', mapping: '(A B)' }],
    target: '(A B)',
    groups: 'A B',
    groupsEnabled: false,
  });
  assert.equal(v.groups.enabled, false);
});

// ---------- 编组校验错误一次性返回 ----------

test('校验：未知端口、端口编入多组等错误一次性返回', () => {
  const r = C.audit({
    ports: 'A B C',
    operations: [{ name: 'op1', mapping: '(A B C)' }],
    target: '(A B C)',
    groups: 'A B X; B C',
  });
  assert.equal(r.ok, false);
  const msgs = r.errors.map((e) => e.message).join('\n');
  assert.ok(r.errors.some((e) => e.scope === 'groups'));
  assert.ok(/不存在的端口/.test(msgs), msgs);
  assert.ok(/多个校准组/.test(msgs), msgs);
});

test('校验：同组内重复端口报错', () => {
  const v = C.validateInput({
    ports: 'A B C',
    operations: [{ name: 'op1', mapping: '(A B C)' }],
    target: '(A B C)',
    groups: 'A A B',
  });
  assert.equal(v.ok, false);
  assert.ok(v.errors.some((e) => /同一校准组内重复/.test(e.message)));
});

test('修改编组后冻结摘要随之改变（旧容差结论不能复用）', () => {
  const mk = (groups) =>
    C.audit({
      ports: 'A B C D',
      operations: [{ name: 'rotate', mapping: '(A B C D)' }],
      target: '(A C)',
      groups,
    });
  const r1 = mk('A B; C D');
  const r2 = mk('A C; B D');
  assert.equal(r1.member, true);
  assert.notDeepEqual(r1.frozenInput.groups, r2.frozenInput.groups);
  // 棋盘式编组下 (A C) 同组——空链即可
  assert.deepEqual(r2.factorWord, []);
});

// ---------- 穷举对照 ----------

test('穷举对照：容差结论与组元素枚举一致（n=3/4 全划分 × 全目标）', () => {
  const groupSets = {
    3: [
      [cyc(3, [0, 1, 2])],
      [cyc(3, [0, 1, 2]), cyc(3, [0, 1])],
    ],
    4: [
      [cyc(4, [0, 1, 2, 3])],
      [cyc(4, [0, 1, 2, 3]), cyc(4, [0, 1])],
      [cyc(4, [0, 1], [2, 3]), cyc(4, [0, 2], [1, 3])],
    ],
  };
  let checked = 0;
  for (const n of [3, 4]) {
    for (const gens of groupSets[n]) {
      const group = bruteGroup(n, gens);
      const levels = C.buildChain(n, gens, gens.map((_, i) => [i + 1]));
      for (const bo of allPartitions(n)) {
        const blocks = blocksOf(bo);
        for (const t of allPerms(n)) {
          let expect = false;
          for (const g of group.values()) {
            let ok = true;
            for (let x = 0; x < n; x++) if (bo[g[x]] !== bo[t[x]]) { ok = false; break; }
            if (ok) { expect = true; break; }
          }
          const sol = C.solveTolerance(n, levels, t, bo, blocks);
          checked++;
          if (expect) {
            assert.equal(sol.ok, true, '漏判：n=' + n + ' t=' + t.join('') + ' bo=' + bo.join(''));
            const g = C.multiplyWord(sol.word, gens, n);
            for (let x = 0; x < n; x++) assert.equal(bo[g[x]], bo[t[x]]);
            const rho = C.compose(C.invert(g, n), t, n);
            for (let x = 0; x < n; x++) assert.equal(bo[rho[x]], bo[x]);
          } else {
            assert.equal(sol.ok, false, '误判：n=' + n + ' t=' + t.join('') + ' bo=' + bo.join(''));
          }
        }
      }
    }
  }
  assert.ok(checked > 1000, '应对照上千个目标，实际 ' + checked);
});

test('穷举对照：集合稳定子 K=G∩H 阶与链轨道积一致', () => {
  const groupSets = [
    { n: 4, gens: [cyc(4, [0, 1, 2, 3])] },
    { n: 4, gens: [cyc(4, [0, 1, 2, 3]), cyc(4, [0, 1])] },
    { n: 4, gens: [cyc(4, [0, 1], [2, 3]), cyc(4, [0, 2], [1, 3])] },
  ];
  for (const { n, gens } of groupSets) {
    const group = bruteGroup(n, gens);
    const levels = C.buildChain(n, gens, gens.map((_, i) => [i + 1]));
    for (const bo of allPartitions(n)) {
      let bruteOrder = 0;
      for (const g of group.values()) {
        let ok = true;
        for (let x = 0; x < n; x++) if (bo[g[x]] !== bo[x]) { ok = false; break; }
        if (ok) bruteOrder++;
      }
      const k = C.buildSetStabilizerChain(n, gens, levels, bo, blocksOf(bo));
      let chainOrder = 1;
      for (const d of k.diagnostics) chainOrder *= d.orbitSize;
      assert.equal(chainOrder, bruteOrder, 'K 阶不符 bo=' + bo.join(''));
      assert.equal(k.complete, true);
    }
  }
});

// ---------- 多链按操作名 ASCII 序稳定裁决 ----------

test('裁决：容差链在所有可行颜色轨迹词中取字典序最小者，且结果确定', () => {
  const n = 4;
  const gens = [cyc(4, [0, 1, 2, 3]), cyc(4, [0, 1])]; // 操作名排序后 rotate < swap
  const bo = new Int16Array([0, 0, 1, 1]);
  const blocks = [[0, 1], [2, 3]];
  const target = cyc(4, [1, 2]); // 跨组目标
  const mkLevels = () => C.buildChain(n, gens, [[1], [2]]);
  const r1 = C.solveTolerance(n, mkLevels(), target, bo, blocks);
  const r2 = C.solveTolerance(n, mkLevels(), target, bo, blocks);
  assert.deepEqual(r1.word, r2.word);

  // 独立枚举全部颜色状态轨迹（不做最小剪枝），收集所有 g 词，
  // 与求解器的稳定裁决结果逐因子比较
  const levels = mkLevels();
  const all = [];
  const invertWord = (w) => w.slice().reverse().map((t) => -t);
  const enumDfs = (i, c, gWord) => {
    if (i === n) {
      all.push(gWord);
      return;
    }
    const L = levels[i];
    const wanted = bo[i];
    for (let y = 0; y < n; y++) {
      if (L.beta[y] == null || c[y] !== wanted) continue;
      const cNext = new Int16Array(n);
      for (let w = i + 1; w < n; w++) cNext[w] = c[L.beta[y][w]];
      // g = t_0^{-1}·t_1^{-1}…：随层数递增拼接本层代表之逆
      enumDfs(i + 1, cNext, gWord.concat(invertWord(L.word[y])));
    }
  };
  const c0 = new Int16Array(n);
  for (let z = 0; z < n; z++) c0[z] = bo[target[z]];
  enumDfs(0, c0, []);
  assert.ok(all.length >= 2, '该目标应有多条可行链用于裁决，实际 ' + all.length);
  for (const w of all) assert.ok(C.compareWords(r1.word, w) <= 0);

  // 操作录入顺序打乱（经按名排序）后结论一致
  const a = C.audit({
    ports: 'p0 p1 p2 p3',
    operations: [
      { name: 'swap', mapping: '(p0 p1)' },
      { name: 'rotate', mapping: '(p0 p1 p2 p3)' },
    ],
    target: '(p1 p2)',
    groups: 'p0 p1; p2 p3',
  });
  const b = C.audit({
    ports: 'p0 p1 p2 p3',
    operations: [
      { name: 'rotate', mapping: '(p0 p1 p2 p3)' },
      { name: 'swap', mapping: '(p0 p1)' },
    ],
    target: '(p1 p2)',
    groups: 'p0 p1; p2 p3',
  });
  assert.deepEqual(a.factorWord, b.factorWord);
});

// ---------- 规模上限 ----------

test('规模上限：n=12、多块编组容差判定快速完成且 K 完备', () => {
  const n = 12;
  const names = Array.from({ length: n }, (_, i) => 'P' + i);
  const ops = [
    { name: 'g_cycle', mapping: '(' + names.join(' ') + ')' },
    { name: 'g_swap', mapping: '(P0 P1)' },
    { name: 'g_p2', mapping: '(P2 P3)' },
    { name: 'g_p4', mapping: '(P4 P5)' },
    { name: 'g_p6', mapping: '(P6 P7)' },
    { name: 'g_p8', mapping: '(P8 P9)' },
    { name: 'g_p10', mapping: '(P10 P11)' },
    { name: 'g_mid', mapping: '(P5 P8)' },
  ];
  const started = Date.now();
  const r = C.audit({
    ports: names.join(' '),
    operations: ops,
    target: '(P0 P4)(P1 P5)',
    groups: 'P0 P1 P2 P3; P4 P5 P6 P7; P8 P9; P10 P11',
  });
  assert.ok(Date.now() - started < 10000);
  assert.equal(r.ok, true);
  assert.equal(r.member, true);
  assert.equal(r.setStabilizerComplete, true);
  // 终态各端口落入目标组
  const last = r.steps[r.steps.length - 1].perm;
  const groupOf = new Map();
  r.groupsSummary.forEach((g, bi) => g.forEach((nm) => groupOf.set(nm, bi)));
  const targetNames = {};
  r.frozenInput.target.forEach((p) => { targetNames[p.from] = p.to; });
  for (const nm of names) {
    assert.equal(groupOf.get(names[last[names.indexOf(nm)]]), groupOf.get(targetNames[nm]));
  }
});
