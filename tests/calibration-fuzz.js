'use strict';
// 分块容差判定与全枚举对拍：
// 对 n<=4 的多种生成元集、全部 n! 个目标、全部集合划分（Bell 数，n=4 为 15），
// 比较 calibrationAudit 结论与“枚举 G 全部元素 × 枚举块保持条件”的结论。
const C = require('../public/core.js');

function allPerms(n) {
  const out = [];
  const rec = (p, used) => {
    if (p.length === n) {
      out.push(p.slice());
      return;
    }
    for (let v = 0; v < n; v++) {
      if (used[v]) continue;
      used[v] = 1;
      p.push(v);
      rec(p, used);
      p.pop();
      used[v] = 0;
    }
  };
  rec([], new Uint8Array(n));
  return out;
}

function bruteGroup(n, gens) {
  const id = C.identity(n);
  const seen = new Map();
  seen.set(id.join(','), id);
  const queue = [id];
  while (queue.length) {
    const cur = queue.shift();
    for (const g of gens) {
      for (const h of [g, C.invert(g, n)]) {
        const ng = C.compose(cur, h, n);
        const k = ng.join(',');
        if (!seen.has(k)) {
          seen.set(k, ng);
          queue.push(ng);
        }
      }
    }
  }
  return seen;
}

// 全部集合划分
function allPartitions(n) {
  const out = [];
  const rec = (i, parts) => {
    if (i === n) {
      out.push(parts.map((p) => p.slice()));
      return;
    }
    for (let j = 0; j < parts.length; j++) {
      parts[j].push(i);
      rec(i + 1, parts);
      parts[j].pop();
    }
    parts.push([i]);
    rec(i + 1, parts);
    parts.pop();
  };
  rec(0, []);
  return out;
}

function cyc(n, ...cs) {
  const p = C.identity(n);
  for (const c of cs) for (let i = 0; i < c.length; i++) p[c[i]] = c[(i + 1) % c.length];
  return p;
}

let cases = 0;
let tolerableCount = 0;

function run(n, gens) {
  const names = C.identity(n).map((_, i) => 'p' + i);
  const ops = gens.map((g, i) => ({ name: 'g' + i, perm: g }));
  const groupElems = bruteGroup(n, gens);
  const partitions = allPartitions(n);
  for (const t of allPerms(n)) {
    for (const groups of partitions) {
      const r = C.calibrationAudit(names, ops, t, groups);
      // 期望：存在 g∈G 使 g 把每个块 B_j 映成 t(B_j)
      const blockOf = new Int8Array(n);
      groups.forEach((g, j) => g.forEach((x) => { blockOf[x] = j; }));
      let expected = false;
      let witness = null;
      for (const [, g] of groupElems) {
        let ok = true;
        for (let x = 0; x < n; x++) {
          if (blockOf[g[x]] !== blockOf[t[x]]) { ok = false; break; }
        }
        if (ok) { expected = true; witness = g; break; }
      }
      cases++;
      if (r.member !== expected) {
        console.error('MISMATCH n=' + n, 'gens=', JSON.stringify(gens),
          'target=', t, 'groups=', JSON.stringify(groups),
          'got=', r.member, 'expected=', expected, 'reason=', r.reason);
        process.exit(1);
      }
      if (expected) {
        tolerableCount++;
        // 独立复算：g·r = t 且 r 逐块保持
        const gs = gens;
        const gPerm = C.multiplyWord(r.factorWord, gs, n);
        const residual = C.compose(C.invert(gPerm, n), t, n);
        const rebuilt = C.compose(gPerm, residual, n);
        if (!C.equalPerm(rebuilt, t)) {
          console.error('REBUILD FAIL', t, JSON.stringify(groups));
          process.exit(1);
        }
        for (let x = 0; x < n; x++) {
          if (blockOf[residual[x]] !== blockOf[x]) {
            console.error('RESIDUAL CROSS-BLOCK', t, JSON.stringify(groups), residual);
            process.exit(1);
          }
        }
      } else {
        // 失败必须给证据
        if (!r.evidence || r.evidence.level < 0) {
          console.error('NO EVIDENCE', t, JSON.stringify(groups));
          process.exit(1);
        }
      }
    }
  }
}

// n=3：多种群（平凡/C3/S3）
run(3, []);
run(3, [cyc(3, [0, 1, 2])]);
run(3, [cyc(3, [0, 1])]);
run(3, [cyc(3, [0, 1, 2]), cyc(3, [0, 1])]);
run(3, [cyc(3, [0, 1]), cyc(3, [1, 2])]);
// n=4：C4 / V4 / 一个 A4 生成对 / S4 / 一个非传递群
run(4, [cyc(4, [0, 1, 2, 3])]);
run(4, [cyc(4, [0, 1], [2, 3]), cyc(4, [0, 2], [1, 3])]);
run(4, [cyc(4, [0, 1, 2]), cyc(4, [0, 1, 2, 3])]);
run(4, [cyc(4, [0, 1, 2, 3]), cyc(4, [0, 1])]);
run(4, [cyc(4, [0, 1]), cyc(4, [2, 3])]);
run(4, [cyc(4, [0, 1, 2])]); // 固定 3 的 S3（非传递）
run(4, [cyc(4, [0, 1]), cyc(4, [0, 1, 2, 3]), cyc(4, [1, 2])]);

console.log('对拍 ' + cases + ' 个（目标×划分×群）用例全部一致，其中容差成立 ' +
  tolerableCount + ' 例。');
