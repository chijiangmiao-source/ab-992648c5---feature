'use strict';
/*
 * app.js —— 审计页面逻辑。
 * 关键点：用户在计算未结束时改写规程并再次提交，旧 Worker 回包不得覆盖新输入/新结论。
 * 实现：每次提交递增 requestId（代次）；回包仅在 id 匹配当前代次时应用；
 *       任何输入变更立即撤销旧结论。
 */
(function () {
  const $ = (id) => document.getElementById(id);

  let worker = null;
  let currentRequestId = 0;
  let latestResult = null;
  let replay = null;

  function esc(s) {
    return String(s)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;');
  }

  function ensureWorker() {
    if (worker) return worker;
    worker = new Worker('worker.js');
    worker.onmessage = (ev) => {
      const msg = ev.data || {};
      if (currentRequestId !== msg.requestId) {
        // 旧 Worker 回包：明确丢弃，不得触碰当前输入与结论
        console.info('丢弃过期审计回包 #' + msg.requestId + '（当前 #' + currentRequestId + '）');
        return;
      }
      latestResult = msg.result;
      renderResult(msg.result);
      setComputing(false);
    };
    worker.onerror = (e) => {
      renderError('Worker 错误：' + (e.message || '未知错误'));
      setComputing(false);
    };
    return worker;
  }

  function collectInput() {
    const rows = Array.from(document.querySelectorAll('.op-row'));
    const operations = rows.map((row) => ({
      name: row.querySelector('.op-name').value,
      mapping: row.querySelector('.op-mapping').value,
    }));
    return {
      ports: $('ports').value,
      operations,
      target: $('target').value,
      groups: $('groups').value,
    };
  }

  function setComputing(on) {
    $('btn-audit').disabled = on;
    $('status-line').className = on ? 'status computing' : 'status';
    $('status-line').textContent = on ? 'Schreier–Sims 链构造与成员剥离中…' : '';
  }

  // 输入一旦变更，立即撤销旧结论
  function invalidate() {
    currentRequestId += 1; // 使任何在途旧回包失效
    latestResult = null;
    replay = null;
    $('result').innerHTML =
      '<p class="muted">规程已变更，旧结论已撤销。请重新发起审计。</p>';
    $('replay').classList.add('hidden');
  }

  function renderError(message) {
    latestResult = null;
    $('result').innerHTML =
      '<div class="error-box"><strong>无法发起审计：</strong>' + esc(message) + '</div>';
    $('replay').classList.add('hidden');
  }

  function renderChainTable(result) {
    let html =
      '<details class="chain-details"><summary>稳定子链诊断' +
      '（按端口标识排序的确定性 Schreier–Sims 链）</summary>';
    html +=
      '<table class="chain-table"><thead><tr><th>端口层</th><th>基点端口</th>' +
      '<th>轨道大小</th><th>强生成元数</th></tr></thead><tbody>';
    for (const row of result.chainSummary) {
      html +=
        '<tr><td>' + (row.level + 1) + '</td><td>' +
        esc(result.names[row.base]) + '</td><td>' + row.orbitSize +
        '</td><td>' + row.strongGeneratorCount + '</td></tr>';
    }
    html += '</tbody></table></details>';
    return html;
  }

  function factorBadges(result, word) {
    return word
      .map((tok) => {
        const k = Math.abs(tok) - 1;
        const inv = tok < 0;
        return (
          '<span class="factor' + (inv ? ' inv' : '') + '">' +
          esc(result.operationNames[k]) + (inv ? '⁻¹' : '') + '</span>'
        );
      })
      .join('<span class="dot">·</span>');
  }

  function renderFrozenSummary(result) {
    const f = result.frozenInput;
    if (!f) return '';
    const groupsLine = f.groupsEnabled
      ? f.groups.map((g) => '{' + g.map(esc).join('、') + '}').join('，')
      : '未启用';
    let html = '<details class="chain-details"><summary>本次结论冻结的输入摘要' +
      '（修改编组或原规程后旧结论立即失效）</summary><ul class="evidence">';
    html += '<li>端口：<span class="orbit">' + f.ports.map(esc).join('、') + '</span></li>';
    html += '<li>操作：<span class="orbit">' + f.operations.map(esc).join('、') + '</span></li>';
    html += '<li>目标：<span class="orbit">' +
      f.target.map((p) => esc(p.from) + '→' + esc(p.to)).join('，') + '</span></li>';
    html += '<li>校准编组：<span class="orbit">' + groupsLine + '</span></li>';
    html += '</ul></details>';
    return html;
  }

  function renderResidualGroups(result) {
    const moved = result.residualByGroup.filter((g) => g.moved);
    if (moved.length === 0) {
      return '<p class="muted">各组内残余换位均为恒等——操作链直接精确实现目标，无需组内重标。</p>';
    }
    // 把块内映射渲染成循环记号
    const cyclesOf = (g) => {
      const to = {};
      for (const m of g.mapping) to[m.from] = m.to;
      const seen = new Set();
      const cycles = [];
      for (const m of g.mapping) {
        const start = m.from;
        if (seen.has(start) || to[start] === start) continue;
        const cyc = [];
        let cur = start;
        while (!seen.has(cur)) {
          seen.add(cur);
          cyc.push(cur);
          cur = to[cur];
        }
        if (cyc.length >= 2) cycles.push(cyc);
      }
      return cycles
        .map((c) =>
          c.length === 2
            ? '<span class="b">' + esc(c[0]) + '↔' + esc(c[1]) + '</span>'
            : '<span class="b">(' + c.map(esc).join(' ') + ')</span>'
        )
        .join('，');
    };
    let html = '<h3>各组内残余换位（操作链送达后，组内重标即得目标）</h3><ul class="evidence">';
    for (const g of moved) {
      html +=
        '<li>校准组 <span class="orbit">{' + g.ports.map(esc).join('、') + '}</span> 内：' +
        cyclesOf(g) + '</li>';
    }
    html += '</ul>';
    return html;
  }

  function renderSetStabilizer(result) {
    if (!result.setStabilizer || !result.setStabilizer.length) return '';
    let html =
      '<details class="chain-details"><summary>集合稳定子 K = G ∩ H 诊断' +
      '（递归分块传送子 + Schreier 闭包，完备性 ' +
      (result.setStabilizerComplete ? '已校验' : '未通过') + '）</summary>';
    html +=
      '<table class="chain-table"><thead><tr><th>端口层</th><th>基点端口</th>' +
      '<th>K 轨道大小</th><th>可达同组点数</th><th>强生成元数</th></tr></thead><tbody>';
    for (const row of result.setStabilizer) {
      html +=
        '<tr><td>' + (row.level + 1) + '</td><td>' + esc(result.names[row.base]) + '</td><td>' +
        row.orbitSize + '</td><td>' + row.reachableOrbitSize + '</td><td>' +
        row.strongGeneratorCount + '</td></tr>';
    }
    html += '</tbody></table></details>';
    return html;
  }

  function renderResult(result) {
    const host = $('result');
    if (!result.ok) {
      let html =
        '<div class="error-box"><div class="verdict reject">结论已撤销 · 输入不合法</div>';
      html += '<ul class="error-list">';
      for (const e of result.errors) {
        html += '<li><span class="scope">[' + esc(e.scope) + ']</span> ' + esc(e.message) + '</li>';
      }
      html += '</ul></div>';
      host.innerHTML = html;
      $('replay').classList.add('hidden');
      return;
    }

    if (result.member) {
      const tol = !!result.tolerance;
      let html = tol
        ? '<div class="verdict pass">✓ 容差可导出（每组内部重标后可实现目标）</div>'
        : '<div class="verdict pass">✓ 可导出（目标属于生成元组生成的置换群）</div>';
      html +=
        '<p>目标可由下列<span class="b">操作因子链</span>实现' +
        (tol
          ? '（逐层分块传送子递归构造，端口仅被送入目标组对应轨道；链已逐操作乘回复核）：'
          : '（横截代表逐层复算，因子词已逐操作乘回校验）：') +
        '</p>';
      html += '<div class="factor-chain">' + factorBadges(result, result.factorWord) + '</div>';
      if (tol) {
        html += renderResidualGroups(result);
        html += renderSetStabilizer(result);
      }
      html += renderChainTable(result);
      html += renderFrozenSummary(result);
      host.innerHTML = html;
      setupReplay(result);
    } else {
      const ev = result.evidence;
      const tol = !!result.tolerance;
      let html = '<div class="verdict reject">✗ ' + (tol ? '容差不可导出' : '不可导出') + '</div>';
      html +=
        '<p>在第 <span class="b">' + (ev.level + 1) +
        '</span> 个端口层（基点端口 <span class="b">' + esc(ev.baseName) +
        '</span>）无法把端口送入目标编组：</p><ul class="evidence">';
      if (tol) {
        html +=
          '<li>该层稳定子作用下基点的允许轨道（端口）：<span class="orbit">' +
          (ev.allowedOrbitNames && ev.allowedOrbitNames.length
            ? ev.allowedOrbitNames.map(esc).join('、')
            : '∅（空）') + '</span></li>';
        if (ev.targetBlockPortNames) {
          html +=
            '<li>目标校准组（端口必须落入此组）：<span class="orbit">' +
            ev.targetBlockPortNames.map(esc).join('、') + '</span></li>';
        }
        if (ev.orbitDetail && ev.orbitDetail.length) {
          html +=
            '<li>该层 G 稳定子全轨道、对应来源端口及其块证据：<table class="chain-table">' +
            '<thead><tr><th>轨道点 y</th><th>来源端口 cur⁻¹(y)</th>' +
            '<th>来源所在块</th><th>是否在目标组</th></tr></thead><tbody>';
          for (const d of ev.orbitDetail) {
            html +=
              '<tr><td>' + esc(d.pointName) + '</td><td>' + esc(d.sourceName) +
              '</td><td>' + d.landsBlockId + '</td><td>' +
              (d.inTargetBlock ? '是' : '否') + '</td></tr>';
          }
          html += '</tbody></table></li>';
        }
        html +=
          '<li>允许轨道与目标组不相交 —— 横截代表无法把该基点端口送入目标编组，' +
          '故不存在任何能实现目标的操作串（即使允许组内任意重标）。</li>';
      } else {
        html +=
          '<li>该层稳定子作用下基点可达轨道（端口）：<span class="orbit">' +
          ev.orbitNames.map(esc).join('、') + '</span></li>';
        html +=
          '<li>当前残差中基点 <span class="b">' + esc(ev.baseName) +
          '</span> 的像为 <span class="b">' + esc(ev.attemptedImageName) +
          '</span>，不在上述轨道内 —— 横截代表无法消去该基点像，' +
          '故不存在能实现目标的任何操作串。</li>';
      }
      html += '</ul>';
      html += renderChainTable(result);
      html += renderFrozenSummary(result);
      host.innerHTML = html;
      $('replay').classList.add('hidden');
    }
  }

  // ---------- 逐步回放 ----------

  function stopPlay() {
    if (replay && replay.timer) {
      clearTimeout(replay.timer);
      replay.timer = null;
    }
  }

  function setupReplay(result) {
    const panel = $('replay');
    panel.classList.remove('hidden');
    stopPlay();
    replay = {
      steps: result.steps,
      pos: 0,
      names: result.names,
      tolerance: !!result.tolerance,
      groups: result.groupsSummary || [],
      timer: null,
    };
    renderReplay();

    $('btn-prev').onclick = () => {
      stopPlay();
      replay.pos = Math.max(0, replay.pos - 1);
      renderReplay();
    };
    $('btn-next').onclick = () => {
      stopPlay();
      replay.pos = Math.min(replay.steps.length - 1, replay.pos + 1);
      renderReplay();
    };
    $('btn-play').onclick = () => {
      if (replay.timer) {
        stopPlay();
        renderReplay();
        return;
      }
      const tick = () => {
        if (!replay) return;
        if (replay.pos >= replay.steps.length - 1) {
          stopPlay();
          renderReplay();
          return;
        }
        replay.pos += 1;
        replay.timer = setTimeout(tick, 850);
        renderReplay();
      };
      tick();
    };
    $('btn-reset').onclick = () => {
      stopPlay();
      replay.pos = 0;
      renderReplay();
    };
  }

  function renderReplay() {
    if (!replay) return;
    const { steps, pos, names } = replay;
    const step = steps[pos];
    let html = '<table class="port-table"><thead><tr><th></th>';
    for (const nm of names) html += '<th>' + esc(nm) + '</th>';
    html += '</tr></thead><tbody><tr>';
    html += '<td class="rowhead">当前接线</td>';
    for (let i = 0; i < names.length; i++) html += '<td>' + esc(names[step.perm[i]]) + '</td>';
    html += '</tr></tbody></table>';

    html += '<p class="muted">第 ' + pos + ' / ' + (steps.length - 1) + ' 步';
    if (pos > 0) {
      html +=
        '——刚执行：<span class="b">' + esc(steps[pos].operation) +
        (steps[pos].inverse ? '⁻¹' : '') + '</span>';
    } else {
      html += '（初始排列）';
    }
    html += '</p>';

    if (replay.tolerance && replay.pos === replay.steps.length - 1) {
      const groupsLine = replay.groups.length
        ? replay.groups.map((g) => '{' + g.map(esc).join('、') + '}').join('，')
        : '（全部单例）';
      html +=
        '<p class="muted">当前为操作链的送达状态：各端口已落入目标校准组 ' +
        '<span class="orbit">' + groupsLine + '</span> 的对应组；' +
        '再执行各组内部残余换位（见结论区）即得目标接线。</p>';
    }

    if (pos > 0) {
      const applied = [];
      for (let k = 1; k <= pos; k++) {
        applied.push(
          '<span class="factor' + (steps[k].inverse ? ' inv' : '') + '">' +
          esc(steps[k].operation) + (steps[k].inverse ? '⁻¹' : '') + '</span>'
        );
      }
      html += '<div class="factor-chain small">' + applied.join('<span class="dot">·</span>') + '</div>';
    }
    $('replay-view').innerHTML = html;
    $('btn-prev').disabled = pos <= 0;
    $('btn-next').disabled = pos >= steps.length - 1;
    $('btn-play').textContent = replay.timer ? '暂停' : '播放';
  }

  // ---------- 规程编辑行 ----------

  function addOpRow(name, mapping) {
    const wrap = $('ops');
    const row = document.createElement('div');
    row.className = 'op-row';
    row.innerHTML =
      '<input class="op-name" type="text" placeholder="操作名（如 swap_ab）" value="' +
      esc(name || '') + '" />' +
      '<input class="op-mapping" type="text" placeholder="(A B)(C D) 或 A-&gt;B, B-&gt;A" />';
    row.querySelector('.op-mapping').value = mapping || '';
    wrap.appendChild(row);
    row.querySelector('.op-name').addEventListener('input', invalidate);
    row.querySelector('.op-mapping').addEventListener('input', invalidate);
  }

  function fillExample() {
    $('ports').value = 'A B C D';
    $('ops').innerHTML = '';
    addOpRow('flip_cd', '(C D)');
    addOpRow('rotate', '(A B C D)');
    addOpRow('swap_ab', '(A B)');
    $('target').value = '(A C)(B D)';
    $('groups').value = '';
    invalidate();
  }

  function fillToleranceExample() {
    // C4 循环群只能整体旋转；把 {A B}、{C D} 各编为校准组后，
    // 目标 (A C) 可由 rotate³ 送达对应组，再组内重标导出。
    $('ports').value = 'A B C D';
    $('ops').innerHTML = '';
    addOpRow('rotate', '(A B C D)');
    $('target').value = '(A C)';
    $('groups').value = 'A B; C D';
    invalidate();
  }

  $('btn-add-op').addEventListener('click', () => {
    if (document.querySelectorAll('.op-row').length >= 8) return;
    addOpRow('', '');
    invalidate();
  });
  $('btn-remove-op').addEventListener('click', () => {
    const rows = document.querySelectorAll('.op-row');
    if (rows.length > 1) {
      rows[rows.length - 1].remove();
      invalidate();
    }
  });
  $('btn-audit').addEventListener('click', () => {
    const input = collectInput();
    currentRequestId += 1; // 新代次：所有在途旧回包将被丢弃
    latestResult = null;
    setComputing(true);
    ensureWorker().postMessage({
      type: 'audit-request',
      requestId: currentRequestId,
      input,
    });
  });
  $('btn-example').addEventListener('click', fillExample);
  $('ports').addEventListener('input', invalidate);
  $('target').addEventListener('input', invalidate);
  $('groups').addEventListener('input', invalidate);

  let btnTolExample = $('btn-tolerance-example');
  if (btnTolExample) btnTolExample.addEventListener('click', fillToleranceExample);

  fillExample();
})();
