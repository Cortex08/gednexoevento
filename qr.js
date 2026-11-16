/* ============================================================
   Gerador de QR Code — modo byte, correção nível M, versões 1 a 4.
   Escrito aqui porque a política de segurança da página (CSP) só
   aceita script do próprio domínio, sem CDN.
   Capacidade: até 62 caracteres — de sobra para um código de credencial.
   Uso:  QR.svg("GN-ABC-DEF")  ->  string SVG
   ============================================================ */
(function (global) {
  "use strict";

  /* ---------- aritmética no corpo de Galois GF(256) ---------- */
  var EXP = new Uint8Array(512), LOG = new Uint8Array(256);
  (function () {
    var x = 1;
    for (var i = 0; i < 255; i++) {
      EXP[i] = x; LOG[x] = i;
      x <<= 1; if (x & 0x100) x ^= 0x11D;
    }
    for (var j = 255; j < 512; j++) EXP[j] = EXP[j - 255];
  })();

  function mul(a, b) { return (a === 0 || b === 0) ? 0 : EXP[LOG[a] + LOG[b]]; }

  function genPoly(n) {
    var p = [1];
    for (var i = 0; i < n; i++) {
      var r = new Array(p.length + 1);
      for (var z = 0; z < r.length; z++) r[z] = 0;
      for (var a = 0; a < p.length; a++) {
        r[a]     ^= mul(p[a], 1);
        r[a + 1] ^= mul(p[a], EXP[i]);
      }
      p = r;
    }
    return p;
  }

  function ecBytes(data, n) {
    var g = genPoly(n), buf = data.slice(), i, j;
    for (i = 0; i < n; i++) buf.push(0);
    for (i = 0; i < data.length; i++) {
      var c = buf[i];
      if (!c) continue;
      for (j = 0; j < g.length; j++) buf[i + j] ^= mul(g[j], c);
    }
    return buf.slice(data.length);
  }

  /* ---------- tabela das versões (nível M) ---------- */
  var V = {
    1: { ec: 10, blocks: [16],    align: [] },
    2: { ec: 16, blocks: [28],    align: [6, 18] },
    3: { ec: 26, blocks: [44],    align: [6, 22] },
    4: { ec: 18, blocks: [32, 32], align: [6, 26] }
  };

  function capacidade(v) {
    var t = 0, b = V[v].blocks;
    for (var i = 0; i < b.length; i++) t += b[i];
    return t - 2;             // 2 bytes para cabeçalho (modo + contador)
  }

  /* ---------- texto -> bytes UTF-8 ---------- */
  function utf8(s) {
    var out = [], e = encodeURIComponent(String(s));
    for (var i = 0; i < e.length; i++) {
      if (e.charAt(i) === "%") { out.push(parseInt(e.substr(i + 1, 2), 16)); i += 2; }
      else out.push(e.charCodeAt(i));
    }
    return out;
  }

  /* ---------- palavras de dados ---------- */
  function dataCodewords(bytes, ver) {
    var total = 0, b = V[ver].blocks, i, j;
    for (i = 0; i < b.length; i++) total += b[i];

    var bits = [];
    function put(v, n) { for (var k = n - 1; k >= 0; k--) bits.push((v >>> k) & 1); }

    put(4, 4);                      // modo byte
    put(bytes.length, 8);           // contador (versões 1 a 9 usam 8 bits)
    for (i = 0; i < bytes.length; i++) put(bytes[i], 8);

    var max = total * 8;
    for (i = 0; i < 4 && bits.length < max; i++) bits.push(0);   // terminador
    while (bits.length % 8) bits.push(0);

    var cw = [];
    for (i = 0; i < bits.length; i += 8) {
      var v = 0;
      for (j = 0; j < 8; j++) v = (v << 1) | bits[i + j];
      cw.push(v);
    }
    var pad = [0xEC, 0x11], k = 0;
    while (cw.length < total) cw.push(pad[k++ % 2]);
    return cw;
  }

  function interleave(cw, ver) {
    var info = V[ver], blocks = [], ecs = [], off = 0, i, b;
    for (i = 0; i < info.blocks.length; i++) {
      var d = cw.slice(off, off + info.blocks[i]);
      off += info.blocks[i];
      blocks.push(d);
      ecs.push(ecBytes(d, info.ec));
    }
    var out = [], maxD = 0;
    for (i = 0; i < info.blocks.length; i++) maxD = Math.max(maxD, info.blocks[i]);
    for (i = 0; i < maxD; i++)
      for (b = 0; b < blocks.length; b++)
        if (i < blocks[b].length) out.push(blocks[b][i]);
    for (i = 0; i < info.ec; i++)
      for (b = 0; b < ecs.length; b++) out.push(ecs[b][i]);
    return out;
  }

  /* ---------- máscaras ---------- */
  function maskFn(k, r, c) {
    switch (k) {
      case 0: return (r + c) % 2 === 0;
      case 1: return r % 2 === 0;
      case 2: return c % 3 === 0;
      case 3: return (r + c) % 3 === 0;
      case 4: return (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0;
      case 5: return ((r * c) % 2) + ((r * c) % 3) === 0;
      case 6: return (((r * c) % 2) + ((r * c) % 3)) % 2 === 0;
      default: return ((((r + c) % 2) + ((r * c) % 3)) % 2) === 0;
    }
  }

  function formatBits(mask) {           // nível M = 00
    var data = (0 << 3) | mask, v = data << 10;
    for (var i = 14; i >= 10; i--) if (v & (1 << i)) v ^= 0x537 << (i - 10);
    return (((data << 10) | v) ^ 0x5412) & 0x7FFF;
  }

  /* ---------- montagem da matriz ---------- */
  function esqueleto(ver) {
    var n = 17 + 4 * ver, m = [], fn = [], i, j;
    for (i = 0; i < n; i++) {
      m.push(new Array(n)); fn.push(new Array(n));
      for (j = 0; j < n; j++) { m[i][j] = 0; fn[i][j] = 0; }
    }
    function set(r, c, v) {
      if (r < 0 || r >= n || c < 0 || c >= n) return;
      m[r][c] = v; fn[r][c] = 1;
    }

    // marcadores de posição e separadores
    [[0, 0], [0, n - 7], [n - 7, 0]].forEach(function (p) {
      for (var dr = -1; dr <= 7; dr++) for (var dc = -1; dc <= 7; dc++) {
        var anel  = (dr >= 0 && dr <= 6 && (dc === 0 || dc === 6)) ||
                    (dc >= 0 && dc <= 6 && (dr === 0 || dr === 6));
        var miolo = dr >= 2 && dr <= 4 && dc >= 2 && dc <= 4;
        set(p[0] + dr, p[1] + dc, (anel || miolo) ? 1 : 0);
      }
    });

    // linhas de sincronismo
    for (i = 8; i < n - 8; i++) { set(6, i, i % 2 === 0 ? 1 : 0); set(i, 6, i % 2 === 0 ? 1 : 0); }

    // padrões de alinhamento
    var AL = V[ver].align;
    for (i = 0; i < AL.length; i++) for (j = 0; j < AL.length; j++) {
      var r = AL[i], c = AL[j];
      if ((r === 6 && c === 6) || (r === 6 && c === n - 7) || (r === n - 7 && c === 6)) continue;
      for (var dr = -2; dr <= 2; dr++) for (var dc = -2; dc <= 2; dc++)
        set(r + dr, c + dc, Math.max(Math.abs(dr), Math.abs(dc)) !== 1 ? 1 : 0);
    }

    set(n - 8, 8, 1);                                   // módulo sempre escuro

    // reserva a área da informação de formato
    for (i = 0; i <= 8; i++) { fn[8][i] = 1; fn[i][8] = 1; }
    for (i = 0; i < 8; i++) { fn[8][n - 1 - i] = 1; fn[n - 1 - i][8] = 1; }

    return { n: n, m: m, fn: fn };
  }

  function colocarDados(est, cw, mask) {
    var n = est.n, m = est.m, fn = est.fn;
    var bits = [], i, j;
    for (i = 0; i < cw.length; i++) for (j = 7; j >= 0; j--) bits.push((cw[i] >>> j) & 1);

    var idx = 0, subindo = true;
    for (var col = n - 1; col > 0; col -= 2) {
      if (col === 6) col--;                              // pula a coluna de sincronismo
      for (var k = 0; k < n; k++) {
        var row = subindo ? (n - 1 - k) : k;
        for (var w = 0; w < 2; w++) {
          var cc = col - w;
          if (fn[row][cc]) continue;
          var bit = idx < bits.length ? bits[idx++] : 0;
          if (maskFn(mask, row, cc)) bit ^= 1;
          m[row][cc] = bit;
        }
      }
      subindo = !subindo;
    }
  }

  function colocarFormato(est, mask) {
    var n = est.n, m = est.m, f = formatBits(mask);
    for (var i = 0; i < 15; i++) {
      // a sequência de posições guarda do bit 14 ao bit 0, nessa ordem
      var bit = (f >>> (14 - i)) & 1;
      if (i < 6)       m[8][i] = bit;
      else if (i === 6) m[8][7] = bit;
      else if (i === 7) m[8][8] = bit;
      else if (i === 8) m[7][8] = bit;
      else              m[14 - i][8] = bit;

      // cópia 2: 7 bits na vertical (sem invadir o módulo escuro) e 8 na horizontal
      if (i < 7) m[n - 1 - i][8] = bit;
      else       m[8][n - 15 + i] = bit;
    }
  }

  /* ---------- pontuação das máscaras ---------- */
  function penalidade(m) {
    var n = m.length, p = 0, i, j, k;

    // regra 1: sequências de 5 ou mais módulos iguais
    for (i = 0; i < n; i++) {
      var rc = 1, cc = 1;
      for (j = 1; j < n; j++) {
        rc = (m[i][j] === m[i][j - 1]) ? rc + 1 : 1;
        if (rc === 5) p += 3; else if (rc > 5) p += 1;
        cc = (m[j][i] === m[j - 1][i]) ? cc + 1 : 1;
        if (cc === 5) p += 3; else if (cc > 5) p += 1;
      }
    }

    // regra 2: blocos 2x2 da mesma cor
    for (i = 0; i < n - 1; i++) for (j = 0; j < n - 1; j++) {
      var v = m[i][j];
      if (v === m[i][j + 1] && v === m[i + 1][j] && v === m[i + 1][j + 1]) p += 3;
    }

    // regra 3: padrão 1:1:3:1:1 com 4 claros de um lado
    var A = [1,0,1,1,1,0,1,0,0,0,0], B = [0,0,0,0,1,0,1,1,1,0,1];
    function bate(get, start, pat) {
      for (var t = 0; t < 11; t++) if (get(start + t) !== pat[t]) return false;
      return true;
    }
    for (i = 0; i < n; i++) {
      for (j = 0; j <= n - 11; j++) {
        var lin = (function (r) { return function (x) { return m[r][x]; }; })(i);
        var col = (function (c) { return function (x) { return m[x][c]; }; })(i);
        if (bate(lin, j, A) || bate(lin, j, B)) p += 40;
        if (bate(col, j, A) || bate(col, j, B)) p += 40;
      }
    }

    // regra 4: desvio da proporção de 50% de módulos escuros
    var escuros = 0;
    for (i = 0; i < n; i++) for (j = 0; j < n; j++) escuros += m[i][j];
    var pct = escuros * 100 / (n * n);
    p += Math.floor(Math.abs(pct - 50) / 5) * 10;

    return p;
  }

  /* ---------- API ---------- */
  function matrix(texto) {
    var bytes = utf8(texto), ver = 0;
    for (var v = 1; v <= 4; v++) if (bytes.length <= capacidade(v)) { ver = v; break; }
    if (!ver) throw new Error("Texto longo demais para o QR (máx. " + capacidade(4) + " bytes).");

    var cw = interleave(dataCodewords(bytes, ver), ver);

    var melhor = null, melhorP = Infinity;
    for (var mask = 0; mask < 8; mask++) {
      var est = esqueleto(ver);
      colocarDados(est, cw, mask);
      colocarFormato(est, mask);
      var p = penalidade(est.m);
      if (p < melhorP) { melhorP = p; melhor = est.m; }
    }
    return melhor;
  }

  function svg(texto, opts) {
    opts = opts || {};
    var m = matrix(texto),
        n = m.length,
        quiet = opts.quiet == null ? 4 : opts.quiet,
        total = n + quiet * 2,
        escuro = opts.dark  || "#06121F",
        claro  = opts.light || "#FFFFFF",
        d = "";

    for (var r = 0; r < n; r++) {
      var c = 0;
      while (c < n) {
        if (!m[r][c]) { c++; continue; }
        var ini = c;
        while (c < n && m[r][c]) c++;
        d += "M" + (ini + quiet) + " " + (r + quiet) + "h" + (c - ini) + "v1h-" + (c - ini) + "z";
      }
    }

    return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ' + total + ' ' + total +
           '" shape-rendering="crispEdges" role="img" aria-label="QR code da credencial">' +
           '<rect width="' + total + '" height="' + total + '" fill="' + claro + '"/>' +
           '<path d="' + d + '" fill="' + escuro + '"/></svg>';
  }

  // usado só pelos testes: monta com uma máscara fixa
  function matrixComMascara(texto, mask) {
    var bytes = utf8(texto), ver = 0;
    for (var v = 1; v <= 4; v++) if (bytes.length <= capacidade(v)) { ver = v; break; }
    var cw = interleave(dataCodewords(bytes, ver), ver);
    var est = esqueleto(ver);
    colocarDados(est, cw, mask);
    colocarFormato(est, mask);
    return est.m;
  }

  global.QR = { matrix: matrix, svg: svg, _comMascara: matrixComMascara, _penalidade: penalidade };

})(typeof window !== "undefined" ? window : this);
