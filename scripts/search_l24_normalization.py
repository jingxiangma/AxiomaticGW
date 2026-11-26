#!/usr/bin/env python3
"""Explore the complete L24 correction without searching new 3-spin rows.

The four primitive diagrams are independently transcribed from Wennink.
Raw vertex substitution is checked against admcycles StableGraph.glue_vertex.
The entire candidate and operation provenance are retained. This search is
not itself a proof of the L24 class equation; see the report scope.
"""
import argparse
import hashlib
import importlib.metadata
import json
import os
import sys
import tempfile
import time
from pathlib import Path
from itertools import permutations, combinations
sys.dont_write_bytecode = True
from search_belorousski_pandharipande import key
ROOT = Path(__file__).resolve().parents[1]
start = time.monotonic()

def progress(s, **kw):
    print(json.dumps(dict(stage=s, seconds=round(time.monotonic() - start, 3), **kw)), flush=True)

def raw(term, n):
    G = term.gamma
    (ka, ps) = term.poly.monom[0]
    return dict(
        genus=list(map(int, G.genera())),
        leg_vertices=[int(G.vertex(l)) for l in range(1, n + 1)],
        endpoints=[[int(G.vertex(h)) for h in ed] for ed in G.edges()],
        kappa=[[int(p[j]) if j < len(p) else 0 for j in range(3)] for p in ka],
        leg_psi=[int(ps.get(l, 0)) for l in range(1, n + 1)],
        half_psi=[[int(ps.get(h, 0)) for h in ed] for ed in G.edges()])

def flags(g, v):
    # External markings first, then edge branches in the retained raw ordering.
    return ([('leg', i, 0) for i, x in enumerate(g['leg_vertices']) if x == v] +
            [('half', i, j) for i, e in enumerate(g['endpoints'])
             for j, x in enumerate(e) if x == v])

def power(g, f):
    return g['leg_psi'][f[1]] if f[0] == 'leg' else g['half_psi'][f[1]][f[2]]

def replace_raw(g, v, s, extra=None):
    fs = flags(g, v)
    assert len(fs) == len(s['leg_vertices'])
    pos = {f: j for (j, f) in enumerate(fs)}
    rest = [w for w in range(len(g['genus'])) if w != v]
    old = {w: i for (i, w) in enumerate(rest)}
    offset = len(rest)
    out = dict(genus=[g['genus'][w] for w in rest] + s['genus'],
               kappa=[g['kappa'][w] for w in rest] + s['kappa'],
               leg_vertices=[], leg_psi=[], endpoints=[], half_psi=[])
    extra = extra or [0] * len(fs)

    def get(f, w, p):
        if w != v:
            return (old[w], p)
        i = pos[f]
        return (offset + s['leg_vertices'][i], s['leg_psi'][i] + extra[i])
    for (i, (w, p)) in enumerate(zip(g['leg_vertices'], g['leg_psi'])):
        (w, p) = get(('leg', i, 0), w, p)
        out['leg_vertices'].append(w)
        out['leg_psi'].append(p)
    for (i, (e, ps)) in enumerate(zip(g['endpoints'], g['half_psi'])):
        pairs = [get(('half', i, j), w, p) for (j, (w, p)) in enumerate(zip(e, ps))]
        out['endpoints'].append([w for (w, p) in pairs])
        out['half_psi'].append([p for (w, p) in pairs])
    for (e, ps) in zip(s['endpoints'], s['half_psi']):
        out['endpoints'].append([offset + w for w in e])
        out['half_psi'].append(ps)
    return out

def boundary(n, A):
    return dict(genus=[0, 0], kappa=[[0] * 3, [0] * 3],
                leg_vertices=[int(i not in A) for i in range(n)],
                leg_psi=[0] * n, endpoints=[[0, 1]], half_psi=[[0, 0]])

def decorations(g, v):
    return sum((power(g, f) for f in flags(g, v)))

def primitive(g):
    return 2 in g['genus'] and all(
        h == 2 or (len(flags(g, v)) == 3 and decorations(g, v) == 0
                   and not any(g['kappa'][v])) for v, h in enumerate(g['genus']))

def run_search():
    from sage.all import QQ, vector, matrix
    from admcycles import TautologicalRing, admcycles, StableGraph, stable_graph, tautological_ring
    from sage.version import version
    from export_admcycles_certificate import require
    from export_genus_two_psi_pullbacks import SOURCE_PINS, PRODUCER_PINS
    require(version == '10.9' and importlib.metadata.version('admcycles') == '1.4', 'Changed environment')
    for (filename, digest) in SOURCE_PINS.items():
        require(hashlib.sha256((ROOT / 'environments' / filename).read_bytes()).hexdigest() == digest, 'Changed source file')
    for mod in (admcycles, stable_graph, tautological_ring):
        require(hashlib.sha256(Path(mod.__file__).read_bytes()).hexdigest() == PRODUCER_PINS[Path(mod.__file__).name], 'Changed producer')
    admcycles.set_online_lookup(False)
    admcycles.set_online_lookup_default(False)
    R = TautologicalRing(2, 4, moduli='st', base_ring=QQ)
    native_count = 0

    def native_graph(g, external=None, start=None):
        n = len(g['leg_vertices'])
        external = external or list(range(1, n + 1))
        start = start or n + 1
        ls = [[] for _ in g['genus']]
        ps = {}
        for (l, v, p) in zip(external, g['leg_vertices'], g['leg_psi']):
            ls[v].append(l)
            if p:
                ps[l] = p
        edges = []
        for (j, (edge, powers)) in enumerate(zip(g['endpoints'], g['half_psi'])):
            labels = [start + 2 * j, start + 2 * j + 1]
            edges.append(tuple(labels))
            for (l, v, p) in zip(labels, edge, powers):
                ls[v].append(l)
                if p:
                    ps[l] = p
        # Native constructors retain and mutate lists; never lend the held frame's lists.
        return (StableGraph(list(g['genus']), ls, edges, mutable=True), ps)

    def replace(g, v, s, extra=None):
        nonlocal native_count
        original = json.dumps((g, s), sort_keys=True)
        out = replace_raw(g, v, s, extra)
        fs = flags(g, v)
        n = len(g['leg_vertices'])
        labels = [f[1] + 1 if f[0] == 'leg' else n + 1 + 2 * f[1] + f[2] for f in fs]
        (G, pg) = native_graph(g)
        (H, ph) = native_graph(s, labels, 100)
        if extra:
            for (l, p) in zip(labels, extra):
                if p:
                    ph[l] = ph.get(l, 0) + p
        (vg, vs, dil) = ({}, {}, {})
        G.glue_vertex(v, H, vg, vs, dil)
        psi = {l: p for (l, p) in pg.items() if l not in labels}
        psi.update({dil.get(l, l): p for (l, p) in ph.items()})
        ka = [[0] * 3 for _ in G.genera()]
        for (old, new) in vs.items():
            ka[new] = list(g['kappa'][old])
        for (old, new) in vg.items():
            ka[new] = list(s['kappa'][old])
        native = R(G.copy(mutable=False), kappa=ka, psi=psi)
        require(len(native._terms) == 1, 'Unexpected native dimension collapse')
        term = next(iter(native._terms.values()))
        require(len(term.poly.monom) == 1 and list(term.poly.coeff) == [1],
                'Native substitution changed the raw monomial coefficient')
        nr = raw(term, n)
        require(key(out) == key(nr), 'Independent native graph substitution differs')
        require(json.dumps((g, s), sort_keys=True) == original, 'Native constructor mutated the source frame')
        native_count += 1
        return out
    classes = R.generators(3)
    graphs = [raw(next(iter(e._terms.values())), 4) for e in classes]
    keys = {key(g): i for (i, g) in enumerate(graphs)}
    assert len(keys) == 2090
    # Four primitive diagrams, followed by the average fixing marking 2.
    pictures = [
        (1, dict(genus=[2, 0, 0], leg_vertices=[1, 0, 2, 2],
                 endpoints=[[0, 1], [1, 2]], leg_psi=[0]*4, half_psi=[[1, 0], [0, 0]])),
        (3, dict(genus=[2, 0, 0], leg_vertices=[0, 2, 1, 2],
                 endpoints=[[0, 1], [1, 2]], leg_psi=[1, 0, 0, 0], half_psi=[[0, 0], [0, 0]])),
        (-3, dict(genus=[2, 0, 0], leg_vertices=[1, 1, 2, 2],
                  endpoints=[[0, 1], [0, 2]], leg_psi=[0]*4, half_psi=[[0, 0], [1, 0]])),
        (-3, dict(genus=[2, 0, 0, 0], leg_vertices=[1, 3, 2, 3],
                  endpoints=[[0, 1], [1, 2], [2, 3]], leg_psi=[0]*4, half_psi=[[0, 0]]*3))]
    for (c, g) in pictures:
        g['kappa'] = [[0] * 3 for _ in g['genus']]
    perms = []
    for a in permutations([0, 2, 3]):
        p = [0, 1, 0, 0]
        for (x, y) in zip([0, 2, 3], a):
            p[x] = y
        perms.append(p)

    def relabel(g, p):
        return dict(g, leg_vertices=[g['leg_vertices'][i] for i in p], leg_psi=[g['leg_psi'][i] for i in p])
    dest = [[keys[key(relabel(g, p))] for g in graphs] for p in perms]

    def average(row):
        out = vector(QQ, len(graphs))
        for ds in dest:
            for i in row.nonzero_positions():
                out[ds[i]] += row[i] / 6
        return out
    encode = lambda x: [int(QQ(x).numerator()), int(QQ(x).denominator())]
    sparse = lambda row: [[int(i), encode(row[i])] for i in row.nonzero_positions()]
    source = json.loads((ROOT / 'environments/belorousski-pandharipande.json').read_text())
    B = TautologicalRing(2, 3, moduli='st', base_ring=QQ)
    bp = B.from_vector(vector(QQ, [QQ(a) / b for (a, b) in source['requested']]), 2)
    pull = bp.forgetful_pullback([4]).rename_legs({1: 2, 2: 3, 3: 4, 4: 1}, inplace=False)
    # The existing BP frame sums six assignments; the paper uses the half-weighted relation.
    lifted = (pull * (-R.psi(1) + 3 * R.psi(2) + R.psi(3) + R.psi(4)) / 12).vector(3)
    current = average(lifted)
    initial = vector(QQ, current)
    steps = []
    sources = {}
    high = [i for (i, c) in enumerate(current) if c and any((h == 2 and decorations(graphs[i], v) >= 2 for (v, h) in enumerate(graphs[i]['genus'])))]
    progress('initial', terms=len(current.nonzero_positions()), high=len(high))
    for i in high:
        g = graphs[i]
        v = g['genus'].index(2)
        fs = flags(g, v)
        ps = [power(g, f) for f in fs]
        n = len(fs)
        assert sum(ps) == 2 and (not any(g['kappa'][v]))
        chosen = [j for (j, p) in enumerate(ps) if p]
        kind = 'square' if len(chosen) == 1 else 'product'
        m = len(chosen)
        order = chosen + [j for j in range(n) if j not in chosen]
        cachekey = (kind, n, tuple(order))
        if cachekey not in sources:
            data = json.loads((ROOT / f'environments/genus-two-psi-{kind}-exploration.json').read_text())
            S = TautologicalRing(2, m, moduli='st', base_ring=QQ)
            x = S.from_vector(vector(QQ, [QQ(a) / b for (a, b) in data['requested']]), 2)
            if n > m:
                x = x.forgetful_pullback(list(range(m + 1, n + 1)))
            x = x.rename_legs({j + 1: order[j] + 1 for j in range(n)}, inplace=False)
            vs = x.vector(2)
            cs = x.parent().generators(2)
            sources[cachekey] = [(vs[j], raw(next(iter(cs[j]._terms.values())), n)) for j in vs.nonzero_positions()]
        row = vector(QQ, len(graphs))
        for (c, s) in sources[cachekey]:
            row[keys[key(replace(g, v, s))]] += c
        assert row[i] == 1
        weight = -current[i]
        current += weight * row
        steps.append(dict(kind=kind, base=i, vertex=v, order=order, weight=encode(weight), row=sparse(row)))
    assert not any((c and any((h == 2 and decorations(graphs[i], v) >= 2 for (v, h) in enumerate(graphs[i]['genus']))) for (i, c) in enumerate(current)))
    progress('high_removed', terms=len(current.nonzero_positions()), steps=len(steps))
    while True:
        todo = next(((i, v) for i in current.nonzero_positions() if 2 in graphs[i]['genus'] for (v, h) in enumerate(graphs[i]['genus']) if h == 0 and decorations(graphs[i], v)), None)
        if todo is None:
            break
        (i, v) = todo
        g = graphs[i]
        fs = flags(g, v)
        n = len(fs)
        ps = [power(g, f) for f in fs]
        a = next((j for (j, p) in enumerate(ps) if p))
        assert n >= 4
        (b, c) = [j for j in range(n) if j != a][:2]
        others = [j for j in range(n) if j not in (a, b, c)]
        extra = ps[:]
        extra[a] -= 1
        row = vector(QQ, len(graphs))
        row[i] = 1
        for d in range(1, len(others) + 1):
            for comb in combinations(others, d):
                s = boundary(n, {a, *comb})
                out = replace(g, v, s, extra)
                row[keys[key(out)]] -= 1
        weight = -current[i]
        current += weight * row
        steps.append(dict(kind='rational_psi', base=i, vertex=v, flag=a, anchors=[b, c], weight=encode(weight), row=sparse(row)))
    progress('rational_removed', terms=len(current.nonzero_positions()), steps=len(steps), primitive_terms=sum((primitive(graphs[i]) for i in current.nonzero_positions())))
    target = vector(QQ, len(graphs))
    for (c, g) in pictures:
        for p in perms:
            target[keys[key(relabel(g, p))]] += QQ(c) / 6
    pri = [i for (i, g) in enumerate(graphs) if primitive(g)]
    current = average(current)
    progress('primitive_delta', terms=sum((current[i] != target[i] for i in pri)))
    wdvv = []
    baseclasses = R.generators(2)
    for (b, e) in enumerate(baseclasses):
        g = raw(next(iter(e._terms.values())), 4)
        if 2 not in g['genus'] or any((any(k) for k in g['kappa'])):
            continue
        for (v, h) in enumerate(g['genus']):
            if h != 0 or len(flags(g, v)) != 4 or decorations(g, v) != 0:
                continue
            channels = []
            for A in ({0, 1}, {0, 2}, {0, 3}):
                row = vector(QQ, len(graphs))
                row[keys[key(replace(g, v, boundary(4, A)))]] = 1
                channels.append(row)
            for c in (1, 2):
                wdvv.append(dict(base=b, graph=g, vertex=v, channel=c, row=average(channels[0] - channels[c])))
    rows = [current] + [d['row'] for d in wdvv]
    mat = matrix(QQ, [[row[i] for i in pri] for row in rows])
    rhs = vector(QQ, [target[i] for i in pri])
    progress('wdvv_solve', shape=mat.dimensions())
    try:
        w = mat.solve_left(rhs)
    except ValueError:
        progress('wdvv_insufficient', rank=mat.rank())
        raise
    result = sum((c * row for (c, row) in zip(w, rows)), vector(QQ, len(graphs)))
    assert all((result[i] == target[i] for i in pri))
    progress('complete', scale=str(w[0]), wdvv_selected=len(w.nonzero_positions()) - 1, terms=len(result.nonzero_positions()))
    payload = dict(
        graphs=graphs, initial=sparse(initial), steps=steps, normalization_scale=encode(w[0]),
        wdvv=[dict(base=d['base'], graph=d['graph'], vertex=d['vertex'], channel=d['channel'],
                   weight=encode(c), row=sparse(d['row'])) for c, d in zip(w[1:], wdvv) if c],
        full=sparse(result), primitive=sparse(target), permutations=perms)
    require(all((not any((any(k) for k in graphs[i]['kappa'])) and all((h < 2 or decorations(graphs[i], v) <= 1 for (v, h) in enumerate(graphs[i]['genus']))) for i in result.nonzero_positions())), 'Incomplete high-power elimination')
    require(w[0] == 1 and len(result.nonzero_positions()) == 721, 'Review changed normalization outcome')
    expr = R.from_vector(result, 3)
    diagnostics = [(expr * R.psi(1) ** 4).evaluate(), (expr * R.psi(2) ** 4).evaluate(), (expr * R.psi(1) ** 2 * R.psi(2) ** 2).evaluate()]
    require(all((x == 0 for x in diagnostics)), 'Intersection diagnostic failed')
    payload.update(
        schema_version=1, frame='l24_direct_normalization_exploration_v1',
        normalization='raw_gluing_pushforward', pictures=pictures, source_sha256=SOURCE_PINS,
        producer_sha256=PRODUCER_PINS, environment={'sage': version, 'admcycles': '1.4'},
        native_substitution_checks=native_count,
        intersection_diagnostics=[encode(x) for x in diagnostics],
        source='https://arxiv.org/html/2210.04038; sections 4 and 7.1',
        scope='Sage exploration only. The three psi pullbacks have separate Lean replay; '
              'the full 721-term L24 combination, contextual attachments and WDVV corrections '
              'are not yet Lean-certified. Original geometric validity remains explicit.')
    progress('validated', native_substitution_checks=native_count)
    return payload

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='gw-l24-normalize-') as tmp:
        for k in ('DOT_SAGE', 'ADMCYCLES_CACHE_DIR', 'MPLCONFIGDIR', 'XDG_CACHE_HOME'):
            p = Path(tmp) / k
            p.mkdir()
            os.environ[k] = str(p)
        (Path(os.environ['DOT_SAGE']) / 'admcycles').mkdir()
        result = run_search()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
if __name__ == '__main__':
    main()
