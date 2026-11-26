#!/usr/bin/env python3
"""Export untrusted BP initial hints and coefficients for offline Lean replay.

The held BP operations, auxiliary frame and final initialClaim are not rewritten.
Graph coverage, dimension soundness and complete coefficient equality are proved
in Lean. Native export and Python lookup/accumulation are outside that boundary.
"""
import argparse
import hashlib
import json
import re
from fractions import Fraction
from itertools import permutations
from pathlib import Path

from export_admcycles_certificate import require, unique_object
from export_l24_corrections import FRAME_IDS, balanced_coordinates
from test_l24_normalization import flags, key, power, relabel

ROOT = Path(__file__).resolve().parents[1]
SOURCE_PINS = {
    'environments/belorousski-pandharipande.json':
        '5868b2f3ef1e5a45e6175b6349566b72c778f4ab028ef941b43498fd0ee8d1bc',
    'environments/l24-normalization-exploration.json':
        '227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7',
    'environments/decorated-forgetful-exploration.json':
        '86cf72f217babf9b3deefe3d3fad443de0032ffe78dcc90c0d68e34c67601699',
    'environments/l24-initial-dimension-audit.json':
        '18a5848c5b2642127bcbfbb55ab8129bdd6ca92885d34e79e6d772ff5ef204ba',
    'AxiomaticGW/Tautological/L24Initial.lean':
        'ada19ad280fe716e84f76eef4117eb215a5d05c0798eaee202b91fc8a3011e6f',
    'AxiomaticGW/Tautological/L24InitialGraphs.lean':
        '43bad39c05289b7c27e57a287797872247b7208352202b8a8ae34c2dc181c55c',
    'AxiomaticGW/Tautological/Fixtures/L24CorrectionsReplay.lean':
        '3baaaad9de3b34b66bf0e79bf849322cbcae00119fa60505ed02fa3863e784b4',
    'AxiomaticGW/Tautological/Fixtures/L24Claims.lean':
        '5727452cb886c8d9deb5d583c7f6293b037803a431b6c74fb4e272129042a74e',
}

def context(raw):
    for name, expected in SOURCE_PINS.items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected,
                "Changed held source: " + name)
    payload = json.loads(raw, object_pairs_hook=unique_object)
    old = json.loads((ROOT / "environments/decorated-forgetful-exploration.json").read_bytes())
    require(hashlib.sha256(raw).hexdigest() == old["lean_payload_sha256"],
            "Native payload differs from the checked original export")
    bp = json.loads((ROOT / "environments/belorousski-pandharipande.json").read_bytes())
    report = json.loads((ROOT / "environments/l24-normalization-exploration.json").read_bytes())
    extra = json.loads((ROOT / "environments/l24-initial-dimension-audit.json").read_bytes())[
        "extra_columns_after_average_before_cancellation"]
    require(len(extra) == 45 and not set(extra) & set(FRAME_IDS), "Changed auxiliary frame")
    return payload, bp, report, list(FRAME_IDS) + extra

def rat(c):
    return str(c[0]) if c[1] == 1 else f'({c[0]} / {c[1]})'


def wrap(s, indent='  '):
    tokens = re.findall(r'\(by decide \+kernel\)|\(by norm_num \[StableArity\]\)|\S+', s)
    lines = []
    line = indent
    for tok in tokens:
        if len(line.rstrip()) + 1 + len(tok) > 96 and line.strip():
            lines.append(line.rstrip())
            line = indent + '  '
        if line.strip():
            line += ' '
        line += tok
    if line.strip():
        lines.append(line.rstrip())
    return '\n'.join(lines)


def format_source(s):
    return '\n'.join(
        wrap(line.strip(), line[:len(line) - len(line.lstrip())])
        if len(line) > 100 else line for line in s.splitlines()
    ) + '\n'


def header(imports, title, ns):
    return '\n'.join([
        '/-', 'Copyright (c) 2026 JMA. All rights reserved.',
        'Released under Apache 2.0 license as described in the file LICENSE.',
        'Authors: JMA', '-/', 'module', '',
    ] + ['public import ' + i for i in imports] + [
        '', '/-!', title, '-/', '', '@[expose] public section', '',
        'namespace AxiomaticGW.' + ns, 'open RelationCertificate', '',
        'set_option maxRecDepth 20000', '', '',
    ])


def iso_hint(G, H):
    v = len(G['genus'])
    e = len(G['endpoints'])
    require(v == len(H['genus']) and e == len(H['endpoints'])
            and G['leg_psi'] == H['leg_psi'], 'Incompatible graph sizes or leg powers')
    for vp in permutations(range(v)):
        if any(H['genus'][vp[i]] != G['genus'][i]
               or H['kappa'][vp[i]] != G['kappa'][i] for i in range(v)):
            continue
        if any(vp[a] != b for a, b in zip(G['leg_vertices'], H['leg_vertices'])):
            continue
        for ep in permutations(range(e)):
            swaps = []
            for j in range(e):
                good = [b for b in (0, 1) if all(
                    vp[G['endpoints'][j][k]] == H['endpoints'][ep[j]][k ^ b]
                    and G['half_psi'][j][k] == H['half_psi'][ep[j]][k ^ b]
                    for k in (0, 1))]
                if not good:
                    break
                swaps.append(bool(good[0]))
            else:
                return dict(vertices=list(vp), edges=list(ep), swaps=swaps)
    raise ValueError('No isomorphism')


def lean_hint(h):
    def nums(a):
        return '[' + ', '.join(str(x) for x in a) + ']'

    swaps = ', '.join('true' if x else 'false' for x in h['swaps'])
    return '⟨' + nums(h['vertices']) + ', ' + nums(h['edges']) + ', [' + swaps + ']⟩'


def raw_key(g):
    # This intentionally incomplete key proposes a hint; Lean checks every decoration.
    ns = ([len(g['genus']), len(g['endpoints'])] + g['genus'] + g['leg_vertices']
          + sum(g['endpoints'], []) + g['leg_psi'] + sum(g['half_psi'], []))
    h = 0
    for x in ns:
        h = (h * 37 + x + 1) % 2147483647
    return h


def produce(raw):
    payload, bp, report, all_ids = context(raw)
    graphs = report["graphs"]
    keys = {key(g): i for i, g in enumerate(graphs)}
    hints = {}
    records = [[] for _ in range(4)]
    seen = set()
    for case in payload['cases']:
        if case['additional_markings'] != 1 or not case['name'].startswith('bp_'):
            continue
        _, i, e = case['name'].split('_')
        i, e = int(i), int(e)
        seen.add((i, e))
        paper = bp['published_terms'][i]
        c = Fraction(*paper['coefficient']) / paper['automorphism']
        for term in case['terms']:
            raw_graph = dict(term['graph'])
            raw_graph.pop('codimension')
            raw_graph['kappa'] = [[0] * 3 for _ in raw_graph['genus']]
            raw_graph = relabel(raw_graph, [3, 0, 1, 2])
            for k in range(4):
                g = dict(raw_graph, leg_psi=raw_graph['leg_psi'][:])
                g['leg_psi'][k] += 1
                if any(sum(power(g, f) for f in flags(g, v))
                       > 3 * genus - 3 + len(flags(g, v))
                       for v, genus in enumerate(g['genus'])):
                    records[k].append((0, [0, 1]))
                    continue
                target = keys[key(g)]
                j = all_ids.index(target)
                hint = iso_hint(g, graphs[target])
                entry = (j, hint)
                h = raw_key(g)
                require(h not in hints or hints[h] == entry, 'Ambiguous candidate key')
                hints[h] = entry
                q = c * term['coefficient']
                records[k].append((j, [q.numerator, q.denominator]))
    require(seen == {(i, e) for i in range(20) for e in range(6)}, 'Missing BP assignment')
    require(all(len(row) == 306 for row in records), 'Changed pullback size')
    return hints, records

def tree(entries):
    if len(entries)==1:
        k,(j,h)=entries[0]
        return f'(if k = {k} then ⟨{j}, {lean_hint(h)}⟩ else ⟨0, ⟨[], [], []⟩⟩)'
    m=len(entries)//2
    return f'(if k < {entries[m][0]} then {tree(entries[:m])} else {tree(entries[m:])})'

def hints_source(hints):
    s=header(['AxiomaticGW.Tautological.L24InitialGraphs','AxiomaticGW.Tautological.L24Initial','AxiomaticGW.Tautological.CotangentDimensionReplay'], '# Candidate graph destinations for the BP initial row\n\nA small numeric key only selects a proposed destination and finite bijections.\nIt is not an isomorphism test: every retained term must separately pass all\nincidence, genus, kappa and cotangent checks. Missing keys return an invalid\nempty hint. Collisions cannot supply a proof of graph coverage.', 'L24InitialHints')
    s+='''/-- Quick incidence and cotangent key, with no mathematical authority on its own. -/
def graphKey (G : DecoratedStableGraph (Fin 4)) : ℕ :=
  ([G.graph.vertexCount, G.graph.edgeCount] ++
    (List.finRange G.graph.vertexCount).map G.graph.genus ++
    (List.finRange 4).map (fun i ↦ (G.graph.legVertex i).val) ++
    (List.finRange G.graph.edgeCount).flatMap
      (fun e ↦ [(G.graph.endpoint e 0).val, (G.graph.endpoint e 1).val]) ++
    (List.finRange 4).map G.legPsiPower ++
    (List.finRange G.graph.edgeCount).flatMap
      (fun e ↦ [G.halfEdgePsiPower e 0, G.halfEdgePsiPower e 1])).foldl
        (fun h n ↦ (h * 37 + n + 1) % 2147483647) 0

/-- An untrusted candidate table; full graph coverage supplies its meaning. -/
def lookupKey (k : ℕ) : Fin 860 × GraphIsomorphismHint :=
'''+wrap(tree(sorted(hints.items())))+'\n\n'
    s+='''/-- A proposed finite column, used only together with its coverage proof. -/
def columnIndex (G : DecoratedStableGraph (Fin 4)) : Fin 860 := (lookupKey (graphKey G)).1

/-- Proposed ordered bijections for the same candidate. -/
def hint (G : DecoratedStableGraph (Fin 4)) : GraphIsomorphismHint :=
  (lookupKey (graphKey G)).2

end AxiomaticGW.L24InitialHints
'''
    return format_source(s)

def replay_source(records):
    s=header(['AxiomaticGW.Tautological.L24InitialHints','AxiomaticGW.Tautological.StrataCoordinateRecords','AxiomaticGW.Tautological.Fixtures.L24CorrectionsReplay'], '# Exact BP initial coefficients and auxiliary cancellation\n\nThe proposed records retain all 306 signed terms for each of the four psi\ncontributions, including a zero marker for each justified dimension excess.\nThey must equal the actual Lean computation before arithmetic is used.\nThe final target is the unchanged, independently held initial L24 claim.', 'L24InitialReplay')
    coords=[]
    for k,row in enumerate(records):
        s+=f'set_option maxHeartbeats 800000 in\n-- Elaborating the 306 exact records exceeds the default declaration budget.\n/-- Proposed records for the psi-{k} term; no multiplicity is removed. -/\ndef records{k} : List (Fin 860 × ℚ) :=\n'+wrap(' ++ '.join('(['+', '.join(f'({i}, {rat(c)})' for i,c in row[start:start+51])+'] : List (Fin 860 × ℚ))' for start in range(0,len(row),51)))+'\n\n'
        s+=f'''/-- The records equal the actual dimension-pruned signed pullback computation. -/
theorem records{k}_checked : CotangentCombination.dimensionRecords
    L24InitialHints.columnIndex (Pi.single {k} 1) L24Initial.pullback =
    (records{k} : Multiset (Fin 860 × ℚ)) := by
  decide +kernel

'''
        q=[Fraction(0) for _ in range(860)]
        for i,c in row:q[i]+=Fraction(*c)
        coords.append(q)
        s+=f'/-- Proposed consolidated coefficients, before the weighted marking average. -/\ndef raw{k} : Coordinates 860 :=\n'+wrap(balanced_coordinates([[c.numerator,c.denominator] for c in q]))+'\n\n'
        s+=f'''/-- Kernel arithmetic adds every signed coefficient at its proposed destination. -/
theorem raw{k}_checked : StrataOperation.recordCoordinates records{k} = raw{k} := by
  decide +kernel

/-- Consolidation of the actual signed pullback contribution. -/
theorem coordinates{k}_checked :
    CotangentCombination.recordCoordinates (CotangentCombination.dimensionRecords
      L24InitialHints.columnIndex (Pi.single {k} 1) L24Initial.pullback) = raw{k} := by
  rw [records{k}_checked]
  simpa only [CotangentCombination.recordCoordinates, Multiset.map_coe, Multiset.sum_coe,
    StrataOperation.recordCoordinates_eq_sum] using raw{k}_checked

'''
    s+='/-- The four independently checked coordinate contributions. -/\ndef raw : Fin 4 → Coordinates 860 :=\n  ![raw0, raw1, raw2, raw3]\n\n'
    s+='''/-- The actual computed coordinate vector, including all dimension-pruning markers. -/
theorem coordinates_checked (k : Fin 4) :
    CotangentCombination.recordCoordinates (CotangentCombination.dimensionRecords
      L24InitialHints.columnIndex (Pi.single k 1) L24Initial.pullback) = raw k := by
  fin_cases k
'''
    for k in range(4):
        s+=f'  · exact coordinates{k}_checked\n'
    s+='\n'
    before=[sum(w*coords[k][j] for k,w in enumerate([-1,3,1,1]))/12 for j in range(860)]
    s+='/-- Exact coefficients of the weighted BP expression before averaging. -/\ndef beforeAverageClaim : Coordinates 860 :=\n'+wrap(balanced_coordinates([[c.numerator,c.denominator] for c in before]))+'\n\n'
    s+='''/-- All four cotangent contributions retain the original factor one twelfth. -/
theorem beforeAverage_checked :
    (1 / 12 : ℚ) • (∑ k : Fin 4, L24Initial.psiWeights k • raw k) = beforeAverageClaim := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero,
    L24Initial.psiWeights, raw, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  revert j
  decide +kernel

/-- Averaging cancels every auxiliary coefficient and recovers the held initial row. -/
theorem initial_checked : L24InitialGraphs.averageCoordinates beforeAverageClaim =
    L24InitialGraphs.extend L24CorrectionsReplay.initialClaim := by
  decide +kernel

/-- All signed multiplicities from the 120 original BP assignments survive. -/
theorem pullback_size : L24Initial.pullback.card = 306 := by
  decide +kernel

/-- Exactly 198 of the four weighted collections have a component dimension excess. -/
theorem pruned_count : (∑ k : Fin 4, (L24Initial.pullback.filter fun t ↦
    t.2.expression.exceedsComponentDimension t.2.decoration (Pi.single k 1) = true).card) =
    198 := by
  decide +kernel

end AxiomaticGW.L24InitialReplay
'''
    return format_source(s)

def replay_sources(raw):
    hints, records = produce(raw)
    return {"L24InitialHints.lean": hints_source(hints),
            "Fixtures/L24InitialReplay.lean": replay_source(records)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_payload", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, source in replay_sources(args.native_payload.read_bytes()).items():
        path = args.output_dir / name
        if args.check:
            require(path.read_text() == source, "Stored replay differs: " + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)


if __name__ == "__main__":
    main()
