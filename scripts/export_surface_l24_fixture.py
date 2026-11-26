#!/usr/bin/env python3
"""Emit untrusted column records for the fixed complete degree-zero L24 request.

Lean checks all 815 weighted columns, including zero columns, before collecting
the full equation. Input coefficients have no mathematical authority. The probe
uses the same surface algorithm and pinned query codecs as the full comparison.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from export_admcycles_certificate import require, unique_object
from export_surface_l24 import generate as comparison_program

ROOT = Path(__file__).resolve().parents[1]
SOURCE_PINS = {
    "AxiomaticGW/Surfaces/L24.lean": "77939b253b1097086ae853b18bfcfdc1b2d9a13f7b821229e3218e3e3c9804af",
    "AxiomaticGW/Surfaces/GenusTwoTerms.lean": "b5a926569f56ad80c0930c13ef61b722d62ebf5c0e10f1630e30c1885aff689f",
    "AxiomaticGW/Surfaces/DecoratedTermExpansion.lean": "88cacbaf7cd0231b35081b63b9bbdd5d6798e82abc6323dbaae19733d464f1d8",
    "AxiomaticGW/Tautological/L24Gluing.lean": "0bf7a0b35982faddbb69520c594a1e12061b3867121db9926daf090f278433c1",
    "AxiomaticGW/Tautological/Fixtures/L24CorrectionsReplay.lean": "3baaaad9de3b34b66bf0e79bf849322cbcae00119fa60505ed02fa3863e784b4",
    "scripts/export_surface_l24.py": "7381e36b46a31ae00de771c68e00777e04e33923b03fc7b46e3204ef39e006d8",
    "scripts/SurfaceBP.lean": "517b9cbdd9817728ad4f0762c77d178daf6169e1c9396b1653b7cae91cfc69e4",
    "AxiomaticGW/Tautological/Fixtures/L24Claims.lean": "5727452cb886c8d9deb5d583c7f6293b037803a431b6c74fb4e272129042a74e",
    "AxiomaticGW/Tautological/L24Terms.lean": "27b4f3725dd8c33f9c56cc003f309cafd8045c7112bedcaa24120ec298b0c4d3",
    "AxiomaticGW/Surfaces/L24Terms.lean": "e7027eb27e14c729e1e3e30954da27cca8ece2588c922463d157c97fe12a3e48",
    "AxiomaticGW/Surfaces/GenusTwoCachedTerms.lean": "52bd9fbe376f8209a94e1ed1d3e62f8f44840458c08da1b26ef75ee9d2be6b9c"
}

labels={0:'.unit',1:'.hyperplane',2:'.point'}
def key(q):
    require(q['genus'] == 2 and q['curve'] == [0], 'Changed residual request')
    ins=', '.join('⟨'+labels[l]+', '+str(p)+'⟩' for l,p in q['insertions'])
    return '⟨2, ![0], {'+ins+'}, by decide +kernel⟩'
def polynomial(terms):
    pieces=[]
    for t in terms:
        n,d=t['coefficient']; c=Fraction(n,d)
        require(bool(c) and len(t['monomial']) == 1, 'Changed nonzero affine column')
        pieces.append(f'({n}/{d}, {{{key(t["monomial"][0])}}})')
    return '{'+', '.join(pieces)+'}' if pieces else '0'

def check_sources():
    for name, expected in SOURCE_PINS.items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected,
                'Changed held source: ' + name)


def generate(payload):
    check_sources()
    rows = json.loads(payload, object_pairs_hook=unique_object)
    require(type(rows) is list and len(rows) == 815, 'Incomplete column coverage')
    require(all(type(r) is dict and set(r) == {'column', 'terms'} for r in rows),
            'Malformed column record')
    require(all(type(r['column']) is int for r in rows) and
            [r['column'] for r in rows] == list(range(815)), 'Changed column indices')
    for row in rows:
        require(type(row['terms']) is list, 'Malformed term list')
        for term in row['terms']:
            require(type(term) is dict and set(term) == {'coefficient', 'monomial'},
                    'Malformed term')
            c = term['coefficient']
            require(type(c) is list and len(c) == 2 and all(type(x) is int for x in c)
                    and c[1] > 0, 'Malformed exact coefficient')
            f = Fraction(*c)
            require(c == [f.numerator, f.denominator], 'Noncanonical rational')
            require(type(term['monomial']) is list and len(term['monomial']) == 1,
                    'Changed affine column')
            q = term['monomial'][0]
            require(type(q) is dict and set(q) == {'genus', 'curve', 'insertions'}
                    and type(q['genus']) is int and q['genus'] == 2
                    and type(q['curve']) is list and len(q['curve']) == 1
                    and type(q['curve'][0]) is int and q['curve'][0] == 0,
                    'Changed residual request')
            require(type(q['insertions']) is list and all(type(i) is list and len(i) == 2
                    and all(type(x) is int for x in i) and i[0] in labels and i[1] >= 0
                    for i in q['insertions']), 'Malformed insertion')
    text='''/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.L24

/-!
# A complete L24 surface coefficient check

Every held column is replayed separately before the full equation is collected.
The degree-zero plane example reproduces a residual genus-two dilaton equation;
it is a normalization regression, not a new invariant value or seed.
-/

@[expose] public section

namespace AxiomaticGW.SurfaceL24
open GluingExpression

set_option Elab.async false
set_option maxRecDepth 20000

/-- Collected equation for the four original states `H,H,1,1` in class zero. -/
def planeZero : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.term 1 {⟨2, ![0], {⟨.unit, 1⟩, ⟨.point, 0⟩}, by decide +kernel⟩} +
  RationalTerms.term (-3) {⟨2, ![0], {⟨.point, 0⟩}, by decide +kernel⟩}

private def planeZeroColumn (i : Fin 815) : RationalTerms (SurfaceAncestorKey .plane) :=
  RationalTerms.scale (L24CorrectionsReplay.fullClaim i)
    ((L24Gluing.term i).expression.surfaceDecoratedTerms .plane
      (SurfaceGenusTwo.vertexTerms .plane) (L24Gluing.term i).decoration 0 0
      ![.hyperplane, .hyperplane, .unit, .unit])

/-- Held uncollected contributions; zero columns and cancelling terms stay in the check. -/
private def planeZeroExpanded (i : Fin 815) : RationalTerms (SurfaceAncestorKey .plane) :=
'''
    for row in rows:
        if row['terms']:
            text+=f'  if i.val = {row["column"]} then\n    {polynomial(row["terms"])} else\n'
    text+='  0\n\n'
    for block,lo in enumerate(range(0,815,32)):
        hi=min(lo+32,815)
        text+=f'''set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- A bounded block keeps kernel memory independent of the complete equation size.
private theorem planeZero_block{block} : ∀ i : Fin 815,
    {lo} ≤ i.val → i.val < {hi} → planeZeroColumn i = planeZeroExpanded i := by
  decide +kernel

'''
    text+='''private theorem planeZero_columns_checked (i : Fin 815) :
    planeZeroColumn i = planeZeroExpanded i := by
'''
    for block,hi in enumerate(range(32,815,32)):
        lower='(Nat.zero_le _)' if block==0 else f'(Nat.le_of_not_gt h{block-1})'
        text+=f'  by_cases h{block} : i.val < {hi}\n  · exact planeZero_block{block} i {lower} h{block}\n'
    text+='  exact planeZero_block25 i (Nat.le_of_not_gt h24) i.isLt\n\n'
    text+='''private theorem planeZero_expanded_checked :
    L24Relation.genusTwoTerms .plane 0 0 0 ![.hyperplane, .hyperplane, .unit, .unit] =
      ∑ i, planeZeroExpanded i := by
  have hbind {α β : Type} (s : Multiset α) (f : α → Multiset β) :
      s.bind f = (s.map f).sum := by
    induction s using Multiset.induction_on with
    | empty => rfl
    | cons a s ih =>
      simp only [Multiset.cons_bind, Multiset.map_cons, Multiset.sum_cons, ih]
  have hsum : L24Relation.genusTwoTerms .plane 0 0 0
      ![.hyperplane, .hyperplane, .unit, .unit] = ∑ i, planeZeroColumn i := by
    simp only [L24Relation.genusTwoTerms, L24Relation.surfaceTerms,
      L24Relation.cotangentRelation, CotangentCombination.pullback, Multiset.bind_map,
      CotangentTerm.addMarkings, Multiset.map_singleton, Int.cast_one, mul_one,
      Multiset.bind_singleton]
    rw [hbind]
    simp only [← Finset.sum_eq_multiset_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : L24CorrectionsReplay.fullClaim i = 0
    · simp only [h, ne_eq, not_true_eq_false, if_false, planeZeroColumn,
        RationalTerms.scale, if_true]
    · rw [if_pos h]
      rfl
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ ↦ planeZero_columns_checked i)

set_option maxRecDepth 65536 in
/-- The executable full equation has exactly the held coefficients and residual queries. -/
theorem planeZero_checked : RationalTerms.Equivalent
    (L24Relation.genusTwoTerms .plane 0 0 0 ![.hyperplane, .hyperplane, .unit, .unit])
    planeZero := by
  rw [planeZero_expanded_checked]
  decide +kernel

end AxiomaticGW.SurfaceL24
'''
    return text

PROBE_BODY = r'''def columnJSON (i : Fin 815) : String :=
  let c := L24CorrectionsReplay.fullClaim i
  let t := L24Gluing.term i
  let p := RationalTerms.scale c
    (t.expression.surfaceDecoratedTerms .plane (SurfaceGenusTwo.vertexTerms .plane)
      t.decoration 0 0 ![.hyperplane, .hyperplane, .unit, .unit])
  "{\"column\":" ++ toString i.val ++ ",\"terms\":" ++ termsJSON p ++ "}"
end AxiomaticGW.SurfaceL24Export
open AxiomaticGW SurfaceL24Export

def main : IO Unit :=
  IO.println ("[" ++ String.intercalate "," ((List.finRange 815).map columnJSON) ++ "]")
'''


def native_program():
    check_sources()
    namespace = 'namespace AxiomaticGW.SurfaceL24Export\n'
    helpers = comparison_program().split(namespace, 1)[1].split('def caseJSON', 1)[0]
    # A standalone interpreted probe must load the imported bytecode as well as its interface.
    return ('import AxiomaticGW.Surfaces.L24Terms\nset_option maxRecDepth 20000\n\n'
            + namespace + helpers + PROBE_BODY)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--probe-output', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.probe_output:
        require(args.input is None and args.output is None, 'Choose one exporter mode')
        output, source = args.probe_output, native_program()
    else:
        require(args.input is not None and args.output is not None, 'Input and output required')
        output, source = args.output, generate(args.input.read_bytes())
    if args.check:
        require(output.read_text() == source, 'Stored L24 column source differs')
    else:
        output.write_text(source)


if __name__ == '__main__':
    main()
