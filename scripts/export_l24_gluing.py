#!/usr/bin/env python3
"""Propose explicit gluings for the unchanged L24 frame; Lean checks every graph.

The generator supplies spanning-tree choices, flag orders and component powers.
It never rewrites the held graphs or relation coefficients. Finite graph hints
are checked against the actual Lean gluing computation before use in a theorem.
"""
import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path

from export_admcycles_certificate import require, unique_object, vector
from export_l24_corrections import FRAME_IDS
from export_l24_initial import format_source, header, lean_hint

ROOT = Path(__file__).resolve().parents[1]
SOURCE_PINS = {
    "environments/l24-normalization-exploration.json": "227cd365a71aa1377c2b6c79c5a15b3217edbaf348cab6bcc8f4ab2c543cebe7",
    "AxiomaticGW/Tautological/L24Graphs.lean": "f54ac87da5e274687177227add9b009f1c1aadecc9addb1494939cdc74e0ade0",
    "AxiomaticGW/Tautological/Fixtures/L24CorrectionsReplay.lean": "3baaaad9de3b34b66bf0e79bf849322cbcae00119fa60505ed02fa3863e784b4",
    "scripts/export_l24_corrections.py": "6345849b3b85f02507feafe9692a3bea7b20298f13305be356e6dd0686d0229b",
    "scripts/export_l24_initial.py": "064788e008696675ebb30d6c047ef69c61c101b4bf95f9fa96b0c989f2ec39ec",
    "scripts/export_admcycles_certificate.py": "28b9d7b9c81d10ef241f6a7a9082cf29047967ddf03ddf1d4433057b6b8d05f8",
    "AxiomaticGW/Tautological/Fixtures/L24Claims.lean": "5727452cb886c8d9deb5d583c7f6293b037803a431b6c74fb4e272129042a74e"
}


def vec(values):
    return vector([str(x) for x in values])


def balanced(values, start=0):
    if all(v == values[0] for v in values):
        return values[0]
    middle = len(values) // 2
    return (f'(if i.val < {start + middle} then {balanced(values[:middle], start)} '
            f'else {balanced(values[middle:], start + middle)})')


@dataclass
class Component:
    vertices: list
    edges: list
    flags: list
    expression: str
    decoration: str
    decisions: str
    genus: int


class GluingBuilder:
    def __init__(self):
        self.permutations = {}

    def permutation(self, order):
        """Input order[new] = old; Lean expects the forward map old -> new."""
        require(sorted(order) == list(range(len(order))), 'Invalid flag permutation')
        forward = tuple(order.index(i) for i in range(len(order)))
        if list(forward) == list(range(len(order))):
            return None
        if forward not in self.permutations:
            self.permutations[forward] = f'flagPermutation{len(self.permutations)}'
        return self.permutations[forward]

    def decompose(self, graph):
        require(not any(any(p) for p in graph['kappa']), 'Kappa decoration needs another API')
        components = []
        for vertex, genus in enumerate(graph['genus']):
            flags = [('l', i) for i, v in enumerate(graph['leg_vertices']) if v == vertex]
            flags += [('h', e, b) for e, ends in enumerate(graph['endpoints'])
                      for b, v in enumerate(ends) if v == vertex]
            powers = [graph['leg_psi'][f[1]] if f[0] == 'l'
                      else graph['half_psi'][f[1]][f[2]] for f in flags]
            require(2 * genus - 2 + len(flags) > 0, 'Unstable component')
            expression = (f'(GluingExpression.fundamental {genus} (Fin {len(flags)}) '
                          '(by norm_num [StableArity]))')
            components.append(Component([vertex], [], flags, expression,
                                        vec(powers), 'inferInstance', genus))
        loops = []
        for edge, (left, right) in enumerate(graph['endpoints']):
            x = next(c for c in components if left in c.vertices)
            y = next(c for c in components if right in c.vertices)
            if x is y:
                loops.append(edge)
                continue
            i = x.flags.index(('h', edge, 0))
            j = y.flags.index(('h', edge, 1))
            merged = Component(
                x.vertices + y.vertices, x.edges + y.edges + [edge],
                x.flags[:i] + x.flags[i + 1:] + y.flags[:j] + y.flags[j + 1:],
                f'(join (m := {len(x.flags) - 1}) (n := {len(y.flags) - 1}) {i} {j}\n'
                f'    {x.expression}\n    {y.expression})',
                f'({x.decoration}, {y.decoration})',
                f'({x.decisions}, {y.decisions})', x.genus + y.genus)
            components = [c for c in components if c is not x and c is not y] + [merged]
        require(len(components) == 1, 'Disconnected graph')
        x = components[0]
        for edge in loops:
            first = [x.flags.index(('h', edge, b)) for b in (0, 1)]
            order = first + [i for i in range(len(x.flags)) if i not in first]
            name = self.permutation(order)
            if name:
                x.expression = f'({x.expression}.relabel {name})'
            x.expression = f'(close {x.expression})'
            x.flags = [x.flags[i] for i in order[2:]]
            x.edges.append(edge)
            x.genus += 1
        order = [x.flags.index(('l', i)) for i in range(len(graph['leg_vertices']))]
        name = self.permutation(order)
        if name:
            x.expression = f'({x.expression}.relabel {name})'
        require(x.genus == 2 and len(order) == 4, 'Wrong held genus or marking count')
        hint = dict(vertices=x.vertices, edges=x.edges, swaps=[False] * len(x.edges))
        return x.expression, x.decoration, x.decisions, hint


def generate():
    for name, expected in SOURCE_PINS.items():
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == expected,
                'Changed held source: ' + name)
    report = json.loads((ROOT / 'environments/l24-normalization-exploration.json').read_bytes(),
                        object_pairs_hook=unique_object)
    require(len(FRAME_IDS) == 815 and len(set(FRAME_IDS)) == 815, 'Changed held frame size')
    builder = GluingBuilder()
    terms = [builder.decompose(report['graphs'][i]) for i in FRAME_IDS]
    expressions = dict.fromkeys(t[0] for t in terms)
    expressions = {s: f'expression{i}' for i, s in enumerate(expressions)}
    text = header([
        'AxiomaticGW.Tautological.L24Graphs',
        'AxiomaticGW.Tautological.GetzlerGluing',
        'AxiomaticGW.Tautological.CotangentCombination',
        'AxiomaticGW.Tautological.GraphIsomorphismHint',
    ], '# Actual decorated gluings for the full L24 frame\n\n'
       'Every held column is built from stable components and the existing raw\n'
       'separating and nonseparating operations. Component powers are attached\n'
       'before nodes close. Explicit bijections check all incidences and powers\n'
       'against the independently held frame; no relation coefficient changes.', 'L24Gluing')
    text = text.replace('open RelationCertificate', 'open RelationCertificate GluingExpression GetzlerGraphs')
    for forward, name in builder.permutations.items():
        inverse = [forward.index(i) for i in range(len(forward))]
        text += (f'/-- Actual component-flag transport, before closing nodes or naming markings. -/\n'
                 f'def {name} : Equiv.Perm (Fin {len(forward)}) where\n'
                 f'  toFun := {vec(forward)}\n  invFun := {vec(inverse)}\n'
                 '  left_inv := by decide +kernel\n  right_inv := by decide +kernel\n\n')
    for expression, name in expressions.items():
        text += (f'/-- A shared raw gluing construction for the held four-marked frame. -/\n'
                 f'def {name} : GluingExpression 2 (Fin 4) :=\n  {expression}\n\n')
    for i, (expression, decoration, decisions, _) in enumerate(terms):
        text += (f'/-- Held column {i}, with all original external and node cotangent powers. -/\n'
                 f'def term{i} : CotangentTerm 2 (Fin 4) :=\n'
                 f'  ⟨{expressions[expression]}, {decoration}, {decisions}⟩\n\n')
    text += ('/-- All 815 actual constructions in exactly the existing column order. -/\n'
             'def term (i : Fin 815) : CotangentTerm 2 (Fin 4) :=\n  '
             + balanced([f'term{i}' for i in range(815)]) + '\n\n')
    text += ('/-- Proposed vertex and edge bijections, verified by the complete checker. -/\n'
             'def hint (i : Fin 815) : GraphIsomorphismHint :=\n  '
             + balanced([lean_hint(t[3]) for t in terms]) + '\n\n')
    text += '''/-- The kernel checks all decorations and node branches in every constructed graph. -/
theorem hints_valid : ∀ i, (hint i).check
    ((term i).expression.decoratedGraph (term i).decoration) (L24Graphs.graph i) = true := by
  decide +kernel

/-- Each constructed term denotes precisely the held raw graph class. -/
theorem term_stratum (i : Fin 815) :
    (term i).expression.decoratedStratum (term i).decoration = L24Graphs.columns i := by
  apply Quotient.sound
  exact (DecoratedStableGraph.isomorphic?_eq_true_iff _ _).mp
    (GraphIsomorphismHint.check_sound (hint i) _ _ (hints_valid i))

end AxiomaticGW.L24Gluing
'''
    return format_source(text), dict(columns=len(terms), expressions=len(expressions),
                                    flag_permutations=len(builder.permutations))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source, counts = generate()
    if args.check:
        require(args.output.read_text() == source, 'Stored gluing replay differs')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(source)
    print(json.dumps(counts, sort_keys=True))


if __name__ == '__main__':
    main()
