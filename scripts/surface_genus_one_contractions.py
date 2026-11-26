"""Untrusted intermediate contractions for smaller kernel proof steps.

The invariant candidates themselves come from the separate published
recurrence. Here the pinned admcycles frame supplies graph incidences;
Lean checks each resulting number against its own gluing expression.
"""

from fractions import Fraction
from functools import cache
import hashlib
from itertools import product
import json
from math import comb

import export_surface_genus_zero_tables as rational
from explore_surface_getzler import curve_assignments, SOURCE, SOURCE_SHA256
from explore_surface_degree_zero import constant_value


REPRESENTATIVES = dict(zip(
    ("delta22", "delta23", "delta24", "delta34", "delta03", "delta04", "deltaBeta"),
    (0, 3, 15, 21, 25, 29, 30)))
WEIGHTS = (Fraction(-9), Fraction(12), Fraction(3), Fraction(-6),
           Fraction(-1, 2), Fraction(-1, 8), Fraction(3, 4))


def contractions(target, elliptic, *, bound=rational.BOUND):
    data = SOURCE.read_bytes()
    if hashlib.sha256(data).hexdigest() != SOURCE_SHA256:
        raise ValueError("The pinned admcycles Getzler frame changed")
    frame = json.loads(data)
    genus_zero = rational.table(target, bound)
    rank = len(rational.TARGETS[target][2])
    dual = (2, 1, 0) + tuple(range(3, rank + 2))
    inverse = (1, 1, 1) + (-1,) * (rank - 1)

    @cache
    def vertex(genus, curve, labels):
        energy = rational.energy(target, curve)
        n = energy + genus - 1 + len(labels) - sum(
            {0: 0, 1: 1, 2: 2}.get(b, 1) for b in labels)
        if n < 0:
            return n, Fraction(0)
        if energy == 0:
            insertions = tuple((b, 0) for b in labels) + ((2, 0),) * n
            return n, constant_value(("ancestor", genus, curve, insertions), Fraction)
        value = (genus_zero if genus == 0 else elliptic)[curve]
        lattice = rational.lattice(target, curve)
        for b in labels:
            if b == 0:
                return n, Fraction(0)
            if b == 1:
                value *= lattice[0]
            elif b >= 3:
                value *= -lattice[b - 2]
        return n, value

    # Cache all state-labelled vertex data independently of the requested class.
    states_by_kind = {}
    for kind, index in REPRESENTATIVES.items():
        graph = frame["graphs"][index]
        vertices = len(graph["genus"])
        states = []
        for assignment in product(range(len(dual)), repeat=len(graph["endpoints"])):
            labels = [[] for _ in range(vertices)]
            for v in graph["leg_vertices"]:
                labels[v].append(1)
            weight = 1
            for b, (left, right) in zip(assignment, graph["endpoints"]):
                labels[left].append(b)
                labels[right].append(dual[b])
                weight *= inverse[b]
            states.append((weight, tuple(tuple(sorted(a)) for a in labels)))
        states_by_kind[kind] = graph, states

    result = {}
    for beta in rational.bounded(target, bound):
        energy = rational.energy(target, beta)
        if energy <= 1:
            continue
        n = energy - 2
        totals = []
        for graph, states in states_by_kind.values():
            value = Fraction(0)
            for curves in curve_assignments(beta, len(graph["genus"])):
                if any(g == 1 and rational.energy(target, c) == energy
                       for g, c in zip(graph["genus"], curves)):
                    continue  # The same elliptic pivot guard as in Lean.
                for weight, labels in states:
                    term, remaining = Fraction(weight), n
                    for g, c, a in zip(graph["genus"], curves, labels):
                        points, scalar = vertex(g, c, a)
                        if not scalar or not 0 <= points <= remaining:
                            break
                        term *= comb(remaining, points) * scalar
                        remaining -= points
                    else:
                        if remaining == 0:
                            value += term
            totals.append(value)
        if sum(w * c for w, c in zip(WEIGHTS, totals)) / 9 != elliptic[beta]:
            raise ValueError(f"Graph/intersection recurrence disagreement at {target}, {beta}")
        result[beta] = totals
    return result
