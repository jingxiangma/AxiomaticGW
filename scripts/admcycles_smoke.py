#!/usr/bin/env python3
"""Check the pinned Sage/admcycles runtime using exact full-stable arithmetic.

Run with the installed Sage Python, for example:
    conda run -n axiomatic-gw-sage python scripts/admcycles_smoke.py

The JSON report includes explicit relation coefficients and a row-span
witness. This is a computational regression, not a Lean proof, a geometric
relation certificate, or a claim that the computed relations are complete.
The relation fixture is the admcycles 1.4 FZ_matrix(2, 2) upstream doctest:
https://gitlab.com/modulispaces/admcycles/-/blob/ea8abbb6245406c735e1d615841c41dcc83b590e/admcycles/DR/relations.py#L312
"""

import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import sys
import tempfile


EXPECTED_SAGE = "10.9"
EXPECTED_ADMCYCLES = "1.4"


def require(condition, message):
    """Keep checks active even when Python runs with optimization enabled."""
    if not condition:
        raise RuntimeError(message)


def digest(value):
    serialized = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(serialized.encode("utf-8")).hexdigest()


def run_checks():
    # These imports must follow cache isolation in main().
    from sage.all import QQ, ZZ, identity_matrix, matrix, vector
    from sage.version import version as sage_version
    from admcycles import TautologicalRing
    from admcycles.admcycles import (
        FZ_conjecture_holds,
        generating_indices,
        genstobasis,
        set_online_lookup,
        set_online_lookup_default,
    )
    from admcycles.DR.algebra import (
        convert_vector_to_monomial_basis,
        convert_vector_to_pushforward_basis,
    )
    from admcycles.DR.graph import all_strata
    from admcycles.DR.moduli import MODULI_ST
    from admcycles.DR.relations import FZ_matrix

    admcycles_version = importlib.metadata.version("admcycles")
    require(
        sage_version == EXPECTED_SAGE,
        f"Expected Sage {EXPECTED_SAGE}, found {sage_version}; "
        "review this fixture and environment lock before updating the pin.",
    )
    require(
        admcycles_version == EXPECTED_ADMCYCLES,
        f"Expected admcycles {EXPECTED_ADMCYCLES}, found {admcycles_version}; "
        "review the coordinate and relation APIs before updating the pin.",
    )

    # Both the active setting and persisted default are confined to this run.
    set_online_lookup(False)
    set_online_lookup_default(False)
    cached_functions = (generating_indices, genstobasis, FZ_conjecture_holds)
    require(
        all(not function.go_online for function in cached_functions),
        "admcycles relation lookup was not disabled",
    )

    def rational(q):
        q = QQ(q)
        return [int(q.numerator()), int(q.denominator())]

    def encoded_vector(values):
        return [rational(q) for q in values]

    def encoded_matrix(values):
        return [encoded_vector(row) for row in values.rows()]

    genus_one_integral = TautologicalRing(1, 1, moduli="st").kappa(1).evaluate()
    require(genus_one_integral == QQ(1) / 24, "Genus-one kappa integral is not 1/24")

    # Distinct external labels are used in general; here n=0, so no symmetry
    # quotient of the markings is involved. All computations retain the full
    # stable locus, including loop strata.
    genus, codimension, markings = 2, 2, ()
    relation_matrix = matrix(QQ, FZ_matrix(genus, codimension, markings, MODULI_ST))
    expected_matrix = matrix(QQ, [
        [60, -60, 84, 0, 6, 0, 0, 0],
        [473760, -100512, 33984, -10080, 6624, -10080, -288, -72],
        [115920, -12240, 13536, -5040, 1584, -5040, -144, -36],
        [0, 0, 102, -30, 0, 0, -3, 0],
        [0, 0, 30, 42, 0, 0, -3, 0],
        [0, 0, 0, 0, 66, -60, -6, -3],
        [0, 0, 0, 0, 15, 6, -21, -QQ(3) / 2],
    ])
    require(relation_matrix == expected_matrix, "Full-stable genus-two FZ fixture changed")

    # This nonzero target is specified independently of the generated matrix.
    # It equals row 0 + row 3/2 - 2*row 6/3 in the upstream fixture.
    target_pushforward = vector(QQ, [60, -60, 135, -15, -4, -4, QQ(25) / 2, 1])
    witness = relation_matrix.solve_left(target_pushforward)
    require(witness * relation_matrix == target_pushforward, "Invalid exact row-span witness")

    strata = all_strata(genus, codimension, markings, MODULI_ST)
    size = relation_matrix.ncols()
    require(len(strata) == size == 8, "Relation columns and raw strata do not agree")
    standard_basis = identity_matrix(QQ, size)

    def to_monomial(values):
        return vector(QQ, convert_vector_to_monomial_basis(
            values, genus, codimension, markings, MODULI_ST))

    def to_pushforward(values):
        return vector(QQ, convert_vector_to_pushforward_basis(
            values, genus, codimension, markings, MODULI_ST))

    pushforward_to_monomial = matrix(QQ, [to_monomial(e) for e in standard_basis.rows()])
    monomial_to_pushforward = matrix(QQ, [to_pushforward(e) for e in standard_basis.rows()])
    require(pushforward_to_monomial != standard_basis, "Fixture misses nontrivial kappa conversion")
    require(
        pushforward_to_monomial * monomial_to_pushforward == standard_basis
        and monomial_to_pushforward * pushforward_to_monomial == standard_basis,
        "Kappa coordinate conversions are not two-sided inverses",
    )
    monomial_relations = matrix(QQ, [to_monomial(row) for row in relation_matrix.rows()])
    require(
        monomial_relations == relation_matrix * pushforward_to_monomial,
        "Kappa conversion is not consistent on relation rows",
    )
    target_monomial = to_monomial(target_pushforward)
    require(to_pushforward(target_monomial) == target_pushforward, "Target round-trip failed")
    require(witness * monomial_relations == target_monomial, "Witness changed under coordinate conversion")

    ring = TautologicalRing(genus, len(markings), moduli="st", base_ring=QQ)
    generators = ring.generators(codimension)
    require(len(generators) == size, "Public generator count differs from raw strata")
    for index, generator in enumerate(generators):
        require(
            generator.vector(codimension) == standard_basis.row(index),
            f"Public generator {index} has a different raw coordinate index",
        )
        require(
            ring.from_vector(standard_basis.row(index), codimension).vector(codimension)
            == standard_basis.row(index),
            f"Raw coordinate round-trip failed for generator {index}",
        )
    require(
        ring.from_vector(target_monomial, codimension).vector(codimension) == target_monomial,
        "Public raw-vector round-trip reduced or changed the relation target",
    )

    # Store sparse polynomial coefficients with explicit exponents, not repr()
    # strings. Graph order is the pinned upstream order, not a Lean canonical
    # graph labeling. Empty term lists denote the zero polynomial.
    graph_coordinates = []
    for index, graph in enumerate(strata):
        graph_coordinates.append({
            "index": index,
            "rows": int(graph.M.nrows()),
            "columns": int(graph.M.ncols()),
            "matrix_polynomials": [
                [[[[int(power) for power in exponent], int(ZZ(coefficient))]
                  for exponent, coefficient in sorted(entry.dict().items())]
                 for entry in row]
                for row in graph.M.rows()
            ],
        })

    coordinates = {
        "genus": genus,
        "markings": list(markings),
        "codimension": codimension,
        "locus": "full_stable",
        "graph_encoding": "admcycles.DR.Graph.M; sorted sparse [exponent_tuple, integer_coefficient]",
        "polynomial_variables": list(strata[0].M.base_ring().variable_names()),
        "graphs": graph_coordinates,
        "pushforward_to_monomial": encoded_matrix(pushforward_to_monomial),
        "monomial_to_pushforward": encoded_matrix(monomial_to_pushforward),
    }
    arithmetic = {
        "rational_encoding": "[numerator, positive denominator]",
        "fz_rows_pushforward": encoded_matrix(relation_matrix),
        "fz_rows_monomial": encoded_matrix(monomial_relations),
        "target_pushforward": encoded_vector(target_pushforward),
        "target_monomial": encoded_vector(target_monomial),
        "row_combination_witness": encoded_vector(witness),
    }
    return {
        "schema_version": 1,
        "status": "passed",
        "scope": "Exact computational regression; not a Lean or geometric certificate; "
                 "no completeness claim for FZ relations.",
        "environment": {
            "sage": sage_version,
            "admcycles": admcycles_version,
            "python": platform.python_version(),
            "architecture": platform.machine(),
            "platform": platform.system(),
        },
        "cache": {"ephemeral": True, "relation_online_lookup": False},
        "genus_one_kappa_integral": rational(genus_one_integral),
        "checks": {
            "upstream_fz_fixture": True,
            "exact_row_span_witness": True,
            "two_sided_kappa_conversion": True,
            "raw_generator_round_trips": size,
            "raw_target_round_trip": True,
        },
        "raw_coordinate_sha256": digest(coordinates),
        "exact_arithmetic_sha256": digest(arithmetic),
        "coordinates": coordinates,
        "arithmetic": arithmetic,
    }


def main():
    with tempfile.TemporaryDirectory(prefix="axiomatic-gw-admcycles-smoke-") as temporary:
        # Set these before importing Sage or admcycles: both inspect cache
        # locations at import time. No existing user cache is read or updated.
        for variable, directory in (
            ("DOT_SAGE", "sage"),
            ("ADMCYCLES_CACHE_DIR", "admcycles"),
            ("MPLCONFIGDIR", "matplotlib"),
            ("XDG_CACHE_HOME", "xdg"),
        ):
            location = Path(temporary) / directory
            location.mkdir()
            os.environ[variable] = str(location)
        # admcycles 1.4 stores its lookup preference under DOT_SAGE even
        # when the relation cache is redirected with ADMCYCLES_CACHE_DIR.
        (Path(os.environ["DOT_SAGE"]) / "admcycles").mkdir()
        report = run_checks()
        print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"admcycles smoke test FAILED: {type(error).__name__}: {error}", file=sys.stderr)
        raise
