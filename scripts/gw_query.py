#!/usr/bin/env python3
"""Compute a surface GW query and have Lean check the exported exact answer."""
import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
import os
from operator import index
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile

from check_gkm_inputs import unique_object
from genus_two_zero_divisor_pairs import accepts as accepts_zero_divisor_pair

ROOT = Path(__file__).resolve().parents[1]
SURFACES = {"X0": ("plane", (3,)), "X1": ("hirzebruchOne", (1, 2)),
            "X2": ("blowupTwo", (1, 1, 1))}
LABELS = {"unit": ".unit", "H": ".hyperplane", "pt": ".point",
          "E1": ".exceptional 0", "E2": ".exceptional 1"}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def natural(value):
    """Normalize exact Python or Sage integers before serializing the request."""
    try:
        n = index(value)
    except TypeError:
        raise ValueError("Expected a nonnegative integer") from None
    if isinstance(value, bool) or n < 0:
        raise ValueError("Expected a nonnegative integer")
    return n


def validate(q):
    if type(q) is not dict or set(q) != {"target", "genus", "class", "insertions"}:
        raise ValueError("Expected target, genus, class and ordered insertions")
    if type(q["target"]) is not str or q["target"] not in SURFACES:
        raise ValueError("Expected X0, X1 or X2")
    surface, weights = SURFACES[q["target"]]
    g, beta, marks = q["genus"], q["class"], q["insertions"]
    g = natural(g)
    if g > 2:
        raise ValueError("Supported genera are 0, 1 and 2")
    if not isinstance(beta, list) or len(beta) != len(weights):
        raise ValueError("Expected full nonnegative effective-class coordinates")
    beta = [natural(coordinate) for coordinate in beta]
    basis = {"unit", "H", "pt"} | {f"E{i}" for i in range(1, len(weights))}
    if not isinstance(marks, list) or not all(
            isinstance(m, list) and len(m) == 2 and type(m[0]) is str and
            m[0] in basis for m in marks):
        raise ValueError("Expected ordered [basis label, nonnegative psi power] insertions")
    marks = [[label, natural(power)] for label, power in marks]
    if not any(beta) and 2 * g + len(marks) <= 2:
        raise ValueError("Degree zero at unstable curve arity is outside the geometric domain")
    return ({"target": q["target"], "genus": g, "class": beta, "insertions": marks},
            surface, sum(i * w for i, w in zip(beta, weights)))


@dataclass(frozen=True)
class Route:
    module: str
    candidate: str                     # closed Option ℚ expression in the request namespace
    conclusion: str                    # VALUE is replaced by the verified rational literal
    proof: str
    interpretation: str               # public theorem exposing the geometric inputs
    derivation: str
    canonical_state: str = ""
    descendant_witness: str = ""


def canonical_family(marks, energy):
    """Identify a possible canonical query. Lean checks the complete ordered request."""
    if len(marks) == energy + 1 and all(mark == ["pt", 0] for mark in marks):
        return ".primary"
    if not marks or any(mark != ["pt", 0] for mark in marks[1:]):
        return None
    label, power = marks[0]
    if power != 1:
        return None
    if label == "pt" and len(marks) - 1 == max(energy - 1, 0):
        return ".point"
    if len(marks) - 1 == energy:
        return {"H": ".hyperplane", "E1": ".exceptional 0", "E2": ".exceptional 1"}.get(label)
    return None


def checked_row_route(module, fixture, row, frame_name, *, witness=None):
    witness = witness or f"{fixture}.accepted {row}"
    proof = (f"have hq : request = {fixture}.requests {row} := by decide +kernel\n"
             f"  have hv : {fixture}.values {row} = VALUE := by decide +kernel\n"
             f"  rw [hq, ← hv]\n  exact {witness}")
    return Route(module, f"some ({fixture}.values {row})",
                 "SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 request VALUE", proof,
                 "SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry",
                 f"The {frame_name} reconstruction certificate matches the complete ordered request.",
                 descendant_witness="certified")


def pair_route(module, fixture, args, accepted, operation, reason):
    """The candidate and proof use the same explicitly indexed row and ordered query."""
    proof = (f"have hq : request = {fixture}.requests {args} := by decide +kernel\n"
             f"  rw [hq]\n  exact ({accepted}).trans (by decide +kernel)")
    return Route(module, f"some ({fixture}.values {args})",
                 f"SurfaceGenusTwo.{operation} 0 request = some VALUE", proof,
                 "SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry",
                 reason, descendant_witness=f".{operation.removesuffix('Value?')} certified")


def blowup_pair_route(q):
    from gkm_genus_two_unit_pairs import FAMILIES as unit_groups, pairs as unit_pairs
    from gkm_genus_two_divisor_pairs import FAMILIES as divisor_groups, pairs as divisor_pairs
    from gkm_genus_two_positive_pairs import FAMILIES as positive_groups, STATES

    marks = q["insertions"]
    ordered = (tuple(q["class"]), tuple(m[1] for m in marks), tuple(m[0] for m in marks))
    for group, target, _, singles in unit_groups:
        if target == q["target"]:
            for j, single in enumerate(singles):
                options = unit_pairs(single)
                if ordered in options:
                    args = f"{j} {options.index(ordered)}"
                    fixture = f"GKM.GenusTwoUnitPairs.{group}"
                    module = ("GKM.Fixtures.BlowupTwoLineCompletedReplay" if group == "StrictLinePoint"
                              else "GKM.Fixtures.GenusTwoUnitPairReplay")
                    return pair_route(module, fixture, args, f"({fixture}.accepted {args}).2", "unitPairValue?",
                                      "The ordered string or dilaton equation reduces to a certified singleton.")
    for group, target, _, singles, divisors in divisor_groups:
        if target == q["target"]:
            for j, single in enumerate(singles):
                for d, label in enumerate(divisors):
                    options = divisor_pairs(single, label)
                    if ordered in options:
                        args = f"{j} {d} {options.index(ordered)}"
                        fixture = f"GKM.GenusTwoDivisorPairs.{group}"
                        strict = group == "StrictLine"
                        module = ("GKM.Fixtures.BlowupTwoLineCompletedReplay" if strict
                                  else "GKM.Fixtures.GenusTwoDivisorPairReplay")
                        theorem = "all_accepted" if strict else "accepted"
                        accepted = f"({fixture}.{theorem} {args}).2"
                        return pair_route(module, fixture, args, accepted, "divisorPairValue?",
                                          "The divisor equation includes the signed cup-product correction.")
    if all(label in STATES[q["target"]][1:] and power == 1 for label, power in marks):
        for group, target, _, beta in positive_groups:
            if target == q["target"] and beta == ordered[0]:
                j, k = (STATES[target].index(label) for label, _ in marks)
                fixture = f"GKM.GenusTwoPositivePairs.{group}"
                proof = (f"have hq : request = {fixture}.requests {j} {k} := by decide +kernel\n"
                         f"  rw [hq]\n  exact ({fixture}.divisors_accepted {j-1} {k-1}).trans "
                         "(by decide +kernel)")
                return Route("GKM.Fixtures.GenusTwoPositivePairReplay", f"some ({fixture}.values {j} {k})",
                             "SurfaceGenusTwoBlowupDescendants.queryValue? 0 request = some VALUE", proof,
                             "SurfaceGenusTwoBlowupDescendantReconstruction.queryValue?_eq_checkedEval_from_geometry",
                             "The two cotangent powers use the 25-graph product relation and rational-tail calibration.")
    return None


def select(q, surface, energy):
    g, marks = q["genus"], q["insertions"]
    X = "SurfaceTarget." + surface
    weight = sum(power + {"unit": 0, "pt": 2}.get(label, 1) for label, power in marks)
    if weight != energy + g - 1 + len(marks):
        return Route("Surfaces.DimensionVanishing", "request.dimensionVanishing?",
                     "request.dimensionVanishing? = some VALUE", "decide +kernel",
                     "SurfaceQuery.dimensionVanishing?_sound",
                     "The total insertion codimension differs from the signed virtual dimension.")
    family = canonical_family(marks, energy) if g == 2 else None
    if g < 2:
        ns = ("SurfaceGenusZero", "SurfaceGenusOne")[g]
        prefix = ("GenusZero", "GenusOne")[g]
        if 0 < energy <= 12 and marks == [["pt", 0]] * (energy + g - 1):
            count = f"({X}.effective.energy request.beta" + (" - 1)" if g == 0 else ")")
            binding = f"request = SurfaceQuery.points {X} {g} request.beta {count}"
            return Route(f"Surfaces.{prefix}Benchmarks", f"{ns}.pointBenchmark? {X} request.beta",
                         f"{binding} ∧ {ns}.pointValue {X} request.beta = VALUE",
                         "constructor\n  · decide +kernel\n  · exact (" + ns +
                         ".pointBenchmark?_sound _ _ _ (by decide +kernel)).2.2",
                         ns + ".pointBenchmark_checkedEval",
                         "The full request matches the point benchmark. Its bounded table replays "
                         + ("the WDVV equations." if g == 0 else "the WDVV and Getzler equations."))
        evaluator = ns + ".queryValue? request"
        module = "Surfaces." + ("GenusZeroFullDescendants", "GenusOneDescendants")[g]
        geometry = ns + ".queryValue?_eq_checkedEval"
    elif energy == 0 and len(marks) == 1 and marks[0][1] >= 2:
        evaluator = "SurfaceGenusTwo.degreeZeroOnePointQueryValue? request"
        if marks == [["unit", 2]]:
            section = {"X0": "Plane", "X1": "OneBlowup", "X2": "TwoBlowups"}[q["target"]]
            fixture = "GKM.GenusTwoDegreeZeroReplay." + section
            return Route("GKM.Fixtures.GenusTwoDegreeZeroReplay", f"some ({fixture}.values 0)",
                         evaluator + " = some VALUE",
                         f"exact {fixture}.accepted 0",
                         "SurfaceGenusTwo.degreeZeroOnePointQueryValue?_sound",
                         "Degree-zero rational tails vanish. The checked one-point ancestor supplies the value.")
        module = "Surfaces.GenusTwoDegreeZeroDescendants"
        geometry = "SurfaceGenusTwo.degreeZeroOnePointQueryValue?_sound"
    elif q["target"] == "X0":
        ns = "BelorousskiPandharipande"
        evaluator = ns + ".planeQueryValue? request"
        geometry = ns + ".planeQueryValue?_eq_checkedEval"
        if 0 < energy <= 4 and len(marks) <= 2 and sum(
                {"unit": 0, "H": 1, "pt": 2}[s] + k for s, k in marks) == energy + 1 + len(marks):
            return Route("Surfaces.PlaneGenusTwoFewMarkingBenchmarks",
                         "SurfaceGenusTwo.planeFewMarkingBenchmark? request",
                         evaluator + " = some VALUE",
                         "exact SurfaceGenusTwo.planeFewMarkingBenchmark?_sound _ _ (by decide +kernel)",
                         geometry, "Full-query lookup followed by the proved plane BP and descendant reductions.")
        if 0 < energy <= 12 and family:
            return Route("Surfaces.PlaneGenusTwoBenchmarks",
                         "SurfaceGenusTwo.planeCanonicalBenchmark? request",
                         ns + ".planeCheckCanonicalClaim 4 PlaneGenusTwoScalarTable.values request VALUE = true",
                         "exact SurfaceGenusTwo.planeCanonicalBenchmark?_sound _ _ (by decide +kernel)",
                         ns + ".planeCheckCanonicalClaim_checkedEval_from_geometry",
                         "The complete degree-four BP table certifies this primary or first-descendant request.")
        module = "Surfaces.PlaneGenusTwoDescendants"
    else:
        ns = "SurfaceGenusTwoBlowupDescendants"
        evaluator = ns + ".queryValue? 0 request"
        geometry = "SurfaceGenusTwoBlowupDescendantReconstruction.queryValue?_eq_checkedEval_from_geometry"
        module = "Surfaces.GenusTwoBlowupDescendantReconstruction"
        beta = q["class"]
        if energy == 1 and len(marks) == 2:
            pair = blowup_pair_route(q)
            if pair is not None:
                return pair
        if q["target"] == "X2" and beta == [1, 1, 0] and len(marks) <= 2:
            from gkm_bl2_mixed_exceptional import REQUESTS
            ordered = (tuple(beta), tuple(k for _, k in marks), tuple(label for label, _ in marks))
            if ordered in REQUESTS["X2"]:
                return checked_row_route("GKM.Fixtures.BlowupTwoMixedExceptionalReplay",
                                         "GKM.BlowupTwoMixedExceptional", REQUESTS["X2"].index(ordered),
                                         "mixed exceptional")
        if q["target"] == "X2" and beta in ([2, 0, 0], [0, 2, 0]) and marks != [["pt", 2]]:
            import gkm_bl2_double_exceptional_pairs as pairs
            import gkm_bl2_double_exceptional_singletons as singles
            ordered = (tuple(beta), tuple(k for _, k in marks), tuple(label for label, _ in marks))
            for packet in (singles, pairs):
                if ordered in packet.REQUESTS["X2"]:
                    return checked_row_route(f"GKM.Fixtures.{packet.NAMESPACE}", f"GKM.{packet.NAMESPACE}",
                                             packet.REQUESTS["X2"].index(ordered), "double exceptional")
        if q["target"] == "X2" and energy == 2 and beta[2] > 0 and len(marks) == 1:
            from gkm_bl2_positive_plane_energy_two import REQUESTS
            ordered = (tuple(beta), (marks[0][1],), (marks[0][0],))
            row = REQUESTS["singletons"]["X2"].index(ordered)
            if beta == [0, 0, 2]:
                return checked_row_route("GKM.Fixtures.BlowupTwoDoubleLineReplay", "GKM.BlowupTwoDoubleLineReplay",
                                         row, "double strict line")
            return checked_row_route("GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoReplay",
                                     "GKM.BlowupTwoPositivePlaneEnergyTwoSingletons", row, "ruling singleton")
        fiber = q["target"] == "X1" and beta == [0, 1]
        double_exceptional = q["target"] == "X1" and beta == [2, 0]
        if (fiber or double_exceptional) and len(marks) == 2:
            from gkm_f1_energy_two import DOUBLE_PAIRS, FIBER_PAIRS
            frame = FIBER_PAIRS if fiber else DOUBLE_PAIRS
            ordered = (tuple(beta), tuple(k for _, k in marks), tuple(label for label, _ in marks))
            if ordered in frame.requests["X1"]:
                return checked_row_route(f"GKM.Fixtures.{frame.namespace}Replay", f"GKM.{frame.namespace}",
                                         frame.requests["X1"].index(ordered), "energy-two")
        if (energy == 1 or fiber or double_exceptional) and len(marks) == 1:
            labels = ["unit", "H", *[f"E{i}" for i in range(1, len(beta))], "pt"]
            label, power = marks[0]
            if power == energy + 2 - {"unit": 0, "pt": 2}.get(label, 1):
                if fiber or double_exceptional:
                    family_name = "F1FiberOneMarking" if fiber else "F1DoubleExceptionalOneMarking"
                    fixture = "GKM." + family_name
                    module = f"GKM.Fixtures.{family_name}Replay"
                    row = str(labels.index(label))
                    accepted = f"{fixture}.accepted {row}"
                elif beta[-1] == 0:
                    section = "OneBlowup" if q["target"] == "X1" else "TwoBlowups"
                    row = str(beta.index(1) * len(labels) + labels.index(label))
                    fixture = "GKM.GenusTwoOneMarking." + section
                    module = "GKM.Fixtures.GenusTwoOneMarkingReplay"
                    accepted = f"{fixture}.accepted {row}"
                else:
                    fixture = "GKM.BlowupTwoLineOneMarkingReplay"
                    module = "GKM.Fixtures.BlowupTwoLineCompletedReplay"
                    row = str(labels.index(label))
                    accepted = f"{fixture}.all_accepted {row}"
                proof = (f"have hq : request = {fixture}.requests {row} := by decide +kernel\n"
                         f"  rw [hq]\n  exact ({accepted}).trans (by decide +kernel)")
                return Route(module, f"some ({fixture}.values {row})", evaluator + " = some VALUE",
                             proof, geometry, "The singleton descendant includes the ancestor contribution "
                             "and signed calibration terms. Lean checks the ordinary GKM row.")
        bound = 3 if q["target"] == "X1" else 1
        if family and (beta[-1] == 0 or energy <= bound):
            key = f"({family} : SurfaceGenusTwoBlowupOrder.Family {X})"
            state = f"(request.beta, {key})"
            conclusion = (f"request = {key}.query request.beta ∧ "
                          f"SurfaceGenusTwoBlowupRecursion.values 0 {state} = VALUE")
            if q["class"][-1] == 0:
                candidate = f"some (SurfaceGenusTwoBlowupBoundary.value request.beta {key})"
                reduction = f"SurfaceGenusTwoBlowupRecursion.values_boundary 0 {state} (by decide +kernel)"
                module = "Surfaces.GenusTwoBlowupReconstruction"
                reason = "The canonical row at plane degree zero uses the full exceptional class and divisor label."
            elif q["target"] == "X1" and energy == 3:
                candidate = f"some (BlowupF1FiberHReduction.boundary {state})"
                reduction = f"F1PlaneLine.values_eq {state} (by decide +kernel)"
                module = "Surfaces.Fixtures.F1PlaneLineL24Replay"
                reason = "The 24-state F1 table uses incidence vanishing at the shifted class 2E+F."
            elif q["target"] == "X1":
                candidate = f"some (BlowupF1FiberHReduction.boundary {state})"
                reduction = f"BlowupF1FiberTable.values_eq {state} (by decide +kernel)"
                module = "Surfaces.Fixtures.BlowupF1FiberTable"
                reason = "The ordered insertions select a row of the checked sixteen-state F1 BP/L24 table."
            else:
                candidate = f"some (BlowupTwoLineTable.candidate 0 {state})"
                reduction = f"BlowupTwoLineTable.values_eq {state} (by decide +kernel)"
                module = "Surfaces.Fixtures.BlowupTwoLineL24.Assembly"
                reason = "The twenty-state table uses the full 815-term shifted equation for the strict line."
            proof = f"constructor\n  · decide +kernel\n  · exact ({reduction}).trans (by decide +kernel)"
            return Route(module, candidate, conclusion, proof,
                         "SurfaceGenusTwoBlowupReconstruction.values_eq_eval_from_geometry", reason, state)
        if beta[-1] == 0 and energy > 0 and any(label == "pt" for label, _ in marks):
            evaluator = "SurfaceGenusTwo.exceptionalPointQueryValue? request"
            return Route("Surfaces.ExceptionalEvaluationSupport", evaluator, evaluator + " = some VALUE",
                         "decide +kernel", "SurfaceGenusTwo.exceptionalPointQueryValue?_sound",
                         "A point insertion pulls back to zero on the exceptional image, at any power.")
        if energy == 1 and len(marks) <= 2:
            from gkm_genus_two_energy_one import REQUESTS
            ordered = (tuple(beta), tuple(k for _, k in marks), tuple(label for label, _ in marks))
            frame = REQUESTS[q["target"]]
            if ordered in frame:
                row = frame.index(ordered)
                family_name = "OneBlowup" if q["target"] == "X1" else "TwoBlowups"
                fixture = f"GKM.GenusTwoEnergyOne.{family_name}"
                module = ("GKM.Fixtures.GenusTwoEnergyOneF1Replay" if q["target"] == "X1"
                          else "GKM.Fixtures.GenusTwoEnergyOneReplay")
                return checked_row_route(module, fixture, row, "energy-one")
        if accepts_zero_divisor_pair(q):
            evaluator = "SurfaceGenusTwo.zeroDivisorPair? request"
            return Route("Surfaces.GenusTwoZeroDivisorPairs", evaluator, evaluator + " = some VALUE",
                         "decide +kernel", "SurfaceGenusTwo.zeroDivisorPair?_checkedEval",
                         "The divisor has zero curve intersection and zero lowered cotangent coefficient.")
        if q["target"] == "X2" and beta in ([2, 0, 0], [0, 2, 0]) and len(marks) == 2:
            reductions = (["unit", 0], ["unit", 1], ["H", 0], ["E1", 0], ["E2", 0])
            for position, marking in enumerate(marks):
                if marking in reductions:
                    axis = beta.index(2)
                    rule = reductions.index(marking)
                    label = LABELS[marks[1 - position][0]]
                    last = "true" if position == 1 else "false"
                    fixture = "BlowupTwoDoubleExceptionalMarked"
                    indices = f"{axis} {rule} ({label})"
                    values = f"{fixture}.values {indices}"
                    proof = (f"have hq : request = {fixture}.request {indices} {last} := by decide +kernel\n"
                             f"  have hv : {values} = VALUE := by decide +kernel\n"
                             f"  rw [hq, ← hv]\n  exact {fixture}.checked {indices} {last}")
                    return Route(f"Surfaces.Fixtures.{fixture}", f"some ({values})",
                                 ns + ".CheckedDescendant 0 request VALUE", proof,
                                 "SurfaceGenusTwoBlowupDescendantReconstruction.checkedDescendant_from_geometry",
                                 "The ordered string, dilaton or divisor equation reduces to the five checked "
                                 "singletons on this exceptional axis.", descendant_witness="certified")
            import gkm_bl2_double_exceptional_few_markings as complete
            ordered = (tuple(beta), tuple(k for _, k in marks), tuple(label for label, _ in marks))
            if ordered in complete.REQUESTS["X2"]:
                return checked_row_route("GKM.Fixtures.BlowupTwoDoubleExceptionalCompleteReplay",
                                         f"GKM.{complete.NAMESPACE}", complete.REQUESTS["X2"].index(ordered),
                                         "double exceptional mixed cotangent and calibrated ancestor")
        if q["target"] == "X2" and energy == 2 and beta[2] > 0 and len(marks) == 2:
            marked = any((label == "unit" and k <= 1) or (label not in ("pt", "unit") and k == 0)
                         for label, k in marks)
            strict_line_point = beta == [0, 0, 2] and sum(label == "pt" for label, _ in marks) == 1
            ruling_divisor_point = beta[2] == 1 and any(label == "pt" for label, _ in marks) and any(
                label in ("H", "E1", "E2") for label, _ in marks)
            if marked or strict_line_point or ruling_divisor_point:
                from gkm_bl2_positive_plane_energy_two import REQUESTS
                ordered = (tuple(beta), tuple(k for _, k in marks), tuple(label for label, _ in marks))
                row = REQUESTS["pairs"]["X2"].index(ordered)
                fixture = "GKM.BlowupTwoPositivePlaneEnergyTwoPairs"
                if marked:
                    return checked_row_route("GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoReplay",
                                             fixture, row, "energy-two marked pair",
                                             witness=f"{fixture}.marked_accepted (j := {row}) (by decide +kernel)")
                if ruling_divisor_point:
                    return checked_row_route("GKM.Fixtures.BlowupTwoRulingDivisorPointReplay",
                                             fixture, row, "ruling divisor and point interior",
                                             witness=f"{fixture}.ruling_divisor_point_accepted "
                                                     f"(n := {row}) (by decide +kernel)")
                return checked_row_route("GKM.Fixtures.BlowupTwoPositivePlaneEnergyTwoCoverage",
                                         fixture, row, "strict-line interior point pair",
                                         witness=f"{fixture}.verified_accepted (j := {row}) (by decide +kernel)")
        if energy <= bound:
            if q["target"] == "X1" and energy == 3:
                module, table, accepted = ("Surfaces.Fixtures.F1PlaneLineL24Replay",
                                           "(F1PlaneLine.candidate 0)", "F1PlaneLine.accepted")
            elif q["target"] == "X1":
                bound = 2
                module, table, accepted = ("Surfaces.Fixtures.BlowupF1FiberTable", "BlowupF1FiberHReduction.boundary",
                                           "BlowupF1FiberTable.accepted")
            else:
                module, table, accepted = ("Surfaces.Fixtures.BlowupTwoLineL24.Assembly", "(BlowupTwoLineTable.candidate 0)",
                                           "BlowupTwoLineTable.accepted")
            candidate = f"{ns}.queryValueWith? {table} request"
            proof = (f"rw [← {ns}.queryValueWith?_eq 0 {bound} {table} {accepted} request (by decide +kernel)]\n"
                     "  decide +kernel")
            return Route(module, candidate, evaluator + " = some VALUE", proof, geometry,
                         "The verified bounded table supplies the canonical values throughout the mixed cotangent expansion.")
    return Route(module, evaluator, evaluator + " = some VALUE", "decide +kernel", geometry,
                 "Evaluate the full descendant reconstruction and reduce the same closed claim in the kernel.")


def replay_lean(path, timeout=None):
    """Replay a file and clean up the entire Lean process group if interrupted."""
    # A single query and its axiom audits can share a large graph proof. Replay them serially.
    command = ["lake", "env", "lean", "--threads=1", str(path)]
    proc = subprocess.Popen(command, cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                            start_new_session=True)
    try:
        output = proc.communicate(timeout=timeout)[0]
    except subprocess.TimeoutExpired:
        raise ValueError(f"Lean exceeded {timeout}s checking this query") from None
    finally:
        if proc.poll() is None:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.communicate()
    return subprocess.CompletedProcess(command, proc.returncode, stdout=output)


def lean(source, folder, timeout):
    path = folder / "Query.lean"
    path.write_text(source, encoding="utf-8")
    run = replay_lean(path, timeout)
    output = run.stdout
    if run.returncode or "sorryAx" in output:
        raise ValueError("Lean did not certify the query. " + output.strip()[-1600:])
    return output


def checked_axioms(output, theorem):
    prefix = re.escape(f"'{theorem}'")
    match = re.search(prefix + r" depends on axioms:\s*\[([^\]]*)\]", output)
    if match:
        axioms = {name.strip() for name in match[1].split(",") if name.strip()}
    elif f"'{theorem}' does not depend on any axioms" in output:
        axioms = set()
    else:
        raise ValueError(f"Missing axiom audit for {theorem}")
    if not axioms <= AXIOMS:
        raise ValueError(f"Unexpected axiom in {theorem}: {sorted(axioms - AXIOMS)}")
    return sorted(axioms)


def geometric_seeds(query, route):
    """Named numerical seed hypotheses of the interpretation theorem."""
    if route.module in ("Surfaces.ExceptionalEvaluationSupport", "Surfaces.DimensionVanishing",
                        "Surfaces.GenusTwoZeroDivisorPairs"):
        return {}
    divisors = range(1, len(query["class"]))
    seeds = {"line": [1, 1], **{f"exceptional E{i}": [1, 1] for i in divisors}}
    if query["genus"] >= 1:
        seeds["genusOneHyperplane"] = [-1, 8]
        for i in divisors:
            seeds[f"genusOneExceptional E{i}"] = [-1, 24]
    if query["genus"] == 2 and "degreeZeroOnePoint" not in route.interpretation:
        seeds["genusTwoHyperplane"] = [-1, 960]
        for i in divisors:
            seeds[f"genusTwoExceptional E{i}"] = [-1, 2880]
    return seeds


def geometric_source(route, surface, literal):
    """Specialize the existing reconstruction theorem while retaining all of its geometric hypotheses."""
    theorem = route.interpretation
    target = f"SurfaceTarget.{surface}"
    typed = f"(X := {target})"
    helper = ""
    rewrite = ""
    if theorem.endswith(".pointBenchmark_checkedEval"):
        ns = theorem.split(".")[0]
        args = f"{typed} (beta := request.beta) (hbeta := by decide +kernel) (hbound := by decide +kernel)"
        rewrite = (f"← certified.1, {ns}.pointBenchmarkValues_eq {target} request.beta "
                   "(by decide +kernel), certified.2")
    elif route.canonical_state:
        args = f"{typed} (i := 0) (s := {route.canonical_state})"
        helper = (f"private abbrev target := {target}\n"
                  "private theorem evaluated_iff {C : StableCurveCohomology ℚ}\n"
                  "    {Omega : GromovWittenTheory ℚ (SurfaceCohomology target.blowups) target.Curve target.effective C}\n"
                  "    {M : StableMapDescendants Omega} {I : StableCurveIntegration C}\n"
                  "    (U : UnstableDescendantConventions M I) :\n"
                  f"    {literal} = request.eval U ↔ request.checkedEval U = some {literal} := by\n"
                  "  rw [SurfaceQuery.checkedEval_of_geometricDomain U request domain, Option.some.injEq, eq_comm]\n\n")
        rewrite = "Prod.fst, Prod.snd, certified.2, ← certified.1, evaluated_iff"
    elif theorem.endswith(".planeCheckCanonicalClaim_checkedEval_from_geometry"):
        args = (f"(bound := 4) (values := PlaneGenusTwoScalarTable.values) (query := request) "
                f"(claimed := {literal}) (hcheck := certified)")
    elif theorem.endswith(".degreeZeroOnePointQueryValue?_sound"):
        args = f"{typed} (q := request) (claimed := {literal}) (hvalue := certified)"
    elif theorem.endswith(".dimensionVanishing?_sound"):
        args = f"{typed} (q := request) (hg := domain) (v := {literal}) (hv := certified)"
    elif theorem.endswith(".zeroDivisorPair?_checkedEval"):
        args = f"{typed} (q := request) (v := {literal}) (h := certified)"
    elif theorem.endswith(".exceptionalPointQueryValue?_sound"):
        args = f"{typed} (q := request) (claimed := {literal}) (h := certified)"
    elif route.descendant_witness:
        args = (f"{typed} (i := 0) (q := request) (hg := rfl) (v := {literal}) "
                f"(hv := {route.descendant_witness})")
    else:
        params = "" if theorem.startswith("BelorousskiPandharipande.") else typed + " "
        if theorem.startswith("SurfaceGenusTwoBlowupDescendantReconstruction."):
            params += "(i := 0) "
        args = params + "(q := request) (hg := rfl)"
        rewrite = f"certified, eq_comm (a := some {literal})"
    applied = f"@{theorem} {args}"
    body = (f"  let law := {applied}\n  show _ from by\n    simp only [{rewrite}] at law\n    exact law"
            if rewrite else "  " + applied)
    return ("\n" + helper + "private abbrev geometricDerivation :=\n" + body + "\n\n"
            "/-- This exact request has the displayed GW value under the reconstruction theorem's original inputs. -/\n"
            "theorem geometric : type_of% geometricDerivation := geometricDerivation\n")


def reconstruct(query, *, timeout=None, gkm_report=None):
    """Return (JSON-compatible result, replayable Lean source). Works from Sage or Python."""
    if timeout is not None:
        timeout = natural(timeout)
        if timeout == 0:
            raise ValueError("Expected a positive timeout")
    query, surface, energy = validate(query)
    insertion_proof = None
    incoming = None
    binding = None
    if gkm_report is not None:
        from gkm_research_query import equivariant_fixture, incoming_claim
        incoming = incoming_claim(query, Path(gkm_report).read_bytes())
        binding = equivariant_fixture(incoming)
    curve = query["class"]
    empty_graph = (incoming is not None and query["target"] == "X2"
                   and curve[2] == 0 and curve[0] > 0 and curve[1] > 0)
    if incoming is not None and not empty_graph:
        from gkm_research_query import exceptional_insertion_source
        insertion_proof = exceptional_insertion_source(query)
    route = select(query, surface, energy)
    digest = hashlib.sha256(json.dumps(query, ensure_ascii=True, sort_keys=True,
                                       separators=(",", ":")).encode()).hexdigest()
    name = "AxiomaticGW.Research.Query_" + digest[:20]
    beta = ", ".join(str(n) for n in query["class"])
    marks = ", ".join(f"⟨{LABELS[s]}, {p}⟩" for s, p in query["insertions"])
    imports = f"import AxiomaticGW.{route.module}\n"
    if incoming is not None:
        comparison_module = binding[0] if binding is not None else "GKM.EquivariantCoefficients"
        if comparison_module != route.module:
            imports += f"import AxiomaticGW.{comparison_module}\n"
    if empty_graph:
        imports += "import AxiomaticGW.GKM.Fixtures.BlowupTwoExceptionalGraphSupport\n"
    if insertion_proof:
        imports += "import AxiomaticGW.GKM.Fixtures.ExceptionalMarkedGraphSupport\n"
    if ((route.canonical_state or "queryValueWith?" in route.candidate)
            and route.module != "Surfaces.GenusTwoBlowupReconstruction"):
        imports += "import AxiomaticGW.Surfaces.GenusTwoBlowupReconstruction\n"
        if "queryValueWith?" in route.candidate:
            imports += "import AxiomaticGW.Surfaces.GenusTwoBlowupQueryCertificate\n"
    if route.interpretation.startswith("SurfaceGenusTwoBlowupDescendantReconstruction."):
        imports += "import AxiomaticGW.Surfaces.GenusTwoBlowupDescendantReconstruction\n"
    head = (imports + "\n" +
            f"namespace {name}\n\n/-- Requested genus, effective class and ordered descendants. -/\n"
            f"def request : SurfaceQuery .{surface} := ⟨{query['genus']}, ![{beta}], [{marks}]⟩\n\n")
    with tempfile.TemporaryDirectory(prefix="gw-query-") as d:
        folder = Path(d)
        output = lean(head + f"#eval IO.println (match ({route.candidate} : Option ℚ) with\n"
                      '  | none => "GW_NONE"\n  | some x => s!"GW_RAT {x.num} {x.den}")\n'
                      f"end {name}\n", folder, timeout)
        values = re.findall(r"^GW_RAT (-?\d+) ([1-9]\d*)$", output, re.M)
        if len(values) != 1:
            raise ValueError("The selected evaluator did not return a rational")
        value = Fraction(*map(int, values[0]))
        if incoming is not None:
            supplied = Fraction(*incoming["ordinary"])
            if supplied != value:
                raise ValueError(f"GKM supplied {supplied}, while reconstruction returned {value}")
            head = "-- GKM ordinary comparison, report SHA256 " + incoming["report_sha256"] + "\n" + head
        literal = f"({value.numerator} / {value.denominator} : ℚ)"
        conclusion = route.conclusion.replace("VALUE", literal)
        proof = (head + "/-- The request is in the geometric query domain. -/\n"
                 "theorem domain : request.GeometricDomain := by decide +kernel\n\n"
                 "/-- Exact answer from the specified surface query evaluator. -/\n"
                 "theorem certified :\n    " + conclusion +
                 " := by\n  " + route.proof.replace("VALUE", literal) + "\n")
        proof += geometric_source(route, surface, literal)
        if incoming is not None:
            from gkm_research_query import specialization_source
            proof += specialization_source(incoming, literal, conclusion)
        if empty_graph:
            from gkm_research_query import mixed_exceptional_graph_source
            proof += mixed_exceptional_graph_source(*curve[:2])
        if insertion_proof:
            proof += insertion_proof
        proof += "\nend " + name + "\n"
        theorem = name + ".certified"
        geometry = "AxiomaticGW." + route.interpretation
        audited = [name + ".domain", theorem, geometry, name + ".geometric"]
        if incoming is not None:
            audited.append(name + ".comparison")
            if "regular_representative" in incoming:
                audited.append(name + ".submitted_presentation")
            if "plane_line_point_power" in incoming or "exceptional_cubic" in incoming:
                audited.append(name + ".fixed_locus_comparison")
                if "exceptional_cubic" in incoming:
                    audited.append(name + ".integrated_locus_comparison")
                if incoming.get("plane_line_point_power", 0) > 0:
                    audited.append(name + ".equivariant_grading")
            if binding is not None:
                audited.append(name + ".equivariant_comparison")
            if "double_exceptional_comparison_row" in incoming:
                audited.append(name + ".exceptional_surface_comparison")
        if empty_graph:
            audited.append(name + ".empty_graph_comparison")
        if insertion_proof:
            audited.append(name + ".insertion_comparison")
        proof += "\n" + "".join(f"#print axioms {declaration}\n" for declaration in audited)
        audit = lean(proof, folder, timeout)
        axioms = {t: checked_axioms(audit, t) for t in audited}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(package["rev"] for package in manifest["packages"] if package["name"] == "mathlib")
    result = {
        "format": "axiomatic-gw-query-v1", "status": "certified", "query": query,
        "ordinary_rational": [value.numerator, value.denominator],
        "normalization": "ordinary GW over the rationals, complex codimension",
        "theorem": theorem, "module": "AxiomaticGW." + route.module,
        "derivation": route.derivation, "geometric_interpretation": geometry, "geometric_theorem": name + ".geometric",
        "geometric_inputs": "notes/mathematics/SurfaceReconstructionInputs.md",
        "geometric_seed_hypotheses": geometric_seeds(query, route),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(), "mathlib_revision": mathlib,
        "axioms": axioms, "certificate_sha256": hashlib.sha256(proof.encode()).hexdigest(),
    }
    if incoming is not None:
        result["gkm_comparison"] = incoming
        result["comparison_theorem"] = name + ".comparison"
        if "regular_representative" in incoming:
            result["submitted_presentation_theorem"] = name + ".submitted_presentation"
        if "plane_line_point_power" in incoming or "exceptional_cubic" in incoming:
            result["fixed_locus_comparison_theorem"] = name + ".fixed_locus_comparison"
            if "exceptional_cubic" in incoming:
                result["integrated_locus_comparison_theorem"] = name + ".integrated_locus_comparison"
            if incoming.get("plane_line_point_power", 0) > 0:
                result["equivariant_grading_theorem"] = name + ".equivariant_grading"
        if binding is not None:
            result["equivariant_comparison_theorem"] = name + ".equivariant_comparison"
        if "double_exceptional_comparison_row" in incoming:
            result["exceptional_surface_comparison_theorem"] = name + ".exceptional_surface_comparison"
    if empty_graph:
        result["empty_graph_comparison_theorem"] = name + ".empty_graph_comparison"
    if insertion_proof:
        result["insertion_comparison_theorem"] = name + ".insertion_comparison"
    return result, proof


def save_certificate(path, source):
    """Publish the checked bytes in one step while preserving any existing certificate."""
    with tempfile.NamedTemporaryFile(dir=path.parent) as temporary:
        temporary.write(source.encode("utf-8"))
        temporary.flush()
        os.link(temporary.name, path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", type=Path, help="JSON request")
    parser.add_argument("--certificate", type=Path, required=True, help="new .lean file")
    parser.add_argument("--timeout", type=int, help="optional limit in seconds per Lean pass")
    parser.add_argument("--gkm-report", type=Path, help="compare the regular GKM specialization and any available certified equivariant row")
    args = parser.parse_args()
    try:
        if (args.timeout is not None and args.timeout <= 0) or args.certificate.suffix != ".lean":
            raise ValueError("Expected a positive timeout and a .lean certificate path")
        if os.path.lexists(args.certificate):
            raise ValueError(f"Certificate already exists: {args.certificate}")
        query = json.loads(args.request.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
        result, source = reconstruct(query, timeout=args.timeout, gkm_report=args.gkm_report)
        save_certificate(args.certificate, source)
        print(json.dumps(result, sort_keys=True))
    except (OSError, ValueError) as err:
        print(json.dumps({"status": "unverified", "error": str(err)}), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
