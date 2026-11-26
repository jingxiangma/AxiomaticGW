#!/usr/bin/env python3
"""Localize one research query with the pinned GKM producer and preserve its exact function."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from check_gkm_inputs import RationalFunction, add_polynomials, polynomial, unique_object
from export_gkm_certificate import EVAL_SIMP, VECTOR_SIMP, nonvanishing_point, polynomial_text, rational_text
from gkm_report_cli import explore_report
from gkm_three_point_descendants import read_report

KIND = "gkm_localization.surface_research_query"
EXCEPTIONAL_CUBICS = {("X1", (1, 0), ("E1",)): "f1", ("X2", (1, 0, 0), ("E1",)): "first",
                      ("X2", (0, 1, 0), ("E2",)): "second"}


def regular_presentation(submitted, witness=None):
    """Check a regular witness or find a polynomial quotient by exact sparse division."""
    def fraction(pair):
        if not isinstance(pair, dict) or set(pair) != {"numerator", "denominator"}:
            raise ValueError("Wrong fraction fields")
        return RationalFunction(polynomial(pair["numerator"]), polynomial(pair["denominator"]))

    original = fraction(submitted)
    if witness is not None:
        regular = fraction(witness)
        if not polynomial(witness["denominator"]).get((0, 0)) or original != regular:
            raise ValueError("Invalid regular representative for the submitted fraction")
        return witness
    denominator = polynomial(submitted["denominator"])
    if denominator.get((0, 0)):
        return submitted
    remainder, quotient = original.numerator, {}
    (a, b), coeff = max(denominator.items())
    while remainder:
        (i, j), lead = max(remainder.items())
        if i < a or j < b:
            raise ValueError("A non-polynomial fraction with a vanishing denominator needs a regular_representative")
        shift, scale = (i - a, j - b), lead / coeff
        quotient[shift] = scale
        remainder = add_polynomials(remainder, {(k + shift[0], l + shift[1]): -v * scale
                                                for (k, l), v in denominator.items()})
    return {"numerator": [[list(k), [c.numerator, c.denominator]] for k, c in sorted(quotient.items())],
            "denominator": [[[0, 0], [1, 1]]]}


def submitted_presentation_source(claim, literal):
    """Prove equality to the literal original field element through denominator nonvanishing."""
    submitted = claim["equivariant"]
    a, b = nonvanishing_point(submitted["denominator"])
    eval_simp = ", ".join(EVAL_SIMP[1:] + VECTOR_SIMP)
    return f"""
noncomputable def submittedNumerator : GKM.EquivariantCoefficients.Polynomial :=
  {polynomial_text(submitted["numerator"], ring=True)}
noncomputable def submittedDenominator : GKM.EquivariantCoefficients.Polynomial :=
  {polynomial_text(submitted["denominator"], ring=True)}

/-- The actual submitted fraction equals the regular function in the comparison and
has the same ordinary GW specialization, even if its own denominator vanishes at zero. -/
theorem submitted_presentation :
    embed submittedNumerator / embed submittedDenominator = gkmFunction ∧
    Specializes (embed submittedNumerator / embed submittedDenominator) {literal} := by
  have hn := embed_ne_zero_of_eval submittedDenominator ![{a}, {b}] (by
    norm_num only [submittedDenominator, {eval_simp}])
  have hd : atZero gkmDenominator ≠ 0 := by
    norm_num [gkmDenominator, {", ".join(EVAL_SIMP)}]
  have h : embed submittedNumerator / embed submittedDenominator = gkmFunction := by
    apply (div_eq_div_iff hn (embed_ne_zero_of_atZero _ hd)).mpr
    simp only [submittedNumerator, submittedDenominator, gkmNumerator, gkmDenominator,
      map_mul, map_pow, map_add, map_zero, embed_C]
    ring
  exact ⟨h, h ▸ ordinary_specialization⟩
"""


def equivariant_fixture(claim):
    """Return the certified module, Lean namespace and index for a known full-field comparison."""
    if "positive_plane_row" in claim:
        row = claim["positive_plane_row"]
        ns = "BlowupTwoPositivePlaneEnergyTwo" + row["frame"].capitalize()
        return f"GKM.Fixtures.{ns}", f"GKM.{ns}", row["index"]
    if "double_exceptional_comparison_row" in claim:
        return ("GKM.Fixtures.BlowupTwoDoubleExceptionalComparison", "GKM.BlowupTwoDoubleExceptionalFewMarkings",
                claim["double_exceptional_comparison_row"])
    if "plane_line_point_power" in claim:
        return ("GKM.Fixtures.PlaneLineOneMarkedPoint", "GKM.PlaneLineOneMarkedPoint",
                claim["plane_line_point_power"])
    if "exceptional_cubic" in claim:
        ns = "GKM.ExceptionalGenusTwoCubicReplay"
        return "GKM.Fixtures.ExceptionalCubicGeometricLoci", ns, "." + claim["exceptional_cubic"]
    if "double_exceptional_singleton_row" in claim:
        return ("GKM.Fixtures.BlowupTwoDoubleExceptionalSingletons", "GKM.BlowupTwoDoubleExceptionalSingletons",
                claim["double_exceptional_singleton_row"])
    if "energy_one_row" in claim:
        row = claim["energy_one_row"]
        section = {"X1": "OneBlowup", "X2": "TwoBlowups"}[row["target"]]
        return "GKM.Fixtures.GenusTwoEnergyOneEquivariant", f"GKM.GenusTwoEnergyOne.{section}", row["index"]
    if "fiber_one_marking_row" in claim:
        return "GKM.Fixtures.F1FiberOneMarkingReplay", "GKM.F1FiberOneMarking", claim["fiber_one_marking_row"]
    if "zero_divisor_row" in claim:
        from gkm_zero_divisor_pairs import FRAMES
        row = claim["zero_divisor_row"]
        _, namespace, _ = FRAMES[row["target"]]
        if row.get("partial"):
            namespace += "Partial"
        return f"GKM.Fixtures.{namespace}", f"GKM.{namespace}", row["index"]
    if "mixed_exceptional_row" in claim:
        return ("GKM.Fixtures.BlowupTwoMixedExceptional", "GKM.BlowupTwoMixedExceptional",
                claim["mixed_exceptional_row"])
    if "double_exceptional_pair_row" in claim:
        return ("GKM.Fixtures.BlowupTwoDoubleExceptionalPairs", "GKM.BlowupTwoDoubleExceptionalPairs",
                claim["double_exceptional_pair_row"])
    if "f1_energy_two_row" in claim:
        from gkm_f1_energy_two import FRAMES
        row = claim["f1_energy_two_row"]
        namespace = FRAMES[row["frame"]].namespace
        return f"GKM.Fixtures.{namespace}", f"GKM.{namespace}", row["index"]
    return None


def specialization_source(incoming, literal, conclusion):
    fraction = incoming.get("regular_representative", incoming["equivariant"])
    numerator = polynomial_text(fraction["numerator"], ring=True)
    denominator = polynomial_text(fraction["denominator"], ring=True)
    n0 = rational_text(polynomial(fraction["numerator"]).get((0, 0), 0))
    d0 = rational_text(polynomial(fraction["denominator"]).get((0, 0), 0))
    evaluation = ("atZero, map_add, map_mul, map_pow, map_zero, MvPolynomial.eval₂Hom_C, "
                  "MvPolynomial.eval₂Hom_X', RingHom.id_apply, Pi.zero_apply")
    source = f"""
open GKM.EquivariantCoefficients

noncomputable def gkmNumerator : GKM.EquivariantCoefficients.Polynomial :=
  {numerator}
noncomputable def gkmDenominator : GKM.EquivariantCoefficients.Polynomial :=
  {denominator}
noncomputable def gkmFunction : Coefficient := embed gkmNumerator / embed gkmDenominator

/-- The incoming equivariant function is regular in this presentation at zero weights. -/
theorem ordinary_specialization : Specializes gkmFunction {literal} := by
  have hn : atZero gkmNumerator = ({n0} : ℚ) := by
    norm_num only [gkmNumerator, {evaluation}]
  have hd : atZero gkmDenominator = ({d0} : ℚ) := by
    norm_num only [gkmDenominator, {evaluation}]
  refine ⟨gkmNumerator, gkmDenominator, ?_, rfl, ?_⟩
  · exact fun hz ↦ (by decide +kernel : ({d0} : ℚ) ≠ 0) (hd.symm.trans hz)
  · exact (congrArg₂ (· / ·) hn hd).trans (by decide +kernel)

/-- The exact requested GW computation and the regular GKM specialization agree. -/
theorem comparison : ({conclusion}) ∧ Specializes gkmFunction {literal} :=
  ⟨certified, ordinary_specialization⟩
"""
    if "regular_representative" in incoming:
        source += submitted_presentation_source(incoming, literal)
    row = equivariant_fixture(incoming)
    if row is not None:
        _, fixture, i = row
        if "exceptional_cubic" in incoming:
            return source + f"""
/-- The original full request and both equivariant characters agree with the cubic calculation. -/
theorem equivariant_comparison :
    request = {fixture}.requests {i} ∧ gkmFunction = {fixture}.equivariant {i} := by
  constructor
  · decide +kernel
  · have hd : atZero gkmDenominator ≠ 0 := by norm_num [gkmDenominator, {evaluation}]
    rw [gkmFunction, div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [{fixture}.equivariant, gkmNumerator, gkmDenominator, map_add, map_mul, map_pow,
      embed_C, embed_X_zero, embed_X_one]
    all_goals ring

/-- The incoming rational function equals the sum over the three genus distributions
and two marked endpoints of the exceptional edge. -/
theorem fixed_locus_comparison : gkmFunction = ∑ g : Fin 3, ∑ m : Fin 2, {fixture}.locus {i} g m :=
  equivariant_comparison.2.trans ({fixture}.sum_loci {i}).symm

private abbrev integratedLocusDerivation :=
  let law := @GKM.ExceptionalCubicGeometricLoci.geometric_sum (c := {i})
  show _ from by
    simp only [← equivariant_comparison.2] at law
    exact law

/-- Under the curve and Hodge class identities, integrating the stable vertices and summing
the six signed primitive exceptional loci gives this exact incoming character function. -/
theorem integrated_locus_comparison : type_of% integratedLocusDerivation := integratedLocusDerivation
"""
        if "plane_line_point_power" in incoming:
            source += f"""
/-- The supplied two-character fraction equals the marked plane line's two-flag sum. -/
theorem equivariant_comparison :
    request = {fixture}.requests {i} ∧ gkmFunction = {fixture}.equivariant {i} := by
  constructor
  · decide +kernel
  · have hd : atZero gkmDenominator ≠ 0 := by
      norm_num [gkmDenominator, {evaluation}]
    rw [{fixture}.equivariant_eq_polynomial, gkmFunction,
      div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [gkmNumerator, gkmDenominator, {fixture}.polynomial, map_add, map_mul, map_sub,
      map_pow, embed_C, embed_X_zero, embed_X_one]
    all_goals ring

/-- The complete field value equals the sum of the six original oriented fixed-locus factors. -/
theorem fixed_locus_comparison : gkmFunction =
    ∑ e : Fin 3, ({fixture}.flag {i} e false + {fixture}.flag {i} e true) :=
  equivariant_comparison.2.trans ({fixture}.sum_flags {i}).symm
"""
            if i > 0:
                source += f"""
/-- The supplied regular polynomial has the equivariant degree of this descendant. -/
theorem equivariant_grading : ∃ p : GKM.EquivariantCoefficients.Polynomial,
    p.IsHomogeneous {i - 1} ∧ gkmFunction = embed p :=
  ⟨{fixture}.polynomial {i}, {fixture}.polynomial_homogeneous {i - 1},
    equivariant_comparison.2.trans ({fixture}.equivariant_eq_polynomial {i})⟩
"""
            return source
        variable_terms = any(powers != [0, 0] for side in ("numerator", "denominator")
                             for powers, _ in fraction[side])
        finish = " <;> ring" if variable_terms else ""
        source += f"""
/-- The full ordered request and incoming fraction agree with the certified localization row. -/
theorem equivariant_comparison :
    request = {fixture}.requests {i} ∧
      gkmFunction = {fixture}.equivariant {i} := by
  constructor
  · decide +kernel
  · have hv : {fixture}.values {i} = {literal} := by decide +kernel
    have hd : atZero gkmDenominator ≠ 0 := by
      norm_num [gkmDenominator, {evaluation}]
    rw [{fixture}.equivariant_eq_ordinary, hv, gkmFunction,
      div_eq_iff (embed_ne_zero_of_atZero _ hd)]
    norm_num [gkmNumerator, gkmDenominator, map_add, map_mul, map_pow, embed_C]{finish}
"""
        if "double_exceptional_comparison_row" in incoming:
            source += f"""
/-- Marking-by-marking comparison to the original F₁ reconstruction, with the full incoming field. -/
theorem exceptional_surface_comparison :
    {fixture}.project? request = ({fixture}.counterpart {i}).map (fun c ↦ ({fixture}.sourceRow c).1) ∧
    (∀ c, {fixture}.counterpart {i} = some c →
      SurfaceGenusTwoBlowupDescendants.CheckedDescendant 0 ({fixture}.sourceRow c).1 {literal}) ∧
    ({fixture}.counterpart {i} = none → gkmFunction = 0) := by
  rw [equivariant_comparison.1]
  have hv : {fixture}.values {i} = {literal} := by decide +kernel
  exact ⟨({fixture}.projection {i}).1, fun c hc ↦ hv ▸ ({fixture}.matched {i} c hc).2.1,
    fun hc ↦ equivariant_comparison.2.trans ({fixture}.unmatched {i} hc).2⟩
"""
    return source


def mixed_exceptional_graph_source(a, b):
    """Check the incoming rational function against empty connected graph support."""
    return f"""
/-- The pinned toric target has no connected graph of this request's full curve class. -/
theorem empty_graph_support :
    IsEmpty (GKM.FixedGraphSupport.AtDegree GKM.CurveReplay.TwoBlowups.tables request.beta) :=
  GKM.BlowupTwoExceptionalGraphSupport.mixed_isEmpty {a} {b} (by decide) (by decide)

/-- The actual supplied rational function vanishes before ordinary specialization. -/
theorem empty_graph_comparison :
    IsEmpty (GKM.FixedGraphSupport.AtDegree GKM.CurveReplay.TwoBlowups.tables request.beta) ∧
      gkmFunction = 0 := by
  refine ⟨empty_graph_support, ?_⟩
  have hn : gkmNumerator = 0 := by
    unfold gkmNumerator
    ring
  rw [gkmFunction, hn, map_zero, zero_div]
"""


def exceptional_insertion_source(query):
    """Bind a zero native insertion product to the exact exceptional class and marks."""
    target, beta = query["target"], query["class"]
    if target == "X0" or beta[-1] != 0 or not any(beta):
        return None
    labels = {label for label, _ in query["insertions"]}
    section = "OneBlowup" if target == "X1" else "TwoBlowups"
    ns = "GKM.ExceptionalMarkedGraphSupport"
    decide = "(by decide +kernel)"
    if "pt" in labels:
        theorem = "oneBlowup_point" if target == "X1" else "twoBlowups_point"
        proof = f"{ns}.{theorem} request {decide} {decide} {decide}"
    elif target == "X2" and (beta[0] == 0 or beta[1] == 0):
        axis = 0 if beta[0] else 1
        foreign = 1 - axis
        if f"E{foreign + 1}" not in labels:
            return None
        proof = (f"{ns}.foreign_divisor {axis} {foreign} {decide} ⟨{beta[axis]}, {decide}⟩ "
                 f"request {decide} {decide}")
    else:
        return None
    return f"""
/-- Every connected support has zero insertion product and the supplied full torus value is zero. -/
theorem insertion_comparison :
    {ns}.Vanishes GKM.CurveReplay.{section}.tables
        GKM.SurfaceFrames.{section}.request.restrictions request ∧ gkmFunction = 0 := by
  refine ⟨{proof}, ?_⟩
  have hn : gkmNumerator = 0 := by
    unfold gkmNumerator
    ring
  rw [gkmFunction, hn, map_zero, zero_div]
"""


def frame(query):
    requests = {target: [] for target in ("X0", "X1", "X2")}
    powers = tuple(power for _, power in query["insertions"])
    labels = tuple(label for label, _ in query["insertions"])
    requests[query["target"]].append((tuple(query["class"]), powers, labels))
    return requests


def incoming_claim(query, raw):
    """Select the same full ordered request after exact specialization and provenance checks."""
    import gkm_bl2_line_canonical as canonical
    import gkm_bl2_double_exceptional_pairs as double_pairs
    import gkm_bl2_double_exceptional_singletons as double_singles
    import gkm_bl2_double_exceptional_few_markings as double_all
    import gkm_bl2_positive_plane_energy_two as positive_plane
    import gkm_bl2_mixed_exceptional as mixed_exceptional
    import gkm_bl2_line_one_marking as line
    import gkm_bl2_line_point_unit_square as line_point_unit
    from gkm_f1_energy_two import FRAMES
    import gkm_f1_fiber_h as fiber_h
    import gkm_f1_fiber_one_marking as fiber_single
    import gkm_f1_fiber_remaining as fiber
    import gkm_f1_plane_line as f1_line
    import gkm_genus_one_descendants as genus_one
    import gkm_genus_two_degree_zero as degree_zero
    import gkm_genus_two_divisor_pairs as divisor_pairs
    import gkm_genus_two_energy_one as primitive_frame
    import gkm_genus_two_one_marking as singleton
    import gkm_genus_two_positive_pairs as positive_pairs
    import gkm_genus_two_unit_pairs as unit_pairs
    import gkm_genus_zero_descendants as genus_zero
    import gkm_plane_few_markings as plane
    import gkm_zero_divisor_pairs as zero_divisors

    # Use each held report's original validator, including the independent plane manifest.
    readers = {module.KIND: module.read_report for module in
               (fiber_h, genus_one, genus_zero, degree_zero, plane)}
    readers["gkm_localization.three_point_descendants"] = read_report
    genus_two_frames = {module.KIND: module.REQUESTS for module in
                        (fiber, singleton, line, canonical, unit_pairs, divisor_pairs, positive_pairs,
                         line_point_unit, primitive_frame, f1_line, fiber_single, mixed_exceptional,
                         double_pairs, double_singles, double_all)}
    genus_two_frames.update({positive_plane.kind(name): frame
                             for name, frame in positive_plane.REQUESTS.items()})
    divisor_targets = {zero_divisors.kind(t): t for t in zero_divisors.FRAMES}
    genus_two_frames.update({f.kind: f.requests for f in FRAMES.values()})
    try:
        data = json.loads(raw, object_pairs_hook=unique_object)
        kind = data["kind"]
        original = None
        if kind == KIND:
            if len(data["cases"]) != 1:
                raise ValueError("A single research query must have exactly one row")
            row, = data["cases"]
            submitted = row["equivariant"]
            regular = regular_presentation(submitted, row.get("regular_representative"))
            if regular != submitted:
                original = submitted
                row["equivariant"] = regular
            report, grouped = read_report(json.dumps(data), requests=frame(query), genus=query["genus"], kind=kind)
        elif kind == zero_divisors.kind("X2") + ".partial":
            from gkm_zero_divisor_checkpoints import read_partial
            report, _ = read_partial(raw, "X2")
            grouped = {"X0": [], "X1": [], "X2": report["cases"]}
        elif kind in divisor_targets:
            report, grouped = read_report(raw, requests=zero_divisors.requests(divisor_targets[kind]),
                                          genus=2, kind=kind)
        elif kind in readers:
            report, grouped = readers[kind](raw)
        elif kind in genus_two_frames:
            report, grouped = read_report(raw, requests=genus_two_frames[kind], genus=2, kind=kind)
        else:
            raise ValueError("Unsupported GKM descendant report kind")
        beta, powers, labels = frame(query)[query["target"]][0]
        matches = [case for case in grouped[query["target"]]
                   if case["genus"] == query["genus"] and tuple(case["class"]) == beta and
                   tuple(case["powers"]) == powers and tuple(case["labels"]) == labels]
        if len(matches) != 1:
            raise ValueError("GKM report has no unique row for the requested target, class and markings")
        case = matches[0]
        claim = {"report_sha256": hashlib.sha256(raw).hexdigest(), "kind": kind,
                 "producer_revision": report["source"]["revision"], "environment": report["environment"],
                 "equivariant": case["equivariant"], "ordinary": case["ordinary"]}
        if original is not None:
            claim["regular_representative"] = claim["equivariant"]
            claim["equivariant"] = original
        target = query["target"]
        ordered = (beta, powers, labels)
        if (target == "X0" and query["genus"] == 0 and beta == (1,) and labels == ("pt",)):
            claim["plane_line_point_power"] = powers[0]
        elif query["genus"] == 2 and powers == (3,) and (target, beta, labels) in EXCEPTIONAL_CUBICS:
            claim["exceptional_cubic"] = EXCEPTIONAL_CUBICS[target, beta, labels]
        elif query["genus"] == 2 and ordered in double_singles.REQUESTS[target]:
            claim["double_exceptional_singleton_row"] = double_singles.REQUESTS[target].index(ordered)
        elif query["genus"] == 2 and ordered in double_pairs.REQUESTS[target]:
            claim["double_exceptional_pair_row"] = double_pairs.REQUESTS[target].index(ordered)
        elif query["genus"] == 2 and ordered in primitive_frame.REQUESTS[target]:
            claim["energy_one_row"] = {"target": target, "index": primitive_frame.REQUESTS[target].index(ordered)}
        elif query["genus"] == 2 and ordered in fiber_single.REQUESTS[target]:
            claim["fiber_one_marking_row"] = fiber_single.REQUESTS[target].index(ordered)
        elif query["genus"] == 2 and ordered in mixed_exceptional.REQUESTS[target]:
            claim["mixed_exceptional_row"] = mixed_exceptional.REQUESTS[target].index(ordered)
        elif query["genus"] == 2:
            for name, packet in FRAMES.items():
                if ordered in packet.requests[target]:
                    claim["f1_energy_two_row"] = {"frame": name, "index": packet.requests[target].index(ordered)}
                    break
            else:
                if target in zero_divisors.FRAMES:
                    divisor_rows = zero_divisors.requests(target)[target]
                    if ordered in divisor_rows:
                        if target == "X1":
                            claim["zero_divisor_row"] = {"target": target, "index": divisor_rows.index(ordered)}
                        else:
                            from gkm_zero_divisor_checkpoints import key, read_partial
                            held = Path(__file__).resolve().parents[1] / "environments/gkm-zero-divisor-bl2-partial.json"
                            _, native_rows = read_partial(held.read_bytes(), target)
                            checked_rows = [key(row) for row in native_rows]
                            if ordered in checked_rows:
                                claim["zero_divisor_row"] = {"target": target, "partial": True,
                                                            "index": checked_rows.index(ordered)}
        if query["genus"] == 2 and ordered in double_all.REQUESTS[target]:
            claim["double_exceptional_comparison_row"] = double_all.REQUESTS[target].index(ordered)
        if query["genus"] == 2:
            for name, requests in positive_plane.REQUESTS.items():
                if ordered in requests[target]:
                    claim["positive_plane_row"] = {"frame": name, "index": requests[target].index(ordered)}
                    break
        return claim
    except (KeyError, TypeError, IndexError, ZeroDivisionError) as err:
        raise ValueError("Malformed GKM report") from err


def main():
    from gw_query import validate

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("request", type=Path)
    parser.add_argument("--producer", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        query, _, _ = validate(json.loads(args.request.read_text(), object_pairs_hook=unique_object))
        raw = explore_report(args.producer, frame(query), query["genus"], KIND)
        incoming_claim(query, raw)
        with args.output.open("xb") as output:
            output.write(raw)
    except (OSError, ValueError, subprocess.CalledProcessError) as err:
        print(f"GKM exploration failed: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
