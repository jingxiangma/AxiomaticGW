# Mathematical terminology audit

This ledger records the repository-wide terminology review completed on 2026-07-18. It covers the public entry point, all 42 production modules, their module docstrings and public declaration comments, public structures and definitions, and the associated theorem families. Private helpers were checked for local accuracy but are not presented as literature-level objects.

## Sources and policy

The primary terminology sources were the TeX archives for Dumitrescu's *On 2-dimensional topological field theories*, Kontsevich--Manin's *Gromov-Witten classes, quantum cohomology, and enumerative geometry*, Mulase--Safnuk's *Mirzakhani's recursion relations, Virasoro constraints and the KdV hierarchy*, and Givental's *Gromov-Witten invariants and quantization of quadratic hamiltonians*. The [online reference ledger](../references/online/README.md) records source URLs and access metadata.

Public names use a standard literature term when the represented object has that mathematical role. Project-specific carriers retain descriptive qualifiers. When a carrier uses a standard term but does not encode every usual property, its module docstring and the limitations below state the exact formal boundary.

## Canonical changes

| Earlier name or path | Canonical name or path | Reason |
| --- | --- | --- |
| `TopologicalCorrelatorTheory` | `TwoDimensionalTFT` | The whole theory is a two-dimensional TFT; correlators are its component maps. |
| `threePointFunctional` | `threePointFunction` | Three-point function/correlator is the standard term. |
| `CurveClassGW` | `GromovWittenTheory` | The structure contains the primary classes together with the metric, unit, grading, gluing, normalization, and dimension axioms. |
| `smallProductCoefficient`, `smallProductSeries` | `smallQuantumProductCoefficient`, `smallQuantumProduct` | The mathematical operation is the small quantum product. |
| `formalBigProduct` family | `bigQuantumProduct` family | The mathematical operation is the big quantum product; formal completion is part of its representation. |
| `GenusZeroHigherBoundary.higherWDVV` | `GenusZeroWDVV.wdvv` | The field is precisely scalar genus-zero WDVV at arbitrary primary background. |
| `GW/QuantumProduct.lean` | `GW/SmallQuantumProduct.lean` | The module proves the small quantum-product laws. |
| `GW/FormalQuantumProduct.lean` plus the former `GW/BigQuantumProduct.lean` | consolidated `GW/BigQuantumProduct.lean` | One module now owns the big product, WDVV, associativity, and primary potential. |
| `AxiomaticGW.Point.Descendants` | `AxiomaticGW.PointTarget.Descendants` | The target is a point, matching the existing `PointTarget` namespace and the standard phrase “GW theory of a point.” |

## Comment vocabulary

| Avoided wording | Standard or precise wording | Reason |
| --- | --- | --- |
| flat identity | flat unit | CohFT and Gromov--Witten literature uses the flat-unit axiom. |
| one/two/three-input correlator | one/two/three-point correlator | The mathematical object is an n-point function; “input” remains appropriate only when discussing Lean multilinear slots. |
| curve ancestor, descendant powers in an ancestor correlator | stable-curve ancestor, cotangent powers | Ancestors use cotangent-line classes on the stable-curve moduli space and must remain distinct from stable-map descendants. |
| coefficient product, curve-class theory | fixed-class contribution to the small quantum product, genus-zero Gromov--Witten theory | These phrases identify the standard operation and the theory supplying its coefficients. |
| genuine stabilization comparison, quantized inverse calibration on completed Fock potentials | supplied factorized rational-tail comparison, supplied quantized action on coefficientwise Fock data | The current structures package hypothesis data and do not construct the underlying geometry or quantization. |

## Formal limitations of retained terms

| Term | Formal boundary |
| --- | --- |
| `TwoDimensionalTFT` | Implements the finite-labelled correlator presentation. The oriented bordism category and symmetric monoidal functor are not constructed. |
| `TopologicalCohFT` | Implements only stable arities with scalar, degree-zero values. |
| `StableCurveCohomology` | Is an abstract even-cohomology target with named pullbacks, not the cohomology of constructed moduli stacks. |
| `StableGraphPullbacks` | Stores order-coherent graph pullbacks; it does not define combinatorial edge contraction or construct geometric boundary maps. |
| `GromovWittenTheory` | Is coefficientwise in effective curve class and axiomatic; it does not construct stable-map spaces or virtual classes. |
| `DescendantAncestorComparison.boundaryCorrection` | Is only the residual difference unless a `StabilizationBoundaryComparison` supplies explicit rational-tail boundary support. |
| `TwoPointCalibration` | Stores two-point operator coefficients and a constant term. Symplecticity requires `CalibrationBoundaryRelation`; a geometric fundamental solution is not constructed. |
| `CompletedFockPotential` | Is a coefficientwise genus-indexed carrier. It is not the unrestricted exponential partition function or a constructed topological Fock completion. |
| `QuantizedCalibrationAction` | Is explicitly supplied additive action data; the repository does not derive a quantization construction from the calibration alone. |
| `GiventalComparison` | Records the quantized descendant--ancestor identity as additional hypothesis data. |
| `VirtualGWPackage` | Bundles axiomatic outputs expected from future virtual geometry; inhabiting it does not certify a virtual-geometric origin. |

## Module audit

| Module | Terminology decision |
| --- | --- |
| `AxiomaticGW.lean` | Public imports use the canonical small/big quantum-product and point-target module paths. |
| `Coefficients/DescendantVariables.lean` | `DescendantVariable`, `FormalPotential`, and formal partial-derivative terminology retained. |
| `Coefficients/EffectiveCurveClass.lean` | `EffectiveCurveMonoid`, energy bounds, and curve-class splittings retained as the project finiteness package. |
| `Coefficients/GenusExpansion.lean` | Genus potentials and total free energy retained; the missing exponential completion is explicit. |
| `Coefficients/Novikov.lean` | `NovikovSeries`, coefficients, monomials, and the finite-support inclusion retained. |
| `CohFT/Ancestors.lean` | Ancestor correlator, stable-curve psi, integration, and pushforward terminology retained. |
| `CohFT/Basic.lean` | `CohFT`, `GradedCohFT`, and `GradedStateSpace` are standard and retained. |
| `CohFT/Classification.lean` | Topological CohFT classification and Frobenius reconstruction terminology retained. |
| `CohFT/Constant.lean` | Constant cohomology target and topological-part conversion names retained. |
| `CohFT/Frobenius.lean` | `threePointFunction` is canonical; product, WDVV, and Frobenius extraction terminology retained. |
| `CohFT/GenusZero.lean` | `GenusZeroCohFT` and genus-zero restriction terminology retained. |
| `CohFT/StableCurve.lean` | Stable-curve cohomology, relabelling, gluing, and low-genus package names retained with their abstract boundary. |
| `CohFT/Tautological.lean` | Psi classes, kappa classes, integration, forgetful pushforward, and the forgetful correction formula retained. |
| `CohFT/Topological.lean` | `TopologicalCohFT` retained for the stable scalar degree-zero theory; restriction now starts from `TwoDimensionalTFT`. |
| `CohFT/TopologicalPart.lean` | Topological part and scalar projection terminology retained. |
| `Combinatorics/StableArity.lean` | Stable arity and stable-curve dimension terminology retained. |
| `Combinatorics/StableGraph.lean` | Stable graph, half-edge, valence, Betti number, total genus, and contraction-order terminology retained; missing contraction is explicit. |
| `Frobenius/Basic.lean` | Trace pairing and commutative Frobenius algebra terminology retained. |
| `Frobenius/Coalgebra.lean` | Comultiplication and coalgebra terminology follows mathlib and is retained. |
| `Frobenius/Constructions.lean` | Casimir/canonical copairing and handle-element terminology retained. |
| `Frobenius/Examples.lean` | Base-ring and product-algebra example names retained. |
| `GW/Basic.lean` | `GromovWittenTheory` is canonical; `GWOutputDegree` and `GWDivisorAxiom` retain the standard GW abbreviation. |
| `GW/BigQuantumProduct.lean` | Big quantum product, genus-zero WDVV, associativity, and primary-potential terminology standardized. |
| `GW/Constant.lean` | `constantGromovWittenTheory` is the beta-zero reference namespace. |
| `GW/Descendants/Basic.lean` | Stable-map descendants, ancestor classes, and numerical invariant terminology retained. |
| `GW/Descendants/Comparison.lean` | Descendant--ancestor comparison retained; the weak boundary-correction limitation is explicit. |
| `GW/Descendants/Equations.lean` | String, dilaton, and divisor equation terminology retained. |
| `GW/Descendants/FullPotential.lean` | Unstable conventions, extended invariants, and full descendant-potential terminology retained. |
| `GW/Descendants/Potentials.lean` | Descendant/ancestor potentials, insertion derivatives, and residual-series terminology retained. |
| `GW/Descendants/Stabilization.lean` | Stabilization comparison, calibration, symplecticity, quantized action, and Givental comparison retained with explicit hypothesis boundaries. |
| `GW/SmallQuantumProduct.lean` | Small quantum product, fixed-class coefficients, WDVV, and associativity terminology standardized. |
| `Geometry/VirtualGWPackage.lean` | `VirtualGWPackage` retained as an explicitly non-realizing algebraic output carrier. |
| `Linear/Contraction.lean` | Named-slot contraction, self-contraction, and pair-contraction terminology retained. |
| `Linear/Copairing.lean` | Copairing and tensor-endomorphism correspondence terminology retained. |
| `Linear/PerfectPairing.lean` | Symmetric perfect pairing and duality terminology retained. |
| `PointTarget/Descendants.lean` | Point-target primary class, psi-class intersection numbers, WDVV, and DVV terminology retained under the canonical module path. |
| `Tautological/BasicStrata.lean` | “One-vertex stable graph” and “fundamental stratum” are used for the undecorated graph with no internal edges; the operadic term “corolla” is avoided in the public API. |
| `Tautological/DecoratedStableGraph.lean` | Decorated stable graph, leg, internal half-edge, arithmetic genus, kappa/psi decoration, codimension, graph isomorphism, and decorated stratum follow the standard tautological-ring terminology. |
| `Tautological/Getzler.lean` | `GetzlerStratum` indexes the seven named symmetric cycles on `Mbar(1,4)` and is distinct from `Fin 4`, the marking type. The orbifold-cycle normalization is explicit in `GetzlerStrataEncoding`. |
| `Tautological/LowGenus.lean` | Genus-zero psi-class intersection values and the multinomial formula follow standard point-target intersection notation; agreement with geometric integration is an explicit certificate. |
| `Tautological/StrataAlgebra.lean` | “Certified strata product” is used because the structure records product laws but does not yet implement the common-refinement and excess-intersection algorithm; it is not advertised as the tautological ring. |
| `Tautological/StrataModule.lean` | “Strata module” denotes the free rational module on decorated stable-graph isomorphism classes; “known-relations quotient” avoids claiming that supplied relations generate the full tautological ideal. |
| `Tautological/StrataRealization.lean` | “Realization” denotes a degree-preserving linear map into an abstract stable-curve cohomology target, not a construction of the moduli stack or its cohomology. |
| `TFT/Basic.lean` | The bundled object is canonically `TwoDimensionalTFT`; its fields remain correlators and sewing laws. |
| `TFT/Classification.lean` | `threePointFunction`, Frobenius product recovery, trace compatibility, and round-trip terminology standardized. |
| `TFT/Correlator.lean` | Individual finite-labelled maps remain `correlator`, matching the literature. |
| `TFT/Examples.lean` | Two-dimensional TFT regression examples retain their algebra-specific names. |
| `TFT/FiniteProduct.lean` | Uses mathlib's `MultilinearMap.mkPiAlgebra` directly and records only the missing relabelling lemma. |
| `TFT/Frobenius.lean` | The canonical construction is `CommFrobeniusAlgebra.toTwoDimensionalTFT`. |
| `TFT/Sewing.lean` | Separating and nonseparating sewing terminology retained. |

## Maintenance rule

When adding or renaming a public mathematical declaration, cite the standard term in its docstring or in the relevant mathematical note. Update this ledger when a new module introduces a domain object or when a carrier gains enough structure to justify a stronger standard name.
