# AxiomaticGW

Lean formalization of the algebraic foundations of axiomatic Gromov--Witten
theory.

The repository is the home of the full project, but development proceeds in
small verified milestones.  The current milestone is the finite-free,
commutative Frobenius-algebra layer needed for topological field theories and
CohFT gluing.

## Final scope

The endpoint is an **all-genus axiomatic Gromov--Witten theory**, resolved by
curve class and equipped with the complete descendant package.  In particular,
the final theory is intended to support

- primary GW classes for every stable `(g, S)` and every effective curve class;
- separating and nonseparating gluing, the flat unit, grading, virtual
  dimension, effectivity, and the divisor axiom;
- descendant insertions indexed by arbitrary powers of stable-map
  `psi`-classes;
- ancestor insertions using stable-curve `psi`-classes, together with the
  descendant--ancestor comparison;
- Novikov completion and genus expansion;
- all-genus descendant and ancestor potentials;
- string, dilaton, divisor, splitting, genus-reduction, and tautological
  relations whenever the required abstract geometric operations are present.

A bare CohFT already contains all stable genera.  The genus-zero API is only a
derived restriction used to prove associativity and WDVV.  Descendants are not
fields of the minimal CohFT structure: they require `psi`-classes,
pushforwards, integration, and projection formulas.  Moreover, stable-map
descendants and stable-curve ancestors are kept distinct.

## Architecture

The intended dependency direction is

```text
                         Combinatorics
                        /             \
Mathlib -> Linear -> Frobenius -> TFT  \
                \                       -> CohFT -> GW -> Geometry
                 -> Coefficients       /
                \                     /
                 -> Moduli -----------
```

The planned source layout is:

```text
AxiomaticGW/
  Linear/
    PerfectPairing.lean
    Copairing.lean
    Contraction.lean

  Frobenius/
    Basic.lean
    Constructions.lean
    Coalgebra.lean
    Examples.lean

  TFT/
    Basic.lean
    Frobenius.lean

  Combinatorics/
    StableArity.lean
    FiniteLabels.lean
    StableGraph.lean
    GraphContraction.lean

  Coefficients/
    EffectiveCurveClass.lean
    Novikov.lean
    GenusExpansion.lean
    DescendantVariables.lean

  Moduli/
    StableCurveSystem.lean
    Gluing.lean
    TautologicalSystem.lean
    Integration.lean

  CohFT/
    Basic.lean                 # full all-genus CohFT
    Unit.lean
    GenusZero.lean             # restriction of the all-genus theory
    Frobenius.lean
    TopologicalPart.lean
    Ancestors.lean             # stable-curve psi-classes
    Potential.lean

  GW/
    CurveClass.lean
    Basic.lean                 # beta-resolved, full all-genus primary theory
    Grading.lean
    Divisor.lean
    Novikov.lean
    QuantumProduct.lean
    Ancestors.lean
    Descendants/
      Basic.lean               # stable-map psi insertions
      Axioms.lean
      Comparison.lean          # descendants versus ancestors
      Potential.lean           # all-genus total descendant potential

  Geometry/
    StableMapSystem.lean
    VirtualGWPackage.lean
    Realization.lean

  Examples/
    Point.lean
    FrobeniusTFT.lean
    ProjectiveLine.lean
```

Only modules with implemented content are created.  The tree above records
ownership and dependency boundaries without committing prematurely to Lean
interfaces that have not yet been tested.

The essential formalization chain is

```text
perfect duality and contractions
  -> Frobenius algebra and topological CohFT
  -> full all-genus CohFT
  -> beta-resolved all-genus primary GW theory
  -> Novikov-valued CohFT and quantum products
  -> full descendants, ancestors, comparison, and total potentials
  -> realization from an abstract virtual stable-map package
```

## Current milestone

The current public API follows the chain

```text
counit -> trace pairing -> perfect duality -> copairing -> handle element.
```

The core definitions are basis-free.  `CommFrobeniusAlgebra` is an explicit
object rather than a typeclass, since a fixed algebra can admit more than one
Frobenius functional.

Build the project with:

```bash
lake build
```
