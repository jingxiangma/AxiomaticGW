# AxiomaticGW

Lean formalization of the algebraic foundations of axiomatic Gromov--Witten
theory.

The repository is the home of the full project, but development proceeds in
small verified milestones.  The current milestone is the finite-free,
commutative Frobenius-algebra layer needed for topological field theories and
CohFT gluing.

## Architecture

The intended dependency direction is

```text
Mathlib
   |
   v
Linear ---> Frobenius ---> TFT
   |                        |
   +----> Combinatorics ----+----> CohFT ---> GW
   +----> Moduli -----------+                 |
                                               v
                                           Geometry
```

Only modules with implemented content are created.  Planned later layers are:

- `TFT`: the topological CohFT associated to a Frobenius algebra;
- `Combinatorics`: stable arities, finite labels, and stable graphs;
- `Moduli`: abstract stable-curve cohomology and tautological interfaces;
- `CohFT`: a genus-zero precursor, full all-genus unital CohFTs, potentials,
  and descendant constructions built from additional tautological data;
- `GW`: curve-class-resolved axioms, Novikov packaging, and quantum products;
- `Geometry`: an abstract virtual-GW realization interface.

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
