# CohFT design decisions before implementation

This document records the architectural decisions that should be settled before
implementing M3 and the full CohFT/GW layers. Decisions are discussed in the
order listed below. A decision is marked **Settled** only after it has been
explicitly accepted.

## Decision summary

| ID | Question | Current recommendation | Status |
| --- | --- | --- | --- |
| D1 | Which part of stable-curve cohomology is in scope? | Even cohomology only | **Settled** |
| D2 | How is cohomological degree represented? | Codimension degree: Lean degree `d` represents `H^(2d)` | **Settled** |
| D3 | Is the grading internal or external? | One total ring with internal degree submodules | **Settled** |
| D4 | What is the base coefficient ring? | A commutative `Q`-algebra for the new CohFT/GW layer | Pending; discuss next |
| D5 | What is the target of separating pullback? | Use `H₁ tensor[R] H₂`, making the needed Kunneth identification part of the abstract system | Pending |
| D6 | How are genera and label sets indexed? | Retain arbitrary finite label types and explicit `StableArity` proofs | Pending |
| D7 | What are the directions and composition conventions for geometric maps? | Fix all cohomological operations as contravariant pullbacks with one relabelling convention | Pending |
| D8 | Is the state space graded? | Treat `V` as the ungraded even state space initially | Pending |
| D9 | How much coherence belongs in the first M3 interface? | Primitive maps and their immediate laws only; defer stable graphs | Pending |
| D10 | Where do low-genus geometric facts live? | Separate extension containing the `Mbar(0,3)` and `Mbar(0,4)` facts | Pending |
| D11 | Is `H^0 = R` part of every cohomology system? | No; use an optional connected degree-zero extension | Pending |
| D12 | What validates the initial architecture? | Constant cohomology system plus conversion of the existing topological CohFT | Pending |

Here `Q`, `tensor`, and `H^(2d)` in the table denote `ℚ`, `⊗[R]`, and
ordinary degree-`2d` cohomology respectively; ASCII is used in the table to
keep its source readable.

## Settled decisions

### D1. Even cohomology only

For each stable pair `(g,S)`, the target models

```text
H^even(Mbar(g,S); R).
```

Odd cohomology and Koszul signs are outside the project scope. Products,
external products, relabelling, and gluing therefore use ordinary
commutativity.

### D2. Codimension grading

Lean degree `d` represents ordinary cohomological degree `2d`:

```text
Lean degree d = H^(2d)(Mbar(g,S); R).
```

This is the Chow/codimension convention. In particular:

- `psi`, divisor, and first Chern classes have degree one;
- `kappa_m` has degree `m`;
- `lambda_j` has degree `j`;
- top degree is the complex dimension `3g - 3 + |S|`;
- integration and virtual-dimension formulas do not require factors of two.

### D3. Internal grading

Each `H g S` is one total commutative algebra with degree submodules

```lean
degree : ℕ → Submodule R (H g S).
```

Every element has a finite homogeneous decomposition and multiplication sends
degrees `i` and `j` to degree `i + j`. A homogeneous element can still be given
the type `↥(degree d)`, while a general CohFT class lands directly in the total
ring `H g S`.

The intended implementation is a small project-owned package such as
`EvenGradedAlgebra R` built on mathlib's `GradedAlgebra`, not a reimplementation
of mathlib's grading machinery.

## Pending decisions

### D4. Base coefficient ring

The main options are:

1. arbitrary `CommRing R`;
2. `[CommRing R] [Algebra ℚ R]`;
3. exactly `R = ℚ`;
4. a characteristic-zero field.

The current recommendation is option 2 for the new M3--M9 interfaces. It
contains rational GW theory while allowing Novikov rings, equivariant
parameters, and formal-series coefficient extensions. It also makes all
factorial denominators available. The already completed Frobenius/TFT layer
can remain generic over an arbitrary commutative ring.

This decision is the next one to settle.

### D5. Separating pullback and Kunneth data

For separating gluing, decide whether the pullback has codomain

```text
H(g1, Option S) tensor[R] H(g2, Option T)
```

or a separately supplied cohomology ring of the product moduli space together
with an external-product map. The recommendation is to use the tensor product
directly and regard the required Kunneth identification as an axiom of the
abstract even-cohomology system.

This decision determines the shape of separating CohFT contraction.

### D6. Indexing stable moduli spaces

Decide whether to continue with separate parameters

```lean
(g : ℕ) (S : Type u) [Fintype S] (h : StableArity g S)
```

or introduce a bundled stable-index type. The recommendation is to retain the
current unbundled finite-label convention so that `Option S`, `S ⊕ T`, and
equivalences of label types remain easy to use. Stability proofs should not
affect data, relying on proof irrelevance.

Universe levels for label types and the target family must be fixed as part of
this decision.

### D7. Directions of geometric operations

The project needs one precise convention for:

- relabelling equivalences;
- forgetful pullback;
- separating-gluing pullback;
- nonseparating-gluing pullback.

All cohomology maps should be contravariant, but relabelling notation can still
be oriented in either direction. The chosen convention must make identity,
inverse, and composition laws easy to state and agree with the existing
`MultilinearMap.domDomCongr` convention.

### D8. State-space grading

Decide whether `V` is:

1. an ungraded finite-free module representing only even state-space classes;
   or
2. an internally graded module with a graded perfect pairing.

The recommendation is option 1 for the initial CohFT interface. This matches
the completed project foundations and avoids signs. A separate graded-state
extension can be added if M6 degree constraints require it. The consequence is
that initial M4 classes have target grading but their input degrees are not
tracked by the type system.

### D9. Initial coherence boundary

Decide which laws are fields of the first stable-curve system. The recommended
core contains:

- relabelling identity and composition;
- naturality of primitive gluing under relabelling;
- forgetful identity/composition where defined;
- the immediate forget/glue compatibility needed by the flat-unit axiom;
- symmetry of the two branches or node labels.

General stable graphs, arbitrary iterated gluing, graph contraction, and
independence of all edge-contraction orders should be a later layer. Before
coding, the exact minimal law list must be written down to avoid either an
unusable weak interface or a very large first structure.

### D10. Low-genus geometry

Extraction of a Frobenius algebra and WDVV requires more than primitive maps:

- point-like degree-zero behavior of `Mbar(0,3)`;
- the relevant equality between the two boundary presentations of
  `Mbar(0,4)`.

The recommendation is to place these facts in a `GenusZeroGeometry`-style
extension of the basic M3 system. This keeps the general gluing interface from
silently assuming connectedness or special low-genus relations.

### D11. Connected degree-zero cohomology

Projection to degree zero does not by itself produce a scalar-valued
topological CohFT. One also needs an identification

```text
degreeZero(H g S) equiv R.
```

The recommendation is to make this an optional `ConnectedDegreeZero`-style
extension. The core stable-curve system should not claim that every abstract
target has scalar degree zero.

### D12. First acceptance tests

Before building tautological or stable-graph layers, decide the minimum test of
the architecture. The recommendation is to require:

1. a constant system `H g S = R`, concentrated in degree zero;
2. a generalization of the existing contraction API from scalar codomain `R`
   to an arbitrary target module;
3. conversion of the existing `TopologicalCohFT` into the new full CohFT over
   the constant system;
4. successful relabelling, unit, separating, and nonseparating regression
   examples.

If these examples require excessive instance plumbing or repeated direct-sum
unfolding, the M3 package should be revised before proceeding to M5.

## Discussion order

Continue with D4 and then settle D5--D12 in order. After every decision, update
its status and replace the recommendation with the accepted convention.
