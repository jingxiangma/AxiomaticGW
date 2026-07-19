# Completed milestone: from Frobenius algebras to topological field theory

This note records the completed formalization phase after the commutative Frobenius-algebra and coalgebra layer. The milestone specifications below retain their implementation-order wording as a historical record; the status table states the delivered result. The target is the algebraic correlator model of a closed oriented two-dimensional topological field theory. The geometric bordism category is not formalized.

For the underlying definitions and mathematical explanations, see [M1: perfect pairings and Frobenius algebras](../mathematics/M01PerfectPairingsAndFrobeniusAlgebras.md) and [M2: two-dimensional topological field theory](../mathematics/M02TwoDimensionalTFT.md).

For a commutative Frobenius algebra $(A,\epsilon)$ with handle element $E$, the central construction is the finite-labelled correlator

$$
\omega_{g,S}((a_s)_{s\in S})
=
\epsilon\left(\prod_{s\in S}a_s\,E^g\right),
$$

where $g\in\mathbb N$ and $S$ is an arbitrary finite label type. The use of finite label types, rather than only $\operatorname{Fin}(n)$, prepares the API for CohFT relabelling and gluing.

## Implementation status

| Milestone | Status | Verified content |
| --- | --- | --- |
| T0 | Complete | Scope, finite-label convention, and the distinction from a geometric bordism category are recorded. |
| T1 | Complete | `MultilinearMap.mkPiAlgebra` and the project relabelling lemma support the finite-labelled correlator calculations. |
| T2 | Complete | `CommFrobeniusAlgebra.correlator` and its evaluation and relabelling theorems compile for arbitrary finite label types. |
| T3 | Complete | Empty, one-, two-, and three-input normalizations, unit insertion, and handle recursion compile. |
| T4 | Complete | Basis-free `contractTwo`, `selfContract`, and `pairContract` operations compile with explicit evaluation lemmas. |
| T5 | Complete | Linearity and invariance under swapping the two node labels compile. |
| T6 | Complete | The abstract metric contraction and Frobenius sewing identities compile without choosing a basis. |
| T7 | Complete | Nonseparating contraction of a correlator is proved to add one handle. |
| T8 | Complete | Separating contraction of two correlators is proved to give the correlator of the glued component. |
| T9 | Complete | `TwoDimensionalTFT` and `CommFrobeniusAlgebra.toTwoDimensionalTFT` compile. |
| T10 | Complete | Base-ring and product-algebra correlators and API regression tests compile. |
| T11 | Complete | Stable arities, `TopologicalCohFT`, and the stable restriction of a correlator theory compile. |
| T12 | Complete for the current fixed-algebra API | The counit and three-point product are extracted, the forward theory recovers the original multiplication, and the Frobenius round trip is proved. A classification on a bare module requires separately bundling the extracted ring structure. |

The status table is updated only after the corresponding Lean declarations compile. Final verification with `lake build`, `lake lint`, and `lake test` passes for the completed phase.

## T0. Fix the scope and conventions

The implemented theory uses scalar-valued correlators for every genus and every finite label type, including unstable arities. `TopologicalCohFT` restricts these correlators to stable pairs.

Before bundling a theory, record the conventions for tensor orientation, distinguished gluing labels, and relabelling. The initial implementation should not claim that the oriented bordism category has been formalized.

**Completion criterion:** The correlator interface and tensor conventions are documented before a bundled TFT structure is introduced.

## T1. Finite-labelled multiplication

Create `AxiomaticGW/TFT/FiniteProduct.lean` using mathlib's existing `MultilinearMap.mkPiAlgebra` and `MultilinearMap.domDomCongr`.

Prove that the multilinear product evaluates as $\prod_{s\in S}a_s$, is invariant under an equivalence of label types, gives $1$ for the empty label type, factors over a disjoint union, and is unchanged when the algebra unit is inserted at a new label.

**Completion criterion:** All finite-product manipulations needed by the correlator formula work directly with arbitrary finite label types, without converting them to `Fin n`.

## T2. Define the Frobenius correlators

Create `AxiomaticGW/TFT/Correlator.lean` and define a multilinear map of the form

```lean
noncomputable def CommFrobeniusAlgebra.correlator
    (F : CommFrobeniusAlgebra R A)
    (g : ℕ) (S : Type*) [Fintype S] :
    MultilinearMap R (fun _ : S ↦ A) R
```

Its primary evaluation theorem should be

$$
F.\operatorname{correlator}_{g,S}(a)
=
F.\operatorname{counit}
\left(
\left(\prod_{s\in S}a_s\right)F.\operatorname{handleElement}^g
\right).
$$

**Completion criterion:** The definition and evaluation theorem compile for every finite label type $S$.

## T3. Low-genus normalization and elementary identities

Prove the special cases

$$
\omega_{0,\varnothing}=\epsilon(1),
\qquad
\omega_{0,1}(a)=\epsilon(a),
$$

$$
\omega_{0,2}(a,b)=\eta(a,b),
\qquad
\omega_{0,3}(a,b,c)=\eta(ab,c).
$$

Also prove relabelling invariance, insertion of the algebra unit, and the elementary genus recursion coming from $E^{g+1}=E^gE$.

**Completion criterion:** The counit, pairing, multiplication, unit, and handle operation appear as recognizable special cases of the correlators.

## T4. Named-slot contraction

Create `AxiomaticGW/Linear/Contraction.lean`. Define one operation for contracting two slots of a single multilinear map and another for contracting one slot from each of two multilinear maps.

The preferred label conventions are `Option S` for one distinguished gluing label, `S ⊕ Fin 2` for two distinguished gluing labels, and `S ⊕ T` for the labels remaining after separating gluing.

**Completion criterion:** Both contraction operations have explicit evaluation lemmas in terms of the copairing.

## T5. Contraction coherence

Prove that swapping the two contracted slots does not change the contraction, contraction is natural under relabelling, contraction is linear in the multilinear map, contraction of the pairing with its copairing gives the identity, and the orientation of one internal edge does not matter.

The theorem that several disjoint contractions commute can wait until stable graphs are introduced.

**Completion criterion:** The one-edge gluing proofs use named contraction theorems and do not unfold the construction of the copairing.

## T6. Frobenius sewing identity

Prove the basis-free form of the central separating-sewing identity. If a basis notation writes $C_\eta=\sum_i u_i\otimes v_i$, the identity is

$$
\sum_i\epsilon(xu_i)\epsilon(v_i y)=\epsilon(xy).
$$

The Lean proof should use the existing contraction characterization of the Casimir tensor, not a chosen basis.

**Completion criterion:** Separating gluing reduces to this named theorem and ordinary commutative-ring calculations.

## T7. Nonseparating gluing

Prove the handle-attachment identity

$$
\operatorname{selfContract}
\left(\omega_{g,S\sqcup\{+,-\}}\right)
=
\omega_{g+1,S}.
$$

Contracting the two new inputs inserts $\mu(C_\eta)=E$.

**Completion criterion:** Genus reduction is proved for every finite label type $S$.

## T8. Separating gluing

Prove

$$
\operatorname{pairContract}
\left(
\omega_{g_1,S\sqcup\{\star\}},
\omega_{g_2,T\sqcup\{\star\}}
\right)
=
\omega_{g_1+g_2,S\sqcup T}.
$$

The proof should combine the sewing identity with $E^{g_1}E^{g_2}=E^{g_1+g_2}$.

**Completion criterion:** Gluing two connected surfaces agrees with the correlator assigned to the glued surface.

## T9. Bundle the two-dimensional TFT

Create `AxiomaticGW/TFT/Basic.lean` and `AxiomaticGW/TFT/Frobenius.lean`. The canonical `TwoDimensionalTFT` name follows the mathematical literature; its docstring identifies the implemented object as the correlator presentation and does not claim that the bordism category or symmetric monoidal functor has been constructed.

The bundled data should include the state space, symmetric perfect pairing, finite-labelled correlators, relabelling, unit insertion, separating gluing, nonseparating gluing, and normalization at genus zero with two inputs.

Construct

```lean
CommFrobeniusAlgebra.toTwoDimensionalTFT
```

from every finite-free commutative Frobenius algebra.

**Completion criterion:** Every current `CommFrobeniusAlgebra` canonically produces the bundled two-dimensional TFT.

## T10. Examples and regression tests

For the base-ring example, prove

$$
\omega_{g,S}((a_s))=\prod_s a_s.
$$

For the product algebra $R\times R$, compute the correlators using the two coordinate idempotents. Add regression tests for relabelling, unit insertion, separating gluing, nonseparating gluing, and the empty label type.

**Completion criterion:** `lake build`, `lake lint`, and `lake test` all pass without `sorry` or `admit`.

## T11. Restrict to a topological CohFT

After the two-dimensional TFT is stable, create `AxiomaticGW/Combinatorics/StableArity.lean` and `AxiomaticGW/CohFT/Topological.lean`.

Represent the stability condition without natural-number subtraction, for example by

$$
3\leq 2g+|S|.
$$

Restrict the correlators to stable arities and interpret their scalar values as degree-zero CohFT classes.

**Completion criterion:** Every Frobenius algebra produces a bundled scalar-valued or degree-zero topological CohFT.

## T12. Reverse construction and classification

This was implemented after the forward construction rather than as its prerequisite. It recovers the counit from $\omega_{0,1}$, the pairing from $\omega_{0,2}$, and multiplication from $\omega_{0,3}$, then proves the applicable round-trip theorems in the fixed-algebra API.

The intended classification result is

$$
\text{commutative Frobenius algebras}
\simeq
\text{two-dimensional TFTs}.
$$

### Implemented boundary

The current repository represents `CommFrobeniusAlgebra R A` on a carrier `A` that already has `CommRing A` and `Algebra R A` instances. Within that design, T12 now extracts the one-point counit and the three-point bilinear product, proves that the theory constructed from a Frobenius algebra recovers its original multiplication, constructs the reverse Frobenius structure under trace compatibility, and proves the Frobenius round trip.

A literal equivalence starting from a bare module would also have to install the extracted multiplication and unit as new `CommRing` and `Algebra` instances and prove that those instances use the module's existing addition and scalar action. That is a larger bundled-algebra refactor and is recorded as a later foundational extension rather than being hidden inside the correlator milestone.

## Historical implementation order

```text
T1 finite products
  -> T2 correlator definition
  -> T3 elementary identities
  -> T4--T5 contraction API
  -> T6 sewing identity
  -> T7--T8 gluing
  -> T9 bundled theory
  -> T10 examples
```

This order was completed through T12. Current project priorities are recorded in [`ImplementationProgress.md`](ImplementationProgress.md), not in this historical milestone sequence.
