# M10. Geometric realization

The axiomatic theory becomes geometric when its classes are constructed from moduli spaces of stable maps and their virtual fundamental classes. This phase should first be expressed through an abstract realization interface rather than by immediately formalizing the entire construction of virtual classes.

## 1. Stable maps

Let $X$ be a smooth projective target and $\beta$ an effective curve class. The moduli space

$$
\overline{\mathcal M}_{g,S}(X,\beta)
$$

parametrizes stable maps $f:C\to X$ with marked points. It carries evaluation maps

$$
\operatorname{ev}_i:
\overline{\mathcal M}_{g,S}(X,\beta)
\longrightarrow X
$$

and, in the stable range, a stabilization map

$$
\operatorname{st}:
\overline{\mathcal M}_{g,S}(X,\beta)
\longrightarrow
\overline{\mathcal M}_{g,S}.
$$

The actual dimension of the stable-map space can be wrong, so ordinary fundamental classes do not give deformation-invariant intersection numbers.

## 2. Virtual fundamental class

A perfect obstruction theory produces a virtual fundamental class

$$
[\overline{\mathcal M}_{g,S}(X,\beta)]^{\mathrm{vir}}
$$

in the expected dimension. The primary GW class is

$$
\Omega^X_{g,S,\beta}((\gamma_i))
=
\operatorname{st}_*
\left(
\prod_{i\in S}\operatorname{ev}_i^*(\gamma_i)
\cap
[\overline{\mathcal M}_{g,S}(X,\beta)]^{\mathrm{vir}}
\right).
$$

Integrating this class, possibly after multiplying by tautological classes, gives numerical GW invariants.

## 3. Why the axioms hold

Relabelling follows from symmetry of the marked points. The flat-unit property follows from forgetting a marking and the compatibility of virtual classes. Separating gluing follows from the virtual class of a boundary fiber product over the diagonal $X\to X\times X$; contraction by the inverse Poincare pairing is the cohomological expression of that diagonal. Nonseparating gluing is governed by the analogous self-node construction.

The divisor equation uses the compatibility of evaluation classes with the universal curve. Grading follows from virtual dimension. Descendant identities use cotangent-line comparison and boundary formulas.

## 4. Abstract virtual GW package

The first implementation boundary is represented algebraically by a package containing the stabilized primary theory, stable-map descendants, and a descendant--ancestor residual decomposition. A future geometric construction must produce stronger evidence from stable-map objects, evaluation and stabilization maps, virtual classes, pullback and proper pushforward, external products, refined pullback along diagonals, and all required compatibility theorems. In particular, the current residual field does not encode boundary support. The intended future implication is

$$
\text{genuine virtual-geometric construction}
\Longrightarrow
\text{curve-class-resolved axiomatic GW theory}.
$$

Such a construction theorem would mark a precise boundary between axiomatic formalization and virtual intersection theory; it is not currently present.

In Lean, `VirtualGWPackage` is deliberately only an algebraic output carrier. It does not introduce placeholder types for stacks or virtual cycles that no theorem can use; instead it exposes projections to stored `CurveClassGW`, `StableMapDescendants`, and `DescendantAncestorComparison` structures. Inhabiting the carrier does not certify that these fields arise from geometry.

## 5. Longer-term geometry

Constructing the package from first principles would require a theory of Deligne--Mumford or derived stacks, Chow or homology groups, proper pushforward, refined Gysin maps, perfect obstruction theories, intrinsic normal cones, and virtual pullback compatibility. That is a substantial independent project and is not a prerequisite for completing the axiomatic development.

This phase will close the roadmap only when a genuine geometric construction connects the abstract structures back to Gromov--Witten invariants.
