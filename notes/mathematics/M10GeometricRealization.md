# M10. Geometric realization

The axiomatic theory becomes geometric when its classes are constructed from moduli spaces of stable maps and their virtual fundamental classes. The repository expresses the first implementation boundary through an abstract algebraic carrier rather than pretending to construct virtual classes.

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

The stable-map stack need not be smooth, pure-dimensional, or of the expected dimension, so its ordinary fundamental class does not supply the required deformation-invariant intersection theory.

## 2. Virtual fundamental class

A perfect obstruction theory of the expected virtual dimension produces a virtual fundamental class

$$
[\overline{\mathcal M}_{g,S}(X,\beta)]^{\mathrm{vir}}
$$

in the expected dimension. First form the homology or Chow class

$$
I^X_{g,S,\beta}((\gamma_i))
:=
\operatorname{st}_*
\left(
\prod_{i\in S}\operatorname{ev}_i^*(\gamma_i)
\cap
[\overline{\mathcal M}_{g,S}(X,\beta)]^{\mathrm{vir}}
\right).
$$

When Poincare duality is available, the cohomology-valued GW class used by a CohFT is

$$
\Omega^X_{g,S,\beta}((\gamma_i))
=\operatorname{PD}\bigl(I^X_{g,S,\beta}((\gamma_i))\bigr)
\in H^*(\overline{\mathcal M}_{g,S}).
$$

This distinction avoids identifying a pushed-forward virtual homology class with a cohomology class without duality. Numerical invariants are obtained by integrating the cohomology class, possibly after multiplying by tautological classes.

## 3. Why the axioms hold

Relabelling follows from symmetry of the marked points. The flat-unit property follows from forgetting a marking and the compatibility of virtual classes. In the project's even-cohomology convention, choose a basis $(e_a)$ of the state space and inverse Poincare matrix $(\eta^{ab})$. The cohomology class dual to the diagonal is

$$
\operatorname{PD}([\Delta_X])
=\sum_{a,b}\eta^{ab}e_a\otimes e_b.
$$

The stable-map boundary is a fiber product over $X\times X$ pulled back along $\Delta_X$. Applying the virtual splitting and projection formulas therefore produces exactly the inverse-metric sums in the CohFT gluing axioms. The nonseparating formula uses the same diagonal class for the two branches of a self-node.

The divisor equation uses the compatibility of evaluation classes with the universal curve. Grading follows from virtual dimension. Descendant identities use cotangent-line comparison and boundary formulas.

## 4. Abstract virtual GW package

The first implementation boundary is represented algebraically by a package containing the stabilized primary theory, stable-map descendants, and a descendant--ancestor residual decomposition. A future geometric construction must produce stronger evidence from stable-map objects, evaluation and stabilization maps, virtual classes, pullback and proper pushforward, external products, refined pullback along diagonals, and all required compatibility theorems. In particular, the current residual field does not encode boundary support. The intended future implication is

$$
\text{constructed virtual-geometric data}
\Longrightarrow
\text{curve-class-resolved axiomatic GW theory}.
$$

Such a construction theorem would mark a precise boundary between axiomatic formalization and virtual intersection theory; it is not currently present.

In Lean, `VirtualGWPackage` is deliberately only an algebraic output carrier. It does not introduce placeholder types for stacks or virtual cycles that no theorem can use; instead it exposes projections to stored `GromovWittenTheory`, `StableMapDescendants`, and `DescendantAncestorComparison` structures. The separate optional `StabilizationBoundaryComparison` package strengthens the weak residual with explicit positive-degree rational-tail data, but neither package certifies that its fields arise from geometry.

## 5. Longer-term geometry

Constructing the package from first principles would require a theory of Deligne--Mumford or derived stacks, Chow or homology groups, proper pushforward, refined Gysin maps, perfect obstruction theories, intrinsic normal cones, and virtual pullback compatibility. That is a substantial independent project and is not a prerequisite for completing the axiomatic development.

This phase will close the roadmap only when a concrete geometric construction connects the abstract structures back to Gromov--Witten invariants.
