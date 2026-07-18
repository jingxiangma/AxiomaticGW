# M8. Descendants and descendant--ancestor comparison

Primary GW invariants use only evaluation classes. Descendants additionally use cotangent-line classes on moduli spaces of stable maps. Ancestors use cotangent-line classes pulled back from moduli spaces of stable curves. These classes are related, but they are not definitionally the same.

## 1. Stable-map descendants

Let

$$
\overline{\mathcal M}_{g,S}(X,\beta)
$$

be the moduli space of stable maps. The universal stable map has a cotangent line $L_i^{\mathrm{map}}$ at each marking and a class

$$
\psi_i^{\mathrm{map}}=c_1(L_i^{\mathrm{map}}).
$$

For insertions $\gamma_i\in H^*(X)$, the descendant invariant is

$$
\left\langle
\prod_{i\in S}\tau_{k_i}(\gamma_i)
\right\rangle_{g,\beta}
=
\int_{[\overline{\mathcal M}_{g,S}(X,\beta)]^{\mathrm{vir}}}
\prod_{i\in S}
(\psi_i^{\mathrm{map}})^{k_i}
\operatorname{ev}_i^*(\gamma_i).
$$

These are numerical invariants unless additional markings are retained and the expression is pushed forward to a stable-curve space.

## 2. Ancestors

The stabilization map to the moduli of curves gives ancestor cotangent classes

$$
\bar\psi_i=\operatorname{st}^*(\psi_i^{\mathrm{curve}}).
$$

Replacing $\psi_i^{\mathrm{map}}$ by $\bar\psi_i$ defines ancestor invariants. Ancestors interact more directly with CohFT gluing because their psi classes come from the same stable-curve spaces on which CohFT classes live.

## 3. Comparison

The two cotangent lines differ when stabilization contracts a component. Schematically,

$$
\psi_i^{\mathrm{map}}
=
\bar\psi_i+\text{boundary corrections}.
$$

The correction strata describe rational components that become unstable after forgetting the map. Iterating this identity expresses descendants in terms of ancestors and lower-complexity boundary contributions. In generating-function form the comparison is commonly organized by a fundamental solution, or $S$-operator, built from genus-zero two-point descendants.

The formalization therefore maintains distinct interfaces for stable-map and stable-curve psi classes. Their comparison is recorded through explicit residual and optional stabilization-boundary hypotheses, never a definitional equality.

## 4. Abstract descendant package

An axiomatic descendant extension needs stable-map psi classes, evaluation insertions, integration against a virtual class, and formulas for forgetting markings and restricting to boundary strata. String, dilaton, divisor, and topological recursion equations follow only after these properties are supplied.

Once primary, ancestor, and descendant correlators are defined with suitable completions, they can be assembled into all-genus generating functions. See [M9: all-genus potentials and equations](M09PotentialsAndEquations.md).

## 5. Implemented boundary

`GromovWittenTheory.ancestorClass` uses stable-curve `PsiClasses`, while `StableMapDescendants.descendantClass` is a distinct stabilized stable-map family with zero-power, relabelling, total-degree, and negative-total-degree laws. `DescendantAncestorComparison` remains the weak residual API. The optional `StabilizationBoundaryComparison` strengthens it by expressing that residual as a finite sum over positive-degree rational-tail splittings, with the boundary pushforward, tail weights, and state-space tail operators visible as hypotheses. Those same tail operators define `TwoPointCalibration`; a separately named two-point boundary identity implies coefficientwise symplecticity. `GiventalComparison` exposes the additional genus-one factor and quantized partition identity rather than claiming they follow from a bare residual. Concrete stable-map geometry must still construct these packages. No definitional identification between the two cotangent-line theories is used.
