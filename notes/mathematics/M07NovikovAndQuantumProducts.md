# M7. Novikov coefficients and quantum products

Curve-class-resolved GW classes form a family indexed by $\beta$. Novikov coefficients package that family into a single CohFT while controlling the generally infinite sum over effective classes.

## 1. Why completion is needed

Formally one wants symbols $Q^\beta$ satisfying

$$
Q^{\beta_1}Q^{\beta_2}=Q^{\beta_1+\beta_2}
$$

and series

$$
\sum_{\beta\in B}a_\beta Q^\beta.
$$

The monoid algebra permits only finite support, which is often too small for GW theory. The project uses the positive locally finite effective monoid fixed in D13: an additive energy $E:B\to\mathbb N$ is positive away from zero, and the entire set of classes below each energy bound is finite. Consequently every coefficient function $B\to R$ is locally finite with respect to energy.

The Novikov coefficient ring is the completed monoid ring of all coefficient functions $B\to R$. Addition is pointwise and multiplication is convolution over the finite antidiagonal $\beta_1+\beta_2=\beta$. This completion preserves distinct curve classes of equal energy. The finite-support additive monoid algebra embeds as a subring and remains useful for finite regression examples, but it is not the final coefficient type.

## 2. Novikov-valued CohFT

Define

$$
\Omega_{g,S}
=
\sum_{\beta\in B}Q^\beta\Omega_{g,S,\beta}.
$$

Coefficientwise separating gluing becomes ordinary CohFT gluing because the coefficient of $Q^\beta$ in a product is

$$
\sum_{\beta_1+\beta_2=\beta}
\Omega_{\beta_1}\Omega_{\beta_2}.
$$

Thus, once all sums are well-defined, the curve-class-resolved axioms produce a CohFT over the Novikov coefficient ring. Proving identities coefficientwise before passing to the completion keeps the summability issues explicit.

## 3. Small quantum product

The three-point genus-zero classes define the small quantum product by

$$
\eta(a*_Q b,c)
=
\sum_{\beta\in B}Q^\beta
\left\langle a,b,c\right\rangle_{0,3,\beta}.
$$

The separating gluing relation for four-point invariants proves associativity. Under the degree-zero normalization,

$$
a*_Q b\equiv a\smile b
\pmod{Q^{\beta\ne0}}.
$$

## 4. Big quantum product and WDVV

Introduce a formal parameter $t\in V$ and the genus-zero primary potential

$$
F_0(t)
=
\sum_{\beta}\sum_{n\ge0}
\frac{Q^\beta}{n!}
\left\langle t,\ldots,t\right\rangle_{0,n,\beta}.
$$

The big quantum product is characterized by

$$
\eta(a*_t b,c)=\partial_a\partial_b\partial_cF_0(t).
$$

The two boundary decompositions of $\overline{\mathcal M}_{0,4}$ give the WDVV equation, which is equivalent to associativity of $*_t$. The divisor equation often rewrites divisor variables as rescalings of the Novikov monomials.

Descendant theory requires a second distinction, between cotangent lines on stable maps and on stable curves. See [M8: descendants and ancestors](M08DescendantsAndAncestors.md).

## 5. Implemented boundary

`NovikovSeries D R` is implemented as the full coefficient function type with finite-antidiagonal convolution. Its semiring, ring, and commutative-ring laws are proved by finite reindexing; monomial multiplication and the injective map from `AddMonoidAlgebra` are part of the public API. A `CurveClassGW` determines each fixed-beta three-point product coefficient and hence a state-valued Novikov coefficient family for ordinary inputs. `QuantumProductFamily` is the abstract small/big product interface and proves associativity from metric invariance and WDVV. A construction of the entire big family from one particular GW theory awaits its concrete insertion-variable potential.
