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

The monoid algebra permits only finite support, which is often too small for GW theory. A Novikov ring allows infinite support subject to a local-finiteness condition measured by an energy or degree function $E:B\to\mathbb R_{\ge0}$. A typical condition says that only finitely many nonzero terms have energy at most any fixed bound.

The exact completion should be kept abstract until the effective monoid and finiteness theorem needed by the intended examples are fixed.

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
