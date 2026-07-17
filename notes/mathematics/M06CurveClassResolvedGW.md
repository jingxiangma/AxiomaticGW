# M6. Curve-class-resolved Gromov--Witten axioms

Gromov--Witten theory refines a CohFT by remembering the homology class of the curve in the target and by imposing grading, divisor, and normalization properties that are not part of the abstract CohFT axioms.

## 1. Effective curve classes

Let $B$ be a commutative monoid of effective curve classes. For a smooth projective target one has in mind the effective part of $H_2(X,\mathbb Z)$, but the axiomatic theory can begin with an abstract monoid.

The primary GW classes are multilinear maps

$$
\Omega_{g,S,\beta}:V^{\otimes S}
\longrightarrow H_{g,S},
\qquad
\beta\in B.
$$

Indexing directly by effective classes makes effectivity structural. If one instead indexes by a whole group, a separate axiom must say that non-effective classes contribute zero.

## 2. Curve-class-resolved gluing

At a separating node, the total class splits between the two components:

$$
\xi^*\Omega_{g_1+g_2,S\sqcup T,\beta}
=
\sum_{\beta_1+\beta_2=\beta}
\operatorname{Contr}_{C_\eta}
\bigl(
\Omega_{g_1,S\sqcup\{*\},\beta_1}
\boxtimes
\Omega_{g_2,T\sqcup\{*\},\beta_2}
\bigr).
$$

At a nonseparating node, normalization does not split the curve into two components, so the class remains $\beta$:

$$
\iota^*\Omega_{g+1,S,\beta}
=
\operatorname{Contr}_{C_\eta}
\bigl(\Omega_{g,S\sqcup\{+,-\},\beta}\bigr).
$$

Relabelling and the flat-unit axiom are imposed coefficientwise in $\beta$.

## 3. Grading and virtual dimension

The state space and stable-curve cohomology are graded. Abstractly, a
`GradedCohFT` extends the bare CohFT by recording this state-space grading, the
homogeneous unit, and degree compatibility of the pairing. The
curve-class-resolved GW theory extends that graded CohFT and adds the
$\beta$-dependent degree constraint below.

For a target $X$ of complex dimension $d$, the expected complex dimension of the stable-map space is

$$
\operatorname{vdim}_{\mathbb C}
\overline{\mathcal M}_{g,S}(X,\beta)
=
(1-g)(d-3)+|S|+\int_\beta c_1(TX).
$$

The degree assigned to $\Omega_{g,S,\beta}$ must agree with this dimension after accounting for the degrees of the insertions and for pushforward along stabilization. An abstract theory therefore records the grading and the homomorphism $\beta\mapsto\int_\beta c_1(TX)$.

## 4. Divisors and degree zero

For a divisor class $D\in V^1$ in codimension grading, the primary divisor axiom has the stable form

$$
\pi_*\Omega_{g,S\sqcup\{*\},\beta}((v_s),D)
=
\left(\int_\beta D\right)
\Omega_{g,S,\beta}((v_s)),
$$

where $\pi$ forgets the divisor marking, with unstable and degree-zero exceptional cases handled explicitly. This pushforward formula should be kept distinct from the flat-unit axiom, which uses pullback along $\pi$. The pairing $\langle D,\beta\rangle=\int_\beta D$ is extra GW data and cannot be recovered from a bare CohFT.

Degree-zero normalization connects the theory to classical intersection theory. In genus zero it ensures that the coefficient of the zero curve class recovers the classical cup product. Higher-genus degree-zero terms can involve obstruction and Hodge data, so they should not be confused with the cohomological degree-zero, or topological, part of a CohFT.

## 5. Axiomatic core

The first GW structure should separate a curve-class-resolved CohFT core from optional target-dependent properties such as deformation invariance or mapping-to-a-point formulas. This keeps the algebraic gluing theory reusable while allowing stronger packages to extend it.

The coefficientwise theory becomes an ordinary CohFT only after summation over $\beta$. See [M7: Novikov coefficients and quantum products](M07NovikovAndQuantumProducts.md).
