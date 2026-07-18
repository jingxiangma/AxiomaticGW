# The point target and stable-curve intersection theory

The Gromov--Witten theory of a point is the cleanest universal test of the axiomatic framework. It contains no target geometry, no nonzero curve classes, and no evaluation classes. What remains is precisely the intersection theory of the moduli spaces of stable curves.

## 1. Stable maps to a point

Every map to a point is constant, so the only curve class is zero. For every stable pair $(g,S)$ there is a canonical identification

$$
\overline{\mathcal M}_{g,S}(\mathrm{pt},0)
\cong
\overline{\mathcal M}_{g,S}.
$$

The point state space is the coefficient ring $R$, its unit is $1$, and its pairing is ordinary multiplication:

$$
\eta(x,y)=xy.
$$

For inputs $(a_s)_{s\in S}$, the primary class is the constant degree-zero class

$$
\Omega^{\mathrm{pt}}_{g,S,0}(a)
=
\left(\prod_{s\in S}a_s\right)1
\in
H^0(\overline{\mathcal M}_{g,S};R).
$$

Thus all nontrivial information in the point theory comes from the geometry of $\overline{\mathcal M}_{g,S}$ itself.

## 2. Descendants are psi-class intersections

Because stabilization is the identity for stable maps to a point, stable-map cotangent lines and stable-curve cotangent lines agree. Point descendants and ancestors therefore coincide. With powers $d:S\to\mathbb N$, the invariant is the psi-class intersection number

$$
\left\langle\prod_{s\in S}\tau_{d_s}\right\rangle_g
=
\int_{\overline{\mathcal M}_{g,S}}
\prod_{s\in S}\psi_s^{d_s}.
$$

The psi monomial has codimension $\sum_s d_s$, while the complex dimension of the moduli space is $3g-3+|S|$. Consequently

$$
\left\langle\prod_{s\in S}\tau_{d_s}\right\rangle_g=0
\qquad\text{unless}\qquad
\sum_{s\in S}d_s=3g-3+|S|.
$$

Relabelling the markings does not change the number. These two facts are derived in Lean from `PsiClasses.monomial_degree`, top-degree integration, and naturality under label equivalences.

## 3. Genus-zero WDVV

The primary point product is ordinary multiplication in $R$. The two boundary restrictions of the unit class on $\overline{\mathcal M}_{0,4}$ are both the unit in the tensor-product target, so point-target WDVV reduces to associativity of multiplication:

$$
(xy)z=x(yz).
$$

Although this equation is algebraically trivial for a point, it is an important interface test: the same `GenusZeroGeometry` boundary comparison used for general CohFTs accepts the universal unit class.

## 4. DVV recursion

The point theory also isolates the Virasoro constraints for psi-class intersections. Set

$$
D_m=(2m+1)!!,
\qquad
D_{-1}=1.
$$

Let $S$ be a stable nondistinguished arity, let $d:S\to\mathbb N$, and distinguish one additional insertion $\tau_{k+1}$. The DVV recursion is

$$
\begin{aligned}
D_{k+1}
\left\langle\tau_{k+1}\prod_{s\in S}\tau_{d_s}\right\rangle_g
={}&
\sum_{s\in S}
\frac{D_{k+d_s}}{D_{d_s-1}}
\left\langle\tau_{d_s+k}\prod_{t\ne s}\tau_{d_t}\right\rangle_g
\\
&+\frac12
\sum_{a+b=k-1}D_aD_b
\Bigg(
\left\langle\tau_a\tau_b\prod_{s\in S}\tau_{d_s}\right\rangle_{g-1}
\\
&\hspace{7em}+
\sum_{\substack{g_1+g_2=g\\I\sqcup J=S}}
\left\langle\tau_a\prod_{i\in I}\tau_{d_i}\right\rangle_{g_1}
\left\langle\tau_b\prod_{j\in J}\tau_{d_j}\right\rangle_{g_2}
\Bigg).
\end{aligned}
$$

The genus-reduction term is omitted when $g=0$, and the sum over $a+b=k-1$ is empty when $k=0$. Unstable component correlators are interpreted as zero. The recursion is used together with the initial values

$$
\langle\tau_0^3\rangle_0=1,
\qquad
\langle\tau_1\rangle_1=\frac1{24}.
$$

This coefficient recursion is the DVV form of the Virasoro constraints for the Witten--Kontsevich generating function. It is not a consequence of the primitive pullback rules in `PsiClasses`; a geometric stable-curve model must prove it from stronger tautological input or supply it as an explicit hypothesis.

## 5. Lean boundary

[`PointTarget/Descendants.lean`](../../AxiomaticGW/PointTarget/Descendants.lean) implements `PointTarget.primaryClass`, `intersectionNumber`, the point ancestor map, relabelling and dimension-vanishing theorems, the two initial-value interfaces, and the unit-class WDVV check. `PointTarget.DVVRecursion` states the full labelled all-genus formula above using finite subsets for the splitting sum.

The module does not currently construct a `StableMapDescendants` instance for the point, so the geometric equality of point descendants and ancestors is mathematical context rather than an implemented identification theorem.

The module deliberately does not manufacture a concrete cohomology ring for $\overline{\mathcal M}_{g,S}$. A future geometric stable-curve model should instantiate `StableCurveCohomology`, `PsiClasses`, and `StableCurveIntegration`, prove the initial intersections and `DVVRecursion`, and then obtain the numerical point theory from these existing definitions.
