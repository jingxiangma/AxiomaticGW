# M5. Tautological classes and ancestors

A bare CohFT supplies cohomology classes but does not by itself supply integration, pushforwards, or distinguished tautological classes. This phase adds the intersection-theoretic operations needed for numerical correlators and ancestor insertions.

## 1. Cotangent-line classes

For each marking $i$, let $L_i$ be the cotangent line to the universal stable curve at that marking. Its first Chern class is

$$
\psi_i=c_1(L_i)\in H^2(\overline{\mathcal M}_{g,S}).
$$

These are stable-curve classes. The descendant layer distinguishes them from the cotangent-line classes on moduli spaces of stable maps.

Let $\pi:\overline{\mathcal M}_{g,S\sqcup\{*\}}\to\overline{\mathcal M}_{g,S}$ forget the marking $*$. Distinguishing the cotangent classes on the source and target, the correction formula is

$$
\psi_i^{S\sqcup\{*\}}
=\pi^*\psi_i^S+D_{i,*},
$$

where $D_{i,*}$ is the boundary divisor whose generic curve has $i$ and $*$ on a three-pointed rational component. The superscripts prevent the common ambiguity of writing the two different cotangent classes with the same symbol.

## 2. Other tautological classes

With the convention used in this project, the kappa classes are defined by

$$
\kappa_m=\pi_*(\psi_*^{m+1}).
$$

The Hodge bundle $\mathbb E$ has fiber $H^0(C,\omega_C)$, and its Chern classes are

$$
\lambda_j=c_j(\mathbb E).
$$

Boundary strata, psi classes, kappa classes, and lambda classes generate the standard tautological system used in curve intersection theory.

## 3. Required operations

To use these classes one needs cup products, pullbacks, proper pushforwards, external products, and integration

$$
\int_{\overline{\mathcal M}_{g,S}}:H^{\mathrm{top}}_{g,S}\longrightarrow R.
$$

They must satisfy functoriality, base-change identities where appropriate, and the projection formula

$$
f_*(f^*\alpha\smile\beta)=\alpha\smile f_*\beta.
$$

The geometric tautological system satisfies these identities. The implemented abstract interface retains only the particular pushforward, degree, naturality, and projection laws used by current theorems; it does not claim a complete six-functor formalism.

## 4. Ancestor correlators

For a CohFT $\Omega$, ancestor correlators are defined using stable-curve psi classes:

$$
\left\langle
\prod_{i\in S}\bar\tau_{k_i}(v_i)
\right\rangle_g
=
\int_{\overline{\mathcal M}_{g,S}}
\Omega_{g,S}((v_i))
\prod_{i\in S}\psi_i^{k_i}.
$$

The bar on $\bar\tau$ distinguishes these stable-curve cotangent insertions from stable-map descendants. String, dilaton, and topological recursion equations additionally require the relevant push-pull identities and unstable conventions; they do not follow from the displayed integral alone.

The next stage enriches the theory by effective curve classes and the additional axioms special to Gromov--Witten theory. See [M6: curve-class-resolved GW axioms](M06CurveClassResolvedGW.md).

## 5. Implemented boundary

The Lean ancestor layer now contains marked `psi`-classes with relabelling and primitive gluing pullbacks, top-degree integration, and forgetful pushforward with relabelling naturality, its degree shift, degree-zero vanishing, and the projection formula. It also contains rational-tail correction data, kappa classes with derived degree and relabelling laws, and numerical ancestor correlators. General pushforward composition and base-change laws are not encoded. The constant stable-curve target validates the implemented operations. Hodge classes and general decorated boundary strata are still omitted because no implemented theorem consumes them; they belong in the extension that first needs them.
