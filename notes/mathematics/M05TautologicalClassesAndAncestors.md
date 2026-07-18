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

## 3. Decorated boundary strata

Let $\Gamma$ be a connected stable graph of genus $g$ with legs labelled by $S$, and let

$$
\xi_\Gamma:\overline{\mathcal M}_\Gamma=\prod_{v\in V(\Gamma)}\overline{\mathcal M}_{g(v),n(v)}\longrightarrow\overline{\mathcal M}_{g,S}
$$

be its gluing morphism. A decoration is a monomial $\alpha$ in positive-index kappa classes at vertices and psi classes at legs and internal half-edges. The associated decorated boundary stratum is

$$
[\Gamma,\alpha]=(\xi_\Gamma)_*\alpha.
$$

The project follows the `admcycles` convention for this syntax: the definition does not divide by $|\operatorname{Aut}(\Gamma)|$. Its codimension is

$$
|E(\Gamma)|+\sum_{v\in V(\Gamma)}\sum_{a\geq 1}a\,m_{v,a}+\sum_{h\in H(\Gamma)}k_h,
$$

where $m_{v,a}$ is the exponent of $\kappa_a$ and $k_h$ is the psi exponent at a flag. Graph isomorphism may permute vertices and edges and may exchange the two half-edges of each node; it fixes the external labels and transports all decorations. The formal strata module is the free $\mathbb Q$-vector space on these isomorphism classes. It is not itself the tautological ring: the product requires the common-refinement and excess-intersection formula, and the quotient requires proved tautological relations.

For a self-intersection along a node with branches $h$ and $h'$, the normal line is $L_h^\vee\otimes L_{h'}^\vee$, so its first Chern class is

$$
-\psi_h-\psi_{h'}.
$$

This excess factor is one of the terms that a correct common-refinement product must insert. The current Lean layer records a proof-carrying product contract but does not yet enumerate common refinements.

On $\overline{\mathcal M}_{1,4}$, Getzler's symmetric codimension-two relation is

$$
12\delta_{2,2}-4\delta_{2,3}-2\delta_{2,4}+6\delta_{3,4}+\delta_{0,3}+\delta_{0,4}-2\delta_\beta=0.
$$

Getzler's named cycles use an orbifold-cycle normalization, while the formal decorated strata above use raw gluing pushforwards. Therefore a Lean encoding of the seven names must provide its normalization explicitly; simply identifying each name with an unweighted graph would conflate two conventions.

## 4. Required operations

To use these classes one needs cup products, pullbacks, proper pushforwards, external products, and integration

$$
\int_{\overline{\mathcal M}_{g,S}}:H^{\mathrm{top}}_{g,S}\longrightarrow R.
$$

They must satisfy functoriality, base-change identities where appropriate, and the projection formula

$$
f_*(f^*\alpha\smile\beta)=\alpha\smile f_*\beta.
$$

The geometric tautological system satisfies these identities. The implemented abstract interface retains only the particular pushforward, degree, naturality, and projection laws used by current theorems; it does not claim a complete six-functor formalism.

## 5. Ancestor correlators

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

## 6. Implemented boundary

The Lean ancestor layer contains marked `psi`-classes with relabelling and primitive gluing pullbacks, top-degree integration, and forgetful pushforward with relabelling naturality, its degree shift, degree-zero vanishing, and the projection formula. It also contains rational-tail correction data, kappa classes with derived degree and relabelling laws, and numerical ancestor correlators. The separate tautological-strata layer contains finite decorated stable graphs modulo isomorphism, codimension, one-vertex strata, the free rational strata module, dimension relations, arbitrary supplied relation quotients, a certified product contract, and degree-preserving realization maps that factor through relations proved to lie in the kernel. It records the exact named Getzler coefficient vector and the standard genus-zero psi values $1$, $1$, and $2$ for the first three test cases. General pushforward composition and base-change laws, Hodge classes, a native all-genus product enumeration, an explicit normalized Getzler graph encoding, geometric relation proofs, and a concrete cohomology ring remain unimplemented. The constant stable-curve target validates the older abstract ancestor operations but is not a geometric realization of the new strata quotient.
