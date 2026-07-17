# M5. Tautological classes and ancestors

A bare CohFT supplies cohomology classes but does not by itself supply integration, pushforwards, or distinguished tautological classes. This phase adds the intersection-theoretic operations needed for numerical correlators and ancestor insertions.

## 1. Cotangent-line classes

For each marking $i$, let $L_i$ be the cotangent line to the universal stable curve at that marking. Its first Chern class is

$$
\psi_i=c_1(L_i)\in H^2(\overline{\mathcal M}_{g,S}).
$$

These are stable-curve classes. They will later be distinguished from the cotangent-line classes on moduli spaces of stable maps.

The forgetful map satisfies a correction formula of the form

$$
\psi_i=\pi^*\psi_i+D_{i,*},
$$

where $D_{i,*}$ is the boundary divisor on which the markings $i$ and $*$ lie on a rational tail. This boundary term is the source of topological recursion relations.

## 2. Other tautological classes

The kappa classes may be defined by pushforward:

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

An abstract tautological stable-curve system records these operations without initially constructing the actual moduli stacks.

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

The bar emphasizes that these are ancestor insertions. Forgetful-map and boundary formulas lead to the string equation, dilaton equation, and topological recursion relations, once the corresponding unstable conventions are fixed.

The next stage enriches the theory by effective curve classes and the additional axioms special to Gromov--Witten theory. See [M6: curve-class-resolved GW axioms](M06CurveClassResolvedGW.md).

## 5. Implementation readiness

M3 and M4 now supply the prerequisites for this phase: internally graded
stable-curve targets, degree-preserving relabelling and primitive pullbacks,
their immediate coherence laws, and full CohFT classes. The first M5
implementation should therefore add only the tautological data used by an
initial theorem: marked `psi`-classes and their relabelling/pullback behavior,
followed by integration and pushforward once a concrete ancestor construction
needs them. Stable graphs, kappa classes, and Hodge classes should be added in
the tranche that first consumes them rather than as unused fields.
