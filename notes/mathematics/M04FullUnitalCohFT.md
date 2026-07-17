# M4. Full unital CohFT

A cohomological field theory is an all-genus system of multilinear cohomology classes compatible with the boundary geometry of stable curves.

## 1. State space and classes

Let $V$ be a finite free $R$-module with a symmetric perfect pairing $\eta$ and a distinguished vector $\mathbf 1$. A unital CohFT assigns, to every stable pair $(g,S)$, a multilinear map

$$
\Omega_{g,S}:V^{\otimes S}\longrightarrow H_{g,S}.
$$

The word **full** means that the theory includes every stable genus, not only genus zero. The genus-zero theory is a restriction of this all-genus object.

The basic CohFT does not require a grading on $V$. A later **graded CohFT** equips the same state space with a decomposition

$$
V=\bigoplus_{p\geq 0}V^p,
$$

requires the unit to lie in $V^0$, and records the degree compatibility of the pairing. It extends rather than replaces the ungraded CohFT, so all CohFT maps and gluing axioms are inherited unchanged. Curve-class-resolved GW theory then extends the graded CohFT and supplies its curve-class-dependent dimension law.

## 2. Relabelling and gluing

The maps $\Omega_{g,S}$ are natural under bijections of label sets. For separating gluing, pulling back a class to the boundary equals the product of the two component classes with the two new state-space inputs contracted by the copairing $C_\eta$:

$$
\xi^*\Omega_{g_1+g_2,S\sqcup T}
=
\operatorname{Contr}_{C_\eta}
\bigl(\Omega_{g_1,S\sqcup\{*\}}\boxtimes
\Omega_{g_2,T\sqcup\{*\}}\bigr).
$$

For nonseparating gluing,

$$
\iota^*\Omega_{g+1,S}
=
\operatorname{Contr}_{C_\eta}
\bigl(\Omega_{g,S\sqcup\{+,-\}}\bigr).
$$

These equations are the cohomological versions of the TFT sewing identities.

## 3. Unit and normalization

The flat-unit axiom states that insertion of $\mathbf 1$ at a new marking is pullback along the forgetful map:

$$
\Omega_{g,S\sqcup\{*\}}((v_s),\mathbf 1)
=
\pi^*\Omega_{g,S}((v_s)).
$$

At $(g,n)=(0,3)$ the normalization requires

$$
\Omega_{0,3}(a,b,\mathbf 1)=\eta(a,b).
$$

## 4. Underlying Frobenius algebra

Because $\overline{\mathcal M}_{0,3}$ is a point, the three-point class defines a product by

$$
\eta(a*b,c)=\Omega_{0,3}(a,b,c).
$$

Relabelling gives commutativity, the unit axiom makes $\mathbf 1$ the identity, and the boundary relation in $\overline{\mathcal M}_{0,4}$ gives associativity. Invariance of $\eta$ follows directly from the symmetric three-point function. Thus every unital CohFT has an underlying commutative Frobenius algebra.

## 5. Topological part and genus zero

Projecting every class to cohomological degree zero gives a class valued in $H^0_{g,S}$. A `ConnectedDegreeZero` extension coherently identifies this module with $R$ for every stable pair. Under that explicit hypothesis, the projection gives the scalar-valued **topological part** of a CohFT, determined by the underlying Frobenius algebra. For actual stable-curve moduli spaces this extension expresses their usual connectedness property.

Restricting to genus zero yields a genus-zero CohFT. Integrating its primary classes produces a formal potential whose boundary factorization gives WDVV and hence the formal big product. These are derived constructions, not replacements for the full all-genus definition.

Additional intersection-theoretic data are required before inserting tautological classes. See [M5: tautological classes and ancestors](M05TautologicalClassesAndAncestors.md).

## 6. Implementation status

This milestone is complete. The Lean API contains the all-genus CohFT and its genus-zero restriction, extracts the product from the three-point class, and derives commutativity, the unit laws, metric invariance, WDVV, and associativity. Coherent `ConnectedDegreeZero` data define the topological part. For scalar-valued topological CohFTs, the extracted Frobenius theory agrees with the original correlators in every stable genus and arity.
