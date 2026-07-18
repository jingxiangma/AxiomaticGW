# M4. Full unital CohFT

A cohomological field theory is an all-genus system of multilinear cohomology classes compatible with the boundary geometry of stable curves.

## 1. State space and classes

Let $V$ be a finite free $R$-module with a symmetric perfect pairing $\eta$ and a distinguished vector $\mathbf 1$. A unital CohFT assigns, to every stable pair $(g,S)$, a multilinear map

$$
\Omega_{g,S}:V^{\otimes S}\longrightarrow H_{g,S}.
$$

The word **full** means that the theory includes every stable genus, not only genus zero. The genus-zero theory is a restriction of this all-genus object.

The basic CohFT does not require a grading on $V$. The **graded CohFT** extension equips the same state space with a decomposition

$$
V=\bigoplus_{p\geq 0}V^p,
$$

requires the unit to lie in $V^0$, and records the degree compatibility of the pairing. It extends rather than replaces the ungraded CohFT, so all CohFT maps and gluing axioms are inherited unchanged. Curve-class-resolved GW theory then extends the graded CohFT and supplies its curve-class-dependent dimension law.

## 2. Relabelling and gluing

The maps $\Omega_{g,S}$ are natural under bijections of label sets. Choose a basis $(e_a)$ of $V$, write $\eta_{ab}=\eta(e_a,e_b)$, and let $(\eta^{ab})$ be the inverse matrix. For input families $x:S\to V$ and $y:T\to V$, the separating gluing axiom is

$$
\xi^*\Omega_{g_1+g_2,S\sqcup T}(x,y)
=
\sum_{a,b}\eta^{ab}
\Omega_{g_1,S\sqcup\{*\}}(x,e_a)
\boxtimes
\Omega_{g_2,T\sqcup\{*\}}(y,e_b).
$$

For nonseparating gluing, the corresponding formula is

$$
\iota^*\Omega_{g+1,S}(x)
=
\sum_{a,b}\eta^{ab}
\Omega_{g,S\sqcup\{+,-\}}(x,e_a,e_b).
$$

These expressions are independent of the chosen basis because $\sum_{a,b}\eta^{ab}e_a\otimes e_b=C_\eta$. They are the cohomological analogues of the two TFT contraction formulas in M2.

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

After identifying $H^0(\overline{\mathcal M}_{0,3};R)$ with $R$, the three-point class defines a product by

$$
\eta(a*b,c)=\Omega_{0,3}(a,b,c).
$$

If $\omega(a,b,c)$ denotes this scalar three-point function, equality of the $12|34$ and $13|24$ boundary divisor classes in $H^2(\overline{\mathcal M}_{0,4})$ gives

$$
\sum_{a,b}\omega(x,y,e_a)\eta^{ab}\omega(e_b,z,w)
=
\sum_{a,b}\omega(x,z,e_a)\eta^{ab}\omega(e_b,y,w).
$$

This is WDVV. Nondegeneracy of $\eta$ identifies it with $(x*y)*z=x*(y*z)$. Relabelling gives commutativity, the unit axiom makes $\mathbf 1$ the identity, and symmetry of $\omega$ gives Frobenius invariance.

## 5. Topological part and genus zero

Projecting every class to cohomological degree zero gives a class valued in $H^0_{g,S}$. A `ConnectedDegreeZero` extension coherently identifies this module with $R$ for every stable pair. Under that explicit hypothesis, the projection gives the scalar-valued **topological part** of a CohFT, determined by the underlying Frobenius algebra. For actual stable-curve moduli spaces this extension expresses their usual connectedness property.

Restricting to genus zero yields a genus-zero CohFT and its ordinary Frobenius product. The curve-class-resolved GW layer later constructs a big quantum product from integrated primary invariants; commutativity and reduction at zero background are derived from the primitive axioms, while associativity at arbitrary background uses the optional higher boundary relation. These are derived constructions, not replacements for the full all-genus definition.

Additional intersection-theoretic data are required before inserting tautological classes. See [M5: tautological classes and ancestors](M05TautologicalClassesAndAncestors.md).

## 6. Implementation status

This milestone is complete. The Lean API contains the all-genus CohFT and its genus-zero restriction, extracts the product from the three-point class, and derives commutativity, the unit laws, metric invariance, WDVV, and associativity. Coherent `ConnectedDegreeZero` data define the topological part. For scalar-valued topological CohFTs, the extracted Frobenius theory agrees with the original correlators in every stable genus and arity.
