# Frobenius algebras, 2D topological field theory, and CohFTs

These notes record the mathematical conventions behind the first
formalization milestone.  They also separate two related statements:

1. commutative Frobenius algebras are equivalent to oriented two-dimensional
   topological field theories;
2. a commutative Frobenius algebra determines a topological, degree-zero
   CohFT, while a general CohFT contains strictly more information.

The abbreviation **2D TFT** is standard.  The phrase "2D CohFT" is less
standard: a CohFT is already indexed by moduli spaces of curves of every
genus.  When the CohFT takes values only in cohomological degree zero, we call
it a **topological CohFT**.

## 1. Algebraic setting

Let $R$ be a commutative ring and let $A$ be a commutative, associative,
unital $R$-algebra. For the constructions involving duals and tensor
products, we assume that $A$ is finite free over $R$. More generally, finite
projective modules are the natural setting, but finite free modules have a
better-supported initial Lean API.

Write

$$
A^\vee=\operatorname{Hom}_R(A,R).
$$

A **commutative Frobenius algebra** is $A$ together with an $R$-linear map

$$
\epsilon:A\longrightarrow R
$$

such that the trace pairing

$$
\eta(a,b)=\epsilon(ab)
$$

is perfect.

The map $\epsilon$ is variously called the Frobenius functional, trace, or
counit.  We use **counit**, anticipating the associated coalgebra structure.

## 2. Perfectness

The pairing induces a linear map

$$
\eta^\sharp:A\longrightarrow A^\vee,
\qquad
\eta^\sharp(a)(b)=\eta(a,b).
$$

Perfectness means that this map is an isomorphism.  In the symmetric setting,
the map induced from the other argument is then the same up to the canonical
flip.  Mathlib's `LinearMap.IsPerfPair` records bijectivity in both arguments.

Over a field, for a finite-dimensional vector space, perfectness is equivalent
to ordinary nondegeneracy:

$$
\eta(a,b)=0\ \text{for every }b \quad\Longrightarrow\quad a=0.
$$

Over a general commutative ring, injectivity is not sufficient.  The gluing
formulas used later require an actual inverse to $\eta^\sharp$, so perfectness is
the correct integral notion.

## 3. Symmetry and Frobenius invariance

For a commutative algebra, symmetry is automatic:

$$
\eta(a,b)=\epsilon(ab)=\epsilon(ba)=\eta(b,a).
$$

The pairing is also invariant under multiplication:

$$
\eta(ab,c)
=\epsilon(abc)
=\eta(a,bc).
$$

Equivalently, multiplication by any element is self-adjoint with respect to
$\eta$:

$$
\eta(ab,c)=\eta(b,ac).
$$

One can instead begin with a perfect invariant bilinear form $\eta$ and recover
the counit by

$$
\epsilon(a)=\eta(a,1).
$$

Indeed, invariance and the unit give

$$
\epsilon(ab)=\eta(ab,1)=\eta(a,b).
$$

Thus the counit formulation and the invariant-pairing formulation are
equivalent.

## 4. The copairing or Casimir tensor

Perfectness gives a canonical isomorphism

$$
A\otimes_R A
\xrightarrow{\ \eta^\sharp\otimes\mathrm{id}\ }
A^\vee\otimes_R A
\xrightarrow{\sim}
\operatorname{End}_R(A).
$$

The **copairing**, **inverse metric**, or **Casimir tensor** is the inverse image
of the identity endomorphism:

$$
C_\eta\in A\otimes_R A,
\qquad
C_\eta=(A\otimes A\simeq\operatorname{End}(A))^{-1}(\mathrm{id}_A).
$$

This is a basis-free definition.  If a basis calculation writes

$$
C_\eta=\sum_i u_i\otimes v_i,
$$

then its defining contraction identity is

$$
\sum_i\eta(u_i,x)v_i=x.
$$

Symmetry of the pairing implies symmetry of the copairing:

$$
\tau(C_\eta)=C_\eta,
\qquad
\tau(a\otimes b)=b\otimes a.
$$

This identity will later ensure that contracting an internal edge does not
depend on an ordering of its two half-edges.

## 5. Comultiplication and the handle element

The Frobenius pairing makes multiplication and comultiplication adjoint.  The
comultiplication may be written using the Casimir tensor as

$$
\Delta(a)=(a\otimes 1)C_\eta=(1\otimes a)C_\eta.
$$

It satisfies the counit identities

$$
(\epsilon\otimes\mathrm{id})\Delta=\mathrm{id},
\qquad
(\mathrm{id}\otimes\epsilon)\Delta=\mathrm{id},
$$

and is coassociative.  In the commutative case it is cocommutative.  The
Frobenius relation can be expressed as

$$
\Delta(ab)
=(a\otimes1)\Delta(b)
=\Delta(a)(1\otimes b).
$$

The **handle element**, also called the Euler element, is

$$
E=\mu(C_\eta)=\sum_i u_iv_i.
$$

Adding one handle to a surface corresponds algebraically to multiplication by
$E$.

## 6. Examples

### The base ring

Take $A=R$ and $\epsilon=\mathrm{id}$. Then

$$
\eta(a,b)=ab,
\qquad
C_\eta=1\otimes1,
\qquad
E=1.
$$

This is the first compiled example in the project.

### A product of fields

For $A=K\times K$, define

$$
\epsilon(a,b)=a+b.
$$

With idempotents $e_1=(1,0)$ and $e_2=(0,1)$, the pairing is diagonal:

$$
\eta(e_i,e_j)=\delta_{ij}.
$$

Consequently,

$$
C_\eta=e_1\otimes e_1+e_2\otimes e_2,
\qquad
E=e_1+e_2=1.
$$

### Dual numbers

Let

$$
A=K[x]/(x^2)
$$

and let $\epsilon$ extract the coefficient of $x$. In the basis $(1,x)$,

$$
[\eta]=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix},
\qquad
C_\eta=1\otimes x+x\otimes1,
\qquad
E=2x.
$$

This is a useful nonsemisimple test example.

## 7. Equivalence with oriented 2D TFTs

An oriented two-dimensional TFT is a symmetric monoidal functor

$$
Z:\operatorname{Bord}^{\mathrm{or}}_2
\longrightarrow R\text{-}\operatorname{Mod},
$$

where objects are closed oriented one-manifolds and morphisms are oriented
two-dimensional bordisms.

The value of the TFT on the positively oriented circle is the state space

$$
A=Z(S^1).
$$

Basic bordisms give the Frobenius operations:

| Bordism | Algebraic operation |
| --- | --- |
| pair of pants, two inputs and one output | multiplication $\mu:A\otimes A\to A$ |
| disk as an outgoing bordism | unit $R\to A$ |
| disk as an incoming bordism | counit $\epsilon:A\to R$ |
| reversed pair of pants | comultiplication $\Delta:A\to A\otimes A$ |
| cylinder | identity of $A$ |

The relations between decompositions of surfaces give associativity,
commutativity, the unit and counit identities, and the Frobenius relation.
Conversely, these algebraic identities imply that the value assigned using a
pair-of-pants decomposition is independent of the chosen decomposition.

This yields the classification theorem:

$$
\boxed{
\text{oriented 2D TFTs over }R
\simeq
\text{commutative Frobenius }R\text{-algebras}.
}
$$

At the level of correlators, a connected genus-$g$ surface with $n$ incoming
circles defines

$$
\omega_{g,n}(a_1,\ldots,a_n)
=
\epsilon\!\left(a_1\cdots a_nE^g\right).
$$

For a closed connected genus-$g$ surface, its partition function is

$$
Z(\Sigma_g)=\epsilon(E^g).
$$

## 8. Relationship with CohFTs

A unital CohFT consists of a state space $(V,\eta,\mathbf 1)$ and, for every stable
pair

$$
2g-2+n>0,
$$

classes or multilinear maps

$$
\Omega_{g,n}:V^{\otimes n}
\longrightarrow
H^\bullet(\overline{\mathcal M}_{g,n};R).
$$

These maps satisfy symmetric-group equivariance, separating and
nonseparating gluing, and the flat-unit axiom.  At every node, the two new
marked points are contracted using the inverse metric $C_\eta$.

Because

$$
\overline{\mathcal M}_{0,3}\cong\mathrm{pt},
$$

the three-point class defines a product by

$$
\eta(a*b,c)=\Omega_{0,3}(a,b,c).
$$

The CohFT axioms imply that this product is commutative, unital, and invariant.
Associativity follows from the two boundary decompositions of
$\overline{\mathcal M}_{0,4}$. Thus every unital CohFT has an underlying commutative Frobenius
algebra.

Conversely, a commutative Frobenius algebra defines a topological CohFT by

$$
\Omega_{g,n}(a_1,\ldots,a_n)
=
\epsilon(a_1\cdots a_nE^g)\,1
\in H^0(\overline{\mathcal M}_{g,n};R).
$$

This is the CohFT version of the associated 2D TFT.  However, a general CohFT
can have positive-cohomological-degree classes, and these are not determined
by the Frobenius algebra.  The precise relationship is therefore

$$
\boxed{
\text{Frobenius algebra}
\simeq
\text{oriented 2D TFT}
\simeq
\text{topological CohFT},
}
$$

while

$$
\boxed{
\text{general CohFT}
\Longrightarrow
\text{underlying Frobenius algebra}
}
$$

is not reversible without discarding the higher-degree information.

For Gromov--Witten theory there is one further distinction.  The individual
curve-class terms $\Omega_{g,n,\beta}$ form a curve-class-resolved theory. Only
after summing them with Novikov weights does one obtain an ordinary
Novikov-valued CohFT. Descendants require additional $\psi$-class and
integration data and are not part of the minimal Frobenius or CohFT
definitions.

## 9. Current formalization status

The mathematical discussion above is broader than the Lean development that
currently exists. This section records the exact boundary. A declaration is
listed as formalized only when it is present in the repository, compiles, and
contains no `sorry`.

### 9.1 Formalized now

| Mathematical content | Lean declaration | Status |
| --- | --- | --- |
| bundled symmetric perfect pairing | `AxiomaticGW.SymmetricPerfectPairing` | defined |
| metric map $\eta^\sharp:V\simeq V^\vee$ | `SymmetricPerfectPairing.toDual` | defined |
| evaluation formula for $\eta^\sharp$ | `SymmetricPerfectPairing.toDual_apply` | proved |
| canonical equivalence $V\otimes V\simeq\operatorname{End}(V)$ | `SymmetricPerfectPairing.tensorEndEquiv` | defined |
| pure-tensor contraction formula | `SymmetricPerfectPairing.tensorEndEquiv_tmul` | proved |
| basis-free copairing $C_\eta$ | `SymmetricPerfectPairing.copairing` | defined |
| $C_\eta$ contracts to the identity | `SymmetricPerfectPairing.tensorEndEquiv_copairing` | proved |
| pointwise contraction identity | `SymmetricPerfectPairing.copairing_contract` | proved |
| trace pairing $\eta(a,b)=\epsilon(ab)$ | `AxiomaticGW.tracePairing` | defined and evaluated |
| commutative Frobenius algebra via a counit and perfect trace pairing | `AxiomaticGW.CommFrobeniusAlgebra` | defined |
| equality determined by the counit | `CommFrobeniusAlgebra.ext` | proved |
| derived symmetric perfect pairing | `CommFrobeniusAlgebra.pairing` | defined |
| symmetry and Frobenius invariance of the trace pairing | `pairing_isSymm`, `pairing_assoc` | proved |
| construction from an invariant perfect pairing | `CommFrobeniusAlgebra.ofInvariantPairing` | defined |
| recovery of the supplied invariant pairing | `pairing_ofInvariantPairing` | proved |
| Casimir tensor of a Frobenius algebra | `CommFrobeniusAlgebra.casimir` | defined |
| contraction characterization of the Casimir tensor | `tensorEndEquiv_casimir` | proved |
| handle element $E=\mu(C_\eta)$ | `CommFrobeniusAlgebra.handleElement` | defined |
| base-ring example $A=R$ | `CommFrobeniusAlgebra.baseRing` | constructed |
| $C_\eta=1\otimes1$ and $E=1$ for the base ring | `baseRing_casimir`, `baseRing_handleElement` | proved |

The current implementation works over a commutative ring, with a commutative
algebra. Finite-free hypotheses are introduced only for the tensor--endomorphism
equivalence, copairing, Casimir tensor, and handle element.

### 9.2 Discussed here but not yet formalized

The following statements and constructions appear in these notes as
mathematical motivation, but they do **not** yet have completed Lean proofs in
this repository:

- symmetry of the copairing,
  $\tau(C_\eta)=C_\eta$;
- the comultiplication
  $\Delta(a)=(a\otimes1)C_\eta$;
- coassociativity, cocommutativity, and the two counit identities;
- the Frobenius relation between multiplication and comultiplication;
- interoperability with mathlib's `Coalgebra` structure;
- the product-algebra and dual-number examples;
- morphisms, isomorphisms, transport, tensor products, and base change of
  Frobenius algebras;
- finite-projective modules without a chosen finite-free instance;
- graded, super, or noncommutative Frobenius algebras;
- the oriented bordism category and the classification of oriented 2D TFTs;
- a bundled 2D TFT or topological CohFT;
- the correlator formula
  $\omega_{g,n}(a_1,\ldots,a_n)=\epsilon(a_1\cdots a_nE^g)$ and its gluing
  proofs;
- the extraction of a Frobenius algebra from an all-genus CohFT;
- moduli-of-curves interfaces, stable graphs, general CohFTs, descendants,
  Novikov coefficients, or axiomatic Gromov--Witten theory.

### 9.3 Next formalization boundary

The next algebraic milestone is

$$
\text{copairing symmetry}
\longrightarrow
\text{comultiplication}
\longrightarrow
\text{coalgebra laws}
\longrightarrow
\text{Frobenius relation}.
$$

Only after that layer is stable will the project define the associated
topological field theory and prove the genus-$g$ correlator gluing identities.
