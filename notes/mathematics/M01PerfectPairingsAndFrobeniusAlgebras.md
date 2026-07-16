# M1. Perfect pairings and Frobenius algebras

This note describes the algebraic data that later appear at every node of a topological field theory, a CohFT, or Gromov--Witten theory.

## 1. Algebraic setting

Let $R$ be a commutative ring and let $A$ be a commutative, associative, unital $R$-algebra. We assume initially that $A$ is finite free as an $R$-module. Finite projective modules are the more intrinsic setting, but finite freeness gives a convenient first formalization interface.

Write

$$
A^\vee=\operatorname{Hom}_R(A,R).
$$

A bilinear pairing $\eta:A\otimes_R A\to R$ is **perfect** if the induced map

$$
\eta^\sharp:A\longrightarrow A^\vee,
\qquad
\eta^\sharp(a)(b)=\eta(a,b),
$$

is an isomorphism. Over a field this is equivalent to nondegeneracy for a finite-dimensional vector space. Over a general ring, injectivity alone is not sufficient: contraction formulas require an actual inverse to $\eta^\sharp$.

## 2. Commutative Frobenius algebras

A **commutative Frobenius $R$-algebra** is a commutative unital $R$-algebra $A$ together with an $R$-linear counit

$$
\epsilon:A\longrightarrow R
$$

such that the trace pairing

$$
\eta(a,b)=\epsilon(ab)
$$

is perfect. The words *Frobenius functional*, *trace*, and *counit* are all used for $\epsilon$.

Commutativity implies symmetry:

$$
\eta(a,b)=\epsilon(ab)=\epsilon(ba)=\eta(b,a).
$$

Associativity implies Frobenius invariance:

$$
\eta(ab,c)=\epsilon(abc)=\eta(a,bc).
$$

Conversely, one may begin with a symmetric perfect invariant pairing and define $\epsilon(a)=\eta(a,1)$. Invariance then gives $\epsilon(ab)=\eta(a,b)$, so the counit and invariant-pairing definitions are equivalent.

## 3. Copairing and contraction

Perfectness gives a canonical equivalence

$$
A\otimes_R A
\xrightarrow{\ \eta^\sharp\otimes\mathrm{id}\ }
A^\vee\otimes_R A
\xrightarrow{\sim}
\operatorname{End}_R(A).
$$

The **copairing**, **inverse metric**, or **Casimir tensor** is the inverse image of the identity endomorphism:

$$
C_\eta\in A\otimes_R A.
$$

If a basis calculation writes $C_\eta=\sum_i u_i\otimes v_i$, its defining identity is

$$
\sum_i\eta(u_i,x)v_i=x.
$$

This characterization is basis-free. Symmetry of $\eta$ implies

$$
\tau(C_\eta)=C_\eta,
\qquad
\tau(a\otimes b)=b\otimes a.
$$

The copairing is the tensor inserted whenever two marked points are joined to form a node.

## 4. Coalgebra structure

The pairing makes multiplication and comultiplication adjoint. The comultiplication is

$$
\Delta(a)=(a\otimes1)C_\eta=(1\otimes a)C_\eta.
$$

It satisfies

$$
(\epsilon\otimes\mathrm{id})\Delta=\mathrm{id},
\qquad
(\mathrm{id}\otimes\epsilon)\Delta=\mathrm{id},
$$

and it is coassociative. In the commutative case it is cocommutative. Its compatibility with multiplication is the Frobenius relation

$$
\Delta(ab)=(a\otimes1)\Delta(b)=\Delta(a)(1\otimes b).
$$

The **handle element**, or Euler element, is

$$
E=\mu(C_\eta)=\sum_i u_iv_i.
$$

To see why, regard a surface with one additional handle as the composite of a
pair of pants that splits one circle into two and a pair of pants that merges
those two circles again. A two-dimensional TFT assigns $\Delta$ to the first
bordism and $\mu$ to the second. Hence the operator assigned to the handle is

$$
(\mu\circ\Delta)(a)
=\mu\bigl((a\otimes1)C_\eta\bigr)
=a\,\mu(C_\eta)
=aE.
$$

Thus multiplication by $E$ represents the addition of one handle to a
surface. Equivalently, cutting open a handle produces two boundary circles;
sewing them back together inserts the two legs of $C_\eta$, and merging those
legs turns the insertion into $\mu(C_\eta)=E$.

## 5. Examples

For $A=R$ and $\epsilon=\mathrm{id}$, one has $C_\eta=1\otimes1$ and $E=1$.

For $A=K\times K$ with $\epsilon(a,b)=a+b$, the standard idempotents $e_1,e_2$ satisfy

$$
C_\eta=e_1\otimes e_1+e_2\otimes e_2,
\qquad
E=e_1+e_2=1.
$$

For the dual numbers $A=K[x]/(x^2)$ with $\epsilon$ equal to extraction of the coefficient of $x$,

$$
C_\eta=1\otimes x+x\otimes1,
\qquad
E=2x.
$$

The last example is nonsemisimple and is useful for checking that arguments do not accidentally assume diagonalizability.

## 6. Bridge to the next phase

The operations $\mu$, $1$, $\epsilon$, $\Delta$, and the identities above are exactly the algebraic images of the elementary oriented two-dimensional bordisms. This is the starting point of [M2: two-dimensional topological field theory](M02TwoDimensionalTFT.md).
