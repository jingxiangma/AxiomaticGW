# M2. Two-dimensional topological field theory

This note explains how a commutative Frobenius algebra determines all correlators of a closed oriented two-dimensional topological field theory.

## 1. Bordisms and field theories

An **oriented 2D TFT** is a symmetric monoidal functor

$$
Z:\operatorname{Bord}^{\mathrm{or}}_2\longrightarrow R\text{-}\operatorname{Mod}.
$$

Objects of the bordism category are closed oriented one-manifolds, morphisms are diffeomorphism classes of compact oriented bordisms, composition is gluing along parametrized boundary circles, and the monoidal operation is disjoint union. The state modules must be dualizable; the project works with finite free modules.

The **state space** is the value on a positively oriented circle:

$$
A=Z(S^1).
$$

With two circles incoming and one outgoing, the pair of pants gives $\mu:A\otimes_R A\to A$; with one incoming and two outgoing, it gives $\Delta:A\to A\otimes_R A$. The disks give $\mathbf 1:R\to A$ and $\epsilon:A\to R$, and the cylinder gives $\mathrm{id}_A$. Functoriality under gluing gives the associativity, unit, counit, and Frobenius relations.

Conversely, a commutative Frobenius algebra assigns maps to pair-of-pants decompositions. The Frobenius identities prove that the result is independent of the chosen decomposition. This gives the classification

$$
\text{oriented 2D TFTs over }R
\simeq
\text{commutative Frobenius }R\text{-algebras}.
$$

### Feynman-diagram dictionary

We read the diagrams from left to right. A **black dot** marks an external circle carrying a state. A **trivalent junction** is a pair-of-pants bordism: two legs merging into one denote multiplication, while one leg splitting into two denotes comultiplication. A leg created from no input denotes the unit, and a leg ending with no output denotes the counit.

![Dictionary identifying the Feynman diagrams for merging, creation, splitting, and annihilation with the corresponding two-dimensional bordisms and Frobenius algebra operations](images/m02-feynman-dictionary.png)

The base field denoted by $\mathbb{k}$ in the dictionary plays the role of the base ring $R$ used in these notes.

## 2. Finite-labelled correlators

Let $S$ be a finite type. The TFT assigns to a connected genus-$g$ surface with incoming boundary circles labelled by $S$ and no outgoing boundary an $R$-linear functional

$$
\omega_{g,S}:\bigotimes_{s\in S}A\longrightarrow R.
$$

This functional is the **connected genus-$g$, $S$-labelled correlator**. Equivalently, $\omega_{g,S}$ is multilinear in a family of states $(a_s)_{s\in S}$, where the circle labelled by $s$ carries $a_s\in A$. Using a label type rather than only the number $|S|$ makes relabelling and gluing canonical: a bijection $S\simeq T$ reindexes the inputs, while disjoint collections of inputs are indexed by $S\sqcup T$.

Let

$$
m_S:\bigotimes_{s\in S}A\longrightarrow A,
\qquad
m_S\left(\bigotimes_{s\in S}a_s\right)=\prod_{s\in S}a_s,
$$

with $m_\varnothing(1)=1_A$. Let $m_E:A\to A$ be multiplication by the handle element. The map assigned to a connected genus-$g$ bordism from the $S$-labelled circles to the empty one is

$$
\omega_{g,S}=\epsilon\circ m_E^g\circ m_S.
$$

Indeed, the genus-one bordism with one incoming and one outgoing circle is the composite $\mu\circ\Delta$, and

$$
\mu\circ\Delta=m_E,
\qquad
m_E(a)=aE.
$$

It follows directly that

$$
\boxed{\displaystyle
\omega_{g,S}((a_s)_{s\in S})
=
\epsilon\left(\prod_{s\in S}a_s\,E^g\right).}
$$

Associativity and commutativity make $m_S$ independent of an ordering or parenthesization, and the Frobenius relation identifies the maps obtained from different pair-of-pants decompositions.

![Feynman diagram for a genus-zero three-point correlator: three external states pass through two multiplication vertices and terminate at the counit](images/m02-genus-zero-decomposition.svg)

The **handle operator** is therefore

$$
H=\mu\circ\Delta:A\longrightarrow A.
$$

![Feynman diagram for the handle operator: a state splits at comultiplication, travels along two internal legs, and rejoins at multiplication to acquire one factor of the Euler element](images/m02-handle-sewing.svg)

Using $\Delta(a)=(a\otimes1)C_\eta$ and $E=\mu(C_\eta)$, we obtain

$$
H(a)
=\mu\bigl((a\otimes1)C_\eta\bigr)
=a\,\mu(C_\eta)
=aE.
$$

Its $g$-fold composite is

$$
H^g(x)=xE^g.
$$

For example, when $g=1$ and $S=\{1,2\}$,

$$
(\mu\circ\Delta)(ab)
=\sum_i abu_iv_i
=abE,
\qquad
\omega_{1,\{1,2\}}(a,b)=\epsilon(abE).
$$

For $S=\varnothing$, the convention $m_\varnothing(1)=1_A$ gives the closed genus-$g$ **partition function**

$$
Z(\Sigma_g)=\epsilon(E^g).
$$

This is the same correlator formula with the convention that the empty product is $1_A$. In particular, the genus-one closed surface is the torus, and

$$
Z(T^2)=\epsilon(E).
$$

Finally, the genus-zero one-, two-, and three-point correlators recover the basic Frobenius data:

$$
\omega_{0,1}(a)=\epsilon(a),
\qquad
\omega_{0,2}(a,b)=\eta(a,b),
\qquad
\omega_{0,3}(a,b,c)=\epsilon(abc)=\eta(ab,c).
$$

The one-point correlator is the counit, the two-point correlator is the Frobenius pairing, and the perfectness of that pairing means that the three-point correlator determines the multiplication.

## 3. Sewing identities

Write the copairing as $C_\eta=\sum_i u_i\otimes v_i$. Its contraction identity implies the basic sewing formula

$$
\sum_i\epsilon(xu_i)\epsilon(v_i y)=\epsilon(xy).
$$

This is an immediate contraction calculation:

$$
\sum_i\epsilon(xu_i)\epsilon(v_i y)
=\epsilon\left(\left(\sum_i\eta(x,u_i)v_i\right)y\right)
=\epsilon(xy),
$$

where symmetry of $\eta$ and the defining identity of $C_\eta$ are used in the second equality.

**Nonseparating sewing** identifies two distinguished boundary circles on the same connected surface and creates a handle:

$$
\sum_i
\omega_{g,S\sqcup\{+,-\}}
((a_s),u_i,v_i)
=
\omega_{g+1,S}((a_s)).
$$

In the Feynman graph, this contraction creates a self-loop. The loop has first Betti number one, so it raises the total genus from $g$ to $g+1$.

![Nonseparating sewing: contracting two boundary legs on the same genus-g correlator creates a self-loop and raises the genus by one](images/m02-nonseparating-sewing.svg)

**Separating sewing** identifies one distinguished boundary circle on each of two connected surfaces and joins the components:

$$
\sum_i
\omega_{g_1,S\sqcup\{*\}}((a_s),u_i)
\omega_{g_2,T\sqcup\{*\}}((b_t),v_i)
=
\omega_{g_1+g_2,S\sqcup T}((a_s),(b_t)).
$$

Here the new edge joins two previously distinct vertices and creates no graph cycle. Its first Betti number is zero, so the genus of the connected surface is $g_1+g_2$.

![Separating sewing: contracting one boundary leg from each of two correlators creates an internal edge joining the components without adding a graph cycle](images/m02-separating-sewing.svg)

Symmetry of $C_\eta$ shows that neither sewing operation depends on the ordering of the two half-edges.

## 4. Topological CohFT viewpoint

Restricting to stable pairs $2g-2+|S|>0$ and multiplying each scalar correlator by the unit class in $H^0(\overline{\mathcal M}_{g,S})$ gives a topological, degree-zero CohFT. A general CohFT has higher-degree cohomology classes and therefore contains more information than its Frobenius algebra or associated TFT.

The next phase replaces scalar targets by an abstract system of cohomology groups for stable-curve moduli spaces. See [M3: stable curves and gluing](M03StableCurvesAndGluing.md).
