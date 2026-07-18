# M3. Stable curves and gluing

This note describes the geometric operations on moduli spaces of stable curves that form the target-side infrastructure of a CohFT.

## 1. Stable marked curves

A connected nodal curve of arithmetic genus $g$ with markings indexed by a finite set $S$ is stable when every irreducible genus-zero component has at least three special points and every genus-one component has at least one special point. Numerically, the moduli space exists in the stable range

$$
2g-2+|S|>0.
$$

Its compact moduli space is denoted

$$
\overline{\mathcal M}_{g,S}.
$$

Finite label sets are preferable to a fixed ordered set because all geometric maps are naturally expressed by adding, removing, or relabelling named points.

## 2. Primitive maps

For a bijection $\sigma:S\simeq T$, relabelling gives an isomorphism between the corresponding moduli spaces and hence a pullback on cohomology.

For a new label $*$, forgetting that marking and stabilizing gives

$$
\pi:\overline{\mathcal M}_{g,S\sqcup\{*\}}
\longrightarrow
\overline{\mathcal M}_{g,S}.
$$

Separating gluing identifies one new marking on each of two curves:

$$
\xi:\overline{\mathcal M}_{g_1,S\sqcup\{*\}}
\times
\overline{\mathcal M}_{g_2,T\sqcup\{*\}}
\longrightarrow
\overline{\mathcal M}_{g_1+g_2,S\sqcup T}.
$$

Nonseparating gluing identifies two markings on one curve:

$$
\iota:\overline{\mathcal M}_{g,S\sqcup\{+,-\}}
\longrightarrow
\overline{\mathcal M}_{g+1,S}.
$$

A CohFT is formulated using the pullbacks $\xi^*$ and $\iota^*$ because its values are cohomology classes on the target moduli space.

## 3. Abstract cohomology system

The axiomatic project does not initially construct the stacks $\overline{\mathcal M}_{g,S}$. Instead, it uses only their even cohomology and needs an abstract family of ordinary commutative graded algebras

$$
H_{g,S}
$$

equipped with relabelling pullbacks, forgetful pullbacks, gluing pullbacks, external products, and their compatibility laws. The first interface includes functoriality of relabelling, naturality of primitive gluing, compatibility of forgetting with gluing, and node/component symmetries. Coherence for arbitrary iterated gluings belongs to the separate optional stable-graph layer rather than the core interface.

The Lean grading is half the ordinary cohomological degree: its degree-$d$ piece models $H^{2d}(\overline{\mathcal M}_{g,S})$. Consequently `psi` and divisor classes have degree one, top degree is the complex dimension, and no Koszul signs occur in products or gluing. `StableCurveCohomology` enforces vanishing above `3g - 3 + |S|`; it does not assert that the top component itself is nonzero. Odd cohomology is deliberately outside the scope of the interface.

This interface isolates the part of stable-curve geometry actually used by CohFT axioms.

Two optional extensions record geometric facts not forced by this abstract interface. `GenusZeroGeometry` contains the point identification for $\overline{\mathcal M}_{0,3}$ and the relevant four-point boundary relation. `ConnectedDegreeZero` supplies coherent identifications

$$
H^0_{g,S}\cong R
$$

for every stable pair. The latter is automatic for the actual connected moduli spaces but is kept separate for abstract targets; it is exactly what turns the degree-zero projection of a CohFT into an $R$-valued topological CohFT.

## 4. Stable graphs

A stable graph records a boundary stratum. Its vertices carry genera, its legs carry the labels in $S$, and its internal edges pair half-edges. Every vertex satisfies its own stability condition. The total genus is

$$
g(\Gamma)=h^1(\Gamma)+\sum_{v}g(v).
$$

Contracting every internal edge describes the map from a product of vertex moduli spaces to $\overline{\mathcal M}_{g,S}$. The optional graph-pullback layer records the order coherence needed to make graph evaluation independent of the order in which edges are processed.

`StableGraph` implements this finite combinatorics using an edge type with two branches, so loops and multiple edges are represented without a half-edge quotient. It defines vertex label types, valence, first Betti number, total genus, relabeling, and complete contraction orders. `StableGraphPullbacks` is an optional extension recording ordered graph pullbacks and their permutation coherence; the derived canonical pullback is independent of a complete edge order, and the constant cohomology target supplies a concrete algebraic instance. Actual combinatorial edge contraction and geometric graph pullbacks for moduli-space targets remain unimplemented.

With this target-side system available, one can state the full CohFT axioms. See [M4: full unital CohFT](M04FullUnitalCohFT.md).
