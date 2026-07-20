# Core structure dependencies: Frobenius algebra, TFT, CohFT, and axiomatic GW theory

This note records how the four central structures of AxiomaticGW depend on one another. It complements the phase-by-phase notes by presenting the constructions as explicit input--output transformations.

The structures are related, but not simply by inheritance:

```text
commutative Frobenius algebra <====> two-dimensional TFT
              ^                              ^
              | genus-zero extraction       | degree-zero/topological part
              +------------ CohFT -----------+
                              ^
                              | the same gluing pattern, refined by beta
                              |
                 axiomatic Gromov--Witten theory
```

The upward arrows forget information. A CohFT contains cohomology classes of stable-curve moduli spaces, while its Frobenius algebra and TFT retain only genus-zero or degree-zero shadows. Axiomatic GW theory adds an effective curve-class grading to the CohFT gluing pattern. A Novikov sum can recombine those graded pieces only when the required scalar extension and completion are available.

## 1. Frobenius algebra to two-dimensional TFT

### Input

Let $R$ be a commutative ring. The input is a finite-free commutative $R$-algebra with a Frobenius functional:

$$
(A,\mu,1,\epsilon),
\qquad
\eta(x,y)=\epsilon(xy),
$$

where the trace pairing $\eta$ is perfect. Its inverse metric is the Casimir tensor

$$
C_\eta\in A\otimes_R A.
$$

Multiplying the two legs of $C_\eta$ gives the handle element

$$
E=\mu(C_\eta)\in A.
$$

### Output

The output is a family of scalar correlators, indexed by a genus $g$ and a finite set of labels $S$:

$$
\omega^A_{g,S}:\bigotimes_{s\in S}A\longrightarrow R,
$$

with evaluation formula

$$
\boxed{
\omega^A_{g,S}((a_s)_{s\in S})
=\epsilon\left(\left(\prod_{s\in S}a_s\right)E^g\right).
}
$$

The multiplication combines the external states, the copairing contracts the two states placed at every node, and the factor $E^g$ records the genus. These correlators satisfy relabelling, unit insertion, separating sewing, nonseparating sewing, and two-point normalization. They therefore define the finite-labelled correlator presentation of a two-dimensional TFT:

$$
(A,\mu,1,\epsilon,C_\eta)
\longmapsto
(A,\eta,1,\{\omega^A_{g,S}\}).
$$

In Lean this is `CommFrobeniusAlgebra.toTwoDimensionalTFT`; the correlator formula is `CommFrobeniusAlgebra.correlator_apply`.

## 2. Two-dimensional TFT to Frobenius algebra and topological CohFT

### Input

The input is a finite-free state space with a symmetric perfect metric, a unit, and compatible scalar correlators:

$$
(V,\eta,\mathbf 1,\{\omega_{g,S}\}),
\qquad
\omega_{g,S}:\bigotimes_{s\in S}V\longrightarrow R.
$$

### Frobenius output

The genus-zero one-point correlator recovers the counit, and the genus-zero three-point correlator recovers multiplication after raising its last input with the perfect metric:

$$
\epsilon(x)=\omega_{0,1}(x),
\qquad
\eta(x*y,z)=\omega_{0,3}(x,y,z).
$$

Perfectness of $\eta$ determines $x*y$ uniquely. In the standard finite commutative setting, with the trace-compatibility condition used by the project classification, the output is

$$
(V,\eta,\mathbf 1,\{\omega_{g,S}\})
\longmapsto
(V,*,\mathbf 1,\epsilon),
$$

a commutative Frobenius algebra. Conversely, the Frobenius correlator construction recovers the original TFT data in the current fixed-algebra API.

### Topological-CohFT output

Restricting to stable arities and placing each scalar correlator in cohomological degree zero gives

$$
\Omega^{\mathrm{top}}_{g,S}(v)
=\omega_{g,S}(v)\,1_{H_{g,S}},
$$

where $H_{g,S}$ is the chosen stable-curve cohomology target. Thus

$$
(V,\eta,\mathbf 1,\{\omega_{g,S}\})
\longmapsto
\{\Omega^{\mathrm{top}}_{g,S}\}.
$$

The repository implements this construction first for its constant stable-curve target. The relevant declarations are `TwoDimensionalTFT.toTopologicalCohFT` and `TopologicalCohFT.toConstantCohFT`.

## 3. CohFT to its Frobenius and TFT shadows

### Input

Let $H_{g,S}$ be an abstract even cohomology algebra assigned to every stable pair, equipped with relabelling, forgetful, separating-gluing, and nonseparating-gluing pullbacks. A CohFT supplies

$$
(V,\eta,\mathbf 1,\{\Omega_{g,S}\}),
\qquad
\Omega_{g,S}:\bigotimes_{s\in S}V\longrightarrow H_{g,S},
$$

subject to the corresponding naturality, unit, and gluing axioms.

### Genus-zero Frobenius output

The space $\overline{\mathcal M}_{0,3}$ is a point. After choosing the project interface

$$
\iota_{0,3}:H_{0,3}\simeq R,
$$

the three-point class becomes the scalar function

$$
\omega_{0,3}^{\Omega}(x,y,z)
=\iota_{0,3}(\Omega_{0,3}(x,y,z)).
$$

The extracted product $*_\Omega$ is defined by

$$
\boxed{
\eta(x *_\Omega y,z)
=\iota_{0,3}(\Omega_{0,3}(x,y,z)).
}
$$

Relabelling gives commutativity, the flat-unit axiom gives the identity, and the two boundary presentations of $\overline{\mathcal M}_{0,4}$ give WDVV and hence associativity. The output is the genus-zero Frobenius algebra

$$
(V,\eta,\mathbf 1,\{\Omega_{g,S}\})
\longmapsto
(V,*_\Omega,\mathbf 1,\epsilon_\Omega).
$$

This construction is implemented by the `GenusZeroCohFT` product and its conversion to `CommFrobeniusAlgebra` under `GenusZeroGeometry`.

### Degree-zero TFT output

Suppose each connected degree-zero piece is identified with the coefficient ring:

$$
H_{g,S}^{0}\simeq R.
$$

Projecting a CohFT class to degree zero and applying this identification gives

$$
\omega^\Omega_{g,S}
=\pi_0\circ\Omega_{g,S}:
\bigotimes_{s\in S}V\longrightarrow R.
$$

These scalar correlators form the topological part of the CohFT:

$$
\{\Omega_{g,S}\}
\longmapsto
\{\omega^\Omega_{g,S}\}.
$$

The higher-degree components of $\Omega_{g,S}$ are precisely the information discarded by this operation. In Lean the required degree-zero identifications are bundled by `ConnectedDegreeZero`, and the output is `CohFT.topologicalPart`.

## 4. Axiomatic GW theory as a curve-class-resolved CohFT pattern

### Input

Let $B$ be a positive locally finite monoid of effective curve classes. The primary axiomatic GW input consists of

$$
(B,V,\eta,\mathbf 1,c_1,\{\Omega_{g,S,\beta}\}_{\beta\in B}),
$$

where

$$
\Omega_{g,S,\beta}:
\bigotimes_{s\in S}V
\longrightarrow H_{g,S}.
$$

Besides the CohFT-style relabelling, unit, and node-contraction laws, it carries a state-space grading, the first-Chern degree $c_1:B\to\mathbb Z$, the virtual-dimension condition, effectivity, beta-zero normalization, and optional divisor data.

### Separating output law

The essential new dependence appears at a separating node. For a total curve class $\beta$, the boundary restriction is a convolution over all effective splittings:

$$
\boxed{
\operatorname{gl}_{\mathrm{sep}}^*
\Omega_{g_1+g_2,S\sqcup T,\beta}
=
\sum_{\beta_1+\beta_2=\beta}
\operatorname{Contr}_{C_\eta}
\left(
\Omega_{g_1,S\sqcup\{*\},\beta_1},
\Omega_{g_2,T\sqcup\{*\},\beta_2}
\right).
}
$$

Nonseparating gluing preserves the curve class:

$$
\operatorname{gl}_{\mathrm{irr}}^*
\Omega_{g+1,S,\beta}
=
\operatorname{Contr}_{C_\eta}
\left(
\Omega_{g,S\sqcup\{+,-\},\beta}
\right).
$$

A fixed-$\beta$ family is therefore not by itself an ordinary CohFT: its separating boundary depends on every pair $(\beta_1,\beta_2)$ summing to $\beta$.

### Conditional Novikov output

If scalar extension and completion are justified, introduce formal monomials $Q^\beta$ and form

$$
\Omega^Q_{g,S}
=\sum_{\beta\in B}Q^\beta\Omega_{g,S,\beta}.
$$

Since

$$
Q^{\beta_1}Q^{\beta_2}=Q^{\beta_1+\beta_2},
$$

the separating sum becomes the ordinary CohFT gluing equation over the Novikov coefficient ring. Schematically,

$$
\{\Omega_{g,S,\beta}\}_{\beta\in B}
\overset{\sum_\beta Q^\beta(-)}{\longmapsto}
\{\Omega^Q_{g,S}\}.
$$

This arrow is deliberately conditional in the current project. `GromovWittenTheory` keeps arbitrary $H_{g,S}$-valued classes coefficientwise; the repository does not construct a general scalar extension of those targets or bundle a conversion to a Novikov-valued `CohFT`. Numerical and finite-free state-valued operations do carry the completed convolution structure needed for quantum products.

## 5. Information retained and forgotten

The complete input--output picture is

$$
(A,\mu,\epsilon)
\longmapsto
\{\omega^A_{g,S}\}
\longmapsto
\{\Omega^{\mathrm{top}}_{g,S}\},
$$

$$
\{\Omega_{g,S}\}
\longmapsto
(*_\Omega,\{\omega^\Omega_{g,S}\}),
$$

and, conditionally,

$$
\{\Omega_{g,S,\beta}\}
\overset{\sum_\beta Q^\beta(-)}{\longmapsto}
\{\Omega^Q_{g,S}\}.
$$

The first line constructs all topological correlators from local Frobenius data. The second forgets the positive-degree stable-curve cohomology carried by a general CohFT. The third recombines curve-class coefficients but requires a completion that is not automatic for arbitrary cohomology targets.

The dependencies can therefore be read in two directions:

- **construction direction:** Frobenius algebra $\to$ TFT $\to$ topological CohFT, and beta-resolved GW data $\to$ a Novikov-valued CohFT when completion is available;
- **extraction direction:** CohFT $\to$ genus-zero Frobenius algebra and CohFT $\to$ degree-zero TFT.

Neither extraction is an equivalence for a general CohFT because both discard its positive-degree cohomology classes. The Frobenius algebra--TFT equivalence is the special topological classification.

## Related notes

- [M1: perfect pairings and Frobenius algebras](M01PerfectPairingsAndFrobeniusAlgebras.md)
- [M2: two-dimensional topological field theory](M02TwoDimensionalTFT.md)
- [M4: full unital CohFT](M04FullUnitalCohFT.md)
- [M6: curve-class-resolved GW axioms](M06CurveClassResolvedGW.md)
- [M7: Novikov coefficients and quantum products](M07NovikovAndQuantumProducts.md)
