# M9. All-genus potentials and equations

Generating functions collect infinitely many GW invariants into algebraic objects on which structural identities can be written compactly. Their definitions require completed rings in the curve-class, genus, marking, and descendant variables.

## 1. Descendant variables

Choose a basis $(\phi_\alpha)$ of the state space and formal variables $t_k^\alpha$ for $k\ge0$. Write

$$
\mathbf t(\psi)=\sum_{k\ge0}\sum_\alpha t_k^\alpha\phi_\alpha\psi^k.
$$

The genus-$g$ descendant potential is

$$
\mathcal F_g(\mathbf t)
=
\sum_{\beta}\sum_{n\ge0}
\frac{Q^\beta}{n!}
\left\langle
\mathbf t(\psi),\ldots,\mathbf t(\psi)
\right\rangle_{g,n,\beta}.
$$

The analogous expression with ancestor classes $\bar\psi$ defines the ancestor potential.

This is the conventional full formula. The base Lean construction `descendantPotential` sets coefficients outside stable curve arities to zero. That stable-sector convention is narrower: for positive curve class, a stable-map invariant can exist even when the stabilized curve arity is unstable, so the omitted coefficients are not proved to vanish geometrically. The optional `UnstableDescendantConventions` supplies those numerical values explicitly, with multilinearity, relabelling, and integer virtual-dimension compatibility. Its degree-zero unstable values are all auxiliary zeros, outside the geometric query domain. `fullDescendantPotential` combines this family with the stable invariants without identifying an auxiliary convention with a geometric invariant.

## 2. Genus expansion

Introduce a formal genus parameter $\hbar$. The total free energy is

$$
\mathcal F=\sum_{g\ge0}\hbar^{g-1}\mathcal F_g.
$$

Negative powers occur because the genus-zero term is weighted by $\hbar^{-1}$. The coefficient ring must therefore support Laurent behavior in $\hbar$ together with power-series behavior in the remaining variables. The conventional total descendant potential is

$$
\mathcal D=\exp(\mathcal F)
=\exp\left(\sum_{g\ge0}\hbar^{g-1}\mathcal F_g\right).
$$

Because powers of the genus-zero term produce $\hbar^{-n}$ for arbitrarily large $n$, $\mathcal D$ does not belong to the ordinary Laurent-series ring used for $\mathcal F$. It requires a filtered Fock-space completion with appropriate local-finiteness conditions.

## 3. Basic equations

For stable correlators, the string equation is

$$
\left\langle\tau_0(\mathbf1)\prod_{i\in S}\tau_{k_i}(\gamma_i)\right\rangle_{g,\beta}
=
\sum_{i:k_i>0}
\left\langle\tau_{k_i-1}(\gamma_i)
\prod_{j\ne i}\tau_{k_j}(\gamma_j)\right\rangle_{g,\beta}.
$$

The dilaton equation is

$$
\left\langle\tau_1(\mathbf1)\prod_{i\in S}\tau_{k_i}(\gamma_i)\right\rangle_{g,\beta}
=
(2g-2+|S|)
\left\langle\prod_{i\in S}\tau_{k_i}(\gamma_i)\right\rangle_{g,\beta}.
$$

For a divisor $D$, the descendant divisor equation is

$$
\begin{aligned}
\left\langle\tau_0(D)\prod_{i\in S}\tau_{k_i}(\gamma_i)\right\rangle_{g,\beta}
={}&
\left(\int_\beta D\right)
\left\langle\prod_{i\in S}\tau_{k_i}(\gamma_i)\right\rangle_{g,\beta}
\\
&+\sum_{i:k_i>0}
\left\langle\tau_{k_i-1}(D\smile\gamma_i)
\prod_{j\ne i}\tau_{k_j}(\gamma_j)\right\rangle_{g,\beta}.
\end{aligned}
$$

For the full numerical extension, add the following correction to the right-hand side of each equation. Here $n=|S|$ counts the remaining markings, before adding the string, dilaton, or divisor insertion. Every correction is zero outside its stated support.

| Equation | Exceptional support | Added correction |
| --- | --- | --- |
| String | $g=0$, $\beta=0$, $n=2$, and all $k_i=0$ | $\eta(\gamma_1,\gamma_2)$ |
| Dilaton | $g=1$, $\beta=0$, $n=0$ | $c_X$ |
| Divisor | $g=0$, $\beta=0$, $n=2$, and all $k_i=0$ | $\langle D,\gamma_1,\gamma_2\rangle_{0,3,0}$ |
| Divisor | $g=1$, $\beta=0$, $n=0$ | $\ell_X(D)$ |

The dilaton coefficient is signed: the genus-zero values at $n=0,1,2$ are $-2,-1,0$. The stable Lean law retains its natural-number expression, since stability makes that subtraction nonnegative; the full law uses `dilatonCoefficient` in the coefficient ring. The metric correction does not assign a nonzero value to the auxiliary degree-zero two-point correlator. In particular `UnstableDescendantConventions.twoPoint_zero` now concludes zero, replacing its former metric-valued statement. The independent two-point calibration convention is unchanged.

For a smooth projective target of complex dimension $d$, the geometric initial values are

$$
c_X=\frac{\chi(X)}{24},
\qquad
\ell_X(D)=-\frac1{24}\int_X D\smile c_{d-1}(TX).
$$

The signs agree with [Tseng, Theorem 1.1, equations (1.3)--(1.4)](https://arxiv.org/pdf/0912.3580), specialized to a target with trivial stabilizers. The formal interfaces supply the scalar and linear functional explicitly; they do not prove a Chern-class interpretation. The point fixture uses $c_X=1/24$; the surface parameter fixtures use $3/24,4/24,5/24$, with their target identifications reserved for R1. [Wennink's Lemma 4.10](https://arxiv.org/pdf/2210.04038) prints a conflicting negative dilaton sign; the positive point normalization and Tseng formula determine the convention here.

Passing to differential equations for potentials packages the metric exception into the usual quadratic string term. Splitting and genus reduction also yield quadratic expressions because markings are distributed between components and the two node states are contracted by $C_\eta$.

For a geometric state space, $D\smile\gamma_i$ is cup product. The abstract Lean interface instead asks for a bilinear divisor action because a bare `GromovWittenTheory` does not carry an independently specified cup product.

## 4. Tautological relations

Relations in the tautological rings of $\overline{\mathcal M}_{g,S}$ produce universal equations for every CohFT and hence for GW theory. Genus-zero boundary relations give WDVV and topological recursion. Higher-genus relations lead to further constraints after decorating stable graphs by CohFT classes and contracting their edges.

A formal theorem should distinguish clearly between an equation that follows from the minimal GW axioms and one that requires a particular tautological relation as an additional input.

## 5. Axiomatic endpoint

At this stage the intended project has an all-genus, curve-class-resolved theory with primary classes, descendants, ancestors, Novikov coefficients, explicitly hypothesized comparison identities, genus potentials, and total free energies. The implemented endpoint is narrower in the ways stated below.

The remaining question is why geometric GW invariants satisfy these axioms. See [M10: geometric realization](M10GeometricRealization.md).

## 6. Implemented boundary

Formal descendant variables are represented by `MvPowerSeries`, with project-owned partial derivatives, their Leibniz and commutation laws, commuting iterated derivatives, stable-sector projection, and basis-direction insertion derivatives. `GromovWittenTheory.descendantPotential` and `ancestorPotential` construct stable-sector genus potentials coefficientwise from invariants using a canonical finite occurrence-label type and the reciprocal multiplicity factorial. `DescendantAncestorComparison.descendantPotential_eq_ancestor_add_boundary` lifts the recorded residual identity to these constructed series; despite the retained declaration name, it does not prove geometric boundary support.

`GWPotentials` stores the resulting Novikov-valued genus potentials. `totalFreeEnergy` is an actual `LaurentSeries`, defined as $\hbar^{-1}$ times the corresponding power series, and its coefficient at $\hbar^{g-1}$ is proved to be the genus-$g$ potential. `DescendantStringDilatonLaws` records the unchanged stable equations. The revised `UnstableDescendantConventions` combines its numerical data with the separately defined exceptional terms to give corrected `global_string`, `global_dilaton`, and `fullDescendantPotential`. `invariantMap`, `invariant_relabel`, and `invariant_eq_zero_of_degree_ne` expose the full numerical family's coherence. R0 is implemented and verified within this numerical-interface scope; finite boundary fixtures verify normalization compatibility without constructing an all-genus geometric point or surface model.

The optional full divisor extension uses the actual integrated genus-zero primary cubic for its first correction, and a supplied genus-one linear functional for its second. This avoids identifying an arbitrary `divisorAction` with a cup product without a compatibility theorem. These are correlator/coefficient equations; a packaged vector-field PDE syntax is not claimed. The unrestricted exponential $\exp(\mathcal F)$ remains outside the Laurent completion; `CompletedFockPotential` is instead a coefficientwise carrier used only with an explicit quantized action.

The point-target specialization is developed separately in [The point target and stable-curve intersection theory](PointTargetAndStableCurves.md). It identifies point ancestors with psi-class intersections and states the higher tautological DVV recursion as an additional geometric hypothesis.
