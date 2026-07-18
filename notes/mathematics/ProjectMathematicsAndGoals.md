# The mathematics and goals of AxiomaticGW

## 1. Purpose of the project

AxiomaticGW is a Lean formalization of the algebraic and axiomatic structure of Gromov--Witten theory. Its purpose is not initially to construct moduli stacks or virtual fundamental classes from first principles. Instead, it isolates the operations and identities that make Gromov--Witten invariants behave as a cohomological field theory and proves their consequences in a reusable formal system.

The intended endpoint is an all-genus, curve-class-resolved theory containing:

- primary Gromov--Witten classes;
- separating and nonseparating gluing;
- the flat unit and divisor axioms;
- grading and virtual-dimension constraints;
- tautological classes and ancestor invariants;
- stable-map descendants and their comparison with ancestors;
- Novikov coefficients and quantum products;
- genus expansions, genus potentials, and total free energies;
- string, dilaton, divisor, splitting, genus-reduction, WDVV, and tautological equations under the corresponding abstract hypotheses.

The project proceeds from elementary multilinear algebra to this endpoint in small independently checked layers.

The notation uses a coefficient ring $R$. The principal numerical specialization is rational GW theory, with $R=\mathbb Q$ before adjoining Novikov or formal variables. The exact Lean-level generality of the new CohFT interfaces is an architectural decision tracked separately; it does not change the mathematical endpoint described here.

## 2. The geometric source of Gromov--Witten theory

Let $X$ be a smooth projective variety and let $\beta$ be an effective curve class. The moduli space

$$
\overline{\mathcal M}_{g,S}(X,\beta)
$$

parametrizes stable maps to $X$ from genus-$g$ nodal curves whose marked points are labelled by a finite set $S$. It has evaluation maps

$$
\operatorname{ev}_i:
\overline{\mathcal M}_{g,S}(X,\beta)\longrightarrow X
\qquad (i\in S)
$$

and, in the stable range, a stabilization map

$$
\operatorname{st}:
\overline{\mathcal M}_{g,S}(X,\beta)
\longrightarrow
\overline{\mathcal M}_{g,S}.
$$

The stable-map space generally has the wrong ordinary dimension. A virtual fundamental class supplies the expected intersection theory. Given insertions $\gamma_i\in H^*(X)$, the associated primary GW class is schematically

$$
\Omega^X_{g,S,\beta}((\gamma_i))
=
\operatorname{st}_*
\left(
  \prod_{i\in S}\operatorname{ev}_i^*(\gamma_i)
  \cap
  [\overline{\mathcal M}_{g,S}(X,\beta)]^{\mathrm{vir}}
\right).
$$

This class lies on the moduli space of stable curves. The symmetries, forgetful maps, and boundary gluings of stable curves turn the collection of all such classes into a highly structured object.

The formalization begins with that structure. It first assumes abstract cohomology and gluing operations satisfying their geometric identities, then derives the algebraic consequences. A later realization theorem will state which abstract virtual-stable-map data are sufficient to construct the axiomatic theory.

## 3. Algebraic foundations

### 3.1 Perfect pairings

The state space $V$ is finite free over the coefficient ring and has a symmetric perfect pairing

$$
\eta:V\otimes V\longrightarrow R.
$$

Perfectness identifies $V$ with its dual. Equivalently, it produces a canonical copairing, or inverse metric,

$$
C_\eta\in V\otimes V.
$$

Contracting node insertions against $C_\eta$ is the algebraic form of gluing two branches of a curve.

### 3.2 Frobenius algebras

A commutative Frobenius algebra consists of a commutative algebra $A$ and a counit

$$
\epsilon:A\longrightarrow R
$$

such that

$$
\eta(a,b)=\epsilon(ab)
$$

is a perfect pairing. The inverse metric determines the Casimir tensor, comultiplication, and handle element $E$.

The associated finite-labelled topological correlators are

$$
\omega_{g,S}((a_s))
=
\epsilon\left(\prod_{s\in S}a_s\,E^g\right).
$$

Their contraction identities encode separating and nonseparating sewing of closed oriented surfaces. This Frobenius-to-TFT layer is the completed foundation of the repository.

## 4. Stable curves and the cohomology convention

The moduli space of stable curves with genus $g$ and finite label set $S$ is denoted

$$
\overline{\mathcal M}_{g,S}.
$$

Its numerical stability condition is

$$
2g-2+|S|>0,
$$

represented in Lean without natural-number subtraction as

$$
3\leq 2g+|S|.
$$

The project uses only even stable-curve cohomology. For each stable pair it models an abstract commutative graded algebra

$$
H_{g,S}=H^{\mathrm{even}}(\overline{\mathcal M}_{g,S};R).
$$

The grading uses the algebraic-geometric codimension convention:

$$
H_{g,S}^{d}\quad\text{models}\quad
H^{2d}(\overline{\mathcal M}_{g,S};R).
$$

Thus divisors and psi classes have degree one, multiplication adds degrees, and top degree equals the complex dimension $3g-3+|S|$. Odd cohomology and Koszul signs are outside the project scope.

The grading is internal: $H_{g,S}$ is one total algebra equipped with degree submodules and a finite homogeneous decomposition. This lets general CohFT classes live in the total ring while retaining typed homogeneous pieces.

The abstract stable-curve system supplies pullbacks for:

- relabelling marked points by finite-set equivalences;
- forgetting a marked point and stabilizing;
- separating gluing of two curves at distinguished markings;
- nonseparating gluing of two markings on one curve.

It also records the functoriality, naturality, and coherence identities used by CohFT axioms. Stable graphs later package iterated boundary gluings.

## 5. Cohomological field theories

A unital CohFT assigns to every stable pair $(g,S)$ a multilinear map

$$
\Omega_{g,S}:V^{\otimes S}\longrightarrow H_{g,S}.
$$

The defining properties are the following.

### 5.1 Relabelling

The classes are natural under bijections of finite label sets. The project uses finite types rather than only ordered sets `Fin n` so this symmetry is present in the indexing itself.

### 5.2 Separating gluing

When a curve splits into components of genera $g_1$ and $g_2$, restriction to the corresponding boundary equals the external product of the component classes with the two new state-space inputs contracted against $C_\eta$:

$$
\xi^*\Omega_{g_1+g_2,S\sqcup T}
=
\operatorname{Contr}_{C_\eta}
\left(
  \Omega_{g_1,S\sqcup\{*\}}
  \boxtimes
  \Omega_{g_2,T\sqcup\{*\}}
\right).
$$

### 5.3 Nonseparating gluing

Identifying two markings on one curve raises the genus by one:

$$
\iota^*\Omega_{g+1,S}
=
\operatorname{Contr}_{C_\eta}
\left(\Omega_{g,S\sqcup\{+,-\}}\right).
$$

### 5.4 Flat unit

There is a distinguished vector $\mathbf 1\in V$. Inserting it at a new marking agrees with pullback along the forgetful map:

$$
\Omega_{g,S\sqcup\{*\}}((v_s),\mathbf 1)
=
\pi^*\Omega_{g,S}((v_s)).
$$

The three-point normalization identifies the unit insertion with the metric.

## 6. Frobenius algebra and WDVV from a CohFT

Because $\overline{\mathcal M}_{0,3}$ is a point, the three-point class defines a multiplication on $V$ by

$$
\eta(a*b,c)=\Omega_{0,3}(a,b,c).
$$

Relabelling gives commutativity, the flat-unit axiom gives the identity, and the two boundary presentations of $\overline{\mathcal M}_{0,4}$ give associativity. The same boundary relation, written for a varying insertion, is the WDVV equation.

Consequently the genus-zero Frobenius algebra is derived from the full all-genus CohFT. It is not a replacement for the higher-genus theory.

Projecting to codimension zero gives the topological part when the degree-zero cohomology is identified with the coefficient ring. The existing scalar-valued `TopologicalCohFT` is the model and regression test for this construction.

## 7. Tautological classes and ancestors

For a marking $i$, the stable-curve cotangent line has first Chern class

$$
\psi_i\in H^2(\overline{\mathcal M}_{g,S}),
$$

which has project degree one. Other distinguished classes include

$$
\kappa_m=\pi_*(\psi_*^{m+1})
\qquad\text{and}\qquad
\lambda_j=c_j(\mathbb E).
$$

Using integration on the stable-curve space, ancestor correlators are

$$
\left\langle
\prod_{i\in S}\bar\tau_{k_i}(v_i)
\right\rangle_g
=
\int_{\overline{\mathcal M}_{g,S}}
\Omega_{g,S}((v_i))
\prod_{i\in S}\psi_i^{k_i}.
$$

To formalize this expression, the stable-curve system must be extended with proper pushforward, integration, external products, projection formulas, base-change identities, top-degree rules, and the relevant tautological relations.

## 8. Curve-class-resolved GW theory

Let $B$ be a monoid of effective curve classes. A GW theory refines a CohFT to classes

$$
\Omega_{g,S,\beta}:V^{\otimes S}\longrightarrow H_{g,S},
\qquad \beta\in B.
$$

At a separating node the total class is distributed over the two components:

$$
\xi^*\Omega_{g_1+g_2,S\sqcup T,\beta}
=
\sum_{\beta_1+\beta_2=\beta}
\operatorname{Contr}_{C_\eta}
\left(
  \Omega_{g_1,S\sqcup\{*\},\beta_1}
  \boxtimes
  \Omega_{g_2,T\sqcup\{*\},\beta_2}
\right).
$$

The formal system must state a finiteness condition making this coefficient sum meaningful. Nonseparating gluing preserves $\beta$.

Additional GW data and axioms include:

- effectivity of curve classes;
- the virtual complex dimension
  $$
  (1-g)(\dim_\mathbb C X-3)+|S|+\int_\beta c_1(TX);
  $$
- grading compatibility;
- the divisor--curve pairing and divisor equation;
- a geometric degree-zero formula recovering classical multiplication;
- explicit treatment of unstable exceptional cases.

These properties are not consequences of a bare CohFT.

## 9. Novikov coefficients and quantum products

Introduce formal monomials $Q^\beta$ satisfying

$$
Q^{\beta_1}Q^{\beta_2}=Q^{\beta_1+\beta_2}.
$$

The coefficientwise theory is assembled as

$$
\Omega_{g,S}=\sum_{\beta\in B}Q^\beta\Omega_{g,S,\beta}.
$$

A Novikov support condition controls the infinite sum. The small quantum product is characterized by

$$
\eta(a*_Q b,c)
=
\sum_{\beta\in B}Q^\beta
\langle a,b,c\rangle_{0,3,\beta}.
$$

Its associativity follows from separating gluing on $\overline{\mathcal M}_{0,4}$. Adding a formal point $t\in V$ gives the big quantum product and the genus-zero primary potential; WDVV is the corresponding associativity equation.

The project proves cohomology-valued identities coefficientwise. Numerical invariants and the finite-free state space pass to the chosen Novikov completion, where fixed coefficients use only finite antidiagonals. An arbitrary cohomology family $B\to H$ is not identified with the algebraic tensor product $(B\to R)\otimes_R H$ without an additional target-finiteness or completed-tensor hypothesis.

## 10. Descendants and ancestors are different

Stable-map descendant classes live on $\overline{\mathcal M}_{g,S}(X,\beta)$:

$$
\psi_i^{\mathrm{map}}=c_1(L_i^{\mathrm{map}}).
$$

Ancestor classes are pulled back from the stable-curve space:

$$
\bar\psi_i=\operatorname{st}^*(\psi_i^{\mathrm{curve}}).
$$

They are not definitionally equal. Stabilization can contract a rational component, producing boundary corrections of the schematic form

$$
\psi_i^{\mathrm{map}}
=
\bar\psi_i+\text{boundary terms}.
$$

Descendant invariants integrate powers of $\psi_i^{\mathrm{map}}$ against the virtual class. Ancestor invariants use powers of $\bar\psi_i$. The project keeps these classes in distinct interfaces. The current Lean API records only their residual difference; a genuine comparison derived from explicit stabilization and boundary hypotheses remains future work.

## 11. All-genus potentials

With descendant variables $t_k^\alpha$, the genus-$g$ potential is schematically

$$
\mathcal F_g
=
\sum_{\beta}\sum_{n\geq 0}\frac{Q^\beta}{n!}
\left\langle
\mathbf t(\psi),\ldots,\mathbf t(\psi)
\right\rangle_{g,n,\beta}.
$$

Introducing a genus parameter $\hbar$, the total free energy is formally

$$
\mathcal F=\sum_{g\geq 0}\hbar^{g-1}\mathcal F_g.
$$

This expression requires a completion simultaneously controlling curve classes, insertion variables, descendant degree, and genus. It is bounded below by $\hbar^{-1}$ and therefore fits an ordinary Laurent-series genus expansion. Its exponential can contain arbitrarily negative powers of $\hbar$ and is deferred until a concrete theorem requires a filtered mixed completion.

Once the coefficient ring is defined, geometric axioms become formal differential equations: string, dilaton, divisor, splitting, genus reduction, WDVV, topological recursion, and higher tautological relations.

## 12. Formalization boundary

### Included in the main project

- Abstract even cohomology of stable-curve spaces.
- Pullbacks, external products, gluing, pushforwards, and integration as explicitly axiomatized operations.
- Full unital CohFTs and their Frobenius/topological/genus-zero consequences.
- Effective-curve-class refinements and Novikov packaging.
- Ancestor and descendant theories with a formal residual identity.
- Quantum products, stable-sector potentials, and optional stable equations.
- An abstract algebraic output carrier for future virtual GW realizations.

### Not required for the axiomatic endpoint

- Construction of Deligne--Mumford stacks in Lean.
- Construction of the actual moduli stacks of stable curves or stable maps.
- Chow groups and rational equivalence from first principles.
- Perfect obstruction theories and intrinsic normal cones.
- Construction of virtual fundamental classes.
- Proof that a particular projective variety supplies all geometric data.

These are important longer-term geometric projects, but requiring them first would prevent development of the reusable axiomatic theory.

## 13. Milestone chain

```text
M1  perfect pairings and Frobenius algebras                 complete
  -> M2  finite-labelled two-dimensional TFT               complete
  -> M3  even cohomology of stable curves and gluing       complete
  -> M4  full unital all-genus CohFT                       complete
  -> M5  tautological classes, integration, and ancestors complete core
  -> M6  curve-class-resolved GW axioms                    complete core
  -> M7  Novikov coefficients and quantum products         coefficientwise core complete
  -> M8  descendants and descendant--ancestor comparison   optional rational-tail comparison implemented
  -> M9  all-genus potentials and equations                stable and explicit unstable extensions implemented
  -> M10 abstract geometric realization                    algebraic carrier only
```

Each phase is intended to compile independently and expose a stable API before the next phase begins.

## 14. Current status

The repository currently contains:

- symmetric perfect pairings and canonical copairings;
- commutative Frobenius algebras and their coalgebra structure;
- basis-free contraction and sewing identities;
- finite-labelled all-genus TFT correlators;
- separating and nonseparating sewing;
- a bundled topological correlator theory;
- its scalar-valued stable topological CohFT restriction;
- recovery of the counit and three-point product in the current fixed-algebra API;
- internally graded even-cohomology targets with primitive stable-curve maps;
- the full cohomology-valued CohFT interface and optional graded/geometric extensions;
- the constant degree-zero target and conversion to and from the existing topological CohFT;
- genus-zero restriction, Frobenius extraction, WDVV, and associativity;
- coherent degree-zero scalarization and full stable-arity classification of topological CohFTs by commutative Frobenius algebras;
- stable-curve psi classes, integration, forgetful pushforward, kappa classes, and ancestors;
- positive locally finite effective curve classes and beta-resolved primary GW axioms;
- the beta-preserving Novikov ring, fixed-beta quantum-product coefficients, and derived coefficientwise small WDVV and associativity;
- the invariant-defined commutative formal big product and its proved zero-background specialization to the small product;
- an optional higher-background WDVV package deriving formal big-product associativity;
- finite stable graphs and optional order-independent graph pullbacks;
- distinct stable-map descendants and stable-curve ancestors with both a weak residual API and an optional positive-tail factorization;
- invariant-defined Novikov-valued stable-sector descendant and ancestor potentials, their residual identity, and Laurent total free energies;
- a tail-derived two-point calibration with separately named symplectic and quantized-comparison hypotheses;
- explicit unstable conventions, a full descendant potential, global string/dilaton laws, and the separately usable divisor law;
- a self-contained point-target block identifying ancestors with psi intersections on stable curves and stating the all-genus DVV proposition as an additional hypothesis;
- an abstract virtual-GW algebraic output carrier, not a construction from geometry.

The next internal theorem boundary is the third-derivative characterization of the primary potential and a vector-field presentation of the global equations. The more important external boundary is a concrete stable-curve or stable-map geometric model instantiating the optional graph, stabilization, higher-boundary, or DVV hypotheses. The settled architectural choices are recorded in the design-decision ledger.

## 15. Criteria for success

The project succeeds when the main endpoint is expressed by Lean structures and theorems rather than only mathematical prose. In particular, it should be possible to:

1. construct a full CohFT from its abstract classes and verify its axioms;
2. recover the associated Frobenius algebra and prove associativity and WDVV;
3. construct Novikov-valued numerical invariants and quantum products from coefficientwise GW data;
4. define primary, ancestor, and descendant invariants without conflating their cotangent-line classes;
5. derive the standard equations from named abstract hypotheses;
6. eventually construct the axiomatic GW theory from genuine virtual-geometric input, rather than merely repackaging already axiomatized fields;
7. verify every implemented milestone with no `sorry` or `admit`.

## Further reading within the repository

- [Detailed mathematics notes for M1--M10](README.md)
- [Implementation roadmap](../milestones/AxiomaticGWRoadmap.md)
- [Mathlib inventory](../milestones/MathlibInventory.md)
- [CohFT design decisions](../milestones/CohFTDesignDecisions.md)
