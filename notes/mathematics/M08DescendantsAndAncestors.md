# M8. Descendants and descendant--ancestor comparison

Primary GW invariants use only evaluation classes. Descendants additionally use cotangent-line classes on moduli spaces of stable maps. Ancestors use cotangent-line classes pulled back from moduli spaces of stable curves. These classes are related, but they are not definitionally the same.

## 1. Stable-map descendants

Let

$$
\overline{\mathcal M}_{g,S}(X,\beta)
$$

be the moduli space of stable maps. The universal stable map has a cotangent line $L_i^{\mathrm{map}}$ at each marking and a class

$$
\psi_i^{\mathrm{map}}=c_1(L_i^{\mathrm{map}}).
$$

For insertions $\gamma_i\in H^*(X)$, the descendant invariant is

$$
\left\langle
\prod_{i\in S}\tau_{k_i}(\gamma_i)
\right\rangle_{g,\beta}
=
\int_{[\overline{\mathcal M}_{g,S}(X,\beta)]^{\mathrm{vir}}}
\prod_{i\in S}
(\psi_i^{\mathrm{map}})^{k_i}
\operatorname{ev}_i^*(\gamma_i).
$$

These are numerical invariants unless additional markings are retained and the expression is pushed forward to a stable-curve space.

## 2. Ancestors

The stabilization map to the moduli of curves gives ancestor cotangent classes

$$
\bar\psi_i=\operatorname{st}^*(\psi_i^{\mathrm{curve}}).
$$

Replacing $\psi_i^{\mathrm{map}}$ by $\bar\psi_i$ defines ancestor invariants. Ancestors interact more directly with CohFT gluing because their psi classes come from the same stable-curve spaces on which CohFT classes live.

## 3. Comparison

The two cotangent lines differ on the locus where stabilization contracts the component carrying the marking. If $D_i$ denotes the sum of boundary divisors whose generic stable map has $i$ on a positive-degree rational tail that becomes unstable after forgetting the map, then

$$
\psi_i^{\mathrm{map}}
=
\bar\psi_i+[D_i].
$$

Products of this identity express descendants as ancestors plus terms supported on rational-tail boundary strata. At the generating-function level, Givental packages the genus-zero two-point descendants into an operator series $S_t(z)=1+S_1z^{-1}+S_2z^{-2}+\cdots$ characterized by

$$
\eta(a,S_t(z)b)
=
\eta(a,b)
+\sum_{k\ge0}
\left\langle a,b\psi^k\right\rangle_{0,2}(t)z^{-k-1}.
$$

The geometric two-point relations imply the symplectic identity

$$
S_t^*(-z)S_t(z)=1,
$$

where the adjoint is taken with respect to $\eta$. This identity is additional geometry, not a formal consequence of choosing an arbitrary operator series.

The formalization therefore maintains distinct interfaces for stable-map and stable-curve psi classes. Its weak comparison records only the residual difference. The optional stabilization package separately requires rational-tail support and factorization, while its calibration becomes symplectic only after a named two-point boundary relation is supplied.

## 4. Abstract descendant package

An axiomatic descendant extension needs stable-map psi classes, evaluation insertions, integration against a virtual class, and formulas for forgetting markings and restricting to boundary strata. String, dilaton, divisor, and topological recursion equations follow only after these properties are supplied.

Once primary, ancestor, and descendant correlators are defined with suitable completions, they can be assembled into all-genus generating functions. See [M9: all-genus potentials and equations](M09PotentialsAndEquations.md).

## 5. Implemented boundary

`GromovWittenTheory.ancestorClass` uses stable-curve `PsiClasses`, while `StableMapDescendants.descendantClass` is a distinct stabilized stable-map family with zero-power, relabelling, total-degree, and negative-total-degree laws. `DescendantAncestorComparison` remains the weak residual API. The optional `StabilizationBoundaryComparison` strengthens it by expressing that residual as a finite sum over positive-degree rational-tail splittings, with the boundary pushforward, tail weights, and state-space tail operators visible as hypotheses. Those same tail operators define `TwoPointCalibration`; a separately named two-point boundary identity implies coefficientwise symplecticity. `GiventalComparison` supplies a genus-one scalar factor and a coefficientwise descendant--ancestor identity rather than deriving either from a bare residual. Concrete stable-map geometry must still construct these packages. No definitional identification between the two cotangent-line theories is used.


## 6. Surface divisor action and unstable arities

For the three fixed surfaces, the existing numerical and stable string/divisor laws determine the divisor action. Evaluating the degree-zero four-point correlator with insertions $D,1,\tau_1(x),y$ in the two ways gives

$$
\eta(D\mathbin{\star}x,y)=\langle D,x,y\rangle_{0,0}
=\int_X Dxy.
$$

The first equality is generic; the second follows from the already derived surface classical cubic, extended by multilinearity. Nondegeneracy therefore gives $D\mathbin{\star}x=Dx$ for arbitrary divisor states and arbitrary linear insertions. This is proved in [`DivisorAction.lean`](../../AxiomaticGW/GW/Descendants/DivisorAction.lean) and [`DescendantDivisor.lean`](../../AxiomaticGW/Surfaces/DescendantDivisor.lean), without a new action-compatibility hypothesis.

At nonzero effective class, $e=c_1(X)\cdot\beta>0$. Solving the full divisor equation gives

$$
\left\langle\prod_i\tau_{k_i}(a_i)\right\rangle_{g,\beta}
=\frac{1}{e}\left(
\left\langle c_1(X)\prod_i\tau_{k_i}(a_i)\right\rangle_{g,\beta}
-\sum_{i:k_i>0}
\left\langle\tau_{k_i-1}(c_1(X)a_i)\prod_{j\ne i}\tau_{k_j}(a_j)\right\rangle_{g,\beta}
\right).
$$

For curve-unstable requests, every recursive branch decreases
$\sum_i k_i+\max(0,3-(2g+n))$: the first term adds a primary marking, and the corrections lower a positive cotangent power. [`DescendantStabilization.lean`](../../AxiomaticGW/Surfaces/DescendantStabilization.lean) implements this reduction, proves its computed bound sufficient, and proves agreement with the original numerical family whenever the supplied stable values are correct. Agreement of two stable families implies agreement at every arity; a fixed stable family has at most one numerical extension under the existing laws. Full curve classes and exceptional intersection signs are retained. Degree-zero unstable requests keep the auxiliary zero convention and are excluded by the geometric query adapter.

This proves an arity reduction, not stable descendant reconstruction or descendant--ancestor comparison. The stable callback is still required. Section 8 constructs the numerical rational-tail operators from this callback and identifies stored operators under an explicit paired-value condition. Deriving stable topological recursion from primitive cotangent and gluing laws and proving finite seed sufficiency for descendants remain open. See the [arity-reduction validation record](../../environments/surface-descendant-stabilization-validation.json).


## 7. Derived low-genus ancestor lowering

[`GenusOnePsi.lean`](../../AxiomaticGW/Tautological/GenusOnePsi.lean) fixes a raw three-column frame on $\overline{\mathcal M}_{1,1}$ and binds the searched certificate to $\psi_1-\frac1{24}\xi_*1$. Here $\xi$ glues the two ordered node flags on the three-point rational curve. Its graph has two automorphisms, so $\xi_*1=2\delta_{\mathrm{irr}}$; the normalized boundary formula has coefficient $1/12$. The Sage exporter preserves the original two 3-spin generator parameters, exact row coefficients and all graph decorations. Kernel replay checks the requested linear combination; geometric vanishing of those original rows remains an explicit input. The conventions follow [Getzler, equations (8)–(11)](https://arxiv.org/html/math/9801003#S4).

[`PsiBoundaryExpansion.lean`](../../AxiomaticGW/Tautological/PsiBoundaryExpansion.lean) constructs the actual gluing graph for the rational-tail divisor in the existing one-marking psi formula. `TailCompatible` identifies that divisor with this raw gluing class. It is a primitive geometric identification, separate from the stable-map two-point tail operators. The proved universal-curve base-change rule pulls each boundary graph back to the sum of its marking placements. Adding the new tail term and iterating derives the psi expansion for any number of additional markings. The genus-zero base follows from three-point dimension vanishing; the genus-one base consumes the accepted certificate above.

Every output graph has one edge. Multiplying by the remaining ancestor monomial and the actual GW class, integrating, and applying the existing gluing soundness theorem gives `genusZero_ancestor_eq_contractions` and `genusOne_ancestor_eq_contractions`. Their left side has powers $k+\mathbf 1_i$; component contractions use the restrictions of $k$ and zero powers on new node flags. The full curve class, all ordered effective splittings, inverse-metric contraction and marking multiplicities are retained.

The [regressions](../../AxiomaticGWTest/Tautological/PsiBoundaryExpansion.lean) exercise old/new label transport, exact tail incidence, loop normalization, finite marking expansions and both geometric consumers. These results derive stable-curve ancestor equations. A terminating numerical evaluator, finite descendant seed sufficiency and the stable-map descendant--ancestor comparison still remain to be completed; see the [validation record](../../environments/low-genus-psi-validation.json).

## 8. Actual two-point operators at zero primary deformation

For the existing full numerical descendant family $U$, perfectness of the pairing determines a unique operator $S_{m+1,\beta}$ by

$$
\eta(x,S_{m+1,\beta}y)=\langle x,\tau_m(y)\rangle_{0,\beta}.
$$

The first slot is the attaching node and has power zero. [`raiseTwoPoint`](../../AxiomaticGW/Linear/TwoPointOperator.lean) constructs the operator without choosing a basis and proves that sewing it to a linear main-component contribution is application of that operator. Transport of the state space conjugates it. [`calibrationCoefficient`](../../AxiomaticGW/GW/Descendants/TwoPointCalibration.lean) adds $S_{0,0}=\mathrm{id}$, $S_{0,\beta}=0$ for $\beta\ne0$, and derives $S_{m+1,0}=0$ from the auxiliary numerical convention. The metric constant term is therefore separate from a degree-zero two-point GW value. This is the specialization $t=0$ of [Givental's convention in §5](https://arxiv.org/html/math/0108100); additional primary deformation insertions are not included.

Primary relabelling proves $\eta(x,S_{1,\beta}y)=\eta(S_{1,\beta}x,y)$. This is the first-order symmetry condition, without a proof of the higher symplectic identities. `TwoPointCalibration.IsFromDescendants` specifies the geometric paired values and the full constant-term normalization; it uniquely identifies an already stored calibration with this construction. For `StabilizationBoundaryComparison`, `TwoPointCompatible` is exactly that identification. Substituting it removes arbitrary tail-operator choices from the existing correction sum. The main boundary maps, tail weights and residual identity remain supplied; this substitution does not derive a mixed stable-map cotangent formula.

For the fixed surfaces, the virtual dimension is $\deg x+\deg y+m=1+e$, where $e=c_1(X)\cdot\beta$. Consequently $S_{p,\beta}=0$ for $p>e+2$. The earlier unstable-arity adapter computes every remaining coefficient from stable genus-zero descendants and proves uniqueness under agreement of those stable values. The geometric construction in Sections 9–10 below removes that stable-value callback for calibration.

At $p=1$ both insertions are primary, so the existing WDVV reconstruction already determines every matrix. Its dimension rule forces vanishing for $e>3$. [`FirstCalibration.lean`](../../AxiomaticGW/Surfaces/Fixtures/FirstCalibration.lean) checks the complete remaining finite sector, including zeros. The nonzero actions are:

| Curve class, when present | Nonzero images of basis states |
| --- | --- |
| $H$ | $\mathrm{pt}\mapsto1$ |
| $E_i$ | $E_i\mapsto-E_i$ |
| $H-E_i$ | $H,E_i\mapsto1$; $\mathrm{pt}\mapsto H-E_i$ |
| $H-E_1-E_2$ on the two-point blowup | $H,E_1,E_2\mapsto H-E_1-E_2$ |

All unlisted inputs and classes give zero. The ten nonzero matrices use only the original line and exceptional seeds and named geometric laws. Native GKM computes all 25 positive-class matrices with energy at most three, including fifteen zero matrices; 564 ordinary entries agree. Actual incoming ordinary entries are kernel replayed at their full classes and basis labels. Exact equivariant multiplication and ordinary specialization are checked separately in Python; the geometric localization theorem and imported CohFT classes remain open. See the [GKM workflow](../references/GKMExchange.md#first-calibration-coefficient) and [validation record](../../environments/two-point-calibration-validation.json).

## 9. Mixed comparison from primitive virtual intersection laws

[`StableMapIntersection.lean`](../../AxiomaticGW/Geometry/StableMapIntersection.lean) defines a mixed invariant by integrating the existing descendant class against an ancestor monomial. With zero ancestor powers it is the old descendant invariant; with zero descendant powers it is the old ancestor invariant. An optional raw intersection realization supplies evaluation and stable-map cotangent classes, virtual integration, stabilization pullback/pushforward, the projection formula, and agreement with the existing numerical and cohomology-valued families. These are geometric hypotheses, not a construction of moduli spaces.

[`RationalTailComparison.lean`](../../AxiomaticGW/Geometry/RationalTailComparison.lean) gives each positive-degree contracted tail its own boundary cohomology algebra, representing the fiber product over node evaluations. Pullbacks from the total, main and tail spaces identify the retained marking with tail label 1, the attaching node with tail label 0, and the main replacement node with `none`. All ancestor powers restrict to the main component, including the ancestor at the replacement node. The cotangent cycle law is paired with arbitrary ambient classes; refined diagonal splitting holds for arbitrary component classes. Neither law assumes descendant exponents or the final numerical recurrence.

Write $F_{g,\beta}(m,d;e;y,a)$ for the mixed invariant with distinguished descendant power $m$, remaining powers $d$, ancestor powers $e$, distinguished state $y$, and remaining states $a$. The derived `mixed_step` is

$$
F_{g,\beta}(m+1,d;e;y,a)
=F_{g,\beta}(m,d;e+\delta_{\mathrm{none}};y,a)
+\sum_{\beta_m+\beta_t=\beta,\ \beta_t\ne0}
F_{g,\beta_m}(0,d;e;S_{m+1,\beta_t}y,a).
$$

This is the mixed-cotangent mechanism of [Kontsevich–Manin, Theorem 1.2, equation (4)](https://arxiv.org/html/alg-geom/9708024), derived here using the existing inverse metric and actual two-point family. Stability is $2g-2+n>0$. At zero curve class the tail sum is empty. Every main tail term has strictly smaller energy, and every displayed descendant dependency has fewer stable-map powers. The finite mixed-to-ancestor reduction in Section 11 now implements this elimination; general numerical ancestor evaluation remains open.

## 10. Reconstruction of every calibration power on the fixed surfaces

For three rational markings the ancestor term vanishes by the dimension of $\overline M_{0,3}$. [`CalibrationRecursion.lean`](../../AxiomaticGW/GW/Descendants/CalibrationRecursion.lean) derives the resulting three-point descendant equation, then applies the original divisor law. Set $D=c_1(X)$, $e(\beta)=D\cdot\beta$, and $C_0(y)=D\cup y$. The primary divisor equation and classical cubic identify the positive-class primary operator as $C_\beta=e(\beta)S_{1,\beta}$. The resulting operator identity is

$$
e(\beta)S_{m+2,\beta}
=\sum_{\beta_m+\beta_t=\beta,\ \beta_t\ne0}
C_{\beta_m}S_{m+1,\beta_t}-S_{m+1,\beta}C_0,
\qquad \beta\ne0.
$$

The two products have the indicated order. The last term is the cup-action correction on the retained input. Effective positivity makes division by $e(\beta)$ valid on all three surfaces; the zero class is handled separately by the auxiliary convention.

[`Surfaces/CalibrationRecursion.lean`](../../AxiomaticGW/Surfaces/CalibrationRecursion.lean) implements this finite matrix recursion, structurally decreasing the inverse-loop power. `reconstructedCalibrationMatrix_eq` proves agreement with the actual calibration at every power and full effective class, discharging the first-coefficient input with the existing WDVV theorem and finite line/exceptional seeds. No higher calibration value or stable-descendant callback is assumed. This proves determination of the calibration sector under the named geometric inputs; it does not yet give a total evaluator for all descendants.

Native GKM agrees on the [thirty held requests](../../AxiomaticGW/Surfaces/Fixtures/HigherCalibration.lean), with all 582 incoming ordinary entries checked by Lean. For example, on the plane $S_{2,H}(H)=-1$, $S_{5,H}(1)=6\,\mathrm{pt}$, $S_{6,H}=0$, and the unit coordinate of $S_{4,2H}(\mathrm{pt})$ is $1/2$. These examples include higher descendants in classes whose first coefficient vanishes. The [replay workflow](../references/GKMExchange.md#higher-calibration-recursion) retains exact equivariant data and full classes. Geometric realization, full symplecticity, nonzero primary deformation, and imported CohFT classes remain separate obligations.

## 11. Finite ancestor expressions and complete three-point rational descendants

[`MixedComparison.lean`](../../AxiomaticGW/GW/Descendants/MixedComparison.lean) transports the distinguished-marking formula through `Equiv.optionSubtypeNe`. The new `mixed_step_at` updates only the chosen marking and relabels both cotangent families and all states together.

[`MixedAncestorReduction.lean`](../../AxiomaticGW/Surfaces/MixedAncestorReduction.lean) expands the calibration state in the existing surface basis. `transferMark` lowers the chosen descendant power along the shifted branch and clears it on each positive-tail branch. `mixedAncestorTerms` then advances through an explicit finite marking list. Both recursions are structural; no search convergence or numerical oracle is assumed. Repeated markings are harmless, and a sound partial traversal requires zero descendant powers at every unlisted marking.

The public `SurfaceQuery.ancestorTerms` traverses every marking and produces exact rational terms in `SurfaceAncestorKey`. `eval_ancestorTerms` identifies this expression with the actual descendant query in every genus, at every stable arity and effective class. Higher calibration coefficients are discharged by the preceding finite-seed theorem. `eval_mixedAncestorTerms_congr` shows that only ancestor values of the original genus and marking count are used. All full curve classes, ancestor powers and state labels remain explicit.

[`ThreePointDescendants.lean`](../../AxiomaticGW/Surfaces/ThreePointDescendants.lean) completes the numerical sector with genus zero and three markings: every positive ancestor power vanishes on the zero-dimensional curve space, and the remaining primaries are already reconstructed. `threePointValue_eq` proves the total exact evaluator equals the actual invariant for every class and all three powers on P², F₁ and Bl₂P². Its final statement assumes only the existing geometric laws and finite genus-zero seeds. For example,

$$
\langle\tau_2(\mathrm{pt}),\tau_2(\mathrm{pt}),1\rangle_{0,2H}^{\mathbb P^2}=1,
\qquad
\langle\tau_3(H),H,1\rangle_{0,H}^{\mathbb P^2}=-2.
$$

On either blowup, $\langle\tau_1(E_i),\tau_1(E_i),1\rangle_{0,2E_i}=-1$. These are conditional consequences of the stated geometric inputs, with independent native localization agreement on the [27 held requests](../../AxiomaticGW/Surfaces/Fixtures/ThreePointDescendants.lean). General ancestor evaluation, higher-genus reconstruction, geometric realization, full symplecticity, primary deformation and imported semisimple CohFT classes remain open. The [validation manifest](../../environments/mixed-ancestor-reduction-validation.json) records the exact scope.

## 12. Complete genus-zero descendants at every finite arity

[`AncestorMarkings.lean`](../../AxiomaticGW/Surfaces/AncestorMarkings.lean) sorts the existing insertion multiset without losing multiplicities or separating a state from its power. The sort has an exposed structural body for kernel replay and is proved equal to mathlib's canonical order. A finite marking equivalence sends retained base label zero to an occurrence with positive psi power.

[`GenusZeroAncestors.lean`](../../AxiomaticGW/Surfaces/GenusZeroAncestors.lean) lowers that power by one and evaluates the existing genus-zero psi-boundary expansion. The [component bounds](../../AxiomaticGW/Surfaces/GluingDegree.lean) show that each component has genus zero and at most the remaining total psi degree. Hence every recursive dependency strictly decreases the original total. `ancestorValueFuel_stable` proves independence of any sufficient fuel bound, and `ancestorValue_eq_eval` identifies the resulting exact number with the actual ancestor invariant. Terminal primary values are discharged by the original WDVV reconstruction; no extra ancestor value is an input.

[`GenusZeroDescendants.lean`](../../AxiomaticGW/Surfaces/GenusZeroDescendants.lean) evaluates the finite mixed reduction with this ancestor family. `stableValue_eq` covers arbitrary stable marking counts, effective classes and descendant powers. [`GenusZeroFullDescendants.lean`](../../AxiomaticGW/Surfaces/GenusZeroFullDescendants.lean) transports arbitrary finite marking types through the sorted occurrence frame and expands arbitrary state vectors in the existing surface basis. This constructs the callback required by the earlier anticanonical stabilization algorithm. `value_eq` covers every numerical arity, and `queryValue?_eq_checkedEval` answers exactly the original genus-zero geometric domain. Positive-degree unstable arities are included; auxiliary degree-zero unstable requests and unsupported genera return `none` at this query boundary.

The final theorems use the same finite line/exceptional seeds, WDVV geometry, original psi-forgetting/gluing compatibility and primitive virtual mixed-comparison inputs already recorded in this note. No solved numerical recurrence or infinite family of stable values is assumed. Determination follows because the computed value is independent of the supplied geometric theory. Applicability to actual moduli spaces remains conditional on those explicit inputs.

Kernel examples distinguish the degree-zero intersections with powers `(1,1,0,0,0)` and `(2,0,0,0,0)` on five rational markings, giving 2 and 1 after inserting the surface point class. Three unit psi factors on six markings give 6. At positive plane line class, the four-marked ancestor with powers `(3,0,0,0)` and states `(pt,1,1,H)` is zero, while its stable-map descendant is 1. Further native comparisons include the one-point value `⟨τ₂(H)⟩₀,H = −3` and the exceptional double-cover value `⟨τ₂(E),τ₁(E),1,1⟩₀,2E = −3/2`.

All [34 held native GKM values](../../AxiomaticGW/GKM/Fixtures/GenusZeroDescendantReplay.lean) are replayed against this evaluator, covering arities zero through two and four through six. The earlier three-marked suite remains valid. See the [validation manifest](../../environments/genus-zero-descendant-validation.json) for command outcomes and assumptions. The following extension supplies total genus-one ancestors and descendants; genus two, geometric realization, full symplecticity, primary deformation and actual semisimple CohFT import remain required.

## 13. Complete genus-one descendants at every finite arity

[`GenusOneAncestors.lean`](../../AxiomaticGW/Surfaces/GenusOneAncestors.lean) selects a positive-power occurrence and transports it to the retained label on the one-point elliptic base. It uses the original expansion with raw loop coefficient $1/24$ and the separating tails introduced by forgetting. Every component receives at most the remaining total psi degree. Rational components are evaluated by the preceding genus-zero reconstruction; elliptic components recurse with strictly smaller total degree. No new node powers, signs or graph automorphism factors are inserted.

`ancestorValueFuel_stable` proves sufficient-fuel independence. `ancestorValue_unique` proves uniqueness for the derived triangular equations once the already reconstructed rational and primary dependencies are fixed. `ancestorStep_eval` derives those equations from the original accepted genus-one psi presentation, the two geometric row-vanishing inputs and the primitive realization/gluing laws. `ancestorValue_eq_eval` then closes both terminal families with the original WDVV/Getzler theorems and finite low-genus seeds. A family of ancestor values is not an input to that final theorem.

[`GenusOneDescendants.lean`](../../AxiomaticGW/Surfaces/GenusOneDescendants.lean) composes the finite mixed reduction with this elliptic evaluator and the already reconstructed rational calibration. Sorted marking transport and the existing multilinear expansion construct stable values on arbitrary finite marking types. The anticanonical adapter covers the remaining positive-degree zero-marking requests. `value_eq` and `queryValue?_eq_checkedEval` identify the resulting numerical and geometric queries; the auxiliary degree-zero empty request and unsupported genera are rejected. Equality to this fixed executable value gives determination for every theory satisfying the same finite seeds and explicit geometric contract.

The raw loop recovers $3/24,4/24,5/24$ for the degree-zero one-point unit dilaton on the three targets. These are derived values, not additional seeds. At plane line class, the one-point hyperplane ancestor of power three vanishes, whereas its stable-map descendant is $1/8$. Further kernel-checked native comparisons give

$$
\left\langle\tau_5(\mathrm{pt})\right\rangle_{1,2H}^{\mathbb P^2}=\frac1{32},
\qquad
\left\langle\tau_2(E)\right\rangle_{1,2E}^{\mathbb F_1}=-\frac1{16}.
$$

All [41 incoming GKM claims](../../AxiomaticGW/GKM/Fixtures/GenusOneDescendantReplay.lean) are checked against the evaluator. Native localization and the Lean recurrence use different numerical implementations but share the geometric normalizations and mathematical intersection theory. Neither their agreement nor the exact Python equivariant preflight supplies an imported class-valued CohFT or a geometric localization theorem. The [validation manifest](../../environments/genus-one-descendant-validation.json) records the R6 conditional numerical gate, rejected claims, source pins and remaining R1/R3–R5/R7–R8 obligations.
