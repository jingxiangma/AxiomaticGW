# Shifted-degree BP reconstruction for the plane

**Status, 2026-10-04:** The three canonical plane genus-two families now have a terminating executable recursion, uniqueness from the original BP equations and soundness under the existing geometric inputs and three finite seeds. Every retained remainder dependency is canonical and strictly smaller in degree; the initial primary entry follows from the original source-degree-one HPP equation. The complete coefficient matrix has determinant `7776d` at positive degree. The initial constant now has kernel replay, and an exact scalar evaluator supports claim-bound finite-table certificates. The three canonical line values are now kernel-certified as zero and replay the pinned GKM requests. The remaining positive-degree benchmark replay is in progress. No new numerical seed or geometric hypothesis is added. Ten held native coefficient rows and seven admcycles comparisons supplement the coefficient proofs; those comparisons alone do not certify invariant values.

## Requests and conventions

Use the fixed plane coordinates `![d]`, of anticanonical energy `3d`, and the existing stable-map descendant families

$$
N_d=\langle\mathrm{pt}^{3d+1}\rangle_{2,d},\qquad
H_d=\langle\tau_1(H)\mathrm{pt}^{3d}\rangle_{2,d},\qquad
P_d=\langle\tau_1(\mathrm{pt})\mathrm{pt}^{3d-1}\rangle_{2,d}.
$$

Here `d` is positive. The point descendant at degree zero is not one of these requests. The source audit follows [Belorousski–Pandharipande, Sections 3.2 and 3.5](https://arxiv.org/pdf/math/9803072), which uses the four original state assignments `HHH`, `HHP`, `HPP`, and `PPP`. The coefficient extraction below uses the repository's full six-assignment raw relation, without dividing the resulting row by six.

For a BP equation at source degree `D` with three original labels of total codimension `s`, dimension requires `n = 3D + 2 - s` additional primary points. The existing input-class diagnostics missed a necessary possibility: use source degree `D = d + 1` to determine invariants at degree `d`.

## Exact coefficient matrix

For rows `HHP`, `HPP`, `PPP` at degree `d+1`, the respective added-point counts are `3d+1`, `3d`, and `3d-1`. The symbolic coefficient matrix on columns `(N_d,H_d,P_d)` is

$$
M(d)=
\begin{pmatrix}
-108d & -27d^2+27d+12 & 27d^3+9d^2\\
-36 & -36d+12 & 36d^2\\
0 & -18 & 18d
\end{pmatrix},\qquad \det M(d)=7776d.
$$

The same symbolic calculation gives zero coefficients for all three original-degree variables in those mixed-point rows. The source-degree cancellation is now proved in Lean for every requested variable, as described below. All three rows now have uniform Lean identifications with their full normalized equations. Their complete canonical support and strict decrease outside the degree-`d` block are proved. The determinant is attached to that actual coefficient matrix and gives a nonzero positive-degree pivot.

The [explorer](../../scripts/explore_genus_two_shifted.py) derives these polynomials directly; it does not fit them to finitely many degree values. For each edge-state and curve assignment, component dimension fixes the number of additional points. A vertex of genus `g`, degree `b`, and `m` original flags requires

$$
k=3b+g-1+m-\sum_j\bigl(\deg(\gamma_j)+\psi_j\bigr).
$$

The multinomial coefficient counts labelled placements. The one-psi pullback retains its negative rational-tail correction with a nonempty set of added points, including when the original psi lies at a node. In a one-degree shift the rational components have total degree one, so only the classical cubic and genus-zero line value enter these coefficients. Both are already supplied by the existing reconstruction. The original native and finite admcycles comparisons retained plane first-calibration corrections. Their vanishing after primary unit reduction is now proved for the complete Lean normalization, so the new plane evaluator can omit them using that equality theorem.

The [native payload](../../environments/genus-two-shifted-native.json) and [comparison report](../../environments/genus-two-shifted-exploration.json) check the shifted matrix at `d=1,2`, the supplementary `HHH` row at `d=1`, and three zero input-class rows at source degree two. Seven rows use actual admcycles forgetful pullbacks and incidence-based contraction in addition to the symbolic calculation. These paths share the held BP relation, plane conventions, and lower-genus initial values; they do not independently prove geometric validity.

## What Lean proves now

[`GenusTwoCoefficients.lean`](../../AxiomaticGW/Surfaces/GenusTwoCoefficients.lean) proves `coefficientEval_eq` for any requested variable and full input curve class, with arbitrary marking and cotangent powers. Positive-class complements and negative normalization tails are retained. A separate theorem proves zero coefficient when every component genus is at most one.

[`GenusTwoCoefficientRelations.lean`](../../AxiomaticGW/Surfaces/GenusTwoCoefficientRelations.lean) identifies the executable BP and complete L24 entries with their original normalized polynomials. The BP evaluator skips sixteen diagrams only after their coefficients are proved zero; it does not remove them from the full equation or its constant term. Input-class entries agree with the previous leading evaluator. The [kernel regressions](../../AxiomaticGWTest/Surfaces/GenusTwoCoefficients.lean) exercise positive rational complements, both separating orientations, nonzero calibration corrections, higher ancestor tags, and distinct equal-energy classes.

[`PointPullbackContraction.lean`](../../AxiomaticGW/Surfaces/PointPullbackContraction.lean) now proves a recursive binomial compression of the complete signed expansion for arbitrary terminal values, cotangent powers, genus and point count. Pascal's identity counts the two sides of each original separating edge. New negative tails are evaluated by the original single-component formula with one fewer additional point, even when that correction increases graph size. The proof includes node powers and retains integer signs and repeated placements.

[`GenusTwoPointCoefficients.lean`](../../AxiomaticGW/Surfaces/GenusTwoPointCoefficients.lean) applies this theorem to the actual BP and complete L24 coefficient evaluators. Genus-two components supply normalized singleton coefficients and their rational complements supply the previously reconstructed constants. Component-genus preservation justifies ignoring graphs with no genus-two component. The two `pointCoefficient_eq_full` theorems identify the results with their complete original normalized polynomials, without a new geometric or numerical hypothesis.

The [kernel fixture](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoShifted.lean) proves that the `PPP` equation at source degree two has coefficient `-18` on `H_1`. It also proves that the shifted `HPP` row has coefficient `-36` on `N_1`, by separately checking its four contributions `-12, 0, 18, -42`. These certify matrix entries, not the values of `H_1` or `N_1`. Two earlier monolithic diagnostics were interrupted. The new standalone check completed in 39.957 seconds with peak child RSS 7866630144 bytes, so substantial kernel cost remains. The separate primary-entry replay completed in 48.191 seconds with peak child RSS 6771212288 bytes. The compressed native driver reproduced all ten saved rows byte for byte in 68.925 seconds in the recorded run; the earlier uncompressed run took 131.098 seconds. These development observations are not a controlled benchmark.

## Uniform plane component normalization

[`PlaneNormalization.lean`](../../AxiomaticGW/Surfaces/PlaneNormalization.lean) proves `normalizedTerms_plane_eq_direct` for every plane ancestor key. The sparse first-calibration matrix has image in the unit direction. Every correction in the genus-at-least-two branch is therefore a primary query with a unit insertion and vanishes term by term. This is equality of the complete uncollected expression, not just its leading coefficient. The lower-genus and higher-power branches remain unchanged, and no seed or geometric assumption is added.

For primary labels with no unit, degree `d` and `h` hyperplane occurrences give coefficient `d^h`. A hyperplane descendant additionally contributes the primary correction `h * d^(h-1)`, where the exponent uses natural subtraction and the coefficient is zero when `h=0`. A point descendant has no such correction. These formulas remain valid at degree zero; in particular, the one-hyperplane correction uses `0^0=1` and is retained. Primary units and the string/dilaton branches keep their existing definitions.

The signed dimension tests are also proved uniformly: a genus-`g` primary point query needs `n+1=3d+g`, and a single first descendant of a basis label `b` needs `n+codim(b)+1=3d+g`. These tests do not turn auxiliary unstable conventions into geometric queries.

[`PlaneGenusTwoCoefficients.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoCoefficients.lean) uses the exact class support of that normalization to reject a genus-two component at a different class before reducing its insertions. Its component, signed point-contraction and BP equality theorems identify the shortcut with the complete generic evaluator. Positive rational complements and stable-curve cotangent-tail corrections are still present. The [regressions](../../AxiomaticGWTest/Surfaces/PlaneNormalization.lean) retain repeated-divisor corrections, multiple units and degree-zero terms. The [validation record](../../environments/plane-normalization-validation.json) records the implementation checks.

## Recursion over the effective remainder

[`WeightedCurveSplitting.lean`](../../AxiomaticGW/Coefficients/WeightedCurveSplitting.lean) proves the exact reindexing

$$
\sum_{\alpha+\beta=\gamma+\delta}F(\alpha,\beta)
=\sum_{\epsilon+\beta=\delta}F(\gamma+\epsilon,\beta),
$$

provided the summand vanishes unless $\gamma\leq\alpha$ coordinatewise. The second-component version retains the opposite orientation. [`GenusTwoCoefficientSupport.lean`](../../AxiomaticGW/Surfaces/GenusTwoCoefficientSupport.lean) supplies that support for complete normalized coefficients and signed point contractions on all three surfaces. Incomparable classes remain distinct even when their energies agree.

[`GenusTwoRemainder.lean`](../../AxiomaticGW/Surfaces/GenusTwoRemainder.lean) uses this identity at every separating edge. Its main-component recursion also reindexes the new rational tails created by cotangent pullback and terminates by decreasing the added-point count. `remainderPointCoefficient_eq` identifies it with the complete original signed coefficient at class $\gamma+\delta$, for arbitrary powers and marking counts. The rational components still use the existing reconstructed values and every binomial multiplicity and inverse-metric sign is retained.

For the plane, [`remainderVertex_plane_zero`](../../AxiomaticGW/Surfaces/PlaneGenusTwoRemainder.lean) proves that the terminal genus-two component consumes zero remainder. Consequently, with $\delta=H$, each surviving class assignment puts a line on exactly one rational component and degree zero on the other rational components. The two ordered edge splits are proved explicitly. The absolute-source-degree BP interface checks that the requested degree is no larger than the source before subtracting, and is proved equal to the original consumer even when that check fails. The native driver and the existing two kernel coefficient certificates now use this interface.

The [regressions](../../AxiomaticGWTest/Surfaces/GenusTwoRemainder.lean) retain both separating orientations, a degree-zero divisor correction, a nonzero signed new-tail coefficient $-3$, a nonzero blowup calibration correction $-1$, incomparable exceptional classes, unreduced higher ancestor powers and loops without genus-two components. These are coefficient tests, not new invariant values. The [validation manifest](../../environments/genus-two-remainder-validation.json) records replay and comparison evidence. The following increment closes primary placements and the one-psi component at remainder one. Full matrix identification remains open; the source-degree cancellation is supplied by the later extension below.

## Closed primary placements and the one-psi line remainder

[`PrimaryPointPullback.lean`](../../AxiomaticGW/Surfaces/PrimaryPointPullback.lean) proves that an undecorated component's signed recursion equals its terminal primary value at the key with all added points. [`GenusTwoPrimaryPoints.lean`](../../AxiomaticGW/Surfaces/GenusTwoPrimaryPoints.lean) identifies rational components with the existing reconstructed scalar formula. A stable degree-zero primary component receives no added points; a plane line contributes one exactly when there is no unit and the total number of points is two. Binomial support reduction preserves the zero result when too few new points are available, and explicitly guards against excess original points. The remainder evaluator uses this proved primary shortcut.

Write $C_n(a)$ for the requested primary main-component coefficient with $n$ added points and zero effective remainder, and $R_n(s,a)$ for the same coefficient with one psi at the original marking $s$ and effective remainder $H$. The [cotangent-tail proof](../../AxiomaticGW/Surfaces/GenusTwoPointTails.lean) establishes, for every $n$ and every requested variable,

$$
R_n(s,a)=
\begin{cases}
-\binom n2 C_{n-2}(a[s\mapsto H]),&a_s=H,\\
-n C_{n-1}(a[s\mapsto H]),&a_s=\mathrm{pt},\\
0,&a_s=1.
\end{cases}
$$

Natural subtraction at the two small-count boundaries is multiplied by a proved zero binomial or zero scalar. This is not an assumed recurrence: the proof follows the actual rational-tail label equivalences, sums its full class and inverse-metric contractions, kills the primary unit term, and inducts through the signed universal-curve pullback. It includes node psi factors. The original negative-tail regression `-3` now uses this theorem; cubic-class coefficient checks give `-108` and `-24`. These are equation coefficients, not genus-two invariant values.

The zero-remainder first-power component is closed by the following extension. Combining both cases with the four BP diagrams, proving the entire matrix and complete support, and establishing reconstruction remain open. The [validation manifest](../../environments/genus-two-primary-points-validation.json) records tests, source pins and this boundary. No seed, geometric hypothesis, application or GKM gate changes.

## Zero-remainder first-power coefficients

Let $T_n(s,a)$ be the coefficient in the original normalized terminal key with one psi at $s$ and $n$ added primary points. With $C_n$ as above, the [zero-remainder theorem](../../AxiomaticGW/Surfaces/GenusTwoZeroRemainder.lean) proves

$$
R^{(0)}_n(s,a)=T_n(s,a)-
\begin{cases}
n C_{n-1}(a[s\mapsto\mathrm{pt}]),&a_s=1,\\
0,&a_s\ne1.
\end{cases}
$$

At $n=0$ the correction vanishes, including the truncated index. A new rational tail at zero remainder has degree zero; its classical triple survives only for the two units and the new point, and it receives no additional points. The inverse metric then replaces the original unit by a point on the main component. The proof iterates the actual signed point-pullback step, retaining all original markings and the dimension check.

[`PlanePointNormalization.lean`](../../AxiomaticGW/Surfaces/PlanePointNormalization.lean) identifies $T_n$ with the existing canonical first-descendant terms using the original psi-labelled state, all other original labels with their multiplicities, and $n$ additional points. The selected occurrence agrees with that state independently of the internal insertion sort. No restriction excluding unit insertions is imposed. The generalized insertion-key lemma preserves arbitrary old cotangent powers when a labelled primary point becomes a counted point.

Twelve [regressions](../../AxiomaticGWTest/Surfaces/GenusTwoZeroRemainder.lean) check classical support, the nonzero negative correction, repeated divisors, degree zero, the no-point boundary, and the exact pairing of psi powers with labels. For a single original unit, the primary line coefficient is $6-4=2$; the corresponding cubic and degree-zero coefficient checks also give $2$. A retained cubic hyperplane gives $9$, and the repeated-hyperplane product correction gives $6$. These are coefficients, not new invariant values. The [validation record](../../environments/genus-two-zero-remainder-validation.json) records the proof and comparison evidence. The full shifted matrix and reconstruction remain unproved. The following source-degree extension closes that part of the support obligation.

## The uniform three-point row

[`PlanePointContractions.lean`](../../AxiomaticGW/Surfaces/PlanePointContractions.lean) now proves the complete `PPP` row of the displayed matrix for every positive degree. It uses the original four genus-two diagrams and all six marking permutations. Two specified rational points force a line component with a hyperplane at the node and no further points on that component. The first diagram then has a classical rational component containing a point and a hyperplane, so it vanishes. The second diagram puts three points on a rational component of degree at most one and also vanishes.

The third diagram retains psi on the original genus-two point insertion, with a primary hyperplane at the node. The fourth retains psi on the hyperplane node, with the original primary point. Their raw coefficients are respectively `3` and `-3`. Canonical normalization and the six marking assignments therefore give `(0, -18, 18d)` on `(N_d, H_d, P_d)`. `normalized_plane_three_points_row` identifies these entries with the entire normalized BP equation at degree `d+1`, rather than a selected graph surrogate.

The stronger coefficient formula holds for any requested variable and any added-point count `n` at a one-degree remainder. Its exact dimension guard is `n+1=3d`; only the point descendant with `n` primary points and the hyperplane descendant with `n+1` primary points survive. Thus the zero-degree boundary and noncanonical ancestor requests are covered. This one-degree-remainder statement does not itself prove source-degree cancellation or support at larger remainders. Source-degree cancellation is established separately below.

Nine [consumer regressions](../../AxiomaticGWTest/Surfaces/PlanePointContractions.lean) distinguish external and node psi, reject changed multiplicities and higher-power ancestors, cover degree zero, and test the quartic row and the full original cubic-variable coefficient `54`. The [combined validation record](../../environments/genus-two-zero-remainder-validation.json) separates successful targeted checks from the still-running project-wide rebuild. No milestone acceptance changes.

## Mixed rational complements and source-degree cancellation

[`PlaneMixedPointContractions.lean`](../../AxiomaticGW/Surfaces/PlaneMixedPointContractions.lean) retains the actual main marking and node maps. Write $C_m(t,\delta)$ for the main contraction with external state $a$, node state $t$, $m$ added points and remaining plane degree $\delta$. Its main graph and decorations are arbitrary. At total remainder one, the rational pair contractions are

$$
J_{HP}(n)=C_n(1,0)+nC_{n-1}(H,0),
$$

$$
J_{HH}(n)=nC_{n-1}(1,0)+\binom n2 C_{n-2}(H,0)+C_n(\mathrm{pt},1).
$$

The last term is essential: a classical two-hyperplane component has a unit on the rational side of the node, hence a point on the main side, and leaves the line remainder on the main expression. The small-count boundaries retain this term when both binomial terms vanish. Interchanging the rational external states preserves the contraction. Specializations to the second, third and fourth actual BP diagrams retain the unit psi contribution and distinguish psi at the original marking from psi at the node.

[`PlaneSourceDegree.lean`](../../AxiomaticGW/Surfaces/PlaneSourceDegree.lean) proves zero remainder coefficients in all three mixed rows for every requested variable and every added-point count. In `HPP` and `PPP`, the rational pair or quadruple vanishes classically. In `HHP`, the first two diagrams vanish, while the two single-psi diagrams can be nonzero individually. Their two equal point states give identical terminal insertion multisets and no unit correction, so their raw coefficients `3` and `-3` cancel. Every one of the six original marking occurrences is retained.

The `normalized_plane_*_source_degree` theorems identify these zeros with coefficients of the full original normalized equations. Combining them with the previously proved full-class support gives `normalized_plane_*_degree_lt`: a nonzero genus-two coefficient has degree strictly less than the equation degree $D$. For $D=d+1$, this gives degree at most $d$. Identifying all degree-$d$ variables with the three canonical columns is still required; the theorem alone is not a decreasing reconstruction step for degree $d$.

Twelve [regressions](../../AxiomaticGWTest/Surfaces/PlaneMixedPointContractions.lean) check the retained classical branch, small binomial boundaries, rational-slot symmetry, two individually nonzero source-degree `HHP` diagrams, their full-equation cancellation, higher-ancestor variables, degree zero and the strict support API. The [validation manifest](../../environments/genus-two-mixed-plane-validation.json) records all 36 new public theorem axiom checks, targeted tests, repeated offline Sage comparisons and the still-pending broader build. No new numerical value, seed or geometric assumption is supplied.

## Canonical main components and the HPP row

[`PlaneCanonicalComponents.lean`](../../AxiomaticGW/Surfaces/PlaneCanonicalComponents.lean) now proves closed primary, single-unit, single-hyperplane, repeated-hyperplane and paired-unit coefficients. The single unit psi contributes two primary copies after the signed point-tail correction. With one retained non-unit state, a primary unit gives one primary copy by string, while a unit psi gives three copies after its correction. A repeated hyperplane gives its descendant divisor factor plus one primary point correction. All these formulas retain the exact dimension guard and apply at degree zero and zero added points. [`RenamedCoefficient.lean`](../../AxiomaticGW/Coefficients/RenamedCoefficient.lean) justifies coefficient collection through addition and scalar multiplication without assuming injective renaming.

[`PlaneMixedRows.lean`](../../AxiomaticGW/Surfaces/PlaneMixedRows.lean) exposes the actual middle node of the inner BP rational component. Classical unit and two-hyperplane products and rational-slot symmetries preserve the complete gluing incidence. All four genus-two diagrams and all six marking occurrences yield the full HPP coefficient formula. If the requested variable has degree `d`, a one-degree remainder contributes only when `n=3d`, and its three coefficients are

$$
-36,\qquad 12-12n,\qquad 12nd.
$$

Thus `normalized_plane_hyperplane_two_points_row` proves `(-36, 12-36d, 36d²)` in the complete normalized BP equation of source degree `d+1`. The stronger canonical theorem covers every requested variable, including higher-ancestor tags and changed point multiplicities. Combined with source-degree cancellation, `normalized_plane_hyperplane_two_points_lower` proves that every noncanonical surviving variable has degree strictly below `d`. The HHP and coupled-system extension below completes the same support obligation for all three rows.

Thirteen [consumer examples](../../AxiomaticGWTest/Surfaces/PlaneMixedRows.lean) check renaming collisions, zero scaling, the unit and repeated-hyperplane degree-zero boundaries, both psi slots, the exact quartic row, changed requests, higher ancestors and strict degree decrease. The [validation record](../../environments/genus-two-hpp-validation.json) distinguishes targeted proof and offline exploration checks from the pending broader rebuild. These are equation coefficients; no invariant value, seed or geometric hypothesis is added.

## Complete HHP row and coefficient block

[`PlaneHyperplaneRow.lean`](../../AxiomaticGW/Surfaces/PlaneHyperplaneRow.lean) retains the actual middle node of the inner rational component. Two external points on its line place a hyperplane at the main node. The two equal point states have the same negative single-psi line tail; their raw coefficients cancel only after both contributions are retained. All four genus-two diagrams and all six marking occurrences give the HHP coefficient, with dimension guard `n=3d+1`:

$$
(24-36d-24n)N_n^* + (12n-6\binom n2)H_{n-1}^*
+6d\binom n2 P_{n-2}^*.
$$

Here the starred symbols indicate equality with the specified primary or first-descendant request, not numerical invariant values. The zero- and one-point cases are proved separately before simplifying natural subtraction. At `n=3d+1`, the row is `(-108d, -27d²+27d+12, 27d³+9d²)`; the HHP formula includes degree zero.

[`PlaneShiftedSystem.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedSystem.lean) defines `planeShiftedTerms` from the three original normalized equations and `planeShiftedMatrix` by extracting their actual canonical coefficients. `planeShiftedMatrix_eq` proves the displayed matrix at every positive degree; `planeShiftedMatrix_det` and `planeShiftedMatrix_det_ne_zero` prove its determinant and nonvanishing. `planeShiftedTerms_lower` proves that every other variable with a nonzero coefficient has degree less than `d`, including unreduced ancestor tags. The positive-degree condition is essential: PPP at degree zero does not have the displayed positive-degree row.

`planeShiftedSolve` is an executable rational formula for any supplied right-hand side. Its specification and uniqueness theorems certify the actual coefficient equations. They do not supply or assume the lower-degree invariant data. The [consumer tests](../../AxiomaticGWTest/Surfaces/PlaneShiftedSystem.lean) cover the retained inner line, nonzero signed tails, small-point boundaries, quartic row, changed requests, higher ancestors, determinant and solver. The [validation record](../../environments/genus-two-plane-system-validation.json) records the source and assumption audit and broader checks.

## Collected remainder and geometric solved step

The degree bound is a statement about **collected nonzero coefficients**. The raw graph expansion can contain cancelling current- or source-degree terms, so deleting the canonical singleton monomials from the raw expression is not sufficient for recursive evaluation.

[`CollectedTerms.lean`](../../AxiomaticGW/Coefficients/CollectedTerms.lean) merges equal monomials and removes zero totals. Its evaluation and coefficient theorems preserve the complete polynomial, including constants and nonlinear terms. Finite singleton isolation does not discard any other monomial.

[`PlaneShiftedRemainder.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedRemainder.lean) applies this operation to the actual normalized equations and then removes the three distinct canonical requests. Every variable in every retained term has genus two, satisfies the original dimension condition and has degree strictly below `d`. If `r_i(v)` denotes evaluation of this remainder, the complete equation is exactly

$$
\operatorname{eval}_v(p_i)=\bigl(M(d)x(v)\bigr)_i+r_i(v),\qquad
x(v)=(N_d(v),H_d(v),P_d(v)).
$$

The solver receives `-r(v)`, including the constant term with its correct sign. The right-hand side is unchanged by arbitrary changes to values at degree `d` or above. Two valuations satisfying the original equations and agreeing on every smaller-degree genus-two dependency therefore agree on the canonical triple.

[`PlaneShiftedStep.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedStep.lean) applies this identity to actual invariant evaluation through `eval_normalizedGenusTwoTerms_eq_zero`. It retains the source-row validity, primitive geometry and finite low-genus seed boundary. It neither assumes a solved recurrence nor introduces a genus-two value. The plane has no exceptional divisor, so the corresponding empty seed obligations are discharged internally.

Eleven [consumer regressions](../../AxiomaticGWTest/Surfaces/PlaneShiftedRemainder.lean) cover complete cancellation, repeated nonzero coefficients, raw zero terms, constants, nonlinear monomials, absent isolated variables, distinct initial queries, degree-one dependencies, right-hand-side independence, the sign and uniqueness. The following extension replaces the smaller-degree valuation callback with a closed canonical recursion.

## Canonical closure and finite-seed reconstruction

[`DecoratedTermDegree.lean`](../../AxiomaticGW/Surfaces/DecoratedTermDegree.lean) proves that a residual component's total psi power plus the original graph's edge count is at most its codimension plus the external psi powers. Signed forgetful pullbacks preserve existing edges. Each of the twenty BP diagrams has a boundary edge and codimension two, so [`BPCotangentSupport.lean`](../../AxiomaticGW/Surfaces/BPCotangentSupport.lean) bounds every residual component of a primary BP equation by one psi power, on all three fixed surfaces and at every added-marking count.

On the plane, [`PlaneCanonicalSupport.lean`](../../AxiomaticGW/Surfaces/PlaneCanonicalSupport.lean) uses the signed dimension condition and the existing primary/first-descendant normalization to identify each surviving component with one of $N_b,H_b,P_b$ at its exact original degree. This includes unit and divisor corrections and degree zero. [`PlaneShiftedClosure.lean`](../../AxiomaticGW/Surfaces/PlaneShiftedClosure.lean) consequently proves that every actual variable in the collected degree-$d$ remainder is canonical at some $b<d$. No higher-ancestor tag or other insertion pattern remains in these equations.

The positive-degree determinant theorem does not apply at zero, so the initial sector is derived separately. Define the closed lower-genus computation

$$
C=\operatorname{eval}_{v=0}(p_1^{(d=0)}),
$$

represented by `planeShiftedConstant 0 1`. [`PlaneGenusTwoInitial.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoInitial.lean) proves that its collected remainder contains no genus-two variable and that the entire source-degree-one HPP equation is

$$
\operatorname{eval}_v(p_1^{(d=0)})=-36N_0(v)+12H_0(v)+C.
$$

The existing seed $H_0=-1/960$ therefore gives $N_0=(C-1/80)/36$. The nominal $P_0$ query is dimension-incompatible and vanishes. This yields the initial triple

$$
x_0=\left((C-1/80)/36,-1/960,0\right).
$$

$C$ is computed from the complete original equation and the existing lower-genus algorithms; it is not a supplied seed or unknown-value callback. [`PlaneGenusTwoInitialValues.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoInitialValues.lean) now proves $C=1/80$ by kernel evaluation of an exactly equivalent scalar contraction. Thus the initial triple is $(0,-1/960,0)$ and $N_0=0$ is derived. The earlier whole-polynomial experiments did not supply this certificate.

[`PlaneGenusTwoRecursion.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoRecursion.lean) defines the exact recursion $x_d=M(d)^{-1}(-r_d)$ from earlier canonical triples and proves termination by degree. It proves the original full positive-degree equations and uniqueness from the initial triple and those equations. Its extension of canonical triples by zero outside their proved support is only an internal equation valuation, not an evaluator for arbitrary genus-two queries.

[`PlaneGenusTwoReconstruction.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoReconstruction.lean) derives the initial triple and positive-degree equations for actual GW evaluation, then identifies the algorithm with all three canonical families at every degree. Its numerical inputs are exactly the existing line value $1$, genus-one degree-zero hyperplane value $-1/8$, and genus-two degree-zero hyperplane value $-1/960$. Original source validity, primitive geometry and surface identification remain explicit hypotheses; no solved recurrence, new geometric law or additional seed is assumed.

Twelve [consumer examples](../../AxiomaticGWTest/Surfaces/PlaneGenusTwoRecursion.lean) cover zero-degree normalization, the canonical dependency bound, exclusion of higher ancestors, exact canonical-table extension, the initial H seed and derived triple, independence of the initial remainder, satisfaction of the original HHP equation and uniqueness. The [validation record](../../environments/genus-two-plane-reconstruction-validation.json) records all 33 public declaration axiom audits and integrated checks. It does not claim a new evaluated genus-two benchmark.

## Exact scalar replay

[`PlaneGenusTwoConstant.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoConstant.lean) evaluates the complete constant using certified lower-genus point values. The first four BP diagrams have a retained genus-two component and contribute zero to this constant. All sixteen remaining diagrams are proved undecorated. The shared primary graph evaluator therefore solves the unique dimension-compatible point distribution at each separating edge, keeping its binomial coefficient, every full-class split, node weight and marking occurrence. Total graph genus may exceed one; its low-genus interpretation requires every component to have genus at most one. The earlier genus-zero/one interfaces are preserved.

[`PlaneGenusTwoScalar.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoScalar.lean) identifies the complete remainder with its scalar constant plus the finitely many earlier canonical coefficients times their values. Zero candidate values avoid unnecessary coefficient computations. The [internal support tables](../../environments/plane-genus-two-lower-genus-support.json) certify both lower genera through degree five, including the values 87304 and 87192. These are required by the source-degree-five quartic equations; the application bound remains energy twelve. Cached evaluation falls back to the original algorithms outside the proved energy-fifteen support bound.

[`PlaneGenusTwoCertificate.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoCertificate.lean) checks every degree from zero through an independently specified bound. Its soundness theorem identifies the entire table with the original terminating recursion. `planeCheckCanonicalClaim` additionally binds the full query and claimed rational value. A computed candidate or a matching digest is insufficient: each retained scalar calculation must be kernel-checked.

The [line fixture](../../AxiomaticGW/Surfaces/Fixtures/GenusTwoPlaneLine.lean) certifies all three line queries as zero. Its complete constants are `(1/10, 1/20, 1/40)` and its coefficients on the sole nonzero earlier entry `H₀ = -1/960` are `(96, 48, 24)`. All three remainders vanish. The scalar exchange tests reject fourteen malformed inputs and an internally consistent forged equation whose changed constant is not the original BP constant. The [GKM replay](../../AxiomaticGW/GKM/Fixtures/PlaneGenusTwoLineReplay.lean) certifies the same full requests and ordinary values; localization and class-valued CohFT applicability remain separate obligations.

## Exploration and certificate generation

The [frozen twelve-query manifest](../../environments/plane-genus-two-benchmarks.json) records the published expected values from [Belorousski–Pandharipande, equation (12) and the section 3.5 table](https://arxiv.org/pdf/math/9803072v1). The quartic triple is `(27, 42, 25/4)`. These individual stable-map invariants have no factorial normalization. The reference shares BP and lower-genus mathematical inputs; its tabulation was not generated by this evaluator.

Run the Lean driver at the fixed degree-four bound, compare the held published values, then export a certificate with that bound held independently:

```bash
lake env lean --run scripts/PlaneGenusTwoScalar.lean 4 /tmp/plane-genus-two-candidates.json
python3 -B scripts/check_plane_genus_two_benchmarks.py /tmp/plane-genus-two-candidates.json
python3 -B scripts/export_plane_genus_two_scalar.py /tmp/plane-genus-two-candidates.json \
  --bound 4 --output /tmp/PlaneGenusTwoTable.lean
lake env lean /tmp/PlaneGenusTwoTable.lean
```

The driver uses Lean's interpreter. A compiled executable was profiled while eagerly initializing an unrelated L24 source relation before the first query; the interpreted path reaches the requested scalar computations without that initialization. Runtime results remain untrusted candidates. The exporter checks complete degree/query/dependency coverage and rational arithmetic, while the generated Lean source checks each complete constant and required earlier coefficient and proves the table and exact query claims. It reuses the separately checked line scalars. The complete degree-four interpreter run finished with exit zero. The [saved candidates](../../environments/genus-two-plane-scalar-native.json) match all twelve held published queries, including the quartic triple `(27,42,25/4)`. Their higher-degree kernel replay remains in progress. Three new regression methods check the full published comparison, reject a coherently altered quartic system, and preserve every obligation when exporting separate scalar modules.

[`PlaneGenusTwoClaim.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoClaim.lean) supplies the final geometric interpretation of an accepted query certificate. It composes the certificate's full-query binding with `planeCanonicalValues_from_geometry`, preserving that theorem's original geometric inputs and exactly its three seeds. Its conclusion is `query.checkedEval U = some claimed`; the degree-zero canonical requests remain geometric because genus two is stable at every marking count. This theorem compiles without adding an invariant-family or recurrence hypothesis.

The [scalar validation record](../../environments/genus-two-plane-scalar-validation.json) separates completed kernel and exchange checks from pending full-suite validation.

## Next proof obligations

1. Finish practical kernel replay of the positive-degree complete remainders, preserving their proved equality with the original equations. The initial constant is now certified.
2. Complete the fixed plane primary and first-descendant numerical suites through energy twelve, including all required zero values and independent expected-value provenance.
3. Complete arbitrary genus-two descendant reconstruction, including the higher-power few-marking suite, using the existing BP, L24 and cotangent identities without adding unknown families as seeds.
4. Establish finite-seed reconstruction and every fixed benchmark for both blowups, preserving their full effective monoids. The class-valued GKM and research-release gates remain mandatory.

The shifted equations for plane degree four use source degree five. Their lower-genus inputs can therefore exceed the energy-twelve benchmark window. The existing lower-genus algorithms apply at arbitrary classes; internal queries must not be truncated to that benchmark window.


The saved candidate file can be exported into separate scalar modules so edits to table assembly do not repeat the expensive arithmetic proofs:

```sh
python3 -B scripts/export_plane_genus_two_scalar.py environments/genus-two-plane-scalar-native.json \
  --bound 4 --output AxiomaticGW/Surfaces/Fixtures/GenusTwoPlaneTable.lean --split-scalars
```

Each generated scalar module and the assembled table require a successful Lean build before acceptance. The original monolithic export remains available. The split and monolithic paths check the same complete constants, every coefficient of a nonzero earlier value, and every full query.

The degree-two monolithic proof was intentionally stopped after its measured physical footprint reached about 20 GB on the 16 GiB host. [`PlaneGenusTwoScalarParts.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoScalarParts.lean) now proves that each complete constant is the sum of all sixteen original diagrams and six marking assignments, and each earlier coefficient is the sum of all four retained diagrams and six assignments. Every raw weight, zero entry and marking multiplicity is preserved. The source-degree guard is applied before natural subtraction. These equalities hold at arbitrary degrees, including degree zero, and introduce no numerical seed or geometric assumption.

The component candidate run completed through degree four. Its [saved report](../../environments/genus-two-plane-scalar-parts-candidates.json) has exactly the same complete constants, earlier coefficients, remainders, queries and twelve values as the original report. The additional component values remain candidates until checked by Lean. Generate component candidates, verify the saved degree-two source and replay it with:

```bash
lake env lean --run scripts/PlaneGenusTwoScalar.lean --parts 4 /tmp/plane-scalar-parts.json
python3 -B scripts/export_plane_genus_two_scalar_parts.py \
  environments/genus-two-plane-scalar-parts-candidates.json --bound 4 --degree 2 \
  --output AxiomaticGW/Surfaces/Fixtures/GenusTwoPlaneDegree2Scalars.lean --check
lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree2Scalars
```

Omit `--check` to regenerate a scalar source. For degrees three and four, change the degree and output filename together and add `--reuse-markings --proof-method fast`.

The component exporter supports degrees two through four, preserving the existing `constants` and `coefficients_*` theorem statements consumed by the table. The complete degree-two module now compiles: all 360 contributions and their assembly into the original six scalars are checked. The wrapper measured 469.604 seconds and about 4.03 GB peak resident memory; a separate in-progress physical-footprint sample was 3.1 GB. The degree-three and degree-four certificates were subsequently accepted, as recorded below. Each summand has a separate kernel proof, and the complete scalar theorem sums only the already checked rational values. The first nonzero degree-two component passed in 2.360 seconds. A real Lean regression rejects opposite changes to two components even though every complete scalar and reconstructed value stays unchanged. The three exporter tests also check the held published queries, all component counts and twenty-two malformed inputs. The [component validation record](../../environments/genus-two-plane-scalar-parts-validation.json) records the checked scope and pending numerical proofs.

The [benchmark validation record](../../environments/genus-two-plane-benchmark-validation.json) records the complete candidate comparison and geometric interpretation proof separately from the pending higher-degree kernel certificates.


## Marking reuse and direct nonprimary coefficients

The cubic and quartic scalar fixtures and the complete twelve-query canonical table now pass kernel checking. The quartic triple is `(27, 42, 25/4)`. The bounded [benchmark interface](../../AxiomaticGW/Surfaces/PlaneGenusTwoBenchmarks.lean) checks the full incoming request and supplies its accepted claim, with complete positive-class coverage through energy twelve. The optimized exporter preserves every original component statement and public scalar theorem:

```sh
python3 -B scripts/export_plane_genus_two_scalar_parts.py \
  environments/genus-two-plane-scalar-parts-candidates.json --bound 4 --degree 4 \
  --reuse-markings --proof-method fast \
  --output AxiomaticGW/Surfaces/Fixtures/GenusTwoPlaneDegree4Scalars.lean
lake build AxiomaticGW.Surfaces.Fixtures.GenusTwoPlaneDegree4Scalars
```

[`PlaneGenusTwoScalarSymmetry.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoScalarSymmetry.lean) permits arithmetic reuse only when transported states agree at every external label. All six occurrences remain in the sum. HHP and HPP each have three different state assignments; PPP has one. The cubic fixture checks 140 arithmetic representatives for its 360 component statements. The quartic fixture checks 196 for its 504 component statements.

[`PlaneGenusTwoFirstCoefficients.lean`](../../AxiomaticGW/Surfaces/PlaneGenusTwoFirstCoefficients.lean) proves that a primary main component has zero coefficient at a requested variable containing a positive descendant power. Pulling back one psi creates only primary main-component corrections, so these coefficients reduce to the normalized terminal key at zero remainder and vanish at positive remainder. This holds for arbitrary finite labels and point counts. The executable guard checks the actual requested positive power and main-component total psi at most one; all other inputs use the original evaluator. No complete coefficient is replaced by an interpolated formula or a new seed.

The fast proof method applies existing mathlib vector-selection lemmas locally during CBV for constants. Coefficient claims first rewrite to the proved optimized evaluator, then use `decide +kernel`: direct CBV still exhausted a million heartbeats on a zero nested-gluing coefficient, while kernel reduction checked the same claim. Positive controls and coherent false components test that change. The default exporter reproduces the degree-two fixture. Every generated fixture still requires successful Lean kernel replay.

The complete quartic replay took 384.405 seconds by the wrapper (415 seconds displayed by Lake), with 7,867,711,488 bytes peak resident memory. All 504 original component statements remain, including zeros. The complete table and benchmark consumer pass separately; [validation](../../environments/genus-two-plane-scalar-replay-validation.json) preserves earlier resource interruptions and failed controls. The 45 two-marked plane certificates, both blowup reconstructions and genuine semisimple CohFT interoperability remain open.
