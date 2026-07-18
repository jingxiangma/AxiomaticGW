# AGENTS.md

## Role of the agent

This repository is an existing Lean 4 mathematical formalization project built on mathlib. A substantial part of the theory has already been implemented, often with AI assistance.

The agent's default role is therefore **reviewer, verifier, and maintainer**, not greenfield designer. Unless a task explicitly asks for a new development:

1. inspect the existing formalization before proposing anything new;
2. verify that it expresses the intended mathematics;
3. identify concrete defects, gaps, duplication, or fragility;
4. revise only what has a clear mathematical or engineering justification;
5. preserve sound existing architecture and public APIs whenever possible.

Existing code is evidence of an intended design, but it is not automatically the mathematical specification. Names, comments, and compiling proofs must all be checked rather than trusted.

These instructions apply to the entire repository unless a more specific `AGENTS.md` in a subdirectory overrides them.

---

## 1. Priorities

Review and revise in the following order:

1. **Mathematical correctness** — definitions and theorem statements express the intended mathematics.
2. **Logical integrity** — no placeholders, hidden substitute axioms, contradictory assumptions, or vacuous results.
3. **Coherent architecture and API** — the implementation uses suitable mathlib abstractions and supports downstream work.
4. **Proof robustness** — proofs rely on stable public APIs rather than accidental simplification, imports, or implementation details.
5. **Maintainability** — declarations are discoverable, reusable, documented, and located appropriately.
6. **Style and performance** — naming, imports, automation, simplification, and compilation behavior follow local and mathlib conventions.

Compilation is necessary, but it is not evidence by itself that the mathematics is correct or that the code is well designed.

---

## 2. Non-negotiable rules

- Do not leave `sorry`, `admit`, or equivalent placeholders in completed work.
- Do not introduce an axiom, fake instance, contradictory hypothesis, or stronger assumption merely to make a proof compile.
- Do not weaken or silently change a mathematical statement to match an existing proof.
- Do not rewrite a working development wholesale merely because another design is possible.
- Do not perform broad renaming, reformatting, import changes, or refactoring unrelated to the task.
- Do not discard, overwrite, reset, or conceal user changes.
- Do not use destructive Git commands such as `git reset --hard`, `git clean`, or forced checkout.
- Do not commit, push, rebase, or alter branch history unless explicitly requested.
- Do not claim that a command, test, or build succeeded unless it was actually run successfully.
- Do not describe a targeted review as comprehensive when files or downstream components were not checked.

---

## 3. Required review-and-revision workflow

### Step 0: Protect the working tree

Before editing:

```bash
git status --short
git diff --stat
git diff
```

Determine which modifications already exist and which belong to the current task. Preserve all unrelated work. Do not assume that an uncommitted change was produced by the current agent.

When the repository is not clean, keep the patch narrowly scoped and inspect the final diff carefully for accidental interference.

### Step 1: Recover the intended mathematics

Read, in this order where available:

1. the user's current request;
2. project design notes, README files, issue notes, and module docstrings;
3. the mathematical source or specification cited by the project;
4. relevant existing definitions, theorem statements, examples, and downstream uses.

For the part under review, determine explicitly:

- the mathematical objects involved;
- conventions, indexing, orientations, signs, and normalizations;
- necessary hypotheses and intended generality;
- the exact conclusion of each important theorem;
- how the declarations are used later in the project.

Use project-wide search to inspect every use of a declaration before changing its type or behavior:

```bash
rg -n "DeclarationName|related_term" .
```

When sources disagree, follow the explicit task and the clearest project specification. Treat the current implementation as a candidate realization, not as decisive proof of intent.

### Step 2: Establish a baseline

Before making a substantive change:

- inspect the relevant files and their imports;
- compile the directly relevant file or target;
- run a broader build when practical and appropriate;
- record pre-existing errors and warnings separately from errors introduced by the patch;
- inspect the relevant area for placeholders or temporary scaffolding.

Typical commands are:

```bash
lake env lean path/to/File.lean
lake build
rg -n '\b(sorry|admit)\b' path/to/relevant/area
```

Use the commands configured by the repository when they differ from these examples.

If the baseline already fails, first isolate the failure. Do not obscure a pre-existing failure by making unrelated changes.

### Step 3: Review before editing

Perform the following review passes.

#### A. Mathematical semantics

Check that:

- each definition matches the intended mathematical object;
- all required compatibility conditions are encoded;
- no field is redundant in a way that permits incoherent data;
- theorem statements have the correct quantifiers, hypotheses, conclusion, and direction;
- equality, equivalence, isomorphism, and definitional equality are not confused;
- finite, nonempty, commutative, projective, free, classical, or nondegeneracy assumptions are present only when justified;
- boundary cases, zero objects, empty types, low-dimensional cases, and degenerate parameters behave correctly;
- signs, factor order, variance, dualization, indexing, and composition order agree with the chosen conventions;
- examples genuinely instantiate the intended theory rather than a weaker surrogate.

Be alert to a theorem that is technically provable but vacuous because its hypotheses are inconsistent or uninhabited.

#### B. Lean representation and API

Check that:

- existing mathlib structures are reused where appropriate;
- no local declaration duplicates an existing project or mathlib concept under another name;
- data, properties, structures, propositions, and typeclasses are used for the right roles;
- typeclasses represent canonical inferable structure rather than contextual or noncanonical choices;
- bundled morphisms and equivalences are used instead of raw functions plus repeated compatibility proofs;
- coercions and instances do not create ambiguity or synthesis loops;
- the API contains the elementary lemmas needed by ordinary downstream proofs;
- users are not forced to unfold implementation details repeatedly;
- foundational files do not depend on higher-level applications;
- the current abstraction is neither artificially specialized nor gratuitously generalized.

Repeated `unfold`, `change`, coercion manipulation, or nearly identical `simpa only` blocks are evidence to look for a missing API lemma. They are not, by themselves, permission for a large redesign.

#### C. Proof quality

Check that each important proof:

- proves the theorem actually stated;
- uses stable public declarations rather than private representation details;
- does not succeed only because of an unexpectedly broad simp set or accidental import;
- does not conceal the mathematical argument inside opaque, brittle automation;
- does not duplicate a theorem already available in the project or mathlib;
- uses classical logic or noncomputability only where mathematically needed;
- has useful intermediate lemmas when the same argument recurs;
- remains understandable to a mathematician familiar with Lean.

Do not replace a correct proof solely because a shorter proof exists. Revise it when the replacement improves correctness, robustness, API use, performance, or substantial readability.

#### D. Global behavior

Review additions to global state especially carefully:

- `[simp]` lemmas;
- typeclass instances;
- coercions;
- notation;
- scoped attributes;
- namespace openings;
- exported declarations.

A local convenience is not sufficient justification for a global simp lemma or instance. Check rewrite orientation, termination, ambiguity, competing normal forms, and downstream effects.

#### E. Integration and documentation

Check that:

- names follow local and mathlib conventions;
- declarations are in the correct namespace and file;
- imports reflect actual dependencies;
- comments and docstrings describe what the code really proves;
- no documentation overstates completeness, generality, canonicity, or mathematical significance;
- representative examples or regression tests cover consequential behavior.

### Step 4: Classify findings

Classify concrete findings before revising:

- **Critical:** mathematically false or mismatched statement, unsound placeholder, contradictory model, broken build, or result not actually proved.
- **High:** foundational representation or public API defect likely to cause incorrect or unusable downstream work.
- **Medium:** brittle proof, duplicated abstraction, missing reusable lemma, problematic simp/instance behavior, or unnecessary assumption.
- **Low:** naming, documentation, file placement, local style, or minor simplification.

Address correctness and logical integrity before style. Do not spend most of a task polishing low-severity issues while a higher-severity issue remains unresolved.

Every reported issue should identify:

- the file and declaration;
- the mathematical or Lean consequence;
- evidence that the issue is real;
- the smallest reasonable correction.

### Step 5: Choose a conservative revision

The default revision strategy is:

1. preserve mathematically sound definitions and public interfaces;
2. repair the root defect rather than patching every symptom;
3. make the smallest coherent change that solves the identified problem;
4. update all affected downstream uses consistently;
5. add a helper lemma only when it expresses reusable mathematics or removes genuine recurring implementation friction;
6. avoid speculative abstractions that are not required by current or clearly planned use.

A redesign is justified only when the existing representation is mathematically wrong, internally incoherent, incompatible with necessary downstream constructions, or demonstrably responsible for pervasive fragility. When redesigning, state the reason and migration impact explicitly.

When several sound designs are possible, prefer the established project design unless another option gives a material, demonstrated advantage. Do not churn architecture based on taste.

### Step 6: Implement incrementally

While editing:

- keep changes local and logically grouped;
- compile after each meaningful change;
- search mathlib and the local project before adding declarations;
- use existing public APIs where possible;
- preserve declaration names and theorem signatures unless changing them is part of the justified fix;
- add or revise examples when they expose the behavior being corrected;
- remove temporary scratch declarations before finishing;
- do not edit unrelated code simply to make the final diff look uniform.

Scratch experiments may use broad imports and temporary examples, but finished source files should follow the repository's normal import and documentation discipline.

### Step 7: Validate the revision

At minimum:

1. compile every changed Lean file;
2. compile directly affected downstream files or targets;
3. run the full project build when feasible or expected by the task;
4. inspect all new warnings;
5. check the touched area for placeholders;
6. inspect important simplification and typeclass behavior;
7. inspect the final diff for accidental edits and whitespace errors.

Useful commands include:

```bash
lake env lean path/to/ChangedFile.lean
lake build
git diff --check
git diff --stat
git diff -- path/to/changed/files
rg -n '\b(sorry|admit)\b' path/to/changed/area
```

For key results, use small `example` blocks or a temporary scratch file to test the public API from a user's perspective. Remove disposable tests afterward; retain tests that serve as meaningful regression examples.

When axiom discipline matters, inspect the assumptions of key results, for example with `#print axioms`, and distinguish standard Lean axioms from accidental `sorryAx` or project-specific axioms.

### Step 8: Review the final patch

Before declaring completion, ask:

- Does the revised code now state and prove the intended mathematics?
- Did any theorem become weaker, stronger, or differently normalized?
- Did any public declaration change unnecessarily?
- Are all global simp lemmas, instances, coercions, and notations justified?
- Does the patch introduce a duplicate concept or dependency inversion?
- Are the comments and documentation now accurate?
- Is every changed line connected to a reported issue or necessary consequence?
- Were pre-existing failures kept distinct from new failures?

---

## 4. Special scrutiny for AI-generated formalization

Because existing code may have been generated by agents, actively check for the following recurring failure modes:

- a theorem formalizes a nearby but weaker proposition than its prose description;
- assumptions are much stronger than the mathematics requires;
- hypotheses make the theorem vacuous;
- definitions omit a compatibility axiom or include redundant independent data;
- synonymous duplicate structures or lemmas exist in different files;
- a custom construction duplicates mathlib functionality;
- a proof succeeds through an unintended simp lemma, imported theorem, or contradictory local assumption;
- typeclass instances encode noncanonical choices;
- coercions or instances work in one example but are ambiguous globally;
- an arbitrary sign, ordering, basis, orientation, or indexing convention is hidden rather than documented;
- names or comments claim an equivalence while the code proves only one implication;
- a proof uses repeated conversions because the abstraction boundary is wrong;
- broad imports conceal the true dependency structure;
- unused abstractions were added in anticipation of work that never materialized;
- examples test only compilation and not the intended mathematical behavior;
- comments confidently overstate what has actually been formalized.

Do not assume that elaborate code is necessary. Conversely, do not replace it with a short automated proof until the reason the short proof works is understood.

---

## 5. Revision policies

### 5.1 Definitions

Preserve an existing definition when it is mathematically sound and supports the required API. Revise it only with evidence of a semantic, architectural, or integration problem.

When changing a definition:

- identify all constructors, projections, instances, notation, and downstream theorems affected;
- document any changed convention;
- provide compatibility lemmas or a coherent migration when appropriate;
- avoid keeping two competing foundational definitions without a clear boundary.

### 5.2 Theorem statements

Do not silently alter a theorem statement to rescue its proof.

If a statement is wrong or misaligned with the intended mathematics:

1. explain the discrepancy;
2. correct the statement;
3. update dependent declarations;
4. record whether the new statement is stronger, weaker, or simply different;
5. verify representative downstream uses.

If the statement is correct and only the proof is defective, preserve the public statement.

### 5.3 Proofs

Prefer proofs that expose the mathematical mechanism and rely on stable APIs. A slightly longer transparent proof is often better than an opaque proof whose success depends on global automation.

Extract a helper lemma when it:

- states meaningful reusable mathematics;
- occurs more than once;
- isolates a delicate coercion, transport, or normalization step;
- materially improves proof stability.

Do not create a one-use lemma merely to disguise a fragile tactic sequence.

### 5.4 Simplification and instances

Add `[simp]` only for a canonical, terminating normalization rule. Do not add both orientations of an equivalence as global simp lemmas.

Add a typeclass instance only when the structure is mathematically canonical and inference should find it globally. Prefer explicit data for contextual choices.

After changing simp lemmas or instances, test representative downstream expressions rather than checking only that the defining file compiles.

### 5.5 Generality

Do not generalize or specialize declarations as an aesthetic exercise.

Remove an unnecessary assumption when this is supported by the proof and improves realistic reuse. Add an assumption only when it is mathematically required and explain why the earlier statement was invalid or underspecified.

Follow neighboring mathlib conventions for rings, modules, finiteness, universes, bundled maps, and typeclass parameters.

### 5.6 Imports and file organization

Do not optimize imports blindly. First determine which declarations are supplied by each import and how neighboring files are organized.

A foundational file must not import a high-level application solely to obtain a convenience lemma. Move genuinely foundational helpers to an appropriate lower-level file when justified.

Avoid moving declarations between files unless placement causes a real dependency, discoverability, or architectural problem.

### 5.7 Documentation

Update documentation whenever behavior, hypotheses, conventions, or scope changes. Documentation must describe the formal statement, not merely the informal aspiration.

Comments should explain mathematics, design constraints, or subtle Lean behavior. They should not narrate obvious tactics or preserve obsolete design discussions as if they were current facts.

---

## 6. Definition of done

A review-and-revision task is complete only when all applicable conditions hold:

- the reviewed declarations agree with the intended mathematics;
- identified correctness defects are fixed or explicitly isolated;
- all changed files compile;
- relevant downstream targets compile;
- no new `sorry`, `admit`, substitute axiom, fake instance, or artificial hypothesis was introduced;
- public APIs were preserved unless a justified correction required a change;
- new or changed simp lemmas, instances, coercions, and notation were tested for global behavior;
- the patch contains no unrelated refactor or formatting churn;
- documentation matches the revised code;
- the final diff was inspected;
- exact validation commands and outcomes are reported;
- remaining uncertainties and unreviewed scope are stated honestly.

A review that finds no necessary code change is valid when it reports what was inspected and what evidence supports that conclusion.

---

## 7. Required completion report

After each task, report concisely:

1. **Scope reviewed:** files, declarations, and mathematical claims inspected.
2. **Findings:** concrete issues, classified by severity; state explicitly when no issue was found.
3. **Revisions made:** exact definitions, theorem statements, proofs, instances, imports, or documentation changed.
4. **Mathematical effect:** whether statements or assumptions changed and why.
5. **Validation:** exact commands run and their outcomes.
6. **Remaining risks:** unresolved questions, pre-existing failures, and portions not reviewed.
7. **Next priority:** the most important mathematically justified follow-up, not a generic list of possible enhancements.

Do not provide only a changelog. The report must distinguish review evidence from implemented changes.

---

## 8. Final standard

The objective is not to maximize the amount of rewritten code. It is to increase confidence that the existing formalization is mathematically faithful, logically sound, coherent with mathlib, and safe to extend.

Prefer:

- verification before modification;
- demonstrated defects over speculative criticism;
- root-cause fixes over symptom patches;
- minimal coherent diffs over wholesale rewrites;
- stable public APIs over implementation-dependent proofs;
- accurate documentation over confident overstatement;
- explicit remaining uncertainty over unsupported claims of completeness.
