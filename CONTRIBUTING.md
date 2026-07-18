# Contributing to AxiomaticGW

Thank you for contributing. AxiomaticGW is a research-stage formalization, so clear mathematical motivation and stable API boundaries matter as much as a proof compiling today.

Contributions may include Lean definitions and proofs, regression examples, mathematical exposition, corrections, or implementation-planning work. For a substantial change, open an issue first so its scope and dependencies can be agreed before implementation. The settled choices in [`CohFTDesignDecisions.md`](notes/milestones/CohFTDesignDecisions.md) should be reopened explicitly when evidence requires a change, not altered implicitly inside an unrelated pull request.

## Development setup

Install Lean through [elan](https://github.com/leanprover/elan), then from the repository root run:

```bash
lake exe cache get
lake build
lake test
```

Use the toolchain pinned in `lean-toolchain`; do not develop against an unrecorded global Lean or mathlib checkout. Dependency updates must include the resulting `lake-manifest.json` change.

Create a focused branch, keep commits logically coherent, and describe both the mathematics and the Lean design in the pull request. Do not include local PDF copies, rendered reference pages, editor state, or generated build files.

## Source-file shape

Start each Lean source file with the copyright header, then `module`, then its imports, followed by the module docstring and namespaces.

```lean
/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Previous.Module

/-!
# Module title

Explain the mathematical purpose and the important design choices.
-/

@[expose] public section
```

Use `public import` when users of the current module need declarations or instances from the imported module. Use an ordinary `import` only for a private implementation dependency. Here, `public` describes Lean re-export behavior, not repository visibility.

## Declarations and documentation

Give every public definition, theorem, structure, class, and data-carrying structure field a `/-- ... -/` documentation comment. Explain the mathematics and any non-obvious Lean design choice, but do not narrate syntax that is already clear from the declaration.

Use `UpperCamelCase` for types and structures, `lowerCamelCase` for definitions and theorems, and established mathlib vocabulary where it exists. Names should describe the mathematical statement rather than its proof.

For domain terminology, use the standard name in the cited mathematical literature. When a Lean structure records only part of a standard object, retain the standard term only with a docstring that states which defining properties are fields, which are derived, and which are absent. Record repository-wide terminology decisions and limitations in [`TerminologyAudit.md`](notes/milestones/TerminologyAudit.md).

Prefer explicit bundled objects such as `F : CommFrobeniusAlgebra R A` when the same carrier can support more than one structure. Install derived typeclass structures only locally with `letI` unless there is a canonical global choice.

Keep lines at or below 100 characters where practical. Use Unicode notation and `fun x ↦ ...`, as configured in `lakefile.toml`.

## Proof style

Prefer a short structural proof whose intermediate steps reflect the mathematical argument. Use `rfl`, `exact`, `rw`, `calc`, extensionality, or induction when they make the reason for the result visible.

`simp` is allowed. A terminal `simp` is often the clearest final step and should not be expanded mechanically. In the middle of a proof, prefer `simp only [...]` when later steps rely on a specific normal form. Avoid an unrestricted nonterminal `simp` followed by a rigid tactic such as `rw`, because changes to the simp set can make that proof fragile.

Add `@[simp]` only when the theorem has a clear, terminating, canonical orientation. Evaluation and projection rules are typical simp lemmas. Derived corollaries that simplify to an existing canonical rule should remain named theorems without the attribute. Run the `simpNF` linter whenever a simp attribute changes.

Avoid global simp rules for symmetric equations such as commutativity or for two competing orientations of the same identity. Use named rewrites instead.

Do not add `sorry`, `admit`, or placeholder axioms to committed code. Keep tests that merely exercise the public API in `AxiomaticGWTest/`, not in the production modules.

## Documentation changes

Use `notes/mathematics/` for mathematical exposition that should remain valid independently of implementation order. Use `notes/milestones/` for status, dependencies, completion criteria, and design decisions. Update the root README only for public-facing project scope, setup, and current high-level status.

Do not hard-wrap Markdown prose. Keep each prose paragraph on one physical source line and let editors and renderers apply visual soft wrapping. Preserve structural line breaks in lists, block quotes, fenced code, displayed mathematics, and tables.

When completing a milestone, update `notes/MathematicsToLean.md` with links from the relevant mathematical-note sections to the implementing Lean modules and principal declarations. Add a dated `notes/milestones/ImplementationProgress.md` entry containing the accepted scope, verification evidence, implementation commit, and a link to the canonical map.

External references should be linked with title, author, source URL, access date, and reuse license when known. Do not commit downloaded papers unless their license clearly permits redistribution and the addition has been agreed.

## Before a pull request

Run all of the following from the repository root:

```bash
lake build
lake lint
lake test
git diff --check
rg -n '\b(sorry|admit)\b' AxiomaticGW AxiomaticGWTest
```

`lake lint` checks mathlib-style declaration documentation, simp normal forms, naming, and the other standard library linters. `lake test` builds the API regression tests without adding them to the public library.

Also review the public import `AxiomaticGW.lean` when adding a new module and add an `AxiomaticGWTest/` regression example for public behavior that should remain stable.

Pull requests should explain:

- the mathematical statement or infrastructure objective;
- the declarations and earlier milestones on which it depends;
- non-obvious representation choices;
- which verification commands were run.

All contributions are submitted under the repository's Apache-2.0 license. Participation is governed by [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md), and sensitive reports should follow [SECURITY.md](SECURITY.md).
