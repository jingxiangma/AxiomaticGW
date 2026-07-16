# Local development style

This repository is currently a local research project. These conventions keep the code close to mathlib style so that future modules can follow one predictable pattern; they do not publish the repository or send anything to GitHub.

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

Use `public import` when users of the current module need declarations or instances from the imported module. Use an ordinary `import` only for a private implementation dependency. Here, `public` describes Lean re-export behavior; it has nothing to do with making the Git repository public.

## Declarations and documentation

Give every public definition, theorem, structure, class, and data-carrying structure field a `/-- ... -/` documentation comment. Explain the mathematics and any non-obvious Lean design choice, but do not narrate syntax that is already clear from the declaration.

Use `UpperCamelCase` for types and structures, `lowerCamelCase` for definitions and theorems, and established mathlib vocabulary where it exists. Names should describe the mathematical statement rather than its proof.

Prefer explicit bundled objects such as `F : CommFrobeniusAlgebra R A` when the same carrier can support more than one structure. Install derived typeclass structures only locally with `letI` unless there is a canonical global choice.

Keep lines at or below 100 characters where practical. Use Unicode notation and `fun x ↦ ...`, as configured in `lakefile.toml`.

## Proof style

Prefer a short structural proof whose intermediate steps reflect the mathematical argument. Use `rfl`, `exact`, `rw`, `calc`, extensionality, or induction when they make the reason for the result visible.

`simp` is allowed. A terminal `simp` is often the clearest final step and should not be expanded mechanically. In the middle of a proof, prefer `simp only [...]` when later steps rely on a specific normal form. Avoid an unrestricted nonterminal `simp` followed by a rigid tactic such as `rw`, because changes to the simp set can make that proof fragile.

Add `@[simp]` only when the theorem has a clear, terminating, canonical orientation. Evaluation and projection rules are typical simp lemmas. Derived corollaries that simplify to an existing canonical rule should remain named theorems without the attribute. Run the `simpNF` linter whenever a simp attribute changes.

Avoid global simp rules for symmetric equations such as commutativity or for two competing orientations of the same identity. Use named rewrites instead.

Do not add `sorry`, `admit`, or placeholder axioms to committed code. Keep tests that merely exercise the public API in `AxiomaticGWTest/`, not in the production modules.

## Before a local commit

Run all of the following from the repository root:

```bash
lake build
lake lint
lake test
git diff --check
rg -n '\b(sorry|admit)\b' AxiomaticGW AxiomaticGWTest
```

`lake lint` checks mathlib-style declaration documentation, simp normal forms, naming, and the other standard library linters. `lake test` builds the API regression tests without adding them to the public library.

Review the diff before committing. Keep commits focused on one coherent mathematical or infrastructure change. Remaining local does not prevent using Git commits: Git records local history until a remote is explicitly configured and pushed.
