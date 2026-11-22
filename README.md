# Schauder bases in unitary orbits

This repository accompanies the paper [A Beginner’s Guide on How to Autoformalize Mathematics in Lean](https://functionalanalysismadrid.com/lean_guide.pdf) by Lukas Liehr, David Muñoz-Lahoz, and Mitchell A. Taylor. The result being formalized in this repository is the following:

**Theorem.** A strongly continuous one-parameter group of unitary operators on a separable infinite-dimensional complex Hilbert space has simple continuous spectrum if and only if there are $g \in H$ and pairwise distinct $t_n \in \mathbb R$ such that $(U_{t_n}g)_n$ is a Schauder basis of $H$.

Here a vector $v$ is cyclic if the linear span of $\{U_t v : t \in \mathbb R\}$ is dense in $H$, a common eigenvector is a nonzero vector $w$ with $U_t w \in \mathbb C w$ for every $t$, and simple continuous spectrum means that $U$ has a cyclic vector and no common eigenvector.

`MainResult` is the Lean formulation of the main theorem in [paper.tex](paper.tex). The following declaration is from [Solution.lean](Solution.lean).

```lean
variable {H : Type*} [ComplexHilbertSpace H] (U : ℝ → UnitaryOperator H)

theorem MainResult
    [SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) (hU : IsStronglyContinuousGroup U) :
    HasSimpleContinuousSpectrum U ↔
      ∃ (g : H) (t : ℕ → ℝ), Injective t ∧ ∃ b : SchauderBasis ℂ H, ∀ n, b n = U (t n) g := by
  exact SchauderBasisOrbits.mainResult U hH hU
```

`MainResult` compiles. `#print axioms MainResult` reports exactly `propext`, `Classical.choice`, and `Quot.sound`, Lean’s three standard axioms.

## The branch `palomar`

This branch is the version of the project for the [Palomar registry](https://palomar-registry.org/). The branch `main` contains the project as it was produced.

- `Challenge.lean` states the theorem as `MainResult`, together with the five definitions it uses. It imports only three Mathlib modules and its proof is `sorry`. This is the statement to audit.
- `Solution.lean` repeats the same definitions and statement and proves `MainResult` from the library theorem `SchauderBasisOrbits.mainResult`. It is the file `Showcase.lean` of the branch `main`.
- `LeanCode/` is the proof library.
- `comparator.json` tells Comparator to compare `MainResult` in the two files and permits the axioms `propext`, `Quot.sound` and `Classical.choice`.
- `formalization.yaml` records sources, authorship, automation and review.

Palomar requires every Lean file of a repository to use Lean's module system. On this branch all Lean files, including those in the `Prompt X` folders, are therefore ported. The port adds the module header to each file, makes 34 private declarations public and writes out two inferred arguments. No statement was changed.

This branch uses Lean v4.36.0-rc2 with the last Mathlib revision for that toolchain. The branch `main` and the `Prompt 5` snapshot use Lean v4.36.0 with a Mathlib revision which is two days newer. The reason is that Palomar renders the Challenge by building its imports, and this does not yet work for Lean v4.36.0. For the same reason `Challenge.lean` imports three Mathlib modules instead of all of Mathlib. Three declarations in `LeanCode/` are adapted to the older Mathlib revision, in `Fourier/Graph.lean`, `Finite/Tuples.lean` and `Spectral/Realization.lean`. Two of them use the earlier name of a Mathlib declaration and one proves a norm identity directly which Mathlib did not contain yet. No theorem statement was changed.

## Source and scope

Both implications of the theorem are proved. The proof relies on Mathlib and on no other dependency, and it contains no `sorry` and no additional axiom. The differences in convention between the manuscript and the Lean statement are listed under `fidelity` in `formalization.yaml` and in the module documentation of `Challenge.lean`.

## Production

The formalization was produced by the workflow described in the paper above. Each `Prompt X` folder is a snapshot of the project after prompt X. `PROMPT.md` records the instructions and `RESULT.md` describes the outcome. The statement in `Challenge.lean` was fixed before any proof was written. The `Showcase.lean` files in the folders `Prompt 1` to `Prompt 4` are this statement before its proof and therefore end in `sorry`.

## Building

```
lake exe cache get
lake build
```

## Licence

This branch is released under the Apache License 2.0, see [LICENSE](LICENSE).
