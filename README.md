# Schauder bases in unitary orbits

**Theorem.** A strongly continuous one-parameter group of unitary operators on a separable infinite-dimensional complex Hilbert space has simple continuous spectrum if and only if there are $g \in H$ and pairwise distinct $t_n \in \mathbb R$ such that $(U_{t_n}g)_n$ is a Schauder basis of $H$. Simple continuous spectrum means that $U$ has a cyclic vector and has no nonzero common eigenvector.

`MainResult` is the Lean formulation of the main theorem in [paper.tex](paper.tex). The following declaration is from [Showcase.lean](Showcase.lean).

```lean
variable {H : Type*} [ComplexHilbertSpace H] (U : ℝ → UnitaryOperator H)

theorem MainResult
    [SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) (hU : IsStronglyContinuousGroup U) :
    HasSimpleContinuousSpectrum U ↔
      ∃ (g : H) (t : ℕ → ℝ), Injective t ∧ ∃ b : SchauderBasis ℂ H, ∀ n, b n = U (t n) g := by
  exact SchauderBasisOrbits.mainResult U hH hU
```

Each `Prompt X` folder is a snapshot of the project after prompt X. `PROMPT.md` records the instructions and `RESULT.md` describes the outcome.

`MainResult` compiles. `#print axioms MainResult` reports exactly `propext`, `Classical.choice`, and `Quot.sound`, Lean’s three standard axioms.
