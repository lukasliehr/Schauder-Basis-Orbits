module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Module.Bases

@[expose] public section

/-!
# Schauder bases in unitary orbits

This file is the statement of record. It imports only Mathlib and contains five definitions and the theorem `MainResult`, whose proof is supplied in `Solution.lean`.

**Theorem.** A strongly continuous one-parameter group of unitary operators `U = (U t)` on a separable infinite-dimensional complex Hilbert space `H` has simple continuous spectrum if and only if there are `g ∈ H` and pairwise distinct `t n ∈ ℝ` such that `(U (t n) g)` is a Schauder basis of `H`.

A vector `v` is cyclic if the linear span of `{U t v : t ∈ ℝ}` is dense in `H`. A common eigenvector is a nonzero vector `w` such that `U t w ∈ ℂ w` for every `t`. Simple continuous spectrum means that `U` has a cyclic vector and no common eigenvector.

## Reading the formal statement

* A unitary operator is a surjective linear isometry `H ≃ₗᵢ[ℂ] H`.
* The group law is stated pointwise as `U (s + t) x = U s (U t x)`. Since every `U t` is a bijection, this gives `U 0 = 1`.
* Strong continuity is continuity of `t ↦ U t x` for every `x`.
* `SchauderBasis ℂ H` is Mathlib's classical Schauder basis indexed by `ℕ`. It consists of basis vectors, continuous coordinate functionals which are biorthogonal to them, and norm convergence of the partial sums of the expansion of every vector. The expression `b n` is the `n`-th basis vector.
* The points `t n` are indexed from `n = 0`, and `Injective t` says that they are pairwise distinct.
* Infinite dimensionality is the hypothesis `¬ FiniteDimensional ℂ H`.
-/

open Function Submodule TopologicalSpace

/-- A complex Hilbert space is a complex inner product space which is complete. -/
class abbrev ComplexHilbertSpace (H : Type*) :=
  NormedAddCommGroup H, InnerProductSpace ℂ H, CompleteSpace H

/-- A unitary operator on H is a surjective linear isometry H → H. -/
abbrev UnitaryOperator (H : Type*) [ComplexHilbertSpace H] := H ≃ₗᵢ[ℂ] H

-- Throughout, U = (U t) is a family of unitary operators on a complex Hilbert space H.
variable {H : Type*} [ComplexHilbertSpace H] (U : ℝ → UnitaryOperator H)

/-- U is a strongly continuous one-parameter group of unitary operators. -/
def IsStronglyContinuousGroup : Prop :=
  (∀ s t x, U (s + t) x = U s (U t x)) ∧ ∀ x, Continuous fun t ↦ U t x

/-- A vector v ∈ H is cyclic if the linear span of {U t v : t ∈ ℝ} is dense in H. -/
def IsCyclicVector (v : H) : Prop :=
  Dense (span ℂ {U t v | t : ℝ} : Set H)

/-- A nonzero vector w ∈ H is a common eigenvector if U t w ∈ ℂ w for every t ∈ ℝ. -/
def IsCommonEigenvector (w : H) : Prop :=
  w ≠ 0 ∧ ∀ t, U t w ∈ ℂ ∙ w

/-- Simple continuous spectrum: U has a cyclic vector and no common eigenvector. -/
def HasSimpleContinuousSpectrum : Prop :=
  (∃ v, IsCyclicVector U v) ∧ ¬ ∃ w, IsCommonEigenvector U w

/-- U has simple continuous spectrum if and only if some (U (t n) g) is a Schauder basis. -/
theorem MainResult
    [SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) (hU : IsStronglyContinuousGroup U) :
    HasSimpleContinuousSpectrum U ↔
      ∃ (g : H) (t : ℕ → ℝ), Injective t ∧ ∃ b : SchauderBasis ℂ H, ∀ n, b n = U (t n) g := by
  sorry
