import Mathlib
import LeanCode.Main

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
  exact SchauderBasisOrbits.mainResult U hH hU
