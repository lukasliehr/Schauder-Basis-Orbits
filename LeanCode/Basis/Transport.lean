import LeanCode.Basis.WeightedIsometry
import LeanCode.Spectral.Realization
import Mathlib.Analysis.Normed.Module.Bases

open Filter Function MeasureTheory

namespace SchauderBasisOrbits

/-- An isometric equivalence transports a native Schauder basis in its original order. -/
noncomputable def transportSchauderBasis {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) (b : SchauderBasis ℂ E) :
    SchauderBasis ℂ F where
  basis := fun n => e (b n)
  coord := fun n => (b.coord n).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  ortho i j := by
    change b.coord i (e.symm (e (b j))) = _
    rw [e.symm_apply_apply, b.ortho]
  expansion x := by
    change HasSum (fun i => b.coord i (e.symm x) • e (b i)) x (SummationFilter.conditional ℕ)
    have h := (e.toContinuousLinearEquiv.hasSum).2 (b.expansion (e.symm x))
    simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_smul] using h

@[simp] theorem transportSchauderBasis_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F)
    (b : SchauderBasis ℂ E) (n : ℕ) :
    transportSchauderBasis e b n = e (b n) := rfl

theorem weightedL2Equiv_realCharLp (μ : Measure ℝ) [IsFiniteMeasure μ] {w : ℝ → ℝ}
    (hw : Measurable w) (hp : ∀ᵐ x ∂μ, 0 < w x) [IsFiniteMeasure (weightedMeasure μ w)] (t : ℝ) :
    weightedL2Equiv hw hp (realCharLp (weightedMeasure μ w) t) =
      realCharMul μ t (weightedL2Equiv hw hp (realCharLp (weightedMeasure μ w) 0)) := by
  have h (s : ℝ) : ⇑(realCharLp (weightedMeasure μ w) s) =ᵐ[μ] realChar s := by
    have hrep := ae_realCharLp (weightedMeasure μ w) s
    rwa [EventuallyEq, ae_weightedMeasure μ hw hp] at hrep
  apply Lp.ext
  filter_upwards [ae_weightedL2Equiv hw hp (realCharLp (weightedMeasure μ w) t),
    ae_weightedL2Equiv hw hp (realCharLp (weightedMeasure μ w) 0), h t, h 0,
    ae_realCharMul μ t (weightedL2Equiv hw hp (realCharLp (weightedMeasure μ w) 0))]
    with x ht hzero hrep ht0 hmul
  rw [ht, hmul, hzero, hrep, ht0, realChar_zero, Complex.real_smul, Complex.real_smul, mul_one, mul_comm]

/-- A weighted rational exponential basis becomes a basis in the original cyclic orbit. -/
theorem CyclicSpectralRealization.orbit_basis_of_weighted {H : Type*} [ComplexHilbertSpace H]
    {U : ℝ → UnitaryOperator H} {v : H} (R : CyclicSpectralRealization U v)
    {w : ℝ → ℝ} (hw : Measurable w) (hp : ∀ᵐ x ∂R.μ.toMeasure, 0 < w x)
    [IsFiniteMeasure (weightedMeasure R.μ.toMeasure w)]
    {t : ℕ → ℚ} (ht : Injective t)
    {b : SchauderBasis ℂ (Lp ℂ 2 (weightedMeasure R.μ.toMeasure w))}
    (hb : ∀ n, b n = realCharLp (weightedMeasure R.μ.toMeasure w) (t n : ℝ)) :
    ∃ (g : H) (s : ℕ → ℝ), Injective s ∧ ∃ b' : SchauderBasis ℂ H, ∀ n, b' n = U (s n) g := by
  let W := weightedL2Equiv hw hp
  let g := R.S (W (realCharLp (weightedMeasure R.μ.toMeasure w) 0))
  refine ⟨g, fun n => (t n : ℝ), Rat.cast_injective.comp ht,
    transportSchauderBasis (W.trans R.S) b, fun n => ?_⟩
  rw [transportSchauderBasis_apply, hb n]
  change R.S (weightedL2Equiv hw hp (realCharLp (weightedMeasure R.μ.toMeasure w) (t n : ℝ))) = _
  rw [weightedL2Equiv_realCharLp, R.intertwines]

end SchauderBasisOrbits
