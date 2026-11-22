module

public import LeanCode.Construction.LineFamilies

@[expose] public section

open MeasureTheory Set Submodule
open scoped InnerProductSpace ComplexOrder MatrixOrder

noncomputable section

namespace SchauderBasisOrbits

/-- The old frequencies followed by the requested frequency, with the old order retained. -/
def residualFrequencies (A : List ℚ) (q : ℚ) : Fin (A.length + 1) → ℚ :=
  Fin.snoc A.get q

theorem residualFrequencies_injective {A : List ℚ} (hA : A.Nodup) {q : ℚ} (hq : q ∉ A) :
    Function.Injective (residualFrequencies A q) := by
  apply Fin.snoc_injective_of_injective (fun _ _ h ↦ hA.get_inj_iff.mp h)
  rintro ⟨i, hi⟩
  exact hq (hi ▸ A.get_mem i)

variable (ρ : Measure ℝ) [IsFiniteMeasure ρ]

def residualAugmentedFamily (A : List ℚ) (q : ℚ) : Fin (A.length + 1) → Lp ℂ 2 ρ :=
  fun i ↦ realCharLp ρ ((residualFrequencies A q i : ℚ) : ℝ)

theorem residualAugmentedFamily_independent [NullSingletonClass ρ] (hρ : ρ ≠ 0)
    {A : List ℚ} (hA : A.Nodup) {q : ℚ} (hq : q ∉ A) :
    LinearIndependent ℂ (residualAugmentedFamily ρ A q) :=
  linearIndependent_realCharLp hρ (Rat.cast_injective.comp (residualFrequencies_injective hA hq))

def rationalOldSpan (A : List ℚ) : Submodule ℂ (Lp ℂ 2 ρ) :=
  span ℂ (Set.range (realFamily ρ A))

instance rationalOldSpan_finite (A : List ℚ) : FiniteDimensional ℂ (rationalOldSpan ρ A) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range _)

def rationalResidual (A : List ℚ) (q : ℚ) : Lp ℂ 2 ρ :=
  realCharLp ρ q - (rationalOldSpan ρ A).starProjection (realCharLp ρ q)

theorem rationalResidual_mem_orthogonal (A : List ℚ) (q : ℚ) :
    rationalResidual ρ A q ∈ (rationalOldSpan ρ A)ᗮ :=
  (rationalOldSpan ρ A).sub_starProjection_mem_orthogonal (realCharLp ρ q)

theorem rationalResidual_ne_zero [NullSingletonClass ρ] (hρ : ρ ≠ 0)
    {A : List ℚ} (hA : A.Nodup) {q : ℚ} (hq : q ∉ A) : rationalResidual ρ A q ≠ 0 := by
  let φ := residualAugmentedFamily ρ A q
  have hS : Set.range (realFamily ρ A) = φ '' Set.range (Fin.castSucc : Fin A.length → Fin (A.length + 1)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, ⟨i, rfl⟩, by simp [φ, residualAugmentedFamily, residualFrequencies, realFamily]⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [φ, residualAugmentedFamily, residualFrequencies, realFamily]⟩
  have hnot := (residualAugmentedFamily_independent ρ hρ hA hq).notMem_span_image
    (s := Set.range (Fin.castSucc : Fin A.length → Fin (A.length + 1))) (x := Fin.last A.length)
    (by simp)
  have hqSpan : realCharLp ρ (q : ℝ) ∉ rationalOldSpan ρ A := by
    unfold rationalOldSpan
    rw [hS]
    simpa [φ, residualAugmentedFamily, residualFrequencies] using hnot
  intro hr
  unfold rationalResidual at hr
  rw [sub_eq_zero] at hr
  exact hqSpan (hr ▸ (rationalOldSpan ρ A).starProjection_apply_mem (realCharLp ρ q))

/-- Coefficients of the rational target residual in the augmented family. -/
structure RationalResidualData (A : List ℚ) (q : ℚ) where
  coefficient : Fin (A.length + 1) → ℂ
  last_one : coefficient (Fin.last A.length) = 1
  synth_eq : synth (residualAugmentedFamily ρ A q) coefficient = rationalResidual ρ A q

theorem exists_rationalResidualData (A : List ℚ) (q : ℚ) :
    Nonempty (RationalResidualData ρ A q) := by
  let f := realCharLp ρ (q : ℝ)
  let S := rationalOldSpan ρ A
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℂ).mp (S.starProjection_apply_mem f)
  refine ⟨⟨Fin.snoc (fun i ↦ -c i) 1, Fin.snoc_last .., ?_⟩⟩
  unfold synth
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, residualAugmentedFamily, residualFrequencies,
    neg_smul, Finset.sum_neg_distrib, one_smul]
  change -(∑ i, c i • realFamily ρ A i) + f = f - S.starProjection f
  rw [hc, sub_eq_neg_add]

namespace RationalResidualData

variable {ρ} {A : List ℚ} {q : ℚ} (D : RationalResidualData ρ A q)

def raw (x : ℝ) : ℂ :=
  ∑ i, D.coefficient i • realChar ((residualFrequencies A q i : ℚ) : ℝ) x

theorem continuous_raw : Continuous D.raw := by
  unfold raw
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (continuous_realChar _)

theorem norm_raw_le (x : ℝ) : ‖D.raw x‖ ≤ ∑ i, ‖D.coefficient i‖ := by
  unfold raw
  calc
    _ ≤ ∑ i, ‖D.coefficient i • realChar ((residualFrequencies A q i : ℚ) : ℝ) x‖ := norm_sum_le ..
    _ = _ := by simp

theorem ae_raw : ⇑(rationalResidual ρ A q) =ᵐ[ρ] D.raw := by
  classical
  rw [← D.synth_eq]
  unfold synth raw
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
      D.coefficient i • residualAugmentedFamily ρ A q i)).trans ?_
  have h (i : Fin (A.length + 1)) :
      ⇑(D.coefficient i • residualAugmentedFamily ρ A q i : Lp ℂ 2 ρ) =ᵐ[ρ]
        fun x ↦ D.coefficient i • realChar ((residualFrequencies A q i : ℚ) : ℝ) x :=
    (Lp.coeFn_smul _ _).trans ((ae_realCharLp ρ _).mono fun x hx ↦
      congrArg (fun v : ℂ ↦ D.coefficient i • v) hx)
  filter_upwards [(Finset.eventually_all Finset.univ).mpr (fun i _ ↦ h i)] with x hx
  exact Finset.sum_congr rfl hx

def coefficientEnergy : ℝ := ∑ i, ‖D.coefficient i‖ ^ 2

theorem coefficientEnergy_ge_one : 1 ≤ D.coefficientEnergy := by
  have h := Finset.single_le_sum (f := fun i ↦ ‖D.coefficient i‖ ^ 2)
    (fun i _ ↦ sq_nonneg _) (Finset.mem_univ (Fin.last A.length))
  simpa [D.last_one, coefficientEnergy] using h

end RationalResidualData

section CopyParameters

variable {d z energy : ℝ}

def residualCopyParameter (d z energy : ℝ) : ℝ :=
  d / Real.sqrt (d ^ 2 + z⁻¹ * energy)

def residualCopyCount (α : ℝ) : ℕ := ⌈(α ^ 2)⁻¹⌉₊

theorem residualCopyParameter_bounds (hd : 0 < d) (hz : 0 < z) (he : 0 < energy) :
    0 < residualCopyParameter d z energy ∧ residualCopyParameter d z energy < 1 := by
  have hh : 0 < z⁻¹ * energy := mul_pos (inv_pos.mpr hz) he
  have hs : 0 < Real.sqrt (d ^ 2 + z⁻¹ * energy) :=
    Real.sqrt_pos_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg d) hh)
  refine ⟨div_pos hd hs, ?_⟩
  unfold residualCopyParameter
  rw [div_lt_one hs]
  exact (Real.lt_sqrt hd.le).mpr (lt_add_of_pos_right _ hh)

theorem residualCopyCount_bounds {α : ℝ} (ha : 0 < α) :
    0 < residualCopyCount α ∧
      1 ≤ (residualCopyCount α : ℝ) * α ^ 2 ∧
      ((residualCopyCount α : ℝ) - 1) * α ^ 2 < 1 := by
  have hs : 0 < α ^ 2 := sq_pos_of_pos ha
  refine ⟨Nat.ceil_pos.mpr (inv_pos.mpr hs), ?_, ?_⟩
  · rw [← div_le_iff₀ hs, one_div]
    exact Nat.le_ceil _
  · rw [← lt_div_iff₀ hs, one_div, sub_lt_iff_lt_add]
    exact Nat.ceil_lt_add_one (inv_nonneg.mpr hs.le)

end CopyParameters

end SchauderBasisOrbits
