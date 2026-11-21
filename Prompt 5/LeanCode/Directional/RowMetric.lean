import LeanCode.Directional.RowReference

open Filter Function MeasureTheory Submodule Matrix
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)

private def liftRow {L : ℕ} (μ : Measure (RowPoint ι L)) [IsFiniteMeasure μ]
    (i : Fin (D.d + L)) : Lp ℂ 2 μ :=
  lift₂ μ (D.rawRow i) (D.measurable_rawRow i) 1 (fun z => (D.norm_rawRow i z).le)

def rowSynth {L : ℕ} (c : Fin (D.d + L) → ℂ) (p : RowPoint ι L) : ℂ :=
  synth (fun i => D.rawRow i p) c

theorem rowSynth_measurable {L : ℕ} (c : Fin (D.d + L) → ℂ) : Measurable (D.rowSynth c) := by
  change Measurable (fun p : RowPoint ι L => ∑ i, c i * D.rawRow i p)
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_const.mul (D.measurable_rawRow i))

theorem rowSynth_bound {L : ℕ} (c : Fin (D.d + L) → ℂ) (p : RowPoint ι L) :
    ‖D.rowSynth c p‖ ≤ ∑ i, ‖c i‖ := by
  unfold rowSynth synth
  calc
    _ ≤ ∑ i, ‖c i • D.rawRow i p‖ := norm_sum_le ..
    _ = _ := by simp [D.norm_rawRow]

theorem ae_synth_liftRow {L : ℕ} (μ : Measure (RowPoint ι L)) [IsFiniteMeasure μ]
    (c : Fin (D.d + L) → ℂ) :
    ⇑(synth (D.liftRow μ) c) =ᵐ[μ] D.rowSynth c := by
  classical
  unfold synth rowSynth
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • D.liftRow μ i)).trans ?_
  have h (i : Fin (D.d + L)) :
      ⇑(c i • D.liftRow μ i : Lp ℂ 2 μ) =ᵐ[μ] (fun p => c i • D.rawRow i p) :=
    (Lp.coeFn_smul _ _).trans ((ae_lift₂ μ _ _ _ _).mono
      (fun p hp => congrArg (fun z : ℂ => c i • z) hp))
  filter_upwards [(Finset.eventually_all Finset.univ).mpr (fun i _ => h i)] with p hp
  exact Finset.sum_congr rfl hp

private theorem liftRow_norm_sq {L : ℕ} (μ : Measure (RowPoint ι L)) [IsFiniteMeasure μ]
    (c : Fin (D.d + L) → ℂ) :
    ‖synth (D.liftRow μ) c‖ ^ 2 = ∫ p, ‖D.rowSynth c p‖ ^ 2 ∂μ := by
  rw [norm_sq_L2_integral]
  exact integral_congr_ae ((D.ae_synth_liftRow μ c).mono
    (fun p hp => congrArg (fun z : ℂ => ‖z‖ ^ 2) hp))

theorem rowReferenceGram_qform {L : ℕ} (c : Fin (D.d + L) → ℂ) :
    qform (D.rowReferenceGram L) c = ∫ p, ‖D.rowSynth c p‖ ^ 2 ∂ρ.prod (torusHaar (Fin L)) := by
  rw [← D.gram_rowLp, qform_gram]
  exact D.liftRow_norm_sq _ c

theorem rowSeedGram_qform_and_hermitian {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) :
    (D.rowSeedGram L hm hm').IsHermitian ∧
    ∀ c : Fin (D.d + L) → ℂ, qform (D.rowSeedGram L hm hm') c =
      ∫ p, (D.seedFiber L hm hm').weight p * ‖D.rowSynth c p‖ ^ 2 ∂ρ.prod (torusHaar (Fin L)) := by
  let W := D.seedFiber L hm hm'
  let ν := ρ.prod (torusHaar (Fin L))
  let μ := weightedMeasure ν W.weight
  let : IsFiniteMeasure μ := finite_weightedMeasure ν (Eventually.of_forall W.weight_le_one)
  have hG : Matrix.gram ℂ (D.liftRow μ) = D.rowSeedGram L hm hm' := by
    ext i j
    rw [Matrix.gram_apply, liftRow, liftRow, inner_lift₂]
    change (∫ p, conj (D.rawRow i p) * D.rawRow j p ∂weightedMeasure ν W.weight) = _
    rw [integral_weightedMeasure ν W.measurable_weight
      (Eventually.of_forall fun p => (W.weight_pos p).le)]
    rfl
  rw [← hG]
  refine ⟨Matrix.isHermitian_gram _ _, fun c => ?_⟩
  rw [qform_gram, D.liftRow_norm_sq]
  exact integral_weightedMeasure ν W.measurable_weight
    (Eventually.of_forall fun p => (W.weight_pos p).le) _

private theorem rowEnergy_integrable {L : ℕ}
    {w : RowPoint ι L → ℝ} (hw : Measurable w) (hwB : ∀ p, 0 ≤ w p ∧ w p ≤ 1)
    (c : Fin (D.d + L) → ℂ) :
    Integrable (fun p => w p * ‖D.rowSynth c p‖ ^ 2) (ρ.prod (torusHaar (Fin L))) := by
  apply Integrable.of_bound (hw.mul ((D.rowSynth_measurable c).norm.pow_const 2)).aestronglyMeasurable
    ((∑ i, ‖c i‖) ^ 2)
  refine Eventually.of_forall fun p => ?_
  change ‖w p * ‖D.rowSynth c p‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (hwB p).1 (sq_nonneg _))]
  exact (mul_le_of_le_one_left (sq_nonneg _) (hwB p).2).trans
    (pow_le_pow_left₀ (norm_nonneg _) (D.rowSynth_bound c p) 2)

theorem rowSeedGram_relative {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) :
    (m * ((1 : ℝ) / 2) ^ L) • D.rowReferenceGram L ≤ D.rowSeedGram L hm hm' ∧
      D.rowSeedGram L hm hm' ≤ D.rowReferenceGram L := by
  obtain ⟨hA, hAq⟩ := D.rowSeedGram_qform_and_hermitian hm hm'
  let U := D.seedFiber L hm hm'
  let lb := m * ((1 : ℝ) / 2) ^ L
  have hlb : 0 < lb := by dsimp [lb]; positivity
  have hL : ∀ p, lb ≤ U.weight p := fun p => seedAt_lower hm.le (D.norm_amplitude_le p.1) p.2
  have hL₁ := (hL (0, 0)).trans (U.weight_le_one _)
  have hΩ := D.rowReferenceGram_posDef L
  constructor
  · apply matrix_le_of_qform_le (hΩ.isHermitian.smul (IsSelfAdjoint.all _)) hA
    intro c
    rw [qform_smul, D.rowReferenceGram_qform, hAq]
    rw [← integral_const_mul]
    exact integral_mono
      (D.rowEnergy_integrable measurable_const (fun _ => ⟨hlb.le, hL₁⟩) c)
      (D.rowEnergy_integrable U.measurable_weight (fun p => ⟨(U.weight_pos p).le, U.weight_le_one p⟩) c)
      (fun p => mul_le_mul_of_nonneg_right (hL p) (sq_nonneg _))
  · apply matrix_le_of_qform_le hA hΩ.isHermitian
    intro c
    rw [D.rowReferenceGram_qform, hAq]
    have hi := D.rowEnergy_integrable (w := fun _ => 1) measurable_const
      (fun _ => ⟨zero_le_one, le_rfl⟩) c
    simpa only [one_mul] using integral_mono
      (D.rowEnergy_integrable U.measurable_weight (fun p => ⟨(U.weight_pos p).le, U.weight_le_one p⟩) c)
      hi (fun p => mul_le_mul_of_nonneg_right (U.weight_le_one p) (sq_nonneg _))

theorem rowSeedGram_posDef {L : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) :
    (D.rowSeedGram L hm hm').PosDef := by
  have hA := (D.rowSeedGram_qform_and_hermitian hm hm').1
  have hrel := (D.rowSeedGram_relative hm hm').1
  apply posDef_of_qform_pos hA
  intro c hc
  have h := qform_mono hrel c
  rw [qform_smul] at h
  exact (mul_pos (by positivity) (qform_pos (D.rowReferenceGram_posDef L) hc)).trans_le h

end

end SchauderBasisOrbits.DirectionalInput
