import LeanCode.Directional.SelectedMeans
import LeanCode.Directional.RowMetric
import LeanCode.Measure.Information

open Filter Function MeasureTheory Submodule Matrix
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace

namespace SchauderBasisOrbits

noncomputable section

theorem FiberWeight.mass_mul_inner_lift₂_pullback {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν] (W : FiberWeight X ν) (ρ : Measure X) [IsFiniteMeasure ρ]
    {u : X × Y → ℂ} (hu : Measurable u) {B : ℝ} (hB : ∀ p, ‖u p‖ ≤ B) (f : Lp ℂ 2 ρ) :
    (W.mass : ℂ) * ⟪lift₂ (W.normalizedMeasure ρ) u hu B hB, W.pullback ρ f⟫_ℂ =
      ∫ x, conj ((W.mass : ℂ) * W.mean u x) * f x ∂ρ := by
  let g := lift₂ ρ (W.mean u) (W.measurable_mean hu) B (W.norm_mean_le hu hB)
  have h : ⟪lift₂ (W.normalizedMeasure ρ) u hu B hB, W.pullback ρ f⟫_ℂ = ⟪g, f⟫_ℂ := by
    rw [← inner_conj_symm, W.inner_pullback_lift₂ ρ f hu hB, inner_conj_symm]
  rw [h, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_lift₂ ρ (W.mean u) (W.measurable_mean hu) B (W.norm_mean_le hu hB)] with x hx
  rw [RCLike.inner_apply', show g x = W.mean u x from hx, map_mul, Complex.conj_ofReal]
  ring

namespace DirectionalInput

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)

def selectedColumnLp {L r n : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
    (S : Scalar.Data r n) (k : Fin n) (i : Fin (D.d + L)) :=
  D.selectedLp hm hm' S (k.succ, i)

private theorem gram_rowReference_phase_base {L : ℕ} (i : Fin L) (j : Fin D.d) :
    D.rowReferenceGram L (Fin.natAdd D.d i) (Fin.castAdd L j) = 0 := by
  have H := (D.gram_rowLp (L := L)) ▸ Matrix.isHermitian_gram ℂ (D.rowLp (L := L))
  rw [← H.apply (Fin.natAdd D.d i) (Fin.castAdd L j), D.rowReferenceGram_base_phase, star_zero]

set_option maxHeartbeats 1000000 in
/-- A selected scalar column pairs with every old basis vector through the
difference between the reference and seed row Grams. -/
theorem selected_pair_old {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n) (k : Fin n)
    (i : Fin (D.d + L)) (j : Fin D.d) :
    let W := (D.seedFiber L hm hm').selected S
    (W.mass : ℂ) * ⟪D.selectedColumnLp hm hm' S k i,
      W.pullback ρ (productFamily ρ D.frequencies j)⟫_ℂ =
      (S.meanColumn k : ℂ) *
      (D.rowReferenceGram L - D.rowSeedGram L hm hm') i (Fin.castAdd L j) := by
  let W := (D.seedFiber L hm hm').selected S
  change (W.mass : ℂ) * ⟪D.selectedColumnLp hm hm' S k i,
    W.pullback ρ (productFamily ρ D.frequencies j)⟫_ℂ = _
  rw [selectedColumnLp, selectedLp, W.mass_mul_inner_lift₂_pullback ρ
    (D.measurable_rawSelected S (k.succ, i)) (fun p => (D.norm_rawSelected S (k.succ, i) p).le)]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have h (x : Base ι) : (W.mass : ℂ) * W.mean
        (D.rawSelected S (k.succ, Fin.castAdd L i)) x =
        (1 - (m : ℂ)) * (S.meanColumn k : ℂ) * mixedChar (D.frequencies i) x :=
      D.selected_mean_base hm hm' S k i x
    simp_rw [h]
    simp only [Matrix.sub_apply, D.rowReferenceGram_base_base, D.rowSeedGram_base_base hm hm']
    let u := productFamily ρ D.frequencies i
    let v := productFamily ρ D.frequencies j
    have hAE := ae_lift₂ ρ (mixedChar (D.frequencies i)) (continuous_mixedChar _).measurable 1
      (fun x => (norm_mixedChar _ x).le)
    calc
      _ = ((1 - (m : ℂ)) * (S.meanColumn k : ℂ)) * ⟪u, v⟫_ℂ := by
        rw [L2.inner_def, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hAE] with x hx
        rw [RCLike.inner_apply', show u x = mixedChar (D.frequencies i) x from hx,
          map_mul, map_mul, map_sub, map_one, Complex.conj_ofReal, Complex.conj_ofReal]
        change _ = _ * (_ * productFamily ρ D.frequencies j x)
        ring
      _ = _ := by ring
  · have h (x : Base ι) : (W.mass : ℂ) * W.mean
        (D.rawSelected S (k.succ, Fin.natAdd D.d i)) x =
        -(m : ℂ) * (S.meanColumn k : ℂ) * D.amplitude x :=
      D.selected_mean_phase hm hm' S k i x
    simp_rw [h]
    have H := (D.rowSeedGram_qform_and_hermitian hm hm').1
    have hA : D.rowSeedGram L hm hm' (Fin.natAdd D.d i) (Fin.castAdd L j) =
        (m : ℂ) * ((D.seedScale : ℂ) *
          ⟪synth (productFamily ρ D.frequencies) D.coeff, productFamily ρ D.frequencies j⟫_ℂ) := by
      rw [← H.apply (Fin.natAdd D.d i) (Fin.castAdd L j), D.rowSeedGram_base_phase hm hm']
      simp only [RCLike.star_def, map_mul, Complex.conj_ofReal, inner_conj_symm]
    simp only [Matrix.sub_apply, D.gram_rowReference_phase_base, hA, zero_sub]
    let e := synth (productFamily ρ D.frequencies) D.coeff
    let v := productFamily ρ D.frequencies j
    calc
      _ = (-(m : ℂ) * (S.meanColumn k : ℂ) * (D.seedScale : ℂ)) * ⟪e, v⟫_ℂ := by
        rw [L2.inner_def, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [D.ae_direction] with x hx
        rw [RCLike.inner_apply', show e x = D.direction x from hx, DirectionalInput.amplitude]
        simp only [map_mul, map_neg, Complex.conj_ofReal]
        ring
      _ = _ := by ring

theorem selected_pair_old_synth {L r n : ℕ} {m : ℝ} (hm : 0 < m)
    (hm' : m ≤ ((1 : ℝ) / 2) ^ L) (S : Scalar.Data r n) (k : Fin n)
    (i : Fin (D.d + L)) (a : Fin D.d → ℂ) :
    let W := (D.seedFiber L hm hm').selected S
    (W.mass : ℂ) * ⟪D.selectedColumnLp hm hm' S k i,
      W.pullback ρ (synth (productFamily ρ D.frequencies) a)⟫_ℂ =
      (S.meanColumn k : ℂ) *
      ((D.rowReferenceGram L - D.rowSeedGram L hm hm') *ᵥ Fin.append a (0 : Fin L → ℂ)) i := by
  let W := (D.seedFiber L hm hm').selected S
  change (W.mass : ℂ) * ⟪D.selectedColumnLp hm hm' S k i,
    W.pullback ρ (synth (productFamily ρ D.frequencies) a)⟫_ℂ = _
  rw [synth, map_sum, inner_sum, Finset.mul_sum, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  simp only [map_smul, inner_smul_right, Fin.append_left, Fin.append_right, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, D.selected_pair_old hm hm']
  ring

end DirectionalInput

end

end SchauderBasisOrbits
