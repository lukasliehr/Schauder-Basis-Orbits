module

public import Mathlib

@[expose] public section

open MeasureTheory Set

namespace SchauderBasisOrbits

private theorem triangle_section_length (T r : ℝ) :
    volume.real (Icc (max 0 (-r)) (min T (T - r))) = max 0 (T - |r|) := by
  rw [Real.volume_real_Icc, max_comm]
  by_cases hr : 0 ≤ r
  · rw [max_eq_left (neg_nonpos.mpr hr), min_eq_right (sub_le_self _ hr),
      sub_zero, abs_of_nonneg hr]
  · have hn := le_of_not_ge hr
    rw [max_eq_right (neg_nonneg.mpr hn), min_eq_left (show T ≤ T - r by linarith),
      abs_of_nonpos hn]

/-- Integrating a function of the difference on a square produces the triangular density. -/
theorem integral_square_difference (T : ℝ) {g : ℝ → ℂ}
    (hg : Continuous g) :
    (∫ s in Icc 0 T, ∫ t in Icc 0 T, g (t - s)) =
      ∫ r, (↑(max 0 (T - |r|)) : ℂ) * g r := by
  let R : Set (ℝ × ℝ) := Icc 0 T ×ˢ Icc 0 T
  let F : ℝ × ℝ → ℂ := R.indicator (fun st ↦ g (st.2 - st.1))
  let E : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.shearSubRight ℝ).symm
  let G : ℝ × ℝ → ℂ := F ∘ E
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hF : Integrable F ((volume : Measure ℝ).prod volume) := by
    apply IntegrableOn.integrable_indicator _ hR
    exact (hg.comp (continuous_snd.sub continuous_fst)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hE : MeasurePreserving E ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) :=
    measurePreserving_prod_add_right _ _
  have hG : Integrable G ((volume : Measure ℝ).prod volume) :=
    (hE.integrable_comp_emb E.measurableEmbedding).mpr hF
  calc
    _ = ∫ st, F st ∂(volume : Measure ℝ).prod volume := by
      rw [integral_prod F hF, ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with s
      by_cases hs : s ∈ Icc 0 T
      · rw [indicator_of_mem hs, ← integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [] with t
        by_cases ht : t ∈ Icc 0 T
        · simp only [indicator_of_mem ht, F, indicator_of_mem (show (s, t) ∈ R from ⟨hs, ht⟩)]
        · simp only [indicator_of_notMem ht, F, indicator_of_notMem (show (s, t) ∉ R from fun h ↦ ht h.2)]
      · rw [indicator_of_notMem hs, ← integral_zero]
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [F, indicator_of_notMem (show (s, t) ∉ R from fun h ↦ hs h.1)]
    _ = ∫ sr, G sr ∂(volume : Measure ℝ).prod volume :=
      (hE.integral_comp E.measurableEmbedding F).symm
    _ = _ := by
      rw [integral_prod_symm G hG]
      apply integral_congr_ae
      filter_upwards [] with r
      have hslice (s : ℝ) :
          G (s, r) = (Icc (max 0 (-r)) (min T (T - r))).indicator (fun _ ↦ g r) s := by
        have hiff : (s, r + s) ∈ R ↔ s ∈ Icc (max 0 (-r)) (min T (T - r)) := by
          simp only [R, mem_prod, mem_Icc, max_le_iff, le_min_iff]
          constructor
          · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
            exact ⟨⟨h₁, by linarith⟩, h₂, by linarith⟩
          · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
            exact ⟨⟨h₁, h₃⟩, by linarith, by linarith⟩
        change F (s, r + s) = _
        unfold F
        by_cases hs : s ∈ Icc (max 0 (-r)) (min T (T - r))
        · rw [indicator_of_mem hs, indicator_of_mem (hiff.mpr hs)]
          simp
        · rw [indicator_of_notMem hs, indicator_of_notMem (fun h ↦ hs (hiff.mp h))]
      simp_rw [hslice]
      rw [integral_indicator measurableSet_Icc, setIntegral_const, triangle_section_length T,
        Complex.real_smul]

end SchauderBasisOrbits
