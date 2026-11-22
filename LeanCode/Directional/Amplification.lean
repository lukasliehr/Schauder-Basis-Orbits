module

public import LeanCode.Directional.SeedParameters
public import Mathlib

@[expose] public section

open Filter
open scoped Topology

namespace SchauderBasisOrbits

noncomputable section

/-- Squared prefix bound for internal columns of a selected family. -/
def selectedPrefixSq (Ks Kv ε : ℝ) : ℝ :=
  1 + (Real.sqrt (Ks ^ 2 - 1) + Real.sqrt ((1 + 2 * ε) * Kv ^ 2 - 1)) ^ 2

theorem continuous_selectedPrefixSq (Ks Kv : ℝ) : Continuous (selectedPrefixSq Ks Kv) := by
  unfold selectedPrefixSq
  fun_prop

/-- Uniform response-to-eigenvalue estimates near the loss-zero limit. -/
theorem selected_response_estimates {ε M Φs Φe Φm t : ℝ}
    (he : 0 < ε) (he' : ε ≤ 1 / 256)
    (hM : 1 - ε ≤ M) (hM' : M ≤ 1)
    (hΦs : Real.sqrt ε < Φs) (hΦs' : Φs ≤ 1 / 4)
    (hΦe : 3 * Φs / 4 ≤ Φe) (hΦe' : Φe ≤ Φs)
    (hΦm₀ : 0 ≤ Φm) (hΦm : Φm ≤ Φs) (ht : Φm ≤ t * Φs) :
    let gain := Φe / (M - Φe)
    let leak := Φm / (M - Φm)
    0 < gain ∧ 3 * Φs / 4 ≤ gain ∧ gain ≤ 2 * Φs ∧
      leak / gain ≤ 8 * t / 3 ∧ (1 - M) / gain ≤ 4 * Real.sqrt ε / 3 := by
  let gain := Φe / (M - Φe)
  let leak := Φm / (M - Φm)
  change 0 < gain ∧ 3 * Φs / 4 ≤ gain ∧ gain ≤ 2 * Φs ∧
    leak / gain ≤ 8 * t / 3 ∧ (1 - M) / gain ≤ _
  have hs : 0 < Φs := (Real.sqrt_pos.2 he).trans hΦs
  have hf : 0 < Φe := by linarith
  have hden : 0 < M - Φe := by linarith
  have hden' : 0 < M - Φm := by linarith
  have hl : 0 < gain := div_pos hf hden
  have hL : 3 * Φs / 4 ≤ gain := by
    apply hΦe.trans ((le_div_iff₀ hden).mpr ?_)
    exact (mul_le_of_le_one_right hf.le (by linarith))
  have hu : gain ≤ 2 * Φs := by
    apply (div_le_iff₀ hden).mpr
    have htemp := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ M - Φe by linarith)
      (show 0 ≤ 2 * Φs by positivity)
    linarith
  have hT : 0 ≤ t := by
    by_contra h
    exact (not_lt_of_ge (hΦm₀.trans ht)) (mul_neg_of_neg_of_pos (lt_of_not_ge h) hs)
  have hperp : leak ≤ 2 * Φm := by
    apply (div_le_iff₀ hden').mpr
    have htemp := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ M - Φm by linarith)
      (show 0 ≤ 2 * Φm by positivity)
    linarith
  refine ⟨hl, hL, hu, (div_le_iff₀ hl).mpr ?_, (div_le_iff₀ hl).mpr ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_left hL (show 0 ≤ 8 * t / 3 by positivity)
    linarith [show 8 * t / 3 * (3 * Φs / 4) = 2 * (t * Φs) by ring]
  · have h₁ := mul_le_mul_of_nonneg_left hL (show 0 ≤ 4 * Real.sqrt ε / 3 by positivity)
    have h₂ := mul_lt_mul_of_pos_left hΦs (Real.sqrt_pos.2 he)
    nlinarith [Real.sq_sqrt he.le]

theorem one_sub_pow_le_mul {M : ℝ} (hM : 0 ≤ M) (hM' : M ≤ 1) (N : ℕ) :
    1 - M ^ N ≤ (N : ℝ) * (1 - M) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hpow : M ^ N ≤ 1 := pow_le_one₀ hM hM'
    have hmul := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hM')
    rw [Nat.cast_succ, pow_succ]
    linarith [show (1 - M ^ N) + M ^ N * (1 - M) = 1 - M ^ N * M by ring]

/-- Rounding up the number of copies keeps both gain overshoot and the
amplified leakage and mass loss quantitatively bounded. -/
theorem selected_amplification_arithmetic {σ gain leak M : ℝ}
    (hσ : 0 < σ) (hgain : 0 < gain) (hleak : 0 ≤ leak) (hM : 0 ≤ M) (hM' : M ≤ 1) :
    ∃ N : ℕ, 0 < N ∧ σ ≤ (N : ℝ) * gain ∧ (N : ℝ) * gain < σ + gain ∧
      (N : ℝ) * leak ≤ (σ + gain) * (leak / gain) ∧
      1 - M ^ N ≤ (σ + gain) * ((1 - M) / gain) := by
  let N := ⌈σ / gain⌉₊
  have h₀ : σ / gain ≤ (N : ℝ) := Nat.le_ceil _
  have h₁ : (N : ℝ) < σ / gain + 1 := Nat.ceil_lt_add_one (div_nonneg hσ.le hgain.le)
  have hN : 0 < N := by
    exact_mod_cast (div_pos hσ hgain).trans_le h₀
  have hh : σ ≤ (N : ℝ) * gain := (div_le_iff₀ hgain).mp h₀
  have hlt : (N : ℝ) * gain < σ + gain := by
    calc
      _ < (σ / gain + 1) * gain := mul_lt_mul_of_pos_right h₁ hgain
      _ = _ := by field_simp
  have hmul (a : ℝ) (ha : 0 ≤ a) : (N : ℝ) * a ≤ (σ + gain) * (a / gain) := by
    calc
      _ = (N : ℝ) * gain * (a / gain) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlt.le (div_nonneg ha hgain.le)
  exact ⟨N, hN, hh, hlt, hmul _ hleak,
    (one_sub_pow_le_mul hM hM' N).trans (hmul _ (sub_nonneg.mpr hM'))⟩

end

end SchauderBasisOrbits
