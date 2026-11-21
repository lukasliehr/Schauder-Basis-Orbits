import LeanCode.Directional.SeedChoice

namespace SchauderBasisOrbits.PacketAndSeed

noncomputable section

variable {δ z θ : ℝ} (A : PacketAndSeed δ z θ)

def selectedMass : ℝ := 1 - (1 - A.m) * A.packet.data.toData.loss

def responseStar : ℝ :=
  A.packet.data.toData.response (A.m * seedSmallEigenvalue θ (A.L : ℝ))

def responseMean : ℝ :=
  seedDirectionFraction θ (A.L : ℝ) * A.responseStar +
    (1 - seedDirectionFraction θ (A.L : ℝ)) *
      A.packet.data.toData.response (A.m * seedLargeEigenvalue θ (A.L : ℝ))

def responsePerp : ℝ := A.packet.data.toData.response A.m

def gain : ℝ := A.responseMean / (A.selectedMass - A.responseMean)

def leak : ℝ := A.responsePerp / (A.selectedMass - A.responsePerp)

structure SelectedBounds : Prop where
  mass_pos : 0 < A.selectedMass
  gain_pos : 0 < A.gain
  leak_nonneg : 0 ≤ A.leak
  gain_le : A.gain ≤ 2 * A.packet.data.toData.loss ^ (1 / 4 : ℝ)
  leak_ratio_le : A.leak / A.gain ≤ 8 * seedRatio θ (A.L : ℝ) ^ (-(1 / 16 : ℝ)) / 3
  mass_loss_ratio_le : (1 - A.selectedMass) / A.gain ≤ 4 * Real.sqrt A.packet.data.toData.loss / 3
  perp_ne_one : A.responsePerp / A.selectedMass ≠ 1
  mean_ne_one : A.responseMean / A.selectedMass ≠ 1

private lemma succ_le_two_pow (L : ℕ) : L + 1 ≤ 2 ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [pow_succ]
    omega

lemma selectedMass_lower : 1 - A.packet.data.toData.loss ≤ A.selectedMass := by
  unfold selectedMass
  exact sub_le_sub_left
    (mul_le_of_le_one_left A.packet.loss_pos.le (by linarith [A.m_pos])) 1

private lemma fourth_root_one_div_256 : ((1 / 256 : ℝ) ^ (1 / 4 : ℝ)) = 1 / 4 := by
  have h := Real.pow_rpow_inv_natCast (x := (1 / 4 : ℝ)) (n := 4)
    (by norm_num) (by decide)
  norm_num at h ⊢

/-- The gain and leakage of a selected packet, with its normalized response
denominators and the uniform bounds needed by amplification. -/
theorem selectedBounds (hθ : 0 < θ) (hθ' : θ < 1)
    (hε : A.packet.data.toData.loss ≤ 1 / 256) : SelectedBounds A := by
  let e := A.packet.data.toData.loss
  let Φ := A.packet.data.toData.response
  let γ := seedSmallEigenvalue θ (A.L : ℝ)
  let Γ := seedLargeEigenvalue θ (A.L : ℝ)
  let p := seedDirectionFraction θ (A.L : ℝ)
  have hL : 1 ≤ (A.L : ℝ) := by exact_mod_cast A.L_pos
  obtain ⟨hγ, hγ₁, hΓ⟩ := seed_eigenvalues_order hθ hθ' hL
  change 0 < γ at hγ
  change γ < 1 at hγ₁
  change 1 < Γ at hΓ
  have hΓ₀ : 0 < Γ := zero_lt_one.trans hΓ
  have htrace : γ + Γ = seedTrace θ (A.L : ℝ) := seed_eigenvalues_sum _ _
  have htrace' : seedTrace θ (A.L : ℝ) ≤ (A.L : ℝ) + 1 := by
    unfold seedTrace
    nlinarith only [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hθ'.le)]
  have hp : 0 ≤ p ∧ p ≤ 1 := seed_fraction_bounds hθ hθ' hL
  have hΓpow : Γ ≤ (2 : ℝ) ^ A.L := by
    have hcast : ((A.L : ℝ) + 1) ≤ (2 : ℝ) ^ A.L := by
      exact_mod_cast succ_le_two_pow A.L
    linarith only [hγ, htrace, htrace', hcast]
  have hmΓ : A.m * Γ ≤ 1 := by
    calc
      _ ≤ A.m * (2 : ℝ) ^ A.L := mul_le_mul_of_nonneg_left hΓpow A.m_pos.le
      _ ≤ ((1 : ℝ) / 2) ^ A.L * (2 : ℝ) ^ A.L :=
        mul_le_mul_of_nonneg_right A.m_le (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hm_le_Γ : A.m ≤ A.m * Γ := by
    nlinarith only [mul_nonneg A.m_pos.le (sub_nonneg.mpr hΓ.le)]
  have hm₁ : A.m ≤ 1 := hm_le_Γ.trans hmΓ
  have hmγ : A.m * γ ≤ A.m := mul_le_of_le_one_right A.m_pos.le hγ₁.le
  have hmγ₀ : 0 ≤ A.m * γ := mul_nonneg A.m_pos.le hγ.le
  have hmΓ₀ : 0 ≤ A.m * Γ := mul_nonneg A.m_pos.le hΓ₀.le
  have hΦm : 0 ≤ A.responsePerp := A.packet.data.toData.response_nonneg A.m_pos.le hm₁
  have hΦΓ : 0 ≤ Φ (A.m * Γ) := A.packet.data.toData.response_nonneg hmΓ₀ hmΓ
  have hmono := A.packet.data.toData.response_antitoneOn
  have hΦperp : A.responsePerp ≤ A.responseStar :=
    hmono ⟨hmγ₀, hmγ.trans hm₁⟩ ⟨A.m_pos.le, hm₁⟩ hmγ
  have hΦlarge : Φ (A.m * Γ) ≤ A.responseStar :=
    hmono ⟨hmγ₀, hmγ.trans hm₁⟩ ⟨hmΓ₀, hmΓ⟩ (hmγ.trans hm_le_Γ)
  have hΦstar : Real.sqrt e < A.responseStar := A.response_lower
  have hstar₀ : 0 ≤ A.responseStar := (Real.sqrt_nonneg e).trans hΦstar.le
  have hΦstar' : A.responseStar ≤ 1 / 4 :=
    A.response_upper.trans
      ((Real.rpow_le_rpow A.packet.loss_pos.le hε (by norm_num : 0 ≤ (1 / 4 : ℝ))).trans_eq
        fourth_root_one_div_256)
  have hΦe : 3 * A.responseStar / 4 ≤ A.responseMean := by
    have hpg : 3 / 4 ≤ p := A.p_ge
    have h₁ := mul_le_mul_of_nonneg_right hpg hstar₀
    have h₂ := mul_nonneg (sub_nonneg.mpr hp.2) hΦΓ
    change 3 * A.responseStar / 4 ≤ p * A.responseStar + (1 - p) * Φ (A.m * Γ)
    linarith only [h₁, h₂]
  have hΦe' : A.responseMean ≤ A.responseStar := by
    have h := mul_le_mul_of_nonneg_left hΦlarge (sub_nonneg.mpr hp.2)
    change p * A.responseStar + (1 - p) * Φ (A.m * Γ) ≤ A.responseStar
    nlinarith only [h]
  have hM' : A.selectedMass ≤ 1 := by
    unfold selectedMass
    exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hm₁) A.packet.loss_pos.le)
  have hM := A.selectedMass_lower
  have hM₀ : 0 < A.selectedMass := by linarith only [hM, hε]
  have hDenPerp : A.responsePerp < A.selectedMass := by linarith only [hM, hε, hΦperp, hΦstar']
  have hDenMean : A.responseMean < A.selectedMass := by linarith only [hM, hε, hΦe', hΦstar']
  have hnum := selected_response_estimates A.packet.loss_pos hε hM hM' hΦstar hΦstar'
    hΦe hΦe' hΦm hΦperp A.response_ratio
  exact {
    mass_pos := hM₀
    gain_pos := hnum.1
    leak_nonneg := div_nonneg hΦm (sub_nonneg.mpr hDenPerp.le)
    gain_le := hnum.2.2.1.trans (mul_le_mul_of_nonneg_left A.response_upper (by norm_num))
    leak_ratio_le := hnum.2.2.2.1
    mass_loss_ratio_le := hnum.2.2.2.2
    perp_ne_one := ((div_lt_one hM₀).mpr hDenPerp).ne
    mean_ne_one := ((div_lt_one hM₀).mpr hDenMean).ne
  }

end

end SchauderBasisOrbits.PacketAndSeed
