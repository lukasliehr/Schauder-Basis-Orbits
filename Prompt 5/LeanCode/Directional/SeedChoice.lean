import LeanCode.Directional.Amplification
import LeanCode.Directional.Response
import LeanCode.Scalar.SupplyContract

open Filter
open scoped Topology MatrixOrder

namespace SchauderBasisOrbits

noncomputable section

theorem tendsto_seedRatio {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) :
    Tendsto (fun L : ℕ => seedRatio θ (L : ℝ)) atTop atTop := by
  refine tendsto_atTop.2 fun r => ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 ((r - 1) * (1 - θ) / θ))
  filter_upwards [eventually_ge_atTop N] with L hL
  have hL' : (N : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : 1 ≤ (L : ℝ) := (le_max_left ..).trans (hN.trans hL')
  have h2 : (r - 1) * (1 - θ) / θ ≤ (L : ℝ) := (le_max_right ..).trans (hN.trans hL')
  have h3 := (div_le_iff₀ hθ).mp h2
  have h4 : r - 1 ≤ θ * (L : ℝ) / (1 - θ) :=
    (le_div_iff₀ (sub_pos.mpr hθ')).mpr (by linarith [mul_comm θ (L : ℝ)])
  exact (show r ≤ 1 + θ * (L : ℝ) / (1 - θ) by linarith).trans (seed_ratio_bounds hθ hθ' h1).1

theorem eventually_seedFraction {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) :
    ∀ᶠ L : ℕ in atTop, 1 ≤ L ∧ 3 / 4 ≤ seedDirectionFraction θ (L : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 + 4 / θ)
  filter_upwards [eventually_ge_atTop N] with L hL
  have hL' : 1 + 4 / θ ≤ (L : ℝ) := hN.trans (by exact_mod_cast hL)
  have hl : 1 < (L : ℝ) := (lt_add_of_pos_right _ (by positivity)).trans_le hL'
  have hab : 4 ≤ θ * ((L : ℝ) - 1) := by
    have h := (div_le_iff₀ hθ).mp (show 4 / θ ≤ (L : ℝ) - 1 by linarith)
    linarith [mul_comm θ ((L : ℝ) - 1)]
  have hbound := (seed_fraction_error hθ hθ' hl).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hab)
  exact ⟨by exact_mod_cast hl.le, by linarith⟩

/-- A scalar packet paired with a compatible directional seed scale. -/
structure PacketAndSeed (δ z θ : ℝ) where
  packet : Scalar.GoodScalar δ z
  L : ℕ
  L_pos : 1 ≤ L
  m : ℝ
  m_pos : 0 < m
  m_le : m ≤ ((1 : ℝ) / 2) ^ L
  p_ge : 3 / 4 ≤ seedDirectionFraction θ (L : ℝ)
  ratio_ge : 2 ≤ seedRatio θ (L : ℝ)
  response_lower : Real.sqrt packet.data.toData.loss <
    packet.data.toData.response (m * seedSmallEigenvalue θ (L : ℝ))
  response_upper : packet.data.toData.response (m * seedSmallEigenvalue θ (L : ℝ)) ≤
    packet.data.toData.loss ^ (1 / 4 : ℝ)
  response_ratio : packet.data.toData.response m ≤
    seedRatio θ (L : ℝ) ^ (-(1 / 16 : ℝ)) *
      packet.data.toData.response (m * seedSmallEigenvalue θ (L : ℝ))

/-- The seed dimension can be fixed first. The scalar packet supply then allows
an arbitrarily small loss for that fixed seed size and ratio. -/
theorem exists_packet_and_seed {δ z θ lossTarget leakTarget : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < 1) (hLoss : 0 < lossTarget)
    (hLeak : 0 < leakTarget)
    (packets : ∀ η > 0, ∃ p : Scalar.GoodScalar δ z, p.data.toData.loss < η) :
    ∃ D : PacketAndSeed δ z θ, D.packet.data.toData.loss < lossTarget ∧
      D.packet.data.toData.loss ≤ 1 / 256 ∧
      seedRatio θ (D.L : ℝ) ^ (-(1 / 16 : ℝ)) < leakTarget := by
  have hR := tendsto_seedRatio hθ hθ'
  have hf := eventually_seedFraction hθ hθ'
  have ht := ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 16 : ℝ))).comp hR).eventually
    (gt_mem_nhds hLeak)
  obtain ⟨L, ⟨hL, hγ⟩, hRge, hleak⟩ := (hf.and ((hR.eventually_ge_atTop 2).and ht)).exists
  let R := seedRatio θ (L : ℝ)
  let F := z / (8 * (1 + z))
  have hF : 0 < F := by unfold F; positivity
  have hcont : ContinuousAt (fun e : ℝ => e ^ (1 / 4 : ℝ)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / 4) (Or.inr (by norm_num))
  have hF' : ∀ᶠ e in 𝓝 (0 : ℝ), e ^ (1 / 4 : ℝ) < F :=
    hcont.eventually (p := fun x : ℝ => x < F) (gt_mem_nhds (by
      simpa only [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using hF))
  obtain ⟨p, hp, hpow⟩ := Metric.eventually_nhds_iff.mp hF'
  let δ' := min p (min lossTarget (1 / 256))
  have hδ' : 0 < δ' := lt_min hp (lt_min hLoss (by norm_num))
  obtain ⟨η, hη, hη'⟩ := exists_compatible_scalar_loss_bound L (show 0 < R by linarith) hδ'
  obtain ⟨P, hP⟩ := packets η hη
  let e := P.data.toData.loss
  have he : 0 < e := P.loss_pos
  obtain ⟨hsmall, he1, hlog, hmass⟩ := hη' e he hP
  have hlt : e ^ (1 / 4 : ℝ) < F := hpow (by
    rw [dist_zero_right, Real.norm_of_nonneg he.le]
    exact hsmall.trans_le (min_le_left ..))
  have hε : e ≤ 1 / 256 := hsmall.le.trans ((min_le_right ..).trans (min_le_right ..))
  have hεGoal : e < lossTarget := hsmall.trans_le ((min_le_right ..).trans (min_le_left ..))
  let Φ := P.data.toData.response
  have hΦ : F ≤ Φ (e ^ 2) := by
    have h := P.data.toData.gain_div_eight_le_response_loss_sq (by dsimp [e] at hε ⊢; linarith)
      P.gram_floor
    simpa only [P.gain_eq, F, Φ, e] using h
  obtain ⟨m, hm, hΦ₀, hΦ₁, hΦr⟩ := Scalar.exists_response_scale he he1 hRge hlog
    P.data.toData.response_antitoneOn (hlt.trans_le hΦ)
    (P.data.toData.response_sqrt_loss_le he)
    (fun {_} hβ hRβ => P.data.toData.response_ratio hβ (by linarith only [hRge]) hRβ)
  have hmpos : 0 < m := (mul_pos (sq_pos_of_pos he) (by linarith : 0 < R)).trans_le hm.1
  have heq : m / R = m * seedSmallEigenvalue θ (L : ℝ) := by simp [R, seedRatio, div_eq_mul_inv]
  rw [heq] at hΦ₀ hΦ₁ hΦr
  exact ⟨⟨P, L, hL, m, hmpos, hm.2.trans hmass, hγ, hRge, hΦ₀, hΦ₁, hΦr⟩,
    hεGoal, hε, hleak⟩

end

end SchauderBasisOrbits
