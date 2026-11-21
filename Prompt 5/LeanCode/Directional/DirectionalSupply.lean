import LeanCode.Directional.SeedChoice
import LeanCode.Directional.AmplifiedCopies
import LeanCode.Scalar.Supply

open Filter MeasureTheory
open scoped Topology ENNReal

namespace SchauderBasisOrbits

variable {ι : Type*} [Fintype ι]

/-- The single selected packet construction, with only the numerical estimates
needed to choose how many independent copies to take. -/
def SelectedPacketFactory (ρ : Measure (ℝ × UnitAddTorus ι)) [IsProbabilityMeasure ρ] : Prop :=
  ∀ (D : DirectionalInput ρ) (Ks δ z : ℝ) (A : PacketAndSeed δ z D.seedTheta),
    1 < Ks → Scalar.commonBound δ < Ks → A.packet.data.toData.loss ≤ 1 / 256 →
    ∃ P : SelectedPacket D Ks A.packet.data.toData.loss,
      P.gain ≤ 2 * A.packet.data.toData.loss ^ (1 / 4 : ℝ) ∧
      P.leak / P.gain ≤ 8 * seedRatio D.seedTheta (A.L : ℝ) ^ (-(1 / 16 : ℝ)) / 3 ∧
      (1 - P.W.mass) / P.gain ≤ 4 * Real.sqrt A.packet.data.toData.loss / 3

private lemma exists_directional_loss_target (Ks Kv : ℝ) {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∃ R > 0, ∀ e : ℝ, 0 ≤ e → e < R →
      selectedPrefixSq Ks Kv e ≤ selectedPrefixSq Ks Kv 0 + η ∧
      2 * e ^ (1 / 4 : ℝ) < η / 2 ∧ 4 * Real.sqrt e / 3 < η / C := by
  have hq : ∀ᶠ e : ℝ in 𝓝 0, selectedPrefixSq Ks Kv e < selectedPrefixSq Ks Kv 0 + η :=
    ((continuous_selectedPrefixSq Ks Kv).tendsto 0).eventually
      (gt_mem_nhds (show selectedPrefixSq Ks Kv 0 < selectedPrefixSq Ks Kv 0 + η by linarith))
  have hp : ContinuousAt (fun e : ℝ => 2 * e ^ (1 / 4 : ℝ)) 0 := by
    refine continuousAt_const.mul (Real.continuousAt_rpow_const 0 (1 / 4) (Or.inr (by norm_num)))
  have hpow : ∀ᶠ e : ℝ in 𝓝 0, 2 * e ^ (1 / 4 : ℝ) < η / 2 :=
    hp.eventually (p := fun x : ℝ => x < η / 2) (gt_mem_nhds (by
      simpa only [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero] using
        (show (0 : ℝ) < η / 2 by positivity)))
  have hs : ContinuousAt (fun e : ℝ => 4 * Real.sqrt e / 3) 0 := by
    fun_prop
  have hsq : ∀ᶠ e : ℝ in 𝓝 0, 4 * Real.sqrt e / 3 < η / C :=
    hs.eventually (p := fun x : ℝ => x < η / C) (gt_mem_nhds (by
      simpa only [Real.sqrt_zero, mul_zero, zero_div] using (div_pos hη hC)))
  obtain ⟨R, hR, hrest⟩ := Metric.eventually_nhds_iff.mp (hq.and (hpow.and hsq))
  refine ⟨R, hR, fun e he hE => ?_⟩
  have ht : dist e 0 < R := by simpa [Real.dist_eq, abs_of_nonneg he] using hE
  obtain ⟨h₁, h₂, h₃⟩ := hrest ht
  exact ⟨h₁.le, h₂, h₃⟩

/-- Use the scalar supply to pick a small-loss packet and then amplify it. -/
theorem directionalSupply_of_selectedPacketFactory
    (ρ : Measure (ℝ × UnitAddTorus ι)) [IsProbabilityMeasure ρ]
    (factory : SelectedPacketFactory ρ) : DirectionalSupply ρ := by
  intro D Ks σ η hKs hσ hη
  let δ := min 1 ((Ks - 1) / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (by linarith)
  have hδ₁ : δ ≤ 1 := min_le_left _ _
  have hδK : 1 + δ < Ks := by linarith only [min_le_right (1 : ℝ) ((Ks - 1) / 2), hKs]
  have hK : Scalar.commonBound δ < Ks := (Scalar.commonBound_lt_one_add hδ).trans hδK
  have hcap : 0 < Scalar.gainCap δ := by
    apply lt_of_lt_of_le _ (Scalar.gainCap_bounds hδ hδ₁).1
    unfold Scalar.initialLoss
    positivity
  let z := Scalar.gainCap δ / 4
  have hz : 0 < z := by dsimp [z]; positivity
  have hzCap : z < Scalar.gainCap δ / 2 := by dsimp [z]; linarith
  let C := σ + η + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let leakTarget := η / (8 * C)
  have ht : 0 < leakTarget := by dsimp [leakTarget]; positivity
  obtain ⟨R, hR, hR'⟩ := exists_directional_loss_target Ks D.K hC hη
  obtain ⟨A, heR, heSmall, hRat⟩ := exists_packet_and_seed hz D.seedTheta_bounds.1
    (D.seedTheta_bounds.2.trans_lt (by norm_num)) hR ht
    (fun η hη => Scalar.exists_goodScalar hδ hδ₁ hz hzCap hη)
  obtain ⟨P, hGain, hLeak, hMass⟩ := factory D Ks δ z A hKs hK heSmall
  have hSmall := hR' _ A.packet.loss_pos.le heR
  have hPgain : P.gain < η / 2 := hGain.trans_lt hSmall.2.1
  have hσgain : 0 < σ + P.gain := add_pos hσ P.gain_pos
  have hPC : σ + P.gain ≤ C := by dsimp [C]; linarith
  have hLeak' : P.leak / P.gain < η / (2 * C) := by
    have htemp := mul_lt_mul_of_pos_left hRat (show (0 : ℝ) < 8 / 3 by norm_num)
    have heq : (8 / 3 : ℝ) * leakTarget = η / (3 * C) := by
      dsimp [leakTarget]
      field_simp
    have haux : η / (3 * C) ≤ η / (2 * C) :=
      div_le_div_of_nonneg_left hη.le (by positivity) (by linarith)
    refine hLeak.trans_lt (?_ : _ < _)
    rw [← heq] at haux
    exact (by nlinarith only [htemp] : 8 * seedRatio D.seedTheta (A.L : ℝ) ^ (-(1 / 16 : ℝ)) / 3 <
      (8 / 3 : ℝ) * leakTarget).trans_le haux
  have hMass' : (1 - P.W.mass) / P.gain < η / C := hMass.trans_lt hSmall.2.2
  obtain ⟨N, hN, hN₁, hN₂, hNLeak, hNMass⟩ :=
    selected_amplification_arithmetic hσ P.gain_pos P.leak_nonneg P.W.mass_pos.le (P.W.mass_le_one 0)
  let F := amplifySelectedPacket P N hN
  have hMassN : 1 - P.W.mass ^ N < η := by
    refine hNMass.trans_lt ((mul_lt_mul_of_pos_left hMass' hσgain).trans_le ?_)
    calc
      _ ≤ C * (η / C) := mul_le_mul_of_nonneg_right hPC (by positivity)
      _ = η := by field_simp
  have hLeakN : (N : ℝ) * P.leak < η / 2 := by
    refine hNLeak.trans_lt ((mul_lt_mul_of_pos_left hLeak' hσgain).trans_le ?_)
    calc
      _ ≤ C * (η / (2 * C)) := mul_le_mul_of_nonneg_right hPC (by positivity)
      _ = η / 2 := by field_simp
  exact ⟨amplified_packet_output F hN₁ hN₂ hMassN
    (by linarith only [hPgain, hLeakN]) hSmall.1⟩

end SchauderBasisOrbits
