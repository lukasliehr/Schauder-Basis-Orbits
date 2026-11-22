module

public import LeanCode.Directional.CopyPackets

@[expose] public section

open Filter Function MeasureTheory
open scoped Topology ENNReal ComplexOrder

namespace SchauderBasisOrbits

variable {ι : Type*} [Fintype ι] {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ]
variable {D : DirectionalInput ρ} {Ks ε : ℝ}

/-- The output of taking independent copies of a single selected packet. -/
structure AmplifiedFamily (P : SelectedPacket D Ks ε) (N : ℕ) extends DirectionalFamily D where
  mass_eq : W.mass = P.W.mass ^ N
  centered_pb : PB (directionalSynthesis ρ W freq).centeredGram
    (Real.sqrt (selectedPrefixSq Ks D.K ε))
  information_eq : (directionalSynthesis ρ W freq).information =
    (N : ℝ) • (directionalSynthesis ρ P.W P.freq).information

private lemma amplify_information_error (P : SelectedPacket D Ks ε) {N : ℕ}
    (A : AmplifiedFamily P N) {σ : ℝ} (hNZ : σ ≤ (N : ℝ) * P.gain) :
    ‖(directionalSynthesis ρ A.W A.freq).information -
      σ • InnerProductSpace.rankOne ℂ (synth (productFamily ρ D.frequencies) D.coeff)
        (synth (productFamily ρ D.frequencies) D.coeff)‖ ≤
      ((N : ℝ) * P.gain - σ) + (N : ℝ) * P.leak := by
  let e := synth (productFamily ρ D.frequencies) D.coeff
  let Pe := InnerProductSpace.rankOne ℂ e e
  have he : ‖e‖ = 1 := D.unit_direction
  have hp : ‖Pe‖ = 1 := by simp [Pe, InnerProductSpace.norm_rankOne, he]
  rw [A.information_eq, P.information_eq]
  change ‖(N : ℝ) • (P.gain • Pe + P.leak • P.leakOp) - σ • Pe‖ ≤ _
  rw [smul_add, smul_smul, smul_smul]
  have hEq : ((N : ℝ) * P.gain) • Pe + ((N : ℝ) * P.leak) • P.leakOp - σ • Pe =
      ((N : ℝ) * P.gain - σ) • Pe + ((N : ℝ) * P.leak) • P.leakOp := by
    rw [sub_smul]
    abel
  rw [hEq]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hNZ),
    abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ (N : ℝ)) P.leak_nonneg), hp, mul_one]
  exact add_le_add (le_refl _) (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left P.leakOp_norm
      (mul_nonneg (by positivity : 0 ≤ (N : ℝ)) P.leak_nonneg))

lemma copied_output_linear_prefix {P : SelectedPacket D Ks ε} {N : ℕ}
    (A : AmplifiedFamily P N) {η : ℝ}
    (hSq : selectedPrefixSq Ks D.K ε ≤ selectedPrefixSq Ks D.K 0 + η) :
    PB (directionalSynthesis ρ A.W A.freq).centeredGram
      (Real.sqrt (selectedPrefixSq Ks D.K 0 + η)) := by
  have hstep := Real.sqrt_le_sqrt hSq
  have hPB := A.centered_pb
  refine ⟨hPB.1.trans hstep, fun k hk c => (hPB.2 k hk c).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hPB.1 hstep 2)
    (qform_nonneg ((directionalSynthesis ρ A.W A.freq).centeredGram_posDef A.centered_injective).posSemidef _)

/-- A single sufficiently small packet provides the directional output once its copies have
the standard product identities. -/
noncomputable def amplified_packet_output {P : SelectedPacket D Ks ε} {N : ℕ}
    (A : AmplifiedFamily P N) {σ η : ℝ}
    (hN₁ : σ ≤ (N : ℝ) * P.gain) (hN₂ : (N : ℝ) * P.gain < σ + P.gain)
    (hLoss : 1 - P.W.mass ^ N < η)
    (hErr : P.gain + (N : ℝ) * P.leak ≤ η)
    (hSq : selectedPrefixSq Ks D.K ε ≤ selectedPrefixSq Ks D.K 0 + η) :
    DirectionalOutput D Ks σ η where
  toDirectionalFamily := A.toDirectionalFamily
  mass_gt := by rw [A.mass_eq]; linarith
  centered_pb := copied_output_linear_prefix A hSq
  information_error := by
    have h := amplify_information_error P A hN₁
    exact h.trans_lt (by linarith only [hN₂, hErr])

/-- Pick one index after taking the three eventual thresholds in the amplification proof. -/
theorem directional_output_of_packet_sequence {ε : ℕ → ℝ} (P : ∀ n, SelectedPacket D Ks (ε n))
    (hε : Tendsto ε atTop (𝓝 0))
    (hGain : Tendsto (fun n => (P n).gain) atTop (𝓝 0))
    (hLeak : Tendsto (fun n => (P n).leak / (P n).gain) atTop (𝓝 0))
    (hLoss : Tendsto (fun n => (1 - (P n).W.mass) / (P n).gain) atTop (𝓝 0))
    (copy : ∀ (n N : ℕ), 0 < N → Nonempty (AmplifiedFamily (P n) N))
    {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    Nonempty (DirectionalOutput D Ks σ η) := by
  have hσGain : Tendsto (fun n => σ + (P n).gain) atTop (𝓝 σ) := by
    simpa only [add_zero] using tendsto_const_nhds.add hGain
  have hErr : Tendsto (fun n => (P n).gain + (σ + (P n).gain) * ((P n).leak / (P n).gain))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hGain.add (hσGain.mul hLeak)
  have hLoss' : Tendsto (fun n => (σ + (P n).gain) * ((1 - (P n).W.mass) / (P n).gain))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hσGain.mul hLoss
  have hq : Tendsto (fun n => selectedPrefixSq Ks D.K (ε n)) atTop
      (𝓝 (selectedPrefixSq Ks D.K 0)) :=
    ((continuous_selectedPrefixSq Ks D.K).tendsto 0).comp hε
  have hQ := (tendsto_order.mp hq).2 (selectedPrefixSq Ks D.K 0 + η) (by linarith)
  have hE := (tendsto_order.mp hErr).2 η hη
  have hM := (tendsto_order.mp hLoss').2 η hη
  obtain ⟨n, hq', he', hm'⟩ := (hQ.and (hE.and hM)).exists
  let Q := P n
  obtain ⟨N, hN, hN₁, hN₂, hNLeak, hNMass⟩ :=
    selected_amplification_arithmetic hσ Q.gain_pos Q.leak_nonneg Q.W.mass_pos.le
      (Q.W.mass_le_one 0)
  obtain ⟨A⟩ := copy n N hN
  have hAErr : Q.gain + (N : ℝ) * Q.leak ≤ η :=
    (add_le_add (le_refl _) hNLeak).trans he'.le
  exact ⟨amplified_packet_output A hN₁ hN₂ (hNMass.trans_lt hm') hAErr hq'.le⟩

end SchauderBasisOrbits
