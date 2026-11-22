module

public import LeanCode.Directional.DirectionalSupply
public import LeanCode.Directional.PacketBounds
public import LeanCode.Directional.SelectedInformation
public import LeanCode.Directional.SelectedPacketAssembly
public import LeanCode.Directional.SelectedPrefixData

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace SchauderBasisOrbits

variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
/-- Build a single selected packet with its actual prefix and information certificates. -/
theorem selectedPacketFactory (ρ : Measure (ℝ × UnitAddTorus ι)) [IsProbabilityMeasure ρ] :
    SelectedPacketFactory ρ := by
  intro D Ks δ z A hKs hKsδ hε
  let S := A.packet.data
  let W := (D.seedFiber A.L A.m_pos A.m_le).selected S.toData
  have hM : W.mass = A.selectedMass := FiberWeight.selected_mass _ _
  have hθ := D.seedTheta_bounds
  have hBounds := A.selectedBounds hθ.1 (by linarith [hθ.2]) hε
  obtain ⟨hIndep, hPB⟩ :=
    D.selected_packet_prefix_certificates (L := A.L) A.m_pos A.m_le A.packet hKs hKsδ
  have hs : S.toData.response A.m / W.mass ≠ 1 := by
    rw [hM]
    exact hBounds.perp_ne_one
  have ht : D.seedResponseMean S.toData A.L A.m / W.mass ≠ 1 := by
    rw [hM]
    exact hBounds.mean_ne_one
  obtain ⟨C, hC, hInfo⟩ :=
    D.selectedTail_information A.m_pos A.m_le S.toData A.L_pos hIndep hs ht
  have hI : (D.selectedTailSynthesis A.m_pos A.m_le S.toData).information =
      A.gain • InnerProductSpace.rankOne ℂ (synth (productFamily ρ D.frequencies) D.coeff)
        (synth (productFamily ρ D.frequencies) D.coeff) + A.leak • C := by
    change (D.selectedTailSynthesis A.m_pos A.m_le S.toData).information =
      (A.responseMean / (A.selectedMass - A.responseMean)) •
        InnerProductSpace.rankOne ℂ (D.baseSynthesis D.coeff) (D.baseSynthesis D.coeff) +
      (A.responsePerp / (A.selectedMass - A.responsePerp)) • C
    rw [← hM]
    exact hInfo
  let P := D.assembleSelectedPacket A.m_pos A.m_le S Ks hBounds.gain_pos
    hBounds.leak_nonneg C hC hIndep hPB hI
  refine ⟨P, hBounds.gain_le, hBounds.leak_ratio_le, ?_⟩
  change (1 - P.W.mass) / A.gain ≤ _
  rw [show P.W.mass = A.selectedMass from
    D.assembleSelectedPacket_mass A.m_pos A.m_le S Ks hBounds.gain_pos
      hBounds.leak_nonneg C hC hIndep hPB hI]
  exact hBounds.mass_loss_ratio_le

/-- Directional extension on any base probability with finitely many torus coordinates. -/
theorem directional_supply (ρ : Measure (ℝ × UnitAddTorus ι)) [IsProbabilityMeasure ρ] :
    DirectionalSupply ρ :=
  directionalSupply_of_selectedPacketFactory ρ (selectedPacketFactory ρ)

end SchauderBasisOrbits
