import LeanCode.Scalar.SupplyContract
import LeanCode.Scalar.ActivationPrefix
import LeanCode.Scalar.Smoothing
import LeanCode.Scalar.Tuning

open Filter Matrix
open scoped Topology MatrixOrder

namespace SchauderBasisOrbits.Scalar

lemma one_le_commonBound {δ : ℝ} (hδ : 0 ≤ δ) : 1 ≤ commonBound δ := by
  unfold commonBound
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
    (show 1 ≤ 1 + δ / 2 + δ / 24000 by linarith)

/-- Starting with the activation prefix estimate, the raw iteration, smoothing, and affine
tuning produce the polynomial scalar supply with exact prescribed gain. -/
theorem exists_goodScalar_of_activation_prefix (hAct : ActivationPrefixEstimate)
    {δ z η : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hz : 0 < z)
    (hzCap : z < gainCap δ / 2) (hη : 0 < η) :
    ∃ s : GoodScalar δ z, s.data.toData.loss < η := by
  obtain ⟨S, hS⟩ := stage_supply_of_step hδ hδ₁
    (fun _ T => stage_step_of_activation_prefix hAct hδ hδ₁ T)
  obtain ⟨j, hj⟩ := ((tendsto_order.mp hS).2 _ hη).exists
  let T := S j
  let D := T.data
  have hzD : z < D.gain := by
    have h := T.gain_lower hδ hδ₁
    have hCap : 0 < gainCap δ := by linarith only [hz, hzCap]
    change 3 * gainCap δ / 4 ≤ D.gain at h
    linarith only [h, hCap, hzCap]
  obtain ⟨N, hN⟩ := ((tendsto_order.mp (smoothData_gain_tendsto D)).1 _ hzD).exists
  let P := smoothData D N
  have hLoss : P.toData.loss = D.loss := by
    rw [Data.loss, smoothData_mass, Data.loss]
  have he : 0 < P.toData.loss := hLoss ▸ T.loss_pos
  have hB : PB P.toData.gram (commonBound δ) := smoothData_pb D N (T.common_augmented_pb hδ hδ₁)
  have hfloor : P.toData.loss ^ 2 • 1 ≤ P.toData.gram := by
    rw [hLoss]
    exact smoothData_floor D N T.gram_floor
  have hdiag (i : Fin T.length) :
      P.toData.gram⁻¹ i.succ i.succ ≤ 1 + 2 * P.toData.loss := by
    rw [hLoss]
    exact (smoothData_inverse_diagonal_le D N i.succ).trans (T.inverse_diagonal i)
  obtain ⟨β, hβ, hg, hp, hl⟩ := exists_tune_gain P hz hN he
  let E := tune P β hβ
  have hPB := tune_pb P (one_le_commonBound hδ.le) hB hβ
  refine ⟨{
    dim := T.dim
    length := T.length
    data := E
    gain_eq := hg
    loss_pos := hp
    gram_floor := tune_floor P hβ hfloor
    inverse_diagonal := tune_inverse_diagonal P hβ hdiag
    augmented_pb := hPB
    centered_hPrefix := E.toData.centerLp_hPrefix_of_gram_pb hPB
  }, ?_⟩
  exact hl.trans_lt (hLoss ▸ hj)


/-- The polynomial scalar supply, with the activation geometry proved in the library. -/
theorem exists_goodScalar {δ z η : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hz : 0 < z)
    (hzCap : z < gainCap δ / 2) (hη : 0 < η) :
    ∃ s : GoodScalar δ z, s.data.toData.loss < η :=
  exists_goodScalar_of_activation_prefix activationPrefixEstimate hδ hδ₁ hz hzCap hη

end SchauderBasisOrbits.Scalar
