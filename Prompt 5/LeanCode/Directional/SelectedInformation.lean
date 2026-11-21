import LeanCode.Directional.SelectedProjection
import LeanCode.Directional.SeedResponse
import LeanCode.Directional.SelectedCentering
import LeanCode.Directional.CaptureOperator

open Filter Function MeasureTheory Submodule Matrix ContinuousLinearMap InnerProductSpace
open scoped ENNReal BigOperators ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsProbabilityMeasure ρ] (D : DirectionalInput ρ)

section Selected

variable {L r n : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
variable (S : Scalar.Data r n)

local notation "I" => Fin (D.d + L)
local notation "Ω" => D.rowReferenceGram L
local notation "A" => D.rowSeedGram L hm hm'
local notation "W" => FiberWeight.selected (D.seedFiber L hm hm') S
local notation "P" => D.selectedTailSynthesis hm hm' S
local notation "V" => span ℂ (Set.range (productFamily ρ D.frequencies))

def seedResponseMean (L : ℕ) (m : ℝ) : ℝ :=
  seedDirectionFraction D.seedTheta (L : ℝ) * S.response (m * seedSmallEigenvalue D.seedTheta (L : ℝ)) +
    (1 - seedDirectionFraction D.seedTheta (L : ℝ)) *
      S.response (m * seedLargeEigenvalue D.seedTheta (L : ℝ))

private theorem starProjection_eq_of_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {E F : Submodule ℂ H}
    [E.HasOrthogonalProjection] [F.HasOrthogonalProjection] (h : E = F) :
    E.starProjection = F.starProjection := by
  cases h
  rfl

private theorem range_selectedTailSynthesis_full :
    (P).full.toLinearMap.range = span ℂ (Set.range (D.tailColumns hm hm' S)) := by
  rw [selectedTailSynthesis, FiberWeight.synthesis_full, range_synthCLM]
  congr 1
  let f : Fin (n * (D.d + L)) ≃ Fin n × I := finProdFinEquiv.symm
  change Set.range ((D.tailColumns hm hm' S) ∘ f) = _
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    exact ⟨f i, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨f.symm j, by simp⟩

/-- The capture quadratic form on the old span. Both scalar responses are
computed from the same positive row Gram and its actual eigencoordinates. -/
theorem selectedTail_capture_quadratic (hL : 1 ≤ L)
    (hIndep : LinearIndependent ℂ (D.selectedAugmented hm hm' S))
    (x : Lp ℂ 2 ρ) (hx : x ∈ V) :
    let e := D.baseSynthesis D.coeff
    Complex.re ⟪x, informationCapture (P).information x⟫_ℂ =
      (S.response m / (W).mass) * ‖x - rankOne ℂ e e x‖ ^ 2 +
      (D.seedResponseMean S L m / (W).mass) * ‖rankOne ℂ e e x‖ ^ 2 := by
  let e := D.baseSynthesis D.coeff
  have he : ‖e‖ = 1 := D.unit_direction
  change Complex.re ⟪x, informationCapture (P).information x⟫_ℂ =
    (S.response m / (W).mass) * ‖x - rankOne ℂ e e x‖ ^ 2 +
      (D.seedResponseMean S L m / (W).mass) * ‖rankOne ℂ e e x‖ ^ 2
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℂ).mp hx
  have hxc : D.baseSynthesis c = x := hc
  obtain ⟨E, β, hE, hΩ, hA, hβ⟩ := matrix_whitening_eigenbasis
    (D.rowReferenceGram_posDef L) (D.rowSeedGram_posDef hm hm') (D.rowSeedGram_relative hm hm').2
  haveI : FiniteDimensional ℂ (span ℂ (Set.range (D.tailColumns hm hm' S))) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range _)
  have hCent := D.selectedTail_centered_injective hm hm' S hIndep
  have hCap := (P).starProjection_full_sq hCent x
  let : FiniteDimensional ℂ (P).full.toLinearMap.range := Module.Finite.range _
  rw [starProjection_eq_of_eq (D.range_selectedTailSynthesis_full hm hm' S)] at hCap
  rw [← hCap, ← hxc, rankOne_apply]
  rw [show (P).pullback (D.baseSynthesis c) =
      (W).pullback ρ (synth (productFamily ρ D.frequencies) c) from rfl]
  rw [D.selected_projection_response hm hm' S E β hE (fun i => ⟨(hβ i).1.le, (hβ i).2⟩) hΩ hA,
    D.old_span_response hm hm' E β hE hΩ hA hL S.response c]
  rw [norm_smul, he, mul_one]
  change ((W).mass)⁻¹ * (S.response m * ‖D.baseSynthesis c - ⟪e, D.baseSynthesis c⟫_ℂ • e‖ ^ 2 +
      (D.seedResponseMean S L m) * ‖⟪e, D.baseSynthesis c⟫_ℂ‖ ^ 2) = _
  simp only [div_eq_mul_inv]
  ring

/-- The selected information operator with its gain and leakage coefficients. -/
theorem selectedTail_information (hL : 1 ≤ L)
    (hIndep : LinearIndependent ℂ (D.selectedAugmented hm hm' S))
    (hs : S.response m / (W).mass ≠ 1)
    (ht : D.seedResponseMean S L m / (W).mass ≠ 1) :
    ∃ C : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ, ‖C‖ ≤ 1 ∧
      (P).information =
        (D.seedResponseMean S L m / ((W).mass - D.seedResponseMean S L m)) •
          rankOne ℂ (D.baseSynthesis D.coeff) (D.baseSynthesis D.coeff) +
        (S.response m / ((W).mass - S.response m)) • C := by
  let e := D.baseSynthesis D.coeff
  let E := V
  let : FiniteDimensional ℂ E := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  have hUnit : ‖e‖ = 1 := D.unit_direction
  have he : e ∈ E := mem_span_range_synth _ _
  have hCent := D.selectedTail_centered_injective hm hm' S hIndep
  have hRange (x : Lp ℂ 2 ρ) : (P).information x ∈ E :=
    (D.selectedTail_means_range hm hm' S) ((P).information_mem_range x)
  have hsplit := information_eq_projected_sum E hUnit he
    ((P).information_positive hCent) hRange hs ht
    (fun x hx => D.selectedTail_capture_quadratic hm hm' S hL hIndep x hx)
  let C := E.starProjection - rankOne ℂ e e
  refine ⟨C, norm_starProjection_sub_rankOne_le_one E hUnit he, ?_⟩
  have cancel (a M : ℝ) (hM : M ≠ 0) (h : a / M ≠ 1) :
      (a / M) / (1 - a / M) = a / (M - a) := by
    have hn : M - a ≠ 0 := by
      intro hz
      have heq : M = a := sub_eq_zero.mp hz
      exact h ((div_eq_iff hM).mpr (by linarith))
    field_simp [hM, hn, sub_ne_zero.mpr h.symm]
  rw [cancel _ _ (W).mass_pos.ne' hs, cancel _ _ (W).mass_pos.ne' ht] at hsplit
  exact hsplit.trans (add_comm _ _)

end Selected

end

end SchauderBasisOrbits.DirectionalInput
