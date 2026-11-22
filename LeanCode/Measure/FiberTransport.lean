module

public import LeanCode.Measure.Information

@[expose] public section

open MeasureTheory ContinuousLinearMap Function
open scoped ComplexOrder MatrixOrder

namespace SchauderBasisOrbits.FiberWeight

noncomputable section

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Measure β} [IsFiniteMeasure κ] {ν : Measure γ} [IsFiniteMeasure ν]
variable (W : FiberWeight α κ) (ρ : Measure α) [IsFiniteMeasure ρ]
variable (e : γ ≃ᵐ β) (he : MeasurePreserving e ν κ)
variable {n : ℕ} {u : Fin n → α × β → ℂ} {v : Fin n → α × γ → ℂ}
variable (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i))
variable (B : Fin n → ℝ) (huB : ∀ i x, ‖u i x‖ ≤ B i) (hvB : ∀ i x, ‖v i x‖ ≤ B i)
variable (hRaw : ∀ i p, v i p = u i (p.1, e p.2))

include hRaw

private lemma mean_synthesis_pullFiber_raw (i : Fin n) (x : α) :
    (W.pullFiber e he).mean (v i) x = W.mean (u i) x := by
  simp_rw [show v i = fun p => u i (p.1, e p.2) from funext (hRaw i)]
  exact W.mean_pullFiber e he (u i) x

theorem synthesis_means_pullFiber :
    ((W.pullFiber e he).synthesis ρ v hv B hvB).means = (W.synthesis ρ u hu B huB).means := by
  change synthCLM (fun i => lift₂ ρ ((W.pullFiber e he).mean (v i)) _ (B i) _) =
    synthCLM (fun i => lift₂ ρ (W.mean (u i)) _ (B i) _)
  apply congrArg synthCLM
  funext i
  apply Lp.ext
  filter_upwards [ae_lift₂ ρ ((W.pullFiber e he).mean (v i)) _ _ _,
    ae_lift₂ ρ (W.mean (u i)) _ _ _] with x hx hy
  rw [hx, hy, mean_synthesis_pullFiber_raw W e he hRaw]

private lemma center_synthesis_pullFiber_raw (i : Fin n) (p : α × γ) :
    (W.pullFiber e he).center (v i) p = W.center (u i) (p.1, e p.2) := by
  unfold FiberWeight.center
  rw [hRaw, mean_synthesis_pullFiber_raw W e he hRaw]

omit hRaw in
/-- The pullback on the normalized weighted L² spaces for a fiber change. -/
def synthesisPullFiberIsometry :
    Lp ℂ 2 (W.normalizedMeasure ρ) →ₗᵢ[ℂ] Lp ℂ 2 ((W.pullFiber e he).normalizedMeasure ρ) :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (W.measurePreserving_pullFiber ρ e he)

theorem synthesis_centered_pullFiber :
    ((W.pullFiber e he).synthesis ρ v hv B hvB).centered =
      (W.synthesisPullFiberIsometry ρ e he).toContinuousLinearMap ∘L
        (W.synthesis ρ u hu B huB).centered := by
  let P := W.pullFiber e he
  let f := MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) e
  let hm := W.measurePreserving_pullFiber ρ e he
  let L := W.synthesisPullFiberIsometry ρ e he
  have hvec (i : Fin n) :
      lift₂ (P.normalizedMeasure ρ) (P.center (v i)) (P.measurable_center (hv i))
        (2 * B i) (P.norm_center_le (hv i) (hvB i)) =
      L (lift₂ (W.normalizedMeasure ρ) (W.center (u i)) (W.measurable_center (hu i))
        (2 * B i) (W.norm_center_le (hu i) (huB i))) := by
    let l := lift₂ (P.normalizedMeasure ρ) (P.center (v i)) (P.measurable_center (hv i))
      (2 * B i) (P.norm_center_le (hv i) (hvB i))
    let t := lift₂ (W.normalizedMeasure ρ) (W.center (u i)) (W.measurable_center (hu i))
      (2 * B i) (W.norm_center_le (hu i) (huB i))
    have heval := Lp.coeFn_compMeasurePreserving (f := f) t hm
    have ht := hm.quasiMeasurePreserving.ae_eq_comp
      (ae_lift₂ (W.normalizedMeasure ρ) (W.center (u i)) (W.measurable_center (hu i))
        (2 * B i) (W.norm_center_le (hu i) (huB i)))
    change l = L t
    apply Lp.ext
    filter_upwards [ae_lift₂ (P.normalizedMeasure ρ) (P.center (v i)) _ _ _, heval, ht]
      with p hp heval ht
    change l p = (Lp.compMeasurePreserving f hm t) p
    rw [hp, heval]
    change P.center (v i) p = t (p.1, e p.2)
    have htu : t (p.1, e p.2) = W.center (u i) (p.1, e p.2) := ht
    rw [htu, center_synthesis_pullFiber_raw W e he hRaw]
  apply ContinuousLinearMap.ext
  intro c
  simp only [FiberWeight.synthesis, coe_comp, Function.comp_apply, synthCLM_apply, synth,
    map_sum, map_smul, LinearIsometry.coe_toContinuousLinearMap]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z => c.ofLp i • z) (hvec i)

theorem synthesis_centeredGram_pullFiber :
    ((W.pullFiber e he).synthesis ρ v hv B hvB).centeredGram =
      (W.synthesis ρ u hu B huB).centeredGram := by
  simp only [CenteredSynthesis.centeredGram]
  rw [synthesis_centered_pullFiber W ρ e he hu hv B huB hvB hRaw]
  apply le_antisymm <;>
    (apply matrix_le_of_qform_le (clmGram_isHermitian _) (clmGram_isHermitian _)
     intro c
     simp [qform_clmGram])

theorem synthesis_centered_injective_pullFiber
    (h : Injective (W.synthesis ρ u hu B huB).centered) :
    Injective ((W.pullFiber e he).synthesis ρ v hv B hvB).centered := by
  rw [synthesis_centered_pullFiber W ρ e he hu hv B huB hvB hRaw]
  exact (W.synthesisPullFiberIsometry ρ e he).injective.comp h

theorem synthesis_information_pullFiber :
    ((W.pullFiber e he).synthesis ρ v hv B hvB).information =
      (W.synthesis ρ u hu B huB).information := by
  unfold CenteredSynthesis.information CenteredSynthesis.centeredInverse
  rw [synthesis_means_pullFiber W ρ e he hu hv B huB hvB hRaw,
    synthesis_centeredGram_pullFiber W ρ e he hu hv B huB hvB hRaw]

end

end SchauderBasisOrbits.FiberWeight
