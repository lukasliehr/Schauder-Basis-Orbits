module

public import LeanCode.Directional.SelectedCentering
public import LeanCode.Directional.SupplyContract
public import LeanCode.Measure.FiberTransport

@[expose] public section

open Filter Function MeasureTheory Submodule
open scoped ENNReal ComplexOrder Topology

namespace SchauderBasisOrbits.DirectionalInput

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {ρ : Measure (Base ι)} [IsFiniteMeasure ρ] (D : DirectionalInput ρ)
variable {L r n : ℕ} {m : ℝ} (hm : 0 < m) (hm' : m ≤ ((1 : ℝ) / 2) ^ L)
variable (S : Scalar.PolynomialData r n)

/-- The two disjoint fresh blocks as one canonical finite torus. -/
def selectedFiberEquiv (L r : ℕ) :
    UnitAddTorus (Fin (L + r)) ≃ᵐ UnitAddTorus (Fin L) × UnitAddTorus (Fin r) :=
  (torusReindex finSumFinEquiv.symm).trans torusSplit

lemma measurePreserving_selectedFiberEquiv (L r : ℕ) :
    MeasurePreserving (selectedFiberEquiv L r) (torusHaar (Fin (L + r)))
      ((torusHaar (Fin L)).prod (torusHaar (Fin r))) :=
  measurePreserving_torusSplit.comp (measurePreserving_torusReindex finSumFinEquiv.symm)

lemma selectedFiberEquiv_apply (y : UnitAddTorus (Fin (L + r))) :
    selectedFiberEquiv L r y =
      (fun i => y (Fin.castAdd r i), fun i => y (Fin.natAdd L i)) := by
  unfold selectedFiberEquiv
  rw [MeasurableEquiv.trans_apply, torusReindex_apply]
  rfl

/-- Reassociate auxiliary coordinates before flattening the fresh two blocks. -/
def selectedCoordinateEquiv (ι : Type*) (L r : ℕ) :
    ((ι ⊕ Fin L) ⊕ Fin r) ≃ (ι ⊕ Fin (L + r)) :=
  (Equiv.sumAssoc ι (Fin L) (Fin r)).trans ((Equiv.refl ι).sumCongr finSumFinEquiv)

lemma selectedCoordinateEquiv_pullback
    (p : Base ι × UnitAddTorus (Fin (L + r))) :
    (Sum.elim p.1.2 p.2) ∘ selectedCoordinateEquiv ι L r =
      Sum.elim (Sum.elim p.1.2 ((selectedFiberEquiv L r p.2).1))
        ((selectedFiberEquiv L r p.2).2) := by
  rw [selectedFiberEquiv_apply]
  funext i
  rcases i with (i | i) | i <;> rfl

/-- The ordered selected frequencies, with all fresh modes on the canonical flat torus. -/
def flatSelectedFrequency (i : Fin (n * (D.d + L))) : MixedFreq (ι ⊕ Fin (L + r)) :=
  padMixedFreq (selectedCoordinateEquiv ι L r).toEmbedding
    (D.selectedFrequency S.toData
      ((finProdFinEquiv : Fin n × Fin (D.d + L) ≃ Fin (n * (D.d + L))).symm i))

lemma flatSelectedFrequency_raw
    (i : Fin (n * (D.d + L))) (p : Base ι × UnitAddTorus (Fin (L + r))) :
    directionalRaw (D.flatSelectedFrequency S i) p =
      D.rawSelectedTail S.toData i (p.1, selectedFiberEquiv L r p.2) := by
  unfold directionalRaw flatSelectedFrequency
  rw [mixedChar_padMixedFreq]
  change mixedChar _ (p.1.1, (Sum.elim p.1.2 p.2) ∘ selectedCoordinateEquiv ι L r) = _
  rw [selectedCoordinateEquiv_pullback p, D.eval_selectedFrequency]
  rfl

lemma flatSelectedFrequency_fresh (i : Fin (n * (D.d + L))) :
    (fun j => (D.flatSelectedFrequency S i).2 (Sum.inr j)) ≠ 0 := by
  obtain ⟨⟨k, l⟩, rfl⟩ :=
    (finProdFinEquiv : Fin n × Fin (D.d + L) ≃ Fin (n * (D.d + L))).surjective i
  intro h
  apply S.mode_ne_zero k
  funext j
  have hj := congrFun h (Fin.natAdd L j)
  simp only [flatSelectedFrequency, Equiv.symm_apply_apply, padMixedFreq, Pi.zero_apply] at hj
  have harg : (selectedCoordinateEquiv ι L r).toEmbedding (Sum.inr j) =
      Sum.inr (Fin.natAdd L j) := rfl
  rw [← harg, padMode_at, D.selectedFrequency_scalar] at hj
  exact hj

lemma flatSelectedFrequency_aux_injective
    (hD : Injective (fun i => (D.frequencies i).2)) :
    Injective (fun i : Fin (n * (D.d + L)) => (D.flatSelectedFrequency S i).2) :=
  (padMode_injective _).comp ((D.selectedFrequency_aux_injective S.toData hD).comp
    (finProdFinEquiv : Fin n × Fin (D.d + L) ≃ Fin (n * (D.d + L))).symm.injective)

lemma flatSelectedFrequency_real (i : Fin (n * (D.d + L))) :
    (D.flatSelectedFrequency S i).1 = 0 ∨
      ∃ j, (D.flatSelectedFrequency S i).1 = (D.frequencies j).1 :=
  D.selectedFrequency_real S.toData _

set_option maxHeartbeats 1600000 in
/-- Transport a certified selected packet from the two product blocks to the canonical torus. -/
def assembleSelectedPacket (Ks : ℝ) {gain leak : ℝ} (hgain : 0 < gain) (hleak : 0 ≤ leak)
    (leakOp : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) (hleakOp : ‖leakOp‖ ≤ 1)
    (hIndep : LinearIndependent ℂ (D.selectedAugmented hm hm' S.toData))
    (hPB : PB (D.selectedTailSynthesis hm hm' S.toData).centeredGram
      (Real.sqrt (selectedPrefixSq Ks D.K S.loss)))
    (hInfo : (D.selectedTailSynthesis hm hm' S.toData).information =
      gain • InnerProductSpace.rankOne ℂ (synth (productFamily ρ D.frequencies) D.coeff)
        (synth (productFamily ρ D.frequencies) D.coeff) + leak • leakOp) :
    SelectedPacket D Ks S.loss := by
  let W := (D.seedFiber L hm hm').selected S.toData
  let e := selectedFiberEquiv L r
  let he := measurePreserving_selectedFiberEquiv L r
  let V := W.pullFiber e he
  let f := D.flatSelectedFrequency (L := L) S
  let p := padMixedPoly (selectedCoordinateEquiv ι L r).toEmbedding (D.selectedPoly L m S)
  let U := D.rawSelectedTail (L := L) S.toData
  let U' := fun i => directionalRaw (f i)
  have hu (i) : Measurable (U i) := D.measurable_rawSelectedTail S.toData i
  have hv (i) : Measurable (U' i) := measurable_directionalRaw _
  let B := fun _ : Fin (n * (D.d + L)) => (1 : ℝ)
  have huB (i p) : ‖U i p‖ ≤ B i := (D.norm_rawSelectedTail S.toData i p).le
  have hvB (i p) : ‖U' i p‖ ≤ B i := (norm_directionalRaw _ p).le
  have hu' := D.flatSelectedFrequency_raw (L := L) S
  let Synth := directionalSynthesis ρ V f
  have hmEq : Synth.means = (D.selectedTailSynthesis hm hm' S.toData).means :=
    FiberWeight.synthesis_means_pullFiber W ρ e he hu hv B huB hvB hu'
  have hgEq : Synth.centeredGram = (D.selectedTailSynthesis hm hm' S.toData).centeredGram :=
    FiberWeight.synthesis_centeredGram_pullFiber W ρ e he hu hv B huB hvB hu'
  have hJ : Synth.information = (D.selectedTailSynthesis hm hm' S.toData).information :=
    FiberWeight.synthesis_information_pullFiber W ρ e he hu hv B huB hvB hu'
  have hInj : Injective Synth.centered :=
    FiberWeight.synthesis_centered_injective_pullFiber W ρ e he hu hv B huB hvB hu'
      (D.selectedTail_centered_injective hm hm' S.toData hIndep)
  refine {
    r := L + r
    n := n * (D.d + L)
    nonempty_family := Nat.mul_pos S.size_pos (by have := D.d_pos; omega)
    W := V
    lower := S.lower
    lower_pos := S.lower_pos
    lower_le := fun x => FiberWeight.selected_lower _ S.toData (x.1, e x.2)
    poly := p
    eval_poly := ?_
    freq := f
    fresh_ne_zero := D.flatSelectedFrequency_fresh S
    aux_injective := D.flatSelectedFrequency_aux_injective S
    real_frequency := D.flatSelectedFrequency_real S
    means_range := ?_
    centered_injective := hInj
    gain := gain
    gain_pos := hgain
    leak := leak
    leak_nonneg := hleak
    leakOp := leakOp
    leakOp_norm := hleakOp
    centered_pb := ?_
    information_eq := ?_
  }
  · intro x
    unfold p
    rw [eval_padMixedPoly]
    change evalMixedPoly _ (x.1.1, (Sum.elim x.1.2 x.2) ∘ selectedCoordinateEquiv ι L r) = _
    rw [selectedCoordinateEquiv_pullback x, D.eval_selectedPoly L hm hm']
    rfl
  · change Synth.means.toLinearMap.range ≤ _
    rw [hmEq]
    exact D.selectedTail_means_range hm hm' S.toData
  · change PB Synth.centeredGram _
    exact hgEq.symm ▸ hPB
  · change Synth.information = _
    exact hJ.trans hInfo


lemma assembleSelectedPacket_mass (Ks : ℝ) {gain leak : ℝ}
    (hgain : 0 < gain) (hleak : 0 ≤ leak)
    (leakOp : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ) (hleakOp : ‖leakOp‖ ≤ 1)
    (hIndep : LinearIndependent ℂ (D.selectedAugmented hm hm' S.toData))
    (hPB : PB (D.selectedTailSynthesis hm hm' S.toData).centeredGram
      (Real.sqrt (selectedPrefixSq Ks D.K S.loss)))
    (hInfo : (D.selectedTailSynthesis hm hm' S.toData).information =
      gain • InnerProductSpace.rankOne ℂ (synth (productFamily ρ D.frequencies) D.coeff)
        (synth (productFamily ρ D.frequencies) D.coeff) + leak • leakOp) :
    (D.assembleSelectedPacket hm hm' S Ks hgain hleak leakOp hleakOp hIndep hPB hInfo).W.mass =
      1 - (1 - m) * S.loss := by
  change ((D.seedFiber L hm hm').selected S.toData).mass = _
  exact FiberWeight.selected_mass _ _

end

end SchauderBasisOrbits.DirectionalInput
