module

public import LeanCode.Directional.AmplifiedOutput
public import LeanCode.Measure.FiberTransport
public import LeanCode.Measure.PiSynthesis

@[expose] public section

open Function MeasureTheory Submodule
open scoped BigOperators ENNReal ComplexOrder

namespace SchauderBasisOrbits

noncomputable section

variable {ι : Type*} [Fintype ι] {ρ : Measure (ℝ × UnitAddTorus ι)} [IsFiniteMeasure ρ]
variable {D : DirectionalInput ρ} {Ks ε : ℝ} (P : SelectedPacket D Ks ε)

lemma copySize_eq (N n : ℕ) : (∑ _ : Fin N, n) = N * n := by
  simp [nsmul_eq_mul]

private lemma finCongr_finSigmaFinEquiv_copySize {N n : ℕ} (b : Fin N) (i : Fin n) :
    finCongr (copySize_eq N n) (finSigmaFinEquiv (n := fun _ : Fin N => n) ⟨b, i⟩) =
      finProdFinEquiv (b, i) := by
  apply Fin.ext
  rw [finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply]
  change (∑ _ : Fin b.val, n) + i.val = i.val + n * b.val
  simp [nsmul_eq_mul, add_comm, mul_comm]

def selectedRawFamily :
    FiberFamily (ℝ × UnitAddTorus ι) (UnitAddTorus (Fin P.r)) P.n where
  value i := directionalRaw (P.freq i)
  measurable i := measurable_directionalRaw _
  norm_le i p := (norm_directionalRaw _ p).le

def copiedFreq (N : ℕ) (i : Fin (∑ _ : Fin N, P.n)) : MixedFreq (ι ⊕ Fin (N * P.r)) :=
  directionalCopyFrequencies N P.toDirectionalFamily (finCongr (copySize_eq N P.n) i)

theorem copiedFreq_raw_eq (N : ℕ) (i : Fin (∑ _ : Fin N, P.n))
    (p : (ℝ × UnitAddTorus ι) × UnitAddTorus (Fin (N * P.r))) :
    directionalRaw (copiedFreq P N i) p =
      (FiberFamily.combine (fun _ : Fin N => selectedRawFamily P)).value i
        (p.1, Scalar.copyPointEquiv N p.2) := by
  obtain ⟨⟨b, k⟩, rfl⟩ := finSigmaFinEquiv.surjective i
  rw [copiedFreq, finCongr_finSigmaFinEquiv_copySize, directionalCopyFrequencies_apply,
    directionalRaw_copy, Scalar.copyPointEquiv_apply]
  change _ = orderedDependentBlocks (fun (b : Fin N) k
    (p : (ℝ × UnitAddTorus ι) × (Fin N → UnitAddTorus (Fin P.r))) =>
      (selectedRawFamily P).value k (p.1, p.2 b)) (finSigmaFinEquiv ⟨b, k⟩) _
  rw [orderedDependentBlocks_apply]
  rfl

/-- Independent copies preserve the centered prefix bound and add their information
operators, on the unchanged base probability and the canonical flat fresh torus. -/
def amplifySelectedPacket (N : ℕ) (hN : 0 < N) : AmplifiedFamily P N := by
  let U := fun _ : Fin N => selectedRawFamily P
  let W := fun _ : Fin N => P.W
  let U' := FiberFamily.combine U
  let W' := FiberWeight.pi W
  let e := Scalar.copyPointEquiv (r := P.r) N
  let he := Scalar.measurePreserving_copyPointEquiv (r := P.r) N
  let V := directionalCopyWeight N P.W
  let f := copiedFreq P N
  let S := directionalSynthesis ρ V f
  let B : Fin (∑ _ : Fin N, P.n) → ℝ := fun _ => 1
  have hv (i) : Measurable (directionalRaw (f i)) := measurable_directionalRaw _
  have hvB (i p) : ‖directionalRaw (f i) p‖ ≤ B i := (norm_directionalRaw _ _).le
  have hRaw := copiedFreq_raw_eq P N
  have hmeans : S.means = (U'.synthesis W' ρ).means :=
    FiberWeight.synthesis_means_pullFiber W' ρ e he U'.measurable hv B U'.norm_le hvB hRaw
  have hC : S.centeredGram = (U'.synthesis W' ρ).centeredGram :=
    FiberWeight.synthesis_centeredGram_pullFiber W' ρ e he U'.measurable hv B U'.norm_le hvB hRaw
  have hInf : S.information = (U'.synthesis W' ρ).information :=
    FiberWeight.synthesis_information_pullFiber W' ρ e he U'.measurable hv B U'.norm_le hvB hRaw
  have hInj : Injective S.centered :=
    FiberWeight.synthesis_centered_injective_pullFiber W' ρ e he U'.measurable hv B U'.norm_le hvB hRaw
      (FiberFamily.combine_centered_injective U W ρ (fun _ => P.centered_injective))
  have hRange : S.means.toLinearMap.range ≤ span ℂ (Set.range (productFamily ρ D.frequencies)) := by
    rw [hmeans]
    exact FiberFamily.combine_means_range U W ρ _ (fun _ => P.means_range)
  refine {
    r := N * P.r
    n := ∑ _ : Fin N, P.n
    nonempty_family := by rw [copySize_eq]; exact Nat.mul_pos hN P.nonempty_family
    W := V
    lower := P.lower ^ N
    lower_pos := pow_pos P.lower_pos N
    lower_le := directionalCopyWeight_lower N P.W P.lower_pos.le P.lower_le
    poly := directionalCopyPoly N P.poly
    eval_poly := eval_directionalCopyPoly N P.poly P.W P.eval_poly
    freq := f
    fresh_ne_zero := fun i => directionalCopyFrequencies_fresh N P.toDirectionalFamily _
    aux_injective := fun h => (directionalCopyFrequencies_aux_injective N P.toDirectionalFamily h).comp
      (finCongr (copySize_eq N P.n)).injective
    real_frequency := fun i => directionalCopyFrequencies_real N P.toDirectionalFamily _
    means_range := hRange
    centered_injective := hInj
    mass_eq := directionalCopyWeight_mass N P.W
    centered_pb := ?_
    information_eq := ?_
  }
  · change PB S.centeredGram _
    rw [hC]
    exact FiberFamily.combine_centered_pb U W ρ _ (Real.sqrt_nonneg _) (fun _ => P.centered_pb)
  · change S.information = _
    rw [hInf, FiberFamily.combine_information_eq_sum U W ρ (fun _ => P.centered_injective)]
    change (∑ _ : Fin N, (directionalSynthesis ρ P.W P.freq).information) = _
    simp [Nat.cast_smul_eq_nsmul]

end

end SchauderBasisOrbits
