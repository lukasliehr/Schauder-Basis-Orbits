import LeanCode.Construction.ProductAssembly
import LeanCode.Measure.PiSynthesis
import LeanCode.Directional.SupplyContract

open MeasureTheory Filter Function
open scoped BigOperators InnerProductSpace

noncomputable section

namespace SchauderBasisOrbits

abbrev ResidualLift.Coordinates {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {A : List ℚ} {q : ℚ} {u lossBudget : ℝ} (R : ResidualLift ρ A q u lossBudget) :=
  ResidualCopyIndex A R.count × Fin R.dim

abbrev ProductPackets {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {A : List ℚ} {q : ℚ} {u lossBudget : ℝ} (R : ResidualLift ρ A q u lossBudget) (η : ℝ) :=
  (i : Fin R.count) → DirectionalOutput (R.directions i) (1 + u) u η

namespace ProductPackets

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : List ℚ} {q : ℚ} {u lossBudget η : ℝ}
variable {R : ResidualLift ρ A q u lossBudget} (P : ProductPackets R η)

abbrev Fresh := Σ i : Fin R.count, Fin ((P i).r)

abbrev AllCoords := R.Coordinates ⊕ Fresh P

def dim : ℕ := Fintype.card (AllCoords P)

def coordinateEquiv : AllCoords P ≃ Fin (dim P) := Fintype.equivFin _

def inclusion (i : Fin R.count) : R.Coordinates ⊕ Fin ((P i).r) ↪ AllCoords P :=
  (Function.Embedding.refl _).sumMap (Function.Embedding.sigmaMk (β := fun i ↦ Fin (P i).r) i)

def groupedWeight :
    FiberWeight (ℝ × UnitAddTorus R.Coordinates)
      (Measure.pi fun i : Fin R.count ↦ torusHaar (Fin (P i).r)) :=
  FiberWeight.pi (fun i ↦ (P i).W)

def fiberEquiv : UnitAddTorus (Fin (dim P)) ≃ᵐ
    UnitAddTorus R.Coordinates × ((i : Fin R.count) → UnitAddTorus (Fin (P i).r)) :=
  (torusReindex (coordinateEquiv P).symm).trans
    ((torusSplit (ι := R.Coordinates) (κ := Fresh P)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.piCurry (fun (i : Fin R.count) (_ : Fin (P i).r) ↦ UnitAddCircle))))

theorem fiberEquiv_apply (y : UnitAddTorus (Fin (dim P))) :
    fiberEquiv P y = ((fun k ↦ y (coordinateEquiv P (Sum.inl k))),
      (fun i k ↦ y (coordinateEquiv P (Sum.inr ⟨i, k⟩)))) := by
  unfold fiberEquiv
  simp only [MeasurableEquiv.trans_apply, torusReindex_apply]
  rfl

theorem measurePreserving_fiberEquiv :
    MeasurePreserving (fiberEquiv P) (torusHaar (Fin (dim P)))
      ((torusHaar R.Coordinates).prod (Measure.pi fun i : Fin R.count ↦ torusHaar (Fin (P i).r))) := by
  let e := MeasurableEquiv.piCurry (fun (i : Fin R.count) (_ : Fin (P i).r) ↦ UnitAddCircle)
  have he : MeasurePreserving e (torusHaar (Fresh P))
      (Measure.pi fun i : Fin R.count ↦ torusHaar (Fin (P i).r)) :=
    measurePreserving_piCurry_const _ _ _ AddCircle.haarAddCircle
  have hprod : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e)
      ((torusHaar R.Coordinates).prod (torusHaar (Fresh P)))
      ((torusHaar R.Coordinates).prod (Measure.pi fun i : Fin R.count ↦ torusHaar (Fin (P i).r))) := by
    refine ⟨(MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e).measurable, ?_⟩
    change Measure.map (Prod.map id e) _ = _
    rw [← Measure.map_prod_map _ _ measurable_id he.measurable, Measure.map_id, he.map_eq]
  exact hprod.comp (measurePreserving_torusSplit (ι := R.Coordinates) (κ := Fresh P))
    |>.comp (measurePreserving_torusReindex (coordinateEquiv P).symm)

/-- The normalized combined weight on the final canonical torus. -/
def flatWeight : FiberWeight ℝ (torusHaar (Fin (dim P))) :=
  (R.weight.nested (groupedWeight P)).pullFiber (fiberEquiv P) (measurePreserving_fiberEquiv P)

def flatToGrouped : (ℝ × UnitAddTorus (Fin (dim P))) ≃ᵐ
    (ℝ × UnitAddTorus R.Coordinates) × ((i : Fin R.count) → UnitAddTorus (Fin (P i).r)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (fiberEquiv P)).trans
    MeasurableEquiv.prodAssoc.symm

theorem flatToGrouped_apply (p : ℝ × UnitAddTorus (Fin (dim P))) :
    flatToGrouped P p =
      ((p.1, fun k ↦ p.2 (coordinateEquiv P (Sum.inl k))),
        fun i k ↦ p.2 (coordinateEquiv P (Sum.inr ⟨i, k⟩))) := by
  change ((p.1, (fiberEquiv P p.2).1), (fiberEquiv P p.2).2) = _
  rw [fiberEquiv_apply]

theorem measurePreserving_flatToGrouped :
    MeasurePreserving (flatToGrouped P) ((flatWeight P).normalizedMeasure ρ)
      ((groupedWeight P).normalizedMeasure (R.weight.normalizedMeasure ρ)) :=
  ((R.weight.measurePreserving_nested ρ (groupedWeight P)).symm MeasurableEquiv.prodAssoc).comp
    ((R.weight.nested (groupedWeight P)).measurePreserving_pullFiber ρ
      (fiberEquiv P) (measurePreserving_fiberEquiv P))

private def paddedPolynomial : MixedPoly (AllCoords P) :=
  padMixedPoly Function.Embedding.inl R.poly *
    ∏ i, padMixedPoly (inclusion P i) (P i).poly

def flatPolynomial : MixedPoly (Fin (dim P)) :=
  padMixedPoly (coordinateEquiv P).toEmbedding (paddedPolynomial P)


private theorem flatWeight_apply (p : ℝ × UnitAddTorus (Fin (dim P))) :
    (flatWeight P).weight p =
      R.weight.weight (p.1, fun k ↦ p.2 (coordinateEquiv P (Sum.inl k))) *
      ∏ i, (P i).W.weight ((p.1, fun k ↦ p.2 (coordinateEquiv P (Sum.inl k))),
        fun k ↦ p.2 (coordinateEquiv P (Sum.inr ⟨i, k⟩))) := by
  change (R.weight.nested (groupedWeight P)).weight (p.1, fiberEquiv P p.2) = _
  rw [fiberEquiv_apply]
  rfl

private theorem padded_eval_packet (i : Fin R.count) (p : ℝ × UnitAddTorus (Fin (dim P))) :
    evalMixedPoly (padMixedPoly (inclusion P i) (P i).poly)
        (p.1, p.2 ∘ (coordinateEquiv P).toEmbedding) =
      (↑((P i).W.weight ((p.1, fun k ↦ p.2 (coordinateEquiv P (Sum.inl k))),
        fun k ↦ p.2 (coordinateEquiv P (Sum.inr ⟨i, k⟩)))) : ℂ) := by
  rw [eval_padMixedPoly]
  let x := fun k : R.Coordinates ↦ p.2 (coordinateEquiv P (Sum.inl k))
  let y := fun k : Fin (P i).r ↦ p.2 (coordinateEquiv P (Sum.inr ⟨i, k⟩))
  have heq :
      (p.2 ∘ (coordinateEquiv P).toEmbedding) ∘ inclusion P i = Sum.elim x y := by
    funext z
    cases z <;> rfl
  change evalMixedPoly (P i).poly (p.1, (p.2 ∘ (coordinateEquiv P).toEmbedding) ∘ inclusion P i) = _
  rw [heq]
  exact (P i).eval_poly ((p.1, x), y)

theorem flatPolynomial_eval (p : ℝ × UnitAddTorus (Fin (dim P))) :
    evalMixedPoly (flatPolynomial P) p = ((flatWeight P).weight p : ℂ) := by
  rw [flatPolynomial, eval_padMixedPoly, paddedPolynomial, evalMixedPoly_mul, flatWeight_apply,
    Complex.ofReal_mul, Complex.ofReal_prod]
  let z : ℝ × UnitAddTorus (AllCoords P) := (p.1, p.2 ∘ (coordinateEquiv P).toEmbedding)
  have hprod := map_prod (mixedEvalHom z) (fun i ↦ padMixedPoly (inclusion P i) (P i).poly) Finset.univ
  simp only [mixedEvalHom_apply] at hprod
  rw [hprod, eval_padMixedPoly]
  congr 1
  · exact R.eval_poly (p.1, fun k ↦ p.2 (coordinateEquiv P (Sum.inl k)))
  · exact Finset.prod_congr rfl fun i _ ↦ padded_eval_packet P i p

def graphWeight : GraphWeight (Fin (dim P)) where
  toFun := (flatWeight P).weight
  poly := flatPolynomial P
  eval_eq := flatPolynomial_eval P
  positive := (flatWeight P).weight_pos
  le_one := (flatWeight P).weight_le_one

theorem flatWeight_loss_le :
    1 - (flatWeight P).mass ≤
      (1 - R.weight.mass) + ∑ i, (1 - (P i).W.mass) := by
  change 1 - R.weight.mass * (groupedWeight P).mass ≤ _
  have h₁ : 0 ≤ 1 - R.weight.mass := sub_nonneg.mpr (R.weight.mass_le_one (0 : ℝ))
  have h₂ : 0 ≤ 1 - (groupedWeight P).mass :=
    sub_nonneg.mpr ((groupedWeight P).mass_le_one (0, 0))
  have h₃ := FiberWeight.pi_mass_loss_le (fun i ↦ (P i).W) (0, 0)
  change 1 - (groupedWeight P).mass ≤ _ at h₃
  nlinarith [mul_nonneg h₁ h₂]

def freq : Fin (∑ i, (P i).n) → MixedFreq (Fin (dim P)) :=
  orderedDependentBlocks (fun i k ↦
    padMixedFreq (coordinateEquiv P).toEmbedding (padMixedFreq (inclusion P i) ((P i).freq k)))

def rawFamilies (i : Fin R.count) :
    FiberFamily (ℝ × UnitAddTorus R.Coordinates) (UnitAddTorus (Fin (P i).r)) (P i).n :=
  ⟨fun k ↦ directionalRaw ((P i).freq k), fun k ↦ measurable_directionalRaw _,
    fun k p ↦ (norm_directionalRaw ((P i).freq k) p).le⟩

theorem rawFamilies_synthesis (i : Fin R.count) :
    ((rawFamilies P) i).synthesis (P i).W (R.weight.normalizedMeasure ρ) =
      directionalSynthesis (R.weight.normalizedMeasure ρ) (P i).W (P i).freq := rfl

theorem eval_freq_eq_groupedRaw (l : Fin (∑ i, (P i).n)) (p : ℝ × UnitAddTorus (Fin (dim P))) :
    mixedChar (freq P l) p = (FiberFamily.combine (rawFamilies P)).value l (flatToGrouped P p) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective l
  rw [freq, orderedDependentBlocks_apply, mixedChar_padMixedFreq, mixedChar_padMixedFreq,
    FiberFamily.combine_value, flatToGrouped_apply]
  change mixedChar ((P i).freq j) (p.1, _) =
    mixedChar ((P i).freq j) (p.1, Sum.elim (fun k ↦ p.2 (coordinateEquiv P (Sum.inl k)))
      (fun k ↦ p.2 (coordinateEquiv P (Sum.inr ⟨i, k⟩))))
  congr 2
  funext s
  cases s <;> rfl

theorem size_pos : 0 < ∑ i, (P i).n := by
  let i : Fin R.count := ⟨0, R.count_pos⟩
  exact (P i).nonempty_family.trans_le
    (Finset.single_le_sum (f := fun j ↦ (P j).n) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))

private theorem inclusion_not_other {i j : Fin R.count} (h : i ≠ j) (k : Fin (P i).r) :
    (Sum.inr ⟨i, k⟩ : AllCoords P) ∉ Set.range (inclusion P j) := by
  rintro ⟨l, hl⟩
  cases l with
  | inl l => simp [inclusion] at hl
  | inr l =>
    have h' : (⟨j, l⟩ : Fresh P) = ⟨i, k⟩ := Sum.inr.inj hl
    exact h (congrArg Sigma.fst h').symm

theorem freq_aux_nonzero (l : Fin (∑ i, (P i).n)) : (freq P l).2 ≠ 0 := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective l
  rw [freq, orderedDependentBlocks_apply]
  intro h
  apply (P i).fresh_ne_zero j
  funext k
  have hk := congrFun h ((coordinateEquiv P).toEmbedding (inclusion P i (Sum.inr k)))
  simpa only [padMixedFreq, padMode_at, Pi.zero_apply] using hk

theorem freq_aux_injective : Function.Injective (fun l ↦ (freq P l).2) := by
  intro l m h
  obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective l
  obtain ⟨⟨j, b⟩, rfl⟩ := finSigmaFinEquiv.surjective m
  simp only [freq, orderedDependentBlocks_apply, padMixedFreq] at h
  have h₁ := padMode_injective (coordinateEquiv P).toEmbedding h
  by_cases hij : i = j
  · subst j
    have h₂ := padMode_injective (inclusion P i) h₁
    exact congrArg (fun k ↦ finSigmaFinEquiv ⟨i, k⟩)
      ((P i).aux_injective (R.direction_modes_injective i) h₂)
  · exfalso
    apply (P i).fresh_ne_zero a
    funext k
    have h₂ := congrFun h₁ (inclusion P i (Sum.inr k))
    rw [padMode_at, padMode_off _ _ (show inclusion P i (Sum.inr k) ∉ Set.range (inclusion P j)
      from inclusion_not_other P hij k)] at h₂
    exact h₂

def groupedSynthesis :
    CenteredSynthesis (Lp ℂ 2 (R.weight.normalizedMeasure ρ))
      (Lp ℂ 2 ((groupedWeight P).normalizedMeasure (R.weight.normalizedMeasure ρ)))
      (∑ i, (P i).n) :=
  (FiberFamily.combine (rawFamilies P)).synthesis (groupedWeight P) (R.weight.normalizedMeasure ρ)

def flatTransport : Lp ℂ 2 ((groupedWeight P).normalizedMeasure (R.weight.normalizedMeasure ρ))
    →ₗᵢ[ℂ] Lp ℂ 2 ((flatWeight P).normalizedMeasure ρ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (flatToGrouped P) (measurePreserving_flatToGrouped P)

theorem ae_flatTransport (f : Lp ℂ 2 ((groupedWeight P).normalizedMeasure (R.weight.normalizedMeasure ρ))) :
    ⇑(flatTransport P f) =ᵐ[(flatWeight P).normalizedMeasure ρ] ⇑f ∘ flatToGrouped P :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_flatToGrouped P)

def flatSynthesis :
    CenteredSynthesis (Lp ℂ 2 (R.weight.normalizedMeasure ρ))
      (Lp ℂ 2 ((flatWeight P).normalizedMeasure ρ)) (∑ i, (P i).n) :=
  (groupedSynthesis P).mapTarget (flatTransport P)

theorem flatSynthesis_full :
    (flatSynthesis P).full = synthCLM (productFamily ((flatWeight P).normalizedMeasure ρ) (freq P)) := by
  unfold flatSynthesis
  rw [CenteredSynthesis.mapTarget_full]
  change (flatTransport P).toContinuousLinearMap ∘L
    (((groupedWeight P).synthesis (R.weight.normalizedMeasure ρ)
      (FiberFamily.combine (rawFamilies P)).value
      (FiberFamily.combine (rawFamilies P)).measurable (fun _ ↦ 1)
      (FiberFamily.combine (rawFamilies P)).norm_le).full) = _
  rw [FiberWeight.synthesis_full]
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.comp_apply, synthCLM_apply, synthCLM_apply]
  change flatTransport P (synth _ (WithLp.ofLp c)) = _
  simp only [synth, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  let f := (FiberFamily.combine (rawFamilies P)).value l
  let h := lift₂ ((groupedWeight P).normalizedMeasure (R.weight.normalizedMeasure ρ))
    f ((FiberFamily.combine (rawFamilies P)).measurable l) 1 ((FiberFamily.combine (rawFamilies P)).norm_le l)
  apply Lp.ext
  have hae : ⇑h =ᵐ[(groupedWeight P).normalizedMeasure (R.weight.normalizedMeasure ρ)] f :=
    ae_lift₂ _ _ _ _ _
  refine (ae_flatTransport P h).trans ?_
  refine ((measurePreserving_flatToGrouped P).quasiMeasurePreserving.ae_eq_comp hae).trans ?_
  refine Filter.EventuallyEq.trans ?_ (ae_lift₂ _ _ _ _ _).symm
  exact Eventually.of_forall fun p ↦ (eval_freq_eq_groupedRaw P l p).symm

theorem flatSynthesis_lift_base (t : ℚ) :
    (flatSynthesis P).pullback (R.weight.pullback ρ (realCharLp ρ t)) =
      productBaseVector ((flatWeight P).normalizedMeasure ρ) t := by
  let f := R.weight.pullback ρ (realCharLp ρ t)
  let g := (groupedWeight P).pullback (R.weight.normalizedMeasure ρ) f
  change flatTransport P g = _
  apply Lp.ext
  refine (ae_flatTransport P g).trans ?_
  apply Filter.EventuallyEq.trans _ (ae_productBaseVector _ t).symm
  have hf : ⇑f =ᵐ[R.weight.normalizedMeasure ρ] fun p ↦ realChar t p.1 :=
    (R.weight.ae_pullback ρ (realCharLp ρ t)).trans
      ((R.weight.measurePreserving_fst ρ).quasiMeasurePreserving.ae_eq_comp (ae_realCharLp ρ t))
  have hg : ⇑g =ᵐ[(groupedWeight P).normalizedMeasure (R.weight.normalizedMeasure ρ)]
      fun p ↦ realChar t p.1.1 :=
    ((groupedWeight P).ae_pullback (R.weight.normalizedMeasure ρ) f).trans
      (((groupedWeight P).measurePreserving_fst (R.weight.normalizedMeasure ρ)).quasiMeasurePreserving.ae_eq_comp hf)
  refine ((measurePreserving_flatToGrouped P).quasiMeasurePreserving.ae_eq_comp hg).trans ?_
  exact Eventually.of_forall (fun p ↦ by rw [Function.comp_apply, flatToGrouped_apply])

theorem grouped_centered_injective :
    Function.Injective (groupedSynthesis P).centered :=
  FiberFamily.combine_centered_injective _ _ _
    (fun i ↦ (rawFamilies_synthesis P i).symm ▸ (P i).centered_injective)

theorem flat_centered_injective : Function.Injective (flatSynthesis P).centered :=
  (groupedSynthesis P).mapTarget_centered_injective (flatTransport P) (grouped_centered_injective P)

theorem flatSynthesis_information :
    (flatSynthesis P).information = ∑ i, (directionalSynthesis (R.weight.normalizedMeasure ρ)
      (P i).W (P i).freq).information := by
  rw [flatSynthesis, CenteredSynthesis.mapTarget_information]
  have h := FiberFamily.combine_information_eq_sum (rawFamilies P) (fun i ↦ (P i).W)
    (R.weight.normalizedMeasure ρ) (fun i ↦ (rawFamilies_synthesis P i).symm ▸ (P i).centered_injective)
  simpa only [groupedSynthesis, groupedWeight, rawFamilies_synthesis] using h

private theorem residualInformation_eq_sum_rankOne {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {n : ℕ} (a : ℝ) (v : Fin n → E) :
    residualInformation a v = ∑ i, a • InnerProductSpace.rankOne ℂ (v i) (v i) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [residualInformation_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, Finset.smul_sum]

theorem information_error :
    ‖(flatSynthesis P).information - R.information‖ ≤ (R.count : ℝ) * η := by
  rw [flatSynthesis_information, ResidualLift.information, residualInformation_eq_sum_rankOne,
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin R.count, η := Finset.sum_le_sum (fun i _ ↦ (P i).information_error.le)
    _ = _ := by simp [nsmul_eq_mul]

end ProductPackets

end SchauderBasisOrbits
