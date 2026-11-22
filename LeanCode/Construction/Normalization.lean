module

public import LeanCode.Construction.LineStep
public import LeanCode.Measure.Products

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace MatrixOrder ComplexOrder

namespace SchauderBasisOrbits

noncomputable section

namespace LineWeight

variable (v : LineWeight) (μ : Measure ℝ) [IsFiniteMeasure μ]

def finiteMeasure : FiniteMeasure ℝ := ⟨v.measure μ, inferInstance⟩

def mass : ℝ := (v.finiteMeasure μ).mass

def normalize : ProbabilityMeasure ℝ := (v.finiteMeasure μ).normalize

theorem mass_pos (hμ : μ ≠ 0) : 0 < v.mass μ := by
  have h : v.finiteMeasure μ ≠ 0 := fun h => v.measure_ne_zero hμ
    (congrArg FiniteMeasure.toMeasure h)
  exact_mod_cast pos_iff_ne_zero.mpr ((v.finiteMeasure μ).mass_ne_zero_iff.mpr h)

theorem measure_eq_mass_smul_normalize :
    v.measure μ = ENNReal.ofReal (v.mass μ) • (v.normalize μ).toMeasure := by
  have h := congrArg FiniteMeasure.toMeasure (v.finiteMeasure μ).self_eq_mass_smul_normalize
  rw [FiniteMeasure.toMeasure_smul] at h
  rw [mass, ENNReal.ofReal_coe_nnreal]
  exact h

theorem normalize_nullSingletonClass [NullSingletonClass μ] (hμ : μ ≠ 0) :
    NullSingletonClass (v.normalize μ).toMeasure := by
  have hν : v.finiteMeasure μ ≠ 0 := fun h => v.measure_ne_zero hμ
    (congrArg FiniteMeasure.toMeasure h)
  refine ⟨fun x => ?_⟩
  rw [normalize, FiniteMeasure.toMeasure_normalize_eq_of_ne_zero _ hν]
  change ((v.finiteMeasure μ).mass⁻¹ • (v.measure μ)) {x} = 0
  simp

theorem integral_measure_eq_mass_smul_normalize {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x, f x ∂v.measure μ = v.mass μ • ∫ x, f x ∂(v.normalize μ).toMeasure := by
  rw [v.measure_eq_mass_smul_normalize μ, integral_smul_measure,
    ENNReal.toReal_ofReal (by unfold mass; positivity)]

theorem prefix_normalize (hμ : μ ≠ 0) (a : List ℚ) {K : ℝ}
    (h : HPrefix (𝕜 := ℂ) (realFamily (v.measure μ) a) K) :
    HPrefix (𝕜 := ℂ) (realFamily (v.normalize μ).toMeasure a) K := by
  have hG : Matrix.gram ℂ (realFamily (v.measure μ) a) =
      (v.mass μ) • Matrix.gram ℂ (realFamily (v.normalize μ).toMeasure a) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.smul_apply, Matrix.gram_apply]
    change ⟪realCharLp (v.measure μ) _, realCharLp (v.measure μ) _⟫_ℂ =
      v.mass μ • ⟪realCharLp (v.normalize μ).toMeasure _, realCharLp (v.normalize μ).toMeasure _⟫_ℂ
    rw [inner_realCharLp, inner_realCharLp, integral_measure_eq_mass_smul_normalize]
  rw [hPrefix_iff_pb, hG] at h
  rw [hPrefix_iff_pb]
  refine ⟨h.1, fun k hk c => ?_⟩
  have hq := h.2 k hk c
  simp only [qform_smul] at hq
  apply le_of_mul_le_mul_left _ (v.mass_pos μ hμ)
  simpa only [mul_left_comm (v.mass μ)] using hq

end LineWeight

@[simp] theorem one_measure (μ : Measure ℝ) : LineWeight.one.measure μ = μ := by
  change μ.withDensity (fun _ => ENNReal.ofReal (1 : ℝ)) = μ
  simp

theorem weighted_residual_integral_normalize (v : LineWeight) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : List ℚ) (q : ℚ) (c : Fin a.length → ℂ) :
    (∫ x, v x * ‖realChar (q : ℝ) x - realSynth a c x‖ ^ 2 ∂μ) =
      v.mass μ * ∫ x, ‖realChar (q : ℝ) x - realSynth a c x‖ ^ 2 ∂(v.normalize μ).toMeasure := by
  calc
    _ = ∫ x, ‖realChar (q : ℝ) x - realSynth a c x‖ ^ 2 ∂v.measure μ :=
      (integral_weightedMeasure μ v.measurable_toFun
        (Eventually.of_forall fun x => (v.positive x).le) _).symm
    _ = _ := v.integral_measure_eq_mass_smul_normalize μ _

theorem lineDistanceSq_normalize (v : LineWeight) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : List ℚ) (q : ℚ) :
    lineDistanceSq μ v a q = v.mass μ * lineDistanceSq (v.normalize μ).toMeasure LineWeight.one a q := by
  let ρ := (v.normalize μ).toMeasure
  obtain ⟨c, hc⟩ := lineDistanceSq_minimizer μ v a q
  obtain ⟨b, hb⟩ := lineDistanceSq_minimizer ρ LineWeight.one a q
  have hone (x : ℝ) : LineWeight.one x = 1 := rfl
  simp only [hone, one_mul] at hb
  change lineDistanceSq μ v a q = v.mass μ * lineDistanceSq ρ LineWeight.one a q
  apply le_antisymm
  · rw [hb]
    exact (lineDistanceSq_le_residual μ v a q b).trans_eq
      (weighted_residual_integral_normalize v μ a q b)
  · rw [hc, weighted_residual_integral_normalize]
    apply mul_le_mul_of_nonneg_left _ (by unfold LineWeight.mass; positivity)
    simpa only [show (fun x => (LineWeight.one : ℝ → ℝ) x) = fun _ => 1 from rfl, one_mul] using
      lineDistanceSq_le_residual ρ LineWeight.one a q c

variable {ι : Type*} [Fintype ι]

theorem GraphWeight.measure_eq_withDensity_prod (W : GraphWeight ι) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (v : LineWeight) :
    W.measure μ v = weightedMeasure ((v.measure μ).prod (torusHaar ι)) W.toFun := by
  unfold GraphWeight.measure LineWeight.measure weightedMeasure
  have hv : Measurable (fun z : ℝ × UnitAddTorus ι => ENNReal.ofReal (v z.1)) :=
    v.measurable_toFun.ennreal_ofReal.comp measurable_fst
  rw [prod_withDensity_left v.measurable_toFun.ennreal_ofReal,
    ← withDensity_mul (μ.prod (torusHaar ι)) hv W.continuous_toFun.measurable.ennreal_ofReal]
  congr with z
  rw [ENNReal.ofReal_mul (v.positive z.1).le]
  rfl

theorem GraphWeight.measure_eq_normalized_fiber (W : GraphWeight ι) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (v : LineWeight) (F : FiberWeight ℝ (torusHaar ι))
    (hW : W.toFun = F.weight) :
    W.measure μ v =
      (ENNReal.ofReal (v.mass μ * F.mass)) • F.normalizedMeasure (v.normalize μ).toMeasure := by
  rw [W.measure_eq_withDensity_prod μ v, v.measure_eq_mass_smul_normalize μ, Measure.prod_smul_left,
    FiberWeight.normalizedMeasure, weightedMeasure, weightedMeasure, hW, withDensity_smul_measure,
    ENNReal.ofReal_mul (by unfold LineWeight.mass; positivity), mul_smul, ← withDensity_smul _ F.measurable_density.ennreal_ofReal]
  congr 2
  funext z
  change ENNReal.ofReal (F.weight z) = ENNReal.ofReal F.mass * ENNReal.ofReal (F.density z)
  rw [← ENNReal.ofReal_mul F.mass_pos.le]
  congr 1
  unfold FiberWeight.density
  field_simp [F.mass_pos.ne']

theorem FiberWeight.integral_loss_prod (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : FiberWeight ℝ (torusHaar ι)) :
    ∫ z, 1 - F.weight z ∂μ.prod (torusHaar ι) = 1 - F.mass := by
  have hint : Integrable (fun z => 1 - F.weight z) (μ.prod (torusHaar ι)) :=
    Integrable.of_bound (measurable_const.sub F.measurable_weight).aestronglyMeasurable 1
      (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (sub_nonneg.mpr (F.weight_le_one z))]
        linarith [F.weight_pos z])
  rw [integral_prod _ hint]
  have heq (x : ℝ) : ∫ y, 1 - F.weight (x, y) ∂torusHaar ι = 1 - F.mass := by
    have hw : Integrable (fun y => F.weight (x, y)) (torusHaar ι) :=
      Integrable.of_bound (F.measurable_weight.comp measurable_prodMk_left).aestronglyMeasurable 1
        (Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (F.weight_pos _).le]; exact F.weight_le_one _)
    simp [integral_sub (integrable_const (1 : ℝ)) hw, F.fiber_mass]
  simp [heq]

/-- Product extension estimates with probability normalization left explicit. -/
structure NormalizedProductLineData (ρ : Measure ℝ) [IsFiniteMeasure ρ] (u : ℝ)
    (a : List ℚ) (q : ℚ) (K δ τ : ℝ) where
  r : ℕ
  n : ℕ
  n_pos : 0 < n
  B : Fin n → MixedFreq (Fin r)
  aux_ne_zero : ∀ i, (B i).2 ≠ 0
  aux_injective : Function.Injective (fun i => (B i).2)
  W : GraphWeight (Fin r)
  F : FiberWeight ℝ (torusHaar (Fin r))
  weight_eq : W.toFun = F.weight
  loss_lt : 1 - F.mass < δ
  Kp : ℝ
  Kp_lt : Kp < max K (linePrefixFloor u) + τ
  prefix_bound : HPrefix (𝕜 := ℂ) (productFamily (F.normalizedMeasure ρ) (appendedMixedFreq a B)) Kp
  independent : LinearIndependent ℂ (productFamily (F.normalizedMeasure ρ) (appendedMixedFreq a B))
  c : Fin (a.length + n) → ℂ
  residual_small :
    (∫ z, ‖evalMixedPoly (residualPoly (appendedMixedFreq a B) q c) z‖ ^ 2
      ∂F.normalizedMeasure ρ) < lineContraction u * lineDistanceSq ρ LineWeight.one a q

/-- The product estimate to establish on each singleton-null probability. -/
def NormalizedProductExtensionSupply (ρ : Measure ℝ) [IsFiniteMeasure ρ] : Prop :=
  ∀ (u : ℝ), 0 < u → u ≤ 1 / 100 → ∀ (a : List ℚ) (q : ℚ) (K δ τ : ℝ),
    a ≠ [] → a.Nodup → q ∉ a → 0 < δ → 0 < τ →
    HPrefix (𝕜 := ℂ) (realFamily ρ a) K → Nonempty (NormalizedProductLineData ρ u a q K δ τ)

theorem gram_productFamily_scale (ν : Measure (ℝ × UnitAddTorus ι))
    [IsFiniteMeasure ν] (ν' : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ν']
    {s : ℝ} (hs : 0 ≤ s) (hν : ν' = ENNReal.ofReal s • ν)
    {n : ℕ} (a : Fin n → MixedFreq ι) :
    Matrix.gram ℂ (productFamily ν' a) = s • Matrix.gram ℂ (productFamily ν a) := by
  ext i j
  rw [Matrix.gram_apply, Matrix.smul_apply, Matrix.gram_apply]
  unfold productFamily
  rw [inner_lift₂, inner_lift₂, hν, integral_smul_measure, ENNReal.toReal_ofReal hs]

/-- Replace both probability normalizations with their positive mass factors in
the hypotheses used by graph restriction. -/
def NormalizedProductLineData.toProductLineStep
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 < u) {v : LineWeight}
    {a : List ℚ} {q : ℚ} {K δ τ : ℝ}
    (D : NormalizedProductLineData (v.normalize μ).toMeasure u a q K δ τ) :
    ProductLineStepData μ u v a q K δ τ := by
  let ρ := (v.normalize μ).toMeasure
  let s := v.mass μ * D.F.mass
  have hm0 := v.mass_pos μ (IsProbabilityMeasure.ne_zero μ)
  have hs : 0 < s := mul_pos hm0 D.F.mass_pos
  have hM : D.F.mass ≤ 1 := D.F.mass_le_one 0
  let σ := D.F.normalizedMeasure ρ
  let ν := D.W.measure μ v
  have hν : ν = ENNReal.ofReal s • σ := D.W.measure_eq_normalized_fiber μ v D.F D.weight_eq
  let A := appendedMixedFreq a D.B
  have hG := gram_productFamily_scale σ ν hs.le hν A
  refine { r := D.r
           n := D.n
           n_pos := D.n_pos
           B := D.B
           aux_ne_zero := D.aux_ne_zero
           aux_injective := D.aux_injective
           W := D.W
           loss_lt := ?_
           Kp := D.Kp
           Kp_lt := D.Kp_lt
           prefix_bound := ?_
           independent := ?_
           c := D.c
           residual_small := ?_ }
  · rw [D.weight_eq, D.F.integral_loss_prod μ]
    exact D.loss_lt
  · rw [hPrefix_iff_pb, hG]
    have hP := (hPrefix_iff_pb _ _).mp D.prefix_bound
    refine ⟨hP.1, fun k hk c => ?_⟩
    simp only [qform_smul]
    simpa only [mul_left_comm s] using mul_le_mul_of_nonneg_left (hP.2 k hk c) hs.le
  · rw [← Matrix.posDef_gram_iff_linearIndependent, hG]
    exact (Matrix.posDef_gram_iff_linearIndependent.mpr D.independent).smul hs
  · let f (z : ℝ × UnitAddTorus (Fin D.r)) := ‖evalMixedPoly (residualPoly A q D.c) z‖ ^ 2
    have hmeas : Measurable (fun z : ℝ × UnitAddTorus (Fin D.r) => v z.1 * D.W.toFun z) :=
      (v.measurable_toFun.comp measurable_fst).mul D.W.continuous_toFun.measurable
    have hEn : (∫ z, v z.1 * D.W.toFun z * f z ∂μ.prod (torusHaar (Fin D.r))) =
        s * ∫ z, f z ∂σ := by
      calc
        _ = ∫ z, f z ∂ν :=
          (integral_weightedMeasure _ hmeas
            (Eventually.of_forall fun z => mul_nonneg (v.positive z.1).le (D.W.positive z).le) f).symm
        _ = _ := by rw [hν, integral_smul_measure, ENNReal.toReal_ofReal hs.le]; rfl
    change (∫ z, v z.1 * D.W.toFun z * f z ∂μ.prod (torusHaar (Fin D.r))) < _
    rw [hEn, lineDistanceSq_normalize]
    calc
      _ < s * (lineContraction u * lineDistanceSq ρ LineWeight.one a q) :=
        mul_lt_mul_of_pos_left D.residual_small hs
      _ ≤ _ := by
        have hθ := (lineContraction_bounds hu).1
        have hd := lineDistanceSq_nonneg ρ LineWeight.one a q
        have hh := mul_le_mul_of_nonneg_left hM hm0.le
        dsimp [s, ρ] at *
        nlinarith [mul_le_mul_of_nonneg_right hh (mul_nonneg hθ.le hd)]

theorem productExtensionSupply_of_normalized {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (normal : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NullSingletonClass ρ],
      NormalizedProductExtensionSupply ρ) :
    ProductLineExtensionSupply μ := by
  intro u hu hu' v a q K δ τ ha hnd hq hδ hτ hp
  let ρ := (v.normalize μ).toMeasure
  let : NullSingletonClass ρ := v.normalize_nullSingletonClass μ (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨D⟩ := normal ρ u hu hu' a q K δ τ ha hnd hq hδ hτ
    (v.prefix_normalize μ (IsProbabilityMeasure.ne_zero μ) a hp)
  exact ⟨D.toProductLineStep hu⟩

end

end SchauderBasisOrbits
