import LeanCode.Finite.Families
import LeanCode.Fourier.RealTotality
import Mathlib

open Filter MeasureTheory Submodule
open scoped ENNReal InnerProductSpace Topology

namespace SchauderBasisOrbits

/-- A pointwise positive measurable line weight bounded by one. -/
structure LineWeight where
  toFun : ℝ → ℝ
  measurable_toFun : Measurable toFun
  positive : ∀ x, 0 < toFun x
  le_one : ∀ x, toFun x ≤ 1

instance : CoeFun LineWeight (fun _ => ℝ → ℝ) := ⟨LineWeight.toFun⟩

def LineWeight.one : LineWeight :=
  ⟨fun _ => 1, measurable_const, fun _ => zero_lt_one, fun _ => le_rfl⟩

def LineWeight.mul (v V : LineWeight) : LineWeight :=
  ⟨fun x => v x * V x, v.measurable_toFun.mul V.measurable_toFun,
    fun x => mul_pos (v.positive x) (V.positive x),
    fun x => (mul_le_of_le_one_right (v.positive x).le (V.le_one x)).trans (v.le_one x)⟩

noncomputable def LineWeight.measure (v : LineWeight) (μ : Measure ℝ) : Measure ℝ :=
  weightedMeasure μ v

instance (v : LineWeight) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (v.measure μ) :=
  finite_weightedMeasure μ (Eventually.of_forall v.le_one)

instance (v : LineWeight) (μ : Measure ℝ) [NullSingletonClass μ] :
    NullSingletonClass (v.measure μ) :=
  ⟨fun x => withDensity_absolutelyContinuous μ _ (measure_singleton x)⟩

theorem LineWeight.measure_ne_zero (v : LineWeight) {μ : Measure ℝ} (hμ : μ ≠ 0) :
    v.measure μ ≠ 0 := by
  intro h
  have heq := (withDensity_eq_zero_iff v.measurable_toFun.ennreal_ofReal.aemeasurable).mp h
  have hf : ∀ᵐ x ∂μ, False := by
    filter_upwards [heq] with x hx
    exact (ENNReal.ofReal_pos.mpr (v.positive x)).ne' hx
  rw [ae_iff] at hf
  exact hμ (Measure.measure_univ_eq_zero.mp (by simpa using hf))

/-- The real exponentials indexed by a finite list, in list order. -/
noncomputable def realFamily (μ : Measure ℝ) [IsFiniteMeasure μ] (A : List ℚ) :
    Fin A.length → Lp ℂ 2 μ :=
  fun i => realCharLp μ ((A.get i : ℚ) : ℝ)

theorem linearIndependent_realFamily (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hμ : μ ≠ 0) {A : List ℚ} (hA : A.Nodup) : LinearIndependent ℂ (realFamily μ A) := by
  apply linearIndependent_realCharLp hμ
  intro i j h
  exact hA.get_inj_iff.mp (Rat.cast_injective h)

/-- A synthesis sum before passing to L². -/
noncomputable def realSynth (A : List ℚ) (c : Fin A.length → ℂ) (x : ℝ) : ℂ :=
  synth (fun i => realChar ((A.get i : ℚ) : ℝ) x) c

theorem continuous_realSynth (A : List ℚ) (c : Fin A.length → ℂ) : Continuous (realSynth A c) := by
  unfold realSynth synth
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (continuous_realChar ((A.get i : ℚ) : ℝ))

theorem norm_realSynth_le (A : List ℚ) (c : Fin A.length → ℂ) (x : ℝ) :
    ‖realSynth A c x‖ ≤ ∑ i, ‖c i‖ := by
  unfold realSynth synth
  calc
    _ ≤ ∑ i, ‖c i • realChar ((A.get i : ℚ) : ℝ) x‖ := norm_sum_le ..
    _ = _ := by simp

theorem ae_synth_realFamily (μ : Measure ℝ) [IsFiniteMeasure μ] (A : List ℚ)
    (c : Fin A.length → ℂ) :
    ⇑(synth (realFamily μ A) c) =ᵐ[μ] realSynth A c := by
  classical
  unfold realSynth synth
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • realFamily μ A i)).trans ?_
  have h (i : Fin A.length) :
      ⇑(c i • realFamily μ A i : Lp ℂ 2 μ) =ᵐ[μ]
        (fun x => c i • realChar ((A.get i : ℚ) : ℝ) x) :=
    (Lp.coeFn_smul (c i) (realCharLp μ ((A.get i : ℚ) : ℝ))).trans
      ((ae_realCharLp μ ((A.get i : ℚ) : ℝ)).mono fun x hx => congrArg (fun z : ℂ => c i • z) hx)
  filter_upwards [Finset.eventually_all Finset.univ |>.mpr (fun i _ => h i)] with x hx
  exact Finset.sum_congr rfl hx

theorem norm_sq_synth_weighted (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    (A : List ℚ) (c : Fin A.length → ℂ) :
    ‖synth (realFamily (v.measure μ) A) c‖ ^ 2 = ∫ x, v x * ‖realSynth A c x‖ ^ 2 ∂μ := by
  rw [norm_sq_L2_integral]
  have h := ae_synth_realFamily (v.measure μ) A c
  calc
    _ = ∫ x, ‖realSynth A c x‖ ^ 2 ∂v.measure μ :=
      integral_congr_ae (h.mono fun x hx => by rw [hx])
    _ = _ := integral_weightedMeasure μ v.measurable_toFun
      (Eventually.of_forall fun x => (v.positive x).le) _

/-- Squared distance to the span of an ordered real-character list. -/
noncomputable def lineDistanceSq (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    (A : List ℚ) (q : ℚ) : ℝ :=
  Metric.infDist (realCharLp (v.measure μ) (q : ℝ))
    (span ℂ (Set.range (realFamily (v.measure μ) A))) ^ 2

theorem lineDistanceSq_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    (A : List ℚ) (q : ℚ) : 0 ≤ lineDistanceSq μ v A q := sq_nonneg _

theorem lineDistanceSq_eq_zero_of_mem (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    {A : List ℚ} {q : ℚ} (hq : q ∈ A) : lineDistanceSq μ v A q = 0 := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
  unfold lineDistanceSq
  have h : realCharLp (v.measure μ) (q : ℝ) ∈
      span ℂ (Set.range (realFamily (v.measure μ) A)) :=
    subset_span ⟨i, by change realCharLp _ ((A.get i : ℚ) : ℝ) = _; rw [hi]⟩
  simp [Metric.infDist_zero_of_mem h]

theorem norm_sq_residual_weighted (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    (A : List ℚ) (q : ℚ) (c : Fin A.length → ℂ) :
    ‖realCharLp (v.measure μ) (q : ℝ) - synth (realFamily (v.measure μ) A) c‖ ^ 2 =
      ∫ x, v x * ‖realChar (q : ℝ) x - realSynth A c x‖ ^ 2 ∂μ := by
  rw [norm_sq_L2_integral]
  have h := (Lp.coeFn_sub ..).trans
    ((ae_realCharLp (v.measure μ) (q : ℝ)).sub (ae_synth_realFamily (v.measure μ) A c))
  calc
    _ = ∫ x, ‖realChar (q : ℝ) x - realSynth A c x‖ ^ 2 ∂v.measure μ :=
      integral_congr_ae (h.mono fun x hx => by rw [hx]; rfl)
    _ = _ := integral_weightedMeasure μ v.measurable_toFun
      (Eventually.of_forall fun x => (v.positive x).le) _

theorem lineDistanceSq_le_residual (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    (A : List ℚ) (q : ℚ) (c : Fin A.length → ℂ) :
    lineDistanceSq μ v A q ≤ ∫ x, v x * ‖realChar (q : ℝ) x - realSynth A c x‖ ^ 2 ∂μ := by
  rw [← norm_sq_residual_weighted]
  apply pow_le_pow_left₀ Metric.infDist_nonneg
  rw [← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem ((mem_span_range_iff_exists_fun _).mpr ⟨c, rfl⟩)

theorem lineDistanceSq_minimizer (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    (A : List ℚ) (q : ℚ) :
    ∃ c : Fin A.length → ℂ,
      lineDistanceSq μ v A q = ∫ x, v x * ‖realChar (q : ℝ) x - realSynth A c x‖ ^ 2 ∂μ := by
  let S := span ℂ (Set.range (realFamily (v.measure μ) A))
  let : FiniteDimensional ℂ S := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  let f := realCharLp (v.measure μ) (q : ℝ)
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℂ).mp (S.starProjection_apply_mem f)
  refine ⟨c, ?_⟩
  rw [← norm_sq_residual_weighted, lineDistanceSq]
  change Metric.infDist f S ^ 2 = ‖f - synth (realFamily (v.measure μ) A) c‖ ^ 2
  rw [← S.dist_starProjection_eq_infDist, dist_eq_norm, synth, hc]

/-- Extend old coefficients by zero along an ordered list prefix. -/
def extendLineCoeffs {A B : List ℚ} (c : Fin A.length → ℂ) (i : Fin B.length) : ℂ :=
  if hi : i.val < A.length then c ⟨i.val, hi⟩ else 0

theorem realSynth_extendLineCoeffs {A B : List ℚ} (hAB : A <+: B)
    (c : Fin A.length → ℂ) (x : ℝ) :
    realSynth B (extendLineCoeffs c) x = realSynth A c x := by
  simp only [realSynth, synth, Finset.sum_fin_eq_sum_range]
  have hsub := Finset.range_mono hAB.length_le
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro i hi
    have ha := Finset.mem_range.mp hi
    have hb := ha.trans_le hAB.length_le
    simp only [dite_eq_left ha, dite_eq_left hb, extendLineCoeffs, List.get_eq_getElem]
    rw [hAB.getElem ha]
  · intro i hi hni
    have ha : ¬ i < A.length := fun h => hni (Finset.mem_range.mpr h)
    have hb := Finset.mem_range.mp hi
    simp [hb, extendLineCoeffs, ha]

private theorem residual_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight)
    (A : List ℚ) (q : ℚ) (c : Fin A.length → ℂ) :
    Integrable (fun x => v x * ‖realChar (q : ℝ) x - realSynth A c x‖ ^ 2) μ := by
  have hc : Continuous (fun x => realChar (q : ℝ) x - realSynth A c x) :=
    (continuous_realChar _).sub (continuous_realSynth A c)
  apply Integrable.of_bound ((v.measurable_toFun.mul (hc.norm.measurable.pow_const 2)).aestronglyMeasurable)
    ((1 + ∑ i, ‖c i‖) ^ 2)
  filter_upwards [] with x
  change ‖v x * ‖realChar (q : ℝ) x - realSynth A c x‖ ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (v.positive x).le (sq_nonneg _))]
  have hle := (norm_sub_le (realChar (q : ℝ) x) (realSynth A c x)).trans
    (add_le_add (norm_realChar _ _).le (norm_realSynth_le A c x))
  exact (mul_le_of_le_one_left (sq_nonneg _) (v.le_one x)).trans (pow_le_pow_left₀ (norm_nonneg _) hle 2)

/-- Squared distances decrease under smaller weights and ordered extensions. -/
theorem lineDistanceSq_mono (μ : Measure ℝ) [IsFiniteMeasure μ] {v w : LineWeight}
    {A B : List ℚ} (hAB : A <+: B) (hvw : (w : ℝ → ℝ) ≤ᵐ[μ] (v : ℝ → ℝ)) (q : ℚ) :
    lineDistanceSq μ w B q ≤ lineDistanceSq μ v A q := by
  obtain ⟨c, hc⟩ := lineDistanceSq_minimizer μ v A q
  rw [hc]
  refine (lineDistanceSq_le_residual μ w B q (extendLineCoeffs c)).trans ?_
  simp only [realSynth_extendLineCoeffs hAB]
  apply integral_mono_ae (residual_integrable μ w A q c) (residual_integrable μ v A q c)
  filter_upwards [hvw] with x hx
  exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)

/-- Any finite prefix estimate passes through an almost-everywhere bounded weight limit. -/
theorem hPrefix_of_weight_limit (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℕ → LineWeight) (w : LineWeight)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (w x)))
    (A : List ℚ) {K : ℝ} (hK : ∀ᶠ n in atTop, HPrefix (𝕜 := ℂ) (realFamily ((v n).measure μ) A) K) :
    HPrefix (𝕜 := ℂ) (realFamily (w.measure μ) A) K := by
  obtain ⟨n, hn⟩ := hK.exists
  refine ⟨hn.1, fun k hk c => ?_⟩
  have hs (c : Fin A.length → ℂ) : Tendsto
      (fun n => ‖synth (realFamily ((v n).measure μ) A) c‖)
      atTop (𝓝 ‖synth (realFamily (w.measure μ) A) c‖) := by
    have hsq := tendsto_integral_of_dominated_convergence
      (μ := μ) (F := fun n x => v n x * ‖realSynth A c x‖ ^ 2)
      (f := fun x => w x * ‖realSynth A c x‖ ^ 2)
      (fun _ => (∑ i, ‖c i‖) ^ 2)
      (fun n => ((v n).measurable_toFun.mul ((continuous_realSynth A c).norm.measurable.pow_const 2)).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ((v n).positive x).le (sq_nonneg _))]
        exact (mul_le_of_le_one_left (sq_nonneg _) ((v n).le_one x)).trans
          (pow_le_pow_left₀ (norm_nonneg _) (norm_realSynth_le A c x) 2))
      (hlim.mono fun x hx => hx.mul_const _)
    simp_rw [← norm_sq_synth_weighted μ] at hsq
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto _).comp hsq
  exact le_of_tendsto_of_tendsto (hs (truncCoeff k c)) ((hs c).const_mul K)
    (hK.mono fun _ h => h.2 k hk c)

end SchauderBasisOrbits
