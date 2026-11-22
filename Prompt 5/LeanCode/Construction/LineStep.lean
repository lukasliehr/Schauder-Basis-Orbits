module

public import LeanCode.Construction.Iteration
public import LeanCode.Fourier.Graph

@[expose] public section

open Filter Function MeasureTheory Submodule
open scoped ENNReal Topology ComplexConjugate InnerProductSpace MatrixOrder ComplexOrder BigOperators

namespace SchauderBasisOrbits

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A polynomial weight for graph restriction. -/
structure GraphWeight (ι : Type*) [Fintype ι] where
  toFun : ℝ × UnitAddTorus ι → ℝ
  poly : MixedPoly ι
  eval_eq : ∀ z, evalMixedPoly poly z = (toFun z : ℂ)
  positive : ∀ z, 0 < toFun z
  le_one : ∀ z, toFun z ≤ 1

theorem GraphWeight.continuous_toFun (W : GraphWeight ι) : Continuous W.toFun := by
  have heq : W.toFun = Complex.re ∘ evalMixedPoly W.poly := by
    funext z
    rw [comp_apply, W.eval_eq, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp (continuous_evalMixedPoly _)

omit [Fintype ι] in
theorem continuous_graphPoint (ω : ι → ℤ) (j : ℕ) : Continuous (graphPoint ω j) := by
  apply continuous_id.prodMk
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)

def GraphWeight.onGraph (W : GraphWeight ι) (ω : ι → ℤ) (j : ℕ) : LineWeight :=
  ⟨fun x => W.toFun (graphPoint ω j x),
    (W.continuous_toFun.comp (continuous_graphPoint ω j)).measurable,
    fun _ => W.positive _, fun _ => W.le_one _⟩

def GraphWeight.measure (W : GraphWeight ι) (μ : Measure ℝ) (v : LineWeight) :
    Measure (ℝ × UnitAddTorus ι) :=
  weightedMeasure (μ.prod (torusHaar ι)) (fun z => v z.1 * W.toFun z)

instance (W : GraphWeight ι) (μ : Measure ℝ) [IsFiniteMeasure μ] (v : LineWeight) :
    IsFiniteMeasure (W.measure μ v) :=
  finite_weightedMeasure _ (Eventually.of_forall fun z =>
    (mul_le_of_le_one_right (v.positive z.1).le (W.le_one z)).trans (v.le_one z.1))

def productFamily {n : ℕ} (ν : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ν]
    (a : Fin n → MixedFreq ι) (i : Fin n) : Lp ℂ 2 ν :=
  lift₂ ν (mixedChar (a i)) (continuous_mixedChar (a i)).measurable 1
    (fun z => (norm_mixedChar _ z).le)

def appendedMixedFreq {n : ℕ} (a : List ℚ) (b : Fin n → MixedFreq ι) :
    Fin (a.length + n) → MixedFreq ι :=
  Fin.append (fun i => (a.get i, 0)) b

def residualPoly {n : ℕ} (a : Fin n → MixedFreq ι) (q : ℚ) (c : Fin n → ℂ) :
    MixedPoly ι :=
  AddMonoidAlgebra.single (q, 0) 1 - ∑ i, AddMonoidAlgebra.single (a i) (c i)

theorem eval_residualPoly {n : ℕ} (a : Fin n → MixedFreq ι) (q : ℚ)
    (c : Fin n → ℂ) (z : ℝ × UnitAddTorus ι) :
    evalMixedPoly (residualPoly a q c) z =
      realChar q z.1 - synth (fun i => mixedChar (a i) z) c := by
  rw [← mixedEvalHom_apply, residualPoly, map_sub, map_sum]
  simp only [mixedEvalHom_apply,
    evalMixedPoly_single, one_mul, mixedChar, torusChar_zero, mul_one, synth, smul_eq_mul]

/-- The finite product estimates in the unnormalized reference measure. This
interface retains the actual mixed frequencies and one residual test vector. -/
structure ProductLineStepData (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ)
    (v : LineWeight) (a : List ℚ) (q : ℚ) (K δ τ : ℝ) where
  r : ℕ
  n : ℕ
  n_pos : 0 < n
  B : Fin n → MixedFreq (Fin r)
  aux_ne_zero : ∀ i, (B i).2 ≠ 0
  aux_injective : Injective (fun i => (B i).2)
  W : GraphWeight (Fin r)
  loss_lt : (∫ z, 1 - W.toFun z ∂μ.prod (torusHaar (Fin r))) < δ
  Kp : ℝ
  Kp_lt : Kp < max K (linePrefixFloor u) + τ
  prefix_bound : HPrefix (𝕜 := ℂ) (productFamily (W.measure μ v) (appendedMixedFreq a B)) Kp
  independent : LinearIndependent ℂ (productFamily (W.measure μ v) (appendedMixedFreq a B))
  c : Fin (a.length + n) → ℂ
  residual_small :
    (∫ z, v z.1 * W.toFun z * ‖evalMixedPoly (residualPoly (appendedMixedFreq a B) q c) z‖ ^ 2
      ∂μ.prod (torusHaar (Fin r))) < lineContraction u * lineDistanceSq μ v a q

def ProductLineExtensionSupply (μ : Measure ℝ) [IsFiniteMeasure μ] : Prop :=
  ∀ (u : ℝ), 0 < u → u ≤ 1 / 100 → ∀ (v : LineWeight) (a : List ℚ) (q : ℚ) (K δ τ : ℝ),
    a ≠ [] → a.Nodup → q ∉ a → 0 < δ → 0 < τ →
    HPrefix (𝕜 := ℂ) (realFamily (v.measure μ) a) K →
    Nonempty (ProductLineStepData μ u v a q K δ τ)

private theorem hPrefix_of_gram_limit {m : ℕ} [Nonempty (Fin m)]
    {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) {K L : ℝ}
    (hKG : PB G K) (hKL : K < L) {Gn : ℕ → Matrix (Fin m) (Fin m) ℂ}
    (hherm : ∀ n, (Gn n).IsHermitian) (hGn : Tendsto Gn atTop (𝓝 G)) :
    ∀ᶠ n in atTop, PB (Gn n) L := by
  let f (η : ℝ) := Real.sqrt ((1 + η) / (1 - η)) * K
  have hc : ContinuousAt f 0 := by
    dsimp [f]
    fun_prop (disch := norm_num)
  have he : ∀ᶠ η in 𝓝 (0 : ℝ), f η < L :=
    hc.eventually (gt_mem_nhds (show f 0 < L by simpa [f] using hKL))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let η := min (r / 2) (1 / 2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη' : η < 1 := (min_le_right ..).trans_lt (by norm_num)
  have hηbar : f η < L := hball (by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hη]
    exact (min_le_left ..).trans_lt (by linarith))
  filter_upwards [eventually_posDef_relative hG hη hη' (Eventually.of_forall hherm) hGn] with n hn
  have hB := hKG.relative (sub_pos.mpr hη') (by linarith) hn.2.1 hn.2.2
  refine ⟨hB.1.trans hηbar.le, fun k hk c => (hB.2 k hk c).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB.1 hηbar.le 2)
    (qform_nonneg hn.1.posSemidef c)

private theorem weighted_product_gram {n : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : LineWeight) (W : GraphWeight ι) (a : Fin n → MixedFreq ι) (i j : Fin n) :
    Matrix.gram ℂ (productFamily (W.measure μ v) a) i j =
      ∫ z, (v z.1 : ℂ) * (W.toFun z * conj (mixedChar (a i) z) * mixedChar (a j) z)
        ∂μ.prod (torusHaar ι) := by
  rw [Matrix.gram_apply, productFamily, productFamily, inner_lift₂]
  have hm : Measurable (fun z : ℝ × UnitAddTorus ι => v z.1 * W.toFun z) :=
    (v.measurable_toFun.comp measurable_fst).mul W.continuous_toFun.measurable
  rw [GraphWeight.measure, integral_weightedMeasure _ hm
    (Eventually.of_forall fun z => mul_nonneg (v.positive z.1).le (W.positive z).le)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [Complex.real_smul]
  push_cast
  ring

private theorem weighted_line_gram {n : ℕ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v V : LineWeight) (a : Fin n → ℚ) (i j : Fin n) :
    Matrix.gram ℂ (fun k => realCharLp ((v.mul V).measure μ) (a k : ℝ)) i j =
      ∫ x, (v x : ℂ) * (V x * conj (realChar (a i : ℝ) x) * realChar (a j : ℝ) x) ∂μ := by
  rw [Matrix.gram_apply, realCharLp, realCharLp, inner_lift₂, LineWeight.measure,
    integral_weightedMeasure _ (v.mul V).measurable_toFun
      (Eventually.of_forall fun x => ((v.mul V).positive x).le)]
  apply integral_congr_ae
  filter_upwards [] with x
  change (v x * V x) • (conj (realChar (a i : ℝ) x) * realChar (a j : ℝ) x) = _
  rw [Complex.real_smul]
  push_cast
  ring

private theorem evaluated_characters_graph {n : ℕ} (a : Fin n → MixedFreq ι) (c : Fin n → ℂ)
    (ω : ι → ℤ) (j : ℕ) (q : ℚ) (x : ℝ) :
    evalMixedPoly (residualPoly a q c) (graphPoint ω j x) =
      realChar (q : ℝ) x - synth (fun i => realChar (graphFrequency ω j (a i) : ℝ) x) c := by
  rw [eval_residualPoly]
  simp only [synth, mixedChar_graph]
  rfl

private theorem hPrefix_ofFn {m : ℕ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (f : Fin m → ℚ) {K : ℝ} (h : HPrefix (𝕜 := ℂ) (fun i => realCharLp ν (f i : ℝ)) K) :
    HPrefix (𝕜 := ℂ) (realFamily ν (List.ofFn f)) K := by
  let e : Fin (List.ofFn f).length ↪ Fin m := Fin.castLEEmb (by simp)
  have he : StrictMono e := fun _ _ h => h
  have heq : realFamily ν (List.ofFn f) =
      (fun i => realCharLp ν (f i : ℝ)) ∘ e := by
    funext i
    change realCharLp ν ((List.ofFn f).get i : ℝ) = realCharLp ν (f (e i) : ℝ)
    simp [List.get_eq_getElem, e]
    rfl
  rw [heq]
  exact h.restrict e he

private theorem complexTests_tendsto_re {A : ℕ → ℂ} {a : ℂ}
    (h : Tendsto A atTop (𝓝 a)) : Tendsto (fun n => (A n).re) atTop (𝓝 a.re) :=
  (Complex.continuous_re.tendsto a).comp h


theorem modePairing_sub (k l ω : ι → ℤ) :
    modePairing (k - l) ω = modePairing k ω - modePairing l ω := by
  simp [modePairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Graph restriction transfers a finite product extension to the line. The
prefix estimate uses positive definiteness of the limiting Gram, and a single
residual coefficient vector suffices for the distance estimate. -/
theorem lineStep_of_product {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    {u : ℝ} {v : LineWeight} {a : List ℚ} {q : ℚ} {K δ τ : ℝ}
    (hnodup : a.Nodup) (d : ProductLineStepData μ u v a q K δ τ) :
    Nonempty (LineStepData μ u v a q K δ τ) := by
  classical
  let ι := Fin d.r
  let N := a.length + d.n
  let A : Fin N → MixedFreq ι := appendedMixedFreq a d.B
  let W := d.W
  let P : Bool ⊕ (Fin N × Fin N) → MixedPoly ι
    | .inl false => 1 - W.poly
    | .inl true => W.poly * (conjMixedPoly (residualPoly A q d.c) * residualPoly A q d.c)
    | .inr (i, j) =>
      W.poly * (conjMixedPoly (AddMonoidAlgebra.single (A i) 1) * AddMonoidAlgebra.single (A j) 1)
  let g : (Bool ⊕ (Fin N × Fin N)) → ℝ → ℂ
    | .inl false => fun _ => 1
    | .inl true => fun x => (v x : ℂ)
    | .inr _ => fun x => (v x : ℂ)
  have hvInt : Integrable (fun x => (v x : ℂ)) μ :=
    Integrable.of_bound v.measurable_toFun.complex_ofReal.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        change ‖(v x : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (v.positive x)]
        exact v.le_one x)
  have hg (k) : Integrable (g k) μ := by
    rcases k with i | ij
    · cases i
      · exact integrable_const _
      · exact hvInt
    · exact hvInt
  let T (k) := polynomialFourierTest (P k) (g k) (hg k)
  let nonzero := (Finset.univ : Finset (Fin d.n)).image (fun i => (d.B i).2)
  let differences := ((Finset.univ : Finset (Fin d.n × Fin d.n)).filter (fun ij => ij.1 ≠ ij.2)).image
    (fun ij => (d.B ij.1).2 - (d.B ij.2).2)
  let L := nonzero ∪ differences
  have hL : ∀ k ∈ L, k ≠ 0 := by
    intro k hk
    rcases Finset.mem_union.mp hk with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact d.aux_ne_zero i
    · obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp h
      exact sub_ne_zero.mpr (d.aux_injective.ne (Finset.mem_filter.mp hij).2)
  obtain ⟨ω, seq, hseq, hω, ht⟩ := simultaneous_graph_average T L hL
  have htests (k) :
      Tendsto (fun n => ∫ x, g k x * evalMixedPoly (P k) (graphPoint ω (seq n) x) ∂μ)
        atTop (𝓝 (∫ z, g k z.1 * evalMixedPoly (P k) z ∂μ.prod (torusHaar ι))) := by
    simpa only [T, polynomialFourierTest_eval, graphPoint] using ht k
  let V (j : ℕ) := W.onGraph ω j
  let f (j : ℕ) (i : Fin N) := graphFrequency ω j (A i)
  let B (j : ℕ) := List.ofFn (fun i => graphFrequency ω j (d.B i))
  have hlist (j : ℕ) : List.ofFn (f j) = a ++ B j := by
    conv_rhs => rw [← List.ofFn_get a]
    rw [← List.ofFn_fin_append]
    congr 1
    ext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [f, A, appendedMixedFreq, graphFrequency, modePairing]
    · simp [f, A, appendedMixedFreq]
  have hsep : ∀ᶠ n in atTop, (a ++ B (seq n)).Nodup := by
    let l (i : Fin d.n) := modePairing (d.B i).2 ω
    have hl0 (i : Fin d.n) : l i ≠ 0 := hω _ (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩))
    have hlin : Injective l := by
      intro i j hij
      by_contra hne
      have hn := hω _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩))
      exact hn (by rw [modePairing_sub]; exact sub_eq_zero.mpr hij)
    have haff := hseq.tendsto_atTop.eventually
      (eventually_affine_frequency_separation (fun i => (d.B i).1) l hlin hl0 a.toFinset)
    filter_upwards [haff] with j hj
    rw [List.nodup_append]
    refine ⟨hnodup, List.nodup_ofFn.mpr hj.1, ?_⟩
    intro x hxA y hyB hxy
    subst y
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hyB
    exact hj.2 i (by simpa only [← hi, List.mem_toFinset, graphFrequency, l] using hxA)
  let G := Matrix.gram ℂ (productFamily (W.measure μ v) A)
  let Gn (n : ℕ) := Matrix.gram ℂ (fun i => realCharLp ((v.mul (V (seq n))).measure μ) (f (seq n) i : ℝ))
  have hGtendsto : Tendsto Gn atTop (𝓝 G) := by
    apply matrix_tendsto_of_entries
    intro i j
    simp only [Gn, G]
    rw [weighted_product_gram]
    simp_rw [weighted_line_gram μ v (V _) (f _) i j]
    simpa only [g, P, f, V, GraphWeight.onGraph,
      evalMixedPoly_mul, evalMixedPoly_conj, evalMixedPoly_single, one_mul, W.eval_eq,
      mixedChar_graph, mul_assoc] using htests (.inr (i, j))
  let Ktarget := max K (linePrefixFloor u) + τ
  let : Nonempty (Fin N) := ⟨⟨0, by dsimp [N]; have := d.n_pos; omega⟩⟩
  have hpb : ∀ᶠ n in atTop,
      HPrefix (𝕜 := ℂ) (realFamily ((v.mul (V (seq n))).measure μ) (a ++ B (seq n))) Ktarget := by
    have hpos : G.PosDef := Matrix.posDef_gram_iff_linearIndependent.mpr d.independent
    have hpG : PB G d.Kp := (hPrefix_iff_pb _ _).mp d.prefix_bound
    filter_upwards [hPrefix_of_gram_limit hpos hpG d.Kp_lt
      (fun n => Matrix.isHermitian_gram _ _) hGtendsto] with n hn
    rw [← hlist]
    exact hPrefix_ofFn (f (seq n)) ((hPrefix_iff_pb _ _).mpr hn)
  have hloss :=
    complexTests_tendsto_re (htests (.inl false))
  have hloss' : Tendsto (fun n => ∫ x, 1 - V (seq n) x ∂μ) atTop
      (𝓝 (∫ z, 1 - W.toFun z ∂μ.prod (torusHaar ι))) := by
    have he (z : ℝ × UnitAddTorus ι) :
        evalMixedPoly (P (.inl false)) z = (↑(1 - W.toFun z) : ℂ) := by
      simp [P, W.eval_eq]
    simpa only [g, one_mul, he, integral_complex_ofReal, Complex.ofReal_re, V, GraphWeight.onGraph] using hloss
  have hLossEvent := hloss'.eventually (gt_mem_nhds d.loss_lt)
  let e (j : ℕ) : Fin (List.ofFn (f j)).length → ℂ :=
    fun i => d.c ⟨i.val, by simpa using i.isLt⟩
  have hResidualEval (j : ℕ) (x : ℝ) :
      evalMixedPoly (residualPoly A q d.c) (graphPoint ω j x) =
        realChar (q : ℝ) x - realSynth (List.ofFn (f j)) (e j) x := by
    rw [evaluated_characters_graph]
    congr 1
    simp only [realSynth, synth, Finset.sum_fin_eq_sum_range, List.length_ofFn]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi, e, f, List.get_eq_getElem]
  have hr := complexTests_tendsto_re (htests (.inl true))
  have hEnergy (z : ℝ × UnitAddTorus ι) :
      (v z.1 : ℂ) * evalMixedPoly (P (.inl true)) z =
        (↑(v z.1 * W.toFun z * ‖evalMixedPoly (residualPoly A q d.c) z‖ ^ 2) : ℂ) := by
    simp only [P, evalMixedPoly_mul, evalMixedPoly_conj, W.eval_eq, Complex.ofReal_mul,
      Complex.ofReal_pow, mul_assoc]
    rw [mul_comm (starRingEnd ℂ _), Complex.mul_conj']
  have hr' : Tendsto (fun n => ∫ x, (v.mul (V (seq n))) x *
      ‖realChar (q : ℝ) x - realSynth (List.ofFn (f (seq n))) (e (seq n)) x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ z, v z.1 * W.toFun z * ‖evalMixedPoly (residualPoly A q d.c) z‖ ^ 2
        ∂μ.prod (torusHaar ι))) := by
    have hE (n : ℕ) (x : ℝ) :
        g (.inl true) x * evalMixedPoly (P (.inl true)) (graphPoint ω (seq n) x) =
          (↑((v.mul (V (seq n))) x *
            ‖realChar (q : ℝ) x - realSynth (List.ofFn (f (seq n))) (e (seq n)) x‖ ^ 2) : ℂ) := by
      have h := hEnergy (graphPoint ω (seq n) x)
      rw [hResidualEval] at h
      exact h
    simpa only [hE, g, hEnergy, integral_complex_ofReal, Complex.ofReal_re] using hr
  have hDist : ∀ᶠ n in atTop, lineDistanceSq μ (v.mul (V (seq n))) (a ++ B (seq n)) q ≤
      lineContraction u * lineDistanceSq μ v a q := by
    filter_upwards [hr'.eventually (gt_mem_nhds d.residual_small)] with n hn
    rw [← hlist]
    exact (lineDistanceSq_le_residual μ _ _ q _).trans hn.le
  obtain ⟨n, hn, hpb', hLoss', hDist'⟩ := (hsep.and (hpb.and (hLossEvent.and hDist))).exists
  refine ⟨⟨V (seq n), a ++ B (seq n), hn, ⟨B (seq n), rfl⟩, ?_, hLoss', hpb', hDist'⟩⟩
  simpa [B] using d.n_pos

theorem lineExtensionSupply_of_product {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (P : ProductLineExtensionSupply μ) : LineExtensionSupply μ := by
  intro u hu hu' v a q K δ τ ha hnodup hq hδ hτ hPB
  obtain ⟨d⟩ := P u hu hu' v a q K δ τ ha hnodup hq hδ hτ hPB
  exact lineStep_of_product hnodup d

end

end SchauderBasisOrbits
