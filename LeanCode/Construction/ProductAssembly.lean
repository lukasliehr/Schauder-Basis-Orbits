import LeanCode.Construction.ResidualLift
import LeanCode.Construction.Normalization
import LeanCode.Construction.ProductGeometry

open MeasureTheory Filter Submodule
open scoped InnerProductSpace BigOperators

noncomputable section

namespace SchauderBasisOrbits

/-- A zero-auxiliary-mode rational exponential in the final product space. -/
def productBaseVector {ι : Type*} [Fintype ι]
    (ν : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ν] (t : ℚ) : Lp ℂ 2 ν :=
  lift₂ ν (mixedChar (t, 0)) (continuous_mixedChar _).measurable 1 (fun p ↦ (norm_mixedChar _ p).le)

theorem ae_productBaseVector {ι : Type*} [Fintype ι]
    (ν : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ν] (t : ℚ) :
    ⇑(productBaseVector ν t) =ᵐ[ν] fun p ↦ realChar t p.1 := by
  refine (ae_lift₂ _ _ _ _ _).trans (Eventually.of_forall fun p ↦ ?_)
  simp [mixedChar]

/-- The combined selected blocks, with their joint centered synthesis and information error. -/
structure ProductSelection {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {A : List ℚ} {q : ℚ} {u lossBudget : ℝ} (R : ResidualLift ρ A q u lossBudget)
    (K δ τ : ℝ) where
  dim : ℕ
  size : ℕ
  size_pos : 0 < size
  modes : Fin size → MixedFreq (Fin dim)
  aux_nonzero : ∀ i, (modes i).2 ≠ 0
  aux_injective : Function.Injective fun i ↦ (modes i).2
  graphWeight : GraphWeight (Fin dim)
  fiberWeight : FiberWeight ℝ (torusHaar (Fin dim))
  weight_eq : graphWeight.toFun = fiberWeight.weight
  loss_lt : 1 - fiberWeight.mass < δ
  coupling : CenteredSynthesis (Lp ℂ 2 (R.weight.normalizedMeasure ρ))
    (Lp ℂ 2 (fiberWeight.normalizedMeasure ρ)) size
  full_eq : coupling.full = synthCLM (productFamily _ modes)
  lift_base (t : ℚ) :
    coupling.pullback (R.weight.pullback ρ (realCharLp ρ t)) = productBaseVector _ t
  center_injective : Function.Injective coupling.centered
  center_prefix : PB coupling.centeredGram (Real.sqrt (1 + 14 * u))
  η : ℝ
  η_lt_u : η < u
  η_lt_capture : η < (u / (1 + 2 * u)) / 2
  information_error : ‖coupling.information - R.information‖ ≤ η
  angle_lt_one : Real.sqrt η < 1
  prefix_slack : max K (linePrefixFloor u) *
    Real.sqrt ((1 + Real.sqrt η) / (1 - Real.sqrt η)) < max K (linePrefixFloor u) + τ

private theorem sum_productFamily_ae {ι : Type*} [Fintype ι] {n : ℕ}
    (ν : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ν]
    (b : Fin n → MixedFreq ι) (a : Fin n → ℂ) :
    ⇑(synth (productFamily ν b) a) =ᵐ[ν] fun p ↦ synth (fun i ↦ mixedChar (b i) p) a := by
  classical
  unfold synth
  refine (Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ a i • productFamily ν b i)).trans ?_
  have h (i : Fin n) : ⇑(a i • productFamily ν b i) =ᵐ[ν] fun p ↦ a i • mixedChar (b i) p :=
    (Lp.coeFn_smul _ _).trans ((ae_lift₂ ν (mixedChar (b i)) (continuous_mixedChar (b i)).measurable 1
      (fun p ↦ (norm_mixedChar _ p).le)).mono fun _ hp ↦
        congrArg (fun z : ℂ ↦ a i • z) hp)
  filter_upwards [(Finset.eventually_all Finset.univ).mpr (fun i _ ↦ h i)] with p hp
  exact Finset.sum_congr rfl hp

private theorem norm_sq_product_residual {ι : Type*} [Fintype ι] {n : ℕ}
    (ν : Measure (ℝ × UnitAddTorus ι)) [IsFiniteMeasure ν]
    (b : Fin n → MixedFreq ι) (q : ℚ) (a : Fin n → ℂ) :
    ‖productBaseVector ν q - synth (productFamily ν b) a‖ ^ 2 =
      ∫ p, ‖evalMixedPoly (residualPoly b q a) p‖ ^ 2 ∂ν := by
  let f := productBaseVector ν q - synth (productFamily ν b) a
  change ‖f‖ ^ 2 = _
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (productBaseVector ν q) (synth (productFamily ν b) a),
    ae_productBaseVector ν q, sum_productFamily_ae ν b a] with p hp h₁ h₂
  rw [inner_self_eq_norm_sq, show f p = _ from hp, Pi.sub_apply, h₁, h₂, eval_residualPoly]

private theorem span_range_finAppend {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {m n : ℕ} (u : Fin m → E) (v : Fin n → E) :
    span 𝕜 (Set.range (Fin.append u v)) = span 𝕜 (Set.range u) ⊔ span 𝕜 (Set.range v) := by
  rw [← span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simp only [Fin.append_left]
      exact Or.inl ⟨i, rfl⟩
    · simp only [Fin.append_right]
      exact Or.inr ⟨j, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨i.castAdd n, Fin.append_left ..⟩
    · exact ⟨j.natAdd m, Fin.append_right ..⟩

set_option maxHeartbeats 900000 in
theorem assemble_normalizedProductLineData {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    [NullSingletonClass ρ] {A : List ℚ} (hA : A.Nodup) {q : ℚ} (hq : q ∉ A)
    {u lossBudget K δ τ : ℝ} (hu : 0 < u)
    (hK : HPrefix (𝕜 := ℂ) (realFamily ρ A) K)
    (R : ResidualLift ρ A q u lossBudget) (hR : ResidualLiftCertificate R)
    (S : ProductSelection R K δ τ) : Nonempty (NormalizedProductLineData ρ u A q K δ τ) := by
  have hρ : ρ ≠ 0 := by
    intro hz
    have he : ρ Set.univ = 1 := measure_univ
    rw [hz] at he
    simp at he
  have hr := rationalResidual_ne_zero ρ hρ hA hq
  let ν := S.fiberWeight.normalizedMeasure ρ
  let Up := S.coupling.pullback.comp (R.weight.pullback ρ)
  let old := fun i : Fin A.length ↦ Up (realFamily ρ A i)
  let new := productFamily ν S.modes
  let Old := span ℂ (Set.range old)
  let New := LinearMap.range S.coupling.full.toLinearMap
  let E := (rationalOldSpan ρ A).map (R.weight.pullback ρ).toLinearMap
  let e := S.coupling.pullback R.target
  let d := ‖rationalResidual ρ A q‖

  have he : ‖R.target‖ = 1 := by
    unfold ResidualLift.target
    rw [LinearIsometry.norm_map, norm_rationalResidualUnit hr]
  have hJ : R.information.IsPositive := residualInformation_positive hu.le _
  have ha (x : Lp ℂ 2 (R.weight.normalizedMeasure ρ)) (hx : x ∈ E) : R.information x = 0 := by
    obtain ⟨f, hf, rfl⟩ := hx
    exact hR.old_zero f hf
  let _ : FiniteDimensional ℂ New := Module.Finite.range S.coupling.full.toLinearMap
  obtain ⟨hAngle, hCapture⟩ := product_capture_estimates S.coupling S.center_injective E hJ ha
    S.information_error R.target he hR.capture
  have hE : E.map S.coupling.pullback.toLinearMap = Old := by
    change ((span ℂ (Set.range (realFamily ρ A))).map (R.weight.pullback ρ).toLinearMap).map
      S.coupling.pullback.toLinearMap = Old
    rw [Submodule.map_span, Submodule.map_span, Set.image_image]
    congr 1
    rw [← Set.range_comp]
    rfl
  have hF : New = span ℂ (Set.range new) := by
    unfold New
    rw [S.full_eq]
    exact range_synthCLM new
  have angle (x : Lp ℂ 2 ν) (hx : x ∈ Old) (y : Lp ℂ 2 ν)
      (hy : y ∈ span ℂ (Set.range new)) : ‖⟪x, y⟫_ℂ‖ ≤ Real.sqrt S.η * ‖x‖ * ‖y‖ := by
    rw [← hE] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    change ‖⟪S.coupling.pullback z, y⟫_ℂ‖ ≤ Real.sqrt S.η * ‖S.coupling.pullback z‖ * ‖y‖
    rw [LinearIsometry.norm_map]
    exact hAngle z hz y (show y ∈ New by rw [hF]; exact hy)
  have hnorm : ‖S.coupling.information‖ ≤ 3 * u := by
    calc
      _ = ‖(S.coupling.information - R.information) + R.information‖ := by rw [sub_add_cancel]
      _ ≤ ‖S.coupling.information - R.information‖ + ‖R.information‖ := norm_add_le _ _
      _ ≤ _ := by linarith [S.information_error, hR.norm_lt, S.η_lt_u]
  have hnPrefix : HPrefix (𝕜 := ℂ) new (linePrefixFloor u) := by
    have hp := S.coupling.fullGram_prefix S.center_injective hnorm S.center_prefix
    unfold CenteredSynthesis.fullGram at hp
    rw [S.full_eq, clmGram_synthCLM_eq_gram] at hp
    exact ((hPrefix_iff_pb _ _).mpr hp).mono (product_prefix_arithmetic hu).le
  have hmap (c : Fin A.length → ℂ) : synth old c = Up (synth (realFamily ρ A) c) := by
    simp [synth, old, map_sum, map_smul]
  have hoPrefix : HPrefix (𝕜 := ℂ) old K := by
    refine ⟨hK.1, fun j hj c ↦ ?_⟩
    simpa only [hmap, LinearIsometry.norm_map] using hK.2 j hj c
  have hoIndependent : LinearIndependent ℂ old :=
    (linearIndependent_realFamily ρ hρ hA).map' Up.toLinearMap (LinearMap.ker_eq_bot.mpr Up.injective)
  have hnIndependent : LinearIndependent ℂ new := by
    rw [linearIndependent_iff_synth_eq_zero]
    intro c hc
    let C := WithLp.toLp 2 c
    have hz : S.coupling.full C = 0 := by
      rw [S.full_eq, synthCLM_apply]
      exact hc
    exact congrArg WithLp.ofLp (S.coupling.full_injective S.center_injective (hz.trans S.coupling.full.map_zero.symm))
  have hOld (t : ℚ) : Up (realCharLp ρ t) = productBaseVector ν t := S.lift_base t
  have hApp : productFamily ν (appendedMixedFreq A S.modes) = Fin.append old new := by
    let pf (b : MixedFreq (Fin S.dim)) := lift₂ ν (mixedChar b)
      (continuous_mixedChar b).measurable 1 (fun p ↦ (norm_mixedChar b p).le)
    funext i
    refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
    · rw [Fin.append_left]
      change pf (appendedMixedFreq A S.modes (Fin.castAdd S.size a)) = old a
      rw [appendedMixedFreq, Fin.append_left]
      exact (hOld (A.get a)).symm
    · rw [Fin.append_right]
      change pf (appendedMixedFreq A S.modes (Fin.natAdd A.length b)) = pf (S.modes b)
      rw [appendedMixedFreq, Fin.append_right]
  let B := max K (linePrefixFloor u) * Real.sqrt ((1 + Real.sqrt S.η) / (1 - Real.sqrt S.η))
  have hfinalPrefix : HPrefix (𝕜 := ℂ) (productFamily ν (appendedMixedFreq A S.modes)) B := by
    rw [hApp]
    exact append_small_angle_hPrefix old new hoPrefix hnPrefix (Real.sqrt_nonneg _) S.angle_lt_one angle
  have hfinalIndep : LinearIndependent ℂ (productFamily ν (appendedMixedFreq A S.modes)) := by
    rw [hApp]
    exact append_small_angle_independent old new hoIndependent hnIndependent
      (Real.sqrt_nonneg _) S.angle_lt_one angle

  have hESpan : (rationalOldSpan ρ A).map Up.toLinearMap = Old := by
    rw [rationalOldSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  let _ : FiniteDimensional ℂ Old := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  have hres : productBaseVector ν q - Old.starProjection (productBaseVector ν q) = d • e := by
    let f := realCharLp ρ q
    have hproj : Old.starProjection (Up f) = Up ((rationalOldSpan ρ A).starProjection f) := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · rw [← hESpan]
        exact ⟨_, (rationalOldSpan ρ A).starProjection_apply_mem f, rfl⟩
      · intro y hy
        rw [← hESpan] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        change ⟪Up f - Up ((rationalOldSpan ρ A).starProjection f), Up z⟫_ℂ = 0
        rw [← map_sub, LinearIsometry.inner_map_map]
        exact (Submodule.mem_orthogonal' _ _).mp
          ((rationalOldSpan ρ A).sub_starProjection_mem_orthogonal f) z hz
    rw [← hOld, show Up (realCharLp ρ q) = Up f from rfl, hproj, ← map_sub]
    change Up (rationalResidual ρ A q) = d • Up (rationalResidualUnit ρ A q)
    change Up (rationalResidual ρ A q) = (d : ℂ) • Up (rationalResidualUnit ρ A q)
    rw [← map_smul]
    exact (congrArg Up (norm_smul_rationalResidualUnit hr)).symm
  have hcap : (u / (1 + 2 * u)) / 4 < ‖New.starProjection e‖ ^ 2 := by
    change (u / (1 + 2 * u)) / 4 < _
    have hpos : 0 < u / (1 + 2 * u) := by positivity
    change u / (1 + 2 * u) - S.η ≤ ‖New.starProjection e‖ ^ 2 at hCapture
    linarith [S.η_lt_capture]
  obtain ⟨p, hp, hclose⟩ := residual_capture_candidate Old New (productBaseVector ν q) hres
    (by unfold e; rw [LinearIsometry.norm_map, he]) (norm_ne_zero_iff.mpr hr) hcap
  have hp' : p ∈ span ℂ (Set.range (productFamily ν (appendedMixedFreq A S.modes))) := by
    rw [hApp, span_range_finAppend, ← hF]
    exact hp
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℂ).mp hp'
  have hd : d ^ 2 = lineDistanceSq ρ LineWeight.one A q := by
    let D (μ : Measure ℝ) [IsFiniteMeasure μ] :=
      Metric.infDist (realCharLp μ q) (rationalOldSpan μ A : Set (Lp ℂ 2 μ)) ^ 2
    have hcongr {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (h : μ₁ = μ₂) :
        D μ₁ = D μ₂ := by subst μ₂; rfl
    change d ^ 2 = D (LineWeight.one.measure ρ)
    rw [hcongr (one_measure ρ)]
    dsimp only [D]
    rw [← (rationalOldSpan ρ A).dist_starProjection_eq_infDist, dist_eq_norm]
    rfl
  have hfinal :
      (∫ p, ‖evalMixedPoly (residualPoly (appendedMixedFreq A S.modes) q c) p‖ ^ 2 ∂ν) <
        lineContraction u * lineDistanceSq ρ LineWeight.one A q := by
    rw [← norm_sq_product_residual, show synth (productFamily ν (appendedMixedFreq A S.modes)) c = p from hc, ← hd]
    exact hclose
  exact ⟨⟨S.dim, S.size, S.size_pos, S.modes, S.aux_nonzero, S.aux_injective, S.graphWeight,
    S.fiberWeight, S.weight_eq, S.loss_lt, B, S.prefix_slack, hfinalPrefix, hfinalIndep, c, hfinal⟩⟩

end SchauderBasisOrbits
