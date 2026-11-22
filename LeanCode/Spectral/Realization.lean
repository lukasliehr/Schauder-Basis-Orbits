module

public import LeanCode.Spectral.Measure
public import LeanCode.Spectral.GramIsometry

@[expose] public section

open Function MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace SchauderBasisOrbits

theorem memLp_realChar_mul (μ : Measure ℝ) (t : ℝ) (f : Lp ℂ 2 μ) :
    MemLp (fun x ↦ realChar t x * f x) 2 μ := by
  apply (Lp.memLp f).congr_norm
    ((continuous_realChar t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [] with x
  simp

noncomputable def realCharMulLp (μ : Measure ℝ) (t : ℝ) (f : Lp ℂ 2 μ) :
    Lp ℂ 2 μ := (memLp_realChar_mul μ t f).toLp _

private theorem ae_realCharMulLp (μ : Measure ℝ) (t : ℝ) (f : Lp ℂ 2 μ) :
    ⇑(realCharMulLp μ t f) =ᵐ[μ] fun x ↦ realChar t x * f x :=
  MemLp.coeFn_toLp _

theorem realCharMulLp_neg_left_inv (μ : Measure ℝ) (t : ℝ) (f : Lp ℂ 2 μ) :
    realCharMulLp μ (-t) (realCharMulLp μ t f) = f := by
  apply Lp.ext
  filter_upwards [ae_realCharMulLp μ (-t) (realCharMulLp μ t f), ae_realCharMulLp μ t f] with x hn ht
  rw [hn, ht, ← mul_assoc, ← realChar_add, neg_add_cancel, realChar_zero, one_mul]

/-- Unitary multiplication by the real character on L² of any measure on the line. -/
noncomputable def realCharMul (μ : Measure ℝ) (t : ℝ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := realCharMulLp μ t
  invFun := realCharMulLp μ (-t)
  left_inv := realCharMulLp_neg_left_inv μ t
  right_inv f := by simpa only [neg_neg] using realCharMulLp_neg_left_inv μ (-t) f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [ae_realCharMulLp μ t (f + g), ae_realCharMulLp μ t f, ae_realCharMulLp μ t g,
      Lp.coeFn_add f g, Lp.coeFn_add (realCharMulLp μ t f) (realCharMulLp μ t g)] with x ha hf hg hfg hsum
    rw [ha, hsum, hfg]
    simp [hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [ae_realCharMulLp μ t (c • f), ae_realCharMulLp μ t f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (realCharMulLp μ t f)] with x ha hf hcf hprod
    simp only [RingHom.id_apply]
    rw [ha, hprod, hcf]
    simp only [Pi.smul_apply, smul_eq_mul, hf]
    ring
  norm_map' f := by
    apply Lp.norm_eq_norm_of_ae_eq
    filter_upwards [ae_realCharMulLp μ t f] with x hx
    simp [hx]

theorem ae_realCharMul (μ : Measure ℝ) (t : ℝ) (f : Lp ℂ 2 μ) :
    ⇑(realCharMul μ t f) =ᵐ[μ] fun x ↦ realChar t x * f x :=
  ae_realCharMulLp μ t f

@[simp] theorem realCharMul_symm (μ : Measure ℝ) (t : ℝ) :
    (realCharMul μ t).symm = realCharMul μ (-t) := by
  ext f
  rfl

theorem realCharMul_add (μ : Measure ℝ) (s t : ℝ) (f : Lp ℂ 2 μ) :
    realCharMul μ (s + t) f = realCharMul μ s (realCharMul μ t f) := by
  apply Lp.ext
  filter_upwards [ae_realCharMul μ (s + t) f, ae_realCharMul μ s (realCharMul μ t f),
    ae_realCharMul μ t f] with x hst hs ht
  rw [hst, hs, ht, realChar_add, mul_assoc]

theorem realCharMul_realCharLp (μ : Measure ℝ) [IsFiniteMeasure μ] (s t : ℝ) :
    realCharMul μ s (realCharLp μ t) = realCharLp μ (s + t) := by
  apply Lp.ext
  filter_upwards [ae_realCharMul μ s (realCharLp μ t), ae_realCharLp μ t,
    ae_realCharLp μ (s + t)] with x h h₁ h₂
  rw [h, h₁, h₂, realChar_add]

variable {H : Type*} [ComplexHilbertSpace H] {U : ℝ → UnitaryOperator H}

/-- A probability spectral measure and a cyclic orbit's unitary realization on its L² space. -/
structure CyclicSpectralRealization (U : ℝ → UnitaryOperator H) (v : H) where
  μ : ProbabilityMeasure ℝ
  S : Lp ℂ 2 μ.toMeasure ≃ₗᵢ[ℂ] H
  map_character : ∀ t, S (realCharLp μ.toMeasure t) = U t v
  intertwines : ∀ t f, S (realCharMul μ.toMeasure t f) = U t (S f)

theorem exists_cyclicSpectralRealization (hU : IsStronglyContinuousGroup U) {v : H}
    (hvc : IsCyclicVector U v) (hv : ‖v‖ = 1) : Nonempty (CyclicSpectralRealization U v) := by
  obtain ⟨μ, hμ⟩ := orbit_spectral_probability hU hv
  have hgram (s t : ℝ) :
      ⟪realCharLp μ.toMeasure s, realCharLp μ.toMeasure t⟫_ℂ = ⟪U s v, U t v⟫_ℂ := by
    rw [inner_realCharLp, orbit_inner_eq_coefficient hU, hμ]
  have hvc' : Dense (Submodule.span ℂ (Set.range fun t : ℝ ↦ U t v) : Set H) := by
    simpa only [IsCyclicVector, Set.range] using hvc
  obtain ⟨S, hS⟩ := exists_isometry_of_gram_eq hgram (dense_span_realCharLp μ.toMeasure) hvc'
  refine ⟨⟨μ, S, hS, fun t f ↦ ?_⟩⟩
  let A := S.toLinearIsometry.toContinuousLinearMap.comp
    (realCharMul μ.toMeasure t).toLinearIsometry.toContinuousLinearMap
  let B := (U t).toLinearIsometry.toContinuousLinearMap.comp S.toLinearIsometry.toContinuousLinearMap
  have hAB : A = B := by
    apply ContinuousLinearMap.ext_on (dense_span_realCharLp μ.toMeasure)
    rintro _ ⟨s, rfl⟩
    change S (realCharMul μ.toMeasure t (realCharLp μ.toMeasure s)) =
      U t (S (realCharLp μ.toMeasure s))
    rw [realCharMul_realCharLp, hS, hS, unitary_group_add hU]
  exact DFunLike.congr_fun hAB f

theorem CyclicSpectralRealization.nullSingletonClass {v : H}
    (R : CyclicSpectralRealization U v) (hU : ¬ ∃ a, IsCommonEigenvector U a) :
    NullSingletonClass R.μ.toMeasure where
  measure_singleton x := by
    by_contra hμ
    let f : ℝ → ℂ := ({x} : Set ℝ).indicator (fun _ ↦ 1)
    have hf : Measurable f := measurable_const.indicator (measurableSet_singleton x)
    have hfB (y : ℝ) : ‖f y‖ ≤ 1 := by
      change ‖({x} : Set ℝ).indicator (fun _ ↦ (1 : ℂ)) y‖ ≤ 1
      by_cases hy : y ∈ ({x} : Set ℝ)
      · rw [indicator_of_mem hy]; simp
      · rw [indicator_of_notMem hy]; simp
    let h := lift₂ R.μ.toMeasure f hf 1 hfB
    have hrep : ⇑h =ᵐ[R.μ.toMeasure] f := ae_lift₂ _ _ _ _ _
    have hne : h ≠ 0 := by
      intro hh
      have he : f =ᵐ[R.μ.toMeasure] 0 :=
        hrep.symm.trans (hh ▸ Lp.coeFn_zero ℂ 2 R.μ.toMeasure)
      have ha : ∀ᵐ y ∂R.μ.toMeasure, y ≠ x :=
        he.mono fun y hy hyx ↦ by subst y; simp [f] at hy
      exact hμ (by simpa using ae_iff.mp ha)
    have hmul (t : ℝ) : realCharMul R.μ.toMeasure t h = realChar t x • h := by
      apply Lp.ext
      filter_upwards [ae_realCharMul R.μ.toMeasure t h, Lp.coeFn_smul (realChar t x) h, hrep]
        with y hm hs hr
      simp only [hm, hs, Pi.smul_apply, smul_eq_mul, hr]
      by_cases hy : y = x
      · subst y
        rfl
      · simp [f, hy]
    apply hU
    refine ⟨R.S h, ?_, fun t ↦ ?_⟩
    · intro h0
      exact hne (R.S.injective (h0.trans (R.S.map_zero).symm))
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨realChar t x, ?_⟩
      rw [← R.intertwines, hmul, map_smul]

end SchauderBasisOrbits
