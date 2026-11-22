module

public import LeanCode.Scalar.ActivationGeometry

@[expose] public section

open Filter Matrix MeasureTheory ContinuousLinearMap
open scoped ENNReal ComplexOrder MatrixOrder InnerProductSpace InnerProduct Topology

namespace SchauderBasisOrbits.Scalar

variable {r n : ℕ} (D : Data r n) {p : ℝ} (A : ActivationSet p)

private lemma activationRefColumn_cutoff_range (N : ℕ) :
    Set.range (activationRefColumn (n := n) (fourierCutoffNumbering N)) =
      Set.range (tupleFourierCutoffFamily 1 (ι := Fin (n + 1)) N) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    let q := activationIndex n (2 * N) i
    let k := fourierCutoffNumbering N q.2
    have hk : k ∈ Set.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [← fourierCutoffNumbering_range]
      exact ⟨q.2, rfl⟩
    exact ⟨(q.1, ⟨k, Finset.mem_Icc.mpr hk⟩), rfl⟩
  · rintro ⟨⟨i, k⟩, rfl⟩
    have hk : k.val ∈ Set.range (fourierCutoffNumbering N) := by
      rw [fourierCutoffNumbering_range]
      exact Finset.mem_Icc.mp k.property
    obtain ⟨j, hj⟩ := hk
    refine ⟨(activationIndex n (2 * N)).symm (i, j), ?_⟩
    simp [activationRefColumn, tupleFourierCutoffFamily, hj]

private lemma activationRefIsometry_cutoff_range (N : ℕ) :
    Set.range (activationRefIsometry (n := n) (fourierCutoffNumbering N)
      (fourierCutoffNumbering_injective N)) =
      {x | ∀ i, x i ∈ fourierCutoffSpan 1 N} := by
  ext x
  change x ∈ LinearMap.range (synthCLM (𝕜 := ℂ)
    (activationRefColumn (n := n) (fourierCutoffNumbering N))).toLinearMap ↔ _
  rw [range_synthCLM, activationRefColumn_cutoff_range]
  exact mem_span_tupleFourierCutoffFamily_iff 1 N x

/-- The canonical activated datum obtained at a symmetric finite Fourier cutoff. -/
noncomputable def activateCutoff (N : ℕ) : Data (r + 1) (activatedCount n (2 * N)) :=
  activate D A (fourierCutoffNumbering N) (fourierCutoffNumbering_zero N)
    (fourierCutoffNumbering_injective N)

private lemma activationRefIsometry_cutoff_zero (N : ℕ) :
    activationRefIsometry (n := n) (fourierCutoffNumbering N) (fourierCutoffNumbering_injective N)
      (EuclideanSpace.single 0 1) = tupleFourierChar 1 ((0 : Fin (n + 1)), (0 : ℤ)) := by
  rw [activationRefIsometry_single]
  simp [activationRefColumn]

private lemma inverse_cutoff_value (N : ℕ) :
    qform (clmGram ((activationEquiv D A).toContinuousLinearMap ∘L
        (activationRefIsometry (n := n) (fourierCutoffNumbering N)
          (fourierCutoffNumbering_injective N)).toContinuousLinearMap))⁻¹ (Pi.single 0 1) =
      (activateCutoff D A N).gram⁻¹ 0 0 := by
  rw [← activate_complexGram_eq_clmGram D A _ (fourierCutoffNumbering_zero N)]
  change qform (activateCutoff D A N).complexGram⁻¹ (Pi.single 0 1) = _
  rw [← (activateCutoff D A N).complexify_gram,
    complexify_inv_of_posDef (activateCutoff D A N).gram_posDef]
  simp [qform]

/-- The finite inverse values increase to the exact value at the ambient constant coordinate. -/
lemma activateCutoff_inv_zero_limit (hp : 0 ≤ p) :
    let f := fun N => (activateCutoff D A N).gram⁻¹ 0 0
    Monotone f ∧ Tendsto f atTop (𝓝 (1 + p * (D.gram⁻¹ 0 0 - 1))) := by
  let U (N : ℕ) := activationRefIsometry (n := n) (fourierCutoffNumbering N)
    (fourierCutoffNumbering_injective N)
  let e := tupleFourierChar 1 ((0 : Fin (n + 1)), (0 : ℤ))
  let d (N : ℕ) := Fin (activatedCount n (2 * N) + 1)
  let v (N : ℕ) : d N → ℂ := Pi.single 0 1
  have hnest : ∀ N M, N ≤ M → Set.range (U N) ⊆ Set.range (U M) := by
    intro N M h
    simp only [U, activationRefIsometry_cutoff_range]
    intro x hx i
    exact fourierCutoffSpan_mono 1 h (hx i)
  have hdense : Dense {x | ∃ N, x ∈ Set.range (U N)} := by
    simp only [U, activationRefIsometry_cutoff_range, Set.mem_ofPred_eq]
    exact dense_tuple_fourierCutoffSpan 1
  have he (N : ℕ) : U N (WithLp.toLp 2 (v N)) = e := activationRefIsometry_cutoff_zero N
  have h := inverse_gram_exhaustion (activationEquiv D A) d U hnest hdense e v he
  dsimp only at h
  have hfun : (fun N => qform (clmGram ((activationEquiv D A).toContinuousLinearMap ∘L
      (U N).toContinuousLinearMap))⁻¹ (v N)) = fun N => (activateCutoff D A N).gram⁻¹ 0 0 :=
    funext (inverse_cutoff_value D A)
  rw [hfun] at h
  have hlim :
      ‖((activationEquiv D A).symm.toContinuousLinearMap†) e‖ ^ 2 =
        1 + p * (D.gram⁻¹ 0 0 - 1) := by
    have hh := activated_inverse_metric_diagonal D A (fourierCutoffNumbering 0) hp
      (fourierCutoffNumbering_injective 0) 0
    rw [clmGram_entry] at hh
    change ⟪((activationEquiv D A).symm.toContinuousLinearMap†)
          (U 0 (EuclideanSpace.single 0 1)),
        ((activationEquiv D A).symm.toContinuousLinearMap†)
          (U 0 (EuclideanSpace.single 0 1))⟫_ℂ = _ at hh
    rw [show U 0 (EuclideanSpace.single 0 1) = e from he 0] at hh
    have hr := congrArg RCLike.re hh
    rw [inner_self_eq_norm_sq] at hr
    change _ = (↑(1 + p * (D.gram⁻¹ _ _ - 1)) : ℂ).re at hr
    simpa only [activationIndex_zero, Complex.ofReal_re] using hr
  rw [hlim] at h
  exact h

private lemma gain_limit_value :
    (1 - p * D.loss) * (1 + p * (D.gram⁻¹ 0 0 - 1)) - 1 =
      activatedGain D.loss D.gain p := by
  have hg : D.gram⁻¹ 0 0 = (1 + D.gain) / D.mass := by
    apply (eq_div_iff D.mass_pos.ne').2
    rw [mul_comm, D.mass_mul_gram_inv_zero_zero]
  rw [hg, activatedGain, Data.loss, sub_sub_cancel]
  field_simp [D.mass_pos.ne']
  ring

/-- The truncated gains increase to the rare-activation limit in the manuscript. -/
lemma activateCutoff_gain_limit (hp : 0 ≤ p) :
    let f := fun N => (activateCutoff D A N).gain
    Monotone f ∧ Tendsto f atTop (𝓝 (activatedGain D.loss D.gain p)) := by
  let f (N : ℕ) := (activateCutoff D A N).gram⁻¹ 0 0
  let M := 1 - p * D.loss
  have hm (N : ℕ) : (activateCutoff D A N).mass = M :=
    activate_mass D A _ hp _ _
  have hM : 0 < M := hm 0 ▸ (activateCutoff D A 0).mass_pos
  have hg (N : ℕ) : (activateCutoff D A N).gain = M * f N - 1 := by
    have h := (activateCutoff D A N).mass_mul_gram_inv_zero_zero
    rw [hm] at h
    change M * f N = _ at h
    linarith only [h]
  simp_rw [hg]
  have h := activateCutoff_inv_zero_limit D A hp
  refine ⟨fun N M' hNM => sub_le_sub_right (mul_le_mul_of_nonneg_left (h.1 hNM) hM.le) _, ?_⟩
  rw [← gain_limit_value D (p := p)]
  exact (tendsto_const_nhds.mul h.2).sub tendsto_const_nhds

/-- A finite auxiliary family retains any prescribed fraction of the limiting positive gain. -/
lemma exists_activateCutoff_gain (hp : 0 ≤ p) (hzp : 0 < activatedGain D.loss D.gain p)
    {α : ℝ} (hα : 0 < α) :
    ∃ N, (1 - α) * activatedGain D.loss D.gain p ≤ (activateCutoff D A N).gain ∧
      (activateCutoff D A N).gain ≤ activatedGain D.loss D.gain p := by
  have h := activateCutoff_gain_limit D A hp
  have hlt : (1 - α) * activatedGain D.loss D.gain p < activatedGain D.loss D.gain p := by
    nlinarith only [mul_pos hα hzp]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp h.2).1 _ hlt)
  refine ⟨N, (hN N le_rfl).le, ?_⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds h.2
    (eventually_atTop.mpr ⟨N, fun M hNM => h.1 hNM⟩)

end SchauderBasisOrbits.Scalar
