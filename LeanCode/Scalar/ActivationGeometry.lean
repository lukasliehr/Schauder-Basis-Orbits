module

public import LeanCode.Scalar.Activation
public import LeanCode.Finite.Tuples
public import LeanCode.Scalar.MatrixMix

@[expose] public section

open MeasureTheory Matrix ContinuousLinearMap
open scoped ENNReal ComplexConjugate ComplexOrder MatrixOrder InnerProductSpace InnerProduct

namespace SchauderBasisOrbits.Scalar

local notation "𝕋" => UnitAddCircle
local notation "μ𝕋" => (@AddCircle.haarAddCircle 1 _)

variable {r n m : ℕ} (D : Data r n) {p : ℝ} (A : ActivationSet p)
variable (Y : Fin (m + 1) → ℤ)

noncomputable def activationRefColumn (i : Fin (activatedCount n m + 1)) :
    HilbertTuple (Fin (n + 1)) (CircleL₂ 1) :=
  tupleFourierChar 1 ((activationIndex n m i).1, Y (activationIndex n m i).2)

lemma activationRefColumn_orthonormal (hY : Function.Injective Y) :
    Orthonormal ℂ (activationRefColumn (n := n) Y) := by
  apply (orthonormal_tupleFourierChar (ι := Fin (n + 1)) 1).comp
  intro i j h
  apply (activationIndex n m).injective
  have h₁ := congrArg (fun q : Fin (n + 1) × ℤ => q.1) h
  have h₂ := congrArg (fun q : Fin (n + 1) × ℤ => q.2) h
  exact Prod.ext h₁ (hY h₂)

/-- Isometric inclusion of the finite reference family, before activation. -/
noncomputable def activationRefIsometry (hY : Function.Injective Y) :
    EuclideanSpace ℂ (Fin (activatedCount n m + 1)) →ₗᵢ[ℂ]
      HilbertTuple (Fin (n + 1)) (CircleL₂ 1) where
  toLinearMap := (synthCLM (activationRefColumn Y)).toLinearMap
  norm_map' x := by
    change ‖synthCLM (activationRefColumn Y) x‖ = ‖x‖
    rw [synthCLM_apply]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [← qform_gram, Matrix.gram_eq_one_iff_orthonormal.2 (activationRefColumn_orthonormal Y hY),
      qform_one, WithLp.toLp_ofLp]

lemma activationRefIsometry_single (hY : Function.Injective Y) (i : Fin (activatedCount n m + 1)) :
    activationRefIsometry Y hY (EuclideanSpace.single i 1) =
      activationRefColumn Y i := by
  change synthCLM (activationRefColumn Y) (EuclideanSpace.single i 1) = _
  rw [synthCLM_apply]
  have hs : WithLp.ofLp (EuclideanSpace.single i (1 : ℂ)) = Pi.single i 1 := rfl
  rw [hs, synth_single, one_smul]

/-- The operator taking the ordinary tuple norm to the activated norm. -/
noncomputable def activationEquiv :
    HilbertTuple (Fin (n + 1)) (CircleL₂ 1) ≃L[ℂ]
      HilbertTuple (Fin (n + 1)) (CircleL₂ 1) :=
  HilbertTuple.activatedSqrtEquiv D.complexGram D.complexGram_posDef
    (lpIndicatorProjection μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier)

lemma clmGram_entry {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (X : EuclideanSpace ℂ ι →L[ℂ] H) (i j : ι) :
    clmGram X i j = ⟪X (EuclideanSpace.single i 1), X (EuclideanSpace.single j 1)⟫_ℂ := by
  rw [← adjoint_inner_right]
  change clmGram X i j =
    ⟪EuclideanSpace.single i 1, (X† ∘L X) (EuclideanSpace.single j 1)⟫_ℂ
  rw [← toEuclideanCLM_clmGram]
  rw [EuclideanSpace.inner_single_left]
  have hj : (EuclideanSpace.single j (1 : ℂ)) = WithLp.toLp 2 (Pi.single j 1) := rfl
  rw [hj, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one]
  simp

private lemma inner_single_tuple {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (i : ι) (f : E) (x : HilbertTuple ι E) :
    ⟪PiLp.single 2 i f, x⟫_ℂ = ⟪f, x i⟫_ℂ := by
  simp only [PiLp.inner_apply, PiLp.single_apply]
  have h (j : ι) : ⟪(if j = i then f else 0), x j⟫_ℂ = if j = i then ⟪f, x i⟫_ℂ else 0 := by
    by_cases hj : j = i <;> simp [hj]
  simp_rw [h]
  simp

private lemma inner_single_activated {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B : Matrix ι ι ℂ) (P : E →L[ℂ] E) (i j : ι) (f g : E) :
    ⟪PiLp.single 2 i f, HilbertTuple.activated B P (PiLp.single 2 j g)⟫_ℂ =
      (1 : Matrix ι ι ℂ) i j * ⟪f, g⟫_ℂ +
        (B - 1) i j * ⟪f, P g⟫_ℂ := by
  rw [inner_single_tuple]
  change ⟪f, (PiLp.single 2 j g : HilbertTuple ι E) i +
      (HilbertTuple.rowAction (B - 1) (HilbertTuple.diagonalMap P (PiLp.single 2 j g))) i⟫_ℂ = _
  simp only [HilbertTuple.rowAction_apply, HilbertTuple.diagonalMap_apply, PiLp.single_apply,
    apply_ite P, map_zero, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    inner_add_right, inner_smul_right, Matrix.one_apply]
  by_cases hij : i = j <;> simp [hij, eq_comm]

private lemma inner_fourierLp_pair (k l : ℤ) :
    ⟪@fourierLp 1 _ 2 _ k, @fourierLp 1 _ 2 _ l⟫_ℂ =
      ∫ y, conj (fourier k y) * fourier l y ∂μ𝕋 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [@coeFn_fourierLp 1 _ 2 _ k, @coeFn_fourierLp 1 _ 2 _ l] with y hk hl
  rw [hk, hl, RCLike.inner_apply']

private lemma inner_fourierLp_indicator (k l : ℤ) :
    ⟪@fourierLp 1 _ 2 _ k, lpIndicatorProjection μ𝕋 A.measurable_carrier
      (@fourierLp 1 _ 2 _ l)⟫_ℂ =
      ∫ y in A.carrier, conj (fourier k y) * fourier l y ∂μ𝕋 := by
  rw [L2.inner_def, ← integral_indicator A.measurable_carrier]
  apply integral_congr_ae
  filter_upwards [ae_lpIndicatorProjection μ𝕋 A.measurable_carrier (@fourierLp 1 _ 2 _ l),
    @coeFn_fourierLp 1 _ 2 _ k, @coeFn_fourierLp 1 _ 2 _ l] with y hf hk hl
  rw [RCLike.inner_apply', hk, hf]
  by_cases hy : y ∈ A.carrier
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hl]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

private lemma activationGramEntry_integral (i j : Fin (n + 1)) (k l : ℤ) :
    (∫ y, activationGramEntry D A i j y * (conj (fourier k y) * fourier l y) ∂μ𝕋) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j * ⟪@fourierLp 1 _ 2 _ k, @fourierLp 1 _ 2 _ l⟫_ℂ +
      (D.complexGram - 1) i j * ⟪@fourierLp 1 _ 2 _ k,
        lpIndicatorProjection μ𝕋 A.measurable_carrier (@fourierLp 1 _ 2 _ l)⟫_ℂ := by
  classical
  rw [inner_fourierLp_pair, inner_fourierLp_indicator, ← integral_indicator A.measurable_carrier,
    ← integral_const_mul, ← integral_const_mul]
  let f : 𝕋 → ℂ := fun y => conj (fourier k y) * fourier l y
  have hf : Integrable f μ𝕋 := by
    apply Integrable.of_bound (((Complex.continuous_conj.comp (fourier k).continuous).mul
      (fourier l).continuous).measurable.aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun y => by
      simp [f, norm_mul, fourier_apply])
  rw [← integral_add (hf.const_mul _) ((hf.indicator A.measurable_carrier).const_mul _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    by_cases hy : y ∈ A.carrier <;>
      simp [activationGramEntry, f, hy, sub_mul] <;> ring)

/-- The activated Gram is the Gram of the standard tuple realization of the finite family. -/
lemma activate_complexGram_eq_clmGram (hY₀ : Y 0 = 0) (hY : Function.Injective Y) :
    (activate D A Y hY₀ hY).complexGram =
      clmGram ((activationEquiv D A).toContinuousLinearMap ∘L
        (activationRefIsometry (n := n) Y hY).toContinuousLinearMap) := by
  ext i j
  rw [activate_complexGram, clmGram_entry]
  change _ = ⟪activationEquiv D A (activationRefIsometry Y hY (EuclideanSpace.single i 1)),
    activationEquiv D A (activationRefIsometry Y hY (EuclideanSpace.single j 1))⟫_ℂ
  rw [activationRefIsometry_single, activationRefIsometry_single]
  have hgram := HilbertTuple.activatedSqrtEquiv_gram D.complexGram D.complexGram_posDef
    (lpIndicatorProjection μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_adjoint μ𝕋 A.measurable_carrier)
  change _ = ⟪(activationEquiv D A).toContinuousLinearMap (activationRefColumn Y i),
    (activationEquiv D A).toContinuousLinearMap (activationRefColumn Y j)⟫_ℂ
  rw [← adjoint_inner_right]
  change _ = ⟪activationRefColumn Y i,
    (((activationEquiv D A).toContinuousLinearMap)† * (activationEquiv D A).toContinuousLinearMap)
      (activationRefColumn Y j)⟫_ℂ
  rw [show ((activationEquiv D A).toContinuousLinearMap)† * (activationEquiv D A).toContinuousLinearMap =
    HilbertTuple.activated D.complexGram (lpIndicatorProjection μ𝕋 A.measurable_carrier) from hgram]
  change _ = ⟪PiLp.single 2 (activationIndex n m i).1 (@fourierLp 1 _ 2 _ (Y (activationIndex n m i).2)),
    HilbertTuple.activated D.complexGram (lpIndicatorProjection μ𝕋 A.measurable_carrier)
      (PiLp.single 2 (activationIndex n m j).1 (@fourierLp 1 _ 2 _ (Y (activationIndex n m j).2)))⟫_ℂ
  rw [inner_single_activated]
  exact activationGramEntry_integral D A _ _ _ _

lemma activate_inverse_compression (hY₀ : Y 0 = 0) (hY : Function.Injective Y) :
    ((activate D A Y hY₀ hY).complexGram)⁻¹ ≤
      clmGram ((activationEquiv D A).symm.toContinuousLinearMap† ∘L
        (activationRefIsometry (n := n) Y hY).toContinuousLinearMap) := by
  rw [activate_complexGram_eq_clmGram]
  exact clmGram_inv_compression _ (activationRefIsometry _ hY)


private lemma inner_fourierLp_indicator_self (hp : 0 ≤ p) (k : ℤ) :
    ⟪@fourierLp 1 _ 2 _ k, lpIndicatorProjection μ𝕋 A.measurable_carrier
      (@fourierLp 1 _ 2 _ k)⟫_ℂ = (p : ℂ) := by
  rw [inner_fourierLp_indicator]
  have h (y : 𝕋) : conj (fourier k y) * fourier k y = (1 : ℂ) := by
    rw [Complex.conj_mul']
    simp [fourier_apply]
  simp_rw [h]
  rw [setIntegral_const]
  have hμ : μ𝕋 A.carrier = ENNReal.ofReal p := A.measure_carrier
  simp [Measure.real, hμ, ENNReal.toReal_ofReal hp, Complex.real_smul]

/-- Before compressing to the finite family, the inverse metric has this exact diagonal. -/
lemma activated_inverse_metric_diagonal (hp : 0 ≤ p) (hY : Function.Injective Y)
    (i : Fin (activatedCount n m + 1)) :
    clmGram ((activationEquiv D A).symm.toContinuousLinearMap† ∘L
        (activationRefIsometry (n := n) Y hY).toContinuousLinearMap) i i =
      (1 + p * (D.gram⁻¹ (activationIndex n m i).1 (activationIndex n m i).1 - 1) : ℝ) := by
  rw [clmGram_entry]
  let U := activationRefIsometry (n := n) Y hY
  let S := (activationEquiv D A).symm.toContinuousLinearMap
  change ⟪(S†) (U (EuclideanSpace.single i 1)), (S†) (U (EuclideanSpace.single i 1))⟫_ℂ = _
  change ⟪(S†) (activationRefIsometry Y hY (EuclideanSpace.single i 1)),
    (S†) (activationRefIsometry Y hY (EuclideanSpace.single i 1))⟫_ℂ = _
  rw [activationRefIsometry_single, ← adjoint_inner_right, adjoint_adjoint]
  have hgram := HilbertTuple.activatedSqrtEquiv_gram_inverse D.complexGram D.complexGram_posDef
    (lpIndicatorProjection μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_adjoint μ𝕋 A.measurable_carrier)
  change ⟪activationRefColumn Y i, (S * S†) (activationRefColumn Y i)⟫_ℂ = _
  rw [show S * S† = HilbertTuple.activated D.complexGram⁻¹
    (lpIndicatorProjection μ𝕋 A.measurable_carrier) from hgram]
  let a := (activationIndex n m i).1
  let k := Y (activationIndex n m i).2
  change ⟪PiLp.single 2 a (@fourierLp 1 _ 2 _ k), HilbertTuple.activated D.complexGram⁻¹
    (lpIndicatorProjection μ𝕋 A.measurable_carrier) (PiLp.single 2 a (@fourierLp 1 _ 2 _ k))⟫_ℂ = _
  rw [inner_single_activated, inner_fourierLp_indicator_self A hp,
    (orthonormal_iff_ite.mp (@orthonormal_fourier 1 _)) k k,
    ← D.complexify_gram, complexify_inv_of_posDef D.gram_posDef]
  simp only [ite_true, Matrix.one_apply, mul_one, Matrix.sub_apply, complexify_apply,
    Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- The diagonal comparison for the truncated inverse of the activated Gram. -/
lemma activate_gram_inv_diagonal_le (hp : 0 ≤ p) (hY₀ : Y 0 = 0) (hY : Function.Injective Y)
    (i : Fin (activatedCount n m + 1)) :
    (activate D A Y hY₀ hY).gram⁻¹ i i ≤
      1 + p * (D.gram⁻¹ (activationIndex n m i).1 (activationIndex n m i).1 - 1) := by
  let E := activate D A Y hY₀ hY
  have hd := Matrix.PosSemidef.diag_nonneg
    (Matrix.le_iff.mp (activate_inverse_compression D A Y hY₀ hY)) (i := i)
  rw [Matrix.sub_apply, sub_nonneg, activated_inverse_metric_diagonal D A Y hp hY] at hd
  change E.complexGram⁻¹ i i ≤ _ at hd
  rw [← E.complexify_gram, complexify_inv_of_posDef E.gram_posDef, complexify_apply] at hd
  exact Complex.real_le_real.mp hd

/-- The activated inverse-diagonal bound used for nonconstant modes concerns the
unnormalized centered Gram. -/
lemma activate_centerGram_inv_diagonal_le (hp : 0 ≤ p) (hY₀ : Y 0 = 0) (hY : Function.Injective Y)
    (i : Fin (activatedCount n m)) :
    (activate D A Y hY₀ hY).centerGram⁻¹ i i ≤
      1 + p * (D.gram⁻¹ (activationIndex n m i.succ).1 (activationIndex n m i.succ).1 - 1) := by
  rw [← Data.gram_inv_succ_succ]
  exact activate_gram_inv_diagonal_le D A Y hp hY₀ hY i.succ


set_option maxHeartbeats 800000 in
/-- The ambient activated form is bounded by the scalar matrix norm when it is at least one. -/
private lemma activated_qform_bound {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (B : Matrix ι ι ℂ) (P : E →L[ℂ] E) (hP : IsIdempotentElem P) (hPa : P† = P)
    (hB : 1 ≤ opNorm B) (x : HilbertTuple ι E) :
    (⟪x, HilbertTuple.activated B P x⟫_ℂ).re ≤ opNorm B * ‖x‖ ^ 2 := by
  let proj : HilbertTuple ι E →L[ℂ] HilbertTuple ι E := HilbertTuple.diagonalMap P
  let u := proj x
  let v := x - u
  have hu : proj u = u := by
    change (proj * proj) x = _
    simp only [proj, ← HilbertTuple.diagonalMap_mul, hP.eq, u]
  have hv : proj v = 0 := by
    simp only [v, map_sub, hu, u, sub_self]
  have ha : proj† = proj := by
    dsimp [proj]
    rw [← HilbertTuple.diagonalMap_adjoint, hPa]
  have horth (z : HilbertTuple ι E) : ⟪v, proj z⟫_ℂ = 0 := by
    rw [← adjoint_inner_left, ha, hv, inner_zero_left]
  let row : HilbertTuple ι E →L[ℂ] HilbertTuple ι E := HilbertTuple.rowAction B
  let y := row u
  have hy : proj y = y := by
    change (proj * row) u = _
    have h := (HilbertTuple.rowAction_commute_diagonalMap B P).eq
    change row * proj = proj * row at h
    rw [← h]
    change row (proj u) = _
    rw [hu]
  have hvu : ⟪v, u⟫_ℂ = 0 := horth x
  have huv : ⟪u, v⟫_ℂ = 0 := by rw [← inner_conj_symm, hvu, map_zero]
  have hvy : ⟪v, y⟫_ℂ = 0 := by rw [← hy]; exact horth y
  have hx : v + u = x := sub_add_cancel _ _
  have hact : HilbertTuple.activated B P x = v + y := by
    rw [HilbertTuple.activated, HilbertTuple.rowAction_sub, HilbertTuple.rowAction_one]
    change x + (row u - u) = (x - u) + row u
    abel
  calc
    _ = ‖v‖ ^ 2 + (⟪u, y⟫_ℂ).re := by
      rw [hact, ← hx]
      simp only [inner_add_left, inner_add_right, huv, hvy, add_zero, zero_add, Complex.add_re]
      rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
    _ ≤ ‖v‖ ^ 2 + opNorm B * ‖u‖ ^ 2 := by
      have hr : ‖row‖ ≤ opNorm B := HilbertTuple.norm_rowAction_le B
      have hyb : ‖y‖ ≤ opNorm B * ‖u‖ :=
        (row.le_opNorm u).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
      have hiy : (⟪u, y⟫_ℂ).re ≤ ‖u‖ * ‖y‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm u y)
      have h := mul_le_mul_of_nonneg_left hyb (norm_nonneg u)
      nlinarith only [hiy, h]
    _ ≤ opNorm B * (‖v‖ ^ 2 + ‖u‖ ^ 2) := by
      rw [mul_add]
      have h := mul_le_mul_of_nonneg_right hB (sq_nonneg ‖v‖)
      linarith only [h]
    _ = opNorm B * ‖x‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v u hvu
      rw [hx] at h
      simpa only [pow_two] using congrArg (fun q : ℝ => opNorm B * q) h.symm

lemma activate_gram_inverse_le_opNorm (hY₀ : Y 0 = 0) (hY : Function.Injective Y) :
    (activate D A Y hY₀ hY).complexGram⁻¹ ≤ opNorm (D.complexGram⁻¹) • 1 := by
  let h := opNorm (D.complexGram⁻¹)
  have hI : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ≤ D.complexGram⁻¹ := by
    simpa using matrix_inv_le_inv D.complexGram_posDef D.complexGram_bounds.2
  have hh : D.complexGram⁻¹ ≤ h • 1 :=
    (opNorm_psd_le_iff D.complexGram_posDef.inv.posSemidef).mp le_rfl
  have h₁ : 1 ≤ h := by
    have hD := Matrix.PosSemidef.diag_nonneg (Matrix.le_iff.mp (hI.trans hh))
      (i := (0 : Fin (n + 1)))
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, ite_true,
      Complex.real_smul, mul_one, sub_nonneg] at hD
    exact Complex.real_le_real.mp (by simpa using hD)
  refine (activate_inverse_compression D A Y hY₀ hY).trans ?_
  let U := activationRefIsometry (n := n) Y hY
  let S := (activationEquiv D A).symm.toContinuousLinearMap
  apply matrix_le_of_qform_le (clmGram_isHermitian _) (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  intro c
  rw [qform_clmGram, qform_smul, qform_one]
  change ‖(S†) (U (WithLp.toLp 2 c))‖ ^ 2 ≤ h * ‖WithLp.toLp 2 c‖ ^ 2
  let x := U (WithLp.toLp 2 c)
  have hSq : (⟪x, (S * S†) x⟫_ℂ).re = ‖(S†) x‖ ^ 2 := by
    change (⟪x, S ((S†) x)⟫_ℂ).re = _
    rw [← adjoint_inner_left, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  change ‖(S†) x‖ ^ 2 ≤ h * ‖WithLp.toLp 2 c‖ ^ 2
  rw [← U.norm_map, ← hSq]
  have hgram := HilbertTuple.activatedSqrtEquiv_gram_inverse D.complexGram D.complexGram_posDef
    (lpIndicatorProjection μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_adjoint μ𝕋 A.measurable_carrier)
  rw [show S * S† = HilbertTuple.activated D.complexGram⁻¹
    (lpIndicatorProjection μ𝕋 A.measurable_carrier) from hgram]
  exact activated_qform_bound _ _ (lpIndicatorProjection_idempotent μ𝕋 A.measurable_carrier)
    (lpIndicatorProjection_adjoint μ𝕋 A.measurable_carrier) h₁ x

lemma activate_centerGram_inverse_le_opNorm (hY₀ : Y 0 = 0) (hY : Function.Injective Y) :
    (activate D A Y hY₀ hY).centerGram⁻¹ ≤ opNorm (D.gram⁻¹) • 1 := by
  let E := activate D A Y hY₀ hY
  have h := activate_gram_inverse_le_opNorm D A Y hY₀ hY
  change E.complexGram⁻¹ ≤ opNorm (D.complexGram⁻¹) • 1 at h
  rw [← E.complexify_gram, ← D.complexify_gram, complexify_inv_of_posDef E.gram_posDef,
    complexify_inv_of_posDef D.gram_posDef, opNorm_complexify, ← complexify_one,
    ← complexify_smul] at h
  have hr : E.gram⁻¹ ≤ opNorm (D.gram⁻¹) • 1 := complexify_le_iff.mp h
  rw [Matrix.le_iff] at hr ⊢
  convert hr.submatrix Fin.succ using 1
  ext i j
  simp [E.gram_inv_succ_succ, Matrix.one_apply]
  rfl

end SchauderBasisOrbits.Scalar
