module

public import LeanCode.Finite.Families

@[expose] public section

/-! Scalar matrices acting on finite tuples with the Hilbert sum-of-squares norm. -/

open Matrix ContinuousLinearMap MeasureTheory
open scoped BigOperators ComplexOrder InnerProductSpace InnerProduct MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace SchauderBasisOrbits

variable {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Finite Hilbert tuples, using the ℓ² norm. -/
abbrev HilbertTuple (ι E : Type*) := PiLp 2 (fun _ : ι ↦ E)

namespace HilbertTuple

/-- Row action of a scalar matrix on a finite tuple of Hilbert vectors. -/
def rowAction (A : Matrix ι ι 𝕜) : HilbertTuple ι E →L[𝕜] HilbertTuple ι E :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι ↦ E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : ι ↦ ∑ j, A i j • PiLp.proj (𝕜 := 𝕜) 2 (fun _ : ι ↦ E) j)

omit [DecidableEq ι] in
@[simp] theorem rowAction_apply (A : Matrix ι ι 𝕜) (x : HilbertTuple ι E) (i : ι) :
    rowAction A x i = ∑ j, A i j • x j := by
  change (∑ j, A i j • PiLp.proj (𝕜 := 𝕜) 2 (β := fun _ : ι ↦ E) j) x = _
  simp only [sum_apply, smul_apply, PiLp.proj_apply]

@[simp] theorem rowAction_one : rowAction (1 : Matrix ι ι 𝕜) = (1 : HilbertTuple ι E →L[𝕜] _) := by
  ext x i
  simp [Matrix.one_apply]

omit [DecidableEq ι] in
@[simp] theorem rowAction_add (A B : Matrix ι ι 𝕜) :
    rowAction (A + B) = (rowAction A : HilbertTuple ι E →L[𝕜] _) + rowAction B := by
  ext x i
  simp [add_smul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
@[simp] theorem rowAction_sub (A B : Matrix ι ι 𝕜) :
    rowAction (A - B) = (rowAction A : HilbertTuple ι E →L[𝕜] _) - rowAction B := by
  ext x i
  simp [sub_smul, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
@[simp] theorem rowAction_real_smul (a : ℝ) (A : Matrix ι ι 𝕜) :
    rowAction (a • A) = (a : 𝕜) • (rowAction A : HilbertTuple ι E →L[𝕜] _) := by
  ext x i
  simp [RCLike.real_smul_eq_coe_mul, mul_smul, Finset.smul_sum]

omit [DecidableEq ι] in
@[simp] theorem rowAction_mul (A B : Matrix ι ι 𝕜) :
    rowAction (A * B) = (rowAction A : HilbertTuple ι E →L[𝕜] _) * rowAction B := by
  ext x i
  change rowAction (A * B) x i = rowAction A (rowAction B x) i
  simp only [rowAction_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

variable [CompleteSpace E]

omit [DecidableEq ι] in
@[simp] theorem rowAction_conjTranspose (A : Matrix ι ι 𝕜) :
    rowAction Aᴴ = (rowAction A : HilbertTuple ι E →L[𝕜] _)† := by
  ext x : 1
  apply ext_inner_left 𝕜
  intro y
  rw [adjoint_inner_right]
  simp only [PiLp.inner_apply, rowAction_apply, inner_sum, sum_inner, inner_smul_left,
    inner_smul_right, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]

theorem rowAction_posSemidef {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) (x : HilbertTuple ι E) :
    0 ≤ RCLike.re ⟪x, rowAction A x⟫_𝕜 := by
  let R := CFC.sqrt A
  have hR : Rᴴ = R := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hRA : Rᴴ * R = A := by rw [hR, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  rw [← hRA, rowAction_mul, rowAction_conjTranspose]
  change 0 ≤ RCLike.re ⟪x, ((rowAction R)†) (rowAction R x)⟫_𝕜
  rw [adjoint_inner_right, inner_self_eq_norm_sq]
  exact sq_nonneg _

/-- Sharp, dimension-free amplification bound for a scalar matrix. -/
theorem norm_rowAction_le (A : Matrix ι ι 𝕜) :
    ‖(rowAction A : HilbertTuple ι E →L[𝕜] _)‖ ≤ opNorm A := by
  have hA : Aᴴ * A ≤ opNorm A ^ 2 • (1 : Matrix ι ι 𝕜) := by
    apply matrix_le_of_qform_le (Matrix.isHermitian_conjTranspose_mul_self A)
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
    intro v
    have hp := pow_le_pow_left₀ (norm_nonneg _)
      ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A).le_opNorm (WithLp.toLp 2 v)) 2
    rw [← opNorm_square_eq, Matrix.toEuclideanCLM_toLp, mul_pow] at hp
    rw [qform_smul, qform_one]
    have hq := qform_conjTranspose_mul (1 : Matrix ι ι 𝕜) A v
    rw [Matrix.mul_one, qform_one] at hq
    exact hq.trans_le hp
  have hD := Matrix.le_iff.mp hA
  have hnorm : 0 ≤ opNorm A := norm_nonneg _
  apply (rowAction A : HilbertTuple ι E →L[𝕜] _).opNorm_le_bound hnorm
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hnorm (norm_nonneg _))).mp
  have hq := rowAction_posSemidef hD x
  rw [rowAction_sub, rowAction_real_smul, rowAction_one, rowAction_mul,
    rowAction_conjTranspose] at hq
  change 0 ≤ RCLike.re ⟪x, ((opNorm A ^ 2 : ℝ) : 𝕜) • x - ((rowAction A)†) (rowAction A x)⟫_𝕜 at hq
  rw [inner_sub_right, inner_smul_right, adjoint_inner_right, map_sub,
    RCLike.re_ofReal_mul, inner_self_eq_norm_sq,
    inner_self_eq_norm_sq] at hq
  rw [mul_pow]
  exact sub_nonneg.mp hq

/-- Apply a Hilbert operator independently in each tuple coordinate. -/
def diagonalMap (D : E →L[𝕜] E) : HilbertTuple ι E →L[𝕜] HilbertTuple ι E :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι ↦ E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : ι ↦ D ∘L PiLp.proj (𝕜 := 𝕜) 2 (fun _ : ι ↦ E) i)

omit [Fintype ι] [DecidableEq ι] [CompleteSpace E] in
@[simp] theorem diagonalMap_apply (D : E →L[𝕜] E) (x : HilbertTuple ι E) (i : ι) :
    (diagonalMap D) x i = D (x i) := rfl

omit [CompleteSpace E] [DecidableEq ι] in
theorem rowAction_commute_diagonalMap (A : Matrix ι ι 𝕜) (D : E →L[𝕜] E) :
    Commute (rowAction A : HilbertTuple ι E →L[𝕜] _) (diagonalMap D) := by
  show rowAction A * diagonalMap D = diagonalMap D * rowAction A
  ext x i
  change rowAction A (diagonalMap D x) i = diagonalMap D (rowAction A x) i
  simp [map_sum, map_smul]

omit [Fintype ι] [DecidableEq ι] [CompleteSpace E] in
@[simp] theorem diagonalMap_mul (D F : E →L[𝕜] E) :
    diagonalMap (D * F) = (diagonalMap D : HilbertTuple ι E →L[𝕜] _) * diagonalMap F := rfl

omit [DecidableEq ι] in
@[simp] theorem diagonalMap_adjoint (D : E →L[𝕜] E) :
    diagonalMap (D†) = (diagonalMap D : HilbertTuple ι E →L[𝕜] _)† := by
  ext x : 1
  apply ext_inner_left 𝕜
  intro y
  rw [adjoint_inner_right]
  simp [PiLp.inner_apply, adjoint_inner_right]

/-- A scalar matrix acts on the range of the fiber projection and the identity acts on the rest. -/
def activated (A : Matrix ι ι 𝕜) (D : E →L[𝕜] E) :
    HilbertTuple ι E →L[𝕜] HilbertTuple ι E :=
  1 + rowAction (A - 1) * diagonalMap D

omit [CompleteSpace E] in
@[simp] theorem activated_one (D : E →L[𝕜] E) :
    activated (1 : Matrix ι ι 𝕜) D = 1 := by
  have hzero : rowAction (0 : Matrix ι ι 𝕜) = (0 : HilbertTuple ι E →L[𝕜] _) := by
    ext x i
    simp
  simp [activated, hzero]

omit [CompleteSpace E] in
theorem activated_mul (A B : Matrix ι ι 𝕜) (D : E →L[𝕜] E) (hD : IsIdempotentElem D) :
    activated (A * B) D = activated A D * activated B D := by
  let d := (diagonalMap D : HilbertTuple ι E →L[𝕜] _)
  let a := (rowAction (A - 1) : HilbertTuple ι E →L[𝕜] _)
  let b := (rowAction (B - 1) : HilbertTuple ι E →L[𝕜] _)
  have hd : d * d = d := by
    change diagonalMap D * diagonalMap D = diagonalMap D
    rw [← diagonalMap_mul, hD.eq]
  have hb : d * b = b * d := (rowAction_commute_diagonalMap (B - 1) D).eq.symm
  have hprod : a * d * (b * d) = (a * b) * d := by
    calc
      _ = a * (d * b) * d := by noncomm_ring
      _ = a * (b * d) * d := by rw [hb]
      _ = (a * b) * (d * d) := by noncomm_ring
      _ = _ := by rw [hd]
  have hmat : (A - 1) + (B - 1) + (A - 1) * (B - 1) = A * B - 1 := by noncomm_ring
  unfold activated
  rw [← hmat, rowAction_add, rowAction_add, rowAction_mul]
  change 1 + (a + b + a * b) * d = (1 + a * d) * (1 + b * d)
  calc
    _ = 1 + a * d + b * d + a * d * (b * d) := by rw [hprod]; noncomm_ring
    _ = _ := by noncomm_ring

theorem activated_adjoint (A : Matrix ι ι 𝕜) (D : E →L[𝕜] E) :
    (activated A D)† = activated Aᴴ (D†) := by
  simp only [activated, ← star_eq_adjoint, star_add, star_mul, star_one]
  simp only [star_eq_adjoint, ← diagonalMap_adjoint, ← rowAction_conjTranspose,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  congr 1
  exact (rowAction_commute_diagonalMap (Aᴴ - 1) (D†)).eq.symm

/-- The activated quadratic metric is realized as this continuous linear equivalence. -/
def activatedSqrtEquiv (A : Matrix ι ι 𝕜) (hA : A.PosDef)
    (D : E →L[𝕜] E) (hD : IsIdempotentElem D) : HilbertTuple ι E ≃L[𝕜] HilbertTuple ι E :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    (f₁ := activated (CFC.sqrt A) D) (f₂ := activated (CFC.sqrt A)⁻¹ D)
    (by
      change activated (CFC.sqrt A) D * activated (CFC.sqrt A)⁻¹ D = 1
      rw [← activated_mul _ _ _ hD, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_sqrt hA).isUnit), activated_one])
    (by
      change activated (CFC.sqrt A)⁻¹ D * activated (CFC.sqrt A) D = 1
      rw [← activated_mul _ _ _ hD, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_sqrt hA).isUnit), activated_one])

omit [CompleteSpace E] in
theorem activatedSqrtEquiv_forward (A : Matrix ι ι 𝕜) (hA : A.PosDef)
    (D : E →L[𝕜] E) (hD : IsIdempotentElem D) :
    (activatedSqrtEquiv A hA D hD).toContinuousLinearMap = activated (CFC.sqrt A) D := rfl

omit [CompleteSpace E] in
theorem activatedSqrtEquiv_inverse (A : Matrix ι ι 𝕜) (hA : A.PosDef)
    (D : E →L[𝕜] E) (hD : IsIdempotentElem D) :
    (activatedSqrtEquiv A hA D hD).symm.toContinuousLinearMap = activated (CFC.sqrt A)⁻¹ D := rfl

theorem activatedSqrtEquiv_gram (A : Matrix ι ι 𝕜) (hA : A.PosDef)
    (D : E →L[𝕜] E) (hD : IsIdempotentElem D) (hDadj : D† = D) :
    let S := (activatedSqrtEquiv A hA D hD).toContinuousLinearMap
    S† * S = activated A D := by
  simp only [activatedSqrtEquiv_forward, activated_adjoint, hDadj]
  rw [(posDef_sqrt hA).isHermitian.eq, ← activated_mul _ _ _ hD, sqrt_mul_sqrt_of_posDef hA]

theorem activatedSqrtEquiv_gram_inverse (A : Matrix ι ι 𝕜) (hA : A.PosDef)
    (D : E →L[𝕜] E) (hD : IsIdempotentElem D) (hDadj : D† = D) :
    let Si := (activatedSqrtEquiv A hA D hD).symm.toContinuousLinearMap
    Si * Si† = activated A⁻¹ D := by
  simp only [activatedSqrtEquiv_inverse, activated_adjoint, hDadj]
  rw [(posDef_sqrt hA).inv.isHermitian.eq, ← activated_mul _ _ _ hD]
  congr 1
  rw [← Matrix.mul_inv_rev, sqrt_mul_sqrt_of_posDef hA]

end HilbertTuple
section Indicator

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {D : Set α} (hD : MeasurableSet D)

def lpIndicatorFun (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).indicator hD.nullMeasurableSet).toLp (D.indicator f)

private theorem ae_lpIndicatorFun (f : Lp ℂ 2 μ) :
    ⇑(lpIndicatorFun μ hD f) =ᵐ[μ] D.indicator f :=
  MemLp.coeFn_toLp _

def lpIndicatorLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := lpIndicatorFun μ hD
  map_add' f g := by
    apply Lp.ext
    filter_upwards [ae_lpIndicatorFun μ hD (f + g), ae_lpIndicatorFun μ hD f,
      ae_lpIndicatorFun μ hD g, Lp.coeFn_add f g,
      Lp.coeFn_add (lpIndicatorFun μ hD f) (lpIndicatorFun μ hD g)] with x hx hf hg hfg hsum
    change (f + g) x = f x + g x at hfg
    change (lpIndicatorFun μ hD f + lpIndicatorFun μ hD g) x =
      lpIndicatorFun μ hD f x + lpIndicatorFun μ hD g x at hsum
    rw [hx, hsum, hf, hg]
    by_cases hm : x ∈ D
    · simpa only [Set.indicator_of_mem hm] using hfg
    · simp [hm]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [ae_lpIndicatorFun μ hD (c • f), ae_lpIndicatorFun μ hD f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (lpIndicatorFun μ hD f)] with x hx hf hcf hs
    by_cases hm : x ∈ D <;> simp [hx, hf, hcf, hs, hm]

/-- Restrict an L² function to a measurable set, setting it to zero outside. -/
def lpIndicatorProjection : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lpIndicatorLinear μ hD).mkContinuous 1 fun f ↦ by
    rw [one_mul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [ae_lpIndicatorFun μ hD f] with x hx
    change ‖lpIndicatorFun μ hD f x‖ ≤ ‖f x‖
    rw [hx]
    by_cases hm : x ∈ D <;> simp [hm]

theorem ae_lpIndicatorProjection (f : Lp ℂ 2 μ) :
    ⇑(lpIndicatorProjection μ hD f) =ᵐ[μ] D.indicator f :=
  ae_lpIndicatorFun μ hD f

theorem lpIndicatorProjection_norm_le : ‖lpIndicatorProjection μ hD‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem lpIndicatorProjection_idempotent : IsIdempotentElem (lpIndicatorProjection μ hD) := by
  ext f : 1
  change lpIndicatorProjection μ hD (lpIndicatorProjection μ hD f) = lpIndicatorProjection μ hD f
  apply Lp.ext
  filter_upwards [ae_lpIndicatorProjection μ hD (lpIndicatorProjection μ hD f),
    ae_lpIndicatorProjection μ hD f] with x hx hf
  rw [hx]
  by_cases hm : x ∈ D <;> simp [hf, hm]

theorem lpIndicatorProjection_adjoint :
    (lpIndicatorProjection μ hD)† = lpIndicatorProjection μ hD := by
  ext f : 1
  apply ext_inner_left ℂ
  intro g
  rw [adjoint_inner_right, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_lpIndicatorProjection μ hD f, ae_lpIndicatorProjection μ hD g] with x hf hg
  by_cases hm : x ∈ D <;> simp [hf, hg, hm]

end Indicator

section OrthonormalSynthesis
open Submodule

variable {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Isometric finite synthesis for an orthonormal family on any finite index type. -/
def orthonormalSynthesis (v : ι → E) (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] E where
  toLinearMap := (Fintype.linearCombination 𝕜 v).comp (WithLp.linearEquiv 2 𝕜 _).toLinearMap
  norm_map' c := by
    change ‖Fintype.linearCombination 𝕜 v (WithLp.ofLp c)‖ = ‖c‖
    rw [Fintype.linearCombination_apply]
    have h := congrArg RCLike.re
      (Matrix.star_dotProduct_gram_mulVec v (WithLp.ofLp c) (WithLp.ofLp c))
    rw [Matrix.gram_eq_one_iff_orthonormal.mpr hv, ← qform, qform_one, WithLp.toLp_ofLp,
      inner_self_eq_norm_sq] at h
    exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.le).antisymm
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h.ge) |>.symm

@[simp] theorem orthonormalSynthesis_apply (v : ι → E) (hv : Orthonormal 𝕜 v)
    (c : EuclideanSpace 𝕜 ι) : orthonormalSynthesis v hv c = ∑ i, (WithLp.ofLp c) i • v i :=
  Fintype.linearCombination_apply _ _ _

theorem orthonormalSynthesis_range (v : ι → E) (hv : Orthonormal 𝕜 v) :
    Set.range (orthonormalSynthesis v hv) = (span 𝕜 (Set.range v) : Set E) := by
  rw [← Fintype.range_linearCombination]
  ext x
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨WithLp.ofLp c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨WithLp.toLp 2 c, hc⟩

@[simp] theorem orthonormalSynthesis_single (v : ι → E) (hv : Orthonormal 𝕜 v) (i : ι) :
    orthonormalSynthesis v hv (WithLp.toLp 2 (Pi.single i 1)) = v i := by
  rw [orthonormalSynthesis_apply]
  simp [Pi.single_apply, ite_smul]

end OrthonormalSynthesis

section FourierCutoff

open Submodule

variable (T : ℝ) [Fact (0 < T)]

/-- The Hilbert space on the circle with normalized Haar measure. -/
abbrev CircleL₂ := Lp ℂ 2 (@AddCircle.haarAddCircle T _)

/-- The span of circle Fourier modes with frequencies between `-N` and `N`. -/
def fourierCutoffSpan (N : ℕ) : Submodule ℂ (CircleL₂ T) :=
  span ℂ ((@fourierLp T _ 2 _) '' {k : ℤ | -(N : ℤ) ≤ k ∧ k ≤ (N : ℤ)})

instance finiteDimensional_fourierCutoffSpan (N : ℕ) :
    FiniteDimensional ℂ (fourierCutoffSpan T N) := by
  unfold fourierCutoffSpan
  exact FiniteDimensional.span_of_finite _ ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).image _)

theorem fourierCutoffSpan_mono : Monotone (fourierCutoffSpan T) := by
  intro M N h
  apply span_mono
  rintro _ ⟨k, hk, rfl⟩
  change -(M : ℤ) ≤ k ∧ k ≤ (M : ℤ) at hk
  refine ⟨k, ?_, rfl⟩
  change -(N : ℤ) ≤ k ∧ k ≤ (N : ℤ)
  omega

theorem fourierLp_mem_cutoff {k : ℤ} {N : ℕ} (hk : -(N : ℤ) ≤ k ∧ k ≤ (N : ℤ)) :
    (@fourierLp T _ 2 _ k) ∈ fourierCutoffSpan T N :=
  subset_span ⟨k, hk, rfl⟩

theorem iSup_fourierCutoffSpan :
    (⨆ N, fourierCutoffSpan T N) = span ℂ (Set.range (@fourierLp T _ 2 _)) := by
  apply le_antisymm
  · exact iSup_le fun N ↦ span_mono (Set.image_subset_range _ _)
  · refine span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact (le_iSup (fourierCutoffSpan T) k.natAbs) (fourierLp_mem_cutoff T (by omega))

theorem dense_fourierCutoffSpan : Dense {x : CircleL₂ T | ∃ N, x ∈ fourierCutoffSpan T N} := by
  have hd : Directed (· ≤ ·) (fourierCutoffSpan T) := (fourierCutoffSpan_mono T).directed_le
  have hset : {x : CircleL₂ T | ∃ N, x ∈ fourierCutoffSpan T N} =
      ↑(⨆ N, fourierCutoffSpan T N) := by
    ext x
    exact (Submodule.mem_iSup_of_directed _ hd).symm
  rw [hset, iSup_fourierCutoffSpan, Submodule.dense_iff_topologicalClosure_eq_top]
  exact span_fourierLp_closure_eq_top (by norm_num)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One Fourier character in one coordinate of the Hilbert tuple. -/
def tupleFourierChar (k : ι × ℤ) : HilbertTuple ι (CircleL₂ T) :=
  PiLp.single 2 k.1 (@fourierLp T _ 2 _ k.2)

theorem orthonormal_tupleFourierChar : Orthonormal ℂ (tupleFourierChar T (ι := ι)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, a⟩ ⟨j, b⟩
  have hFour := orthonormal_iff_ite.mp (@orthonormal_fourier T _) a b
  by_cases hij : i = j
  · subst j
    simpa [tupleFourierChar, PiLp.inner_apply, PiLp.single_apply, apply_ite] using hFour
  · simp [tupleFourierChar, PiLp.inner_apply, PiLp.single_apply, hij, Ne.symm hij, apply_ite]

omit [DecidableEq ι] in
/-- Fourier cutoffs common to all finitely many coordinates have dense union. -/
theorem dense_tuple_fourierCutoffSpan :
    Dense {x : HilbertTuple ι (CircleL₂ T) | ∃ N, ∀ i, x i ∈ fourierCutoffSpan T N} := by
  let d : Set (CircleL₂ T) := {x | ∃ N, x ∈ fourierCutoffSpan T N}
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι ↦ CircleL₂ T)
  have hd : Dense (Set.univ.pi (fun _ : ι ↦ d)) :=
    dense_pi _ (fun _ _ ↦ dense_fourierCutoffSpan T)
  refine (hd.preimage e.toHomeomorph.isOpenMap).mono fun x hx ↦ ?_
  have hx' (i : ι) : ∃ N, x i ∈ fourierCutoffSpan T N :=
    hx i (Set.mem_univ i)
  choose N hN using hx'
  refine ⟨Finset.univ.sup N, fun i ↦ ?_⟩
  exact fourierCutoffSpan_mono T (Finset.le_sup (Finset.mem_univ i)) (hN i)

/-- Finite index set of the integer frequencies in the common circle cutoff. -/
abbrev FourierCutoffIndex (N : ℕ) := {k : ℤ // k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)}

/-- Restriction of the tuple Fourier characters to a given cutoff. -/
def tupleFourierCutoffFamily (N : ℕ) (k : ι × FourierCutoffIndex N) :
    HilbertTuple ι (CircleL₂ T) :=
  tupleFourierChar T (k.1, k.2.val)

theorem orthonormal_tupleFourierCutoffFamily (N : ℕ) :
    Orthonormal ℂ (tupleFourierCutoffFamily T N (ι := ι)) := by
  refine (orthonormal_tupleFourierChar T).comp (f := fun k : ι × FourierCutoffIndex N ↦ (k.1, k.2.val)) ?_
  intro k l h
  exact Prod.ext (congrArg (fun p : ι × ℤ ↦ p.1) h) (Subtype.ext (congrArg (fun p : ι × ℤ ↦ p.2) h))

/-- The common cutoff subspace is exactly the span of the finite tuple character family. -/
theorem mem_span_tupleFourierCutoffFamily_iff (N : ℕ) (x : HilbertTuple ι (CircleL₂ T)) :
    x ∈ span ℂ (Set.range (tupleFourierCutoffFamily T N)) ↔
      ∀ i, x i ∈ fourierCutoffSpan T N := by
  let F := span ℂ (Set.range (tupleFourierCutoffFamily T N (ι := ι)))
  constructor
  · intro hx i
    have hle : F ≤ (fourierCutoffSpan T N).comap (PiLp.projₗ 2 _ (𝕜 := ℂ) i) := by
      apply span_le.mpr
      rintro _ ⟨⟨j, k⟩, rfl⟩
      change (PiLp.single (β := fun _ : ι ↦ CircleL₂ T) 2 j (@fourierLp T _ 2 _ k.val)) i ∈ fourierCutoffSpan T N
      by_cases hi : i = j
      · have hmem := fourierLp_mem_cutoff T (Finset.mem_Icc.mp k.property)
        simpa [PiLp.single_apply, hi] using hmem
      · simp [hi, zero_mem]
    exact hle hx
  · intro hx
    have hSingle (i : ι) : ∀ y, y ∈ fourierCutoffSpan T N → PiLp.single (β := fun _ : ι ↦ CircleL₂ T) 2 i y ∈ F := by
      intro y hy
      refine Submodule.span_induction (p := fun z _ ↦ PiLp.single (β := fun _ : ι ↦ CircleL₂ T) 2 i z ∈ F) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨k, hk, rfl⟩
        exact subset_span ⟨⟨i, ⟨k, Finset.mem_Icc.mpr hk⟩⟩, rfl⟩
      · have he : PiLp.single (β := fun _ : ι ↦ CircleL₂ T) 2 i (0 : CircleL₂ T) = 0 := by
          ext j
          simp [PiLp.single_apply]
        rw [he]
        exact F.zero_mem
      · intro y z _ _ hy hz
        rw [PiLp.single_add]
        exact F.add_mem hy hz
      · intro a y _ hy
        have hs : PiLp.single (β := fun _ : ι ↦ CircleL₂ T) 2 i (a • y) = a • PiLp.single (β := fun _ : ι ↦ CircleL₂ T) 2 i y := by
          ext j
          by_cases hji : j = i <;> simp [hji]
        rw [hs]
        exact F.smul_mem _ hy
    have hsum : (∑ i, PiLp.single (β := fun _ : ι ↦ CircleL₂ T) 2 i (x i)) = x := by
      ext j
      simp [WithLp.ofLp_sum, Finset.sum_apply]
    rw [← hsum]
    exact F.sum_mem fun i _ ↦ hSingle i _ (hx i)


/-- The finite isometry which synthesizes the common Fourier cutoff in every coordinate. -/
def tupleFourierCutoffIsometry (N : ℕ) :
    EuclideanSpace ℂ (ι × FourierCutoffIndex N) →ₗᵢ[ℂ] HilbertTuple ι (CircleL₂ T) :=
  orthonormalSynthesis (tupleFourierCutoffFamily T N) (orthonormal_tupleFourierCutoffFamily T N)

theorem tupleFourierCutoffIsometry_range (N : ℕ) :
    Set.range (tupleFourierCutoffIsometry T (ι := ι) N) =
      {x | ∀ i, x i ∈ fourierCutoffSpan T N} := by
  rw [tupleFourierCutoffIsometry, orthonormalSynthesis_range]
  ext x
  exact mem_span_tupleFourierCutoffFamily_iff T N x

theorem tupleFourierCutoffIsometry_nested (N M : ℕ) (hNM : N ≤ M) :
    Set.range (tupleFourierCutoffIsometry T (ι := ι) N) ⊆
      Set.range (tupleFourierCutoffIsometry T (ι := ι) M) := by
  rw [tupleFourierCutoffIsometry_range, tupleFourierCutoffIsometry_range]
  exact fun x hx i ↦ fourierCutoffSpan_mono T hNM (hx i)

theorem dense_tupleFourierCutoffIsometry :
    Dense {x | ∃ N, x ∈ Set.range (tupleFourierCutoffIsometry T (ι := ι) N)} := by
  simp only [tupleFourierCutoffIsometry_range, Set.mem_ofPred_eq]
  exact dense_tuple_fourierCutoffSpan T

theorem tupleFourierCutoffIsometry_mode (N : ℕ) (i : ι) (k : FourierCutoffIndex N) :
    tupleFourierCutoffIsometry T N (WithLp.toLp 2 (Pi.single (i, k) 1)) =
      tupleFourierChar T (i, k.val) := by
  simp [tupleFourierCutoffIsometry, tupleFourierCutoffFamily]

end FourierCutoff

/-- Integer Fourier modes in the order 0, 1, -1, …, N, -N. -/
def fourierCutoffNumbering (N : ℕ) (j : Fin (2 * N + 1)) : ℤ :=
  if j.val % 2 = 1 then (((j.val + 1) / 2 : ℕ) : ℤ) else -((j.val / 2 : ℕ) : ℤ)

@[simp] theorem fourierCutoffNumbering_zero (N : ℕ) : fourierCutoffNumbering N 0 = 0 := by
  simp [fourierCutoffNumbering]

theorem fourierCutoffNumbering_injective (N : ℕ) : Function.Injective (fourierCutoffNumbering N) := by
  intro i j hij
  apply Fin.ext
  unfold fourierCutoffNumbering at hij
  split at hij <;> split at hij <;> omega

theorem fourierCutoffNumbering_range (N : ℕ) :
    Set.range (fourierCutoffNumbering N) = Set.Icc (-(N : ℤ)) (N : ℤ) := by
  ext k
  constructor
  · rintro ⟨j, rfl⟩
    have hj := j.isLt
    constructor <;> unfold fourierCutoffNumbering <;> split <;> omega
  · rintro ⟨hlo, hhi⟩
    by_cases hp : 0 < k
    · let j : Fin (2 * N + 1) := ⟨2 * k.toNat - 1, by omega⟩
      use j
      unfold fourierCutoffNumbering
      change (if (2 * k.toNat - 1) % 2 = 1 then
        ((((2 * k.toNat - 1) + 1) / 2 : ℕ) : ℤ) else -(((2 * k.toNat - 1) / 2 : ℕ) : ℤ)) = k
      rw [ite_eq_left (by omega)]
      omega
    · let j : Fin (2 * N + 1) := ⟨2 * (-k).toNat, by omega⟩
      use j
      unfold fourierCutoffNumbering
      change (if (2 * (-k).toNat) % 2 = 1 then
        (((2 * (-k).toNat + 1) / 2 : ℕ) : ℤ) else -(((2 * (-k).toNat) / 2 : ℕ) : ℤ)) = k
      rw [ite_eq_right (by omega)]
      omega

namespace HilbertTuple
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {n : ℕ}

/-- Keep all earlier rows, apply the fiber projection to the current row, and discard later rows. -/
def rowCut (j : Fin n) (Proj : E →L[𝕜] E) : HilbertTuple (Fin n) E →L[𝕜] HilbertTuple (Fin n) E :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin n ↦ E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : Fin n ↦
      if i < j then PiLp.proj (𝕜 := 𝕜) 2 (β := fun _ : Fin n ↦ E) i
      else if i = j then Proj ∘L PiLp.proj (𝕜 := 𝕜) 2 (β := fun _ : Fin n ↦ E) i
      else 0)

@[simp] theorem rowCut_apply (j : Fin n) (Proj : E →L[𝕜] E) (x : HilbertTuple (Fin n) E) (i : Fin n) :
    rowCut j Proj x i = if i < j then x i else if i = j then Proj (x i) else 0 := by
  change (if i < j then PiLp.proj (𝕜 := 𝕜) 2 (β := fun _ : Fin n ↦ E) i
    else if i = j then Proj ∘L PiLp.proj (𝕜 := 𝕜) 2 (β := fun _ : Fin n ↦ E) i
    else 0) x = _
  by_cases hlt : i < j <;> by_cases heq : i = j <;> simp [hlt, heq]

section Plane

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {n : ℕ}

/-- Tuple obtained from two coefficient columns in two fixed fiber directions. -/
def ofPlane (u v : E) (a b : Fin n → 𝕜) : HilbertTuple (Fin n) E :=
  WithLp.toLp 2 (fun i ↦ a i • u + b i • v)

@[simp] theorem ofPlane_apply (u v : E) (a b : Fin n → 𝕜) (i : Fin n) :
    ofPlane u v a b i = a i • u + b i • v := rfl

theorem norm_sq_ofPlane (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_𝕜 = 0)
    (a b : Fin n → 𝕜) :
    ‖ofPlane u v a b‖ ^ 2 = ‖WithLp.toLp 2 a‖ ^ 2 + ‖WithLp.toLp 2 b‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, ofPlane_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : ⟪a i • u, b i • v⟫_𝕜 = 0 := by simp [inner_smul_left, inner_smul_right, huv]
  rw [norm_add_sq (𝕜 := 𝕜), h, map_zero, mul_zero, add_zero]
  simp [norm_smul, hu, hv]

@[simp] theorem rowAction_ofPlane (A : Matrix (Fin n) (Fin n) 𝕜)
    (u v : E) (a b : Fin n → 𝕜) :
    rowAction A (ofPlane u v a b) = ofPlane u v (A *ᵥ a) (A *ᵥ b) := by
  ext i
  simp only [rowAction_apply, ofPlane_apply, smul_add, smul_smul, Finset.sum_add_distrib]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]

theorem activated_ofPlane (A : Matrix (Fin n) (Fin n) 𝕜) (D : E →L[𝕜] E)
    (u v : E) (hu : D u = u) (hv : D v = 0) (a b : Fin n → 𝕜) :
    activated A D (ofPlane u v a b) = ofPlane u v (A *ᵥ a) b := by
  have hdiag : diagonalMap D (ofPlane u v a b) = ofPlane u v a (0 : Fin n → 𝕜) := by
    ext i
    simp [map_add, map_smul, hu, hv]
  change ofPlane u v a b + rowAction (A - 1) (diagonalMap D (ofPlane u v a b)) = _
  rw [hdiag, rowAction_ofPlane, Matrix.mulVec_zero]
  ext i
  simp only [PiLp.add_apply, ofPlane_apply, Pi.zero_apply, zero_smul, add_zero,
    Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_smul]
  abel

theorem rowCut_ofPlane (j : Fin n) (P : E →L[𝕜] E)
    (u v : E) (a b : Fin n → 𝕜) {t s : ℝ}
    (hu : P u = (t : 𝕜) • u + (s : 𝕜) • v)
    (hv : P v = (s : 𝕜) • u + ((1 - t : ℝ) : 𝕜) • v) :
    rowCut j P (ofPlane u v a b) =
      ofPlane u v
        (truncCoeff j.val a + Pi.single j ((t : 𝕜) * a j + (s : 𝕜) * b j))
        (truncCoeff j.val b + Pi.single j ((s : 𝕜) * a j + ((1 - t : ℝ) : 𝕜) * b j)) := by
  ext i
  rw [rowCut_apply, ofPlane_apply]
  by_cases hij : i < j
  · have hne : i ≠ j := ne_of_lt hij
    simp [ofPlane_apply, hij, truncCoeff, hne]
  · by_cases heq : i = j
    · subst i
      rw [ite_eq_right (lt_irrefl j), ite_eq_left rfl]
      simp only [map_add, map_smul, hu, hv, smul_add, smul_smul, ofPlane_apply, Pi.add_apply,
        truncCoeff, lt_irrefl, ite_false, Pi.single_eq_same, zero_add, add_smul]
      simp only [mul_comm (a j), mul_comm (b j)]
      abel
    · simp [ofPlane_apply, hij, heq, truncCoeff]

end Plane

end HilbertTuple
end SchauderBasisOrbits
