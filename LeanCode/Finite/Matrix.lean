import Mathlib

/-! Euclidean matrix norms and quadratic forms for the finite Gram estimates. -/

open Matrix Filter
open scoped BigOperators ComplexOrder InnerProductSpace InnerProduct MatrixOrder Matrix.Norms.L2Operator Topology Kronecker

noncomputable section

namespace SchauderBasisOrbits

variable {𝕜 ι κ : Type*} [RCLike 𝕜]
variable [Fintype ι]
variable [DecidableEq ι] in

/-- The operator norm of a matrix acting between Euclidean coefficient spaces. -/
def opNorm [Fintype κ] (A : Matrix κ ι 𝕜) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

variable [DecidableEq ι] in
theorem opNorm_square_eq (A : Matrix ι ι 𝕜) : opNorm A = ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A‖ := rfl

/-- Real quadratic value of a matrix at a coefficient vector. -/
def qform (A : Matrix ι ι 𝕜) (c : ι → 𝕜) : ℝ :=
  RCLike.re (star c ⬝ᵥ (A *ᵥ c))

@[simp] theorem qform_zero (x : ι → 𝕜) : qform (0 : Matrix ι ι 𝕜) x = 0 := by
  simp [qform]

@[simp] theorem qform_add (A B : Matrix ι ι 𝕜) (x : ι → 𝕜) :
    qform (A + B) x = qform A x + qform B x := by
  simp [qform, Matrix.add_mulVec, dotProduct_add]

@[simp] theorem qform_sub (A B : Matrix ι ι 𝕜) (x : ι → 𝕜) :
    qform (A - B) x = qform A x - qform B x := by
  simp [qform, Matrix.sub_mulVec, dotProduct_sub]

@[simp] theorem qform_smul (a : ℝ) (A : Matrix ι ι 𝕜) (x : ι → 𝕜) :
    qform (a • A) x = a * qform A x := by
  simp [qform, Matrix.smul_mulVec, dotProduct_smul, RCLike.real_smul_eq_coe_mul]

theorem qform_nonneg {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) (x : ι → 𝕜) :
    0 ≤ qform A x :=
  (RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

theorem qform_pos {A : Matrix ι ι 𝕜} (hA : A.PosDef) {x : ι → 𝕜} (hx : x ≠ 0) :
    0 < qform A x := by
  exact hA.re_dotProduct_pos hx

theorem posSemidef_of_qform_nonneg {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (h : ∀ x, 0 ≤ qform A x) : A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x ↦ RCLike.nonneg_iff.mpr ?_
  exact ⟨h x, hA.im_star_dotProduct_mulVec_self x⟩

theorem posDef_of_qform_pos {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (h : ∀ x ≠ 0, 0 < qform A x) : A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA fun x hx ↦ ?_
  exact RCLike.pos_iff.mpr ⟨by simpa [qform] using h x hx, by simp [hA.im_star_dotProduct_mulVec_self]⟩

theorem qform_mono {A B : Matrix ι ι 𝕜} (h : A ≤ B) (x : ι → 𝕜) :
    qform A x ≤ qform B x := by
  have hq := qform_nonneg (Matrix.le_iff.mp h) x
  simpa using hq

theorem matrix_le_of_qform_le {A B : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, qform A x ≤ qform B x) : A ≤ B := by
  refine Matrix.le_iff.mpr (posSemidef_of_qform_nonneg (hB.sub hA) fun x ↦ ?_)
  simpa using h x

variable [DecidableEq ι]

theorem qform_eq_re_inner (A : Matrix ι ι 𝕜) (x : ι → 𝕜) :
    qform A x = RCLike.re ⟪WithLp.toLp 2 x, Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A (WithLp.toLp 2 x)⟫_𝕜 := by
  rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

@[simp] theorem qform_one (x : ι → 𝕜) :
    qform (1 : Matrix ι ι 𝕜) x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  simp [qform_eq_re_inner]

theorem abs_qform_le (A : Matrix ι ι 𝕜) (x : ι → 𝕜) :
    |qform A x| ≤ opNorm A * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [qform_eq_re_inner, opNorm_square_eq]
  calc
    _ ≤ ‖⟪WithLp.toLp 2 x, Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A (WithLp.toLp 2 x)⟫_𝕜‖ :=
      RCLike.abs_re_le_norm _
    _ ≤ ‖WithLp.toLp 2 x‖ * ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A (WithLp.toLp 2 x)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 x‖ * (‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A‖ * ‖WithLp.toLp 2 x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by ring

theorem posDef_sqrt {A : Matrix ι ι 𝕜} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  exact (CFC.sqrt_nonneg A).posSemidef.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit)

theorem sqrt_mul_sqrt_of_posDef {A : Matrix ι ι 𝕜} (hA : A.PosDef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

theorem exists_pos_smul_one_le [Nonempty ι] {A : Matrix ι ι 𝕜} (hA : A.PosDef) :
    ∃ a : ℝ, 0 < a ∧ a • (1 : Matrix ι ι 𝕜) ≤ A := by
  obtain ⟨a, ha, hle⟩ :=
    (CFC.exists_pos_algebraMap_le_iff A hA.isHermitian).mpr (fun _ hx ↦ hA.isStrictlyPositive.spectrum_pos hx)
  exact ⟨a, ha, by simpa only [Algebra.algebraMap_eq_smul_one] using hle⟩


omit [DecidableEq ι] in
/-- The Gram quadratic form under a coefficient map. -/
theorem qform_conjTranspose_mul {κ : Type*} [Fintype κ]
    (A : Matrix ι ι 𝕜) (E : Matrix ι κ 𝕜) (x : κ → 𝕜) :
    qform (Eᴴ * A * E) x = qform A (E *ᵥ x) := by
  simp only [qform, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) Eᴴ,
    star_mulVec]

/-- Identity that witnesses the optimizer of the inverse quadratic form. -/
theorem qform_inv_variational {A : Matrix ι ι 𝕜} (hA : A.PosDef) (v c : ι → 𝕜) :
    qform A⁻¹ v - (2 * RCLike.re (star v ⬝ᵥ c) - qform A c) =
      qform A (c - A⁻¹ *ᵥ v) := by
  have hAv : A *ᵥ (A⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
      Matrix.one_mulVec]
  have hc := congrArg RCLike.re (hA.isHermitian.star_dotProduct_mulVec_comm (A⁻¹ *ᵥ v) c)
  simp only [RCLike.star_def, RCLike.conj_re, hAv] at hc
  have hre (x y : ι → 𝕜) : RCLike.re (star x ⬝ᵥ y) = RCLike.re (star y ⬝ᵥ x) := by
    calc
      RCLike.re (star x ⬝ᵥ y) = RCLike.re (star (star x ⬝ᵥ y)) := by
        simp only [RCLike.star_def, RCLike.conj_re]
      _ = RCLike.re (star y ⬝ᵥ x) := by
        rw [star_dotProduct]
        simp only [star_star, dotProduct_comm]
  simp only [qform, Matrix.mulVec_sub, hAv, star_sub, dotProduct_sub, sub_dotProduct, map_sub]
  rw [hc, hre c v, hre (A⁻¹ *ᵥ v) v]
  ring

theorem qform_inv_ge {A : Matrix ι ι 𝕜} (hA : A.PosDef) (v c : ι → 𝕜) :
    2 * RCLike.re (star v ⬝ᵥ c) - qform A c ≤ qform A⁻¹ v := by
  have h := qform_nonneg hA.posSemidef (c - A⁻¹ *ᵥ v)
  rwa [← qform_inv_variational hA, sub_nonneg] at h

theorem qform_inv_eq_optimum {A : Matrix ι ι 𝕜} (hA : A.PosDef) (v : ι → 𝕜) :
    2 * RCLike.re (star v ⬝ᵥ (A⁻¹ *ᵥ v)) - qform A (A⁻¹ *ᵥ v) = qform A⁻¹ v := by
  have h := qform_inv_variational hA v (A⁻¹ *ᵥ v)
  have hz : qform A ((A⁻¹ *ᵥ v) - (A⁻¹ *ᵥ v)) = 0 := by simp [qform]
  rw [hz, sub_eq_zero] at h
  exact h.symm

theorem matrix_inv_le_inv {A B : Matrix ι ι 𝕜} (hA : A.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB : B.PosDef := posDef_of_qform_pos (sub_add_cancel B A ▸ (Matrix.le_iff.mp hAB).isHermitian.add hA.isHermitian) fun x hx ↦ (qform_pos hA hx).trans_le (qform_mono hAB x)
  refine matrix_le_of_qform_le hB.inv.isHermitian hA.inv.isHermitian fun v ↦ ?_
  let c := B⁻¹ *ᵥ v
  calc
    qform B⁻¹ v = 2 * RCLike.re (star v ⬝ᵥ c) - qform B c :=
      (qform_inv_eq_optimum hB v).symm
    _ ≤ 2 * RCLike.re (star v ⬝ᵥ c) - qform A c :=
      sub_le_sub_left (qform_mono hAB c) _
    _ ≤ qform A⁻¹ v := qform_inv_ge hA v c

theorem matrix_inv_compression {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι 𝕜} (hA : A.PosDef) (E : Matrix ι κ 𝕜)
    (hE : Eᴴ * E = 1) (hC : (Eᴴ * A * E).PosDef) :
    (Eᴴ * A * E)⁻¹ ≤ Eᴴ * A⁻¹ * E := by
  refine matrix_le_of_qform_le hC.inv.isHermitian
    (Matrix.isHermitian_conjTranspose_mul_mul E hA.inv.isHermitian) fun v ↦ ?_
  let c := (Eᴴ * A * E)⁻¹ *ᵥ v
  rw [← qform_inv_eq_optimum hC, qform_conjTranspose_mul, qform_conjTranspose_mul]
  -- Apply the ambient variational bound at the image of the compressed optimizer.
  have hb := qform_inv_ge hA (E *ᵥ v) (E *ᵥ c)
  have hp : star (E *ᵥ v) ⬝ᵥ (E *ᵥ c) = star v ⬝ᵥ c := by
    rw [star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]
  simpa only [hp, c] using hb


/-- Entrywise complexification of a real matrix. -/
def complexify {ι κ : Type*} (A : Matrix κ ι ℝ) : Matrix κ ι ℂ :=
  A.map Complex.ofReal

@[simp] theorem complexify_apply {ι κ : Type*} (A : Matrix κ ι ℝ) (i : κ) (j : ι) :
    complexify A i j = (A i j : ℂ) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem complexify_isHermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (complexify A).IsHermitian := by
  exact hA.map _ fun x ↦ by simp

omit [DecidableEq ι] in
/-- The real and imaginary coefficients contribute independently to a real Gram form. -/
theorem qform_complexify (A : Matrix ι ι ℝ) (x : ι → ℂ) :
    qform (complexify A) x =
      qform A (fun i ↦ (x i).re) + qform A (fun i ↦ (x i).im) := by
  simp only [qform, RCLike.re_to_real]
  change (star x ⬝ᵥ (complexify A *ᵥ x)).re = _
  have hsum (f : ι → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reLm f Finset.univ
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hsum,
    Pi.star_apply, Complex.star_def, complexify_apply, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
    Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add, star_trivial,
    Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem posSemidef_complexify {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (complexify A).PosSemidef := by
  refine posSemidef_of_qform_nonneg (complexify_isHermitian hA.isHermitian) fun x ↦ ?_
  rw [qform_complexify]
  exact add_nonneg (qform_nonneg hA _) (qform_nonneg hA _)

omit [DecidableEq ι] in
theorem posDef_complexify {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (complexify A).PosDef := by
  refine posDef_of_qform_pos (complexify_isHermitian hA.isHermitian) fun x hx ↦ ?_
  rw [qform_complexify]
  by_cases hre : (fun i ↦ (x i).re) = 0
  · have him : (fun i ↦ (x i).im) ≠ 0 := by
      intro him
      apply hx
      funext i
      exact Complex.ext (congrFun hre i) (congrFun him i)
    exact add_pos_of_nonneg_of_pos (qform_nonneg hA.posSemidef _) (qform_pos hA him)
  · exact add_pos_of_pos_of_nonneg (qform_pos hA hre) (qform_nonneg hA.posSemidef _)

section Convergence

variable {γ : Type*}

omit [Fintype ι] [DecidableEq ι] in
theorem matrix_tendsto_of_entries {f : γ → Matrix ι ι 𝕜} {l : Filter γ} {A : Matrix ι ι 𝕜}
    (h : ∀ i j, Tendsto (fun x ↦ f x i j) l (𝓝 (A i j))) : Tendsto f l (𝓝 A) := by
  exact tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr (h i)

theorem opNorm_sub_tendsto_zero {f : γ → Matrix ι ι 𝕜} {l : Filter γ} {A : Matrix ι ι 𝕜}
    (h : Tendsto f l (𝓝 A)) :
    Tendsto (fun x ↦ opNorm (f x - A)) l (𝓝 0) := by
  let equiv := (Matrix.toEuclideanLin (𝕜 := 𝕜) (m := ι) (n := ι)).trans
    LinearMap.toContinuousLinearMap
  have hcont : Continuous equiv := equiv.toContinuousLinearEquiv.continuous
  have ht := (hcont.continuousAt.tendsto.comp (h.sub (tendsto_const_nhds (x := A)))).norm
  simpa only [Function.comp_apply, equiv, LinearEquiv.trans_apply, opNorm, sub_self, map_zero, norm_zero] using ht

theorem matrix_inv_tendsto_of_posDef {f : γ → Matrix ι ι 𝕜} {l : Filter γ}
    {A : Matrix ι ι 𝕜} (hA : A.PosDef) (h : Tendsto f l (𝓝 A)) :
    Tendsto (fun x ↦ (f x)⁻¹) l (𝓝 A⁻¹) := by
  have hu := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  refine (continuousAt_matrix_inv A ?_).tendsto.comp h
  simp_rw [show (Ring.inverse : 𝕜 → 𝕜) = Inv.inv from funext Ring.inverse_eq_inv]
  exact continuousAt_inv₀ hu.ne_zero

theorem relative_order_of_opNorm_sub_le {A B : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a η : ℝ}
    (ha : a • (1 : Matrix ι ι 𝕜) ≤ A) (hη : 0 ≤ η)
    (hBA : opNorm (B - A) ≤ η * a) :
    (1 - η) • A ≤ B ∧ B ≤ (1 + η) • A := by
  have hq (x : ι → 𝕜) : |qform B x - qform A x| ≤ η * qform A x := calc
    _ ≤ opNorm (B - A) * ‖WithLp.toLp 2 x‖ ^ 2 := by simpa using abs_qform_le (B - A) x
    _ ≤ (η * a) * ‖WithLp.toLp 2 x‖ ^ 2 := mul_le_mul_of_nonneg_right hBA (sq_nonneg _)
    _ = η * qform (a • (1 : Matrix ι ι 𝕜)) x := by simp only [qform_smul, qform_one]; ring
    _ ≤ η * qform A x := mul_le_mul_of_nonneg_left (qform_mono ha x) hη
  constructor
  · refine matrix_le_of_qform_le (hA.smul (IsSelfAdjoint.all _)) hB fun x ↦ ?_
    rw [qform_smul]
    have hleft := (abs_le.mp (hq x)).1
    linarith only [hleft]
  · refine matrix_le_of_qform_le hB (hA.smul (IsSelfAdjoint.all _)) fun x ↦ ?_
    rw [qform_smul]
    have hright := (abs_le.mp (hq x)).2
    linarith only [hright]

theorem eventually_posDef_relative [Nonempty ι] {f : γ → Matrix ι ι 𝕜} {l : Filter γ}
    {A : Matrix ι ι 𝕜} (hA : A.PosDef) {η : ℝ} (hη : 0 < η) (hη' : η < 1)
    (hh : ∀ᶠ x in l, (f x).IsHermitian) (h : Tendsto f l (𝓝 A)) :
    ∀ᶠ x in l, (f x).PosDef ∧ (1 - η) • A ≤ f x ∧ f x ≤ (1 + η) • A := by
  obtain ⟨a, ha, ha'⟩ := exists_pos_smul_one_le hA
  have hlt := (opNorm_sub_tendsto_zero h).eventually_lt_const (mul_pos hη ha)
  filter_upwards [hh, hlt] with x hx hδ
  have hcomp := relative_order_of_opNorm_sub_le hA.isHermitian hx ha' hη.le hδ.le
  exact ⟨posDef_of_qform_pos hx (fun c hc ↦ by
    have hlo := qform_mono hcomp.1 c
    rw [qform_smul] at hlo
    exact (mul_pos (sub_pos.mpr hη') (qform_pos hA hc)).trans_le hlo), hcomp⟩

end Convergence

section Hilbert

open ContinuousLinearMap

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

theorem norm_adjoint_comp (A : H →L[𝕜] K) :
    ‖A† ∘L A‖ = ‖A‖ ^ 2 := by
  rw [ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

theorem norm_comp_adjoint (A : H →L[𝕜] K) :
    ‖A ∘L A†‖ = ‖A‖ ^ 2 := by
  simpa only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] using
    norm_adjoint_comp (A†)

theorem norm_comp_adjoint_eq_norm_adjoint_comp (A : H →L[𝕜] K) :
    ‖A ∘L A†‖ = ‖A† ∘L A‖ := by
  rw [norm_comp_adjoint, norm_adjoint_comp]

omit [CompleteSpace H] in
theorem rankOne_self_quadratic_nonneg (v x : H) :
    0 ≤ RCLike.re ⟪x, InnerProductSpace.rankOne 𝕜 v v x⟫_𝕜 := by
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm,
    mul_comm, RCLike.mul_conj]
  simp

omit [CompleteSpace H] in
theorem rankOne_unit_eq_starProjection (v : H) (hv : ‖v‖ = 1) :
    InnerProductSpace.rankOne 𝕜 v v = (𝕜 ∙ v).starProjection := by
  ext x
  rw [InnerProductSpace.rankOne_apply, Submodule.starProjection_unit_singleton 𝕜 hv x]

end Hilbert

section Gram

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Gram matrix of a synthesis map, using its Euclidean coefficient space. -/
def clmGram (X : EuclideanSpace 𝕜 ι →L[𝕜] H) : Matrix ι ι 𝕜 :=
  (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)).symm (X† ∘L X)

@[simp] theorem toEuclideanCLM_clmGram (X : EuclideanSpace 𝕜 ι →L[𝕜] H) :
    Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (clmGram X) = X† ∘L X := by
  unfold clmGram
  exact StarAlgEquiv.apply_symm_apply _ _

theorem clmGram_isHermitian (X : EuclideanSpace 𝕜 ι →L[𝕜] H) :
    (clmGram X).IsHermitian := by
  change star (clmGram X) = clmGram X
  let e := Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)
  have hs : star (X† ∘L X) = X† ∘L X := by
    rw [star_eq_adjoint, adjoint_comp, adjoint_adjoint]
  change star (e.symm (X† ∘L X)) = e.symm (X† ∘L X)
  exact (map_star e.symm (X† ∘L X)).symm.trans (congrArg e.symm hs)

theorem qform_clmGram (X : EuclideanSpace 𝕜 ι →L[𝕜] H) (v : ι → 𝕜) :
    qform (clmGram X) v = ‖X (WithLp.toLp 2 v)‖ ^ 2 := by
  rw [qform_eq_re_inner, toEuclideanCLM_clmGram]
  change RCLike.re ⟪WithLp.toLp 2 v, (X†) (X (WithLp.toLp 2 v))⟫_𝕜 = _
  rw [adjoint_inner_right, inner_self_eq_norm_sq]

theorem clmGram_posDef (X : EuclideanSpace 𝕜 ι →L[𝕜] H) (hX : Function.Injective X) :
    (clmGram X).PosDef := by
  refine posDef_of_qform_pos (clmGram_isHermitian X) fun c hc ↦ ?_
  rw [qform_clmGram]
  apply pow_pos
  rw [norm_pos_iff]
  intro hz
  have hzero := hX (hz.trans X.map_zero.symm)
  have hc' := congrArg WithLp.ofLp hzero
  exact hc hc'

theorem clmGram_inv_apply_cancel (X : EuclideanSpace 𝕜 ι →L[𝕜] H)
    (hX : Function.Injective X) (c : EuclideanSpace 𝕜 ι) :
    (X†) (X (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (clmGram X)⁻¹ c)) = c := by
  have hunit := (Matrix.isUnit_iff_isUnit_det (clmGram X)).mp (clmGram_posDef X hX).isUnit
  have heq := congrArg (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (Matrix.mul_nonsing_inv _ hunit)
  rw [map_mul, toEuclideanCLM_clmGram, map_one] at heq
  exact DFunLike.congr_fun heq c

theorem starProjection_range_eq_gram (X : EuclideanSpace 𝕜 ι →L[𝕜] H)
    (hX : Function.Injective X) (y : H) :
    haveI : FiniteDimensional 𝕜 (LinearMap.range X.toLinearMap) :=
      Module.Finite.range X.toLinearMap
    (LinearMap.range X.toLinearMap).starProjection y =
      X (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (clmGram X)⁻¹ ((X†) y)) := by
  let _ : FiniteDimensional 𝕜 (LinearMap.range X.toLinearMap) := Module.Finite.range X.toLinearMap
  let p := Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (clmGram X)⁻¹ ((X†) y)
  have hmem : X p ∈ LinearMap.range X.toLinearMap := ⟨p, rfl⟩
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem ?_
  intro w hw
  obtain ⟨c, rfl⟩ := hw
  change ⟪y - X (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) (clmGram X)⁻¹ ((X†) y)), X c⟫_𝕜 = 0
  rw [inner_sub_left, ← adjoint_inner_left, ← adjoint_inner_left, clmGram_inv_apply_cancel X hX,
    sub_self]

theorem norm_starProjection_range_sq (X : EuclideanSpace 𝕜 ι →L[𝕜] H)
    (hX : Function.Injective X) (y : H) :
    haveI : FiniteDimensional 𝕜 (LinearMap.range X.toLinearMap) :=
      Module.Finite.range X.toLinearMap
    ‖(LinearMap.range X.toLinearMap).starProjection y‖ ^ 2 =
      qform (clmGram X)⁻¹ (WithLp.ofLp ((X†) y)) := by
  let _ : FiniteDimensional 𝕜 (LinearMap.range X.toLinearMap) := Module.Finite.range X.toLinearMap
  calc
    _ = ‖(LinearMap.range X.toLinearMap).orthogonalProjectionOnto y‖ ^ 2 := rfl
    _ = RCLike.re ⟪(LinearMap.range X.toLinearMap).starProjection y, y⟫_𝕜 :=
      (Submodule.re_inner_starProjection_eq_normSq _ _).symm
    _ = _ := by
      rw [Submodule.inner_starProjection_left_eq_right, starProjection_range_eq_gram X hX,
        ← adjoint_inner_left, qform_eq_re_inner, WithLp.toLp_ofLp]

theorem dist_sq_gram (X : EuclideanSpace 𝕜 ι →L[𝕜] H) (hX : Function.Injective X) (y : H) :
    haveI : FiniteDimensional 𝕜 (LinearMap.range X.toLinearMap) :=
      Module.Finite.range X.toLinearMap
    ‖y - (LinearMap.range X.toLinearMap).starProjection y‖ ^ 2 =
      ‖y‖ ^ 2 - qform (clmGram X)⁻¹ (WithLp.ofLp ((X†) y)) := by
  let _ : FiniteDimensional 𝕜 (LinearMap.range X.toLinearMap) := Module.Finite.range X.toLinearMap
  let S := LinearMap.range X.toLinearMap
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection y S
  rw [← norm_starProjection_range_sq X hX]
  change ‖y - S.starProjection y‖ ^ 2 = ‖y‖ ^ 2 - ‖S.starProjection y‖ ^ 2
  rw [← Submodule.starProjection_orthogonal_val]
  linarith only [h]

/-- Inverse compression for an invertible map on a potentially infinite Hilbert space. -/
theorem clmGram_inv_compression (S : H ≃L[𝕜] H) (U : EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] H) :
    (clmGram (S.toContinuousLinearMap ∘L U.toContinuousLinearMap))⁻¹ ≤
      clmGram (S.symm.toContinuousLinearMap† ∘L U.toContinuousLinearMap) := by
  let C := clmGram (S.toContinuousLinearMap ∘L U.toContinuousLinearMap)
  have hC : C.PosDef := clmGram_posDef _ (S.injective.comp U.injective)
  refine matrix_le_of_qform_le hC.inv.isHermitian (clmGram_isHermitian _) fun v ↦ ?_
  let c := C⁻¹ *ᵥ v
  let v₀ := WithLp.toLp 2 v
  let c₀ := WithLp.toLp 2 c
  rw [← qform_inv_eq_optimum hC, qform_clmGram, qform_clmGram]
  have hc : star v ⬝ᵥ c = ⟪U v₀, U c₀⟫_𝕜 := by
    rw [LinearIsometry.inner_map_map, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  change 2 * RCLike.re (star v ⬝ᵥ c) - ‖S (U c₀)‖ ^ 2 ≤
    ‖(S.symm.toContinuousLinearMap†) (U v₀)‖ ^ 2
  have hx := sq_nonneg ‖(S.symm.toContinuousLinearMap†) (U v₀) - S (U c₀)‖
  rw [norm_sub_sq (𝕜 := 𝕜), adjoint_inner_left] at hx
  have hl : S.symm.toContinuousLinearMap (S (U c₀)) = U c₀ := S.symm_apply_apply _
  rw [hl] at hx
  rw [hc]
  linarith only [hx]

end Gram

theorem qform_conjTranspose_mul_self (A : Matrix ι ι 𝕜) (x : ι → 𝕜) :
    qform (Aᴴ * A) x = ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := by
  simpa only [mul_one, qform_one] using qform_conjTranspose_mul (1 : Matrix ι ι 𝕜) A x

theorem opNorm_le_iff_conjTranspose_mul_self_le (A : Matrix ι ι 𝕜) {r : ℝ} (hr : 0 ≤ r) :
    opNorm A ≤ r ↔ Aᴴ * A ≤ r ^ 2 • (1 : Matrix ι ι 𝕜) := by
  rw [opNorm_square_eq]
  constructor
  · intro h
    apply matrix_le_of_qform_le (Matrix.isHermitian_conjTranspose_mul_self _)
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
    intro x
    rw [qform_conjTranspose_mul_self, qform_smul, qform_one, ← mul_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [← Matrix.toEuclideanCLM_toLp]
    exact ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  · intro h
    apply (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A).opNorm_le_bound hr
    intro x
    obtain ⟨x, rfl⟩ := WithLp.toLp_surjective 2 x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp
    have hq := qform_mono h x
    rw [qform_conjTranspose_mul_self, qform_smul, qform_one, ← mul_pow] at hq
    simpa only [Matrix.toEuclideanCLM_toLp] using hq

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem complexify_zero : complexify (0 : Matrix ι ι ℝ) = 0 := by
  ext i j
  simp

omit [Fintype ι] in
@[simp] theorem complexify_one : complexify (1 : Matrix ι ι ℝ) = 1 := by
  ext i j
  simp [Matrix.one_apply, apply_ite]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem complexify_sub (A B : Matrix ι ι ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j
  simp

@[simp] theorem complexify_mul (A B : Matrix ι ι ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  exact map_mul (Complex.ofRealHom.mapMatrix) A B

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem complexify_smul (a : ℝ) (A : Matrix ι ι ℝ) :
    complexify (a • A) = a • complexify A := by
  ext i j
  simp [RCLike.real_smul_eq_coe_mul, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem complexify_conjTranspose (A : Matrix ι ι ℝ) :
    complexify Aᴴ = (complexify A)ᴴ := by
  ext i j
  simp

omit [DecidableEq ι] in
theorem complexify_posSemidef_iff {A : Matrix ι ι ℝ} :
    (complexify A).PosSemidef ↔ A.PosSemidef := by
  refine ⟨fun h ↦ ?_, posSemidef_complexify⟩
  have hA : A.IsHermitian := by
    have hEq := h.isHermitian.eq
    rw [← complexify_conjTranspose] at hEq
    ext i j
    exact Complex.ofReal_injective (by simpa only [complexify_apply] using congrFun₂ hEq i j)
  refine posSemidef_of_qform_nonneg hA fun x ↦ ?_
  have hq := qform_nonneg h (fun i ↦ (x i : ℂ))
  rw [qform_complexify] at hq
  simpa [qform] using hq

omit [DecidableEq ι] in
theorem complexify_le_iff {A B : Matrix ι ι ℝ} :
    complexify A ≤ complexify B ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← complexify_sub, complexify_posSemidef_iff]

/-- Real and complex operator norms of a real coefficient matrix agree. -/
theorem opNorm_complexify (A : Matrix ι ι ℝ) : opNorm (complexify A) = opNorm A := by
  have hu (r : ℝ) (hr : 0 ≤ r) : opNorm (complexify A) ≤ r ↔ opNorm A ≤ r := by
    rw [opNorm_le_iff_conjTranspose_mul_self_le _ hr,
      opNorm_le_iff_conjTranspose_mul_self_le _ hr]
    simpa only [complexify_mul, complexify_conjTranspose, complexify_smul, complexify_one] using
      (complexify_le_iff (A := Aᴴ * A) (B := r ^ 2 • 1))
  exact le_antisymm ((hu _ (norm_nonneg _)).mpr le_rfl) ((hu _ (norm_nonneg _)).mp le_rfl)

section Exhaustion

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Inverse Gram values along nested finite-dimensional isometric inclusions.
The distinguished vector has specified coordinates in every inclusion. -/
theorem inverse_gram_exhaustion (S : H ≃L[𝕜] H) (d : ℕ → Type*)
    [∀ N, Fintype (d N)] [∀ N, DecidableEq (d N)]
    (U : ∀ N, EuclideanSpace 𝕜 (d N) →ₗᵢ[𝕜] H)
    (hnest : ∀ N M, N ≤ M → Set.range (U N) ⊆ Set.range (U M))
    (hdense : Dense {x : H | ∃ N, x ∈ Set.range (U N)})
    (e : H) (v : ∀ N, d N → 𝕜) (he : ∀ N, U N (WithLp.toLp 2 (v N)) = e) :
    let a := fun N ↦ qform (clmGram (S.toContinuousLinearMap ∘L (U N).toContinuousLinearMap))⁻¹ (v N)
    Monotone a ∧ Tendsto a atTop (𝓝 (‖(S.symm.toContinuousLinearMap†) e‖ ^ 2)) := by
  let a := fun N ↦ qform (clmGram (S.toContinuousLinearMap ∘L (U N).toContinuousLinearMap))⁻¹ (v N)
  change Monotone a ∧ Tendsto a atTop (𝓝 (‖(S.symm.toContinuousLinearMap†) e‖ ^ 2))
  let objective := fun x : H ↦ 2 * RCLike.re ⟪e, x⟫_𝕜 - ‖S x‖ ^ 2
  let y := (S.symm.toContinuousLinearMap†) e
  have hcont : Continuous objective := by
    dsimp [objective]
    exact (continuous_const.mul (RCLike.continuous_re.comp (continuous_const.inner continuous_id))).sub
      (S.continuous.norm.pow 2)
  have hObj (x : H) : objective x = ‖y‖ ^ 2 - ‖y - S x‖ ^ 2 := by
    dsimp [objective, y]
    rw [norm_sub_sq (𝕜 := 𝕜), adjoint_inner_left]
    have hx : S.symm.toContinuousLinearMap (S x) = x := S.symm_apply_apply x
    rw [hx]
    ring
  have hMax (x : H) : objective x ≤ ‖y‖ ^ 2 := by
    rw [hObj]
    exact sub_le_self _ (sq_nonneg _)
  have hMaxAttained : objective (S.symm y) = ‖y‖ ^ 2 := by
    rw [hObj, S.apply_symm_apply, sub_self, norm_zero]
    ring
  have hsynthesis (N : ℕ) (c : d N → 𝕜) :
      objective (U N (WithLp.toLp 2 c)) =
        2 * RCLike.re (star (v N) ⬝ᵥ c) -
          qform (clmGram (S.toContinuousLinearMap ∘L (U N).toContinuousLinearMap)) c := by
    have hinner : ⟪e, U N (WithLp.toLp 2 c)⟫_𝕜 = star (v N) ⬝ᵥ c := by
      rw [← he N, LinearIsometry.inner_map_map, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rw [qform_clmGram]
    change 2 * RCLike.re ⟪e, U N (WithLp.toLp 2 c)⟫_𝕜 -
      ‖S (U N (WithLp.toLp 2 c))‖ ^ 2 = _
    rw [hinner]
    rfl
  have hPos (N : ℕ) : (clmGram (S.toContinuousLinearMap ∘L (U N).toContinuousLinearMap)).PosDef :=
    clmGram_posDef _ (S.injective.comp (U N).injective)
  have hupper (N : ℕ) (x : H) (hx : x ∈ Set.range (U N)) : objective x ≤ a N := by
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := WithLp.toLp_surjective 2 c
    rw [hsynthesis]
    exact qform_inv_ge (hPos N) _ _
  have hatt (N : ℕ) : ∃ x ∈ Set.range (U N), objective x = a N := by
    let c := ((clmGram (S.toContinuousLinearMap ∘L (U N).toContinuousLinearMap))⁻¹ *ᵥ v N)
    refine ⟨U N (WithLp.toLp 2 c), ⟨_, rfl⟩, ?_⟩
    rw [hsynthesis]
    exact qform_inv_eq_optimum (hPos N) _
  constructor
  · intro N M hNM
    obtain ⟨x, hx, hax⟩ := hatt N
    rw [← hax]
    exact hupper M x (hnest N M hNM hx)
  · apply tendsto_order.mpr
    constructor
    · intro b hb
      obtain ⟨x, ⟨N, hNx⟩, hxb⟩ :=
        hdense.exists_mem_open (isOpen_lt continuous_const hcont)
          ⟨S.symm y, show b < objective (S.symm y) by simpa only [hMaxAttained] using hb⟩
      exact eventually_atTop.mpr ⟨N, fun M hNM ↦
        (show b < objective x from hxb).trans_le (hupper M x (hnest N M hNM hNx))⟩
    · intro b hb
      apply Eventually.of_forall
      intro N
      obtain ⟨x, _, hax⟩ := hatt N
      rw [← hax]
      exact (hMax x).trans_lt hb

end Exhaustion

theorem opNorm_eq_l2_norm (A : Matrix ι ι 𝕜) : opNorm A = ‖A‖ :=
  (opNorm_square_eq A).trans (Matrix.l2_opNorm_toEuclideanCLM A)

theorem opNorm_mul_le (A B : Matrix ι ι 𝕜) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  simp only [opNorm_eq_l2_norm]
  exact Matrix.l2_opNorm_mul A B

theorem opNorm_conjTranspose (A : Matrix ι ι 𝕜) : opNorm Aᴴ = opNorm A := by
  simp only [opNorm_eq_l2_norm]
  exact Matrix.l2_opNorm_conjTranspose A

theorem opNorm_conjTranspose_mul_self (A : Matrix ι ι 𝕜) : opNorm (Aᴴ * A) = opNorm A ^ 2 := by
  simp only [opNorm_eq_l2_norm]
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]

theorem opNorm_unitary_le_one (U : Matrix.unitaryGroup ι 𝕜) :
    opNorm (U : Matrix ι ι 𝕜) ≤ 1 := by
  have h : opNorm (U : Matrix ι ι 𝕜) ^ 2 = opNorm (1 : Matrix ι ι 𝕜) := by
    rw [← opNorm_conjTranspose_mul_self]
    change opNorm (star (U : Matrix ι ι 𝕜) * (U : Matrix ι ι 𝕜)) = _
    rw [Unitary.coe_star_mul_self]
  have h' : opNorm (1 : Matrix ι ι 𝕜) ≤ 1 := by
    rw [opNorm_square_eq, map_one]
    exact ContinuousLinearMap.norm_id_le
  apply (sq_le_sq₀ (show 0 ≤ opNorm _ from norm_nonneg _) zero_le_one).mp
  rw [h, one_pow]
  exact h'

theorem opNorm_unitary_conj (U : Matrix.unitaryGroup ι 𝕜) (A : Matrix ι ι 𝕜) :
    opNorm ((U : Matrix ι ι 𝕜) * A * (U : Matrix ι ι 𝕜)ᴴ) = opNorm A := by
  have hleft (V : Matrix.unitaryGroup ι 𝕜) (X : Matrix ι ι 𝕜) :
      opNorm ((V : Matrix ι ι 𝕜) * X * (V : Matrix ι ι 𝕜)ᴴ) ≤ opNorm X := by
    have hV := opNorm_unitary_le_one V
    have hn : 0 ≤ opNorm X := norm_nonneg _
    have hn' : 0 ≤ opNorm (V : Matrix ι ι 𝕜) := norm_nonneg _
    calc
      _ ≤ opNorm ((V : Matrix ι ι 𝕜) * X) * opNorm ((V : Matrix ι ι 𝕜)ᴴ) := opNorm_mul_le _ _
      _ ≤ (opNorm (V : Matrix ι ι 𝕜) * opNorm X) * opNorm ((V : Matrix ι ι 𝕜)ᴴ) :=
        mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * opNorm X) * 1 := by
        rw [opNorm_conjTranspose]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hV hn) hV hn' (by positivity)
      _ = _ := by ring
  apply le_antisymm (hleft U A)
  have hr := hleft (star U) ((U : Matrix ι ι 𝕜) * A * (U : Matrix ι ι 𝕜)ᴴ)
  change opNorm (star (U : Matrix ι ι 𝕜) *
    ((U : Matrix ι ι 𝕜) * A * star (U : Matrix ι ι 𝕜)) * star (star (U : Matrix ι ι 𝕜))) ≤ _ at hr
  rw [star_star, ← mul_assoc (star (U : Matrix ι ι 𝕜)), ← mul_assoc (star (U : Matrix ι ι 𝕜)),
    Unitary.coe_star_mul_self, one_mul, mul_assoc, Unitary.coe_star_mul_self, mul_one] at hr
  exact hr

theorem opNorm_eq_eigenvalue_norm {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    opNorm A = ‖fun i ↦ (hA.eigenvalues i : 𝕜)‖ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rw [show (star (hA.eigenvectorUnitary : Matrix ι ι 𝕜)) =
    (hA.eigenvectorUnitary : Matrix ι ι 𝕜)ᴴ from rfl, opNorm_unitary_conj,
    opNorm_eq_l2_norm, Matrix.l2_opNorm_diagonal]
  rfl

theorem opNorm_posSemidef_eq_eigenvalue [Nonempty ι] {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    ∃ i, opNorm A = hA.isHermitian.eigenvalues i := by
  obtain ⟨i, hi⟩ := Finite.exists_max hA.isHermitian.eigenvalues
  refine ⟨i, ?_⟩
  rw [opNorm_eq_eigenvalue_norm hA.isHermitian]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (hA.eigenvalues_nonneg i)).mpr fun j ↦ ?_
    rw [RCLike.norm_ofReal, abs_of_nonneg (hA.eigenvalues_nonneg j)]
    exact hi j
  · simpa only [RCLike.norm_ofReal, abs_of_nonneg (hA.eigenvalues_nonneg i)] using
      norm_le_pi_norm (fun j ↦ (hA.isHermitian.eigenvalues j : 𝕜)) i

theorem opNorm_psd_le_iff [Nonempty ι] {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) {r : ℝ} :
    opNorm A ≤ r ↔ A ≤ r • (1 : Matrix ι ι 𝕜) := by
  constructor
  · intro h
    apply matrix_le_of_qform_le hA.isHermitian (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
    intro x
    rw [qform_smul, qform_one]
    exact (le_abs_self _).trans ((abs_qform_le A x).trans
      (mul_le_mul_of_nonneg_right h (sq_nonneg _)))
  · intro h
    obtain ⟨j, hj⟩ := opNorm_posSemidef_eq_eigenvalue hA
    have hq := qform_mono h (WithLp.ofLp (hA.isHermitian.eigenvectorBasis j))
    rw [qform_smul, qform_one, WithLp.toLp_ofLp, hA.isHermitian.eigenvectorBasis.norm_eq_one,
      one_pow, mul_one] at hq
    rw [hj, hA.isHermitian.eigenvalues_eq]
    exact hq

theorem opNorm_le_re_trace_of_psd [Nonempty ι] {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    opNorm A ≤ RCLike.re A.trace := by
  obtain ⟨i, hi⟩ := opNorm_posSemidef_eq_eigenvalue hA
  rw [hi, Matrix.IsHermitian.trace_eq_sum_eigenvalues hA.isHermitian, map_sum]
  simp only [RCLike.ofReal_re]
  exact Finset.single_le_sum (fun j _ ↦ hA.eigenvalues_nonneg j) (Finset.mem_univ i)

section DualGram

open ContinuousLinearMap

variable {E H : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

theorem norm_isometric_conjugation (V : E →L[𝕜] H) (hV : V† ∘L V = 1) (T : E →L[𝕜] E) :
    ‖V ∘L T ∘L V†‖ = ‖T‖ := by
  have hnorm : ‖V‖ ≤ 1 := V.opNorm_le_bound zero_le_one (fun x ↦ by
    rw [one_mul, (V.norm_map_iff_adjoint_comp_self.mpr hV) x])
  have hnorm' : ‖V†‖ ≤ 1 := by simpa only [LinearIsometryEquiv.norm_map] using hnorm
  have hT (U : E →L[𝕜] E) :
      ‖V ∘L U ∘L V†‖ ≤ ‖U‖ := calc
    _ ≤ ‖V‖ * ‖U ∘L V†‖ := V.opNorm_comp_le _
    _ ≤ ‖V‖ * (‖U‖ * ‖V†‖) :=
      mul_le_mul_of_nonneg_left (U.opNorm_comp_le _) (norm_nonneg _)
    _ ≤ 1 * (‖U‖ * 1) :=
      mul_le_mul hnorm (mul_le_mul_of_nonneg_left hnorm' (norm_nonneg _)) (by positivity)
        zero_le_one
    _ = _ := by ring
  apply le_antisymm (hT T)
  have hBack : (V† ∘L (V ∘L T ∘L V†) ∘L V) = T := by
    ext x
    change (V†) (V (T ((V†) (V x)))) = T x
    have hid (y : E) : (V†) (V y) = y := DFunLike.congr_fun hV y
    rw [hid, hid]
  calc
    ‖T‖ = ‖V† ∘L (V ∘L T ∘L V†) ∘L V‖ := congrArg norm hBack.symm
    _ ≤ ‖V†‖ * ‖(V ∘L T ∘L V†) ∘L V‖ := (V†).opNorm_comp_le _
    _ ≤ ‖V†‖ * (‖V ∘L T ∘L V†‖ * ‖V‖) :=
      mul_le_mul_of_nonneg_left ((V ∘L T ∘L V†).opNorm_comp_le _) (norm_nonneg _)
    _ ≤ 1 * (‖V ∘L T ∘L V†‖ * 1) :=
      mul_le_mul hnorm' (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)) (by positivity)
        zero_le_one
    _ = _ := by ring

theorem norm_sq_synthesis_dual (R S : EuclideanSpace 𝕜 ι →L[𝕜] H) (hR : Function.Injective R) :
    ‖R ∘L S†‖ ^ 2 =
      opNorm (CFC.sqrt (clmGram R) * clmGram S * CFC.sqrt (clmGram R)) := by
  let G := clmGram R
  let C := CFC.sqrt G
  let f := Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)
  let L := f C
  let Li := f C⁻¹
  have hG : G.PosDef := clmGram_posDef R hR
  have hC : C.PosDef := posDef_sqrt hG
  have hCinvUnit := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have hCsq : C * C = G := sqrt_mul_sqrt_of_posDef hG
  have hLiAdj : Li† = Li := by
    change star (f C⁻¹) = f C⁻¹
    rw [← map_star]
    exact congrArg f hC.inv.isHermitian.eq
  have hLAdj : L† = L := by
    change star (f C) = f C
    rw [← map_star]
    exact congrArg f hC.isHermitian.eq
  have hLinv : L * Li = 1 := by
    change f C * f C⁻¹ = 1
    rw [← map_mul, Matrix.mul_nonsing_inv _ hCinvUnit, map_one]
  have hLinv' : Li * L = 1 := by
    change f C⁻¹ * f C = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ hCinvUnit, map_one]
  have hLsq : L * L = R† ∘L R := by
    change f C * f C = _
    rw [← map_mul, hCsq]
    exact toEuclideanCLM_clmGram R
  let V := R ∘L Li
  have hRg : V ∘L L = R := by
    ext x
    change R ((Li * L) x) = R x
    rw [hLinv']
    rfl
  have hV : V† ∘L V = 1 := by
    change (R ∘L Li)† ∘L (R ∘L Li) = 1
    rw [adjoint_comp, hLiAdj]
    change Li * (R† ∘L R) * Li = 1
    rw [← hLsq, ← mul_assoc, hLinv', one_mul, hLinv]
  have hA : f (C * clmGram S * C) = L ∘L S† ∘L S ∘L L := by
    simp only [map_mul, toEuclideanCLM_clmGram, L, f]
    ext x
    rfl
  change ‖R ∘L S†‖ ^ 2 = opNorm (C * clmGram S * C)
  rw [opNorm_square_eq]
  have hh : (R ∘L S†) ∘L (R ∘L S†)† =
      V ∘L (f (C * clmGram S * C)) ∘L V† := by
    rw [hA, ← hRg, adjoint_comp, adjoint_comp, adjoint_adjoint, hLAdj]
    ext x
    rfl
  rw [← norm_comp_adjoint (R ∘L S†), hh, norm_isometric_conjugation V hV]

end DualGram

section Rectangular

variable {κ σ : Type*} [Fintype κ] [Fintype σ] [DecidableEq κ] [DecidableEq σ]

omit [DecidableEq κ] in
theorem opNorm_rect_eq_l2_norm (A : Matrix κ ι 𝕜) : opNorm A = ‖A‖ := rfl

theorem opNorm_rect_conjTranspose (A : Matrix κ ι 𝕜) : opNorm Aᴴ = opNorm A := by
  simp only [opNorm_rect_eq_l2_norm]
  exact Matrix.l2_opNorm_conjTranspose A

omit [DecidableEq κ] in
theorem opNorm_rect_conjTranspose_mul_self (A : Matrix κ ι 𝕜) :
    opNorm (Aᴴ * A) = opNorm A ^ 2 := by
  simp only [opNorm_rect_eq_l2_norm]
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]

omit [DecidableEq σ] in
theorem opNorm_mul_rect (A : Matrix σ κ 𝕜) (B : Matrix κ ι 𝕜) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  simp only [opNorm_rect_eq_l2_norm]
  exact Matrix.l2_opNorm_mul A B

omit [DecidableEq κ] in
theorem opNorm_isometric_columns_le (A : Matrix κ ι 𝕜) (hA : Aᴴ * A = 1) : opNorm A ≤ 1 := by
  have hs := opNorm_rect_conjTranspose_mul_self A
  rw [hA, opNorm_square_eq, map_one] at hs
  apply (sq_le_sq₀ (show 0 ≤ opNorm A from norm_nonneg _) zero_le_one).mp
  rw [← hs, one_pow]
  exact ContinuousLinearMap.norm_id_le

theorem opNorm_rect_compress {A : Matrix κ ι 𝕜} (hA : Aᴴ * A = 1) (B : Matrix κ κ 𝕜) :
    opNorm (Aᴴ * B * A) ≤ opNorm B := by
  have hAn := opNorm_isometric_columns_le A hA
  calc
    _ ≤ opNorm (Aᴴ * B) * opNorm A := opNorm_mul_rect _ _
    _ ≤ opNorm Aᴴ * opNorm B * opNorm A :=
      mul_le_mul_of_nonneg_right (opNorm_mul_rect _ _) (norm_nonneg _)
    _ ≤ 1 * opNorm B * 1 := by
      rw [opNorm_rect_conjTranspose]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hAn (norm_nonneg _)) hAn
        (norm_nonneg _) (by positivity : 0 ≤ 1 * ‖(Matrix.toEuclideanLin B).toContinuousLinearMap‖)
    _ = _ := by ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem qform_fromBlocks_diagonal (A : Matrix ι ι 𝕜) (B : Matrix κ κ 𝕜) (x : ι ⊕ κ → 𝕜) :
    qform (Matrix.fromBlocks A 0 0 B) x =
      qform A (x ∘ Sum.inl) + qform B (x ∘ Sum.inr) := by
  simp [qform, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Function.comp_def]

theorem opNorm_fromBlocks_diagonal_le (A : Matrix ι ι 𝕜) (B : Matrix κ κ 𝕜) :
    opNorm (Matrix.fromBlocks A 0 0 B) ≤ max (opNorm A) (opNorm B) := by
  let K := max (opNorm A) (opNorm B)
  have hn : 0 ≤ opNorm A := norm_nonneg _
  have hK : 0 ≤ K := hn.trans (le_max_left _ _)
  apply (opNorm_le_iff_conjTranspose_mul_self_le _ hK).mpr
  have hA := (opNorm_le_iff_conjTranspose_mul_self_le A hK).mp (le_max_left _ _)
  have hB := (opNorm_le_iff_conjTranspose_mul_self_le B hK).mp (le_max_right _ _)
  have gram : (Matrix.fromBlocks A 0 0 B)ᴴ * Matrix.fromBlocks A 0 0 B =
      Matrix.fromBlocks (Aᴴ * A) 0 0 (Bᴴ * B) := by
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  have hd : (Matrix.fromBlocks (K ^ 2 • (1 : Matrix ι ι 𝕜)) 0 0 (K ^ 2 • (1 : Matrix κ κ 𝕜))) =
      K ^ 2 • (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜) := by
    ext x y
    cases x <;> cases y <;> simp [Matrix.one_apply]
  rw [gram, ← hd]
  refine matrix_le_of_qform_le
    (by exact (gram ▸ Matrix.isHermitian_conjTranspose_mul_self (Matrix.fromBlocks A 0 0 B)))
    (by rw [hd]; exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)) fun x ↦ ?_
  simp only [qform_fromBlocks_diagonal]
  exact add_le_add (qform_mono hA _) (qform_mono hB _)

theorem opNorm_isometric_sandwich_eq {V : Matrix κ ι 𝕜} (hV : Vᴴ * V = 1) (X : Matrix ι ι 𝕜) :
    opNorm (V * X * Vᴴ) = opNorm X := by
  have hVn := opNorm_isometric_columns_le V hV
  apply le_antisymm
  · calc
      _ ≤ opNorm (V * X) * opNorm Vᴴ := opNorm_mul_rect _ _
      _ ≤ (opNorm V * opNorm X) * opNorm Vᴴ :=
        mul_le_mul_of_nonneg_right (opNorm_mul_rect _ _) (norm_nonneg _)
      _ ≤ (1 * opNorm X) * 1 := by
        rw [opNorm_rect_conjTranspose]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hVn (norm_nonneg _)) hVn (norm_nonneg _)
          (by rw [one_mul]; exact norm_nonneg _)
      _ = _ := by ring
  · have h := opNorm_rect_compress hV (V * X * Vᴴ)
    have heq : Vᴴ * (V * X * Vᴴ) * V = (Vᴴ * V) * X * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    rw [heq, hV, Matrix.one_mul, Matrix.mul_one] at h
    exact h

theorem opNorm_sq_rectGram_dual (R S : Matrix κ ι 𝕜) (hR : (Rᴴ * R).PosDef) :
    opNorm (R * Sᴴ) ^ 2 =
      opNorm (CFC.sqrt (Rᴴ * R) * (Sᴴ * S) * CFC.sqrt (Rᴴ * R)) := by
  let A := CFC.sqrt (Rᴴ * R)
  have hA : A.PosDef := posDef_sqrt hR
  have hAA : A * A = Rᴴ * R := sqrt_mul_sqrt_of_posDef hR
  have hAu := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAu
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAu
  let V := R * A⁻¹
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_mul, hA.inv.isHermitian.eq]
    calc
      _ = A⁻¹ * (Rᴴ * R) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hAA, ← Matrix.mul_assoc A⁻¹, hAi, Matrix.one_mul, hAinv]
  have hVA : V * A = R := by
    dsimp only [V]
    rw [Matrix.mul_assoc, hAi, Matrix.mul_one]
  have hAAh : A * Vᴴ = Rᴴ := by
    have h := congrArg Matrix.conjTranspose hVA
    rw [Matrix.conjTranspose_mul, hA.isHermitian.eq] at h
    exact h
  have hCC :
      (R * Sᴴ) * (R * Sᴴ)ᴴ = V * (A * (Sᴴ * S) * A) * Vᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show V * (A * (Sᴴ * S) * A) * Vᴴ = (V * A) * Sᴴ * (S * (A * Vᴴ)) by
      simp only [Matrix.mul_assoc]]
    rw [hVA, hAAh]
  have hN := opNorm_rect_conjTranspose_mul_self (R * Sᴴ)ᴴ
  rw [Matrix.conjTranspose_conjTranspose, opNorm_rect_conjTranspose, hCC,
    opNorm_isometric_sandwich_eq hV] at hN
  exact hN.symm

end Rectangular

omit [DecidableEq ι] in
theorem matrix_congruence_mono {A B : Matrix ι ι 𝕜} (h : A ≤ B) (E : Matrix ι κ 𝕜) :
    Eᴴ * A * E ≤ Eᴴ * B * E := by
  apply Matrix.le_iff.mpr
  have hc := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same E
  rwa [Matrix.mul_sub, Matrix.sub_mul] at hc

/-- Make the first metric the identity while diagonalizing the second. -/
theorem matrix_whitening_eigenbasis {Ω A : Matrix ι ι 𝕜} (hΩ : Ω.PosDef)
    (hA : A.PosDef) (hAΩ : A ≤ Ω) :
    ∃ (E : Matrix ι ι 𝕜) (β : ι → ℝ), IsUnit E ∧ Eᴴ * Ω * E = 1 ∧
      Eᴴ * A * E = Matrix.diagonal (fun i ↦ (β i : 𝕜)) ∧ ∀ i, 0 < β i ∧ β i ≤ 1 := by
  let R := CFC.sqrt Ω
  let Q := R⁻¹
  have hR : R.PosDef := posDef_sqrt hΩ
  have hQ_herm : Qᴴ = Q := hR.inv.isHermitian.eq
  have hΩ_eq : R * R = Ω := sqrt_mul_sqrt_of_posDef hΩ
  have hRu := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hQR : Q * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hRQ : R * Q = 1 := Matrix.mul_nonsing_inv R hRu
  have hQΩ : Qᴴ * Ω * Q = 1 := by
    rw [hQ_herm, ← hΩ_eq, ← Matrix.mul_assoc, hQR, Matrix.one_mul, hRQ]
  let L := Qᴴ * A * Q
  have hLp : L.PosDef := hA.conjTranspose_mul_mul_same
    ((Matrix.mulVec_injective_iff_isUnit).mpr hR.inv.isUnit)
  have hL₁ : L ≤ 1 := hQΩ ▸ matrix_congruence_mono hAΩ Q
  let U := hLp.isHermitian.eigenvectorUnitary
  let U₀ := (U : Matrix ι ι 𝕜)
  let β := hLp.isHermitian.eigenvalues
  let D := Matrix.diagonal (fun i ↦ (β i : 𝕜))
  have hUU : U₀ᴴ * U₀ = 1 := Unitary.coe_star_mul_self U
  have hUu : IsUnit U₀ := by
    apply (Matrix.isUnit_iff_isUnit_det U₀).mpr
    have h := congrArg Matrix.det hUU
    rw [Matrix.det_mul, Matrix.det_one] at h
    refine isUnit_iff_ne_zero.mpr fun hz ↦ ?_
    rw [hz, mul_zero] at h
    exact zero_ne_one h
  have hS : L = U₀ * D * U₀ᴴ := by
    conv_lhs => rw [hLp.isHermitian.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hUL : U₀ᴴ * L * U₀ = D := by
    rw [hS, show U₀ᴴ * (U₀ * D * U₀ᴴ) * U₀ = (U₀ᴴ * U₀) * D * (U₀ᴴ * U₀) by
      simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
  have hD₁ : D ≤ 1 := by
    have h := matrix_congruence_mono hL₁ U₀
    rwa [hUL, Matrix.mul_one, hUU] at h
  let E := Q * U₀
  have hEu : IsUnit E := hR.inv.isUnit.mul hUu
  have hTransform (M : Matrix ι ι 𝕜) : Eᴴ * M * E = U₀ᴴ * (Qᴴ * M * Q) * U₀ := by
    dsimp only [E]
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨E, β, hEu, ?_, ?_, ?_⟩
  · rw [hTransform, hQΩ, Matrix.mul_one, hUU]
  · rw [hTransform]
    exact hUL
  · intro i
    refine ⟨hLp.eigenvalues_pos i, ?_⟩
    have h := qform_mono hD₁ (Pi.single i (1 : 𝕜))
    simpa [D, qform, Matrix.mulVec_diagonal] using h

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Augmented Gram in column-major coordinates with a common row Gram. -/
def columnTensorGram (A Ω : Matrix ι ι 𝕜) (B : Matrix σ σ 𝕜) : Matrix (σ × ι) (σ × ι) 𝕜 :=
  (1 : Matrix σ σ 𝕜) ⊗ₖ A + B ⊗ₖ (Ω - A)

/-- Apply the same coefficient change in every column. -/
def columnTensorChange (E : Matrix ι ι 𝕜) : Matrix (σ × ι) (σ × ι) 𝕜 :=
  (1 : Matrix σ σ 𝕜) ⊗ₖ E

omit [DecidableEq ι] in
theorem columnTensorGram_congruence (A Ω : Matrix ι ι 𝕜) (B : Matrix σ σ 𝕜)
    (E : Matrix ι ι 𝕜) :
    (columnTensorChange E (σ := σ))ᴴ * columnTensorGram A Ω B * columnTensorChange E =
      columnTensorGram (Eᴴ * A * E) (Eᴴ * Ω * E) B := by
  have he : (columnTensorChange E (σ := σ))ᴴ = columnTensorChange Eᴴ := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases h : i = j
    · subst j
      simp [columnTensorChange, Matrix.conjTranspose_apply]
    · simp [columnTensorChange, Matrix.conjTranspose_apply, h, Ne.symm h]
  rw [he]
  simp only [columnTensorChange, columnTensorGram, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] in
theorem posDef_convex_combination {A B : Matrix ι ι 𝕜} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (t • A + (1 - t) • B).PosDef := by
  apply posDef_of_qform_pos
    ((hA.isHermitian.smul (IsSelfAdjoint.all _)).add (hB.isHermitian.smul (IsSelfAdjoint.all _)))
  intro x hx
  simp only [qform_add, qform_smul]
  by_cases hz : t = 0
  · simpa [hz] using qform_pos hB hx
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ht (Ne.symm hz)) (qform_pos hA hx))
      (mul_nonneg (sub_nonneg.mpr ht') (qform_pos hB hx).le)

/-- Convexity of inversion on a line segment of positive definite matrices. -/
theorem matrix_inv_convex_combination {A B : Matrix ι ι 𝕜} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (t • A + (1 - t) • B)⁻¹ ≤ t • A⁻¹ + (1 - t) • B⁻¹ := by
  let S := t • A + (1 - t) • B
  have hS : S.PosDef := posDef_convex_combination hA hB ht ht'
  apply matrix_le_of_qform_le hS.inv.isHermitian
    ((hA.inv.isHermitian.smul (IsSelfAdjoint.all _)).add (hB.inv.isHermitian.smul (IsSelfAdjoint.all _)))
  intro v
  let c := S⁻¹ *ᵥ v
  rw [← qform_inv_eq_optimum hS]
  have h1 := qform_inv_ge hA v c
  have h2 := qform_inv_ge hB v c
  change 2 * RCLike.re (star v ⬝ᵥ c) - qform (t • A + (1 - t) • B) c ≤ _
  simp only [qform_add, qform_smul]
  calc
    _ = t * (2 * RCLike.re (star v ⬝ᵥ c) - qform A c) +
        (1 - t) * (2 * RCLike.re (star v ⬝ᵥ c) - qform B c) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 ht)
      (mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr ht'))

end SchauderBasisOrbits
