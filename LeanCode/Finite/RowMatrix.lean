import LeanCode.Finite.Projection

/-! Hermitian tests and block estimates for real skew matrices. -/

open Matrix ContinuousLinearMap
open scoped BigOperators InnerProductSpace InnerProduct MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace SchauderBasisOrbits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian representative of a real skew matrix. -/
def skewHermitian (S : Matrix ι ι ℝ) : Matrix ι ι ℂ := Complex.I • complexify S

omit [Fintype ι] [DecidableEq ι] in
theorem skewHermitian_isHermitian {S : Matrix ι ι ℝ} (hS : Sᵀ = -S) :
    (skewHermitian S).IsHermitian := by
  ext i j
  have hSij : S j i = -S i j := congrFun₂ hS i j
  simp [skewHermitian, Matrix.conjTranspose_apply, hSij, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem skewHermitian_transpose {S : Matrix ι ι ℝ} (hS : Sᵀ = -S) :
    (skewHermitian S)ᵀ = -skewHermitian S := by
  ext i j
  have hSij : S j i = -S i j := congrFun₂ hS i j
  simp [skewHermitian, hSij, smul_eq_mul]

theorem opNorm_skewHermitian (S : Matrix ι ι ℝ) : opNorm (skewHermitian S) = opNorm S := by
  rw [← opNorm_complexify, opNorm_square_eq, opNorm_square_eq]
  simp [skewHermitian, norm_smul]

/-- The norm test for a real skew matrix only needs one side of the Hermitian order bound. -/
theorem opNorm_skew_le_iff {S : Matrix ι ι ℝ} (hS : Sᵀ = -S) {h : ℝ} (hh : 0 ≤ h) :
    opNorm S ≤ h ↔ (h • (1 : Matrix ι ι ℂ) - skewHermitian S).PosSemidef := by
  let A := skewHermitian S
  have hA : A.IsHermitian := skewHermitian_isHermitian hS
  have hAT : Aᵀ = -A := skewHermitian_transpose hS
  have hnorm : opNorm A = opNorm S := opNorm_skewHermitian S
  change opNorm S ≤ h ↔ (h • (1 : Matrix ι ι ℂ) - A).PosSemidef
  rw [← hnorm]
  constructor
  · intro hn
    refine posSemidef_of_qform_nonneg ((Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).sub hA)
      fun x ↦ ?_
    rw [qform_sub, qform_smul, qform_one, sub_nonneg]
    exact (le_abs_self _).trans ((abs_qform_le A x).trans
      (mul_le_mul_of_nonneg_right hn (sq_nonneg _)))
  · intro hp
    have hp' : (h • (1 : Matrix ι ι ℂ) + A).PosSemidef := by
      simpa only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
        hAT, sub_neg_eq_add] using hp.transpose
    have hc : Commute (h • (1 : Matrix ι ι ℂ) - A) (h • (1 : Matrix ι ι ℂ) + A) := by
      unfold Commute SemiconjBy
      simp only [sub_mul, mul_add, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one, smul_add, smul_sub, smul_smul ]
      abel
    have hprod := Commute.mul_nonneg hp.nonneg hp'.nonneg hc
    have hprod_eq : (h • (1 : Matrix ι ι ℂ) - A) * (h • (1 : Matrix ι ι ℂ) + A) =
        h ^ 2 • (1 : Matrix ι ι ℂ) - Aᴴ * A := by
      rw [hA.eq]
      simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
        smul_sub, pow_two]
      abel
    rw [hprod_eq, Matrix.nonneg_iff_posSemidef] at hprod
    exact (opNorm_le_iff_conjTranspose_mul_self_le A hh).mpr (Matrix.le_iff.mpr hprod)

omit [DecidableEq ι] in
private theorem qform_sum_inl (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ) (c : ι → ℝ) :
    qform A (Sum.elim c (fun _ ↦ 0)) =
      qform (A.submatrix Sum.inl Sum.inl) c := by
  simp only [qform, RCLike.re_to_real, star_trivial, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Matrix.submatrix_apply]

omit [DecidableEq ι] in
private theorem norm_sq_sum_inl (c : ι → ℝ) :
    ‖WithLp.toLp 2 (Sum.elim c (fun _ : Unit ↦ 0))‖ ^ 2 = ‖WithLp.toLp 2 c‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp [Fintype.sum_sum_type]

private theorem qform_eigenvalue {A : Matrix ι ι ℝ} {x : ι → ℝ} {a : ℝ}
    (hx : A *ᵥ x = a • x) :
    qform A x = a * ‖WithLp.toLp 2 x‖ ^ 2 := by
  have qone : dotProduct x x = ‖WithLp.toLp 2 x‖ ^ 2 := by
    simpa [qform] using qform_one x
  unfold qform
  rw [hx, dotProduct_smul, smul_eq_mul, RCLike.re_to_real, star_trivial, qone]

/-- For real skew matrices, deleting one coordinate preserves the largest Rayleigh
value of the positive matrix `Aᴴ * A`. A top eigenspace of a real skew square
contains a two-dimensional plane, allowing one coefficient to be zero. -/
theorem opNorm_sq_skew_eq_submatrix [Nonempty ι]
    {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ} (hA : Aᵀ = -A) :
    opNorm A ^ 2 = opNorm ((Aᴴ * A).submatrix Sum.inl Sum.inl) := by
  let G := Aᴴ * A
  let B := G.submatrix Sum.inl Sum.inl
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hB : B.PosSemidef := hG.submatrix Sum.inl
  have hLam : opNorm G = opNorm A ^ 2 := opNorm_conjTranspose_mul_self A
  rw [← hLam]
  apply le_antisymm
  · by_cases hzero : opNorm G = 0
    · rw [hzero]
      exact norm_nonneg _
    · have hjpos : 0 < opNorm G := lt_of_le_of_ne (show 0 ≤ opNorm G from norm_nonneg _) (Ne.symm hzero)
      obtain ⟨j, hj⟩ := opNorm_posSemidef_eq_eigenvalue hG
      let lam := opNorm G
      let u := hG.isHermitian.eigenvectorBasis j
      let v := WithLp.ofLp u
      have hv : G *ᵥ v = lam • v := by
        change G *ᵥ v = opNorm G • v
        rw [hj]
        exact hG.isHermitian.mulVec_eigenvectorBasis j
      have hvne : v ≠ 0 := by
        intro hh
        have hu0 : u = 0 := by
          apply WithLp.ofLp_injective
          exact hh
        have hn := hG.isHermitian.eigenvectorBasis.norm_eq_one j
        rw [show hG.isHermitian.eigenvectorBasis j = 0 from hu0, norm_zero] at hn
        norm_num at hn
      have hAt : Aᴴ = -A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA
      have hGmul : G = -(A * A) := by
        change Aᴴ * A = _
        rw [hAt, neg_mul]
      let w := A *ᵥ v
      have hww : A *ᵥ w = -lam • v := by
        change A *ᵥ (A *ᵥ v) = _
        rw [mulVec_mulVec, ← neg_neg (A * A), ← hGmul, neg_mulVec, hv, neg_smul]
      have hw : G *ᵥ w = lam • w := by
        change G *ᵥ (A *ᵥ v) = lam • (A *ᵥ v)
        rw [mulVec_mulVec]
        have hc : G * A = A * G := by rw [hGmul, neg_mul, mul_neg, mul_assoc]
        rw [hc, ← mulVec_mulVec, hv, mulVec_smul]
      obtain ⟨y, hy, hyne, hyzero⟩ :
          ∃ y : (ι ⊕ Unit) → ℝ, G *ᵥ y = lam • y ∧ y ≠ 0 ∧ y (.inr ()) = 0 := by
        by_cases hvzero : v (.inr ()) = 0
        · exact ⟨v, hv, hvne, hvzero⟩
        · let a := w (.inr ()) / v (.inr ())
          let y := w - a • v
          have hy : G *ᵥ y = lam • y := by
            dsimp [y]
            rw [mulVec_sub, hw, mulVec_smul, hv, smul_sub]
            congr 1
            simp [smul_smul, mul_comm]
          have hzne : y ≠ 0 := by
            intro hz
            have hz' : w = a • v := sub_eq_zero.mp hz
            have hh : A *ᵥ w = (a * a) • v := by
              rw [hz', mulVec_smul]
              change a • w = _
              rw [hz', smul_smul]
            rw [hww] at hh
            obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
              by_contra! h
              exact hvne (funext h)
            have hEq : -lam * v i = (a * a) * v i := congrFun hh i
            have hEq' := mul_right_cancel₀ hi hEq
            nlinarith [sq_nonneg a]
          refine ⟨y, hy, hzne, ?_⟩
          change w (.inr ()) - a * v (.inr ()) = 0
          dsimp [a]
          field_simp [hvzero]
          ring
      let c := y ∘ Sum.inl
      have hyrepr : y = Sum.elim c (fun _ ↦ 0) := by
        funext i
        cases i with
        | inl i => rfl
        | inr i => simpa using hyzero
      have hcne : c ≠ 0 := by
        intro hc
        apply hyne
        rw [hyrepr, hc]
        funext i
        cases i <;> rfl
      have hcn : 0 < ‖WithLp.toLp 2 c‖ ^ 2 := by
        apply pow_pos (norm_pos_iff.mpr ?_)
        intro hz
        exact hcne (congrArg WithLp.ofLp hz)
      have hq := qform_eigenvalue hy
      rw [hyrepr, qform_sum_inl, norm_sq_sum_inl] at hq
      have hq' := (le_abs_self (qform B c)).trans (abs_qform_le B c)
      rw [show qform B c = lam * ‖WithLp.toLp 2 c‖ ^ 2 from hq] at hq'
      exact le_of_mul_le_mul_right hq' hcn
  · apply (opNorm_psd_le_iff hB).mpr
    refine matrix_le_of_qform_le hB.isHermitian (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
      fun c ↦ ?_
    rw [qform_smul, qform_one]
    have h := (le_abs_self (qform G (Sum.elim c (fun _ ↦ 0)))).trans
      (abs_qform_le G (Sum.elim c (fun _ ↦ 0)))
    rwa [qform_sum_inl, norm_sq_sum_inl] at h

/-- A real skew arrow matrix. -/
def skewArrow (S : Matrix ι ι ℝ) (b : ι → ℝ) (s : ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  let column := Matrix.replicateCol Unit (s • b)
  Matrix.fromBlocks S column (-columnᵀ) 0

omit [Fintype ι] [DecidableEq ι] in
theorem skewArrow_transpose {S : Matrix ι ι ℝ} (hS : Sᵀ = -S) (b : ι → ℝ) (s : ℝ) :
    (skewArrow S b s)ᵀ = -skewArrow S b s := by
  simp [skewArrow, Matrix.fromBlocks_transpose, hS, Matrix.fromBlocks_neg]

theorem opNorm_sq_skewArrow [Nonempty ι]
    {S : Matrix ι ι ℝ} (hS : Sᵀ = -S) (b : ι → ℝ) (s : ℝ) :
    opNorm (skewArrow S b s) ^ 2 = opNorm (-(S * S) + s ^ 2 • Matrix.vecMulVec b b) := by
  rw [opNorm_sq_skew_eq_submatrix (skewArrow_transpose hS b s)]
  congr 1
  rw [conjTranspose_eq_transpose_of_trivial, skewArrow_transpose hS b s, neg_mul]
  ext i j
  simp [skewArrow, Matrix.fromBlocks_multiply, Matrix.mul_apply, smul_eq_mul, pow_two,
    Matrix.vecMulVec_apply]
  ring

omit [DecidableEq ι] in
theorem skewArrow_upper_gram {S : Matrix ι ι ℝ} (hS : Sᵀ = -S) (b : ι → ℝ) (s : ℝ) :
    ((skewArrow S b s)ᴴ * (skewArrow S b s)).submatrix Sum.inl Sum.inl =
      -(S * S) + s ^ 2 • Matrix.vecMulVec b b := by
  rw [conjTranspose_eq_transpose_of_trivial, skewArrow_transpose hS b s, neg_mul]
  ext i j
  simp [skewArrow, Matrix.fromBlocks_multiply, Matrix.mul_apply, smul_eq_mul, pow_two,
    Matrix.vecMulVec_apply]
  ring

theorem skewArrow_sq_le_iff [Nonempty ι] {S : Matrix ι ι ℝ} (hS : Sᵀ = -S)
    (b : ι → ℝ) (s q : ℝ) : opNorm (skewArrow S b s) ^ 2 ≤ q ↔
      (q • (1 : Matrix ι ι ℝ) + S * S - s ^ 2 • Matrix.vecMulVec b b).PosSemidef := by
  have hPSD : (-(S * S) + s ^ 2 • Matrix.vecMulVec b b).PosSemidef :=
    skewArrow_upper_gram hS b s ▸ (Matrix.posSemidef_conjTranspose_mul_self _).submatrix Sum.inl
  rw [opNorm_sq_skewArrow hS, opNorm_psd_le_iff hPSD, Matrix.le_iff]
  have heq :
      q • (1 : Matrix ι ι ℝ) - (-(S * S) + s ^ 2 • Matrix.vecMulVec b b) =
        q • (1 : Matrix ι ι ℝ) + S * S - s ^ 2 • Matrix.vecMulVec b b := by abel
  rw [heq]

theorem opNorm_add_le_real (A B : Matrix ι ι ℝ) : opNorm (A + B) ≤ opNorm A + opNorm B := by
  simp only [opNorm_square_eq, map_add, norm_add_le]

theorem opNorm_smul_real (a : ℝ) (A : Matrix ι ι ℝ) : opNorm (a • A) = |a| * opNorm A := by
  simp only [opNorm_square_eq, map_smul, norm_smul, Real.norm_eq_abs]

theorem vecMulVec_self_toEuclideanCLM (v : ι → ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (Matrix.vecMulVec v v) =
      InnerProductSpace.rankOne ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 v) := by
  ext x : 1
  obtain ⟨x, rfl⟩ := WithLp.toLp_surjective 2 x
  rw [Matrix.toEuclideanCLM_toLp, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  apply WithLp.ofLp_injective
  funext i
  simp [Matrix.vecMulVec_mulVec, mul_comm]

theorem opNorm_vecMulVec_self_real (v : ι → ℝ) :
    opNorm (Matrix.vecMulVec v v) = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [opNorm_square_eq, vecMulVec_self_toEuclideanCLM, InnerProductSpace.norm_rankOne, pow_two]

theorem opNorm_sq_skewArrow_increment [Nonempty ι] {S : Matrix ι ι ℝ} (hS : Sᵀ = -S)
    (b : ι → ℝ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    opNorm (skewArrow S b s) ^ 2 ≤
      opNorm (skewArrow S b r) ^ 2 + (s ^ 2 - r ^ 2) * ‖WithLp.toLp 2 b‖ ^ 2 := by
  rw [opNorm_sq_skewArrow hS, opNorm_sq_skewArrow hS]
  let V := Matrix.vecMulVec b b
  have hdiff : 0 ≤ s ^ 2 - r ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hr hrs 2)
  change opNorm (-(S * S) + s ^ 2 • V) ≤ _
  have hSplit : -(S * S) + s ^ 2 • V =
      (-(S * S) + r ^ 2 • V) + (s ^ 2 - r ^ 2) • V := by
    rw [sub_smul]
    abel
  rw [hSplit]
  apply (opNorm_add_le_real _ _).trans
  rw [opNorm_smul_real, abs_of_nonneg hdiff, opNorm_vecMulVec_self_real]

theorem dotProduct_self_real (x : ι → ℝ) :
    dotProduct x x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  simpa [qform] using qform_one x

omit [DecidableEq ι] in
theorem vecMulVec_mulVec_real (x y z : ι → ℝ) :
    Matrix.vecMulVec x y *ᵥ z = (dotProduct y z) • x := by
  rw [Matrix.vecMulVec_mulVec]
  funext i
  exact mul_comm _ _

omit [Fintype ι] [DecidableEq ι] in
theorem rankOneSkew_transpose (x y : ι → ℝ) :
    (Matrix.vecMulVec x y - Matrix.vecMulVec y x)ᵀ =
      -(Matrix.vecMulVec x y - Matrix.vecMulVec y x) := by
  simp [Matrix.transpose_vecMulVec, neg_sub]

theorem rankOneSkew_pair_nonneg (x y : ι → ℝ) (hxy : dotProduct x y = 1) :
    0 ≤ dotProduct x x * dotProduct y y - 1 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm, hxy, norm_one] at h
  rw [dotProduct_self_real, dotProduct_self_real, ← mul_pow]
  apply sub_nonneg.mpr
  have hh := pow_le_pow_left₀ zero_le_one h 2
  simpa only [one_pow] using hh

omit [DecidableEq ι] in
theorem rankOneSkew_square_diff (x y : ι → ℝ) (hxy : dotProduct x y = 1) :
    let W := Matrix.vecMulVec x y - Matrix.vecMulVec y x
    W *ᵥ (W *ᵥ (x - y)) = -(dotProduct x x * dotProduct y y - 1) • (x - y) := by
  have hyx : dotProduct y x = 1 := (dotProduct_comm y x).trans hxy
  dsimp only
  simp only [Matrix.sub_mulVec, vecMulVec_mulVec_real, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    hxy, hyx, mul_one]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Compress the rank-two skew part to a unit direction whose image is a multiple of x−y. -/
theorem rankOneSkew_exists_unit (x y : ι → ℝ) (hxy : dotProduct x y = 1)
    (hd : 0 < dotProduct x x * dotProduct y y - 1) :
    ∃ u : ι → ℝ, dotProduct u u = 1 ∧
      (Matrix.vecMulVec x y - Matrix.vecMulVec y x) *ᵥ u =
        (Real.sqrt (dotProduct x x * dotProduct y y - 1) / ‖WithLp.toLp 2 (x - y)‖) • (x - y) := by
  let d := dotProduct x x * dotProduct y y - 1
  let a := Real.sqrt d
  let v := x - y
  let m := ‖WithLp.toLp 2 v‖
  let W := Matrix.vecMulVec x y - Matrix.vecMulVec y x
  have hd0 : 0 < d := hd
  have ha : 0 < a := Real.sqrt_pos.mpr hd0
  have ha2 : a ^ 2 = d := Real.sq_sqrt hd0.le
  have hVne : v ≠ 0 := by
    intro hz
    have hEq : x = y := sub_eq_zero.mp hz
    have hxx : dotProduct x x = 1 := by simpa only [← hEq] using hxy
    rw [← hEq, hxx] at hd
    norm_num at hd
  have hm : 0 < m := norm_pos_iff.mpr (fun h ↦ hVne (congrArg WithLp.ofLp h))
  have hW2 : W *ᵥ (W *ᵥ v) = -d • v := rankOneSkew_square_diff x y hxy
  have hWtr : Wᴴ = -W := by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact rankOneSkew_transpose x y
  have hWg : (Wᴴ * W) *ᵥ v = d • v := by
    rw [hWtr, neg_mul, neg_mulVec, ← Matrix.mulVec_mulVec, hW2, neg_smul, neg_neg]
  have hWN : ‖WithLp.toLp 2 (W *ᵥ v)‖ ^ 2 = d * m ^ 2 := by
    rw [← qform_conjTranspose_mul_self, qform, hWg, star_trivial,
      dotProduct_smul, smul_eq_mul, RCLike.re_to_real, dotProduct_self_real]
  let c := -(a * m)⁻¹
  refine ⟨c • (W *ᵥ v), ?_, ?_⟩
  · rw [dotProduct_self_real]
    change ‖c • WithLp.toLp 2 (W *ᵥ v)‖ ^ 2 = 1
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hWN]
    dsimp [c]
    rw [neg_sq, inv_pow, mul_pow, ha2]
    exact inv_mul_cancel₀ (mul_ne_zero hd0.ne' (pow_ne_zero 2 hm.ne'))
  · change W *ᵥ (c • (W *ᵥ v)) = (a / m) • v
    rw [Matrix.mulVec_smul, hW2, smul_smul]
    congr 1
    dsimp [c]
    rw [neg_mul_neg, ← ha2]
    field_simp

/-- Compression of a two-block rotation to one unit vector in its second component. -/
def rotationEmbedding (c s : ℝ) (u : ι → ℝ) : Matrix (ι ⊕ ι) (ι ⊕ Unit) ℝ :=
  let U := Matrix.replicateCol Unit u
  Matrix.fromBlocks (c • 1) (-(s • U)) (s • 1) (c • U)

theorem rotationEmbedding_isometric (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (u : ι → ℝ) (hu : dotProduct u u = 1) :
    (rotationEmbedding c s u)ᴴ * rotationEmbedding c s u = 1 := by
  let U := Matrix.replicateCol Unit u
  have hUU : Uᵀ * U = 1 := by
    ext i j
    cases i
    cases j
    simpa [U, Matrix.mul_apply, dotProduct]
  have hI : (c * c) • (1 : Matrix ι ι ℝ) + (s * s) • (1 : Matrix ι ι ℝ) = 1 := by
    rw [← add_smul, ← pow_two, ← pow_two, hcs, one_smul]
  have hJ : (s * s) • (1 : Matrix Unit Unit ℝ) + (c * c) • (1 : Matrix Unit Unit ℝ) = 1 := by
    rw [add_comm, ← add_smul, ← pow_two, ← pow_two, hcs, one_smul]
  rw [conjTranspose_eq_transpose_of_trivial]
  change (Matrix.fromBlocks (c • 1) (-(s • U)) (s • 1) (c • U))ᵀ *
    Matrix.fromBlocks (c • 1) (-(s • U)) (s • 1) (c • U) = 1
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_smul,
    Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, mul_one, hUU, hI]
  simp only [Matrix.one_mul, Matrix.mul_one, smul_neg, neg_neg, smul_smul,
    mul_comm s c, neg_add_cancel, hJ, Matrix.fromBlocks_one]

omit [DecidableEq ι] in
theorem skew_scalar_compression_zero {S : Matrix ι ι ℝ}
    (hS : Sᵀ = -S) (U : Matrix ι Unit ℝ) : Uᵀ * S * U = 0 := by
  have hT : (Uᵀ * S * U)ᵀ = -(Uᵀ * S * U) := by
    simp [Matrix.transpose_mul, hS, Matrix.mul_assoc]
  ext i j
  cases i
  cases j
  have hx : (Uᵀ * S * U) () () = -(Uᵀ * S * U) () () := congrFun₂ hT () ()
  change (Uᵀ * S * U) () () = 0
  linarith

omit [DecidableEq ι] in
theorem col_eq_mulVec (A : Matrix ι ι ℝ) (u : ι → ℝ) :
    Matrix.replicateCol Unit (A *ᵥ u) = A * Matrix.replicateCol Unit u := by
  ext i j
  simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]

theorem rotationEmbedding_compress_skew {S₀ S₁ : Matrix ι ι ℝ}
    (hS₀ : S₀ᵀ = -S₀) (hS₁ : S₁ᵀ = -S₁) (c s : ℝ) (u : ι → ℝ) :
    (rotationEmbedding c s u)ᴴ * Matrix.fromBlocks S₀ 0 0 S₁ * rotationEmbedding c s u =
      skewArrow (c ^ 2 • S₀ + s ^ 2 • S₁) ((S₁ - S₀) *ᵥ u) (c * s) := by
  let U := Matrix.replicateCol Unit u
  have hU₀ := skew_scalar_compression_zero hS₀ U
  have hU₁ := skew_scalar_compression_zero hS₁ U
  have hh : (-(c * s) • (S₀ * U)) + (s * c) • (S₁ * U) =
      (c * s) • ((S₁ - S₀) * U) := by
    rw [Matrix.sub_mul, smul_sub, neg_smul, mul_comm s c]
    abel
  have hh' : -((s * c) • (Uᵀ * S₀)) + (c * s) • (Uᵀ * S₁) =
      -((c * s) • ((S₁ - S₀) * U))ᵀ := by
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_sub, hS₀, hS₁,
        sub_neg_eq_add, Matrix.mul_add, Matrix.mul_neg, smul_add, smul_neg]
    rw [mul_comm s c]
    abel
  rw [conjTranspose_eq_transpose_of_trivial]
  change (Matrix.fromBlocks (c • 1) (-(s • U)) (s • 1) (c • U))ᵀ *
    Matrix.fromBlocks S₀ 0 0 S₁ * Matrix.fromBlocks (c • 1) (-(s • U)) (s • 1) (c • U) = _
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_smul,
    Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, one_mul, mul_one, Matrix.mul_zero, add_zero,
    zero_add, ← pow_two]
  unfold skewArrow
  have col : Matrix.replicateCol Unit ((c * s) • ((S₁ - S₀) *ᵥ u)) =
      (c * s) • ((S₁ - S₀) * U) := by
    rw [← Matrix.smul_mulVec, col_eq_mulVec, Matrix.smul_mul]
  rw [col]
  congr 1
  · rw [← hh, neg_smul, mul_comm s c]
  · simpa only [Matrix.mul_one, smul_neg, smul_smul, mul_comm s c] using hh'
  · simp [hU₀, hU₁]

theorem opNorm_rotation_compress_skew_le {S₀ S₁ : Matrix ι ι ℝ}
    (hS₀ : S₀ᵀ = -S₀) (hS₁ : S₁ᵀ = -S₁) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (u : ι → ℝ) (hu : dotProduct u u = 1) :
    opNorm (skewArrow (c ^ 2 • S₀ + s ^ 2 • S₁) ((S₁ - S₀) *ᵥ u) (c * s)) ≤
      max (opNorm S₀) (opNorm S₁) := by
  rw [← rotationEmbedding_compress_skew hS₀ hS₁]
  exact (opNorm_rect_compress (rotationEmbedding_isometric c s hcs u hu) _).trans
    (opNorm_fromBlocks_diagonal_le S₀ S₁)

omit [Fintype ι] [DecidableEq ι] in
theorem skewArrow_scale_column (S : Matrix ι ι ℝ) (v : ι → ℝ) (r s : ℝ) :
    skewArrow S (r • v) s = skewArrow S v (s * r) := by
  simp only [skewArrow, smul_smul]

theorem opNorm_sq_skewArrow_interpolate [Nonempty ι] {S₀ S₁ : Matrix ι ι ℝ}
    (hS₀ : S₀ᵀ = -S₀) (hS₁ : S₁ᵀ = -S₁)
    (x y : ι → ℝ) (hxy : dotProduct x y = 1)
    (hDiff : S₁ - S₀ = Matrix.vecMulVec x y - Matrix.vecMulVec y x)
    (hV : dotProduct x x * dotProduct y y - 1 ≤ ‖WithLp.toLp 2 (x - y)‖ ^ 2)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    let d := dotProduct x x * dotProduct y y - 1
    opNorm (skewArrow ((1 - t) • S₀ + t • S₁) (x - y) (Real.sqrt (t * (1 - t)))) ^ 2 ≤
      max (opNorm S₀) (opNorm S₁) ^ 2 + t * (1 - t) * (‖WithLp.toLp 2 (x - y)‖ ^ 2 - d) := by
  let d := dotProduct x x * dotProduct y y - 1
  let v := x - y
  let m := ‖WithLp.toLp 2 v‖
  let c := Real.sqrt (1 - t)
  let s := Real.sqrt t
  let R := Real.sqrt (t * (1 - t))
  let M := (1 - t) • S₀ + t • S₁
  let K := max (opNorm S₀) (opNorm S₁)
  have hdn : 0 ≤ d := rankOneSkew_pair_nonneg x y hxy
  have hmn : 0 ≤ m := norm_nonneg _
  have hRn : 0 ≤ R := Real.sqrt_nonneg _
  have hc : c ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht')
  have hs : s ^ 2 = t := Real.sq_sqrt ht
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hc, hs]; ring
  have hR : R ^ 2 = t * (1 - t) := Real.sq_sqrt (mul_nonneg ht (sub_nonneg.mpr ht'))
  have hR' : c * s = R := by
    dsimp only [R, c, s]
    rw [mul_comm t (1 - t), Real.sqrt_mul (sub_nonneg.mpr ht')]
  have hM : Mᵀ = -M := by
    dsimp only [M]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, hS₀, hS₁, smul_neg, neg_add]
  change opNorm (skewArrow M v R) ^ 2 ≤ K ^ 2 + t * (1 - t) * (m ^ 2 - d)
  by_cases hd : d = 0
  · have hMn : opNorm M ≤ K := by
      dsimp only [M]
      apply (opNorm_add_le_real _ _).trans
      rw [opNorm_smul_real, opNorm_smul_real, abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht')]
      calc
        _ ≤ (1 - t) * K + t * K :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht'))
            (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)
        _ = _ := by ring
    have hZero : opNorm (skewArrow M v 0) ≤ K := by
      have hform : skewArrow M v 0 = Matrix.fromBlocks M 0 0 (0 : Matrix Unit Unit ℝ) := by
        ext i j
        cases i <;> cases j <;> simp [skewArrow]
      rw [hform]
      have h := opNorm_fromBlocks_diagonal_le M (0 : Matrix Unit Unit ℝ)
      have hz : opNorm (0 : Matrix Unit Unit ℝ) = 0 := by
        rw [opNorm_square_eq, map_zero, norm_zero]
      rw [hz, max_eq_left (show 0 ≤ opNorm M from norm_nonneg _)] at h
      exact h.trans hMn
    have hI := opNorm_sq_skewArrow_increment hM v (le_refl 0) hRn
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, hR] at hI
    rw [hd, sub_zero]
    exact hI.trans (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hZero 2) le_rfl)
  · have hd' : 0 < d := lt_of_le_of_ne hdn (Ne.symm hd)
    have hm : 0 < m := by
      have hm2 : 0 < m ^ 2 := hd'.trans_le hV
      exact lt_of_le_of_ne hmn (Ne.symm (fun h ↦ by rw [h] at hm2; norm_num at hm2))
    let a := Real.sqrt d
    have han : 0 ≤ a := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = d := Real.sq_sqrt hdn
    have ha : a ≤ m := (sq_le_sq₀ han hmn).mp (ha2.symm ▸ hV)
    obtain ⟨u, hu, hwu⟩ := rankOneSkew_exists_unit x y hxy hd'
    have hu' : (S₁ - S₀) *ᵥ u = (a / m) • v := hDiff.symm ▸ hwu
    let r := R * (a / m)
    have hr : 0 ≤ r := mul_nonneg hRn (div_nonneg han hmn)
    have hrR : r ≤ R := by
      have h : a / m ≤ 1 := (div_le_iff₀ hm).mpr (by simpa only [one_mul] using ha)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h hRn
    have hSmall := opNorm_rotation_compress_skew_le hS₀ hS₁ c s hcs u hu
    rw [hc, hs, hu', hR', skewArrow_scale_column] at hSmall
    have hSmall' : opNorm (skewArrow M v r) ≤ K := hSmall
    have hInc := opNorm_sq_skewArrow_increment hM v hr hrR
    have hres : (R ^ 2 - r ^ 2) * m ^ 2 = t * (1 - t) * (m ^ 2 - d) := by
      dsimp only [r]
      rw [mul_pow, div_pow, ha2]
      rw [← hR]
      field_simp [hm.ne']
    rw [hres] at hInc
    exact hInc.trans (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hSmall' 2) le_rfl)

/-- A coordinate prefix in the two-dimensional block of the fiber projection. -/
def partialRowProjection (P : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  let s := Real.sqrt (t * (1 - t))
  Matrix.fromBlocks (P + t • Matrix.vecMulVec x y)
    (s • Matrix.replicateCol Unit x) (s • (Matrix.replicateCol Unit y)ᵀ)
    ((1 - t) • (1 : Matrix Unit Unit ℝ))

omit [DecidableEq ι] in
private theorem partialRowAux {P : Matrix ι ι ℝ} {x y : ι → ℝ}
    (hPx : P *ᵥ x = 0) (hyP : y ᵥ* P = 0) (hxy : dotProduct y x = 1) :
    let X := Matrix.replicateCol Unit x
    let Y := (Matrix.replicateCol Unit y)ᵀ
    P * X = 0 ∧ Y * P = 0 ∧ Y * X = 1 ∧ X * Y = Matrix.vecMulVec x y := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    have h := congrFun hPx i
    simpa only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.zero_apply,
      Matrix.mulVec, dotProduct, Pi.zero_apply] using h
  · ext i j
    have h := congrFun hyP j
    simpa only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.transpose_apply, Matrix.zero_apply,
      Matrix.vecMul, dotProduct, Pi.zero_apply] using h
  · ext i j
    cases i
    cases j
    simpa [Matrix.mul_apply, dotProduct] using hxy
  · ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]

omit [DecidableEq ι] in
theorem partialRowProjection_idempotent {P : Matrix ι ι ℝ} (hP : IsIdempotentElem P)
    {x y : ι → ℝ} (hPx : P *ᵥ x = 0) (hyP : y ᵥ* P = 0) (hxy : dotProduct y x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) : IsIdempotentElem (partialRowProjection P x y t) := by
  let X := Matrix.replicateCol Unit x
  let Y := (Matrix.replicateCol Unit y)ᵀ
  let R := X * Y
  let s := Real.sqrt (t * (1 - t))
  obtain ⟨hPX, hYP, hYX, hXY⟩ := partialRowAux hPx hyP hxy
  change P * X = 0 at hPX
  change Y * P = 0 at hYP
  change Y * X = 1 at hYX
  change R = Matrix.vecMulVec x y at hXY
  have hPR : P * R = 0 := by
    dsimp [R]
    rw [← Matrix.mul_assoc, hPX, Matrix.zero_mul]
  have hRP : R * P = 0 := by
    dsimp [R]
    rw [Matrix.mul_assoc, hYP, Matrix.mul_zero]
  have hRX : R * X = X := by
    dsimp [R]
    rw [Matrix.mul_assoc, hYX, Matrix.mul_one]
  have hYR : Y * R = Y := by
    dsimp [R]
    rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have hRR : R * R = R := by
    change R * (X * Y) = _
    rw [← Matrix.mul_assoc, hRX]
  have hss : s ^ 2 = t * (1 - t) := Real.sq_sqrt (mul_nonneg ht (sub_nonneg.mpr ht'))
  have htl : t * t + s * s = t := by nlinarith only [hss]
  have htr : t * s + s * (1 - t) = s := by ring
  have hbl : s * t + (1 - t) * s = s := by ring
  have hbr : s * s + (1 - t) * (1 - t) = 1 - t := by nlinarith only [hss]
  have hf : partialRowProjection P x y t =
      Matrix.fromBlocks (P + t • R) (s • X) (s • Y) ((1 - t) • (1 : Matrix Unit Unit ℝ)) := by
    rw [hXY]
    rfl
  show _ * _ = _
  rw [hf, Matrix.fromBlocks_multiply]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, hP.eq, hPR, hRP, hPX, hYP, hRX, hYR, hRR, hYX,
    show X * Y = R from rfl, smul_zero, add_zero, zero_add]
  simp only [← add_smul, htl, htr, hbl, hbr, add_assoc]

omit [DecidableEq ι] in
theorem partialRowProjection_ne_zero {P : Matrix ι ι ℝ} {x y : ι → ℝ}
    (hPx : P *ᵥ x = 0) (hxy : dotProduct y x = 1) {t : ℝ} (_ht : t ≤ 1) :
    partialRowProjection P x y t ≠ 0 := by
  intro hh
  have hre : 1 - t = 0 := by
    have h := congrFun₂ hh (Sum.inr ()) (Sum.inr ())
    simpa [partialRowProjection, smul_eq_mul] using h
  have ht1 : t = 1 := by linarith
  have htop : P + Matrix.vecMulVec x y = 0 := by
    ext i j
    have h := congrFun₂ hh (Sum.inl i) (Sum.inl j)
    simpa [partialRowProjection, ht1] using h
  have hz : (P + Matrix.vecMulVec x y) *ᵥ x = 0 := by rw [htop, Matrix.zero_mulVec]
  rw [Matrix.add_mulVec, hPx, vecMulVec_mulVec_real, hxy, one_smul, zero_add] at hz
  rw [hz, dotProduct_zero] at hxy
  norm_num at hxy

omit [Fintype ι] [DecidableEq ι] in
theorem partialRowProjection_skew (P : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ) :
    partialRowProjection P x y t - (partialRowProjection P x y t)ᵀ =
      skewArrow (P - Pᵀ + t • (Matrix.vecMulVec x y - Matrix.vecMulVec y x))
        (x - y) (Real.sqrt (t * (1 - t))) := by
  have htl : P + t • Matrix.vecMulVec x y - (Pᵀ + t • Matrix.vecMulVec y x) =
      P - Pᵀ + t • (Matrix.vecMulVec x y - Matrix.vecMulVec y x) := by
    rw [smul_sub]
    abel
  ext i j
  cases i <;> cases j <;>
    simp [partialRowProjection, skewArrow, Matrix.vecMulVec_apply, smul_eq_mul, mul_sub] ; ring

theorem opNorm_sq_idempotent_matrix (P : Matrix ι ι ℝ) (hP : IsIdempotentElem P) (hP0 : P ≠ 0) :
    opNorm P ^ 2 = 1 + opNorm (P - Pᵀ) ^ 2 := by
  let f := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)
  have hp : IsIdempotentElem (f P) := by
    change f P * f P = f P
    rw [← map_mul, hP.eq]
  have hz : f P ≠ 0 := fun hz ↦ hP0 (f.injective (hz.trans (map_zero f).symm))
  have heq := norm_sq_idempotent_eq_one_add_skew_sq (f P) hp hz
  change ‖f P‖ ^ 2 = 1 + ‖f (P - Pᵀ)‖ ^ 2
  rw [map_sub, ← conjTranspose_eq_transpose_of_trivial]
  change ‖f P‖ ^ 2 = 1 + ‖f P - f (star P)‖ ^ 2
  rw [map_star, star_eq_adjoint]
  exact heq

omit [DecidableEq ι] in
theorem row_extended_idempotent {P : Matrix ι ι ℝ} (hP : IsIdempotentElem P)
    {x y : ι → ℝ} (hPx : P *ᵥ x = 0) (hyP : y ᵥ* P = 0) (hxy : dotProduct y x = 1) :
    IsIdempotentElem (P + Matrix.vecMulVec x y) := by
  let R := Matrix.vecMulVec x y
  have hPR : P * R = 0 := by
    dsimp [R]
    rw [Matrix.mul_vecMulVec, hPx]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have hRP : R * P = 0 := by
    dsimp [R]
    rw [Matrix.vecMulVec_mul, hyP]
    ext i j
    simp [Matrix.vecMulVec_apply]
  have hRR : R * R = R := by
    dsimp [R]
    rw [Matrix.mul_vecMulVec, vecMulVec_mulVec_real, hxy, one_smul]
  show (P + R) * (P + R) = P + R
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP.eq, hPR, hRP, hRR, add_zero, zero_add]

theorem idempotent_skew_add_one_le (P : Matrix ι ι ℝ) (hP : IsIdempotentElem P) :
    1 + opNorm (P - Pᵀ) ^ 2 ≤ max 1 (opNorm P ^ 2) := by
  by_cases h0 : P = 0
  · simp [h0, opNorm_square_eq]
  · rw [← opNorm_sq_idempotent_matrix P hP h0]
    exact le_max_right _ _

/-- Dimension-independent row cut interpolation, including the empty earlier prefix. -/
theorem partialRowProjection_norm_sq_le [Nonempty ι]
    {P : Matrix ι ι ℝ} (hP : IsIdempotentElem P)
    {x y : ι → ℝ} (hPx : P *ᵥ x = 0) (hyP : y ᵥ* P = 0) (hxy : dotProduct y x = 1)
    (hx : dotProduct x x ≤ 1) (hy : 1 ≤ dotProduct y y)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    opNorm (partialRowProjection P x y t) ^ 2 ≤
      max 1 (max (opNorm P ^ 2) (opNorm (P + Matrix.vecMulVec x y) ^ 2)) +
        t * (1 - t) * (1 - dotProduct x x) * (dotProduct y y - 1) := by
  let P' := P + Matrix.vecMulVec x y
  let S := P - Pᵀ
  let S' := P' - P'ᵀ
  let W := Matrix.vecMulVec x y - Matrix.vecMulVec y x
  have hP' : IsIdempotentElem P' := row_extended_idempotent hP hPx hyP hxy
  have hS : Sᵀ = -S := by simp [S, Matrix.transpose_sub, neg_sub]
  have hS' : S'ᵀ = -S' := by simp [S', Matrix.transpose_sub, neg_sub]
  have hDef : S' = S + W := by
    dsimp only [S', P', S, W]
    rw [Matrix.transpose_add, Matrix.transpose_vecMulVec]
    abel
  have hDiff : S' - S = W := by rw [hDef, add_sub_cancel_left]
  have hyx : dotProduct x y = 1 := (dotProduct_comm x y).trans hxy
  have hgap : ‖WithLp.toLp 2 (x - y)‖ ^ 2 - (dotProduct x x * dotProduct y y - 1) =
      (1 - dotProduct x x) * (dotProduct y y - 1) := by
    rw [← dotProduct_self_real, dotProduct_sub, sub_dotProduct, sub_dotProduct, hxy, hyx]
    ring
  have hV :
      dotProduct x x * dotProduct y y - 1 ≤ ‖WithLp.toLp 2 (x - y)‖ ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
    linarith only [hgap, hh]
  have hI := opNorm_sq_skewArrow_interpolate hS hS' x y hyx hDiff hV ht ht'
  dsimp only at hI
  rw [hgap] at hI
  have hcomb : (1 - t) • S + t • S' = S + t • W := by
    rw [hDef, smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [hcomb] at hI
  rw [opNorm_sq_idempotent_matrix _ (partialRowProjection_idempotent hP hPx hyP hxy ht ht')
    (partialRowProjection_ne_zero hPx hxy ht'), partialRowProjection_skew]
  change 1 + opNorm (skewArrow (S + t • W) (x - y) (Real.sqrt (t * (1 - t)))) ^ 2 ≤ _
  have hA := idempotent_skew_add_one_le P hP
  have hA' := idempotent_skew_add_one_le P' hP'
  have hC : 1 + max (opNorm S) (opNorm S') ^ 2 ≤
      max 1 (max (opNorm P ^ 2) (opNorm P' ^ 2)) := by
    rcases le_total (opNorm S) (opNorm S') with h | h
    · rw [max_eq_right h]
      exact hA'.trans (max_le_max_left _ (le_max_right _ _))
    · rw [max_eq_left h]
      exact hA.trans (max_le_max_left _ (le_max_left _ _))
  change 1 + opNorm (skewArrow (S + t • W) (x - y) (Real.sqrt (t * (1 - t)))) ^ 2 ≤
    max 1 (max (opNorm P ^ 2) (opNorm P' ^ 2)) +
      t * (1 - t) * (1 - dotProduct x x) * (dotProduct y y - 1)
  linarith only [hI, hC]

section RowGram

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Earlier full columns and one column in the two-dimensional row plane. -/
def partialRowColumns (U : Matrix ι κ ℝ) (x : ι → ℝ) (t : ℝ) :
    Matrix (ι ⊕ Unit) (κ ⊕ Unit) ℝ :=
  Matrix.fromBlocks U (Real.sqrt t • Matrix.replicateCol Unit x) 0
    (Real.sqrt (1 - t) • (1 : Matrix Unit Unit ℝ))

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem partialRowColumns_bilinear (U V : Matrix ι κ ℝ) (x y : ι → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (partialRowColumns U x t)ᵀ * partialRowColumns V y t =
      Matrix.fromBlocks (Uᵀ * V) (Real.sqrt t • (Uᵀ * Matrix.replicateCol Unit y))
        (Real.sqrt t • ((Matrix.replicateCol Unit x)ᵀ * V))
        ((1 - t + t * dotProduct x y) • (1 : Matrix Unit Unit ℝ)) := by
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have hs' : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t :=
    Real.mul_self_sqrt (sub_nonneg.mpr ht')
  have hp : (Matrix.replicateCol Unit x)ᵀ * Matrix.replicateCol Unit y =
      dotProduct x y • (1 : Matrix Unit Unit ℝ) := by
    ext i j
    cases i
    cases j
    simp [Matrix.mul_apply, dotProduct, smul_eq_mul]
  simp only [partialRowColumns, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_zero, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    smul_zero, add_zero, hp, hs']
  congr 1
  rw [← mul_assoc, hs, ← add_smul, add_comm]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem partialRowColumns_comp (U V : Matrix ι κ ℝ) (x y : ι → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    partialRowColumns U x t * (partialRowColumns V y t)ᵀ =
      partialRowProjection (U * Vᵀ) x y t := by
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have hs' : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t :=
    Real.mul_self_sqrt (sub_nonneg.mpr ht')
  have hw : Real.sqrt t * Real.sqrt (1 - t) = Real.sqrt (t * (1 - t)) :=
    (Real.sqrt_mul ht _).symm
  have hp : Matrix.replicateCol Unit x * (Matrix.replicateCol Unit y)ᵀ = Matrix.vecMulVec x y := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  simp only [partialRowColumns, partialRowProjection, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, zero_add, hp, hs, hs', hw,
    show Real.sqrt (1 - t) * Real.sqrt t = Real.sqrt (t * (1 - t)) from (mul_comm _ _).trans hw]

omit [DecidableEq ι] [Fintype κ] in
theorem partialRowColumns_biorthogonal (U V : Matrix ι κ ℝ) (x y : ι → ℝ)
    (hUV : Vᵀ * U = 1) (hx : Vᵀ * Matrix.replicateCol Unit x = 0)
    (hy : (Matrix.replicateCol Unit y)ᵀ * U = 0) (hxy : dotProduct y x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (partialRowColumns V y t)ᵀ * partialRowColumns U x t = 1 := by
  rw [partialRowColumns_bilinear _ _ _ _ ht ht', hUV, hx, hy, hxy]
  simp [sub_add_cancel]

omit [DecidableEq ι] in
theorem partialRowColumns_posDef (U V : Matrix ι κ ℝ) (x y : ι → ℝ)
    (hUV : Vᵀ * U = 1) (hx : Vᵀ * Matrix.replicateCol Unit x = 0)
    (hy : (Matrix.replicateCol Unit y)ᵀ * U = 0) (hxy : dotProduct y x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ((partialRowColumns U x t)ᴴ * partialRowColumns U x t).PosDef := by
  have hb := partialRowColumns_biorthogonal U V x y hUV hx hy hxy ht ht'
  apply Matrix.PosDef.conjTranspose_mul_self
  intro c d h
  have h' := congrArg ((partialRowColumns V y t)ᵀ *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec] using h'

/-- Two-Gram expression for the norm of a partial row projection. -/
theorem partialRowProjection_norm_sq_gram (U V : Matrix ι κ ℝ) (x y : ι → ℝ)
    (hUV : Vᵀ * U = 1) (hx : Vᵀ * Matrix.replicateCol Unit x = 0)
    (hy : (Matrix.replicateCol Unit y)ᵀ * U = 0) (hxy : dotProduct y x = 1)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    let C := (partialRowColumns U x t)ᵀ * partialRowColumns U x t
    let D := (partialRowColumns V y t)ᵀ * partialRowColumns V y t
    opNorm (partialRowProjection (U * Vᵀ) x y t) ^ 2 =
      opNorm (CFC.sqrt C * D * CFC.sqrt C) := by
  dsimp only
  rw [← partialRowColumns_comp _ _ _ _ ht ht']
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    (opNorm_sq_rectGram_dual (partialRowColumns U x t) (partialRowColumns V y t)
      (partialRowColumns_posDef U V x y hUV hx hy hxy ht ht'))

end RowGram

/-- Squared norm of the coefficient cut in the indicated positive metric.
The value 1 bounds the empty cut, as used in the interpolation bound. -/
def gramPrefixNormSq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  max 1 (opNorm (CFC.sqrt B * prefixMask ℝ k * (CFC.sqrt B)⁻¹) ^ 2)

theorem gramPrefixNormSq_le_of_pb {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hB : B.PosDef) (hK : 1 ≤ K) (h : PB B K) {k : ℕ} (hk : k ≤ n) :
    gramPrefixNormSq B k ≤ K ^ 2 := by
  unfold gramPrefixNormSq
  refine max_le (by nlinarith) ?_
  have hle := (metric_opNorm_le_iff hB (prefixMask ℝ k) h.1).mpr (fun c ↦ by
    rw [prefixMask_mulVec]
    exact h.2 k hk c)
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

section GramRowSlice

variable {n : ℕ}

private theorem dot_single_one_self (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    dotProduct (Pi.single j 1) (M *ᵥ Pi.single j 1) = M j j := by simp

theorem prefixMask_succ_real (j : Fin n) :
    prefixMask (n := n) ℝ (j.val + 1) =
      prefixMask ℝ j.val + Matrix.vecMulVec (Pi.single j 1) (Pi.single j 1) := by
  ext i k
  by_cases h : i = k
  · subst k
    by_cases hij : i = j
    · subst i
      simp [prefixMask, Matrix.vecMulVec_apply]
    · have hlt : i ≤ j ↔ i < j := ⟨fun h ↦ lt_of_le_of_ne h hij, le_of_lt⟩
      simp [prefixMask, Matrix.vecMulVec_apply, hij, hlt]
  · by_cases hij : i = j
    · subst i
      simp [prefixMask, Matrix.vecMulVec_apply, h, Ne.symm h]
    · simp [prefixMask, Matrix.vecMulVec_apply, h, hij]

/-- Partial-row projection of the metric root of B, on one interacting two-dimensional plane. -/
def gramRowSlice (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (t : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  let R := CFC.sqrt B
  let Q := R⁻¹
  let e : Fin n → ℝ := Pi.single j 1
  partialRowProjection (R * prefixMask ℝ j.val * Q) (R *ᵥ e) (Q *ᵥ e) t

theorem gramRowSlice_norm_sq_le {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) (hB₁ : B ≤ 1) (j : Fin n) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    opNorm (gramRowSlice B j t) ^ 2 ≤
      max (gramPrefixNormSq B j.val) (gramPrefixNormSq B (j.val + 1)) +
        t * (1 - t) * (1 - B j j) * (B⁻¹ j j - 1) := by
  let _ : Nonempty (Fin n) := ⟨j⟩
  let R := CFC.sqrt B
  let Q := R⁻¹
  let e : Fin n → ℝ := Pi.single j 1
  let F := prefixMask (n := n) ℝ j.val
  let P := R * F * Q
  let x := R *ᵥ e
  let y := Q *ᵥ e
  have hR := posDef_sqrt hB
  have hr : Rᵀ = R := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hR.isHermitian.eq
  have hq : Qᵀ = Q := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hR.inv.isHermitian.eq
  have hIu := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hQR : Q * R = 1 := Matrix.nonsing_inv_mul R hIu
  have hRQ : R * Q = 1 := Matrix.mul_nonsing_inv R hIu
  have hF0 : F *ᵥ e = 0 := by
    rw [show F *ᵥ e = truncCoeff j.val e from prefixMask_mulVec j.val e]
    funext i
    by_cases hi : i = j <;> simp [e, truncCoeff, hi]
  have hVec (A : Matrix (Fin n) (Fin n) ℝ) (h : Aᵀ = A) : e ᵥ* A = A *ᵥ e := by
    simpa only [h] using Matrix.vecMul_transpose A e
  have hE0 : e ᵥ* F = 0 := by
    have hf : Fᵀ = F := by
      rw [← conjTranspose_eq_transpose_of_trivial]
      exact prefixMask_isHermitian j.val
    rw [hVec F hf]
    exact hF0
  have hP : IsIdempotentElem P := by
    change (R * F * Q) * (R * F * Q) = _
    rw [show (R * F * Q) * (R * F * Q) = R * F * (Q * R) * F * Q by simp only [Matrix.mul_assoc],
      hQR, Matrix.mul_one, Matrix.mul_assoc _ F F, (prefixMask_isIdempotent (𝕜 := ℝ) (n := n) j.val).eq]
  have hPx : P *ᵥ x = 0 := by
    change (R * F * Q) *ᵥ (R *ᵥ e) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ Q R, hQR, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hF0, Matrix.mulVec_zero]
  have hyP : y ᵥ* P = 0 := by
    change (Q *ᵥ e) ᵥ* (R * F * Q) = 0
    rw [← hVec _ hq, Matrix.vecMul_vecMul, ← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q,
      hQR, Matrix.one_mul, ← Matrix.vecMul_vecMul, hE0, Matrix.zero_vecMul]
  have hxy : dotProduct y x = 1 := by
    change dotProduct (Q *ᵥ e) (R *ᵥ e) = 1
    rw [Matrix.dotProduct_mulVec, ← hVec _ hq, Matrix.vecMul_vecMul, hQR, Matrix.vecMul_one]
    simp [e]
  have hxx : dotProduct x x = B j j := by
    change dotProduct (R *ᵥ e) (R *ᵥ e) = _
    rw [Matrix.dotProduct_mulVec, ← hVec _ hr, Matrix.vecMul_vecMul,
      sqrt_mul_sqrt_of_posDef hB, ← Matrix.dotProduct_mulVec]
    exact dot_single_one_self B j
  have hyy : dotProduct y y = B⁻¹ j j := by
    have hQ2 : Q * Q = B⁻¹ := by
      change R⁻¹ * R⁻¹ = B⁻¹
      rw [← Matrix.mul_inv_rev, sqrt_mul_sqrt_of_posDef hB]
    change dotProduct (Q *ᵥ e) (Q *ᵥ e) = _
    rw [Matrix.dotProduct_mulVec, ← hVec _ hq, Matrix.vecMul_vecMul,
      hQ2, ← Matrix.dotProduct_mulVec]
    exact dot_single_one_self B⁻¹ j
  have hx : dotProduct x x ≤ 1 := by
    rw [hxx]
    have hdr := qform_mono hB₁ e
    simpa [qform, e] using hdr
  have hy : 1 ≤ dotProduct y y := by
    rw [hyy]
    have hi := matrix_inv_le_inv hB hB₁
    rw [inv_one] at hi
    have hdr := qform_mono hi e
    simpa [qform, e] using hdr
  have hNext : P + Matrix.vecMulVec x y = R * prefixMask ℝ (j.val + 1) * Q := by
    rw [prefixMask_succ_real, Matrix.mul_add, Matrix.add_mul]
    congr 1
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    exact congrArg (Matrix.vecMulVec x) (hVec _ hq).symm
  have hh := partialRowProjection_norm_sq_le hP hPx hyP hxy hx hy ht ht'
  rw [hxx, hyy, hNext] at hh
  change opNorm (gramRowSlice B j t) ^ 2 ≤ _
  refine hh.trans ?_
  have hmax :
      max 1 (max (opNorm P ^ 2) (opNorm (R * prefixMask ℝ (j.val + 1) * Q) ^ 2)) =
        max (gramPrefixNormSq B j.val) (gramPrefixNormSq B (j.val + 1)) := by
    dsimp only [gramPrefixNormSq, P, F, R, Q]
    conv_rhs => rw [max_assoc, max_left_comm _ 1, ← max_assoc 1 1, max_self]
  rw [hmax]

end GramRowSlice

end SchauderBasisOrbits
