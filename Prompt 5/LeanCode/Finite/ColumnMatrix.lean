import LeanCode.Finite.Families

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

noncomputable section
namespace SchauderBasisOrbits

variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem mulVec_blockDiagonal_component (G : κ → Matrix ι ι 𝕜) (x : ι × κ → 𝕜)
    (i : ι) (j : κ) :
    (Matrix.blockDiagonal G *ᵥ x) (i,j) = (G j *ᵥ fun i' ↦ x (i',j)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, ite_mul]

omit [DecidableEq ι] in
theorem qform_blockDiagonal_component (G : κ → Matrix ι ι 𝕜) (x : ι × κ → 𝕜) :
    qform (Matrix.blockDiagonal G) x = ∑ j, qform (G j) (fun i ↦ x (i,j)) := by
  simp only [qform, dotProduct, Fintype.sum_prod_type, mulVec_blockDiagonal_component, Pi.star_apply]
  rw [Finset.sum_comm, map_sum]

omit [DecidableEq ι] in
theorem posSemidef_blockDiagonal_of {G : κ → Matrix ι ι 𝕜} (h : ∀ j, (G j).PosSemidef) :
    (Matrix.blockDiagonal G).PosSemidef := by
  apply posSemidef_of_qform_nonneg
  · unfold Matrix.IsHermitian
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    exact funext (fun j ↦ (h j).isHermitian.eq)
  · intro x
    rw [qform_blockDiagonal_component]
    exact Finset.sum_nonneg (fun j _ ↦ qform_nonneg (h j) _)

omit [DecidableEq ι] in
theorem posDef_blockDiagonal_of {G : κ → Matrix ι ι 𝕜} (h : ∀ j, (G j).PosDef) :
    (Matrix.blockDiagonal G).PosDef := by
  refine posDef_of_qform_pos (posSemidef_blockDiagonal_of (fun j ↦ (h j).posSemidef)).isHermitian ?_
  intro x hx
  obtain ⟨⟨i, j⟩, hij⟩ : ∃ p, x p ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  have hne : (fun i' ↦ x (i',j)) ≠ 0 := fun h ↦ hij (congrFun h i)
  rw [qform_blockDiagonal_component]
  exact (qform_pos (h j) hne).trans_le (Finset.single_le_sum
    (fun j' _ ↦ qform_nonneg (h j').posSemidef _) (Finset.mem_univ j))

omit [DecidableEq ι] in
theorem blockDiagonal_le_of {G H : κ → Matrix ι ι 𝕜} (h : ∀ j, G j ≤ H j) :
    Matrix.blockDiagonal G ≤ Matrix.blockDiagonal H := by
  apply Matrix.le_iff.mpr
  rw [← Matrix.blockDiagonal_sub]
  exact posSemidef_blockDiagonal_of (fun j ↦ Matrix.le_iff.mp (h j))

theorem columnTensorChange_isUnit (E : Matrix ι ι 𝕜) (hE : IsUnit E) :
    IsUnit (columnTensorChange E (σ := κ)) := by
  have hi : columnTensorChange E (σ := κ) * columnTensorChange E⁻¹ = 1 := by
    unfold columnTensorChange
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det E).mp hE), Matrix.one_kronecker_one]
  have hh := congrArg Matrix.det hi
  rw [Matrix.det_mul, Matrix.det_one] at hh
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  refine isUnit_iff_ne_zero.mpr fun hz ↦ ?_
  rw [hz, zero_mul] at hh
  exact zero_ne_one hh

theorem matrix_congruence_le_iff {A B E : Matrix ι ι 𝕜} (hE : IsUnit E) :
    Eᴴ * A * E ≤ Eᴴ * B * E ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact hE.posSemidef_star_left_conjugate_iff

variable {n : ℕ}

/-- Mask that keeps all rows of an initial column segment. -/
def completedColumnMask (𝕜 ι : Type*) [Zero 𝕜] [One 𝕜] [DecidableEq ι]
    (n k : ℕ) : Matrix (Fin n × ι) (Fin n × ι) 𝕜 :=
  Matrix.blockDiagonal (fun _ : ι ↦ prefixMask (n := n) 𝕜 k)

omit [Fintype ι] in
theorem completedColumnMask_eq_tensor (k : ℕ) :
    completedColumnMask 𝕜 ι n k = prefixMask 𝕜 k ⊗ₖ (1 : Matrix ι ι 𝕜) := by
  ext ⟨c,i⟩ ⟨d,j⟩
  by_cases h : i = j <;> simp [completedColumnMask, Matrix.blockDiagonal_apply, h]

theorem completedColumnMask_commute (E : Matrix ι ι 𝕜) (k : ℕ) :
    Commute (completedColumnMask 𝕜 ι n k) (columnTensorChange E) := by
  change completedColumnMask 𝕜 ι n k * columnTensorChange E =
    columnTensorChange E * completedColumnMask 𝕜 ι n k
  rw [completedColumnMask_eq_tensor, columnTensorChange,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

omit [Fintype ι] [DecidableEq ι] in
private theorem columnTensorChange_conjTranspose (E : Matrix ι ι 𝕜) :
    (columnTensorChange E : Matrix (Fin n × ι) (Fin n × ι) 𝕜)ᴴ = columnTensorChange Eᴴ := by
  simp only [columnTensorChange, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

omit [Fintype ι] in
/-- Whitened column Gram breaks up into one scalar Gram mixture for each row eigenvalue. -/
theorem columnTensorGram_diagonal (B : Matrix (Fin n) (Fin n) 𝕜) (β : ι → ℝ) :
    columnTensorGram (Matrix.diagonal (fun i ↦ (β i : 𝕜))) (1 : Matrix ι ι 𝕜) B =
      Matrix.blockDiagonal (fun i ↦ β i • (1 : Matrix (Fin n) (Fin n) 𝕜) + (1 - β i) • B) := by
  ext ⟨k,i⟩ ⟨l,j⟩
  by_cases h : i = j
  · subst j
    simp only [columnTensorGram, Matrix.blockDiagonal_apply_eq, Matrix.add_apply, Matrix.kronecker_apply,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.sub_apply,
      Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_sub, RCLike.ofReal_one]
    ring
  · simp [columnTensorGram, Matrix.blockDiagonal_apply, Matrix.one_apply, h]

theorem PB.one {K : ℝ} (hK : 1 ≤ K) : PB (1 : Matrix (Fin n) (Fin n) 𝕜) K := by
  refine ⟨zero_le_one.trans hK, fun k _ c ↦ ?_⟩
  have h : qform (1 : Matrix (Fin n) (Fin n) 𝕜) (truncCoeff k c) ≤ qform 1 c := by
    simp only [qform_one, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : i.val < k <;> simp [truncCoeff, hi]
  exact h.trans (by
    calc
      _ = (1 : ℝ) * qform (1 : Matrix (Fin n) (Fin n) 𝕜) c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (by simp))

set_option maxHeartbeats 800000 in
/-- SC06: positive augmented Gram and prefix control for completed columns. -/
theorem columnTensorGram_completed_prefix {A Ω : Matrix ι ι 𝕜} {B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) (hΩ : Ω.PosDef) (hAΩ : A ≤ Ω) (hB : B.PosDef)
    {K : ℝ} (hK : 1 ≤ K) (hPB : PB B K) :
    let H := columnTensorGram A Ω B
    H.PosDef ∧ ∀ k ≤ n, completedColumnMask 𝕜 ι n k * H * completedColumnMask 𝕜 ι n k ≤ K ^ 2 • H := by
  let H := columnTensorGram A Ω B
  obtain ⟨E, β, hE, hEΩ, hEA, hβ⟩ := matrix_whitening_eigenbasis hΩ hA hAΩ
  let Z := columnTensorChange E (σ := Fin n)
  have hZu : IsUnit Z := columnTensorChange_isUnit E hE
  let G := fun i ↦ β i • (1 : Matrix (Fin n) (Fin n) 𝕜) + (1 - β i) • B
  have hZHZ : Zᴴ * H * Z = Matrix.blockDiagonal G := by
    change (columnTensorChange E)ᴴ * columnTensorGram A Ω B * columnTensorChange E = _
    rw [columnTensorGram_congruence, hEΩ, hEA, columnTensorGram_diagonal]
  have hGp (i : ι) : (G i).PosDef :=
    posDef_convex_combination Matrix.PosDef.one hB (hβ i).1.le (hβ i).2
  constructor
  · apply hZu.posDef_star_left_conjugate_iff.mp
    change (Zᴴ * H * Z).PosDef
    rw [hZHZ]
    exact posDef_blockDiagonal_of hGp
  · intro k hk
    let J := completedColumnMask 𝕜 ι n k
    let F := prefixMask (n := n) 𝕜 k
    have hGcuts (i : ι) : F * G i * F ≤ K ^ 2 • G i := by
      have pb : PB (G i) K := PB.add_smul (PB.one hK) hPB (hβ i).1.le (sub_nonneg.mpr (hβ i).2)
      exact ((pb_iff_matrix_le (hGp i).isHermitian K).mp pb).2 k hk
    have hWhitened : J * Matrix.blockDiagonal G * J ≤ K ^ 2 • Matrix.blockDiagonal G := by
      change Matrix.blockDiagonal (fun _ : ι ↦ F) * Matrix.blockDiagonal G *
        Matrix.blockDiagonal (fun _ : ι ↦ F) ≤ _
      rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_smul]
      exact blockDiagonal_le_of hGcuts
    have hJZ : J * Z = Z * J := (completedColumnMask_commute E k).eq
    have hJZ' : Zᴴ * J = J * Zᴴ := by
      change (columnTensorChange E)ᴴ * J = J * (columnTensorChange E)ᴴ
      rw [columnTensorChange_conjTranspose]
      exact (completedColumnMask_commute Eᴴ k).eq.symm
    apply (matrix_congruence_le_iff hZu).mp
    have hTrans : Zᴴ * (J * H * J) * Z = J * (Zᴴ * H * Z) * J := calc
      _ = (Zᴴ * J) * H * (J * Z) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJZ, hJZ']; simp only [Matrix.mul_assoc]
    rw [hTrans, Matrix.mul_smul, Matrix.smul_mul, hZHZ]
    exact hWhitened

end SchauderBasisOrbits

namespace SchauderBasisOrbits

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
variable {n : ℕ}

/-- Coordinate insertion of one complete column. -/
def columnEmbedding (𝕜 ι : Type*) [Zero 𝕜] [One 𝕜] [DecidableEq ι] (k : Fin n) :
    Matrix (Fin n × ι) ι 𝕜 :=
  fun p j ↦ if p = (k, j) then 1 else 0

omit [Fintype ι] in
theorem columnEmbedding_apply (k : Fin n) (p : Fin n × ι) (i : ι) :
    columnEmbedding 𝕜 ι k p i = if p.1 = k ∧ p.2 = i then 1 else 0 := by
  simp [columnEmbedding, Prod.ext_iff]

theorem columnEmbedding_left_mul {σ : Type*} (k : Fin n) (X : Matrix (Fin n × ι) σ 𝕜) :
    (columnEmbedding 𝕜 ι k)ᴴ * X = X.submatrix (fun i ↦ (k, i)) id := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, columnEmbedding, apply_ite, ite_mul]

theorem columnEmbedding_isometric (k : Fin n) :
    (columnEmbedding 𝕜 ι k)ᴴ * columnEmbedding 𝕜 ι k = 1 := by
  rw [columnEmbedding_left_mul]
  ext i j
  simp [columnEmbedding, Matrix.one_apply]

theorem columnEmbedding_right_mul {σ : Type*} (k : Fin n) (X : Matrix σ (Fin n × ι) 𝕜) :
    X * columnEmbedding 𝕜 ι k = X.submatrix id (fun i ↦ (k, i)) := by
  ext i j
  simp [Matrix.mul_apply, columnEmbedding, mul_ite]

theorem columnEmbedding_gram (k : Fin n) (X : Matrix (Fin n × ι) (Fin n × ι) 𝕜) :
    (columnEmbedding 𝕜 ι k)ᴴ * X * columnEmbedding 𝕜 ι k =
      X.submatrix (fun i ↦ (k,i)) (fun i ↦ (k,i)) := by
  rw [columnEmbedding_left_mul, columnEmbedding_right_mul, Matrix.submatrix_submatrix]
  rfl

theorem columnEmbedding_commute_left (k : Fin n) (E : Matrix ι ι 𝕜) :
    (columnEmbedding 𝕜 ι k)ᴴ * columnTensorChange E = E * (columnEmbedding 𝕜 ι k)ᴴ := by
  change (columnEmbedding 𝕜 ι k)ᴴ * (columnTensorChange E (σ := Fin n)) =
    E * (columnEmbedding 𝕜 ι k)ᴴ
  rw [columnEmbedding_left_mul]
  ext i ⟨l,j⟩
  by_cases hl : l = k
  · subst l
    simp [columnTensorChange, Matrix.mul_apply, columnEmbedding, Matrix.conjTranspose_apply, apply_ite]
  · simp [columnTensorChange, Matrix.mul_apply, columnEmbedding, Matrix.conjTranspose_apply, hl, Ne.symm hl]

theorem columnEmbedding_commute_right (k : Fin n) (E : Matrix ι ι 𝕜) :
    (columnTensorChange E)ᴴ * columnEmbedding 𝕜 ι k = columnEmbedding 𝕜 ι k * Eᴴ := by
  let I := columnEmbedding 𝕜 ι k
  let Z := columnTensorChange E (σ := Fin n)
  have h : Iᴴ * Z = E * Iᴴ := columnEmbedding_commute_left k E
  have hc := congrArg (fun X : Matrix ι (Fin n × ι) 𝕜 ↦ Xᴴ) h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hc
  exact hc

theorem blockDiagonal_inv_of {G : ι → Matrix (Fin n) (Fin n) 𝕜} (h : ∀ j, IsUnit (G j)) :
    (Matrix.blockDiagonal G)⁻¹ = Matrix.blockDiagonal (fun j ↦ (G j)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.blockDiagonal_mul]
  have hfun : (fun j ↦ G j * (G j)⁻¹) = 1 := by
    funext j
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (h j))
  rw [hfun, Matrix.blockDiagonal_one]

theorem columnEmbedding_blockDiagonal (k : Fin n) (G : ι → Matrix (Fin n) (Fin n) 𝕜) :
    (columnEmbedding 𝕜 ι k)ᴴ * Matrix.blockDiagonal G * columnEmbedding 𝕜 ι k =
      Matrix.diagonal (fun j ↦ G j k k) := by
  rw [columnEmbedding_gram]
  rfl

theorem matrix_inv_congruence_transport {σ : Type*} [Fintype σ] [DecidableEq σ] (A E : Matrix σ σ 𝕜)
    (hE : IsUnit E) : A⁻¹ = E * (Eᴴ * A * E)⁻¹ * Eᴴ := by
  have heu : IsUnit E.det := (Matrix.isUnit_iff_isUnit_det _).mp hE
  have hEu' : IsUnit Eᴴ.det := (Matrix.isUnit_iff_isUnit_det _).mp (hE.star)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  symm
  calc
    _ = (E * E⁻¹) * A⁻¹ * ((Eᴴ)⁻¹ * Eᴴ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv E heu, Matrix.nonsing_inv_mul _ hEu',
      Matrix.one_mul, Matrix.mul_one]

/-- Forward compression in one column, when that scalar diagonal is at most one. -/
theorem columnTensorGram_column_le {A Ω : Matrix ι ι 𝕜} {B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hΩ : Ω.IsHermitian) (hAΩ : A ≤ Ω) (k : Fin n)
    {m : ℝ} (hm : m ≤ 1) (hBk : B k k = (m : 𝕜)) :
    let I := columnEmbedding 𝕜 ι k
    Iᴴ * columnTensorGram A Ω B * I ≤ Ω := by
  dsimp only
  rw [columnEmbedding_gram]
  have hForm : (columnTensorGram A Ω B).submatrix (fun i ↦ (k,i)) (fun i ↦ (k,i)) =
      A + m • (Ω - A) := by
    ext i j
    simp [columnTensorGram, hBk, RCLike.real_smul_eq_coe_mul]
  rw [hForm]
  refine matrix_le_of_qform_le (hA.add ((hΩ.sub hA).smul (IsSelfAdjoint.all _))) hΩ fun x ↦ ?_
  simp only [qform_add, qform_smul, qform_sub]
  have hp := mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr (qform_mono hAΩ x))
  linarith only [hp]

/-- SC07: inverse column compression after whitening and the scalar inverse mixture bound. -/
theorem columnTensorGram_inv_column_le {A Ω : Matrix ι ι 𝕜} {B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) (hΩ : Ω.PosDef) (hAΩ : A ≤ Ω) (hB : B.PosDef)
    (k : Fin n) {r : ℝ} (hr : 1 ≤ r) (hBInv : RCLike.re (B⁻¹ k k) ≤ r) :
    let I := columnEmbedding 𝕜 ι k
    Iᴴ * (columnTensorGram A Ω B)⁻¹ * I ≤ r • Ω⁻¹ := by
  let H := columnTensorGram A Ω B
  let I := columnEmbedding 𝕜 ι k
  obtain ⟨E, β, hE, hEΩ, hEA, hβ⟩ := matrix_whitening_eigenbasis hΩ hA hAΩ
  let Z := columnTensorChange E (σ := Fin n)
  let G := fun i ↦ β i • (1 : Matrix (Fin n) (Fin n) 𝕜) + (1 - β i) • B
  have hZu := columnTensorChange_isUnit (κ := Fin n) E hE
  have hZHZ : Zᴴ * H * Z = Matrix.blockDiagonal G := by
    change (columnTensorChange E)ᴴ * columnTensorGram A Ω B * columnTensorChange E = _
    rw [columnTensorGram_congruence, hEA, hEΩ, columnTensorGram_diagonal]
  have hGp (i : ι) : (G i).PosDef := posDef_convex_combination Matrix.PosDef.one hB
    (hβ i).1.le (hβ i).2
  let Hinv := Matrix.blockDiagonal (fun i ↦ (G i)⁻¹)
  have hRe i : RCLike.re ((G i)⁻¹ k k) ≤ r := by
    let e : Fin n → 𝕜 := Pi.single k 1
    have hGiv := matrix_inv_convex_combination Matrix.PosDef.one hB (hβ i).1.le (hβ i).2
    change (G i)⁻¹ ≤ β i • (1 : Matrix (Fin n) (Fin n) 𝕜)⁻¹ + (1 - β i) • B⁻¹ at hGiv
    rw [inv_one] at hGiv
    have h := qform_mono hGiv e
    have hh : RCLike.re ((G i)⁻¹ k k) ≤ β i + (1 - β i) * RCLike.re (B⁻¹ k k) := by
      simpa [e, qform, RCLike.real_smul_eq_coe_mul] using h
    have hh₁ := mul_le_mul_of_nonneg_left hBInv (sub_nonneg.mpr (hβ i).2)
    have hh₂ := mul_le_mul_of_nonneg_left hr (hβ i).1.le
    linarith only [hh, hh₁, hh₂]
  have hDiag : Iᴴ * Hinv * I ≤ r • (1 : Matrix ι ι 𝕜) := by
    change (columnEmbedding 𝕜 ι k)ᴴ * Matrix.blockDiagonal (fun i ↦ (G i)⁻¹) *
      columnEmbedding 𝕜 ι k ≤ _
    rw [columnEmbedding_blockDiagonal, Matrix.le_iff]
    have heq : r • (1 : Matrix ι ι 𝕜) - Matrix.diagonal (fun i ↦ (G i)⁻¹ k k) =
        Matrix.diagonal (fun i ↦ (r : 𝕜) - (G i)⁻¹ k k) := by
      ext i j
      by_cases h : i = j <;> simp [h, RCLike.real_smul_eq_coe_mul]
    rw [heq, Matrix.posSemidef_diagonal_iff]
    intro i
    refine RCLike.nonneg_iff.mpr ⟨?_, ?_⟩
    · rw [map_sub, RCLike.ofReal_re]
      exact sub_nonneg.mpr (hRe i)
    · have hi := congrArg RCLike.im ((hGp i).inv.isHermitian.apply k k)
      simp only [RCLike.star_def, RCLike.conj_im] at hi
      rw [map_sub, RCLike.ofReal_im]
      linarith only [hi]
  have hInv : H⁻¹ = Z * Hinv * Zᴴ := by
    rw [matrix_inv_congruence_transport H Z hZu, hZHZ,
      blockDiagonal_inv_of (fun i ↦ (hGp i).isUnit)]
  have hΩInv : Ω⁻¹ = E * Eᴴ := by
    rw [matrix_inv_congruence_transport Ω E hE, hEΩ, inv_one, Matrix.mul_one]
  have hl : Iᴴ * Z = E * Iᴴ := columnEmbedding_commute_left k E
  have hr' : Zᴴ * I = I * Eᴴ := columnEmbedding_commute_right k E
  change Iᴴ * H⁻¹ * I ≤ _
  rw [hInv, hΩInv]
  have hComp : Iᴴ * (Z * Hinv * Zᴴ) * I = E * (Iᴴ * Hinv * I) * Eᴴ := calc
    _ = (Iᴴ * Z) * Hinv * (Zᴴ * I) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hl, hr']; simp only [Matrix.mul_assoc]
  rw [hComp]
  have hout := matrix_congruence_mono hDiag Eᴴ
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hout

end SchauderBasisOrbits

namespace SchauderBasisOrbits

variable {𝕜 ι κ : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The metric insertion and extraction inherit norm bounds from the two Gram compressions. -/
theorem metric_column_norm_bounds [Nonempty κ]
    {H : Matrix ι ι 𝕜} {Ω : Matrix κ κ 𝕜} (hH : H.PosDef) (hΩ : Ω.PosDef)
    (I : Matrix ι κ 𝕜) {r : ℝ} (hr : 0 ≤ r)
    (hInsertion : Iᴴ * H * I ≤ Ω) (hExtraction : Iᴴ * H⁻¹ * I ≤ r • Ω⁻¹) :
    let J := CFC.sqrt H * I * (CFC.sqrt Ω)⁻¹
    let X := CFC.sqrt Ω * Iᴴ * (CFC.sqrt H)⁻¹
    opNorm J ≤ 1 ∧ opNorm X ≤ Real.sqrt r := by
  let P := CFC.sqrt H
  let Q := CFC.sqrt Ω
  let J := P * I * Q⁻¹
  let X := Q * Iᴴ * P⁻¹
  have hP := posDef_sqrt hH
  have hQ := posDef_sqrt hΩ
  have hPi : P⁻¹ᴴ = P⁻¹ := hP.inv.isHermitian.eq
  have hQi : Q⁻¹ᴴ = Q⁻¹ := hQ.inv.isHermitian.eq
  have hPsq : P * P = H := sqrt_mul_sqrt_of_posDef hH
  have hQsq : Q * Q = Ω := sqrt_mul_sqrt_of_posDef hΩ
  have hQinv := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQinv
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQinv
  have hPinvSq : P⁻¹ * P⁻¹ = H⁻¹ := by rw [← Matrix.mul_inv_rev, hPsq]
  have hQinvSq : Q⁻¹ * Q⁻¹ = Ω⁻¹ := by rw [← Matrix.mul_inv_rev, hQsq]
  have hPherm : Pᴴ = P := hP.isHermitian.eq
  have hQherm : Qᴴ = Q := hQ.isHermitian.eq
  have hJgram : Jᴴ * J = Q⁻¹ * (Iᴴ * H * I) * Q⁻¹ := calc
    _ = Q⁻¹ * (Iᴴ * (P * P) * I) * Q⁻¹ := by
      dsimp only [J]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQi, hPherm]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPsq]
  have hXgram : X * Xᴴ = Q * (Iᴴ * H⁻¹ * I) * Q := calc
    _ = Q * (Iᴴ * (P⁻¹ * P⁻¹) * I) * Q := by
      dsimp only [X]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPi, hQherm,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPinvSq]
  have hjId : Q⁻¹ * Ω * Q⁻¹ = 1 := calc
    _ = (Q⁻¹ * Q) * (Q * Q⁻¹) := by rw [← hQsq]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQQ', hQQ, Matrix.one_mul]
  have hxId : Q * (r • Ω⁻¹) * Q = r • (1 : Matrix κ κ 𝕜) := calc
    _ = r • ((Q * Q⁻¹) * (Q⁻¹ * Q)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← hQinvSq]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQQ, hQQ', Matrix.one_mul]
  have hbJ := matrix_congruence_mono hInsertion Q⁻¹
  rw [hQi, ← hJgram, hjId] at hbJ
  have hbX := matrix_congruence_mono hExtraction Q
  rw [hQherm, ← hXgram, hxId] at hbX
  have hj := (opNorm_psd_le_iff (Matrix.posSemidef_conjTranspose_mul_self J) (r := 1)).mpr
    (by simpa only [one_smul] using hbJ)
  have hx := (opNorm_psd_le_iff (Matrix.posSemidef_self_mul_conjTranspose X)).mpr hbX
  rw [opNorm_rect_conjTranspose_mul_self] at hj
  have hx' := opNorm_rect_conjTranspose_mul_self Xᴴ
  rw [Matrix.conjTranspose_conjTranspose, opNorm_rect_conjTranspose] at hx'
  rw [hx'] at hx
  have hhx : opNorm X ^ 2 ≤ Real.sqrt r ^ 2 := by simpa only [Real.sq_sqrt hr] using hx
  exact ⟨(sq_le_sq₀ (show 0 ≤ opNorm J from norm_nonneg _) zero_le_one).mp (by simpa using hj),
    (sq_le_sq₀ (show 0 ≤ opNorm X from norm_nonneg _) (Real.sqrt_nonneg _)).mp hhx⟩

/-- The metric insertion/extraction pair is a section/retraction when the original inclusion
uses orthonormal coefficient coordinates. -/
theorem metric_column_extraction_insert_eq {H : Matrix ι ι 𝕜} {Ω : Matrix κ κ 𝕜}
    (hH : H.PosDef) (hΩ : Ω.PosDef) (I : Matrix ι κ 𝕜) (hI : Iᴴ * I = 1) :
    let J := CFC.sqrt H * I * (CFC.sqrt Ω)⁻¹
    let X := CFC.sqrt Ω * Iᴴ * (CFC.sqrt H)⁻¹
    X * J = 1 := by
  dsimp only
  let P := CFC.sqrt H
  let Q := CFC.sqrt Ω
  change (Q * Iᴴ * P⁻¹) * (P * I * Q⁻¹) = 1
  rw [show (Q * Iᴴ * P⁻¹) * (P * I * Q⁻¹) = Q * Iᴴ * (P⁻¹ * P) * I * Q⁻¹ by
    simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).mp (posDef_sqrt hH).isUnit),
    Matrix.mul_one, Matrix.mul_assoc Q Iᴴ I, hI, Matrix.mul_one,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det Q).mp (posDef_sqrt hΩ).isUnit)]

end SchauderBasisOrbits
