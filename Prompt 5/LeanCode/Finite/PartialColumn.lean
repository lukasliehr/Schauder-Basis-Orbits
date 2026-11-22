module

public import LeanCode.Finite.ColumnMatrix
public import LeanCode.Finite.Projection

@[expose] public section

open Matrix ContinuousLinearMap
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProduct

noncomputable section
namespace SchauderBasisOrbits

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

private theorem opNorm_sq_disjoint_idempotents {P C : Matrix ι ι 𝕜}
    (hP : IsIdempotentElem P) (hC : IsIdempotentElem C) (hPC : P * C = 0) (hCP : C * P = 0)
    {K L : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L) (hPK : opNorm P ≤ K) (hCL : opNorm C ≤ L) :
    opNorm (P + C) ^ 2 ≤ 1 + (Real.sqrt (K ^ 2 - 1) + Real.sqrt (L ^ 2 - 1)) ^ 2 := by
  let f := Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)
  have hP' : IsIdempotentElem (f P) := by
    change f P * f P = f P
    rw [← map_mul, hP.eq]
  have hC' : IsIdempotentElem (f C) := by
    change f C * f C = f C
    rw [← map_mul, hC.eq]
  have hPC' : f P * f C = 0 := by rw [← map_mul, hPC, map_zero]
  have hCP' : f C * f P = 0 := by rw [← map_mul, hCP, map_zero]
  change ‖f (P + C)‖ ^ 2 ≤ _
  rw [map_add]
  exact norm_sq_disjoint_idempotent_add_le _ _ hP' hC' hPC' hCP' hK hL hPK hCL

private theorem metricConjugate_isIdempotent {G M : Matrix ι ι 𝕜} (hG : G.PosDef)
    (hM : IsIdempotentElem M) : IsIdempotentElem (CFC.sqrt G * M * (CFC.sqrt G)⁻¹) := by
  let R := CFC.sqrt G
  let S := R⁻¹
  have hRS : S * R = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det R).mp (posDef_sqrt hG).isUnit)
  show (R * M * S) * (R * M * S) = _
  rw [show (R * M * S) * (R * M * S) = R * M * (S * R) * M * S by simp only [Matrix.mul_assoc],
    hRS, Matrix.mul_one, Matrix.mul_assoc _ M M, hM.eq]

variable {n m : ℕ}

/-- A prefix terminating at row cutoff r inside column k. -/
def partialColumnMask (𝕜 : Type*) [RCLike 𝕜] (n m : ℕ) (k : Fin n) (r : ℕ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜 :=
  let I : Matrix (Fin n × Fin m) (Fin m) 𝕜 := columnEmbedding 𝕜 (Fin m) k
  completedColumnMask 𝕜 (Fin m) n k.val + (I * prefixMask (n := m) 𝕜 r : Matrix (Fin n × Fin m) (Fin m) 𝕜) * Iᴴ

theorem completedColumnMask_isIdempotent (k : ℕ) :
    IsIdempotentElem (completedColumnMask 𝕜 ι n k) := by
  show Matrix.blockDiagonal (fun _ : ι ↦ prefixMask (n := n) 𝕜 k) *
    Matrix.blockDiagonal (fun _ : ι ↦ prefixMask (n := n) 𝕜 k) = _
  rw [← Matrix.blockDiagonal_mul]
  congr 1
  funext i
  exact (prefixMask_isIdempotent (𝕜 := 𝕜) (n := n) k).eq

omit [Fintype ι] in
theorem completedColumnMask_isHermitian (k : ℕ) :
    (completedColumnMask 𝕜 ι n k).IsHermitian := by
  show (Matrix.blockDiagonal (fun _ : ι ↦ prefixMask (n := n) 𝕜 k))ᴴ = _
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext i
  exact prefixMask_isHermitian k

theorem completedColumnMask_columnEmbedding_zero (k : Fin n) :
    completedColumnMask 𝕜 ι n k.val * columnEmbedding 𝕜 ι k = 0 := by
  rw [columnEmbedding_right_mul]
  ext ⟨i,j⟩ r
  change Matrix.blockDiagonal (fun _ : ι ↦ prefixMask (n := n) 𝕜 k.val) (i,j) (k,r) = 0
  by_cases hi : i = k <;> by_cases hj : j = r <;> simp [Matrix.blockDiagonal_apply, prefixMask, hi, hj]

def partialColumnBoundSq (Ks Kv ε : ℝ) : ℝ :=
  1 + (Real.sqrt (Ks ^ 2 - 1) + Real.sqrt ((1 + 2 * ε) * Kv ^ 2 - 1)) ^ 2

set_option maxHeartbeats 700000 in
/-- SC08: every partial column cut is controlled by the completed-column and row bounds. -/
theorem partialColumn_qform_le [Nonempty (Fin m)]
    {H : Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜} {Ω : Matrix (Fin m) (Fin m) 𝕜}
    (hH : H.PosDef) (hΩ : Ω.PosDef) (k : Fin n) (l : ℕ) (hl : l ≤ m)
    {Ks Kv ε : ℝ} (hKs : 1 ≤ Ks) (hKv : 1 ≤ Kv) (hε : 0 ≤ ε)
    (hRow : PB Ω Kv)
    (hFull : completedColumnMask 𝕜 (Fin m) n k.val * H * completedColumnMask 𝕜 (Fin m) n k.val ≤ Ks ^ 2 • H)
    (hInsert : (columnEmbedding 𝕜 (Fin m) k)ᴴ * H * columnEmbedding 𝕜 (Fin m) k ≤ Ω)
    (hExtract : (columnEmbedding 𝕜 (Fin m) k)ᴴ * H⁻¹ * columnEmbedding 𝕜 (Fin m) k ≤ (1 + 2 * ε) • Ω⁻¹)
    (c : Fin n × Fin m → 𝕜) :
    qform H (partialColumnMask 𝕜 n m k l *ᵥ c) ≤ partialColumnBoundSq Ks Kv ε * qform H c := by
  let A := CFC.sqrt H
  let B := CFC.sqrt Ω
  let P₀ := completedColumnMask 𝕜 (Fin m) n k.val
  let C₀ := prefixMask (n := m) 𝕜 l
  let P := A * P₀ * A⁻¹
  let C := B * C₀ * B⁻¹
  let I := columnEmbedding 𝕜 (Fin m) k
  let J := A * I * B⁻¹
  let X := B * Iᴴ * A⁻¹
  let R := J * C * X
  have hP : IsIdempotentElem P := metricConjugate_isIdempotent hH (completedColumnMask_isIdempotent k.val)
  have hC : IsIdempotentElem C := metricConjugate_isIdempotent hΩ (prefixMask_isIdempotent l)
  have hXJ : X * J = 1 := metric_column_extraction_insert_eq hH hΩ I (columnEmbedding_isometric k)
  have hR : IsIdempotentElem R := by
    show (J * C * X) * (J * C * X) = J * C * X
    rw [show (J * C * X) * (J * C * X) = J * C * (X * J) * C * X by simp only [Matrix.mul_assoc],
      hXJ, Matrix.mul_one, Matrix.mul_assoc J C C, hC.eq]
  have hAi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det A).mp (posDef_sqrt hH).isUnit)
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det B).mp (posDef_sqrt hΩ).isUnit)
  have hP₀I : P₀ * I = 0 := completedColumnMask_columnEmbedding_zero k
  have hIP₀ : Iᴴ * P₀ = 0 := by
    have hPh : P₀ᴴ = P₀ := completedColumnMask_isHermitian k.val
    have hc := congrArg (fun M : Matrix (Fin n × Fin m) (Fin m) 𝕜 ↦ Mᴴ) hP₀I
    rw [Matrix.conjTranspose_mul, hPh, Matrix.conjTranspose_zero] at hc
    exact hc
  have hPJ : P * J = 0 := by
    change (A * P₀ * A⁻¹) * (A * I * B⁻¹) = 0
    rw [show (A * P₀ * A⁻¹) * (A * I * B⁻¹) = A * P₀ * (A⁻¹ * A) * I * B⁻¹ by
      simp only [Matrix.mul_assoc], hAi, Matrix.mul_one, Matrix.mul_assoc A P₀ I,
      hP₀I, Matrix.mul_zero, Matrix.zero_mul]
  have hXP : X * P = 0 := by
    change (B * Iᴴ * A⁻¹) * (A * P₀ * A⁻¹) = 0
    rw [show (B * Iᴴ * A⁻¹) * (A * P₀ * A⁻¹) = B * Iᴴ * (A⁻¹ * A) * P₀ * A⁻¹ by
      simp only [Matrix.mul_assoc], hAi, Matrix.mul_one, Matrix.mul_assoc B Iᴴ P₀,
      hIP₀, Matrix.mul_zero, Matrix.zero_mul]
  have hPR : P * R = 0 := by
    change P * (J * C * X) = 0
    rw [show P * (J * C * X) = (P * J) * C * X by simp only [Matrix.mul_assoc],
      hPJ, Matrix.zero_mul, Matrix.zero_mul]
  have hRP : R * P = 0 := by
    change (J * C * X) * P = 0
    rw [Matrix.mul_assoc, hXP, Matrix.mul_zero]
  have hKn : 0 ≤ Ks := zero_le_one.trans hKs
  have hPn : opNorm P ≤ Ks := (metric_opNorm_le_iff hH P₀ hKn).mpr fun x ↦ by
    have hPh : P₀ᴴ = P₀ := completedColumnMask_isHermitian k.val
    -- Reassociate only the left occurrence of the self-adjoint mask.
    have hx : qform (P₀ * H * P₀) x = qform H (P₀ *ᵥ x) := by
      simpa only [hPh] using qform_conjTranspose_mul H P₀ x
    have hx' := qform_mono hFull x
    change qform (P₀ * H * P₀) x ≤ qform (Ks ^ 2 • H) x at hx'
    simpa only [hx, qform_smul] using hx'
  have hCn : opNorm C ≤ Kv := (metric_opNorm_le_iff hΩ C₀ hRow.1).mpr fun x ↦ by
    change qform Ω (prefixMask (n := m) 𝕜 l *ᵥ x) ≤ _
    rw [prefixMask_mulVec]
    exact hRow.2 l hl x
  have hNorm := metric_column_norm_bounds hH hΩ I (by linarith : 0 ≤ 1 + 2 * ε) hInsert hExtract
  let M := Real.sqrt (1 + 2 * ε) * Kv
  have hM : 1 ≤ M := by
    have hS : 1 ≤ Real.sqrt (1 + 2 * ε) := calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    have hm := mul_le_mul hS hKv zero_le_one (Real.sqrt_nonneg (1 + 2 * ε))
    simpa only [one_mul] using hm
  have hRn : opNorm R ≤ M := calc
    _ ≤ opNorm (J * C) * opNorm X := opNorm_mul_rect _ _
    _ ≤ opNorm J * opNorm C * opNorm X := mul_le_mul_of_nonneg_right (opNorm_mul_rect _ _) (norm_nonneg _)
    _ ≤ 1 * Kv * Real.sqrt (1 + 2 * ε) := by
      have hJ : opNorm J ≤ 1 := hNorm.1
      have hX : opNorm X ≤ Real.sqrt (1 + 2 * ε) := hNorm.2
      exact mul_le_mul (mul_le_mul hJ hCn (norm_nonneg _) zero_le_one) hX (norm_nonneg _)
        (by linarith)
    _ = _ := by dsimp only [M]; rw [one_mul, mul_comm]
  have hMsq : M ^ 2 = (1 + 2 * ε) * Kv ^ 2 := by
    dsimp only [M]
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  have hSum := opNorm_sq_disjoint_idempotents hP hR hPR hRP hKs hM hPn hRn
  rw [hMsq] at hSum
  have hSumEq : P + R = A * partialColumnMask 𝕜 n m k l * A⁻¹ := by
    have hR' : R = A * I * C₀ * Iᴴ * A⁻¹ := calc
      _ = A * I * (B⁻¹ * B) * C₀ * (B⁻¹ * B) * Iᴴ * A⁻¹ := by
        dsimp only [R, J, X, C]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBi, Matrix.mul_one, Matrix.mul_one]
    rw [hR']
    change A * P₀ * A⁻¹ + A * I * C₀ * Iᴴ * A⁻¹ = A * (P₀ + I * C₀ * Iᴴ) * A⁻¹
    rw [Matrix.mul_add, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
  rw [hSumEq] at hSum
  let S := partialColumnBoundSq Ks Kv ε
  have hSn : 0 ≤ S := by dsimp only [S, partialColumnBoundSq]; positivity
  have hS : opNorm (A * partialColumnMask 𝕜 n m k l * A⁻¹) ≤ Real.sqrt S := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hSn]
    exact hSum
  have hf := (metric_opNorm_le_iff hH (partialColumnMask 𝕜 n m k l) (Real.sqrt_nonneg S)).mp hS c
  simpa only [Real.sq_sqrt hSn] using hf

end SchauderBasisOrbits
