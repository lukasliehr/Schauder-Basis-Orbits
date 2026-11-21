import LeanCode.Finite.ColumnMatrix

open Matrix
open scoped BigOperators InnerProductSpace MatrixOrder ComplexOrder

noncomputable section

namespace SchauderBasisOrbits

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The mask of a flattened prefix, expressed in column and row coordinates. -/
def columnCutMask (𝕜 : Type*) [Zero 𝕜] [One 𝕜] (n m k : ℕ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜 :=
  Matrix.diagonal (fun p ↦ if p.2.val + m * p.1.val < k then 1 else 0)

theorem qform_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι ι 𝕜) (e : κ ≃ ι) (x : κ → 𝕜) :
    qform (M.submatrix e e) x = qform M (x ∘ e.symm) := by
  unfold qform
  congr 1
  change (∑ i, star (x i) * ∑ j, M (e i) (e j) * x j) =
    ∑ i, star (x (e.symm i)) * ∑ j, M i j * x (e.symm j)
  apply Fintype.sum_equiv e
  intro i
  rw [e.symm_apply_apply]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun j ↦ by simp)

theorem columnCutMask_mulVec_flat {n m : ℕ} (k : ℕ) (c : Fin (n * m) → 𝕜) :
    columnCutMask 𝕜 n m k *ᵥ (c ∘ finProdFinEquiv) =
      truncCoeff k c ∘ finProdFinEquiv := by
  funext p
  rw [columnCutMask, Matrix.mulVec_diagonal]
  change (if p.2.val + m * p.1.val < k then 1 else 0) * c (finProdFinEquiv p) =
    if p.2.val + m * p.1.val < k then c (finProdFinEquiv p) else 0
  split <;> simp

theorem columnCutMask_full {n m : ℕ} :
    columnCutMask 𝕜 n m (n * m) = 1 := by
  have h (p : Fin n × Fin m) : p.2.val + m * p.1.val < n * m :=
    (finProdFinEquiv p).isLt
  simp [columnCutMask, h]

theorem completedColumnMask_eq_diagonal {n m : ℕ} (k : ℕ) :
    completedColumnMask 𝕜 (Fin m) n k =
      Matrix.diagonal (fun p : Fin n × Fin m ↦ if p.1.val < k then 1 else 0) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  by_cases h : r = s
  · subst s
    by_cases h' : i = j
    · subst j
      simp [completedColumnMask, Matrix.blockDiagonal_apply, prefixMask]
    · simp [completedColumnMask, Matrix.blockDiagonal_apply, prefixMask, h']
  · simp [completedColumnMask, Matrix.blockDiagonal_apply, prefixMask, h]

/-- The contribution from the last, possibly incomplete, column. -/
def incompleteColumnMask (𝕜 : Type*) [Zero 𝕜] [One 𝕜] {n m : ℕ} (i : Fin n) (l : ℕ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜 :=
  Matrix.diagonal (fun p ↦ if p.1 = i ∧ p.2.val < l then 1 else 0)

theorem columnCutMask_column {n m : ℕ} (i : Fin n) {l : ℕ} (hl : l ≤ m) :
    columnCutMask 𝕜 n m (m * i.val + l) =
      completedColumnMask 𝕜 (Fin m) n i.val + incompleteColumnMask (m := m) 𝕜 i l := by
  rw [completedColumnMask_eq_diagonal, incompleteColumnMask, columnCutMask, Matrix.diagonal_add]
  congr 1
  funext p
  change (if p.2.val + m * p.1.val < m * i.val + l then (1 : 𝕜) else 0) =
    (if p.1.val < i.val then 1 else 0) + (if p.1 = i ∧ p.2.val < l then 1 else 0)
  rcases lt_trichotomy p.1.val i.val with h | h | h
  · have hp2 := p.2.isLt
    have hle := Nat.mul_le_mul_left m (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at hle
    have hineq : p.2.val + m * p.1.val < m * i.val + l := by omega
    have hi : p.1 ≠ i := fun he ↦ h.ne (congrArg Fin.val he)
    simp [hineq, h, hi]
  · have hi : p.1 = i := Fin.ext h
    simp [hi, Nat.add_comm]
  · have hle := Nat.mul_le_mul_left m (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at hle
    have hineq : ¬ p.2.val + m * p.1.val < m * i.val + l := by omega
    have hi : p.1 ≠ i := fun he ↦ h.ne (congrArg Fin.val he).symm
    simp [hineq, h.not_gt, hi]

theorem incompleteColumnMask_eq_embedding {n m : ℕ} (k : Fin n) (l : ℕ) :
    incompleteColumnMask (m := m) 𝕜 k l =
      columnEmbedding 𝕜 (Fin m) k * (prefixMask (n := m) 𝕜 l : Matrix (Fin m) (Fin m) 𝕜) *
        (columnEmbedding 𝕜 (Fin m) k)ᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.mul_apply, prefixMask]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, columnEmbedding_apply]
  by_cases hi : i = k
  · subst i
    rw [Finset.sum_eq_single a]
    · by_cases hj : j = k
      · subst j
        by_cases ha : a = b
        · subst b
          simp [incompleteColumnMask]
        · simp [incompleteColumnMask, ha, Ne.symm ha]
      · simp [incompleteColumnMask, hj, Ne.symm hj]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  · simp [incompleteColumnMask, Matrix.diagonal_apply, hi]


theorem columnCutMask_qform_le {n m : ℕ} (hm : 0 < m)
    {H : Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜} (hH : H.PosSemidef) {K : ℝ} (hK : 1 ≤ K)
    (hPart : ∀ (i : Fin n) l, l ≤ m → ∀ c : Fin n × Fin m → 𝕜,
      qform H ((completedColumnMask 𝕜 (Fin m) n i.val + incompleteColumnMask (m := m) 𝕜 i l) *ᵥ c)
        ≤ K ^ 2 * qform H c)
    (k : ℕ) (hk : k ≤ n * m) (c : Fin n × Fin m → 𝕜) :
    qform H (columnCutMask 𝕜 n m k *ᵥ c) ≤ K ^ 2 * qform H c := by
  rcases lt_or_eq_of_le hk with hk | rfl
  · have hci : k / m < n := (Nat.div_lt_iff_lt_mul hm).mpr hk
    let i : Fin n := ⟨k / m, hci⟩
    let l := k % m
    have hl : l ≤ m := (Nat.mod_lt _ hm).le
    have hk' : k = m * i.val + l := by
      dsimp only [i, l]
      exact (Nat.div_add_mod k m).symm
    rw [hk', columnCutMask_column i hl]
    exact hPart i l hl c
  · rw [columnCutMask_full, Matrix.one_mulVec]
    exact le_mul_of_one_le_left (qform_nonneg hH _) (by nlinarith)

theorem pb_submatrix_of_column_qform {n m : ℕ}
    {H : Matrix (Fin n × Fin m) (Fin n × Fin m) 𝕜} {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (h : ∀ k ≤ n * m, ∀ c : Fin n × Fin m → 𝕜,
      qform H (columnCutMask 𝕜 n m k *ᵥ c) ≤ K ^ 2 * qform H c) :
    let e : Fin (n * m) ≃ Fin n × Fin m := finProdFinEquiv.symm
    PB ((s • H).submatrix e e) K := by
  dsimp only []
  refine ⟨hK, fun k hk c ↦ ?_⟩
  simp only [qform_submatrix_equiv, Equiv.symm_symm, qform_smul]
  rw [← columnCutMask_mulVec_flat]
  calc
    _ ≤ s * (K ^ 2 * qform H (c ∘ finProdFinEquiv)) :=
      mul_le_mul_of_nonneg_left (h k hk _) hs
    _ = _ := by ring

end SchauderBasisOrbits
