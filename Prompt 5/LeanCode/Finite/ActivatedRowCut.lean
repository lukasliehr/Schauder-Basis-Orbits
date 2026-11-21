import LeanCode.Finite.Tuples
import LeanCode.Finite.RowMatrix
/-! The sharp activated row cut bound, assembled over the exhaustive fiber decomposition. -/

set_option maxHeartbeats 500000



open ContinuousLinearMap Submodule
open scoped BigOperators InnerProductSpace InnerProduct
noncomputable section
namespace SchauderBasisOrbits

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

variable (A : Submodule 𝕜 E) [FiniteDimensional 𝕜 A] {D : E →L[𝕜] E} (hDA : D† = D)

/-- All the orthogonal reducing subspaces, including the two common eigenspaces. -/
def twoProjectionFibers : (Fin (Module.finrank 𝕜 A) ⊕ Bool) → Submodule 𝕜 E :=
  Sum.elim (fun i ↦ twoProjectionPlane D (projectionAxes A hDA i)) (fun b ↦
    (twoProjectionSpan A D)ᗮ ⊓ if b then D.range else D.ker)

theorem twoProjectionFibers_mem_common (hD : IsIdempotentElem D) (b : Bool) (x : E) :
    x ∈ twoProjectionFibers A hDA (Sum.inr b) ↔
      x ∈ (twoProjectionSpan A D)ᗮ ∧ D x = if b then x else 0 := by
  change x ∈ (twoProjectionSpan A D)ᗮ ⊓ (if b then D.range else D.ker) ↔ _
  simp only [Submodule.mem_inf]
  apply and_congr_right
  intro _
  cases b
  · simp
  · simp only [ite_true]
    constructor
    · rintro ⟨y, rfl⟩
      exact DFunLike.congr_fun hD.eq y
    · intro hx
      exact ⟨x, hx⟩

theorem twoProjectionFibers_decomp (hD : IsIdempotentElem D) (x : E) :
    ∃ w : Fin (Module.finrank 𝕜 A) ⊕ Bool → E,
      (∀ i, w i ∈ twoProjectionFibers A hDA i) ∧ (∑ i, w i) = x := by
  obtain ⟨f, u, v, hf, hu, hv, _, _, hDu, hDv, _, hsum⟩ := twoProjection_decompose A D hD hDA x
  refine ⟨Sum.elim f (fun b ↦ if b then u else v), ?_, ?_⟩
  · rintro (i | b)
    · exact hf i
    · apply (twoProjectionFibers_mem_common A hDA hD b _).mpr
      cases b
      · exact ⟨hv, hDv⟩
      · exact ⟨hu, hDu⟩
  · rw [Fintype.sum_sum_type, Fintype.sum_bool]
    simp only [Sum.elim_inl, Sum.elim_inr, ite_true]
    rw [← hsum]
    abel

theorem twoProjectionFibers_orthogonal (hD : IsIdempotentElem D)
    (i j : Fin (Module.finrank 𝕜 A) ⊕ Bool) (hij : i ≠ j) (x y : E)
    (hx : x ∈ twoProjectionFibers A hDA i) (hy : y ∈ twoProjectionFibers A hDA j) :
    ⟪x, y⟫_𝕜 = 0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact orthogonal_twoProjectionPlanes A hD hDA _ (projectionAxes_orthonormal A hDA)
        _ (projectionAxes_mem A hDA) (projectionAxes_eigen A hDA) (fun h ↦ hij (congrArg Sum.inl h)) hx hy
    | inr j =>
      have hy' := ((twoProjectionFibers_mem_common A hDA hD j y).mp hy).1
      exact (Submodule.mem_orthogonal _ _).mp hy' _ ((twoProjectionPlane_le_span A D (projectionAxes_mem A hDA i)) hx)
  | inr i =>
    cases j with
    | inl j =>
      have hx' := ((twoProjectionFibers_mem_common A hDA hD i x).mp hx).1
      exact (Submodule.mem_orthogonal' _ _).mp hx' _ ((twoProjectionPlane_le_span A D (projectionAxes_mem A hDA j)) hy)
    | inr j =>
      have hDx := ((twoProjectionFibers_mem_common A hDA hD i x).mp hx).2
      have hDy := ((twoProjectionFibers_mem_common A hDA hD j y).mp hy).2
      cases i <;> cases j
      · exact (hij rfl).elim
      · have h := inner_D_apply_complement D hD hDA y x
        simp at hDx hDy
        rw [hDx, hDy, sub_zero] at h
        rw [← inner_conj_symm, h, map_zero]
      · have h := inner_D_apply_complement D hD hDA x y
        simp at hDx hDy
        rwa [hDx, hDy, sub_zero] at h
      · exact (hij rfl).elim

theorem twoProjectionFibers_invariant_D (hD : IsIdempotentElem D)
    (i : Fin (Module.finrank 𝕜 A) ⊕ Bool) (x : E) (hx : x ∈ twoProjectionFibers A hDA i) :
    D x ∈ twoProjectionFibers A hDA i := by
  cases i with
  | inl i => exact D_maps_twoProjectionPlane D hD _ hx
  | inr b =>
    have hx' := ((twoProjectionFibers_mem_common A hDA hD b x).mp hx).2
    rw [hx']
    cases b
    · exact Submodule.zero_mem _
    · exact hx

theorem twoProjectionFibers_invariant_initial (hD : IsIdempotentElem D)
    (i : Fin (Module.finrank 𝕜 A) ⊕ Bool) (x : E) (hx : x ∈ twoProjectionFibers A hDA i) :
    A.starProjection x ∈ twoProjectionFibers A hDA i := by
  cases i with
  | inl i =>
    exact initial_maps_twoProjectionPlane A D (projectionAxes_mem A hDA i)
      (projectionAxes_eigen A hDA i) hx
  | inr b =>
    rw [twoProjectionSpan_orthogonal_initial_zero A D
      ((twoProjectionFibers_mem_common A hDA hD b x).mp hx).1]
    exact Submodule.zero_mem _

end SchauderBasisOrbits


open Matrix ContinuousLinearMap
open scoped BigOperators ComplexOrder InnerProductSpace InnerProduct MatrixOrder
noncomputable section
namespace SchauderBasisOrbits.HilbertTuple

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

theorem rowAction_maps_onSubspace (A : Matrix (Fin n) (Fin n) 𝕜) (K : Submodule 𝕜 E)
    (x : HilbertTuple (Fin n) E) (hx : ∀ i, x i ∈ K) (i : Fin n) : rowAction A x i ∈ K := by
  rw [rowAction_apply]
  exact K.sum_mem (fun j _ ↦ K.smul_mem _ (hx j))

theorem rowCut_maps_onSubspace (j : Fin n) (P : E →L[𝕜] E) (K : Submodule 𝕜 E)
    (hP : ∀ x ∈ K, P x ∈ K) (x : HilbertTuple (Fin n) E) (hx : ∀ i, x i ∈ K) (i : Fin n) :
    rowCut j P x i ∈ K := by
  rw [rowCut_apply]
  split
  · exact hx _
  · split
    · exact hP _ (hx _)
    · exact K.zero_mem

theorem activated_maps_onSubspace (A : Matrix (Fin n) (Fin n) 𝕜) (D : E →L[𝕜] E) (K : Submodule 𝕜 E)
    (hD : ∀ x ∈ K, D x ∈ K) (x : HilbertTuple (Fin n) E) (hx : ∀ i, x i ∈ K) (i : Fin n) :
    activated A D x i ∈ K := by
  change x i + rowAction (A - 1) (diagonalMap D x) i ∈ K
  exact K.add_mem (hx i) (rowAction_maps_onSubspace _ K _ (fun j ↦ hD _ (hx j)) i)

theorem activated_eq_on_common (A : Matrix (Fin n) (Fin n) 𝕜) (D : E →L[𝕜] E)
    (x : HilbertTuple (Fin n) E) (d : Bool)
    (hD : ∀ i, D (x i) = if d then x i else 0) :
    activated A D x = if d then rowAction A x else x := by
  cases d with
  | false =>
      have hz : diagonalMap D x = 0 := by
        ext i
        simpa using hD i
      change x + rowAction (A - 1) (diagonalMap D x) = x
      rw [hz, map_zero, add_zero]
  | true =>
      have hz : diagonalMap D x = x := by
        ext i
        exact hD i
      change x + rowAction (A - 1) (diagonalMap D x) = rowAction A x
      rw [hz, rowAction_sub, rowAction_one, sub_apply]
      change x + (rowAction A x - x) = _
      abel

theorem rowAction_preserves_bool_eigen (A : Matrix (Fin n) (Fin n) 𝕜) (D : E →L[𝕜] E)
    (x : HilbertTuple (Fin n) E) (d : Bool)
    (hD : ∀ i, D (x i) = if d then x i else 0) (i : Fin n) :
    D (rowAction A x i) = if d then rowAction A x i else 0 := by
  rw [rowAction_apply, map_sum]
  simp only [map_smul, hD]
  cases d <;> simp

theorem rowCut_eq_mask_on_common (j : Fin n) (P : E →L[𝕜] E)
    (x : HilbertTuple (Fin n) E) (p : Bool) (hP : ∀ i, P (x i) = if p then x i else 0) :
    rowCut j P x = rowAction (prefixMask 𝕜 (j.val + p.toNat)) x := by
  ext i
  rw [rowCut_apply, rowAction_apply]
  have diag : (∑ k, prefixMask 𝕜 (j.val + p.toNat) i k • x k) =
      if i.val < j.val + p.toNat then x i else 0 := by
    rw [Finset.sum_eq_single i]
    · by_cases hlt : i.val < j.val + p.toNat <;> simp [prefixMask, hlt]
    · intro k _ hk
      simp [prefixMask, Matrix.diagonal_apply_ne _ (Ne.symm hk)]
    · simp
  rw [diag, hP]
  cases p
  · by_cases hi : i < j <;> simp [hi]
  · by_cases hi : i < j
    · have hj : i ≤ j := hi.le
      simp [hi, hj]
    · by_cases heq : i = j
      · simp [heq]
      · have hj : ¬i ≤ j := fun h ↦ hi (lt_of_le_of_ne h heq)
        simp [hi, heq, hj]

theorem rowCut_preserves_bool_eigen (j : Fin n) (P D : E →L[𝕜] E)
    (x : HilbertTuple (Fin n) E) (p d : Bool)
    (hP : ∀ i, P (x i) = if p then x i else 0)
    (hD : ∀ i, D (x i) = if d then x i else 0) (i : Fin n) :
    D (rowCut j P x i) = if d then rowCut j P x i else 0 := by
  rw [rowCut_eq_mask_on_common _ _ _ _ hP]
  exact rowAction_preserves_bool_eigen _ _ _ _ hD _

variable [CompleteSpace E]

set_option maxHeartbeats 500000 in
/-- Full-row cut on the common eigenspaces of the two fiber projections. -/
theorem norm_activated_rowCut_common_le
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.PosDef) (D : E →L[𝕜] E)
    (hD : IsIdempotentElem D) (P : E →L[𝕜] E) (j : Fin n) (p d : Bool)
    (x : HilbertTuple (Fin n) E)
    (hxP : ∀ i, P (x i) = if p then x i else 0)
    (hxD : ∀ i, D (x i) = if d then x i else 0) :
    let S := activatedSqrtEquiv B hB D hD
    let C := CFC.sqrt B * prefixMask 𝕜 (j.val + p.toNat) * (CFC.sqrt B)⁻¹
    ‖S (rowCut j P (S.symm x))‖ ≤ max 1 (opNorm C) * ‖x‖ := by
  let S := activatedSqrtEquiv B hB D hD
  let R := CFC.sqrt B
  let Q := (CFC.sqrt B)⁻¹
  let M := prefixMask (n := n) 𝕜 (j.val + p.toNat)
  let C := R * M * Q
  change ‖S (rowCut j P (S.symm x))‖ ≤ max 1 (opNorm C) * ‖x‖
  have hs : S.toContinuousLinearMap = activated R D := activatedSqrtEquiv_forward B hB D hD
  have hsi : S.symm.toContinuousLinearMap = activated Q D := activatedSqrtEquiv_inverse B hB D hD
  change ‖S.toContinuousLinearMap (rowCut j P (S.symm.toContinuousLinearMap x))‖ ≤ _
  rw [hs, hsi, activated_eq_on_common Q D x d hxD]
  cases d with
  | false =>
      have hpres : ∀ i, D (rowCut j P x i) = if false then rowCut j P x i else 0 :=
        rowCut_preserves_bool_eigen _ _ _ _ p false hxP hxD
      change ‖activated R D (rowCut j P x)‖ ≤ _
      rw [activated_eq_on_common _ _ _ false hpres, rowCut_eq_mask_on_common _ _ _ _ hxP]
      change ‖rowAction M x‖ ≤ _
      have ht : ‖rowAction M x‖ ≤ ‖x‖ := by
        apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        simp only [PiLp.norm_sq_eq_of_L2, rowAction_apply]
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.sum_eq_single i]
        · by_cases hi : i.val < j.val + p.toNat <;> simp [M, prefixMask, hi]
        · intro k _ hk
          simp [M, prefixMask, Matrix.diagonal_apply_ne _ (Ne.symm hk)]
        · simp
      exact ht.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (opNorm C)) (norm_nonneg x))
  | true =>
      have hDP (i : Fin n) : P (rowAction Q x i) = if p then rowAction Q x i else 0 :=
        rowAction_preserves_bool_eigen _ _ _ _ hxP _
      have hDD (i : Fin n) : D (rowAction Q x i) = if true then rowAction Q x i else 0 :=
        rowAction_preserves_bool_eigen _ _ _ _ hxD _
      have hpres (i : Fin n) : D (rowCut j P (rowAction Q x) i) = if true then _ else 0 :=
        rowCut_preserves_bool_eigen _ _ _ _ p true hDP hDD i
      change ‖activated R D (rowCut j P (rowAction Q x))‖ ≤ _
      rw [activated_eq_on_common _ _ _ true hpres, rowCut_eq_mask_on_common _ _ _ _ hDP]
      change ‖rowAction R (rowAction M (rowAction Q x))‖ ≤ _
      have heq : rowAction R (rowAction M (rowAction Q x)) = rowAction C x := by
        let rop (A : Matrix (Fin n) (Fin n) 𝕜) : HilbertTuple (Fin n) E →L[𝕜] HilbertTuple (Fin n) E :=
          rowAction A
        change (rop R * rop M * rop Q) x = rop C x
        dsimp only [rop]
        rw [← rowAction_mul, ← rowAction_mul]
      rw [heq]
      have hr : ‖(rowAction C : HilbertTuple (Fin n) E →L[𝕜] HilbertTuple (Fin n) E)‖ ≤ opNorm C :=
        norm_rowAction_le C
      exact ((rowAction C : HilbertTuple (Fin n) E →L[𝕜] HilbertTuple (Fin n) E).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hr.trans (le_max_right _ _)) (norm_nonneg x))

end SchauderBasisOrbits.HilbertTuple


open Matrix
open scoped BigOperators InnerProductSpace
noncomputable section
namespace SchauderBasisOrbits

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

private theorem norm_sq_sum_unit (c : Fin n ⊕ Unit → 𝕜) :
    ‖WithLp.toLp 2 c‖ ^ 2 =
      ‖WithLp.toLp 2 (c ∘ Sum.inl)‖ ^ 2 + ‖c (Sum.inr ())‖ ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Function.comp_apply]

private theorem norm_sq_prefix_add_single (j : Fin n) (b : Fin n → 𝕜) (a : 𝕜) :
    ‖WithLp.toLp 2 (truncCoeff j.val b + Pi.single j a)‖ ^ 2 =
      ‖WithLp.toLp 2 (truncCoeff j.val b)‖ ^ 2 + ‖a‖ ^ 2 := by
  let p := WithLp.toLp 2 (truncCoeff j.val b)
  let v := WithLp.toLp 2 (Pi.single j a : Fin n → 𝕜)
  have hi : ⟪p, v⟫_𝕜 = 0 := by
    dsimp only [p, v]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [truncCoeff]
  have hn : ‖v‖ ^ 2 = ‖a‖ ^ 2 := by
    simp [v]
  change ‖p + v‖ ^ 2 = ‖p‖ ^ 2 + ‖a‖ ^ 2
  rw [norm_add_sq (𝕜 := 𝕜), hi, map_zero, mul_zero, add_zero, hn]

private theorem norm_sq_prefix_le (k : ℕ) (b : Fin n → 𝕜) :
    ‖WithLp.toLp 2 (truncCoeff k b)‖ ^ 2 ≤ ‖WithLp.toLp 2 b‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < k <;> simp [truncCoeff, hi]

private theorem prefix_succ_eq_add_single (j : Fin n) (b : Fin n → 𝕜) :
    truncCoeff (j.val + 1) b = truncCoeff j.val b + Pi.single j (b j) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [truncCoeff]
  · have hlt : i ≤ j ↔ i < j := ⟨fun h ↦ lt_of_le_of_ne h hij, le_of_lt⟩
    simp [truncCoeff, hij, hlt]

/-- Removing the later entries in the second component only improves the norm bound.
The operator on the first component and the one active scalar is the row slice. -/
theorem rowSlice_coefficients_norm_sq_le {T : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) 𝕜}
    (j : Fin n) (a b : Fin n → 𝕜) {L : ℝ} (hL : 1 ≤ L) (hT : opNorm T ^ 2 ≤ L) :
    let w := T *ᵥ (Sum.elim a (fun _ ↦ b j))
    ‖WithLp.toLp 2 (w ∘ Sum.inl)‖ ^ 2 +
      ‖WithLp.toLp 2 (truncCoeff j.val b + Pi.single j (w (Sum.inr ())))‖ ^ 2 ≤
      L * (‖WithLp.toLp 2 a‖ ^ 2 + ‖WithLp.toLp 2 b‖ ^ 2) := by
  let z := Sum.elim a (fun _ : Unit ↦ b j)
  let w := T *ᵥ z
  change ‖WithLp.toLp 2 (w ∘ Sum.inl)‖ ^ 2 +
      ‖WithLp.toLp 2 (truncCoeff j.val b + Pi.single j (w (Sum.inr ())))‖ ^ 2 ≤ _
  rw [norm_sq_prefix_add_single]
  have hz := norm_sq_sum_unit z
  change ‖WithLp.toLp 2 z‖ ^ 2 = ‖WithLp.toLp 2 a‖ ^ 2 + ‖b j‖ ^ 2 at hz
  have hTnorm := (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := Fin n ⊕ Unit) T).le_opNorm (WithLp.toLp 2 z)
  rw [Matrix.toEuclideanCLM_toLp, ← opNorm_square_eq] at hTnorm
  have hNorm := pow_le_pow_left₀ (norm_nonneg _) hTnorm 2
  rw [mul_pow] at hNorm
  have hBound : ‖WithLp.toLp 2 w‖ ^ 2 ≤ L * (‖WithLp.toLp 2 a‖ ^ 2 + ‖b j‖ ^ 2) := by
    rw [← hz]
    exact hNorm.trans (mul_le_mul_of_nonneg_right hT (sq_nonneg _))
  have hb := norm_sq_prefix_le (j.val + 1) b
  rw [prefix_succ_eq_add_single, norm_sq_prefix_add_single] at hb
  calc
    _ = ‖WithLp.toLp 2 (truncCoeff j.val b)‖ ^ 2 + ‖WithLp.toLp 2 w‖ ^ 2 := by
      rw [norm_sq_sum_unit]
      ring
    _ ≤ L * ‖WithLp.toLp 2 (truncCoeff j.val b)‖ ^ 2 +
        L * (‖WithLp.toLp 2 a‖ ^ 2 + ‖b j‖ ^ 2) :=
      add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (sq_nonneg _)) hBound
    _ = L * (‖WithLp.toLp 2 a‖ ^ 2 +
        (‖WithLp.toLp 2 (truncCoeff j.val b)‖ ^ 2 + ‖b j‖ ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hb) (zero_le_one.trans hL)

end SchauderBasisOrbits


open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section
namespace SchauderBasisOrbits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexify_sqrt {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    complexify (CFC.sqrt A) = CFC.sqrt (complexify A) := by
  symm
  refine (CFC.sqrt_eq_iff _ _ (posSemidef_complexify hA).nonneg
    (posSemidef_complexify (CFC.sqrt_nonneg A).posSemidef).nonneg).mpr ?_
  rw [← complexify_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem complexify_inv_eq {A : Matrix ι ι ℝ} (hA : IsUnit A) :
    complexify A⁻¹ = (complexify A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← complexify_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    complexify_one]

omit [Fintype ι] [DecidableEq ι] in
theorem complexify_transpose {κ : Type*} (A : Matrix ι κ ℝ) :
    complexify Aᵀ = (complexify A)ᵀ := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem complexify_add {κ : Type*} (A B : Matrix ι κ ℝ) :
    complexify (A + B) = complexify A + complexify B := by
  ext i j
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem complexify_real_smul {κ : Type*} (a : ℝ) (A : Matrix ι κ ℝ) :
    complexify (a • A) = (a : ℂ) • complexify A := by
  ext i j
  simp [smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem complexify_vecMulVec (x y : ι → ℝ) :
    complexify (Matrix.vecMulVec x y) = Matrix.vecMulVec (Complex.ofReal ∘ x) (Complex.ofReal ∘ y) := by
  ext i j
  simp [Matrix.vecMulVec_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem complexify_replicateCol (x : ι → ℝ) :
    complexify (Matrix.replicateCol Unit x) = Matrix.replicateCol Unit (Complex.ofReal ∘ x) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem complexify_fromBlocks {κ : Type*} (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) :
    complexify (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (complexify A) (complexify B) (complexify C) (complexify D) := by
  ext i j
  cases i <;> cases j <;> rfl

variable {n : ℕ}

theorem complexify_prefixMask (k : ℕ) :
    complexify (prefixMask (n := n) ℝ k) = prefixMask (n := n) ℂ k := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < k <;> simp [prefixMask, hi]
  · simp [prefixMask, hij]

private theorem complexify_mulVec_single (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (Complex.ofReal ∘ (M *ᵥ (Pi.single j 1))) = complexify M *ᵥ (Pi.single j 1) := by
  funext i
  simp [Function.comp_apply]

private theorem vecMulVec_mulVec_complex (x y z : Fin n → ℂ) :
    Matrix.vecMulVec x y *ᵥ z = (dotProduct y z) • x := by
  rw [Matrix.vecMulVec_mulVec]
  funext i
  exact mul_comm _ _

/-- The row slice agrees with the active coefficients of a complete block row. -/
theorem complexify_gramRowSlice_mulVec (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (t : ℝ) (c : Fin n → ℂ) (b : ℂ) :
    let R := complexify (CFC.sqrt B)
    let Q := complexify ((CFC.sqrt B)⁻¹)
    let a := Q *ᵥ c
    let s := Real.sqrt (t * (1 - t))
    let w := (complexify (gramRowSlice B j t)) *ᵥ (Sum.elim c (fun _ ↦ b))
    (w ∘ Sum.inl) = R *ᵥ (truncCoeff j.val a + Pi.single j ((t : ℂ) * a j + (s : ℂ) * b)) ∧
    w (Sum.inr ()) = (s : ℂ) * a j + ((1 - t : ℝ) : ℂ) * b := by
  dsimp only
  let R := complexify (CFC.sqrt B)
  let Q := complexify ((CFC.sqrt B)⁻¹)
  let e : Fin n → ℂ := Pi.single j 1
  let a := Q *ᵥ c
  let s := Real.sqrt (t * (1 - t))
  let x := R *ᵥ e
  let y := Q *ᵥ e
  have hH : ((CFC.sqrt B)⁻¹)ᵀ = (CFC.sqrt B)⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact ((CFC.sqrt_nonneg B).posSemidef.isHermitian.inv).eq
  have hQ : Qᵀ = Q := by
    change (complexify ((CFC.sqrt B)⁻¹))ᵀ = _
    rw [← complexify_transpose, hH]
  have hdot : dotProduct y c = a j := by
    change dotProduct (Q *ᵥ e) c = _
    have eQ : e ᵥ* Q = Q *ᵥ e := by simpa only [hQ] using Matrix.vecMul_transpose Q e
    rw [← eQ, ← Matrix.dotProduct_mulVec]
    simp [e, a]
  have hform : complexify (gramRowSlice B j t) =
      Matrix.fromBlocks (R * prefixMask ℂ j.val * Q + (t : ℂ) • Matrix.vecMulVec x y)
        ((s : ℂ) • Matrix.replicateCol Unit x) ((s : ℂ) • (Matrix.replicateCol Unit y)ᵀ)
        (((1 - t : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) := by
    unfold gramRowSlice partialRowProjection
    simp only [complexify_fromBlocks, complexify_add, complexify_mul, complexify_real_smul,
      complexify_vecMulVec, complexify_prefixMask, complexify_mulVec_single,
      complexify_replicateCol, complexify_transpose, complexify_one, R, Q, x, y, e, s]
  rw [hform, Matrix.fromBlocks_mulVec]
  have hsca : (Matrix.replicateCol Unit x) *ᵥ (fun _ ↦ b) = b • x := by
    funext i
    simp [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]
  have hsca' : ((Matrix.replicateCol Unit y)ᵀ *ᵥ c) () = a j := by
    rw [← hdot]
    simp [Matrix.mulVec, dotProduct]
  have heq (z : ℂ) : Pi.single j z = z • e := by
    funext i
    by_cases hi : i = j <;> simp [e, hi]
  constructor
  · change ((R * prefixMask ℂ j.val * Q + (t : ℂ) • Matrix.vecMulVec x y) *ᵥ c +
        ((s : ℂ) • Matrix.replicateCol Unit x) *ᵥ (fun _ ↦ b)) =
      R *ᵥ (truncCoeff j.val a + Pi.single j ((t : ℂ) * a j + (s : ℂ) * b))
    have hp : R *ᵥ truncCoeff j.val a = (R * prefixMask ℂ j.val * Q) *ᵥ c := by
      rw [← prefixMask_mulVec]
      change R *ᵥ (prefixMask ℂ j.val *ᵥ (Q *ᵥ c)) = _
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec_complex,
      hdot, hsca, heq, Matrix.mulVec_add, Matrix.mulVec_smul, hp]
    change (R * prefixMask ℂ j.val * Q) *ᵥ c + (t : ℂ) • a j • x + (s : ℂ) • b • x =
      (R * prefixMask ℂ j.val * Q) *ᵥ c + ((t : ℂ) * a j + (s : ℂ) * b) • x
    rw [smul_smul, smul_smul, add_smul, add_assoc]
  · change ((((s : ℂ) • (Matrix.replicateCol Unit y)ᵀ) *ᵥ c) +
      ((((1 - t : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) *ᵥ (fun _ ↦ b))) () = _
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsca']

end SchauderBasisOrbits


open ContinuousLinearMap
open scoped BigOperators InnerProductSpace
noncomputable section
namespace SchauderBasisOrbits.HilbertTuple

variable {𝕜 E ι σ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [Fintype ι] [Fintype σ]

/-- Assemble a dimension-independent bound using orthogonal reducing fiber spaces. -/
theorem opNorm_le_of_fiber_decomposition (F : HilbertTuple ι E →L[𝕜] HilbertTuple ι E)
    (K : σ → Submodule 𝕜 E)
    (hdecomp : ∀ x : E, ∃ w : σ → E, (∀ α, w α ∈ K α) ∧ (∑ α, w α) = x)
    (hortho : ∀ i j : σ, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, ⟪x, y⟫_𝕜 = 0)
    (hreduces : ∀ α x, (∀ i, x i ∈ K α) → ∀ i, F x i ∈ K α)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ α x, (∀ i, x i ∈ K α) → ‖F x‖ ≤ M * ‖x‖) :
    ‖F‖ ≤ M := by
  refine F.opNorm_le_bound hM fun x ↦ ?_
  choose w hw heq using fun i : ι ↦ hdecomp (x i)
  let pieces (α : σ) : HilbertTuple ι E := WithLp.toLp 2 fun i ↦ w i α
  have hp : (∑ α, pieces α) = x := by
    ext i
    simpa [pieces, WithLp.ofLp_sum, Finset.sum_apply] using heq i
  have hK (α : σ) (i : ι) : (pieces α) i ∈ K α := hw i α
  rw [← hp]
  refine norm_linearMap_sum_le_of_orthogonal F pieces ?_ ?_ hM (fun α ↦ hbound α _ (hK α))
  · intro α β hab
    rw [PiLp.inner_apply]
    exact Finset.sum_eq_zero fun i _ ↦ hortho α β hab _ (hK α i) _ (hK β i)
  · intro α β hab
    rw [PiLp.inner_apply]
    exact Finset.sum_eq_zero fun i _ ↦ hortho α β hab _ (hreduces α _ (hK α) i) _
      (hreduces β _ (hK β) i)

end SchauderBasisOrbits.HilbertTuple


open Matrix ContinuousLinearMap
open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace SchauderBasisOrbits.HilbertTuple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {n : ℕ}

omit [CompleteSpace E] in
/-- The cut acts on a two-dimensional fiber plane through the real row-slice matrix,
plus unaffected earlier coordinates in the kernel component. -/
theorem norm_activated_rowCut_plane_sq_le
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (D : E →L[ℂ] E)
    (hD : IsIdempotentElem D) (P : E →L[ℂ] E) (j : Fin n)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℂ = 0)
    (hDu : D u = u) (hDv : D v = 0) (a b : Fin n → ℂ)
    {t : ℝ}
    (hPu : P u = (t : ℂ) • u + (Real.sqrt (t * (1 - t)) : ℂ) • v)
    (hPv : P v = (Real.sqrt (t * (1 - t)) : ℂ) • u + ((1 - t : ℝ) : ℂ) • v)
    {L : ℝ} (hL : 1 ≤ L) (hSlice : opNorm (gramRowSlice B j t) ^ 2 ≤ L) :
    let S := activatedSqrtEquiv (complexify B) (posDef_complexify hB) D hD
    ‖S (rowCut j P (S.symm (ofPlane u v a b)))‖ ^ 2 ≤ L * ‖ofPlane u v a b‖ ^ 2 := by
  let S := activatedSqrtEquiv (complexify B) (posDef_complexify hB) D hD
  let R := complexify (CFC.sqrt B)
  let Q := complexify ((CFC.sqrt B)⁻¹)
  let a' := Q *ᵥ a
  let s := Real.sqrt (t * (1 - t))
  let z := Sum.elim a (fun _ : Unit ↦ b j)
  let w := (complexify (gramRowSlice B j t)) *ᵥ z
  have hroot : CFC.sqrt (complexify B) = R := (complexify_sqrt hB.posSemidef).symm
  have hrootInv : (CFC.sqrt (complexify B))⁻¹ = Q :=
    (congrArg Inv.inv hroot).trans (complexify_inv_eq (posDef_sqrt hB).isUnit).symm
  have hS : S.toContinuousLinearMap = activated R D :=
    (activatedSqrtEquiv_forward (complexify B) (posDef_complexify hB) D hD).trans
      (congrArg (fun M ↦ activated M D) hroot)
  have hSi : S.symm.toContinuousLinearMap = activated Q D :=
    (activatedSqrtEquiv_inverse (complexify B) (posDef_complexify hB) D hD).trans
      (congrArg (fun M ↦ activated M D) hrootInv)
  let f := ofPlane u v a b
  have hInput : S.symm f = ofPlane u v a' b :=
    (DFunLike.congr_fun hSi f).trans (activated_ofPlane Q D u v hDu hDv a b)
  let ca := truncCoeff j.val a' + Pi.single j ((t : ℂ) * a' j + (s : ℂ) * b j)
  let cb := truncCoeff j.val b + Pi.single j ((s : ℂ) * a' j + ((1 - t : ℝ) : ℂ) * b j)
  have hCut : rowCut j P (ofPlane u v a' b) = ofPlane u v ca cb :=
    rowCut_ofPlane j P u v a' b hPu hPv
  have hCutApply : rowCut j P (S.symm f) = ofPlane u v ca cb :=
    (congrArg (rowCut j P) hInput).trans hCut
  have hOut : S (rowCut j P (S.symm f)) = ofPlane u v (R *ᵥ ca) cb := calc
    _ = S (ofPlane u v ca cb) := congrArg S hCutApply
    _ = activated R D (ofPlane u v ca cb) := DFunLike.congr_fun hS _
    _ = _ := activated_ofPlane R D u v hDu hDv ca cb
  have hf := complexify_gramRowSlice_mulVec B j t a (b j)
  have hfa : w ∘ Sum.inl = R *ᵥ ca := hf.1
  have hfb : w (Sum.inr ()) = (s : ℂ) * a' j + ((1 - t : ℝ) : ℂ) * b j := hf.2
  have hcb : cb = truncCoeff j.val b + Pi.single j (w (Sum.inr ())) :=
    congrArg (fun x ↦ truncCoeff j.val b + Pi.single j x) hfb.symm
  change ‖S (rowCut j P (S.symm f))‖ ^ 2 ≤ L * ‖f‖ ^ 2
  have hFn : ‖f‖ ^ 2 = ‖WithLp.toLp 2 a‖ ^ 2 + ‖WithLp.toLp 2 b‖ ^ 2 :=
    norm_sq_ofPlane u v hu hv huv a b
  calc
    _ = ‖WithLp.toLp 2 (w ∘ Sum.inl)‖ ^ 2 +
        ‖WithLp.toLp 2 (truncCoeff j.val b + Pi.single j (w (Sum.inr ())))‖ ^ 2 := by
      rw [hOut, norm_sq_ofPlane _ _ hu hv huv, ← hfa, hcb]
    _ ≤ _ := hFn.symm ▸ rowSlice_coefficients_norm_sq_le j a b hL (by
      simpa only [opNorm_complexify] using hSlice)

end SchauderBasisOrbits.HilbertTuple


open Matrix ContinuousLinearMap Submodule
open scoped BigOperators ComplexOrder InnerProductSpace InnerProduct MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace SchauderBasisOrbits

variable {n : ℕ}

/-- Uniform squared norm bound for a cut inside one activated row. -/
def activatedRowCutBound (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  max (gramPrefixNormSq B j.val) (gramPrefixNormSq B (j.val + 1)) +
    (1 - B j j) * (B⁻¹ j j - 1) / 4

private theorem rowCorrection_nonneg {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (hB₁ : B ≤ 1)
    (j : Fin n) : 0 ≤ (1 - B j j) * (B⁻¹ j j - 1) := by
  let e : Fin n → ℝ := Pi.single j 1
  have ha : B j j ≤ 1 := by simpa [qform, e] using qform_mono hB₁ e
  have h := matrix_inv_le_inv hB hB₁
  rw [inv_one] at h
  have hb : 1 ≤ B⁻¹ j j := by simpa [qform, e] using qform_mono h e
  exact mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)

theorem one_le_activatedRowCutBound {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (hB₁ : B ≤ 1)
    (j : Fin n) : 1 ≤ activatedRowCutBound B j := by
  have h := rowCorrection_nonneg hB hB₁ j
  unfold activatedRowCutBound
  exact (le_max_left 1 _).trans ((le_max_left _ _).trans (le_add_of_nonneg_right (by positivity)))

theorem gramRowSlice_uniform_norm_sq_le {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) (hB₁ : B ≤ 1) (j : Fin n) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    opNorm (gramRowSlice B j t) ^ 2 ≤ activatedRowCutBound B j := by
  refine (gramRowSlice_norm_sq_le hB hB₁ j ht ht').trans ?_
  unfold activatedRowCutBound
  have h := rowCorrection_nonneg hB hB₁ j
  have htq : t * (1 - t) ≤ 1 / 4 := by nlinarith only [sq_nonneg (t - 1 / 2)]
  have hp := mul_le_mul_of_nonneg_right htq h
  linarith only [hp]

private theorem max_complex_metricNorm_le_sqrt_row_bound {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosDef) (hB₁ : B ≤ 1) (j : Fin n) (p : Bool) :
    let C := CFC.sqrt (complexify B) * prefixMask ℂ (j.val + p.toNat) * (CFC.sqrt (complexify B))⁻¹
    max 1 (opNorm C) ≤ Real.sqrt (activatedRowCutBound B j) := by
  dsimp only
  have h₁ := one_le_activatedRowCutBound hB hB₁ j
  have h₀ : 0 ≤ activatedRowCutBound B j := zero_le_one.trans h₁
  apply max_le
  · calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h₁
  · rw [← complexify_sqrt hB.posSemidef, ← complexify_inv_eq (posDef_sqrt hB).isUnit,
      ← complexify_prefixMask, ← complexify_mul, ← complexify_mul, opNorm_complexify]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt h₀]
    apply (le_max_right (1 : ℝ) _).trans
    change gramPrefixNormSq B (j.val + p.toNat) ≤ activatedRowCutBound B j
    unfold activatedRowCutBound
    have h := rowCorrection_nonneg hB hB₁ j
    have hprefix : gramPrefixNormSq B (j.val + p.toNat) ≤
        max (gramPrefixNormSq B j.val) (gramPrefixNormSq B (j.val + 1)) := by
      cases p
      · exact le_max_left (gramPrefixNormSq B j.val) (gramPrefixNormSq B (j.val + 1))
      · exact le_max_right (gramPrefixNormSq B j.val) (gramPrefixNormSq B (j.val + 1))
    exact hprefix.trans (le_add_of_nonneg_right (div_nonneg h (by norm_num)))

namespace HilbertTuple
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A06: the sharp row cut bound for an arbitrary finite-rank first fiber projection. -/
theorem opNorm_activated_rowCut_sq_le
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (hB₁ : B ≤ 1)
    (D : E →L[ℂ] E) (hD : IsIdempotentElem D) (hDA : D† = D)
    (A : Submodule ℂ E) [FiniteDimensional ℂ A] (j : Fin n) :
    let S := activatedSqrtEquiv (complexify B) (posDef_complexify hB) D hD
    ‖S.toContinuousLinearMap ∘L rowCut j A.starProjection ∘L S.symm.toContinuousLinearMap‖ ^ 2 ≤
      activatedRowCutBound B j := by
  let S := activatedSqrtEquiv (complexify B) (posDef_complexify hB) D hD
  let P := A.starProjection
  let F := S.toContinuousLinearMap ∘L rowCut j P ∘L S.symm.toContinuousLinearMap
  let K := twoProjectionFibers A hDA
  let L := activatedRowCutBound B j
  have hL : 1 ≤ L := one_le_activatedRowCutBound hB hB₁ j
  have hLn : 0 ≤ L := zero_le_one.trans hL
  change ‖F‖ ^ 2 ≤ L
  rw [← Real.sq_sqrt hLn]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  refine opNorm_le_of_fiber_decomposition F K (twoProjectionFibers_decomp A hDA hD)
    (fun i j hij x hx y hy ↦ twoProjectionFibers_orthogonal A hDA hD i j hij x y hx hy)
    ?_ (Real.sqrt_nonneg _) ?_
  · intro α x hx i
    change S.toContinuousLinearMap (rowCut j P (S.symm.toContinuousLinearMap x)) i ∈ K α
    rw [activatedSqrtEquiv_forward, activatedSqrtEquiv_inverse]
    apply activated_maps_onSubspace _ _ _ (twoProjectionFibers_invariant_D A hDA hD α)
    intro l
    apply rowCut_maps_onSubspace _ _ _ (twoProjectionFibers_invariant_initial A hDA hD α)
    intro k
    exact activated_maps_onSubspace _ _ _ (twoProjectionFibers_invariant_D A hDA hD α) _ hx _
  · have hCommon (x : HilbertTuple (Fin n) E) (p d : Bool)
        (hxP : ∀ i, P (x i) = if p then x i else 0)
        (hxD : ∀ i, D (x i) = if d then x i else 0) : ‖F x‖ ≤ Real.sqrt L * ‖x‖ := by
      have ht := norm_activated_rowCut_common_le (complexify B) (posDef_complexify hB) D hD P j
        p d x hxP hxD
      exact ht.trans (mul_le_mul_of_nonneg_right (max_complex_metricNorm_le_sqrt_row_bound hB hB₁ j p)
        (norm_nonneg x))
    rintro (α | b) x hx
    · let w := projectionAxes A hDA α
      let t := projectionEigenvalues A hDA α
      have hE : P (D w) = (t : ℂ) • w := projectionAxes_eigen A hDA α
      have hw : w ∈ A := projectionAxes_mem A hDA α
      have hwn : ‖w‖ = 1 := (projectionAxes_orthonormal A hDA).1 α
      have hT : 0 ≤ t ∧ t ≤ 1 :=
        projection_eigenvalue_bounds A hD hDA _ (projectionAxes_orthonormal A hDA) _
          (projectionAxes_mem A hDA) (projectionAxes_eigen A hDA) α
      have hPaxis : P w = w := Submodule.starProjection_eq_self_iff.mpr hw
      have hOff (h : t = 0 ∨ t = 1) : projectionPlaneOff D w t = 0 :=
        projectionPlaneOff_zero_at_endpoint A hD hDA _ (projectionAxes_orthonormal A hDA) _
          (projectionAxes_mem A hDA) (projectionAxes_eigen A hDA) α h
      by_cases h0 : t = 0
      · have hDw : D w = 0 := by simpa [projectionPlaneOff, h0] using hOff (Or.inl h0)
        apply hCommon x true false
        · intro i
          obtain ⟨c, d, he⟩ := (mem_twoProjectionPlane_iff D w (x i)).mp (hx i)
          rw [← he]
          simp [hDw, hPaxis]
        · intro i
          obtain ⟨c, d, he⟩ := (mem_twoProjectionPlane_iff D w (x i)).mp (hx i)
          rw [← he]
          simp [hDw]
      · by_cases h1 : t = 1
        · have hDw : D w = w := sub_eq_zero.mp (by simpa [projectionPlaneOff, h1] using hOff (Or.inr h1))
          apply hCommon x true true
          · intro i
            obtain ⟨c, d, he⟩ := (mem_twoProjectionPlane_iff D w (x i)).mp (hx i)
            rw [← he]
            simp [hDw, hPaxis]
          · intro i
            obtain ⟨c, d, he⟩ := (mem_twoProjectionPlane_iff D w (x i)).mp (hx i)
            rw [← he]
            simp [hDw]
        · have ht : 0 < t := lt_of_le_of_ne hT.1 (Ne.symm h0)
          have ht' : t < 1 := lt_of_le_of_ne hT.2 h1
          obtain ⟨u, v, hu, hv, huv, hDu, hDv, huco, hvco, hPu, hPv⟩ :=
            twoProjection_D_basis A hD hDA hw hwn ht ht' hE
          have hh (i : Fin n) := (mem_twoProjectionPlane_iff D w (x i)).mp (hx i)
          choose c d hcd using hh
          let c' := fun i ↦ c i * (Real.sqrt t : ℂ)
          let d' := fun i ↦ d i * (Real.sqrt (1 - t) : ℂ)
          have hx' : x = ofPlane u v c' d' := by
            ext i
            rw [ofPlane_apply, ← hcd i, hvco, huco, smul_smul, smul_smul]
            rfl
          apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
          rw [mul_pow, Real.sq_sqrt hLn, hx']
          exact norm_activated_rowCut_plane_sq_le B hB D hD P j u v hu hv huv hDu hDv c' d'
            hPu hPv hL (gramRowSlice_uniform_norm_sq_le hB hB₁ j ht.le ht'.le)
    · apply hCommon x false b
      · intro i
        exact twoProjectionSpan_orthogonal_initial_zero A D
          ((twoProjectionFibers_mem_common A hDA hD b _).mp (hx i)).1
      · intro i
        exact ((twoProjectionFibers_mem_common A hDA hD b _).mp (hx i)).2

end HilbertTuple
end SchauderBasisOrbits
