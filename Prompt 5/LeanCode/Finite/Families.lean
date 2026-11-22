module

public import LeanCode.Finite.Matrix

@[expose] public section

/-! Ordered finite sums, coefficient masks, and their Gram forms. -/

open Matrix Submodule
open scoped BigOperators ComplexOrder InnerProductSpace MatrixOrder

noncomputable section

namespace SchauderBasisOrbits

variable {𝕜 E α : Type*} [RCLike 𝕜]
variable {n m : ℕ}

/-- Synthesis with finitely many coefficients. -/
def synth [AddCommMonoid E] [Module 𝕜 E] (v : Fin n → E) (c : Fin n → 𝕜) : E :=
  ∑ i, c i • v i

/-- Zero all coefficients at or after the ordered cut. -/
def truncCoeff (k : ℕ) (c : Fin n → 𝕜) : Fin n → 𝕜 :=
  fun i ↦ if i.val < k then c i else 0

@[simp] theorem truncCoeff_zero (c : Fin n → 𝕜) : truncCoeff 0 c = 0 := by
  ext i
  simp [truncCoeff]

theorem truncCoeff_eq_self (c : Fin n → 𝕜) {k : ℕ} (hk : n ≤ k) :
    truncCoeff k c = c := by
  ext i
  simp [truncCoeff, lt_of_lt_of_le i.isLt hk]

@[simp] theorem truncCoeff_full (c : Fin n → 𝕜) : truncCoeff n c = c :=
  truncCoeff_eq_self c le_rfl

@[simp] theorem synth_zero [AddCommMonoid E] [Module 𝕜 E] (v : Fin n → E) :
    synth v (0 : Fin n → 𝕜) = 0 := by simp [synth]

@[simp] theorem synth_single [AddCommMonoid E] [Module 𝕜 E] (v : Fin n → E)
    (j : Fin n) (a : 𝕜) : synth v (Pi.single j a) = a • v j := by
  rw [synth, Finset.sum_eq_single j]
  · simp
  · simp_all
  · simp

/-- Matrix of the coefficient truncation in the standard basis. -/
def prefixMask (𝕜 : Type*) [Zero 𝕜] [One 𝕜] (k : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.diagonal fun i ↦ if i.val < k then 1 else 0

theorem prefixMask_isHermitian (k : ℕ) : (prefixMask (n := n) 𝕜 k).IsHermitian := by
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext i
  by_cases hi : i.val < k <;> simp [hi]

@[simp] theorem prefixMask_mulVec (k : ℕ) (c : Fin n → 𝕜) :
    prefixMask 𝕜 k *ᵥ c = truncCoeff k c := by
  funext i
  rw [prefixMask, Matrix.mulVec_diagonal]
  by_cases hi : i.val < k <;> simp [truncCoeff, hi]

section Hilbert

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every coordinate prefix has norm at most K on the synthesis of a finite family. -/
def HPrefix (v : Fin n → E) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (k : ℕ), k ≤ n → ∀ c : Fin n → 𝕜,
    ‖synth v (truncCoeff k c)‖ ≤ K * ‖synth v c‖

theorem HPrefix.mono {v : Fin n → E} {K L : ℝ} (h : HPrefix (𝕜 := 𝕜) v K) (hKL : K ≤ L) :
    HPrefix (𝕜 := 𝕜) v L :=
  ⟨h.1.trans hKL, fun k hk c ↦ (h.2 k hk c).trans
    (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))⟩

theorem HPrefix.one_le_of_nonzero {v : Fin n → E} {K : ℝ} (h : HPrefix (𝕜 := 𝕜) v K)
    {i : Fin n} (hi : v i ≠ 0) : 1 ≤ K := by
  have ht := h.2 n le_rfl (Pi.single i (1 : 𝕜))
  simp only [truncCoeff_full, synth_single, one_smul] at ht
  exact le_of_mul_le_mul_right (by simpa only [one_mul] using ht) (norm_pos_iff.mpr hi)

theorem HPrefix.one_le {v : Fin (n + 1) → E} {K : ℝ} (h : HPrefix (𝕜 := 𝕜) v K)
    (hv : LinearIndependent 𝕜 v) : 1 ≤ K :=
  h.one_le_of_nonzero (hv.ne_zero 0)

/-- The synthesis map on Euclidean coefficients. -/
def synthCLM (v : Fin n → E) : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E :=
  LinearMap.toContinuousLinearMap
    ((Fintype.linearCombination 𝕜 v).comp (WithLp.linearEquiv 2 𝕜 _).toLinearMap)

@[simp] theorem synthCLM_apply (v : Fin n → E) (c : EuclideanSpace 𝕜 (Fin n)) :
    synthCLM v c = synth v (WithLp.ofLp c) := by
  simp [synthCLM, synth, Fintype.linearCombination_apply]

theorem range_synthCLM (v : Fin n → E) :
    LinearMap.range (synthCLM v).toLinearMap = Submodule.span 𝕜 (Set.range v) := by
  ext x
  rw [← Fintype.range_linearCombination]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨WithLp.ofLp c, by simpa [synth, Fintype.linearCombination_apply] using hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨WithLp.toLp 2 c, by simpa [synth, Fintype.linearCombination_apply] using hc⟩

theorem qform_gram (v : Fin n → E) (c : Fin n → 𝕜) :
    qform (Matrix.gram 𝕜 v) c = ‖synth v c‖ ^ 2 := by
  rw [qform, Matrix.star_dotProduct_gram_mulVec, ← synth, inner_self_eq_norm_sq]

end Hilbert

/-- Prefix bound expressed in the Gram quadratic form. -/
def PB (G : Matrix (Fin n) (Fin n) 𝕜) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (k : ℕ), k ≤ n → ∀ c : Fin n → 𝕜,
    qform G (truncCoeff k c) ≤ K ^ 2 * qform G c

theorem hPrefix_iff_pb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : Fin n → E) (K : ℝ) : HPrefix (𝕜 := 𝕜) v K ↔ PB (Matrix.gram 𝕜 v) K := by
  unfold HPrefix PB
  simp only [qform_gram, ← mul_pow]
  exact and_congr_right fun hK ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).symm

theorem PB.add_smul {G H : Matrix (Fin n) (Fin n) 𝕜} {K a b : ℝ}
    (hG : PB G K) (hH : PB H K) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    PB (a • G + b • H) K := by
  refine ⟨hG.1, fun k hk c ↦ ?_⟩
  simp only [qform_add, qform_smul, mul_add]
  rw [mul_left_comm (K ^ 2) a, mul_left_comm (K ^ 2) b]
  exact add_le_add (mul_le_mul_of_nonneg_left (hG.2 k hk c) ha)
    (mul_le_mul_of_nonneg_left (hH.2 k hk c) hb)


theorem pb_iff_matrix_le {G : Matrix (Fin n) (Fin n) 𝕜} (hG : G.IsHermitian) (K : ℝ) :
    PB G K ↔ 0 ≤ K ∧ ∀ (k : ℕ), k ≤ n →
      prefixMask 𝕜 k * G * prefixMask 𝕜 k ≤ K ^ 2 • G := by
  refine and_congr_right fun _ ↦ forall_congr' fun k ↦ forall_congr' fun _ ↦ ?_
  let D := prefixMask (n := n) 𝕜 k
  have hD : Dᴴ = D := prefixMask_isHermitian k
  have hcong (c : Fin n → 𝕜) : qform (prefixMask 𝕜 k * G * prefixMask 𝕜 k) c =
      qform G (truncCoeff k c) := by
    simpa only [hD, show D *ᵥ c = truncCoeff k c from prefixMask_mulVec k c] using
      qform_conjTranspose_mul G D c
  constructor
  · intro h
    apply matrix_le_of_qform_le
    · simpa only [hD] using Matrix.isHermitian_conjTranspose_mul_mul D hG
    · exact hG.smul (IsSelfAdjoint.all _)
    · intro c
      simpa only [hcong, qform_smul] using h c
  · intro h c
    simpa only [hcong, qform_smul] using qform_mono h c

theorem PB.relative {G L : Matrix (Fin n) (Fin n) 𝕜} {K a b : ℝ}
    (h : PB G K) (ha : 0 < a) (hab : a ≤ b) (hG : a • G ≤ L)
    (hL : L ≤ b • G) : PB L (Real.sqrt (b / a) * K) := by
  have hb : 0 ≤ b := ha.le.trans hab
  have hs := Real.sq_sqrt (div_nonneg hb ha.le)
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) h.1, fun k hk c ↦ ?_⟩
  have hg := qform_mono hG c
  simp only [qform_smul] at hg
  calc
    qform L (truncCoeff k c) ≤ b * qform G (truncCoeff k c) := by
      simpa only [qform_smul] using qform_mono hL (truncCoeff k c)
    _ ≤ b * (K ^ 2 * qform G c) := mul_le_mul_of_nonneg_left (h.2 k hk c) hb
    _ = (Real.sqrt (b / a) * K) ^ 2 * (a * qform G c) := by
      rw [mul_pow, hs]
      field_simp
    _ ≤ (Real.sqrt (b / a) * K) ^ 2 * qform L c :=
      mul_le_mul_of_nonneg_left hg (sq_nonneg _)

section Restriction

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Synthesis is unchanged by extending a coefficient vector by zero along an embedding. -/
theorem synth_extend (v : Fin n → E) (e : Fin m ↪ Fin n) (c : Fin m → 𝕜) :
    synth v (Function.extend e c 0) = synth (v ∘ e) c := by
  unfold synth
  calc
    _ = ∑ j ∈ Finset.univ.map e, (Function.extend e c 0 j) • v j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hnot : ¬∃ i, e i = j := by simpa using hj
      simp [Function.extend_apply' c (0 : Fin n → 𝕜) j hnot]
    _ = _ := by
      rw [Finset.sum_map]
      simp [e.injective.extend_apply]

theorem truncCoeff_extend {e : Fin m ↪ Fin n} {k l : ℕ}
    (h : ∀ i : Fin m, (e i).val < k ↔ i.val < l) (c : Fin m → 𝕜) :
    truncCoeff k (Function.extend e c 0) = Function.extend e (truncCoeff l c) 0 := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    simp [truncCoeff, h i, e.injective.extend_apply]
  · simp [truncCoeff, Function.extend_apply' _ _ _ hj]

/-- Restrict a single cut to an embedded subfamily, given its retained-index pattern. -/
theorem prefix_cut_restrict (v : Fin n → E) (e : Fin m ↪ Fin n) {K : ℝ} {k l : ℕ}
    (hcut : ∀ c : Fin n → 𝕜, ‖synth v (truncCoeff k c)‖ ≤ K * ‖synth v c‖)
    (hk : ∀ i : Fin m, (e i).val < k ↔ i.val < l) (c : Fin m → 𝕜) :
    ‖synth (v ∘ e) (truncCoeff l c)‖ ≤ K * ‖synth (v ∘ e) c‖ := by
  simpa only [truncCoeff_extend hk, synth_extend] using hcut (Function.extend e c 0)

theorem HPrefix.restrict {v : Fin n → E} {K : ℝ} (h : HPrefix (𝕜 := 𝕜) v K)
    (e : Fin m ↪ Fin n) (he : StrictMono e) : HPrefix (𝕜 := 𝕜) (v ∘ e) K := by
  refine ⟨h.1, fun l _ c ↦ ?_⟩
  by_cases hl : l < m
  · let j : Fin m := ⟨l, hl⟩
    apply prefix_cut_restrict v e (h.2 (e j).val (Nat.le_of_lt (e j).isLt)) _ c
    intro i
    exact he.lt_iff_lt
  · exact prefix_cut_restrict v e (h.2 n le_rfl)
      (fun i ↦ iff_of_true (e i).isLt (lt_of_lt_of_le i.isLt (Nat.le_of_not_gt hl))) c

/-- Synthesis of an ordered append splits into the two sums with inherited coefficients. -/
theorem synth_append (u : Fin m → E) (v : Fin n → E) (c : Fin (m + n) → 𝕜) :
    synth (Fin.append u v) c =
      synth u (fun i ↦ c (Fin.castAdd n i)) + synth v (fun j ↦ c (Fin.natAdd m j)) := by
  simp only [synth, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem synth_append_cut_le (u : Fin m → E) (v : Fin n → E) (c : Fin (m + n) → 𝕜)
    {k : ℕ} (hk : k ≤ m) :
    synth (Fin.append u v) (truncCoeff k c) = synth u (truncCoeff k (fun i ↦ c (Fin.castAdd n i))) := by
  rw [synth_append]
  simp only [truncCoeff, Fin.val_castAdd, Fin.val_natAdd]
  have h : (fun j : Fin n ↦ if m + j.val < k then c (Fin.natAdd m j) else 0) = 0 := by
    ext j
    simp [show ¬m + j.val < k by omega]
  rw [h, synth_zero, add_zero]
  rfl

theorem synth_append_cut_ge (u : Fin m → E) (v : Fin n → E) (c : Fin (m + n) → 𝕜)
    {k : ℕ} (hk : m ≤ k) :
    synth (Fin.append u v) (truncCoeff k c) =
      synth u (fun i ↦ c (Fin.castAdd n i)) +
      synth v (truncCoeff (k - m) (fun j ↦ c (Fin.natAdd m j))) := by
  rw [synth_append]
  congr 1
  · congr 1
    ext i
    simp [truncCoeff, lt_of_lt_of_le i.isLt hk]
  · congr 1
    ext j
    simp [truncCoeff, show m + j.val < k ↔ j.val < k - m by omega]

end Restriction

section OrthogonalTail

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*}

theorem mem_span_range_synth (v : Fin n → E) (c : Fin n → 𝕜) :
    synth v c ∈ span 𝕜 (Set.range v) := by
  rw [← range_synthCLM]
  exact ⟨WithLp.toLp 2 c, by simp⟩

theorem exists_synth_of_mem_span {v : Fin n → E} {x : E}
    (h : x ∈ span 𝕜 (Set.range v)) : ∃ c : Fin n → 𝕜, synth v c = x := by
  rw [← range_synthCLM] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨WithLp.ofLp c, by simpa using hc⟩

theorem linearIndependent_iff_synth_eq_zero (v : Fin n → E) :
    LinearIndependent 𝕜 v ↔ ∀ c : Fin n → 𝕜, synth v c = 0 → c = 0 := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, ← LinearMap.ker_eq_bot,
    LinearMap.ker_eq_bot']
  simp only [Fintype.linearCombination_apply, synth]

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem map_synth (A : E →L[𝕜] F) (v : Fin n → E) (c : Fin n → 𝕜) :
    A (synth v c) = synth (A ∘ v) c := by
  simp [synth, map_sum, map_smul]

theorem HPrefix.linearIsometry {v : Fin n → E} {K : ℝ}
    (h : HPrefix (𝕜 := 𝕜) v K) (A : E →ₗᵢ[𝕜] F) : HPrefix (𝕜 := 𝕜) (A ∘ v) K := by
  refine ⟨h.1, fun k hk c ↦ ?_⟩
  change ‖synth (A.toContinuousLinearMap ∘ v) (truncCoeff k c)‖ ≤
    K * ‖synth (A.toContinuousLinearMap ∘ v) c‖
  rw [← map_synth, ← map_synth, LinearIsometry.coe_toContinuousLinearMap]
  simp only [LinearIsometry.norm_map]
  exact h.2 k hk c

instance finiteDimensional_span_fin (v : Fin n → E) : FiniteDimensional 𝕜 (span 𝕜 (Set.range v)) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)

/-- Projection onto the orthogonal complement of the span of the head family. -/
def offHead (u : Fin m → E) : E →L[𝕜] E :=
  (span 𝕜 (Set.range u))ᗮ.starProjection

theorem offHead_add_starProjection (u : Fin m → E) (x : E) :
    offHead (𝕜 := 𝕜) u x + (span 𝕜 (Set.range u)).starProjection x = x := by
  simpa only [offHead, add_comm] using
    (span 𝕜 (Set.range u)).starProjection_add_starProjection_orthogonal x

theorem offHead_eq_sub_starProjection (u : Fin m → E) (x : E) :
    offHead (𝕜 := 𝕜) u x = x - (span 𝕜 (Set.range u)).starProjection x :=
  eq_sub_of_add_eq (offHead_add_starProjection u x)

theorem offHead_eq_zero_of_mem_span (u : Fin m → E) {x : E}
    (hx : x ∈ span 𝕜 (Set.range u)) : offHead (𝕜 := 𝕜) u x = 0 := by
  rw [offHead_eq_sub_starProjection, Submodule.starProjection_eq_self_iff.mpr hx, sub_self]

theorem offHead_apply_le (u : Fin m → E) (x : E) :
    ‖offHead (𝕜 := 𝕜) u x‖ ≤ ‖x‖ :=
  Submodule.norm_starProjection_apply_le _ _

theorem append_independent_offHead (u : Fin m → E) (v : Fin n → E)
    (h : LinearIndependent 𝕜 (Fin.append u v)) : LinearIndependent 𝕜 ((offHead (𝕜 := 𝕜) u) ∘ v) := by
  rw [linearIndependent_iff_synth_eq_zero]
  intro d hd
  rw [← map_synth, offHead_eq_sub_starProjection, sub_eq_zero] at hd
  have hmem : -synth v d ∈ span 𝕜 (Set.range u) := by
    apply neg_mem
    rw [hd]
    exact Submodule.starProjection_apply_mem _ _
  obtain ⟨c, hc⟩ := exists_synth_of_mem_span hmem
  have hcd : synth (Fin.append u v) (Fin.append c d) = 0 := by
    rw [synth_append]
    simp only [Fin.append_left, Fin.append_right, hc, neg_add_cancel]
  have hzero := (linearIndependent_iff_synth_eq_zero _).mp h _ hcd
  funext j
  simpa only [Fin.append_right, Pi.zero_apply] using congrFun hzero (Fin.natAdd m j)

theorem hPrefix_offHead (u : Fin m → E) (v : Fin n → E) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ k : ℕ, k ≤ n → ∀ c : Fin (m + n) → 𝕜,
      ‖synth (Fin.append u v) (truncCoeff (m + k) c)‖ ≤ K * ‖synth (Fin.append u v) c‖) :
    HPrefix (𝕜 := 𝕜) ((offHead (𝕜 := 𝕜) u) ∘ v) K := by
  refine ⟨hK, fun k hk d ↦ ?_⟩
  let x := synth v d
  set Q := (span 𝕜 (Set.range u)).starProjection
  obtain ⟨c, hc⟩ : ∃ c : Fin m → 𝕜, synth u c = -Q x :=
    exists_synth_of_mem_span (neg_mem (Submodule.starProjection_apply_mem _ _))
  have hb := h k hk (Fin.append c d)
  rw [synth_append_cut_ge _ _ _ (Nat.le_add_right m k), synth_append] at hb
  simp only [Fin.append_left, Fin.append_right, Nat.add_sub_cancel_left, hc] at hb
  simp only [← map_synth]
  calc
    ‖offHead (𝕜 := 𝕜) u (synth v (truncCoeff k d))‖ =
        ‖offHead (𝕜 := 𝕜) u (-Q x + synth v (truncCoeff k d))‖ := by
      rw [map_add, offHead_eq_zero_of_mem_span u
        (neg_mem (Submodule.starProjection_apply_mem _ _)), zero_add]
    _ ≤ ‖-Q x + synth v (truncCoeff k d)‖ := offHead_apply_le u _
    _ ≤ K * ‖-Q x + x‖ := hb
    _ = K * ‖offHead (𝕜 := 𝕜) u x‖ := by rw [offHead_eq_sub_starProjection, sub_eq_add_neg, add_comm]

end OrthogonalTail

section Angle

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem HPrefix.le_any_cut {v : Fin n → E} {K : ℝ} (h : HPrefix (𝕜 := 𝕜) v K)
    (k : ℕ) (c : Fin n → 𝕜) :
    ‖synth v (truncCoeff k c)‖ ≤ K * ‖synth v c‖ := by
  by_cases hk : k ≤ n
  · exact h.2 k hk c
  · rw [truncCoeff_eq_self c (by omega)]
    simpa only [truncCoeff_full] using h.2 n le_rfl c

theorem synth_append_cut (u : Fin m → E) (v : Fin n → E) (c : Fin (m + n) → 𝕜) (k : ℕ) :
    synth (Fin.append u v) (truncCoeff k c) =
      synth u (truncCoeff k (fun i ↦ c (Fin.castAdd n i))) +
      synth v (truncCoeff (k - m) (fun j ↦ c (Fin.natAdd m j))) := by
  by_cases hk : k ≤ m
  · rw [synth_append_cut_le _ _ _ hk, Nat.sub_eq_zero_of_le hk, truncCoeff_zero, synth_zero, add_zero]
  · rw [synth_append_cut_ge _ _ _ (by omega), truncCoeff_eq_self (fun i : Fin m ↦ c (Fin.castAdd n i)) (by omega)]

theorem norm_sq_add_bounds_of_angle (x y : E) {β : ℝ}
    (hβ : 0 ≤ β) (h : ‖⟪x, y⟫_𝕜‖ ≤ β * ‖x‖ * ‖y‖) :
    (1 - β) * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ ‖x + y‖ ^ 2 ∧
      ‖x + y‖ ^ 2 ≤ (1 + β) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hRe := (RCLike.abs_re_le_norm ⟪x, y⟫_𝕜).trans h
  have hm := mul_nonneg hβ (sq_nonneg (‖x‖ - ‖y‖))
  rw [norm_add_sq (𝕜 := 𝕜)]
  constructor
  · linarith only [(abs_le.mp hRe).1, hm]
  · linarith only [(abs_le.mp hRe).2, hm]

theorem append_small_angle_hPrefix (u : Fin m → E) (v : Fin n → E) {Ku Kv β : ℝ}
    (hu : HPrefix (𝕜 := 𝕜) u Ku) (hv : HPrefix (𝕜 := 𝕜) v Kv)
    (hβ : 0 ≤ β) (hβ' : β < 1)
    (h : ∀ x ∈ span 𝕜 (Set.range u), ∀ y ∈ span 𝕜 (Set.range v),
      ‖⟪x, y⟫_𝕜‖ ≤ β * ‖x‖ * ‖y‖) :
    HPrefix (𝕜 := 𝕜) (Fin.append u v) (max Ku Kv * Real.sqrt ((1 + β) / (1 - β))) := by
  let K := max Ku Kv
  let L := K * Real.sqrt ((1 + β) / (1 - β))
  have hK : 0 ≤ K := hu.1.trans (le_max_left _ _)
  have hL : 0 ≤ L := mul_nonneg hK (Real.sqrt_nonneg _)
  have hi : 0 < 1 - β := sub_pos.mpr hβ'
  have ha : 0 ≤ 1 + β := by linarith
  have hLs : L ^ 2 * (1 - β) = (1 + β) * K ^ 2 := by
    dsimp [L]
    rw [mul_pow, Real.sq_sqrt (div_nonneg ha hi.le)]
    field_simp
  refine ⟨hL, fun k _ c ↦ ?_⟩
  let a := fun i : Fin m ↦ c (Fin.castAdd n i)
  let b := fun j : Fin n ↦ c (Fin.natAdd m j)
  rw [synth_append_cut, synth_append]
  change ‖synth u (truncCoeff k a) + synth v (truncCoeff (k - m) b)‖ ≤
    L * ‖synth u a + synth v b‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  have hpre := (norm_sq_add_bounds_of_angle _ _ hβ
    (h _ (mem_span_range_synth u (truncCoeff k a)) _ (mem_span_range_synth v (truncCoeff (k - m) b)))).2
  have hfull := (norm_sq_add_bounds_of_angle _ _ hβ
    (h _ (mem_span_range_synth u a) _ (mem_span_range_synth v b))).1
  have hu' := pow_le_pow_left₀ (norm_nonneg _) ((hu.mono (le_max_left Ku Kv)).le_any_cut k a) 2
  have hv' := pow_le_pow_left₀ (norm_nonneg _) ((hv.mono (le_max_right Ku Kv)).le_any_cut (k - m) b) 2
  calc
    _ ≤ (1 + β) * (‖synth u (truncCoeff k a)‖ ^ 2 + ‖synth v (truncCoeff (k - m) b)‖ ^ 2) := hpre
    _ ≤ (1 + β) * ((K * ‖synth u a‖) ^ 2 + (K * ‖synth v b‖) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hu' hv') ha
    _ = L ^ 2 * ((1 - β) * (‖synth u a‖ ^ 2 + ‖synth v b‖ ^ 2)) := by
      simp only [mul_pow]
      rw [← mul_assoc, hLs]
      ring
    _ ≤ L ^ 2 * ‖synth u a + synth v b‖ ^ 2 := mul_le_mul_of_nonneg_left hfull (sq_nonneg _)
    _ = _ := (mul_pow _ _ _).symm

theorem append_small_angle_independent (u : Fin m → E) (v : Fin n → E) {β : ℝ}
    (hu : LinearIndependent 𝕜 u) (hv : LinearIndependent 𝕜 v)
    (hβ : 0 ≤ β) (hβ' : β < 1)
    (h : ∀ x ∈ span 𝕜 (Set.range u), ∀ y ∈ span 𝕜 (Set.range v),
      ‖⟪x, y⟫_𝕜‖ ≤ β * ‖x‖ * ‖y‖) :
    LinearIndependent 𝕜 (Fin.append u v) := by
  rw [linearIndependent_iff_synth_eq_zero] at hu hv ⊢
  intro c hc
  let a := fun i : Fin m ↦ c (Fin.castAdd n i)
  let b := fun j : Fin n ↦ c (Fin.natAdd m j)
  change synth (Fin.append u v) c = 0 at hc
  have hc' : synth u a + synth v b = 0 := (synth_append _ _ _).symm.trans hc
  have hx := (norm_sq_add_bounds_of_angle _ _ hβ
    (h _ (mem_span_range_synth u a) _ (mem_span_range_synth v b))).1
  rw [hc', norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hx
  have hz := nonpos_of_mul_nonpos_right hx (sub_pos.mpr hβ')
  have hza : synth u a = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (synth u a), sq_nonneg ‖synth v b‖]
  have hzb : synth v b = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (synth v b), sq_nonneg ‖synth u a‖]
  have ha := hu a hza
  have hb := hv b hzb
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · exact congrFun ha j
  · exact congrFun hb j

end Angle

theorem PB.complexify {A : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (h : PB A K) :
    PB (complexify A) K := by
  refine ⟨h.1, fun k hk c ↦ ?_⟩
  have hre : (fun i ↦ (truncCoeff k c i).re) = truncCoeff k (fun i ↦ (c i).re) := by
    funext i
    by_cases h : i.val < k <;> simp [truncCoeff, h]
  have him : (fun i ↦ (truncCoeff k c i).im) = truncCoeff k (fun i ↦ (c i).im) := by
    funext i
    by_cases h : i.val < k <;> simp [truncCoeff, h]
  rw [qform_complexify, qform_complexify, hre, him, mul_add]
  exact add_le_add (h.2 k hk _) (h.2 k hk _)

end SchauderBasisOrbits
