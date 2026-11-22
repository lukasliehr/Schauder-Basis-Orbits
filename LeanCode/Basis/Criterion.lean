module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Tactic
public import LeanCode.Finite.Families

@[expose] public section

open Filter Submodule
open scoped Topology InnerProductSpace

namespace SchauderBasisOrbits

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The linear span of the ordered vectors of a native Schauder basis is dense. -/
theorem dense_span_schauderBasis (b : SchauderBasis ℂ H) :
    Dense (span ℂ (Set.range b) : Set H) := by
  intro x
  exact mem_closure_of_tendsto (b.tendsto_proj x) (Eventually.of_forall fun n => by
    have hmem : b.proj n x ∈ (b.proj n).toLinearMap.range := ⟨x, rfl⟩
    rw [b.range_proj_eq_span] at hmem
    exact (span_mono (Set.image_subset_range _ _)) hmem)

/-- Bounded Schauder basis vectors in a Hilbert space have vanishing inner products
against every fixed vector. -/
theorem tendsto_inner_schauderBasis [CompleteSpace H] (b : SchauderBasis ℂ H)
    {C : ℝ} (hC : ∀ n, ‖b n‖ ≤ C) (x : H) :
    Tendsto (fun n => ⟪x, b n⟫_ℂ) atTop (𝓝 0) := by
  let r : ℕ → H := fun n => (InnerProductSpace.toDual ℂ H).symm (b.coord n)
  have hr (n : ℕ) (y : H) : ⟪r n, y⟫_ℂ = b.coord n y :=
    InnerProductSpace.toDual_symm_apply
  have hdense : Dense (span ℂ (Set.range r) : Set H) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    apply eq_bot_iff.mpr
    intro y hy
    rw [Submodule.mem_bot]
    have hcoord (n : ℕ) : b.coord n y = 0 := by
      rw [← hr]
      exact (Submodule.mem_orthogonal _ _).mp hy _ (subset_span ⟨n, rfl⟩)
    have hproj (n : ℕ) : b.proj n y = 0 := by simp [SchauderBasis.proj_apply, hcoord]
    exact tendsto_nhds_unique (b.tendsto_proj y) (by simp [hproj])
  have hspan (y : H) (hy : y ∈ span ℂ (Set.range r)) :
      Tendsto (fun n => ⟪y, b n⟫_ℂ) atTop (𝓝 0) := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop i] with n hn
      rw [hr, b.ortho]
      simp [ne_of_lt hn]
    | zero => simpa only [inner_zero_left] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    | add y z _ _ hy hz => simpa only [inner_add_left, zero_add] using hy.add hz
    | smul c y _ hy => simpa only [inner_smul_left, mul_zero] using hy.const_mul (starRingEnd ℂ c)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hCp : 0 < C + 1 := by linarith [norm_nonneg (b 0), hC 0]
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hdense x) (ε / (2 * (C + 1)))
    (div_pos hε (by positivity))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hspan y hy) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have herr : ‖⟪x - y, b n⟫_ℂ‖ < ε / 2 := by
    calc
      ‖⟪x - y, b n⟫_ℂ‖ ≤ ‖x - y‖ * ‖b n‖ := norm_inner_le_norm _ _
      _ ≤ ‖x - y‖ * (C + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hC n]) (norm_nonneg _)
      _ < (ε / (2 * (C + 1))) * (C + 1) :=
        mul_lt_mul_of_pos_right (by simpa [dist_eq_norm] using hxy) hCp
      _ = ε / 2 := by field_simp
  have hyn : ‖⟪y, b n⟫_ℂ‖ < ε / 2 := by simpa using hN n hn
  rw [dist_zero_right, ← sub_add_cancel x y, inner_add_left]
  exact (norm_add_le ..).trans_lt (by linarith)

section Ordered

variable [CompleteSpace H]

/-- Restrict a finitely supported coefficient vector to the first `N` indices. -/
noncomputable def orderedCut (N : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  (Finsupp.supported ℂ ℂ {i | i < N}).subtype.comp
    (Finsupp.restrictDom ℂ ℂ {i | i < N})

@[simp] theorem orderedCut_apply (N : ℕ) (c : ℕ →₀ ℂ) (i : ℕ) :
    orderedCut N c i = if i < N then c i else 0 := by
  simp [orderedCut, Finsupp.filter_apply]

@[simp] theorem orderedCut_single (N i : ℕ) (a : ℂ) :
    orderedCut N (Finsupp.single i a) = if i < N then Finsupp.single i a else 0 := by
  by_cases h : i < N
  · simp [orderedCut, h, Finsupp.filter_single_of_pos]
  · simp [orderedCut, h, Finsupp.filter_single_of_neg]

theorem orderedCut_comp (N M : ℕ) (c : ℕ →₀ ℂ) :
    orderedCut N (orderedCut M c) = orderedCut (min N M) c := by
  ext i
  simp only [orderedCut_apply, lt_min_iff]
  by_cases h : i < N <;> by_cases h' : i < M <;> simp [h, h']

/-- Uniform boundedness of the algebraic coordinate prefixes on finite sums. -/
def OrderedPrefixBound (v : ℕ → H) (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ N (c : ℕ →₀ ℂ), ‖Finsupp.linearCombination ℂ v (orderedCut N c)‖ ≤
    K * ‖Finsupp.linearCombination ℂ v c‖

omit [CompleteSpace H] in
private theorem denseRange_synthesis {v : ℕ → H}
    (hd : Dense (span ℂ (Set.range v) : Set H)) :
    DenseRange (Finsupp.linearCombination ℂ v) := by
  rw [← Finsupp.range_linearCombination, LinearMap.coe_range] at hd
  exact hd

/-- The continuous extension of the algebraic coordinate projection on a dense span. -/
noncomputable def orderedProjection (v : ℕ → H) (N : ℕ) : H →L[ℂ] H :=
  ((Finsupp.linearCombination ℂ v).comp (orderedCut N)).extendOfNorm
    (Finsupp.linearCombination ℂ v)

theorem orderedProjection_synthesis {v : ℕ → H}
    (hd : Dense (span ℂ (Set.range v) : Set H)) {K : ℝ} (hK : OrderedPrefixBound v K)
    (N : ℕ) (c : ℕ →₀ ℂ) :
    orderedProjection v N (Finsupp.linearCombination ℂ v c) =
      Finsupp.linearCombination ℂ v (orderedCut N c) :=
  LinearMap.extendOfNorm_eq (denseRange_synthesis hd) ⟨K, hK.2 N⟩ c

theorem norm_orderedProjection_le {v : ℕ → H}
    (hd : Dense (span ℂ (Set.range v) : Set H)) {K : ℝ} (hK : OrderedPrefixBound v K)
    (N : ℕ) : ‖orderedProjection v N‖ ≤ K :=
  LinearMap.opNorm_extendOfNorm_le (denseRange_synthesis hd) hK.1 (hK.2 N)

theorem orderedProjection_basis {v : ℕ → H}
    (hd : Dense (span ℂ (Set.range v) : Set H)) {K : ℝ} (hK : OrderedPrefixBound v K)
    (N i : ℕ) : orderedProjection v N (v i) = if i < N then v i else 0 := by
  have hs := orderedProjection_synthesis hd hK N (Finsupp.single i 1)
  simp only [Finsupp.linearCombination_single, one_smul, orderedCut_single] at hs
  rw [hs]
  split <;> simp

theorem orderedProjection_tendsto {v : ℕ → H}
    (hd : Dense (span ℂ (Set.range v) : Set H)) {K : ℝ} (hK : OrderedPrefixBound v K)
    (x : H) : Tendsto (fun N => orderedProjection v N x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨p, hp, hxp⟩ := Metric.mem_closure_iff.mp (hd x) (ε / (K + 1))
    (div_pos hε (by linarith [hK.1]))
  rw [← Finsupp.range_linearCombination] at hp
  obtain ⟨c, rfl⟩ := hp
  refine ⟨c.support.sup id + 1, fun N hN => ?_⟩
  have hcut : orderedCut N c = c := by
    ext i
    rw [orderedCut_apply]
    by_cases hi : i ∈ c.support
    · rw [ite_eq_left (show i < N from lt_of_le_of_lt (Finset.le_sup (f := id) hi) (by omega))]
    · simp [Finsupp.notMem_support_iff.mp hi]
  let p := Finsupp.linearCombination ℂ v c
  have hp : orderedProjection v N p = p := by
    simpa only [hcut] using orderedProjection_synthesis hd hK N c
  have hdiff : orderedProjection v N x - x =
      orderedProjection v N (x - p) + (p - x) := by
    rw [map_sub, hp]
    abel
  rw [dist_eq_norm, hdiff]
  have hdif : ‖x - p‖ < ε / (K + 1) := by simpa [dist_eq_norm, norm_sub_rev] using hxp
  calc
    ‖orderedProjection v N (x - p) + (p - x)‖
        ≤ ‖orderedProjection v N (x - p)‖ + ‖p - x‖ := norm_add_le _ _
    _ ≤ K * ‖x - p‖ + ‖x - p‖ :=
      add_le_add (ContinuousLinearMap.le_of_opNorm_le _ (norm_orderedProjection_le hd hK N) _) (by rw [norm_sub_rev])
    _ = (K + 1) * ‖x - p‖ := by ring
    _ < ε := (lt_div_iff₀' (by linarith [hK.1])).mp hdif

theorem orderedProjection_comp {v : ℕ → H}
    (hd : Dense (span ℂ (Set.range v) : Set H)) {K : ℝ} (hK : OrderedPrefixBound v K)
    (N M : ℕ) (x : H) :
    orderedProjection v N (orderedProjection v M x) = orderedProjection v (min N M) x := by
  refine (denseRange_synthesis hd).induction_on x (p := fun y =>
    orderedProjection v N (orderedProjection v M y) =
      orderedProjection v (min N M) y) (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [orderedProjection_synthesis hd hK, orderedCut_comp]

theorem range_orderedProjection {v : ℕ → H}
    (hd : Dense (span ℂ (Set.range v) : Set H)) {K : ℝ} (hK : OrderedPrefixBound v K)
    (N : ℕ) :
    (orderedProjection v N).toLinearMap.range = span ℂ (Set.range (fun i : Fin N => v i)) := by
  let S := span ℂ (Set.range (fun i : Fin N => v i))
  let : FiniteDimensional ℂ S := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  have hS : IsClosed (S : Set H) := S.isClosed_of_finiteDimensional
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change orderedProjection v N x ∈ S
    refine (denseRange_synthesis hd).induction_on x (p := fun y =>
      orderedProjection v N y ∈ S) (hS.preimage (orderedProjection v N).continuous) ?_
    intro c
    rw [orderedProjection_synthesis hd hK, Finsupp.linearCombination_apply, Finsupp.sum]
    apply sum_mem
    intro i hi
    have hi' : i < N := by
      by_contra h
      have hm := Finsupp.mem_support_iff.mp hi
      rw [orderedCut_apply, ite_eq_right h] at hm
      exact hm rfl
    exact smul_mem S _ (subset_span ⟨⟨i, hi'⟩, rfl⟩)
  · apply span_le.mpr
    rintro y ⟨i, rfl⟩
    exact ⟨v i, by simpa [i.isLt] using orderedProjection_basis hd hK N i⟩

/-- An independent dense sequence with uniformly bounded ordered prefixes is a Schauder basis.
The returned basis has the specified sequence of vectors in the original order. -/
theorem basis_of_orderedPrefixBound {v : ℕ → H}
    (hi : LinearIndependent ℂ v) (hd : Dense (span ℂ (Set.range v) : Set H))
    {K : ℝ} (hK : OrderedPrefixBound v K) :
    ∃ b : SchauderBasis ℂ H, ∀ n, b n = v n := by
  let D : SchauderBasis.RankOneDecomposition ℂ H :=
    { P := orderedProjection v
      e := v
      proj_zero := by
        ext x
        have h := range_orderedProjection hd hK 0
        have hm : orderedProjection v 0 x ∈ (orderedProjection v 0).toLinearMap.range := ⟨x, rfl⟩
        rw [h] at hm
        simpa using hm
      finrank_range := fun n => by
        rw [range_orderedProjection hd hK, finrank_span_eq_card]
        · exact Fintype.card_fin n
        · exact hi.comp (fun i : Fin n => i.val) Fin.val_injective
      proj_comp := orderedProjection_comp hd hK
      proj_tendsto := orderedProjection_tendsto hd hK
      e_mem_range := fun n => by
        refine ⟨v n, ?_⟩
        change orderedProjection v (n + 1) (v n) - orderedProjection v n (v n) = v n
        rw [orderedProjection_basis hd hK, orderedProjection_basis hd hK]
        simp
      e_ne_zero := hi.ne_zero }
  exact ⟨D.basis, fun _ => rfl⟩

omit [CompleteSpace H] in
theorem synthesis_eq_initial_synth (v : ℕ → H) (c : ℕ →₀ ℂ) (N : ℕ)
    (hc : ∀ i ∈ c.support, i < N) :
    Finsupp.linearCombination ℂ v c = synth (fun i : Fin N => v i) (fun i => c i) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset c
      (s := Finset.range N) (fun i hi => Finset.mem_range.mpr (hc i hi)) _ (by simp)]
  rw [synth, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

omit [CompleteSpace H] in
theorem orderedPrefixBound_of_initial (v : ℕ → H) {K : ℝ}
    (hv : ∀ N, HPrefix (𝕜 := ℂ) (fun i : Fin N => v i) K) :
    OrderedPrefixBound v K := by
  refine ⟨(hv 0).1, fun k c => ?_⟩
  let N := max k (c.support.sup id + 1)
  have hc : ∀ i ∈ c.support, i < N := fun i hi =>
    lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)) (le_max_right ..)
  have hcut : ∀ i ∈ (orderedCut k c).support, i < N := by
    intro i hi
    apply hc
    rw [Finsupp.mem_support_iff] at hi ⊢
    rw [orderedCut_apply] at hi
    by_contra h
    simp [h] at hi
  rw [synthesis_eq_initial_synth v c N hc, synthesis_eq_initial_synth v _ N hcut]
  have heq : (fun i : Fin N => orderedCut k c i) = truncCoeff k (fun i : Fin N => c i) := by
    funext i
    exact orderedCut_apply k c i
  rw [heq]
  exact (hv N).2 k (le_max_left ..) (fun i => c i)

omit [CompleteSpace H] in
theorem linearIndependent_of_initial (v : ℕ → H)
    (hv : ∀ N, LinearIndependent ℂ (fun i : Fin N => v i)) :
    LinearIndependent ℂ v := by
  apply linearIndependent_iff.mpr
  intro c hz
  let N := c.support.sup id + 1
  have hc : ∀ i ∈ c.support, i < N := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  rw [synthesis_eq_initial_synth v c N hc, synth] at hz
  have hc0 := Fintype.linearIndependent_iff.mp (hv N) _ hz
  ext i
  by_cases hi : i ∈ c.support
  · exact hc0 ⟨i, hc i hi⟩
  · simpa using Finsupp.notMem_support_iff.mp hi

end Ordered

end SchauderBasisOrbits
