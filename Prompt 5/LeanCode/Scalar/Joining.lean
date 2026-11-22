module

public import LeanCode.Scalar.Inverse
public import LeanCode.Finite.Projection

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace SchauderBasisOrbits.Scalar

variable {r n : ℕ} (D : Data r n) {L : ℕ} (hL : 0 < L)

def blockCoeffs (c : Fin (L * n) → ℝ) (b : Fin L) : Fin n → ℝ :=
  fun i => c (finProdFinEquiv (b, i))

lemma copies_normalizedMean_dotProduct (c : Fin (L * n) → ℝ) :
    (copies D L hL).normalizedMean ⬝ᵥ c =
      ∑ b : Fin L, D.normalizedMean ⬝ᵥ blockCoeffs c b := by
  simp only [dotProduct]
  let f (i : Fin (L * n)) := (copies D L hL).normalizedMean i * c i
  change (∑ i, f i) = _
  rw [← (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).sum_comp f,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp [f, copies_normalizedMean, blockCoeffs]

private lemma split_univ_sum {σ : Type*} [Fintype σ] [LinearOrder σ] (a : σ) (f : σ → ℝ) :
    ∑ b, f b =
      (∑ b ∈ Finset.univ.filter (fun b => b < a), f b) + f a +
        ∑ b ∈ Finset.univ.filter (fun b => a < b), f b := by
  classical
  let left := Finset.univ.filter (fun b => b < a)
  let right := Finset.univ.filter (fun b => a < b)
  have h : left ∪ {a} ∪ right = Finset.univ := by
    ext b
    simp only [left, right, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, iff_true]
    rcases lt_trichotomy b a with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hd : Disjoint left ({a} : Finset σ) := by
    simp [left]
  have hd' : Disjoint (left ∪ {a}) right := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    simp only [left, right, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hb hb'
    rcases hb with h | rfl
    · exact (not_lt_of_ge h.le) hb'
    · exact (lt_irrefl _) hb'
  nth_rw 1 [← h]
  rw [Finset.sum_union hd', Finset.sum_union hd, Finset.sum_singleton]

private lemma blockCoeffs_trunc (c : Fin (L * n) → ℝ) {k : ℕ} (hk : k < L * n)
    (hn : 0 < n) :
    let b₀ : Fin L := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
    let j := k % n
    ∀ b : Fin L, blockCoeffs (truncCoeff k c) b =
      if b < b₀ then blockCoeffs c b else
        if b = b₀ then truncCoeff j (blockCoeffs c b) else 0 := by
  dsimp only
  let b₀ : Fin L := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk⟩
  let j := k % n
  intro b
  change blockCoeffs (truncCoeff k c) b =
    if b < b₀ then blockCoeffs c b else if b = b₀ then truncCoeff j (blockCoeffs c b) else 0
  have hdiv : j + n * b₀.val = k := Nat.mod_add_div k n
  have hj : j < n := Nat.mod_lt k hn
  have hidx (i : Fin n) : (finProdFinEquiv (b, i)).val = i.val + n * b.val := rfl
  funext i
  by_cases hb : b < b₀
  · have hup : n * (b.val + 1) ≤ n * b₀.val := Nat.mul_le_mul_left n (by exact hb)
    rw [Nat.mul_succ] at hup
    have hcut : (finProdFinEquiv (b, i)).val < k := by rw [hidx]; omega
    simp only [blockCoeffs, truncCoeff, if_pos hb, if_pos hcut]
  by_cases he : b = b₀
  · have hcut : (finProdFinEquiv (b, i)).val < k ↔ i.val < j := by
      rw [hidx, he]
      omega
    simp only [if_neg hb, if_pos he, truncCoeff, blockCoeffs, hcut]
  · have hl : b₀ < b := lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm he)
    have hlo : n * (b₀.val + 1) ≤ n * b.val := Nat.mul_le_mul_left n (by exact hl)
    rw [Nat.mul_succ] at hlo
    have hcut : ¬ (finProdFinEquiv (b, i)).val < k := by rw [hidx]; omega
    simp only [blockCoeffs, truncCoeff, if_neg hb, if_neg he, if_neg hcut, Pi.zero_apply]

private lemma copies_qform_cons (s : ℝ) (c : Fin (L * n) → ℝ) :
    qform (copies D L hL).gram (Fin.cons s c) / (copies D L hL).mass =
      (s + ∑ b : Fin L, D.normalizedMean ⬝ᵥ blockCoeffs c b) ^ 2 +
        ∑ b : Fin L, qform D.normalizedGram (blockCoeffs c b) := by
  rw [Data.qform_gram_cons_div_mass, copies_normalizedMean_dotProduct, copies_normalizedGram,
    qform_blockCopies]
  rfl

/-- Join repeated independent centered blocks with their common normalized constant. -/
theorem copies_augmented_pb {Q : ℝ} (hQ : 1 + (L : ℝ) * D.gain < Q)
    (hcenter : PB D.normalizedGram (Real.sqrt Q)) :
    PB (copies D L hL).gram
      (Real.sqrt (Q + Q ^ 2 * D.gain / (Q - 1 - (L : ℝ) * D.gain))) := by
  classical
  let Z := (L : ℝ) * D.gain
  let J := Q + Q ^ 2 * D.gain / (Q - 1 - Z)
  let E := copies D L hL
  have hZ : 0 ≤ Z := mul_nonneg (by positivity) D.gain_nonneg
  have hQ₁ : 1 ≤ Q := by linarith only [hZ, hQ]
  have hQ₀ : 0 ≤ Q := by linarith
  have hJ : 1 ≤ J := by
    have hden : 0 < Q - 1 - Z := by linarith only [hQ]
    have hNum : 0 ≤ Q ^ 2 * D.gain := mul_nonneg (sq_nonneg _) D.gain_nonneg
    have hterm := div_nonneg hNum hden.le
    dsimp [J]
    linarith
  change PB E.gram (Real.sqrt J)
  refine ⟨Real.sqrt_nonneg _, fun k hk v => ?_⟩
  rw [Real.sq_sqrt (by linarith : 0 ≤ J)]
  by_cases hk₀ : k = 0
  · simp only [hk₀, truncCoeff_zero]
    simp [qform]
    exact mul_nonneg (by linarith) (qform_nonneg E.gram_posDef.posSemidef _)
  by_cases hfull : k = L * n + 1
  · rw [hfull, truncCoeff_full]
    exact le_mul_of_one_le_left (qform_nonneg E.gram_posDef.posSemidef _) hJ
  let s := v 0
  let c (i : Fin (L * n)) := v i.succ
  have hv : v = Fin.cons s c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  let k' := k - 1
  have hk' : k = k' + 1 := by dsimp [k']; omega
  have hk'' : k' < L * n := by dsimp [k']; omega
  rw [hv, hk', truncCoeff_cons]
  apply (div_le_div_iff_of_pos_right E.mass_pos).mp
  rw [mul_div_assoc, copies_qform_cons, copies_qform_cons]
  let a : Fin L := ⟨k' / n, (Nat.div_lt_iff_lt_mul D.size_pos).mpr hk''⟩
  let j := k' % n
  let later : Finset (Fin L) := Finset.univ.filter (fun b => a < b)
  let before : Finset (Fin L) := Finset.univ.filter (fun b => b < a)
  let W (b : Fin L) := blockCoeffs c b
  let W' (b : Fin L) := blockCoeffs (truncCoeff k' c) b
  let active := W a
  let kept := truncCoeff j active
  let energy (b : Fin L) := qform D.normalizedGram (W b)
  let mean (b : Fin L) := D.normalizedMean ⬝ᵥ W b
  let energy' (b : Fin L) := qform D.normalizedGram (W' b)
  let mean' (b : Fin L) := D.normalizedMean ⬝ᵥ W' b
  let γ := s + ∑ b, mean b
  let comp := D.normalizedMean ⬝ᵥ (active - kept)
  have hcut (b : Fin L) : W' b =
      if b < a then W b else if b = a then truncCoeff j (W b) else 0 :=
    blockCoeffs_trunc c hk'' D.size_pos b
  have hbefore (b : Fin L) (hb : b ∈ before) : W' b = W b := by
    have hb' : b < a := by simpa [before] using hb
    rw [hcut, if_pos hb']
  have hlater (b : Fin L) (hb : b ∈ later) : W' b = 0 := by
    have hb' : a < b := by simpa [later] using hb
    rw [hcut, if_neg (not_lt_of_ge hb'.le), if_neg (ne_of_gt hb')]
  have hactive : W' a = kept := by simp [hcut, kept, active]
  have hmean0 (b : Fin L) (hb : b ∈ later) : mean' b = 0 := by simp [mean', hlater b hb]
  have henergy0 (b : Fin L) (hb : b ∈ later) : energy' b = 0 := by simp [energy', hlater b hb, qform]
  have hmSum : ∑ b, mean' b = (∑ b ∈ before, mean b) + (D.normalizedMean ⬝ᵥ kept) := by
    rw [split_univ_sum a mean', Finset.sum_eq_zero hmean0, add_zero]
    rw [show mean' a = _ by rw [show mean' a = D.normalizedMean ⬝ᵥ W' a from rfl, hactive]]
    exact congrArg (fun t => t + (D.normalizedMean ⬝ᵥ kept))
      (Finset.sum_congr rfl fun b hb => by simp [mean, mean', hbefore b hb])
  have heSum : ∑ b, energy' b = (∑ b ∈ before, energy b) + qform D.normalizedGram kept := by
    rw [split_univ_sum a energy', Finset.sum_eq_zero henergy0, add_zero]
    rw [show energy' a = _ by rw [show energy' a = qform D.normalizedGram (W' a) from rfl, hactive]]
    exact congrArg (fun t => t + qform D.normalizedGram kept)
      (Finset.sum_congr rfl fun b hb => by simp [energy, energy', hbefore b hb])
  have hmComp : s + ∑ b, mean' b = γ - (∑ b ∈ later, mean b) - comp := by
    dsimp [γ, comp]
    rw [hmSum, split_univ_sum a mean, dotProduct_sub]
    change s + _ = s + (_ + (D.normalizedMean ⬝ᵥ active) + _) - _ - _
    ring
  have heN (b : Fin L) : 0 ≤ energy b := qform_nonneg D.normalizedGram_posDef.posSemidef _
  have hK : 1 ≤ Real.sqrt Q := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQ₁
  have hJ₀ : j ≤ n := (Nat.mod_lt _ D.size_pos).le
  have hsmall : qform D.normalizedGram kept ≤ Q * energy a := by
    simpa only [Real.sq_sqrt hQ₀] using hcenter.2 j hJ₀ active
  have hcomp : comp ^ 2 ≤ D.gain * Q * energy a := by
    have hcb := PB.complement_qform_le D.normalizedGram_posDef hK hcenter hJ₀ active
    rw [Real.sq_sqrt hQ₀] at hcb
    unfold comp
    calc
      _ ≤ D.gain * qform D.normalizedGram (active - kept) :=
        D.normalizedMean_sq_le_gain _
      _ ≤ D.gain * (Q * energy a) := mul_le_mul_of_nonneg_left hcb D.gain_nonneg
      _ = _ := by ring
  have hGain : ∑ b ∈ later, D.gain ≤ Z := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ later)
      (f := fun _ => D.gain) (fun _ _ _ => D.gain_nonneg)
    simpa [Z, nsmul_eq_mul] using h
  have hbound := join_small_mean_constant_bound later (fun _ => D.gain) energy mean
    (fun _ => D.gain_nonneg) heN
    (fun b _ => D.normalizedMean_sq_le_gain (W b)) hZ D.gain_nonneg hQ hGain
    (Finset.sum_nonneg (s := before) fun b _ => heN b) (heN a)
    (qform_nonneg D.normalizedGram_posDef.posSemidef kept) hsmall hcomp (γ := γ)
  change (s + ∑ b, mean' b) ^ 2 + (∑ b, energy' b) ≤ J * (γ ^ 2 + ∑ b, energy b)
  rw [hmComp, heSum, split_univ_sum a energy]
  convert hbound using 1 <;> ring

end SchauderBasisOrbits.Scalar
