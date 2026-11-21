import LeanCode.Scalar.Prefix

open MeasureTheory Matrix Complex
open scoped ENNReal ComplexConjugate ComplexOrder MatrixOrder

namespace SchauderBasisOrbits.Scalar

noncomputable local instance copiesCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance copiesCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (@AddCircle.haarAddCircle 1 _))

/-- Currying a finite product of coordinates preserves the product measure. -/
lemma measurePreserving_curry {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ X)
      (Measure.pi (fun _ : ι × κ => μ)) (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ))) := by
  classical
  let e := MeasurableEquiv.curry ι κ X
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs)]
  have hbox : e.symm ⁻¹' (Set.pi Set.univ s) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i, j))) := by
    ext x
    simp [e, MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hbox, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [← Finset.prod_product', Finset.univ_product_univ]

variable {r n : ℕ} (D : Data r n) (L : ℕ)

/-- The coordinates belonging to the given copy. -/
def copyPoint (x : UnitAddTorus (Fin (L * r))) (b : Fin L) : UnitAddTorus (Fin r) :=
  fun j => x (finProdFinEquiv (b, j))

@[simp] lemma copyPoint_neg (x : UnitAddTorus (Fin (L * r))) (b : Fin L) :
    copyPoint L (-x) b = -copyPoint L x b := rfl

/-- The weight of finitely many independent copies. -/
noncomputable def copiesWeight (x : UnitAddTorus (Fin (L * r))) : ℝ :=
  ∏ b : Fin L, D.w (copyPoint L x b)

lemma measurable_copiesWeight : Measurable (copiesWeight D L) := by
  unfold copiesWeight
  apply Finset.measurable_prod
  intro b hb
  apply D.measurable_w.comp
  exact Measurable.of_eval (fun j => measurable_pi_apply (finProdFinEquiv (b, j)))

/-- The mode is extended by zero outside the coordinate block assigned to its copy. -/
def copyMode (i : Fin (L * n)) (j : Fin (L * r)) : ℤ :=
  let (b, k) := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).symm i
  let (c, h) := (finProdFinEquiv : Fin L × Fin r ≃ Fin (L * r)).symm j
  if b = c then D.mode k h else 0

@[simp] lemma copyMode_apply (b c : Fin L) (k : Fin n) (h : Fin r) :
    copyMode D L (finProdFinEquiv (b, k)) (finProdFinEquiv (c, h)) =
      if b = c then D.mode k h else 0 := by
  simp [copyMode]

lemma copyMode_ne_zero (i : Fin (L * n)) : copyMode D L i ≠ 0 := by
  obtain ⟨⟨b, k⟩, rfl⟩ := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).surjective i
  intro hi
  apply D.mode_ne_zero k
  funext j
  simpa using congrFun hi (finProdFinEquiv (b, j))

lemma copyMode_inj : Function.Injective (copyMode D L) := by
  intro i j h
  obtain ⟨⟨b, k⟩, rfl⟩ := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).surjective i
  obtain ⟨⟨c, l⟩, rfl⟩ := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).surjective j
  have hbc : b = c := by
    by_contra! hbc
    apply D.mode_ne_zero k
    funext f
    simpa [Ne.symm hbc] using congrFun h (finProdFinEquiv (b, f))
  subst c
  have hkl : k = l := D.mode_inj (funext fun f => by
    simpa using congrFun h (finProdFinEquiv (b, f)))
  rw [hkl]

/-- Independent copies on disjoint coordinates, concatenated in copy-first order. -/
noncomputable def copies (hL : 0 < L) : Data (L * r) (L * n) where
  size_pos := Nat.mul_pos hL D.size_pos
  w := copiesWeight D L
  measurable_w := measurable_copiesWeight D L
  lower := D.lower ^ L
  lower_pos := pow_pos D.lower_pos L
  lower_le x := by
    unfold copiesWeight
    calc
      D.lower ^ L = ∏ _ : Fin L, D.lower := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => D.lower_pos.le) fun b _ => D.lower_le _
  le_one x := Finset.prod_le_one₀ (fun _ _ => D.w_nonneg _) (fun _ _ => D.le_one _)
  even_w x := by simp only [copiesWeight, copyPoint_neg, D.even_w]
  mode := copyMode D L
  mode_inj := copyMode_inj D L
  mode_ne_zero := copyMode_ne_zero D L

/-- Rearrange the coordinates into their copy blocks. -/
def copyPointEquiv :
    UnitAddTorus (Fin (L * r)) ≃ᵐ (Fin L → UnitAddTorus (Fin r)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin L × Fin r => UnitAddCircle)
    (finProdFinEquiv : Fin L × Fin r ≃ Fin (L * r)).symm).trans
      (MeasurableEquiv.curry (Fin L) (Fin r) UnitAddCircle)

lemma copyPointEquiv_apply (x : UnitAddTorus (Fin (L * r))) :
    copyPointEquiv (r := r) L x = copyPoint L x := by
  funext b j
  let e : Fin L × Fin r ≃ Fin (L * r) := finProdFinEquiv
  change MeasurableEquiv.piCongrLeft (fun _ : Fin L × Fin r => UnitAddCircle) e.symm x (b, j) =
    x (e (b, j))
  simpa only [Equiv.symm_apply_apply] using MeasurableEquiv.piCongrLeft_apply_apply e.symm
    (β := fun _ : Fin L × Fin r => UnitAddCircle) x (e (b, j))

lemma measurePreserving_copyPointEquiv :
    MeasurePreserving (copyPointEquiv (r := r) L) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin L × Fin r => UnitAddCircle)
    (finProdFinEquiv : Fin L × Fin r ≃ Fin (L * r)).symm
  exact (measurePreserving_curry (ι := Fin L) (κ := Fin r)
    (volume : Measure UnitAddCircle)).comp h

lemma copies_mass (hL : 0 < L) : (copies D L hL).mass = D.mass ^ L := by
  change (∫ x, ∏ b : Fin L, D.w (copyPoint L x b)) = D.mass ^ L
  simp_rw [← copyPointEquiv_apply]
  let f : (Fin L → UnitAddTorus (Fin r)) → ℝ := fun x => ∏ b, D.w (x b)
  change (∫ x, f (copyPointEquiv L x)) = _
  rw [(measurePreserving_copyPointEquiv (r := r) L).integral_comp' f]
  change (∫ x : Fin L → UnitAddTorus (Fin r), ∏ b, D.w (x b)) = _
  rw [integral_fintype_prod_volume_eq_pow]
  simp [Data.mass]


/-- The character index in one copy block, using 0 for the trivial character. -/
def copyLocalIndex (i : Fin (L * n + 1)) (b : Fin L) : Fin (n + 1) :=
  Fin.cases 0 (fun t =>
    let (c, k) := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).symm t
    if c = b then k.succ else 0) i

@[simp] lemma copyLocalIndex_zero (b : Fin L) :
    copyLocalIndex (n := n) L 0 b = 0 := rfl

@[simp] lemma copyLocalIndex_succ (b c : Fin L) (k : Fin n) :
    copyLocalIndex L (finProdFinEquiv (b, k)).succ c = (if b = c then k.succ else 0) := by
  unfold copyLocalIndex
  rw [Fin.cases_succ, Equiv.symm_apply_apply]

lemma copies_augMode_coord (hL : 0 < L) (i : Fin (L * n + 1)) (b : Fin L) (k : Fin r) :
    (copies D L hL).augMode i (finProdFinEquiv (b, k)) =
      D.augMode (copyLocalIndex L i b) k := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · obtain ⟨⟨c, l⟩, rfl⟩ := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).surjective j
    simp only [Data.augMode_succ, copies, copyMode_apply, copyLocalIndex_succ]
    by_cases hcb : c = b <;> simp [hcb]

lemma torusChar_copies (hL : 0 < L) (i : Fin (L * n + 1))
    (x : UnitAddTorus (Fin (L * r))) :
    torusChar ((copies D L hL).augMode i) x =
      ∏ b : Fin L, torusChar (D.augMode (copyLocalIndex L i b)) (copyPoint L x b) := by
  classical
  let f (k : Fin (L * r)) := fourier ((copies D L hL).augMode i k) (x k)
  change (∏ k, f k) = _
  rw [← (finProdFinEquiv : Fin L × Fin r ≃ Fin (L * r)).prod_comp f]
  rw [← Finset.univ_product_univ, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro b hb
  apply Finset.prod_congr rfl
  intro k hk
  simp [f, copies_augMode_coord, copyPoint]

/-- Each entry of the copied Gram is a product of its separate block moments. -/
lemma copies_complexGram (hL : 0 < L) (i j : Fin (L * n + 1)) :
    (copies D L hL).complexGram i j =
      ∏ b : Fin L, D.complexGram (copyLocalIndex L i b) (copyLocalIndex L j b) := by
  simp only [Data.complexGram, charGram, Matrix.of_apply, torusChar_copies]
  let f (b : Fin L) (y : UnitAddTorus (Fin r)) : ℂ :=
    (D.w y : ℂ) * conj (torusChar (D.augMode (copyLocalIndex L i b)) y) *
      torusChar (D.augMode (copyLocalIndex L j b)) y
  have heq (x : UnitAddTorus (Fin (L * r))) :
      (↑(∏ b : Fin L, D.w (copyPoint L x b)) : ℂ) *
        conj (∏ b : Fin L, torusChar (D.augMode (copyLocalIndex L i b)) (copyPoint L x b)) *
        (∏ b : Fin L, torusChar (D.augMode (copyLocalIndex L j b)) (copyPoint L x b)) =
          ∏ b, f b (copyPoint L x b) := by
    rw [ofReal_prod, map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  change (∫ x, (↑(∏ b : Fin L, D.w (copyPoint L x b)) : ℂ) *
      conj (∏ b : Fin L, torusChar (D.augMode (copyLocalIndex L i b)) (copyPoint L x b)) *
      (∏ b : Fin L, torusChar (D.augMode (copyLocalIndex L j b)) (copyPoint L x b))) = _
  simp_rw [heq, ← copyPointEquiv_apply]
  let g (z : Fin L → UnitAddTorus (Fin r)) : ℂ := ∏ b, f b (z b)
  change (∫ x, g (copyPointEquiv L x)) = _
  rw [(measurePreserving_copyPointEquiv (r := r) L).integral_comp' g]
  exact integral_fintype_prod_volume_eq_prod f

lemma copies_gram_div_mass (hL : 0 < L) (i j : Fin (L * n + 1)) :
    (copies D L hL).gram i j / (copies D L hL).mass =
      ∏ b : Fin L, (D.gram (copyLocalIndex L i b) (copyLocalIndex L j b) / D.mass) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_prod, Complex.ofReal_div, ← complexify_apply,
    Data.complexify_gram, copies_complexGram, copies_mass, Complex.ofReal_pow,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma copies_normalizedMean (hL : 0 < L) (b : Fin L) (k : Fin n) :
    (copies D L hL).normalizedMean (finProdFinEquiv (b, k)) = D.normalizedMean k := by
  simp only [Data.normalizedMean, Pi.smul_apply, smul_eq_mul, Data.meanColumn, ← div_eq_inv_mul]
  rw [copies_gram_div_mass]
  rw [Finset.prod_eq_single b]
  · simp
  · intro j hj hne
    simp [Ne.symm hne, D.gram_diag, D.mass_pos.ne']
  · simp


lemma copies_gram_div_mass_same (hL : 0 < L) (b : Fin L) (k l : Fin n) :
    (copies D L hL).gram (finProdFinEquiv (b, k)).succ (finProdFinEquiv (b, l)).succ /
      (copies D L hL).mass = D.gram k.succ l.succ / D.mass := by
  classical
  rw [copies_gram_div_mass, Finset.prod_eq_single b]
  · simp
  · intro j hj hne
    simp [Ne.symm hne, D.gram_diag, D.mass_pos.ne']
  · simp

lemma copies_gram_div_mass_different (hL : 0 < L) {b c : Fin L}
    (hbc : b ≠ c) (k l : Fin n) :
    (copies D L hL).gram (finProdFinEquiv (b, k)).succ (finProdFinEquiv (c, l)).succ /
      (copies D L hL).mass = D.normalizedMean k * D.normalizedMean l := by
  classical
  rw [copies_gram_div_mass, ← Finset.prod_erase_mul _ _ (Finset.mem_univ b), Finset.prod_eq_single c]
  · simp [hbc, Ne.symm hbc, D.gram_zero_succ, Data.meanColumn, Data.normalizedMean,
      div_eq_mul_inv]
    ring
  · intro j hj hjc
    have hjb : j ≠ b := (Finset.mem_erase.mp hj).1
    simp [Ne.symm hjb, Ne.symm hjc, D.gram_diag, D.mass_pos.ne']
  · simp [Ne.symm hbc]

/-- Repeated diagonal blocks, reindexed in copy-first order. -/
def blockCopies (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (L * n)) (Fin (L * n)) ℝ :=
  let e : Fin (L * n) ≃ Fin n × Fin L := finProdFinEquiv.symm.trans (Equiv.prodComm _ _)
  (Matrix.reindex e.symm e.symm) (Matrix.blockDiagonal (fun _ : Fin L => M))

lemma blockCopies_apply (M : Matrix (Fin n) (Fin n) ℝ) (b c : Fin L) (k l : Fin n) :
    blockCopies L M (finProdFinEquiv (b, k)) (finProdFinEquiv (c, l)) =
      if b = c then M k l else 0 := by
  classical
  simp [blockCopies, Matrix.blockDiagonal_apply]

lemma copies_normalizedGram (hL : 0 < L) :
    (copies D L hL).normalizedGram = blockCopies L D.normalizedGram := by
  ext i j
  obtain ⟨⟨b, k⟩, rfl⟩ := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).surjective i
  obtain ⟨⟨c, l⟩, rfl⟩ := (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).surjective j
  rw [Data.normalizedGram_apply, copies_normalizedMean, copies_normalizedMean, blockCopies_apply]
  by_cases hbc : b = c
  · subst c
    rw [copies_gram_div_mass_same, if_pos rfl, D.normalizedGram_apply]
  · rw [copies_gram_div_mass_different D L hL hbc, if_neg hbc, sub_self]

lemma blockCopies_mul (M N : Matrix (Fin n) (Fin n) ℝ) :
    blockCopies L M * blockCopies L N = blockCopies L (M * N) := by
  classical
  unfold blockCopies
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  exact (Matrix.blockDiagonal_mul _ _).symm

lemma blockCopies_one :
    blockCopies L (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  unfold blockCopies
  rw [show (fun _ : Fin L => (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 from rfl,
    Matrix.blockDiagonal_one]
  exact Matrix.submatrix_one_equiv _

lemma blockCopies_inv {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    (blockCopies L M)⁻¹ = blockCopies L M⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [blockCopies_mul, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 hM.isUnit), blockCopies_one]

lemma copies_normalizedGram_inv (hL : 0 < L) :
    (copies D L hL).normalizedGram⁻¹ = blockCopies L D.normalizedGram⁻¹ := by
  rw [copies_normalizedGram, blockCopies_inv L D.normalizedGram_posDef]


lemma blockCopies_mulVec_apply (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin (L * n) → ℝ)
    (b : Fin L) (k : Fin n) :
    (blockCopies L M *ᵥ v) (finProdFinEquiv (b, k)) =
      (M *ᵥ fun l => v (finProdFinEquiv (b, l))) k := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  let f (j : Fin (L * n)) := blockCopies L M (finProdFinEquiv (b, k)) j * v j
  change (∑ j, f j) = _
  rw [← (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).sum_comp f,
    ← Finset.univ_product_univ, Finset.sum_product]
  let g (c : Fin L) := ∑ l : Fin n, M k l * v (finProdFinEquiv (c, l))
  have hg (c : Fin L) : (∑ l : Fin n, f (finProdFinEquiv (c, l))) =
      if c = b then g c else 0 := by
    by_cases hc : c = b
    · subst c
      simp [f, g, blockCopies_apply]
    · simp [f, g, blockCopies_apply, hc, Ne.symm hc]
  simp_rw [hg]
  simp [g]

lemma copies_gain (hL : 0 < L) : (copies D L hL).gain = (L : ℝ) * D.gain := by
  unfold Data.gain
  rw [copies_normalizedGram_inv]
  let f (j : Fin (L * n)) := (copies D L hL).normalizedMean j *
    ((blockCopies L D.normalizedGram⁻¹) *ᵥ (copies D L hL).normalizedMean) j
  change (∑ j, f j) = _
  rw [← (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).sum_comp f,
    ← Finset.univ_product_univ, Finset.sum_product]
  have hf (b : Fin L) (k : Fin n) : f (finProdFinEquiv (b, k)) =
      D.normalizedMean k * (D.normalizedGram⁻¹ *ᵥ D.normalizedMean) k := by
    simp only [f, blockCopies_mulVec_apply, copies_normalizedMean]
  simp_rw [hf]
  simp [dotProduct, nsmul_eq_mul]

/-- The inverse diagonal of a copied datum is the corresponding inverse diagonal of the
one-copy centered matrix, divided by the mass of the other factors. -/
lemma copies_gram_inv_diagonal (hL : 0 < L) (b : Fin L) (j : Fin n) :
    (copies D L hL).gram⁻¹ (finProdFinEquiv (b, j)).succ (finProdFinEquiv (b, j)).succ =
      D.mass * D.centerGram⁻¹ j j / (copies D L hL).mass := by
  rw [Data.gram_inv_succ_succ]
  have hh := congrFun (congrFun (copies_normalizedGram_inv D L hL)
    (finProdFinEquiv (b, j))) (finProdFinEquiv (b, j))
  simp only [Data.normalizedGram_inv, Matrix.smul_apply, smul_eq_mul, blockCopies_apply,
    ite_true] at hh
  rw [eq_div_iff (copies D L hL).mass_pos.ne', mul_comm]
  exact hh


lemma qform_blockCopies (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin (L * n) → ℝ) :
    qform (blockCopies L M) v = ∑ b : Fin L, qform M (fun j => v (finProdFinEquiv (b, j))) := by
  simp only [qform, RCLike.re_to_real, star_trivial, dotProduct]
  let f (k : Fin (L * n)) := v k * (blockCopies L M *ᵥ v) k
  change (∑ j, f j) = _
  rw [← (finProdFinEquiv : Fin L × Fin n ≃ Fin (L * n)).sum_comp f,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp [f, blockCopies_mulVec_apply]

lemma blockCopies_pb {M : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (h : PB M K) :
    PB (blockCopies L M) K := by
  refine ⟨h.1, fun k hk v => ?_⟩
  rw [qform_blockCopies, qform_blockCopies, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  let j := min n (k - n * b.val)
  have ht : (fun i : Fin n => truncCoeff k v (finProdFinEquiv (b, i))) =
      truncCoeff j (fun i => v (finProdFinEquiv (b, i))) := by
    funext i
    unfold truncCoeff
    have he : (finProdFinEquiv (b, i)).val < k ↔ i.val < j := by
      change i.val + n * b.val < k ↔ i.val < min n (k - n * b.val)
      have hi := i.isLt
      omega
    simp only [he]
  rw [ht]
  exact h.2 j (Nat.min_le_left _ _) _

lemma copies_normalizedGram_pb (hL : 0 < L) {K : ℝ} (h : PB D.normalizedGram K) :
    PB (copies D L hL).normalizedGram K := by
  rw [copies_normalizedGram]
  exact blockCopies_pb L h

lemma copies_centerGram_pb (hL : 0 < L) {K : ℝ} (h : PB D.centerGram K) :
    PB (copies D L hL).centerGram K := by
  have hnorm : PB D.normalizedGram K := by
    refine ⟨h.1, fun k hk c => ?_⟩
    simp only [Data.normalizedGram, qform_smul]
    rw [mul_left_comm (K ^ 2)]
    exact mul_le_mul_of_nonneg_left (h.2 k hk c) (inv_nonneg.mpr D.mass_pos.le)
  let E := copies D L hL
  have hc := copies_normalizedGram_pb D L hL hnorm
  refine ⟨hc.1, fun k hk c => ?_⟩
  have ht := hc.2 k hk c
  change qform E.normalizedGram (truncCoeff k c) ≤ _ at ht
  simp only [Data.normalizedGram, qform_smul] at ht
  rw [mul_left_comm (K ^ 2)] at ht
  exact le_of_mul_le_mul_left ht (inv_pos.mpr E.mass_pos)

end SchauderBasisOrbits.Scalar
