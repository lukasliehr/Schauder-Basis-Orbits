import LeanCode.Fourier.Characters
import Mathlib

open Filter MeasureTheory Complex
open scoped BigOperators Topology ComplexConjugate

namespace SchauderBasisOrbits

variable {ι : Type*} [Fintype ι]

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The product of normalized Haar probabilities on the unit-circle coordinates. -/
noncomputable abbrev torusHaar (ι : Type*) [Fintype ι] : Measure (UnitAddTorus ι) :=
  volume

instance torusHaar_probability (ι : Type*) [Fintype ι] : IsProbabilityMeasure (torusHaar ι) :=
  inferInstanceAs (IsProbabilityMeasure (volume : Measure (UnitAddTorus ι)))

theorem integrable_torusChar (k : ι → ℤ) : Integrable (torusChar k) (torusHaar ι) :=
  Integrable.of_bound (continuous_torusChar k).aestronglyMeasurable 1
    (Eventually.of_forall fun _ => (norm_torusChar _ _).le)

theorem integral_torusChar (k : ι → ℤ) :
    ∫ y, torusChar k y ∂torusHaar ι = if k = 0 then 1 else 0 := by
  classical
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := ι)) 0 k
  rw [ContinuousMap.inner_toLp] at h
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  simpa only [eq_comm] using h

/-- A finite Fourier test with integrable base coefficients. -/
structure FourierTest (μ : Measure ℝ) (ι : Type*) where
  coefficients : (ι → ℤ) →₀ (ℝ → ℂ)
  integrable_coeff : ∀ k ∈ coefficients.support, Integrable (coefficients k) μ

noncomputable def FourierTest.eval {μ : Measure ℝ} (G : FourierTest μ ι)
    (x : ℝ) (y : UnitAddTorus ι) : ℂ :=
  G.coefficients.sum fun k g => g x * torusChar k y

/-- Integer pairing of an auxiliary mode with a graph direction. -/
def modePairing (k ω : ι → ℤ) : ℤ := ∑ i, k i * ω i

/-- Choose an integer direction avoiding every listed nonzero mode. -/
theorem exists_integer_direction (L : Finset (ι → ℤ)) (hL : ∀ k ∈ L, k ≠ 0) :
    ∃ ω : ι → ℤ, ∀ k ∈ L, modePairing k ω ≠ 0 := by
  classical
  let e := Fintype.equivFin ι
  let p (k : ι → ℤ) : Polynomial ℤ :=
    ∑ i, Polynomial.C (k i) * Polynomial.X ^ (e i).val
  have hcoeff (k : ι → ℤ) (i : ι) : (p k).coeff (e i).val = k i := by
    change (∑ j : ι, Polynomial.C (k j) * Polynomial.X ^ (e j).val).coeff (e i).val = k i
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl]
    · intro j _ hji
      rw [Polynomial.coeff_C_mul_X_pow]
      exact ite_eq_right (fun h => hji (e.injective (Fin.val_injective h.symm)))
    · simp
  have hp (k : ι → ℤ) (hk : k ∈ L) : p k ≠ 0 := by
    intro h
    apply hL k hk
    funext i
    rw [← hcoeff k i, h, Polynomial.coeff_zero]
    rfl
  have hfin : (⋃ k ∈ (L : Set (ι → ℤ)), {b : ℤ | (p k).IsRoot b}).Finite :=
    L.finite_toSet.biUnion (fun k hk => Polynomial.finite_setOfPred_isRoot (hp k hk))
  obtain ⟨b, hb⟩ := hfin.exists_notMem
  refine ⟨fun i => b ^ (e i).val, fun k hk he => ?_⟩
  apply hb
  refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ?_⟩⟩
  change (p k).eval b = 0
  simpa only [p, Polynomial.eval_finsetSum, Polynomial.eval_C_mul, Polynomial.eval_X_pow,
    modePairing] using he

/-- The shear from the real line to the line times the unit torus. -/
noncomputable def graphPoint (ω : ι → ℤ) (j : ℕ) (x : ℝ) : ℝ × UnitAddTorus ι :=
  (x, fun i => ((j : ℝ) * (ω i : ℝ) * x : ℝ))

/-- A graph substitution preserves rational real frequencies. -/
def graphFrequency (ω : ι → ℤ) (j : ℕ) (b : MixedFreq ι) : ℚ :=
  b.1 + (j : ℚ) * (modePairing b.2 ω : ℚ)

theorem torusChar_graph (ω k : ι → ℤ) (j : ℕ) (x : ℝ) :
    torusChar k (graphPoint ω j x).2 = realChar ((j : ℝ) * (modePairing k ω : ℝ)) x := by
  simp only [torusChar, UnitAddTorus.mFourier, ContinuousMap.coe_mk, graphPoint,
    fourier_coe_apply, Complex.ofReal_one, div_one, realChar, modePairing, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mixedChar_graph (ω : ι → ℤ) (j : ℕ) (b : MixedFreq ι) (x : ℝ) :
    mixedChar b (graphPoint ω j x) = realChar (graphFrequency ω j b : ℝ) x := by
  rw [mixedChar, torusChar_graph]
  change realChar (b.1 : ℝ) x * realChar ((j : ℝ) * (modePairing b.2 ω : ℝ)) x =
    realChar (graphFrequency ω j b : ℝ) x
  rw [← realChar_add, graphFrequency]
  push_cast
  rfl

/-- Restrict a mixed Fourier polynomial to a graph, combining colliding coefficients. -/
noncomputable def restrictMixedPoly (ω : ι → ℤ) (j : ℕ) (p : MixedPoly ι) : RealPoly :=
  AddMonoidAlgebra.ofCoeff (p.coeff.mapDomain (graphFrequency ω j))

theorem eval_restrictMixedPoly (ω : ι → ℤ) (j : ℕ) (p : MixedPoly ι) (x : ℝ) :
    evalRealPoly (restrictMixedPoly ω j p) x = evalMixedPoly p (graphPoint ω j x) := by
  rw [evalRealPoly, restrictMixedPoly, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.sum_mapDomain_index (h := fun (b : ℚ) (c : ℂ) => c * realChar b x)
      (by simp) (fun _ _ _ => add_mul ..)]
  simp only [evalMixedPoly, mixedChar_graph]

section Averages

/-- Cesàro average of the first `N` unit phases, starting at index zero. -/
noncomputable def phaseAverage (N : ℕ) (t : ℝ) : ℂ :=
  (∑ j ∈ Finset.range N, realChar j t) / N

private theorem realChar_nat (j : ℕ) (t : ℝ) : realChar j t = realChar 1 t ^ j := by
  rw [realChar, realChar, ← Complex.exp_natCast_mul]
  congr 1
  push_cast
  ring

theorem norm_phaseAverage_le_one (N : ℕ) (t : ℝ) : ‖phaseAverage N t‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [phaseAverage, hN]
  have hpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [phaseAverage, norm_div, Complex.norm_natCast, div_le_iff₀ hpos, one_mul]
  simpa only [norm_realChar, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
    norm_sum_le (Finset.range N) (fun j => realChar j t)

theorem realChar_one_eq_one_iff (t : ℝ) : realChar 1 t = 1 ↔ ∃ k : ℤ, t = k := by
  rw [realChar, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hi := congrArg Complex.im hk
    simp [Complex.mul_im, Complex.mul_re] at hi
    nlinarith [Real.pi_pos]
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    ring

theorem norm_phaseAverage_le (N : ℕ) (t : ℝ) (ht : realChar 1 t ≠ 1) :
    ‖phaseAverage N t‖ ≤ (2 / ‖1 - realChar 1 t‖) / (N : ℝ) := by
  rw [phaseAverage, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hpos : 0 < ‖1 - realChar 1 t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ht.symm)
  rw [le_div_iff₀ hpos, ← norm_mul]
  simp only [realChar_nat, geom_sum_mul_neg]
  exact (norm_sub_le ..).trans (by simp [norm_pow]; norm_num)

theorem tendsto_phaseAverage_zero {t : ℝ} (ht : ¬ ∃ k : ℤ, t = k) :
    Tendsto (fun N => phaseAverage N t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => norm_phaseAverage_le N t
    ((realChar_one_eq_one_iff t).not.mpr ht))
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- Nonzero real multiples of the difference have no integer resonance almost
everywhere for a finite measure that vanishes on singletons. -/
theorem ae_no_integer_resonance (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (l : ℝ) (hl : l ≠ 0) :
    ∀ᵐ z ∂μ.prod μ, ¬ ∃ k : ℤ, l * (z.1 - z.2) = k := by
  let f : ℝ × ℝ → ℝ := fun z => l * (z.1 - z.2)
  let I : Set ℝ := Set.range (Int.cast : ℤ → ℝ)
  have hf : Measurable f := (continuous_const.mul (continuous_fst.sub continuous_snd)).measurable
  have hm : MeasurableSet (f ⁻¹' I) := hf (Set.countable_range _).measurableSet
  rw [ae_iff]
  change μ.prod μ {z | ¬ ¬ ∃ k : ℤ, l * (z.1 - z.2) = k} = 0
  convert (Measure.measure_prod_null (μ := μ) (ν := μ) hm).2 ?_ using 1
  · congr 1
    ext z
    simp [f, I, eq_comm]
  · filter_upwards with x
    apply measure_mono_null _ ((Set.countable_range (fun k : ℤ => x - (k : ℝ) / l)).measure_zero μ)
    intro y hy
    change f (x, y) ∈ I at hy
    obtain ⟨k, hk⟩ := hy
    refine ⟨k, ?_⟩
    dsimp [f] at hk
    have hh : x - y = (k : ℝ) / l := (eq_div_iff hl).2 (by simpa [mul_comm] using hk.symm)
    linarith

noncomputable def graphCoefficient (μ : Measure ℝ) (g : ℝ → ℂ) (l : ℝ) (j : ℕ) : ℂ :=
  ∫ x, g x * realChar ((j : ℝ) * l) x ∂μ

private theorem integrable_graphIntegrand {μ : Measure ℝ} {g : ℝ → ℂ}
    (hg : Integrable g μ) (t : ℝ) : Integrable (fun x => g x * realChar t x) μ :=
  hg.mul_bdd (continuous_realChar t).aestronglyMeasurable
    (Eventually.of_forall fun x => (norm_realChar t x).le)

private theorem phase_product (l : ℝ) (j : ℕ) (x y : ℝ) :
    realChar ((j : ℝ) * l) x * conj (realChar ((j : ℝ) * l) y) = realChar j (l * (x - y)) := by
  rw [← realChar_neg]
  simp only [realChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The mean square of the graph coefficients is the integral of one
geometric average over the base product measure. -/
theorem graphCoefficient_meanSquare {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℂ}
    (hg : Integrable g μ) (l : ℝ) (N : ℕ) :
    (↑((∑ j ∈ Finset.range N, ‖graphCoefficient μ g l j‖ ^ 2) / (N : ℝ)) : ℂ) =
      ∫ z, (g z.1 * conj (g z.2)) * phaseAverage N (l * (z.1 - z.2)) ∂μ.prod μ := by
  have hterm (j : ℕ) :
      Integrable (fun z : ℝ × ℝ => (g z.1 * conj (g z.2)) *
        realChar j (l * (z.1 - z.2))) (μ.prod μ) ∧
      (↑(‖graphCoefficient μ g l j‖ ^ 2) : ℂ) =
        ∫ z, (g z.1 * conj (g z.2)) * realChar j (l * (z.1 - z.2)) ∂μ.prod μ := by
    let a (x : ℝ) := g x * realChar ((j : ℝ) * l) x
    have ha : Integrable a μ := integrable_graphIntegrand hg _
    have hc : Integrable (fun x => conj (a x)) μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp ha
    have hpoint (z : ℝ × ℝ) :
        a z.1 * conj (a z.2) = (g z.1 * conj (g z.2)) * realChar j (l * (z.1 - z.2)) := by
      dsimp [a]
      rw [map_mul, ← phase_product l j z.1 z.2]
      ring
    refine ⟨(ha.mul_prod hc).congr (Eventually.of_forall hpoint), ?_⟩
    rw [integral_congr_ae (Eventually.of_forall fun z => (hpoint z).symm),
      integral_prod_mul a (fun x => conj (a x)), integral_conj]
    simpa only [Complex.ofReal_pow, graphCoefficient, a] using (Complex.mul_conj' (graphCoefficient μ g l j)).symm
  have hp (z : ℝ × ℝ) :
      (g z.1 * conj (g z.2)) * phaseAverage N (l * (z.1 - z.2)) =
        (∑ j ∈ Finset.range N, (g z.1 * conj (g z.2)) * realChar j (l * (z.1 - z.2))) / N := by
    rw [phaseAverage, ← mul_div_assoc, Finset.mul_sum]
  rw [integral_congr_ae (Eventually.of_forall hp), integral_div,
    integral_finsetSum _ (fun j _ => (hterm j).1)]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  exact fun j _ => by simpa only [Complex.ofReal_pow] using (hterm j).2

theorem tendsto_graphCoefficient_meanSquare {μ : Measure ℝ} [IsFiniteMeasure μ]
    [NullSingletonClass μ] {g : ℝ → ℂ} (hg : Integrable g μ) {l : ℝ} (hl : l ≠ 0) :
    Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, ‖graphCoefficient μ g l j‖ ^ 2) / (N : ℝ))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => ∫ z, (g z.1 * conj (g z.2)) *
      phaseAverage N (l * (z.1 - z.2)) ∂μ.prod μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (μ := μ.prod μ) (f := fun _ => (0 : ℂ))
        (fun z => ‖g z.1‖ * ‖g z.2‖)
        (fun N => by
          have hc : Integrable (fun x => conj (g x)) μ :=
            Complex.conjCLE.toContinuousLinearMap.integrable_comp hg
          refine (hg.mul_prod hc).aestronglyMeasurable.mul ?_
          exact (show Continuous (fun z : ℝ × ℝ => phaseAverage N (l * (z.1 - z.2))) by
            unfold phaseAverage realChar
            fun_prop).aestronglyMeasurable)
        (hg.norm.mul_prod hg.norm)
        (fun N => Eventually.of_forall fun z => by
          simp only [norm_mul, Complex.norm_conj]
          exact mul_le_of_le_one_right (by positivity) (norm_phaseAverage_le_one _ _))
        ((ae_no_integer_resonance μ l hl).mono fun z hz => by
          simpa only [mul_zero] using (tendsto_phaseAverage_zero hz).const_mul (g z.1 * conj (g z.2))))
  simpa only [Function.comp_def, ← graphCoefficient_meanSquare hg l,
    Complex.ofReal_re, Complex.zero_re] using (Complex.continuous_re.tendsto 0).comp ht

private theorem exists_small_of_mean_zero {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (ht : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, a j) / (N : ℝ)) atTop (𝓝 0))
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ j > N, a j < ε := by
  by_contra h
  push Not at h
  obtain ⟨M, hM⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists_forall_of_atTop
  let L := max (N + 1) M
  have hL : 0 < L := lt_of_lt_of_le (Nat.zero_lt_succ N) (le_max_left ..)
  have hlow : (L : ℝ) * ε ≤ ∑ j ∈ Finset.range (L + L), a j := by
    rw [Finset.sum_range_add]
    have hh : (L : ℝ) * ε ≤ ∑ j ∈ Finset.range L, a (L + j) := by
      simpa using (Finset.sum_le_sum (s := Finset.range L) (f := fun _ => ε)
        (g := fun j => a (L + j)) fun j _ => h _ (by
          have := le_max_left (N + 1) M
          change N + 1 ≤ L at this
          omega))
    exact hh.trans (le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => ha i))
  have hML : M ≤ L + L := le_trans (le_max_right ..) (Nat.le_add_right ..)
  have hup := hM _ hML
  have hn : 0 < ((L + L : ℕ) : ℝ) := by exact_mod_cast Nat.add_pos_left hL L
  have hm := (div_lt_iff₀ hn).mp hup
  push_cast at hm
  linarith

/-- One increasing subsequence makes every member of a finite collection of
sequences with vanishing Cesàro mean square tend to zero. -/
theorem common_meanSquare_subsequence {κ : Type*} [Fintype κ] (a : κ → ℕ → ℂ)
    (ha : ∀ k, Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, ‖a k j‖ ^ 2) / (N : ℝ))
      atTop (𝓝 0)) :
    ∃ j : ℕ → ℕ, (∀ n, 0 < j n) ∧ StrictMono j ∧
      ∀ k, Tendsto (fun n => a k (j n)) atTop (𝓝 0) := by
  classical
  let E (j : ℕ) := ∑ k, ‖a k j‖ ^ 2
  have hE : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, E j) / (N : ℝ)) atTop (𝓝 0) := by
    have hsum : Tendsto (fun N : ℕ => ∑ k, (∑ j ∈ Finset.range N, ‖a k j‖ ^ 2) / (N : ℝ))
        atTop (𝓝 (∑ _ : κ, (0 : ℝ))) :=
      tendsto_finsetSum _ (fun k _ => ha k)
    simpa only [Finset.sum_const_zero, ← Finset.sum_div, Finset.sum_comm (s := Finset.univ)] using hsum
  have hex (n N : ℕ) : ∃ j > N, E j < 1 / ((n : ℝ) + 1) :=
    exists_small_of_mean_zero (fun j => Finset.sum_nonneg fun _ _ => sq_nonneg _) hE N (by positivity)
  let step (n N : ℕ) := Classical.choose (hex n N)
  let j : ℕ → ℕ := Nat.rec (step 0 0) (fun n N => step (n + 1) N)
  have hj (n : ℕ) : E (j n) < 1 / ((n : ℝ) + 1) := by
    cases n with
    | zero => exact (Classical.choose_spec (hex 0 0)).2
    | succ n => exact (Classical.choose_spec (hex (n + 1) (j n))).2
  have hmono : StrictMono j :=
    strictMono_nat_of_lt_succ fun n => (Classical.choose_spec (hex (n + 1) (j n))).1
  refine ⟨j, fun n => lt_of_lt_of_le (Classical.choose_spec (hex 0 0)).1 (hmono.monotone (Nat.zero_le n)),
    hmono, fun k => ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero, tendsto_order]
  refine ⟨fun ε hε => Eventually.of_forall fun n => hε.trans_le (norm_nonneg _),
    fun ε hε => ?_⟩
  filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds (show 0 < ε ^ 2 by positivity))] with n hn
  have hle : ‖a k (j n)‖ ^ 2 ≤ E (j n) :=
    Finset.single_le_sum (f := fun k => ‖a k (j n)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  nlinarith [hle.trans_lt ((hj n).trans hn), norm_nonneg (a k (j n))]

end Averages

theorem FourierTest.integrable_all {μ : Measure ℝ} (G : FourierTest μ ι) (k : ι → ℤ) :
    Integrable (G.coefficients k) μ := by
  by_cases h : k ∈ G.coefficients.support
  · exact G.integrable_coeff k h
  · rw [Finsupp.notMem_support_iff.mp h]
    exact integrable_zero _ _ _

theorem FourierTest.integral_graph {μ : Measure ℝ} (G : FourierTest μ ι)
    (ω : ι → ℤ) (j : ℕ) :
    ∫ x, G.eval x (graphPoint ω j x).2 ∂μ =
      ∑ k ∈ G.coefficients.support, graphCoefficient μ (G.coefficients k) (modePairing k ω) j := by
  simp only [FourierTest.eval, Finsupp.sum, torusChar_graph, graphCoefficient]
  exact integral_finsetSum _ (fun k _ => integrable_graphIntegrand (G.integrable_all k) _)

theorem FourierTest.integral_prod {μ : Measure ℝ} [IsFiniteMeasure μ] (G : FourierTest μ ι) :
    ∫ z : ℝ × UnitAddTorus ι, G.eval z.1 z.2 ∂μ.prod (torusHaar ι) =
      ∑ k ∈ G.coefficients.support, if k = 0 then ∫ x, G.coefficients k x ∂μ else 0 := by
  classical
  simp only [FourierTest.eval, Finsupp.sum]
  rw [integral_finsetSum _ (fun k _ => (G.integrable_all k).mul_prod (integrable_torusChar k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_prod_mul (G.coefficients k) (torusChar k), integral_torusChar]
  split <;> simp

/-- A single graph direction and a single increasing sequence give the product
averages of all the tests and avoid all additional forbidden nonzero modes. -/
theorem simultaneous_graph_average {κ : Type*} [Fintype κ] {μ : Measure ℝ}
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (G : κ → FourierTest μ ι) (L : Finset (ι → ℤ)) (hL : ∀ k ∈ L, k ≠ 0) :
    ∃ (ω : ι → ℤ) (j : ℕ → ℕ), StrictMono j ∧
      (∀ k ∈ L, modePairing k ω ≠ 0) ∧
      ∀ r, Tendsto (fun n => ∫ x, (G r).eval x (graphPoint ω (j n) x).2 ∂μ) atTop
        (𝓝 (∫ z : ℝ × UnitAddTorus ι, (G r).eval z.1 z.2 ∂μ.prod (torusHaar ι))) := by
  classical
  let M := (L ∪ (Finset.univ.biUnion (fun r : κ => (G r).coefficients.support))).erase 0
  obtain ⟨ω, hω⟩ := exists_integer_direction M (fun _ h => (Finset.mem_erase.mp h).1)
  have hMem (r : κ) (k : ι → ℤ) (hk : k ∈ (G r).coefficients.support) (hne : k ≠ 0) :
      k ∈ M :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨r, Finset.mem_univ _, hk⟩)⟩
  let a (rk : κ × ↥M) (n : ℕ) :=
    graphCoefficient μ ((G rk.1).coefficients rk.2.val) (modePairing rk.2.val ω) n
  have ha (rk : κ × ↥M) := tendsto_graphCoefficient_meanSquare
    ((G rk.1).integrable_all rk.2.val) (l := (modePairing rk.2.val ω : ℝ)) (by
      exact_mod_cast hω rk.2.val rk.2.property)
  obtain ⟨j, _, hj, hlim⟩ := common_meanSquare_subsequence a ha
  refine ⟨ω, j, hj, fun k hk => hω k (Finset.mem_erase.mpr
    ⟨hL k hk, Finset.mem_union_left _ hk⟩), fun r => ?_⟩
  simp_rw [FourierTest.integral_graph, FourierTest.integral_prod]
  refine tendsto_finsetSum _ (fun k hk => ?_)
  by_cases h : k = 0
  · subst k
    have hzero : modePairing (0 : ι → ℤ) ω = 0 := by simp [modePairing]
    simp [hzero, graphCoefficient]
  · simpa only [ite_eq_right h, a] using hlim (r, ⟨k, hMem r k hk h⟩)

section PolynomialTests

variable {μ : Measure ℝ}

/-- Group the polynomial terms by their auxiliary frequencies, allowing an
integrable multiplier on the real coordinate. -/
noncomputable def polynomialFourierTest (p : MixedPoly ι) (g : ℝ → ℂ) (hg : Integrable g μ) :
    FourierTest μ ι := by
  classical
  let c (k : ι → ℤ) (x : ℝ) : ℂ :=
    ∑ b ∈ p.coeff.support, if b.2 = k then g x * realChar b.1 x * p.coeff b else 0
  let C := p.coeff.support.image Prod.snd
  have hsupport (k : ι → ℤ) (hk : c k ≠ 0) : k ∈ C := by
    by_contra h
    apply hk
    funext x
    apply Finset.sum_eq_zero
    intro b hb
    exact ite_eq_right (fun he => h (Finset.mem_image.mpr ⟨b, hb, he⟩))
  refine ⟨Finsupp.onFinset C c hsupport, fun k _ => ?_⟩
  rw [Finsupp.onFinset_apply]
  apply integrable_finsetSum
  intro b _
  by_cases h : b.2 = k
  · simpa only [h, ite_true] using (integrable_graphIntegrand hg (b.1 : ℝ)).mul_const (p.coeff b)
  · simp only [h, ite_false]
    change Integrable (0 : ℝ → ℂ) μ
    exact integrable_zero _ _ _

theorem polynomialFourierTest_eval (p : MixedPoly ι) (g : ℝ → ℂ) (hg : Integrable g μ)
    (x : ℝ) (y : UnitAddTorus ι) :
    (polynomialFourierTest p g hg).eval x y = g x * evalMixedPoly p (x, y) := by
  classical
  unfold FourierTest.eval polynomialFourierTest
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_onFinset_subset _ (by simp)]
  simp only [Finsupp.onFinset_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, evalMixedPoly, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [ite_eq_left (Finset.mem_image.mpr ⟨b, hb, rfl⟩)]
  unfold mixedChar
  dsimp
  ring

end PolynomialTests

private theorem eventually_affine_ne (b d s t : ℚ) (hst : s ≠ t) :
    ∀ᶠ n : ℕ in atTop, b + (n : ℚ) * s ≠ d + (n : ℚ) * t := by
  by_cases h : ∃ n : ℕ, b + (n : ℚ) * s = d + (n : ℚ) * t
  · obtain ⟨n, hn⟩ := h
    filter_upwards [eventually_gt_atTop n] with j hj hj'
    have heq : ((j : ℚ) - (n : ℚ)) * (s - t) = 0 := by linarith [hn, hj']
    rcases mul_eq_zero.mp heq with hz | hz
    · exact (ne_of_gt hj) (by exact_mod_cast sub_eq_zero.mp hz)
    · exact hst (sub_eq_zero.mp hz)
  · exact Eventually.of_forall fun n hn => h ⟨n, hn⟩

/-- Distinct nonzero integral slopes eventually separate all new rational
frequencies from each other and from a fixed finite set. -/
theorem eventually_affine_frequency_separation {κ : Type*} [Fintype κ] (b : κ → ℚ) (l : κ → ℤ)
    (hl : Function.Injective l) (hne : ∀ i, l i ≠ 0) (A : Finset ℚ) :
    ∀ᶠ n : ℕ in atTop,
      Function.Injective (fun i => b i + (n : ℚ) * (l i : ℚ)) ∧
      ∀ i, b i + (n : ℚ) * (l i : ℚ) ∉ A := by
  classical
  have hp : ∀ᶠ n : ℕ in atTop, ∀ i j : κ, i ≠ j →
      b i + (n : ℚ) * (l i : ℚ) ≠ b j + (n : ℚ) * (l j : ℚ) := by
    have h : ∀ᶠ n : ℕ in atTop, ∀ ij ∈ (Finset.univ : Finset (κ × κ)), ij.1 ≠ ij.2 →
        b ij.1 + (n : ℚ) * (l ij.1 : ℚ) ≠ b ij.2 + (n : ℚ) * (l ij.2 : ℚ) :=
      (Finset.eventually_all _).mpr fun ij _ => by
        by_cases hij : ij.1 = ij.2
        · exact Eventually.of_forall fun _ h => (h hij).elim
        · exact (eventually_affine_ne _ _ _ _ (by exact_mod_cast hl.ne hij)).mono fun _ h _ => h
    exact h.mono fun _ h i j => h (i, j) (Finset.mem_univ _)
  have hA : ∀ᶠ n : ℕ in atTop, ∀ i ∈ (Finset.univ : Finset κ), ∀ q ∈ A,
      b i + (n : ℚ) * (l i : ℚ) ≠ q :=
    (Finset.eventually_all _).mpr fun i _ =>
      (Finset.eventually_all _).mpr fun q _ => by
        simpa using (eventually_affine_ne (b i) q (l i : ℚ) 0 (by exact_mod_cast hne i))
  filter_upwards [hp, hA] with n hn hAn
  exact ⟨fun i j h => not_ne_iff.mp (fun hne' => hn i j hne' h),
    fun i hi => (hAn i (Finset.mem_univ _) _ hi) rfl⟩

end SchauderBasisOrbits
