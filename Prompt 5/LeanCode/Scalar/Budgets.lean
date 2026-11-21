import Mathlib

namespace SchauderBasisOrbits.Scalar

/-- The gain of the initial two-character system for initial loss `a`. -/
noncomputable def initialGain (a : ℝ) : ℝ :=
  a ^ 2 / (4 - 8 * a + 3 * a ^ 2)

lemma initialGain_bounds {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 400) :
    a ^ 2 / 4 ≤ initialGain a ∧ initialGain a ≤ a ^ 2 / 3 := by
  have ha2 : a ^ 2 ≤ a / 400 := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha')]
  have hlo : 3 ≤ 4 - 8 * a + 3 * a ^ 2 := by nlinarith [sq_nonneg a]
  have hhi : 4 - 8 * a + 3 * a ^ 2 ≤ 4 := by linarith
  unfold initialGain
  exact ⟨div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) hhi,
    div_le_div_of_nonneg_left (sq_nonneg a) (by linarith) hlo⟩

/-- The rare activation limit for the gain, before truncating the auxiliary modes. -/
noncomputable def activatedGain (e Z p : ℝ) : ℝ :=
  p / (1 - e) * (Z + e ^ 2 - p * e * (Z + e))

lemma activatedGain_bounds {e Z p : ℝ} (he : 0 < e) (he' : e < 1) (hZ : 0 < Z)
    (hp : 0 < p) (hp' : p ≤ e / (Z + e)) :
    0 < activatedGain e Z p ∧
      p * Z / (1 - e) ≤ activatedGain e Z p ∧
      activatedGain e Z p ≤ p * (Z + e ^ 2) / (1 - e) := by
  have hden : 0 < 1 - e := by linarith
  have hpe : p * (Z + e) ≤ e := (le_div_iff₀ (by positivity)).mp hp'
  have h₁ : p * e * (Z + e) ≤ e ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hpe he.le]
  have h₂ : 0 ≤ p * e * (Z + e) := by positivity
  unfold activatedGain
  constructor
  · exact mul_pos (div_pos hp hden) (by linarith)
  constructor
  · rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hp.le) hden.le
  · rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hp.le) hden.le

lemma exists_activation_parameter {e Z C cap : ℝ} (he : 0 < e) (he' : e < 1)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hcap : 0 < cap) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 / 100 ∧ p ≤ e / (Z + e) ∧ p * C ≤ e / 100 ∧
      0 < activatedGain e Z p ∧ activatedGain e Z p ≤ cap := by
  let p := min (1 / 100 : ℝ)
    (min (e / (Z + e)) (min (e / (100 * (C + 1))) (cap * (1 - e) / (Z + e ^ 2))))
  have hden : 0 < 1 - e := by linarith
  have hCp : 0 < C + 1 := by positivity
  have hZp : 0 < Z + e ^ 2 := by positivity
  have hp : 0 < p := by
    dsimp [p]
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hp₁ : p ≤ 1 / 100 := min_le_left _ _
  have hp₂ : p ≤ e / (Z + e) := (min_le_right _ _).trans (min_le_left _ _)
  have hp₃ : p ≤ e / (100 * (C + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hp₄ : p ≤ cap * (1 - e) / (Z + e ^ 2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC' := (le_div_iff₀ (show 0 < 100 * (C + 1) by positivity)).mp hp₃
  have hcap' := (le_div_iff₀ hZp).mp hp₄
  have h := activatedGain_bounds he he' hZ hp hp₂
  exact ⟨p, hp, hp₁, hp₂, by nlinarith, h.1,
    h.2.2.trans ((div_le_iff₀ hden).mpr hcap')⟩

/-- Two Bernoulli bounds, in the form used for the loss of a product of independent weights. -/
lemma product_loss_bounds {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1) (L : ℕ) :
    (L : ℝ) * t / (1 + (L : ℝ) * t) ≤ 1 - (1 - t) ^ L ∧
      1 - (1 - t) ^ L ≤ (L : ℝ) * t := by
  have ht₁ : 0 < 1 - t := by linarith
  have hL : 0 ≤ (L : ℝ) := by positivity
  have hinv : t ≤ (1 - t)⁻¹ - 1 := by
    rw [inv_eq_one_div, le_sub_iff_add_le, le_div_iff₀ ht₁]
    nlinarith [sq_nonneg t]
  have hbern := one_add_mul_sub_le_pow (a := (1 - t)⁻¹)
    (show (-1 : ℝ) ≤ (1 - t)⁻¹ from (by norm_num : (-1 : ℝ) ≤ 0).trans
      (inv_nonneg.mpr ht₁.le)) L
  have hprod : (1 + (L : ℝ) * t) * (1 - t) ^ L ≤ 1 := by
    have hle : 1 + (L : ℝ) * t ≤ ((1 - t) ^ L)⁻¹ := by
      rw [← inv_pow]
      exact (add_le_add_right (mul_le_mul_of_nonneg_left hinv hL) 1).trans hbern
    rwa [inv_eq_one_div, le_div_iff₀ (pow_pos ht₁ _)] at hle
  have hlower : (1 - t) ^ L ≤ 1 / (1 + (L : ℝ) * t) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hprod)
  have hupper := one_add_mul_sub_le_pow (a := 1 - t) (show (-1 : ℝ) ≤ 1 - t by linarith) L
  refine ⟨?_, by linarith⟩
  have hd : 0 < 1 + (L : ℝ) * t := by positivity
  rw [div_le_iff₀ hd]
  nlinarith [hprod]

/-- N05: the floor used for copying controls both the gain loss and the new mass loss. -/
lemma activation_copy_bounds {a e Z Z₀ p z : ℝ} (he : 0 < e) (hea : e ≤ a) (ha : a ≤ 1 / 400)
    (hZ : 3 * a ^ 2 / 16 ≤ Z) (hZ₀ : 3 * Z₀ / 4 ≤ Z) (hp : 0 < p) (hp₁ : p ≤ 1 / 100)
    (hp₂ : p ≤ e / (Z + e)) (hz₁ : (1 - e / 4) * activatedGain e Z p ≤ z)
    (hz₂ : z ≤ activatedGain e Z p) (hz₃ : z ≤ Z₀ / 8) :
    let L := ⌊Z / z⌋₊
    let e' := 1 - (1 - p * e) ^ L
    1 ≤ L ∧ 0 ≤ Z - L * z ∧ Z - L * z < z ∧
    1 / 10 < (L : ℝ) * p ∧ (L : ℝ) * p ≤ 1 - 3 * e / 4 ∧
    e / 12 ≤ e' ∧ e' ≤ e - 3 * e ^ 2 / 4 := by
  dsimp
  let L := ⌊Z / z⌋₊
  have ha₀ : 0 < a := he.trans_le hea
  have hZpos : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have he' : e < 1 := by linarith
  have hd : 0 < 1 - e := by linarith
  have hd' : 0 < 1 - e / 4 := by linarith
  have h := activatedGain_bounds he he' hZpos hp hp₂
  have hz : 0 < z := (mul_pos hd' h.1).trans_le hz₁
  have hZ₀pos : 0 < Z₀ := by linarith
  have hL : 1 ≤ L := (Nat.one_le_floor_iff _).mpr ((le_div_iff₀ hz).mpr (by linarith))
  have hfloor₁ : (L : ℝ) ≤ Z / z := Nat.floor_le (by positivity)
  have hfloor₂ : Z / z < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hgain₁ := (le_div_iff₀ hz).mp hfloor₁
  have hgain₂ := (div_lt_iff₀ hz).mp hfloor₂
  have hLp₁ : (L : ℝ) * p ≤ 1 - 3 * e / 4 := by
    have hh : p * Z * (1 - e / 4) ≤ z * (1 - e) := by
      have hmul := mul_le_mul_of_nonneg_left h.2.1 hd'.le
      rw [← mul_div_assoc] at hmul
      have hdiv := (div_le_iff₀ hd).mp (hmul.trans hz₁)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hq : p * Z / z ≤ (1 - e) / (1 - e / 4) := by
      rw [div_le_div_iff₀ hz hd']
      linarith only [hh, show z * (1 - e) = (1 - e) * z by ring]
    have hf := mul_le_mul_of_nonneg_left hfloor₁ hp.le
    have hf' : (L : ℝ) * p ≤ p * Z / z := by
      rw [← mul_div_assoc] at hf
      simpa only [mul_comm p] using hf
    refine (hf'.trans hq).trans ((div_le_iff₀ hd').mpr ?_)
    nlinarith [sq_nonneg e]
  have hLp₀ : 1 / 10 < (L : ℝ) * p := by
    have hden : 0 < Z + e ^ 2 := by positivity
    have hupper := (le_div_iff₀ hd).mp (hz₂.trans h.2.2)
    have hfrac : (1 - e) * Z / (Z + e ^ 2) ≤ p * Z / z := by
      rw [div_le_div_iff₀ hden hz]
      calc
        (1 - e) * Z * z = Z * (z * (1 - e)) := by ring
        _ ≤ Z * (p * (Z + e ^ 2)) := mul_le_mul_of_nonneg_left hupper hZpos.le
        _ = p * Z * (Z + e ^ 2) := by ring
    have he2 : e ^ 2 ≤ a ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hea) (show 0 ≤ a + e by positivity)]
    have hratio : 3 / 19 ≤ Z / (Z + e ^ 2) := by
      rw [le_div_iff₀ hden]
      linarith
    have hratio₂ : (1 - 1 / 400) * (3 / 19 : ℝ) ≤ (1 - e) * Z / (Z + e ^ 2) := by
      rw [mul_div_assoc]
      exact mul_le_mul (by linarith) hratio (by norm_num) hd.le
    have hh := mul_lt_mul_of_pos_left hfloor₂ hp
    rw [← mul_div_assoc, mul_add, mul_one] at hh
    nlinarith
  have ht : 0 < p * e := mul_pos hp he
  have ht₁ : p * e < 1 := by
    have := mul_le_mul_of_nonneg_right hp₁ he.le
    nlinarith
  have hprod := product_loss_bounds ht.le ht₁ L
  have hle : (L : ℝ) * (p * e) ≤ e := by nlinarith [mul_le_mul_of_nonneg_right hLp₁ he.le, sq_nonneg e]
  have hgt : e / 10 < (L : ℝ) * (p * e) := by nlinarith [mul_lt_mul_of_pos_right hLp₀ he]
  have hr : e / 12 ≤ (L : ℝ) * (p * e) / (1 + (L : ℝ) * (p * e)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hle he.le,
      mul_le_mul_of_nonneg_right (show e ≤ 1 / 5 by linarith) he.le]
  exact ⟨hL, by linarith, by linarith, hLp₀, hLp₁, hr.trans hprod.1,
    hprod.2.trans (by nlinarith [mul_le_mul_of_nonneg_right hLp₁ he.le])⟩


/-- The block-gain envelope. Activation at stage `n` gives the second branch. -/
noncomputable def etaBound (Z₀ : ℝ) : ℕ → ℝ
  | 0 => Z₀
  | n + 1 => Z₀ * (1 / 2) ^ n / 8

lemma sum_etaBound_succ (Z₀ : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), etaBound Z₀ j =
      Z₀ + Z₀ * (1 - (1 / 2 : ℝ) ^ n) / 4 := by
  induction n with
  | zero => simp [etaBound]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, etaBound, pow_succ]
    ring

lemma sum_etaBound_le {Z₀ : ℝ} (hZ₀ : 0 ≤ Z₀) (n : ℕ) :
    ∑ j ∈ Finset.range n, etaBound Z₀ j ≤ 5 * Z₀ / 4 := by
  cases n with
  | zero => simpa using (show (0 : ℝ) ≤ 5 * Z₀ / 4 by positivity)
  | succ n =>
    rw [sum_etaBound_succ]
    nlinarith [show 0 ≤ Z₀ * (1 / 2 : ℝ) ^ n by positivity]

lemma etaBound_le {Z₀ : ℝ} (hZ₀ : 0 ≤ Z₀) (n : ℕ) : etaBound Z₀ n ≤ Z₀ := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [etaBound]
    have h := pow_le_one₀ (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) (n := n)
    nlinarith [mul_le_of_le_one_right hZ₀ h]

/-- Scalar bound used by both the induction and the final scalar supply. -/
lemma induction_budget_bounds {δ Z₀ Z U V : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hZ₀ : 0 ≤ Z₀) (hZ₀' : Z₀ ≤ (δ / 400) ^ 2 / 3) (hZ : Z ≤ Z₀)
    (hU : 0 ≤ U) (hU' : U ≤ 5 * Z₀ / 4)
    (hV : 0 ≤ V) (hV' : V ≤ 4 * (δ / 400) / 3) :
    let Q := 1 + δ / 4 + 20 * U / δ + V / 2
    1 + δ / 4 ≤ Q ∧ Q ≤ 1 + δ / 4 + 30 * Z₀ / δ + 2 * (δ / 400) / 3 ∧
      Q < 1 + δ / 2 ∧ δ / 8 < Q - 1 - Z ∧ Q ^ 2 / (Q - 1 - Z) < 20 / δ := by
  let Q := 1 + δ / 4 + 20 * U / δ + V / 2
  change 1 + δ / 4 ≤ Q ∧ _ ∧ Q < 1 + δ / 2 ∧ δ / 8 < Q - 1 - Z ∧ _
  have hQ₀ : 1 + δ / 4 ≤ Q := by
    dsimp [Q]
    linarith only [show 0 ≤ 20 * U / δ by positivity, hV]
  have hZ₁ : 30 * Z₀ / δ ≤ δ / 16000 := by
    rw [div_le_iff₀ hδ]
    nlinarith only [hZ₀']
  have hQb : Q ≤ 1 + δ / 4 + 30 * Z₀ / δ + 2 * (δ / 400) / 3 := by
    have hUdiv : 20 * U / δ ≤ 30 * Z₀ / δ := by
      exact div_le_div_of_nonneg_right (by linarith) hδ.le
    dsimp [Q]
    linarith
  have hQ : Q < 1 + δ / 2 := by linarith
  have hδ₂ : δ ^ 2 ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ')]
  have hgap : δ / 8 < Q - 1 - Z := by linarith [show (δ / 400) ^ 2 = δ ^ 2 / 160000 by ring]
  have hgap₀ : 0 < Q - 1 - Z := lt_trans (by positivity) hgap
  have hQsq : Q ^ 2 ≤ 9 / 4 := by
    have hu : Q ≤ 3 / 2 := by linarith
    have hqpos : 0 ≤ Q := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ 3 / 2 + Q by positivity)]
  refine ⟨hQ₀, hQb, hQ, hgap, ?_⟩
  rw [div_lt_div_iff₀ hgap₀ hδ]
  change Q ^ 2 * δ < 20 * (Q - 1 - Z)
  nlinarith only [mul_lt_mul_of_pos_left hgap (show (0 : ℝ) < 20 by norm_num),
    mul_le_mul_of_nonneg_right hQsq hδ.le, hδ]

lemma gain_budget_step {Z₀ Z Z' : ℝ} {n : ℕ}
    (hZ : Z₀ - Z ≤ Z₀ * (1 - (1 / 2) ^ n) / 4)
    (hloss : Z - Z' ≤ etaBound Z₀ (n + 1)) :
    Z₀ - Z' ≤ Z₀ * (1 - (1 / 2) ^ (n + 1)) / 4 := by
  rw [etaBound] at hloss
  rw [pow_succ]
  linarith

lemma loss_budget_step {a e e' V : ℝ}
    (hV : V ≤ 4 * (a - e) / 3) (he' : e' ≤ e - 3 * e ^ 2 / 4) :
    V + e ^ 2 ≤ 4 * (a - e') / 3 := by linarith

lemma inverse_diagonal_step_arithmetic {e e' M C p d : ℝ}
    (he' : 0 < e') (hsmall : e' ≤ 1 / 400) (he : e ≤ 12 * e')
    (hpC : p * C ≤ e / 100) (hM : M ≤ 1) (hMp : 0 ≤ 1 + p * C)
    (hd : d ≤ M * (1 + p * C)) :
    d / (1 - e') ≤ 1 + 2 * e' := by
  have hM' := mul_le_mul_of_nonneg_right hM hMp
  rw [one_mul] at hM'
  have hden : 0 < 1 - e' := by linarith
  have he₂ : e' ^ 2 ≤ e' / 400 :=
    by nlinarith [mul_le_mul_of_nonneg_right hsmall he'.le]
  rw [div_le_iff₀ hden]
  nlinarith only [hd, hM', hpC, he, he', he₂]

/-- Scalar comparison used after bounding the inverse norm by the trace bound. -/
lemma inverse_floor_step_arithmetic {e e' Z₀ h : ℝ} (he : 0 < e) (he' : 0 < e')
    (hsmall : e ≤ 1 / 400) (hdec : e' ≤ e - 3 * e ^ 2 / 4)
    (hZ₀ : Z₀ ≤ (1 / 400 : ℝ) ^ 2 / 3) (hh : h ≤ 1 / e ^ 2) :
    (h + 1 + Z₀) / (1 - e') ≤ 1 / e' ^ 2 := by
  let x := e - 3 * e ^ 2 / 4
  have hx : 0 < x := he'.trans_le hdec
  have hxe : x ≤ e := by dsimp [x]; nlinarith [sq_nonneg e]
  have hx₁ : 0 < 1 - x := by linarith
  have he₁ : 0 < 1 - e' := by linarith [hdec.trans hxe]
  have hden : 0 < 1 - 3 * e / 4 := by linarith
  have hfrac : 1 / e ^ 2 + 1 / (2 * e) ≤ (1 - x) / x ^ 2 := by
    rw [add_comm]
    have heq : (1 - x) / x ^ 2 - 1 / e ^ 2 =
        (1 / 2 + 3 * e / 16) / (e * (1 - 3 * e / 4) ^ 2) := by
      have hx₂ := pow_ne_zero 2 hx.ne'
      have he₂ := pow_ne_zero 2 he.ne'
      rw [div_sub_div (1 - x) 1 hx₂ he₂]
      apply (div_eq_div_iff (mul_ne_zero hx₂ he₂)
        (mul_ne_zero he.ne' (pow_ne_zero 2 hden.ne'))).mpr
      dsimp [x]
      ring
    rw [← le_sub_iff_add_le, heq, div_le_div_iff₀ (by positivity) (by positivity)]
    have hdsq : (1 - 3 * e / 4) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ 3 * e / 4 by positivity)
        (show 0 ≤ 1 + (1 - 3 * e / 4) by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hdsq he.le, sq_nonneg e]
  have hfrac' : (1 - x) / x ^ 2 ≤ (1 - e') / e' ^ 2 := by
    have hs : e' ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ he'.le hdec 2
    exact (div_le_div_of_nonneg_right (show 1 - x ≤ 1 - e' by linarith only
      [show e' ≤ x from hdec]) (sq_nonneg x)).trans
        (div_le_div_of_nonneg_left he₁.le (sq_pos_of_pos he') hs)
  have hZ₁ : 1 + Z₀ ≤ 1 / (2 * e) := by
    have hm := mul_le_mul_of_nonneg_right hZ₀ (show 0 ≤ 2 * e by positivity)
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hm, hsmall]
  rw [div_le_div_iff₀ he₁ (sq_pos_of_pos he')]
  have hh' : h + 1 + Z₀ ≤ (1 - e') / e' ^ 2 :=
    (by linarith only [hh, hZ₁, hfrac, hfrac'] : _)
  simpa only [one_mul] using (le_div_iff₀ (sq_pos_of_pos he')).mp hh'

lemma first_row_step_arithmetic {a e Z : ℝ} (he : 0 ≤ e) (hea : e ≤ a)
    (ha : a ≤ 1 / 400) (hZ : 0 ≤ Z) (hZ' : Z ≤ a ^ 2 / 3) :
    1 + Z + e * (Z + e) / (4 * (1 - e)) ≤ 1 + a ^ 2 := by
  have hapos : 0 ≤ a := he.trans hea
  have ha₂ : a ^ 2 ≤ a := by nlinarith [mul_nonneg hapos (show 0 ≤ 1 - a by linarith)]
  have hdiv : e * (Z + e) / (4 * (1 - e)) ≤ 5 * a ^ 2 / 12 := by
    have hmul : e * (Z + e) ≤ a * (4 * a / 3) :=
      mul_le_mul hea (by linarith) (by positivity) hapos
    rw [div_le_iff₀ (show 0 < 4 * (1 - e) by linarith)]
    have hden : 4 / 5 ≤ 1 - e := by linarith
    nlinarith only [hmul, mul_le_mul_of_nonneg_left hden (show 0 ≤ a ^ 2 by positivity)]
  nlinarith only [hdiv, hZ', sq_nonneg a]

open Filter Topology in
/-- The verified loss recurrence implies that the losses tend to zero. -/
lemma tendsto_zero_of_loss_recurrence {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n)
    (hdec : ∀ n, e (n + 1) ≤ e n - 3 * (e n) ^ 2 / 4) :
    Tendsto e atTop (𝓝 0) := by
  have hant : Antitone e := antitone_nat_of_succ_le fun n => by
    linarith [hdec n, sq_nonneg (e n)]
  have hsum (N : ℕ) : ∑ j ∈ Finset.range N, (e j) ^ 2 ≤ 4 * (e 0 - e N) / 3 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hdec N]
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * e 0 / (3 * r ^ 2))
  have hN' : e N < r := by
    by_contra! h
    have hs : (N : ℝ) * r ^ 2 ≤ ∑ j ∈ Finset.range N, (e j) ^ 2 := by
      calc
        _ = ∑ _ ∈ Finset.range N, r ^ 2 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j hj => by
          have hje := h.trans (hant (Finset.mem_range.mp hj).le)
          exact pow_le_pow_left₀ hr.le hje 2)
    have hNu := (div_lt_iff₀ (show 0 < 3 * r ^ 2 by positivity)).mp hN
    nlinarith only [hNu, hs, hsum N, he N]
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he n)]
  exact (hant hn).trans_lt hN'

/-- Initial loss for a scalar supply with prefix slack `δ`. -/
noncomputable def initialLoss (δ : ℝ) : ℝ := δ / 400

noncomputable def gainCap (δ : ℝ) : ℝ := initialGain (initialLoss δ)

noncomputable def budgetQ (δ U V : ℝ) : ℝ := 1 + δ / 4 + 20 * U / δ + V / 2

noncomputable def commonBound (δ : ℝ) : ℝ := Real.sqrt (1 + δ / 2 + δ / 24000)

lemma gainCap_bounds {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    initialLoss δ ^ 2 / 4 ≤ gainCap δ ∧ gainCap δ ≤ initialLoss δ ^ 2 / 3 :=
  initialGain_bounds (by unfold initialLoss; positivity) (by unfold initialLoss; linarith)

lemma commonBound_lt_one_add {δ : ℝ} (hδ : 0 < δ) : commonBound δ < 1 + δ := by
  unfold commonBound
  have hh : 0 ≤ 1 + δ / 2 + δ / 24000 := by positivity
  apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
  rw [Real.sq_sqrt hh]
  nlinarith [sq_nonneg δ]

end SchauderBasisOrbits.Scalar
