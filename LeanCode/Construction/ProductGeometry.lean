module

public import LeanCode.Measure.Information
public import LeanCode.Construction.Iteration

@[expose] public section

open ContinuousLinearMap Submodule
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace SchauderBasisOrbits

noncomputable section

theorem product_prefix_arithmetic {u : ℝ} (hu : 0 < u) :
    Real.sqrt (1 + 3 * u) * Real.sqrt (1 + 14 * u) < 1 + 10 * u := by
  have h₁ : 0 ≤ 1 + 3 * u := by positivity
  have h₂ : 0 ≤ 1 + 14 * u := by positivity
  have h₃ : 0 ≤ 1 + 10 * u := by positivity
  apply (sq_lt_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h₃).mp
  rw [mul_pow, Real.sq_sqrt h₁, Real.sq_sqrt h₂]
  nlinarith [sq_nonneg u]

def angleLimit (K τ : ℝ) : ℝ :=
  let R := (1 + τ / K) ^ 2
  (R - 1) / (R + 1)

theorem angleLimit_bounds {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    0 < angleLimit K τ ∧ angleLimit K τ < 1 := by
  have hh := div_pos hτ hK
  have hR : 1 < (1 + τ / K) ^ 2 := by nlinarith [sq_nonneg (τ / K)]
  unfold angleLimit
  exact ⟨div_pos (sub_pos.mpr hR) (by positivity),
    (div_lt_one (by positivity)).mpr (by linarith)⟩

theorem angleLimit_slack {K τ β : ℝ} (hK : 0 < K) (hτ : 0 < τ)
    (hβ : 0 ≤ β) (hβ' : β < angleLimit K τ) :
    K * Real.sqrt ((1 + β) / (1 - β)) < K + τ := by
  have h1 : 0 < 1 - β := by linarith [(angleLimit_bounds hK hτ).2]
  have hR : 0 < (1 + τ / K) ^ 2 + 1 := by positivity
  change β < ((1 + τ / K) ^ 2 - 1) / ((1 + τ / K) ^ 2 + 1) at hβ'
  have hRatio : (1 + β) / (1 - β) < (1 + τ / K) ^ 2 := by
    apply (div_lt_iff₀ h1).mpr
    nlinarith [(lt_div_iff₀ hR).mp hβ']
  have hT : 0 ≤ 1 + τ / K := by positivity
  have hf : Real.sqrt ((1 + β) / (1 - β)) < 1 + τ / K := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) hT).mp
    rw [Real.sq_sqrt (div_nonneg (by linarith) h1.le)]
    exact hRatio
  calc
    _ < K * (1 + τ / K) := mul_lt_mul_of_pos_left hf hK
    _ = _ := by field_simp

/-- A common tolerance for all selected product blocks. -/
theorem exists_product_tolerance {N : ℕ} (hN : 0 < N) {K τ δ u : ℝ}
    (hK : 0 < K) (hτ : 0 < τ) (hδ : 0 < δ) (hu : 0 < u) :
    ∃ η : ℝ, 0 < η ∧
      (N : ℝ) * η < u ∧
      (N : ℝ) * η < (u / (1 + 2 * u)) / 2 ∧
      (N : ℝ) * η < δ / 2 ∧
      (N : ℝ) * η < angleLimit K τ ^ 2 ∧
      η < (14 - (Real.sqrt 3 + 2) ^ 2) * u := by
  have hc : 0 < u / (1 + 2 * u) := by positivity
  have hb := (angleLimit_bounds hK hτ).1
  have hs : (Real.sqrt 3 + 2) ^ 2 < 14 := by
    have h₀ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have h₁ : Real.sqrt 3 < 7 / 4 := (sq_lt_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      (by rw [h₀]; norm_num)
    nlinarith
  let M := min u (min ((u / (1 + 2 * u)) / 2) (min (δ / 2) (angleLimit K τ ^ 2)))
  have hM : 0 < M := lt_min hu (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  let η := min (M / (2 * (N : ℝ))) (((14 - (Real.sqrt 3 + 2) ^ 2) * u) / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hNη : (N : ℝ) * η < M := by
    calc
      _ ≤ (N : ℝ) * (M / (2 * (N : ℝ))) := mul_le_mul_of_nonneg_left (min_le_left ..) hN'.le
      _ = M / 2 := by field_simp
      _ < M := by linarith
  refine ⟨η, hη, hNη.trans_le (min_le_left ..),
    hNη.trans_le ((min_le_right ..).trans (min_le_left ..)),
    hNη.trans_le ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))),
    hNη.trans_le ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))), ?_⟩
  exact (min_le_right ..).trans_lt (by nlinarith [mul_pos (sub_pos.mpr hs) hu])

section Capture

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {n : ℕ} (D : CenteredSynthesis E H n)

theorem informationCapture_of_zero {J : E →L[ℂ] E} (hJ : J.IsPositive) {x : E} (hx : J x = 0) :
    informationCapture J x = 0 := by
  have ha : (1 + J) x = x := by simp [hx]
  have h := DFunLike.congr_fun (Ring.inverse_mul_cancel (1 + J) (isUnit_one_add_positive hJ)) x
  change Ring.inverse (1 + J) ((1 + J) x) = x at h
  rw [ha] at h
  rw [informationCapture_eq_one_sub_inverse hJ]
  change x - Ring.inverse (1 + J) x = 0
  rw [h, sub_self]

/-- Perturbing an information operator by `η` changes every capture
quadratic form by at most `η ‖x‖²`. -/
theorem informationCapture_quadratic_error {J J₀ : E →L[ℂ] E}
    (hJ : J.IsPositive) (hJ₀ : J₀.IsPositive)
    {η : ℝ} (hη : ‖J - J₀‖ ≤ η) (x : E) :
    |Complex.re ⟪x, informationCapture J x⟫_ℂ -
      Complex.re ⟪x, informationCapture J₀ x⟫_ℂ| ≤ η * ‖x‖ ^ 2 := by
  have heq : Complex.re ⟪x, informationCapture J x⟫_ℂ -
      Complex.re ⟪x, informationCapture J₀ x⟫_ℂ =
      Complex.re ⟪x, (informationCapture J - informationCapture J₀) x⟫_ℂ := by
    rw [sub_apply, inner_sub_right, Complex.sub_re]
  rw [heq]
  calc
    _ ≤ ‖⟪x, (informationCapture J - informationCapture J₀) x⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖(informationCapture J - informationCapture J₀) x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (η * ‖x‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.le_of_opNorm_le _ ((norm_informationCapture_sub_le hJ hJ₀).trans hη) _) (norm_nonneg _)
    _ = _ := by ring

theorem product_capture_estimates (hd : Function.Injective D.centered)
    (E₀ : Submodule ℂ E) {J₀ : E →L[ℂ] E} (hJ₀ : J₀.IsPositive)
    (hann : ∀ x ∈ E₀, J₀ x = 0) {η c : ℝ} (herr : ‖D.information - J₀‖ ≤ η)
    (e : E) (he : ‖e‖ = 1) (hc : c ≤ Complex.re ⟪e, informationCapture J₀ e⟫_ℂ) :
    haveI : FiniteDimensional ℂ (LinearMap.range D.full.toLinearMap) := Module.Finite.range _
    let F := LinearMap.range D.full.toLinearMap
    (∀ x ∈ E₀, ∀ y ∈ F, ‖⟪D.pullback x, y⟫_ℂ‖ ≤ Real.sqrt η * ‖x‖ * ‖y‖) ∧
    c - η ≤ ‖F.starProjection (D.pullback e)‖ ^ 2 := by
  let F := LinearMap.range D.full.toLinearMap
  let : FiniteDimensional ℂ F := Module.Finite.range _
  have hη := (norm_nonneg _).trans herr
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    have hzero := informationCapture_of_zero hJ₀ (hann x hx)
    have hbound := (abs_le.mp (informationCapture_quadratic_error (D.information_positive hd) hJ₀ herr x)).2
    rw [hzero, inner_zero_right, Complex.zero_re, sub_zero, ← D.starProjection_full_sq hd x] at hbound
    have hnorm : ‖F.starProjection (D.pullback x)‖ ≤ Real.sqrt η * ‖x‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hη]
      exact hbound
    rw [← F.starProjection_eq_self_iff.mpr hy, ← F.inner_starProjection_left_eq_right,
      F.starProjection_eq_self_iff.mpr hy]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  · have hbound := (abs_le.mp (informationCapture_quadratic_error (D.information_positive hd) hJ₀ herr e)).1
    rw [he, one_pow, mul_one, ← D.starProjection_full_sq hd e] at hbound
    linarith

/-- Approximating by the old projection plus the new projection of its residual. -/
theorem residual_capture_candidate (E₀ F : Submodule ℂ H)
    [E₀.HasOrthogonalProjection] [F.HasOrthogonalProjection] (f : H) {e : H} {d c : ℝ}
    (hr : f - E₀.starProjection f = d • e) (he : ‖e‖ = 1)
    (hd : d ≠ 0) (hcap : c < ‖F.starProjection e‖ ^ 2) :
    ∃ p ∈ E₀ ⊔ F, ‖f - p‖ ^ 2 < (1 - c) * d ^ 2 := by
  let r := f - E₀.starProjection f
  refine ⟨E₀.starProjection f + F.starProjection r,
    add_mem ((show E₀ ≤ E₀ ⊔ F from le_sup_left) (E₀.starProjection_apply_mem f))
      ((show F ≤ E₀ ⊔ F from le_sup_right) (F.starProjection_apply_mem r)), ?_⟩
  rw [← sub_sub, show f - E₀.starProjection f = r from rfl]
  change ‖r - F.starProjection r‖ ^ 2 < _
  have hsplit := F.norm_sq_eq_add_norm_sq_starProjection r
  rw [F.starProjection_orthogonal', sub_apply] at hsplit
  change ‖r‖ ^ 2 = ‖F.starProjection r‖ ^ 2 + ‖r - F.starProjection r‖ ^ 2 at hsplit
  have hrn : ‖r‖ ^ 2 = d ^ 2 := by
    rw [show r = d • e from hr, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  have hp : ‖F.starProjection r‖ ^ 2 = d ^ 2 * ‖F.starProjection e‖ ^ 2 := by
    rw [show r = d • e from hr, ContinuousLinearMap.map_smul_of_tower, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hrn, hp] at hsplit
  nlinarith [mul_lt_mul_of_pos_right hcap (sq_pos_of_ne_zero hd)]

end Capture

end

end SchauderBasisOrbits
