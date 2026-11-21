import Mathlib

open Filter
open scoped Topology

namespace SchauderBasisOrbits

noncomputable section

/-- Trace of the two-dimensional seed block, after division by the seed mass. -/
def seedTrace (θ L : ℝ) : ℝ := 1 + (1 - θ) + L * θ

def seedDiscriminant (θ L : ℝ) : ℝ := Real.sqrt (seedTrace θ L ^ 2 - 4 * (1 - θ))

def seedSmallEigenvalue (θ L : ℝ) : ℝ := (seedTrace θ L - seedDiscriminant θ L) / 2

def seedLargeEigenvalue (θ L : ℝ) : ℝ := (seedTrace θ L + seedDiscriminant θ L) / 2

def seedRatio (θ L : ℝ) : ℝ := (seedSmallEigenvalue θ L)⁻¹

def seedDirectionFraction (θ L : ℝ) : ℝ :=
  (seedLargeEigenvalue θ L - 1) / (seedLargeEigenvalue θ L - seedSmallEigenvalue θ L)

theorem seed_trace_discriminant {θ L : ℝ} (hθ : 0 < θ) (hL : 1 ≤ L) :
    0 < seedTrace θ L ^ 2 - 4 * (1 - θ) := by
  have h := mul_nonneg (sub_nonneg.mpr hL) hθ.le
  unfold seedTrace
  nlinarith [sq_nonneg ((L - 1) * θ)]

theorem seed_eigenvalues_sum (θ L : ℝ) :
    seedSmallEigenvalue θ L + seedLargeEigenvalue θ L = seedTrace θ L := by
  unfold seedSmallEigenvalue seedLargeEigenvalue
  ring

theorem seed_eigenvalues_prod {θ L : ℝ} (hθ : 0 < θ) (hL : 1 ≤ L) :
    seedSmallEigenvalue θ L * seedLargeEigenvalue θ L = 1 - θ := by
  have h : seedDiscriminant θ L ^ 2 = seedTrace θ L ^ 2 - 4 * (1 - θ) :=
    Real.sq_sqrt (seed_trace_discriminant hθ hL).le
  unfold seedSmallEigenvalue seedLargeEigenvalue
  nlinarith

theorem seed_eigenvalues_order {θ L : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (hL : 1 ≤ L) :
    0 < seedSmallEigenvalue θ L ∧ seedSmallEigenvalue θ L < 1 ∧ 1 < seedLargeEigenvalue θ L := by
  let γ := seedSmallEigenvalue θ L
  let Γ := seedLargeEigenvalue θ L
  have hsum : γ + Γ = seedTrace θ L := seed_eigenvalues_sum θ L
  have hprod : γ * Γ = 1 - θ := seed_eigenvalues_prod hθ hL
  have hs : γ ≤ Γ := by
    unfold γ Γ seedSmallEigenvalue seedLargeEigenvalue
    have h : 0 ≤ seedDiscriminant θ L := Real.sqrt_nonneg _
    linarith
  have hΓpos : 0 < Γ := by
    have ht : 0 < seedTrace θ L := by
      unfold seedTrace
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) hθ.le]
    linarith
  have hγpos : 0 < γ := pos_of_mul_pos_left (hprod ▸ sub_pos.mpr hθ') hΓpos.le
  have hstraddle : (1 - γ) * (Γ - 1) = L * θ := by
    unfold seedTrace at hsum
    nlinarith
  have hstraddle' : 0 < (1 - γ) * (Γ - 1) := hstraddle ▸ mul_pos (by linarith) hθ
  have hγlt : γ < 1 := by
    by_contra h
    exact not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) hstraddle'
  have hΓgt : 1 < Γ := by
    by_contra h
    exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) hstraddle'
  exact ⟨hγpos, hγlt, hΓgt⟩

theorem seed_ratio_bounds {θ L : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (hL : 1 ≤ L) :
    1 + θ * L / (1 - θ) ≤ seedRatio θ L ∧ seedRatio θ L ≤ (2 + θ * L) / (1 - θ) := by
  have hord := seed_eigenvalues_order hθ hθ' hL
  have hsum := seed_eigenvalues_sum θ L
  have hprod := seed_eigenvalues_prod hθ hL
  have hr : seedRatio θ L = seedLargeEigenvalue θ L / (1 - θ) := by
    unfold seedRatio
    rw [← hprod]
    field_simp [hord.1.ne', (show 0 < seedLargeEigenvalue θ L by linarith [hord.2.2]).ne']
  rw [hr]
  have ha : 0 < 1 - θ := sub_pos.mpr hθ'
  unfold seedTrace at hsum
  constructor
  · apply (le_div_iff₀ ha).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ ha.ne']
    linarith [hord.2.1, mul_comm θ L]
  · exact div_le_div_of_nonneg_right (by linarith [hord.1, mul_comm θ L]) ha.le

theorem seed_fraction_bounds {θ L : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (hL : 1 ≤ L) :
    0 ≤ seedDirectionFraction θ L ∧ seedDirectionFraction θ L ≤ 1 := by
  obtain ⟨hγ, hγ', hΓ⟩ := seed_eigenvalues_order hθ hθ' hL
  have hd : 0 < seedLargeEigenvalue θ L - seedSmallEigenvalue θ L := by linarith
  unfold seedDirectionFraction
  exact ⟨div_nonneg (sub_nonneg.mpr hΓ.le) hd.le, (div_le_one hd).mpr (by linarith)⟩

theorem seed_fraction_error {θ L : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (hL : 1 < L) :
    1 - seedDirectionFraction θ L ≤ 1 / (θ * (L - 1)) := by
  obtain ⟨hγ, hγ', hΓ⟩ := seed_eigenvalues_order hθ hθ' hL.le
  have hsum := seed_eigenvalues_sum θ L
  unfold seedTrace at hsum
  have h₁ : 0 < seedLargeEigenvalue θ L - 1 := by linarith
  have h₂ : 0 < seedLargeEigenvalue θ L - seedSmallEigenvalue θ L := by linarith
  have hes : 1 - seedDirectionFraction θ L =
      (1 - seedSmallEigenvalue θ L) / (seedLargeEigenvalue θ L - seedSmallEigenvalue θ L) := by
    unfold seedDirectionFraction
    field_simp
    ring
  rw [hes]
  calc
    _ ≤ 1 / (seedLargeEigenvalue θ L - seedSmallEigenvalue θ L) :=
      div_le_div_of_nonneg_right (by linarith) h₂.le
    _ ≤ 1 / (seedLargeEigenvalue θ L - 1) :=
      one_div_le_one_div_of_le h₁ (by linarith)
    _ ≤ _ := one_div_le_one_div_of_le (mul_pos hθ (by linarith)) (by nlinarith [hγ'])

/-- Once a seed size and ratio have been fixed, scalar loss can be chosen
small enough to meet both the logarithmic and seed-mass constraints. -/
theorem exists_compatible_scalar_loss_bound (L : ℕ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ε < δ ∧ ε < 1 ∧ 8 * Real.log (4 * R) ≤ Real.log (1 / ε) ∧
        R * Real.sqrt ε ≤ ((1 : ℝ) / 2) ^ L := by
  let B := ((1 : ℝ) / 2) ^ L / R
  have hB : 0 < B := by unfold B; positivity
  let ε₀ := min δ (min 1 (min (Real.exp (-(8 * Real.log (4 * R)))) (B ^ 2)))
  have hε₀ : 0 < ε₀ := lt_min hδ (lt_min zero_lt_one (lt_min (Real.exp_pos _) (sq_pos_of_pos hB)))
  refine ⟨ε₀, hε₀, fun ε he he₀ => ?_⟩
  have hδ' := he₀.trans_le (min_le_left _ _)
  have h₁ := he₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlog := he₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hpow := he₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨hδ', h₁, ?_, ?_⟩
  · have hh := Real.log_le_log he hlog.le
    rw [Real.log_exp] at hh
    rw [one_div, Real.log_inv]
    linarith
  · have hh : Real.sqrt ε ≤ B := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) hB.le).mp
      rw [Real.sq_sqrt he.le]
      exact hpow.le
    calc
      _ ≤ R * B := mul_le_mul_of_nonneg_left hh hR.le
      _ = _ := by unfold B; field_simp

end

end SchauderBasisOrbits
