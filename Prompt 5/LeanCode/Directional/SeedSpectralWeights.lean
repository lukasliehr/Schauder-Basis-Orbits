import LeanCode.Directional.SeedParameters
import Mathlib

open scoped BigOperators

namespace SchauderBasisOrbits

noncomputable section

/-- A vector in the seed's two-dimensional plane can have nonzero coordinates
only at the two eigenvalues of that plane. The second plane vector is the
unnormalized sum of the phase rows. -/
theorem seed_plane_support {κ m L : ℝ} (hκ : 0 < κ) (hm : 0 < m) (hL : 1 ≤ L)
    {β : ℝ} {v z : ℂ}
    (hv : (β : ℂ) * v = (m : ℂ) * (v + (κ : ℂ) * z))
    (hz : (β : ℂ) * z = (m : ℂ) * (((L * κ : ℝ) : ℂ) * v +
      ((1 - κ ^ 2 + L * κ ^ 2 : ℝ) : ℂ) * z)) :
    v = 0 ∨ β = m * seedSmallEigenvalue (κ ^ 2) L ∨ β = m * seedLargeEigenvalue (κ ^ 2) L := by
  by_cases hzero : v = 0
  · exact Or.inl hzero
  right
  let t := β / m
  let a := 1 - κ ^ 2 + L * κ ^ 2
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  have hmt : (m : ℂ) * (t : ℂ) = (β : ℂ) := by
    dsimp [t]
    push_cast
    field_simp
  have h₁ : ((t : ℂ) - 1) * v = (κ : ℂ) * z := by
    apply mul_left_cancel₀ hmC
    calc
      _ = ((m : ℂ) * (t : ℂ)) * v - (m : ℂ) * v := by ring
      _ = _ := by rw [hmt, hv]; ring
  have h₂ : ((t : ℂ) - (a : ℂ)) * z = ((L * κ : ℝ) : ℂ) * v := by
    apply mul_left_cancel₀ hmC
    calc
      _ = ((m : ℂ) * (t : ℂ)) * z - (m : ℂ) * (a : ℂ) * z := by ring
      _ = _ := by rw [hmt, hz]; dsimp [a]; ring
  have hc : (((t ^ 2 - seedTrace (κ ^ 2) L * t + (1 - κ ^ 2) : ℝ) : ℂ)) * v = 0 := by
    calc
      _ = ((t : ℂ) - (a : ℂ)) * (((t : ℂ) - 1) * v - (κ : ℂ) * z) +
          (κ : ℂ) * (((t : ℂ) - (a : ℂ)) * z - ((L * κ : ℝ) : ℂ) * v) := by
        dsimp [a, seedTrace]
        push_cast
        ring
      _ = _ := by rw [h₁, h₂]; ring
  have hroot : t ^ 2 - seedTrace (κ ^ 2) L * t + (1 - κ ^ 2) = 0 :=
    Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hzero)
  have hf : (t - seedSmallEigenvalue (κ ^ 2) L) * (t - seedLargeEigenvalue (κ ^ 2) L) = 0 := by
    nlinarith [seed_eigenvalues_sum (κ ^ 2) L, seed_eigenvalues_prod (sq_pos_of_pos hκ) hL,
      congrArg (fun x : ℝ => x * t) (seed_eigenvalues_sum (κ ^ 2) L)]
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl ((div_eq_iff hm.ne').mp (sub_eq_zero.mp h) |>.trans (mul_comm _ _))
  · exact Or.inr ((div_eq_iff hm.ne').mp (sub_eq_zero.mp h) |>.trans (mul_comm _ _))

/-- Determine the response on the seed direction from its unit mass, its
first spectral moment, and support on the two plane eigenvalues. -/
theorem seed_direction_response {ι : Type*} [Fintype ι] {θ L m : ℝ}
    (hθ : 0 < θ) (hθ' : θ < 1) (hL : 1 ≤ L) (hm : 0 < m)
    (β : ι → ℝ) (v : ι → ℂ)
    (hSupport : ∀ i, v i = 0 ∨ β i = m * seedSmallEigenvalue θ L ∨ β i = m * seedLargeEigenvalue θ L)
    (hMass : ∑ i, ‖v i‖ ^ 2 = 1) (hMoment : ∑ i, β i * ‖v i‖ ^ 2 = m)
    (Φ : ℝ → ℝ) :
    ∑ i, Φ (β i) * ‖v i‖ ^ 2 =
      seedDirectionFraction θ L * Φ (m * seedSmallEigenvalue θ L) +
        (1 - seedDirectionFraction θ L) * Φ (m * seedLargeEigenvalue θ L) := by
  classical
  let γ := seedSmallEigenvalue θ L
  let Γ := seedLargeEigenvalue θ L
  let p := ∑ i, if β i = m * γ then ‖v i‖ ^ 2 else 0
  let q := ∑ i, if β i = m * γ then 0 else ‖v i‖ ^ 2
  have hpq : p + q = 1 := by
    dsimp [p, q]
    rw [← Finset.sum_add_distrib, ← hMass]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp
  have hsplit (f : ℝ → ℝ) :
      (∑ i, f (β i) * ‖v i‖ ^ 2) = f (m * γ) * p + f (m * Γ) * q := by
    dsimp [p, q]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases hSupport i with hi | hi | hi
    · simp [hi]
    · simp [hi, γ]
    · by_cases hh : β i = m * γ
      · simp [hh]
      · rw [ite_eq_right hh, ite_eq_right hh, hi, mul_zero, zero_add]
  have hmom := hsplit id
  change (∑ i, β i * ‖v i‖ ^ 2) = (m * γ) * p + (m * Γ) * q at hmom
  rw [hMoment] at hmom
  have hcancel : 1 = γ * p + Γ * q := by
    have ht : m * 1 = m * (γ * p + Γ * q) := by linarith only [hmom, show
      m * (γ * p + Γ * q) = m * γ * p + m * Γ * q by ring]
    exact mul_left_cancel₀ hm.ne' ht
  have hgap : Γ - γ ≠ 0 := by
    have h := seed_eigenvalues_order hθ hθ' hL
    dsimp [Γ, γ]
    linarith [h.2.1, h.2.2]
  have hp : p = seedDirectionFraction θ L := by
    change p = (Γ - 1) / (Γ - γ)
    apply (eq_div_iff hgap).mpr
    have hq : q = 1 - p := by linarith
    rw [hq] at hcancel
    nlinarith
  have hq : q = 1 - seedDirectionFraction θ L := by linarith
  rw [hsplit Φ, hp, hq]
  ring

theorem seed_perp_response {ι : Type*} [Fintype ι] (β : ι → ℝ) (v : ι → ℂ)
    {m : ℝ} (h : ∀ i, v i = 0 ∨ β i = m) (Φ : ℝ → ℝ) :
    ∑ i, Φ (β i) * ‖v i‖ ^ 2 = Φ m * ∑ i, ‖v i‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases h i with hzero | heq
  · simp [hzero]
  · rw [heq]

end

end SchauderBasisOrbits
