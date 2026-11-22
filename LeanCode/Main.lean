module

public import LeanCode.Basis.Transport
public import LeanCode.Construction.WeightedBasis
public import LeanCode.Construction.Normalization
public import LeanCode.Target.Reverse
public import LeanCode.Construction.ProductStep
public import LeanCode.Directional.Selection

@[expose] public section

open Function MeasureTheory TopologicalSpace

namespace SchauderBasisOrbits

/-- Assemble the orbit-basis equivalence from the finite extension
proposition for singleton-null probability measures. -/
theorem mainResult_of_lineExtensions
    (extend : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ],
      LineExtensionSupply μ)
    {H : Type*} [ComplexHilbertSpace H] [SeparableSpace H] (U : ℝ → UnitaryOperator H)
    (hH : ¬ FiniteDimensional ℂ H) (hU : IsStronglyContinuousGroup U) :
    HasSimpleContinuousSpectrum U ↔
      ∃ (g : H) (t : ℕ → ℝ), Injective t ∧ ∃ b : SchauderBasis ℂ H, ∀ n, b n = U (t n) g := by
  constructor
  · rintro ⟨⟨v, hv⟩, heigen⟩
    obtain ⟨z, hz, hzn⟩ := cyclic_unit_vector hH hv
    obtain ⟨R⟩ := exists_cyclicSpectralRealization hU hz hzn
    let μ := R.μ.toMeasure
    let : NullSingletonClass μ := R.nullSingletonClass heigen
    obtain ⟨w, t, ht, b, hb⟩ :=
      weighted_exponential_basis_of_lineExtension (μ := μ) (by norm_num : (0 : ℝ) < 1)
        (extend μ) (IsProbabilityMeasure.ne_zero μ)
    let : IsFiniteMeasure (weightedMeasure R.μ.toMeasure w.toFun) := inferInstanceAs (IsFiniteMeasure (w.measure μ))
    exact R.orbit_basis_of_weighted w.measurable_toFun (Filter.Eventually.of_forall w.positive) ht hb
  · rintro ⟨g, t, _, b, hb⟩
    exact orbit_basis_implies_simple_spectrum hU hb

/-- Assemble the exact target once the finite product extension has been proved. -/
theorem mainResult_of_productExtensions
    (extend : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ] [NullSingletonClass ρ],
      NormalizedProductExtensionSupply ρ)
    {H : Type*} [ComplexHilbertSpace H] [SeparableSpace H] (U : ℝ → UnitaryOperator H)
    (hH : ¬ FiniteDimensional ℂ H) (hU : IsStronglyContinuousGroup U) :
    HasSimpleContinuousSpectrum U ↔
      ∃ (g : H) (t : ℕ → ℝ), Injective t ∧ ∃ b : SchauderBasis ℂ H, ∀ n, b n = U (t n) g :=
  mainResult_of_lineExtensions
    (fun _ => lineExtensionSupply_of_product (productExtensionSupply_of_normalized extend))
    U hH hU

/-- The full orbit-basis equivalence. -/
theorem mainResult {H : Type*} [ComplexHilbertSpace H] [SeparableSpace H]
    (U : ℝ → UnitaryOperator H) (hH : ¬ FiniteDimensional ℂ H)
    (hU : IsStronglyContinuousGroup U) :
    HasSimpleContinuousSpectrum U ↔
      ∃ (g : H) (t : ℕ → ℝ), Injective t ∧ ∃ b : SchauderBasis ℂ H, ∀ n, b n = U (t n) g := by
  apply mainResult_of_productExtensions _ U hH hU
  intro ρ _ _
  exact normalizedProductExtension_of_supplies
    (fun _ hδ hδ₁ _ hz hcap _ hη => Scalar.exists_goodScalar hδ hδ₁ hz hcap hη)
    (fun _ _ m _ => directional_supply m)

end SchauderBasisOrbits
