import LeanCode.Scalar.Data
import LeanCode.Scalar.Budgets

open Matrix
open scoped MatrixOrder

namespace SchauderBasisOrbits.Scalar

/-- A polynomial scalar packet with its prescribed gain and the quantitative certificates
used in the residual and directional constructions. -/
structure GoodScalar (δ z : ℝ) where
  dim : ℕ
  length : ℕ
  data : PolynomialData dim length
  gain_eq : data.toData.gain = z
  loss_pos : 0 < data.toData.loss
  gram_floor : data.toData.loss ^ 2 • 1 ≤ data.toData.gram
  inverse_diagonal :
    ∀ j : Fin length, data.toData.gram⁻¹ j.succ j.succ ≤ 1 + 2 * data.toData.loss
  augmented_pb : PB data.toData.gram (commonBound δ)
  centered_hPrefix : HPrefix (𝕜 := ℂ) data.toData.centerLp (commonBound δ)

end SchauderBasisOrbits.Scalar
