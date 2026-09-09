import Mathlib.Data.Real.Basic
/-
# Scalar closure for the frequency-resolved nonlinear energy estimate

The analytic frequency-envelope inequality is an input supplied by the paper.
This file verifies only the absorption step once that inequality is available.
-/
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DGBOZK

/-- If the weighted nonlinear coefficient is at most one half, a quadratic
frequency-envelope inequality absorbs to the stated factor-two bound. -/
theorem quadratic_envelope_closure {C₀ Θ Cβ Z : ℝ}
    (hZ : 0 ≤ Z) (hsmall : Θ * Cβ ≤ 1 / 2)
    (hsystem : Z ≤ C₀ + Θ * Cβ * Z) : Z ≤ 2 * C₀ := by
  have hnonlinear : Θ * Cβ * Z ≤ (1 / 2) * Z :=
    mul_le_mul_of_nonneg_right hsmall hZ
  linarith

/-- Positivity of the decay margin used when a frequency envelope has
off-diagonal exponent gamma and the nonlinear convolution costs 2 delta. -/
theorem envelope_decay_margin {γ δ : ℝ} (h : 2 * δ < γ) :
    0 < γ - 2 * δ := by
  linarith

end DGBOZK
