/-
# Scalar core of the smooth anisotropic gauge

This module formalizes elementary consequences of the defining equation

  xi^2 / rho^(2 / alpha) + eta^2 / rho = 1.

It proves bounds for the normalized summands, the corresponding coordinate
bounds, and evenness of the equation in each coordinate.

It does not prove existence, uniqueness, smoothness, homogeneity, implicit
differentiation, or uniform symbol estimates for the gauge.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DGBOZK
namespace GaugeEquationCore

/-- The scalar defining equation for the anisotropic gauge. -/
def gaugeEquation
    (alpha xi eta rho : ℝ) : Prop :=
  xi ^ 2 / rho ^ (2 / alpha) + eta ^ 2 / rho = 1

/--
Both normalized terms in the gauge equation belong to the interval `[0,1]`.
-/
theorem normalized_terms_mem_unit_interval
    {alpha xi eta rho : ℝ}
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    (0 ≤ xi ^ 2 / rho ^ (2 / alpha)
        ∧ xi ^ 2 / rho ^ (2 / alpha) ≤ 1)
      ∧
    (0 ≤ eta ^ 2 / rho
        ∧ eta ^ 2 / rho ≤ 1) := by
  have hRpowPos : 0 < rho ^ (2 / alpha) :=
    Real.rpow_pos_of_pos hrho _
  have hxNonneg :
      0 ≤ xi ^ 2 / rho ^ (2 / alpha) :=
    div_nonneg (sq_nonneg xi) (le_of_lt hRpowPos)
  have hetaNonneg :
      0 ≤ eta ^ 2 / rho :=
    div_nonneg (sq_nonneg eta) (le_of_lt hrho)
  have hsum :
      xi ^ 2 / rho ^ (2 / alpha) + eta ^ 2 / rho = 1 := by
    exact hEquation
  constructor
  · exact ⟨hxNonneg, by linarith⟩
  · exact ⟨hetaNonneg, by linarith⟩

/--
The defining equation implies the squared-coordinate bounds

  xi^2 <= rho^(2 / alpha),  eta^2 <= rho.
-/
theorem coordinate_square_bounds
    {alpha xi eta rho : ℝ}
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    xi ^ 2 ≤ rho ^ (2 / alpha)
      ∧ eta ^ 2 ≤ rho := by
  obtain ⟨⟨_, hxUpper⟩, ⟨_, hetaUpper⟩⟩ :=
    normalized_terms_mem_unit_interval hrho hEquation

  have hRpowPos : 0 < rho ^ (2 / alpha) :=
    Real.rpow_pos_of_pos hrho _

  constructor
  · calc
      xi ^ 2
          =
        (xi ^ 2 / rho ^ (2 / alpha))
          * rho ^ (2 / alpha) := by
            field_simp [ne_of_gt hRpowPos]
      _ ≤ 1 * rho ^ (2 / alpha) :=
        mul_le_mul_of_nonneg_right hxUpper (le_of_lt hRpowPos)
      _ = rho ^ (2 / alpha) := one_mul _
  · calc
      eta ^ 2
          =
        (eta ^ 2 / rho) * rho := by
          field_simp [ne_of_gt hrho]
      _ ≤ 1 * rho :=
        mul_le_mul_of_nonneg_right hetaUpper (le_of_lt hrho)
      _ = rho := one_mul _

/-- The gauge equation is even in the longitudinal coordinate. -/
theorem gaugeEquation_neg_x_iff
    (alpha xi eta rho : ℝ) :
    gaugeEquation alpha (-xi) eta rho
      ↔ gaugeEquation alpha xi eta rho := by
  simp [gaugeEquation]

/-- The gauge equation is even in the transverse coordinate. -/
theorem gaugeEquation_neg_y_iff
    (alpha xi eta rho : ℝ) :
    gaugeEquation alpha xi (-eta) rho
      ↔ gaugeEquation alpha xi eta rho := by
  simp [gaugeEquation]

/-- The gauge equation is simultaneously even in both coordinates. -/
theorem gaugeEquation_neg_both_iff
    (alpha xi eta rho : ℝ) :
    gaugeEquation alpha (-xi) (-eta) rho
      ↔ gaugeEquation alpha xi eta rho := by
  simp [gaugeEquation]

end GaugeEquationCore
end DGBOZK
