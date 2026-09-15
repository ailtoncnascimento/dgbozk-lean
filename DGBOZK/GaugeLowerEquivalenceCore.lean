/-
# Lower equivalence bound for the anisotropic gauge

From the defining equation

  xi^2 / rho^(2 / alpha) + eta^2 / rho = 1,

this module proves

  |xi|^alpha <= rho,
  eta^2 <= rho,

and hence

  (1 / 2) * (|xi|^alpha + eta^2) <= rho.

This is the lower inequality in `eq:gauge-equiv`. The converse inequality
`rho <= |xi|^alpha + eta^2` is not claimed in this module.
-/

import DGBOZK.GaugeEquationCore
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace GaugeLowerEquivalenceCore

open GaugeEquationCore

/--
Raising `x^2` to the real exponent `alpha / 2` gives `|x|^alpha`.
-/
theorem square_rpow_half
    (alpha x : ℝ) :
    (x ^ 2 : ℝ) ^ (alpha / 2)
      = |x| ^ alpha := by
  calc
    (x ^ 2 : ℝ) ^ (alpha / 2)
        =
      (|x| ^ (2 : ℕ) : ℝ) ^ (alpha / 2) := by
        rw [sq_abs]
    _ =
      (|x| ^ (2 : ℝ)) ^ (alpha / 2) := by
        rw [Real.rpow_two]
    _ =
      |x| ^ ((2 : ℝ) * (alpha / 2)) := by
        rw [Real.rpow_mul (abs_nonneg x)]
    _ = |x| ^ alpha := by
      congr 1
      ring

/--
The exponents `2 / alpha` and `alpha / 2` cancel for positive `alpha`.
-/
theorem gauge_rpow_exponents_cancel
    {alpha rho : ℝ}
    (halpha : 0 < alpha)
    (hrho : 0 < rho) :
    (rho ^ (2 / alpha)) ^ (alpha / 2)
      = rho := by
  have hexponent :
      (2 / alpha) * (alpha / 2) = (1 : ℝ) := by
    field_simp [ne_of_gt halpha]
  calc
    (rho ^ (2 / alpha)) ^ (alpha / 2)
        =
      rho ^ ((2 / alpha) * (alpha / 2)) := by
        rw [Real.rpow_mul (le_of_lt hrho)]
    _ = rho ^ (1 : ℝ) := by
      rw [hexponent]
    _ = rho := Real.rpow_one rho

/--
The longitudinal coordinate estimate extracted from the gauge equation.
-/
theorem abs_x_rpow_le_rho
    {alpha xi eta rho : ℝ}
    (halpha : 0 < alpha)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    |xi| ^ alpha ≤ rho := by
  have hSquare :
      xi ^ 2 ≤ rho ^ (2 / alpha) :=
    (coordinate_square_bounds hrho hEquation).1
  have hHalfNonneg :
      0 ≤ alpha / 2 := by
    positivity
  have hRaised :
      (xi ^ 2 : ℝ) ^ (alpha / 2)
        ≤
      (rho ^ (2 / alpha)) ^ (alpha / 2) :=
    Real.rpow_le_rpow
      (sq_nonneg xi)
      hSquare
      hHalfNonneg
  calc
    |xi| ^ alpha
        = (xi ^ 2 : ℝ) ^ (alpha / 2) := by
            symm
            exact square_rpow_half alpha xi
    _ ≤ (rho ^ (2 / alpha)) ^ (alpha / 2) :=
      hRaised
    _ = rho :=
      gauge_rpow_exponents_cancel halpha hrho

/--
The transverse coordinate estimate extracted from the gauge equation.
-/
theorem y_square_le_rho
    {alpha xi eta rho : ℝ}
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    eta ^ 2 ≤ rho :=
  (coordinate_square_bounds hrho hEquation).2

/--
The lower half of the gauge equivalence in the cleaned manuscript:

  (1 / 2) * (|xi|^alpha + eta^2) <= rho.
-/
theorem half_energy_le_rho
    {alpha xi eta rho : ℝ}
    (halpha : 0 < alpha)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    (1 / 2 : ℝ) * (|xi| ^ alpha + eta ^ 2)
      ≤ rho := by
  have hx :
      |xi| ^ alpha ≤ rho :=
    abs_x_rpow_le_rho halpha hrho hEquation
  have heta :
      eta ^ 2 ≤ rho :=
    y_square_le_rho hrho hEquation
  linarith

end GaugeLowerEquivalenceCore
end DGBOZK
