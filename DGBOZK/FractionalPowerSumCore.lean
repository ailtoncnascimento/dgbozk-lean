/-
# Fractional power-sum bound

This module proves the homogeneous inequality

  (|x| + |a|)^alpha
    <= 2 * (|x|^alpha + |a|^alpha)

for 1 <= alpha <= 2.

It then substitutes this estimate into the conditional fractional
phase-increment theorem. After this step, only the secant estimate for
x |x|^alpha remains as an analytic input.
-/

import DGBOZK.FractionalPhaseIncrementCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
For `1 <= alpha <= 2`, the fractional power of a two-term sum is
bounded by twice the sum of the fractional powers.

The generalized mean inequality first gives the sharper coefficient
`2^(alpha - 1)`. The upper restriction `alpha <= 2` then bounds this
coefficient by `2`.
-/
theorem fractional_power_sum
    {alpha x a : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2) :
    (|x| + |a|) ^ alpha
      ≤ 2 * (|x| ^ alpha + |a| ^ alpha) := by
  let xnn : NNReal := ⟨|x|, abs_nonneg x⟩
  let ann : NNReal := ⟨|a|, abs_nonneg a⟩

  have hmeanNN :
      (xnn + ann) ^ alpha
        ≤ (2 : NNReal) ^ (alpha - 1)
            * (xnn ^ alpha + ann ^ alpha) :=
    NNReal.rpow_add_le_mul_rpow_add_rpow
      xnn ann halphaOne

  have hmean :
      (|x| + |a|) ^ alpha
        ≤ (2 : ℝ) ^ (alpha - 1)
            * (|x| ^ alpha + |a| ^ alpha) := by
    exact_mod_cast hmeanNN

  have hexponent : alpha - 1 ≤ 1 := by
    linarith

  have hcoefficient :
      (2 : ℝ) ^ (alpha - 1) ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2)
        hexponent

  have hsumNonneg :
      0 ≤ |x| ^ alpha + |a| ^ alpha := by
    exact add_nonneg
      (Real.rpow_nonneg (abs_nonneg x) alpha)
      (Real.rpow_nonneg (abs_nonneg a) alpha)

  exact hmean.trans
    (mul_le_mul_of_nonneg_right hcoefficient hsumNonneg)

/--
The universal longitudinal phase-increment estimate, reduced to the
single secant estimate for the scalar phase.

The power-sum hypothesis appearing in
`longitudinal_increment_of_secant_and_power_sum` is now discharged
with the explicit constant `K = 2`.
-/
theorem longitudinal_increment_of_secant
    {alpha a xi : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hsecant :
      |scalarFractionalPhase alpha (xi + a)
          - scalarFractionalPhase alpha xi|
        ≤ (alpha + 1) * |a|
            * (|xi| + |a|) ^ alpha) :
    |longitudinalPart alpha a xi|
      ≤ ((alpha + 1) * 2 + 1)
          * |a| * (|xi| ^ alpha + |a| ^ alpha) := by
  have halphaPlus : 0 ≤ alpha + 1 := by
    linarith

  exact longitudinal_increment_of_secant_and_power_sum
    (K := 2)
    halphaPlus
    hsecant
    (fractional_power_sum halphaOne halphaTwo)

end ResonanceTransverse
end DGBOZK
