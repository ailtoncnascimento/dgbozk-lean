/-
# Global secant estimate for the scalar fractional phase

This module proves

  |f_alpha(xi + a) - f_alpha(xi)|
    <= (alpha + 1) |a| (|xi| + |a|)^alpha,

where f_alpha(x) = x |x|^alpha and alpha >= 1.

Combined with the fractional power-sum theorem, this proves the
universal longitudinal phase-increment estimate without conditional
analytic hypotheses.
-/

import DGBOZK.FractionalPhaseDerivativeCore
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

open Set

/--
Global secant estimate for `x |x|^alpha`.

Both endpoints lie in the interval
`[-(|xi|+|a|), |xi|+|a|]`. On this interval the derivative has
absolute value at most
`(alpha+1)(|xi|+|a|)^alpha`.
-/
theorem scalarFractionalPhase_secant
    {alpha xi a : ℝ}
    (halphaOne : 1 ≤ alpha) :
    |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi|
      ≤ (alpha + 1) * |a|
          * (|xi| + |a|) ^ alpha := by
  let R : ℝ := |xi| + |a|

  have halphaPos : 0 < alpha :=
    lt_of_lt_of_le zero_lt_one halphaOne

  have halphaNonneg : 0 ≤ alpha :=
    halphaPos.le

  have hcoefficient : 0 ≤ alpha + 1 := by
    linarith

  have hxiAbs : |xi| ≤ R := by
    dsimp [R]
    exact le_add_of_nonneg_right (abs_nonneg a)

  have hxiaAbs : |xi + a| ≤ R := by
    dsimp [R]
    exact abs_add xi a

  have hxi :
      xi ∈ Set.Icc (-R) R :=
    abs_le.mp hxiAbs

  have hxia :
      xi + a ∈ Set.Icc (-R) R :=
    abs_le.mp hxiaAbs

  have hderivative :
      ∀ z ∈ Set.Icc (-R) R,
        HasDerivWithinAt
          (scalarFractionalPhase alpha)
          ((alpha + 1) * |z| ^ alpha)
          (Set.Icc (-R) R)
          z := by
    intro z hz
    exact
      (hasDerivAt_scalarFractionalPhase
        (x := z) halphaPos).hasDerivWithinAt

  have hbound :
      ∀ z ∈ Set.Icc (-R) R,
        ‖(alpha + 1) * |z| ^ alpha‖
          ≤ (alpha + 1) * R ^ alpha := by
    intro z hz

    have hzAbs : |z| ≤ R := by
      exact abs_le.mpr hz

    have hpower :
        |z| ^ alpha ≤ R ^ alpha :=
      Real.rpow_le_rpow
        (abs_nonneg z)
        hzAbs
        halphaNonneg

    have hscaled :
        (alpha + 1) * |z| ^ alpha
          ≤ (alpha + 1) * R ^ alpha :=
      mul_le_mul_of_nonneg_left hpower hcoefficient

    calc
      ‖(alpha + 1) * |z| ^ alpha‖
          =
        (alpha + 1) * |z| ^ alpha := by
          rw [Real.norm_eq_abs, abs_mul]
          rw [abs_of_nonneg hcoefficient]
          rw [abs_of_nonneg
            (Real.rpow_nonneg (abs_nonneg z) alpha)]
      _ ≤ (alpha + 1) * R ^ alpha := hscaled

  have hmeanValue :
      ‖scalarFractionalPhase alpha (xi + a)
          - scalarFractionalPhase alpha xi‖
        ≤ ((alpha + 1) * R ^ alpha)
            * ‖(xi + a) - xi‖ :=
    (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderivative
      hbound
      hxi
      hxia

  calc
    |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi|
        =
      ‖scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi‖ := by
          symm
          exact Real.norm_eq_abs _
    _ ≤ ((alpha + 1) * R ^ alpha)
          * ‖(xi + a) - xi‖ :=
      hmeanValue
    _ =
      (alpha + 1) * |a|
        * (|xi| + |a|) ^ alpha := by
          dsimp [R]
          rw [show (xi + a) - xi = a by ring]
          ring

/--
The universal fractional longitudinal increment estimate.

Unlike the earlier conditional assembly theorem, this statement has
neither a secant hypothesis nor a power-sum hypothesis.
-/
theorem longitudinal_increment_universal
    {alpha a xi : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2) :
    |longitudinalPart alpha a xi|
      ≤ ((alpha + 1) * 2 + 1)
          * |a| * (|xi| ^ alpha + |a| ^ alpha) := by
  exact longitudinal_increment_of_secant
    halphaOne
    halphaTwo
    (scalarFractionalPhase_secant halphaOne)

end ResonanceTransverse
end DGBOZK
