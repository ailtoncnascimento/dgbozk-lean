/-
# Algebraic assembly of the fractional phase-increment estimate

For

  F_alpha(x) = x |x|^alpha,

the longitudinal resonance component is

  L_alpha(a,xi)
    = F_alpha(xi+a) - F_alpha(xi) - F_alpha(a).

This module proves the final universal bound from two explicit inputs:

* a secant estimate for `F_alpha`;
* a power-sum estimate for nonnegative real powers.

The calculus proof of the secant estimate and the convexity proof of the
power-sum estimate are deliberately separated into later modules.
-/

import DGBOZK.ResonanceTransverseCore
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/-- The scalar fractional phase `x |x|^alpha`. -/
noncomputable def scalarFractionalPhase
    (alpha x : ℝ) : ℝ :=
  x * |x| ^ alpha

/-- The encoded longitudinal component is the second phase increment. -/
theorem longitudinalPart_eq_phase_increment
    (alpha a xi : ℝ) :
    longitudinalPart alpha a xi =
      scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi
        - scalarFractionalPhase alpha a := by
  unfold longitudinalPart scalarFractionalPhase
  ring

/-- Exact absolute value of the scalar fractional phase. -/
theorem abs_scalarFractionalPhase
    (alpha x : ℝ) :
    |scalarFractionalPhase alpha x|
      = |x| * |x| ^ alpha := by
  unfold scalarFractionalPhase
  rw [abs_mul]
  rw [abs_of_nonneg
    (Real.rpow_nonneg (abs_nonneg x) alpha)]

/--
Algebraic assembly of the universal longitudinal increment estimate.

The hypothesis `hsecant` is the mean-value estimate

  |F(xi+a)-F(xi)|
    <= (alpha+1)|a|(|xi|+|a|)^alpha,

while `hpowerSum` is

  (|xi|+|a|)^alpha
    <= K (|xi|^alpha+|a|^alpha).
-/
theorem longitudinal_increment_of_secant_and_power_sum
    {alpha a xi K : ℝ}
    (halphaPlus : 0 ≤ alpha + 1)
    (hsecant :
      |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi|
        ≤
      (alpha + 1) * |a|
        * (|xi| + |a|) ^ alpha)
    (hpowerSum :
      (|xi| + |a|) ^ alpha
        ≤
      K * (|xi| ^ alpha + |a| ^ alpha)) :
    |longitudinalPart alpha a xi|
      ≤
    ((alpha + 1) * K + 1)
      * |a| * (|xi| ^ alpha + |a| ^ alpha) := by
  have hcoefficient :
      0 ≤ (alpha + 1) * |a| := by
    exact mul_nonneg halphaPlus (abs_nonneg a)

  have hsecantScaled :
      |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi|
        ≤
      ((alpha + 1) * K)
        * |a| * (|xi| ^ alpha + |a| ^ alpha) := by
    calc
      |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi|
          ≤
        (alpha + 1) * |a|
          * (|xi| + |a|) ^ alpha :=
        hsecant
      _ ≤
        (alpha + 1) * |a|
          * (K * (|xi| ^ alpha + |a| ^ alpha)) := by
        exact mul_le_mul_of_nonneg_left
          hpowerSum
          hcoefficient
      _ =
        ((alpha + 1) * K)
          * |a| * (|xi| ^ alpha + |a| ^ alpha) := by
        ring

  have hxiPowNonneg :
      0 ≤ |xi| ^ alpha := by
    exact Real.rpow_nonneg (abs_nonneg xi) alpha

  have haPowLe :
      |a| ^ alpha
        ≤ |xi| ^ alpha + |a| ^ alpha := by
    exact le_add_of_nonneg_left hxiPowNonneg

  have hphaseA :
      |scalarFractionalPhase alpha a|
        ≤
      |a| * (|xi| ^ alpha + |a| ^ alpha) := by
    rw [abs_scalarFractionalPhase]
    exact mul_le_mul_of_nonneg_left
      haPowLe
      (abs_nonneg a)

  have htriangle :
      |longitudinalPart alpha a xi|
        ≤
      |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi|
        + |scalarFractionalPhase alpha a| := by
    rw [longitudinalPart_eq_phase_increment]
    calc
      |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi
        - scalarFractionalPhase alpha a|
          =
        |(scalarFractionalPhase alpha (xi + a)
          - scalarFractionalPhase alpha xi)
          + (-scalarFractionalPhase alpha a)| := by
            congr 1
      _ ≤
        |scalarFractionalPhase alpha (xi + a)
          - scalarFractionalPhase alpha xi|
          + |-scalarFractionalPhase alpha a| :=
        abs_add
          (scalarFractionalPhase alpha (xi + a)
            - scalarFractionalPhase alpha xi)
          (-scalarFractionalPhase alpha a)
      _ =
        |scalarFractionalPhase alpha (xi + a)
          - scalarFractionalPhase alpha xi|
          + |scalarFractionalPhase alpha a| := by
        rw [abs_neg]

  calc
    |longitudinalPart alpha a xi|
        ≤
      |scalarFractionalPhase alpha (xi + a)
        - scalarFractionalPhase alpha xi|
        + |scalarFractionalPhase alpha a| :=
      htriangle
    _ ≤
      ((alpha + 1) * K)
          * |a| * (|xi| ^ alpha + |a| ^ alpha)
        + |a| * (|xi| ^ alpha + |a| ^ alpha) :=
      add_le_add hsecantScaled hphaseA
    _ =
      ((alpha + 1) * K + 1)
        * |a| * (|xi| ^ alpha + |a| ^ alpha) := by
      ring

end ResonanceTransverse
end DGBOZK
