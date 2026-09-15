/-
# Derivative of the scalar fractional phase

For alpha > 0, this module proves

  d/dx [x |x|^alpha] = (alpha + 1) |x|^alpha.

The proof treats x = 0 separately. At zero, differentiability follows
directly from the difference quotient |x|^alpha -> 0. Away from zero,
the ordinary product and real-power derivative rules apply.
-/

import DGBOZK.FractionalPowerSumCore
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Filter
open scoped Topology

namespace DGBOZK
namespace ResonanceTransverse

/--
The scalar fractional phase has derivative zero at the origin whenever
the exponent is positive.
-/
theorem hasDerivAt_scalarFractionalPhase_zero
    {alpha : ℝ}
    (halpha : 0 < alpha) :
    HasDerivAt (scalarFractionalPhase alpha) 0 0 := by
  rw [hasDerivAt_iff_tendsto]

  have hcontinuous :
      Continuous (fun y : ℝ => |y| ^ alpha) := by
    exact
      (Real.continuous_rpow_const halpha.le).comp
        continuous_abs

  have htend :
      Tendsto (fun y : ℝ => |y| ^ alpha)
        (nhds 0) (nhds 0) := by
    have hAt :
        ContinuousAt (fun y : ℝ => |y| ^ alpha) 0 :=
      hcontinuous.continuousAt
    change
      Tendsto (fun y : ℝ => |y| ^ alpha)
        (nhds 0) (nhds (|(0 : ℝ)| ^ alpha))
      at hAt
    simpa [Real.zero_rpow halpha.ne'] using hAt

  have heq :
      (fun y : ℝ =>
          ‖y - 0‖⁻¹
            * ‖scalarFractionalPhase alpha y
                - scalarFractionalPhase alpha 0
                - (y - 0) • (0 : ℝ)‖)
        =
      (fun y : ℝ => |y| ^ alpha) := by
    funext y
    by_cases hy : y = 0
    · subst y
      simp [scalarFractionalPhase,
        Real.zero_rpow halpha.ne']
    · have habs : |y| ≠ 0 := abs_ne_zero.mpr hy
      simp [scalarFractionalPhase, Real.norm_eq_abs, habs,
        abs_of_nonneg
          (Real.rpow_nonneg (abs_nonneg y) alpha)]

  rw [heq]
  exact htend

/--
Global derivative formula for the scalar fractional phase.
-/
theorem hasDerivAt_scalarFractionalPhase
    {alpha x : ℝ}
    (halpha : 0 < alpha) :
    HasDerivAt
      (scalarFractionalPhase alpha)
      ((alpha + 1) * |x| ^ alpha)
      x := by
  by_cases hx : x = 0
  · subst x
    simpa [Real.zero_rpow halpha.ne'] using
      hasDerivAt_scalarFractionalPhase_zero halpha
  · have habsPower :
        HasDerivAt
          (fun y : ℝ => |y| ^ alpha)
          ((SignType.sign x : ℝ)
            * alpha * |x| ^ (alpha - 1))
          x := by
      exact
        (hasDerivAt_abs hx).rpow_const
          (Or.inl (abs_ne_zero.mpr hx))

    have hproduct :
        HasDerivAt
          (fun y : ℝ => y * |y| ^ alpha)
          (1 * |x| ^ alpha
            + x * ((SignType.sign x : ℝ)
                * alpha * |x| ^ (alpha - 1)))
          x :=
      (hasDerivAt_id x).mul habsPower

    have hrpow :
        |x| ^ (alpha - 1) * |x|
          = |x| ^ alpha := by
      rw [← Real.rpow_add_one
        (abs_ne_zero.mpr hx) (alpha - 1)]
      congr 1
      ring

    have hderivative :
        1 * |x| ^ alpha
              + x * ((SignType.sign x : ℝ)
                  * alpha * |x| ^ (alpha - 1))
          =
        (alpha + 1) * |x| ^ alpha := by
      calc
        1 * |x| ^ alpha
              + x * ((SignType.sign x : ℝ)
                  * alpha * |x| ^ (alpha - 1))
            =
          |x| ^ alpha
            + alpha * (|x| ^ (alpha - 1)
                * (x * (SignType.sign x : ℝ))) := by
                  ring
        _ =
          |x| ^ alpha
            + alpha * (|x| ^ (alpha - 1) * |x|) := by
                  rw [self_mul_sign]
        _ =
          |x| ^ alpha + alpha * |x| ^ alpha := by
                  rw [hrpow]
        _ = (alpha + 1) * |x| ^ alpha := by
                  ring

    change
      HasDerivAt
        (fun y : ℝ => y * |y| ^ alpha)
        ((alpha + 1) * |x| ^ alpha)
        x

    rw [← hderivative]
    exact hproduct

/--
Consequently, the scalar fractional phase is differentiable everywhere
for every positive exponent.
-/
theorem differentiable_scalarFractionalPhase
    {alpha : ℝ}
    (halpha : 0 < alpha) :
    Differentiable ℝ (scalarFractionalPhase alpha) :=
  fun x =>
    (hasDerivAt_scalarFractionalPhase
      (x := x) halpha).differentiableAt

end ResonanceTransverse
end DGBOZK
