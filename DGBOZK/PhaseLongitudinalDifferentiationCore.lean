/-
# Actual longitudinal derivatives of the DGBOZK phase

This module removes the longitudinal part of the differentiation black box
from `Phase.lean`.

For

  omega_sigma(xi,eta) = xi (eta^2 + sigma |xi|^alpha),

it proves globally, for `alpha > 0`,

  partial_xi omega_sigma
    = eta^2 + sigma (alpha + 1) |xi|^alpha.

On the manuscript half-plane `xi > 0`, this is exactly `velX`. It also proves

  partial_xi velX = hessXX

there. Combined with `PhaseTransverseDifferentiationCore`, every displayed
first- and second-order phase derivative is now verified as a genuine
`HasDerivAt` statement.
-/

import DGBOZK.Phase
import DGBOZK.FractionalPhaseDerivativeCore
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace PhaseLongitudinalDifferentiationCore

open ResonanceTransverse

/--
Algebraic decomposition of the phase into its linear transverse-energy term
and the scalar fractional phase.
-/
theorem omega_eq_linear_add_scalarFractionalPhase
    (alpha sigma xi eta : ℝ) :
    omega alpha sigma xi eta
      =
    xi * eta ^ 2
      + sigma * scalarFractionalPhase alpha xi := by
  unfold omega scalarFractionalPhase
  ring

/--
Global longitudinal derivative of the phase.

The assumption `0 < alpha` is needed only at the origin. Away from the
origin, the corresponding real-power formula is valid more generally.
-/
theorem hasDerivAt_omega_xi_abs
    {alpha sigma xi eta : ℝ}
    (halpha : 0 < alpha) :
    HasDerivAt
      (fun xiVariable =>
        omega alpha sigma xiVariable eta)
      (eta ^ 2
        + sigma * ((alpha + 1) * |xi| ^ alpha))
      xi := by
  have hLinear :
      HasDerivAt
        (fun xiVariable : ℝ =>
          xiVariable * eta ^ 2)
        (eta ^ 2)
        xi := by
    simpa using
      (hasDerivAt_id xi).mul_const (eta ^ 2)

  have hFractional :
      HasDerivAt
        (scalarFractionalPhase alpha)
        ((alpha + 1) * |xi| ^ alpha)
        xi :=
    hasDerivAt_scalarFractionalPhase halpha

  have hScaled :
      HasDerivAt
        (fun xiVariable : ℝ =>
          sigma
            * scalarFractionalPhase alpha xiVariable)
        (sigma * ((alpha + 1) * |xi| ^ alpha))
        xi :=
    hFractional.const_mul sigma

  have hFunction :
      (fun xiVariable : ℝ =>
        omega alpha sigma xiVariable eta)
        =
      (fun xiVariable : ℝ =>
        xiVariable * eta ^ 2
          + sigma
            * scalarFractionalPhase
                alpha xiVariable) := by
    funext xiVariable
    exact
      omega_eq_linear_add_scalarFractionalPhase
        alpha sigma xiVariable eta

  rw [hFunction]
  exact hLinear.add hScaled

/--
On the positive longitudinal half-plane, the verified derivative is exactly
the displayed `velX` formula from `Phase.lean`.
-/
theorem hasDerivAt_omega_xi_of_pos
    {alpha sigma xi eta : ℝ}
    (halpha : 0 < alpha)
    (hxi : 0 < xi) :
    HasDerivAt
      (fun xiVariable =>
        omega alpha sigma xiVariable eta)
      (velX alpha sigma xi eta)
      xi := by
  have hCoefficient :
      eta ^ 2
          + sigma * ((alpha + 1) * |xi| ^ alpha)
        =
      velX alpha sigma xi eta := by
    rw [abs_of_pos hxi]
    unfold velX
    ring

  rw [← hCoefficient]
  exact hasDerivAt_omega_xi_abs halpha

/--
Derivative of the positive-base real power occurring in `velX`.
-/
theorem hasDerivAt_positive_rpow
    {alpha xi : ℝ}
    (hxi : 0 < xi) :
    HasDerivAt
      (fun xiVariable : ℝ =>
        xiVariable ^ alpha)
      (alpha * xi ^ (alpha - 1))
      xi := by
  simpa using
    (hasDerivAt_id xi).rpow_const
      (Or.inl (ne_of_gt hxi))

/--
The displayed longitudinal Hessian entry is the actual derivative of `velX`
on the manuscript half-plane `xi > 0`.
-/
theorem hasDerivAt_velX_xi_of_pos
    {alpha sigma xi eta : ℝ}
    (hxi : 0 < xi) :
    HasDerivAt
      (fun xiVariable =>
        velX alpha sigma xiVariable eta)
      (hessXX alpha sigma xi)
      xi := by
  have hPower :
      HasDerivAt
        (fun xiVariable : ℝ =>
          xiVariable ^ alpha)
        (alpha * xi ^ (alpha - 1))
        xi :=
    hasDerivAt_positive_rpow hxi

  have hScaled :
      HasDerivAt
        (fun xiVariable : ℝ =>
          (sigma * (alpha + 1))
            * xiVariable ^ alpha)
        ((sigma * (alpha + 1))
          * (alpha * xi ^ (alpha - 1)))
        xi :=
    hPower.const_mul (sigma * (alpha + 1))

  have hVelocity :
      HasDerivAt
        (fun xiVariable : ℝ =>
          (sigma * (alpha + 1))
              * xiVariable ^ alpha
            + eta ^ 2)
        ((sigma * (alpha + 1))
          * (alpha * xi ^ (alpha - 1)))
        xi :=
    hScaled.add_const (eta ^ 2)

  have hCoefficient :
      (sigma * (alpha + 1))
          * (alpha * xi ^ (alpha - 1))
        =
      hessXX alpha sigma xi := by
    unfold hessXX
    ring

  rw [← hCoefficient]
  simpa [velX] using hVelocity

/--
The first longitudinal derivative computed by Lean equals the displayed group
velocity.
-/
theorem deriv_omega_xi_of_pos
    {alpha sigma xi eta : ℝ}
    (halpha : 0 < alpha)
    (hxi : 0 < xi) :
    deriv
        (fun xiVariable =>
          omega alpha sigma xiVariable eta)
        xi
      =
    velX alpha sigma xi eta :=
  (hasDerivAt_omega_xi_of_pos halpha hxi).deriv

/--
The second longitudinal derivative computed by Lean equals the displayed
Hessian entry.
-/
theorem deriv_velX_xi_of_pos
    {alpha sigma xi eta : ℝ}
    (hxi : 0 < xi) :
    deriv
        (fun xiVariable =>
          velX alpha sigma xiVariable eta)
        xi
      =
    hessXX alpha sigma xi :=
  (hasDerivAt_velX_xi_of_pos hxi).deriv

end PhaseLongitudinalDifferentiationCore
end DGBOZK
