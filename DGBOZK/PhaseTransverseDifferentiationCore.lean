/-
# Actual transverse derivatives of the DGBOZK phase

This module verifies the transverse derivative formulas from `Phase.lean`
as genuine `HasDerivAt` statements.
-/

import DGBOZK.Phase
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false

namespace DGBOZK
namespace PhaseTransverseDifferentiationCore

/-- The derivative of the square function. -/
theorem hasDerivAt_square
    (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => z ^ 2)
      (2 * x)
      x := by
  simpa [id, mul_comm] using
    (hasDerivAt_id x).pow 2

/--
Actual transverse derivative of the phase:

  partial_eta omega_sigma(xi,eta) = velY(xi,eta).
-/
theorem hasDerivAt_omega_eta
    (alpha sigma xi eta : ℝ) :
    HasDerivAt
      (fun etaVariable =>
        omega alpha sigma xi etaVariable)
      (velY xi eta)
      eta := by
  have hInside :
      HasDerivAt
        (fun etaVariable : ℝ =>
          etaVariable ^ 2
            + sigma * |xi| ^ alpha)
        (2 * eta)
        eta := by
    simpa [id, mul_comm] using
      ((hasDerivAt_id eta).pow 2).add_const
        (sigma * |xi| ^ alpha)

  have hResult :=
    HasDerivAt.const_mul xi hInside

  simpa [
    omega,
    velY,
    mul_comm,
    mul_left_comm,
    mul_assoc
  ] using hResult

/--
The transverse derivative of the longitudinal velocity is the mixed Hessian
entry:

  partial_eta velX = hessXY.
-/
theorem hasDerivAt_velX_eta
    (alpha sigma xi eta : ℝ) :
    HasDerivAt
      (fun etaVariable =>
        velX alpha sigma xi etaVariable)
      (hessXY eta)
      eta := by
  have hResult :=
    ((hasDerivAt_id eta).pow 2).const_add
      (sigma * (alpha + 1) * xi ^ alpha)

  simpa [
    velX,
    hessXY,
    id,
    mul_comm,
    mul_left_comm,
    mul_assoc
  ] using hResult

/--
The transverse derivative of the transverse velocity is the transverse
Hessian entry:

  partial_eta velY = hessYY.
-/
theorem hasDerivAt_velY_eta
    (xi eta : ℝ) :
    HasDerivAt
      (fun etaVariable =>
        velY xi etaVariable)
      (hessYY xi)
      eta := by
  have hResult :=
    HasDerivAt.const_mul
      (2 * xi)
      (hasDerivAt_id eta)

  simpa [
    velY,
    hessYY,
    id,
    mul_comm,
    mul_left_comm,
    mul_assoc
  ] using hResult

/--
The longitudinal derivative of the transverse velocity is the same mixed
Hessian entry:

  partial_xi velY = hessXY.
-/
theorem hasDerivAt_velY_xi
    (xi eta : ℝ) :
    HasDerivAt
      (fun xiVariable =>
        velY xiVariable eta)
      (hessXY eta)
      xi := by
  have hResult :=
    HasDerivAt.const_mul
      (2 * eta)
      (hasDerivAt_id xi)

  simpa [
    velY,
    hessXY,
    id,
    mul_comm,
    mul_left_comm,
    mul_assoc
  ] using hResult

/-- Equality of the two verified mixed derivative values. -/
theorem verified_mixed_derivatives_agree
    (alpha sigma xi eta : ℝ) :
    deriv
        (fun etaVariable =>
          velX alpha sigma xi etaVariable)
        eta
      =
    deriv
        (fun xiVariable =>
          velY xiVariable eta)
        xi := by
  rw [
    (hasDerivAt_velX_eta
      alpha sigma xi eta).deriv,
    (hasDerivAt_velY_xi
      xi eta).deriv
  ]

end PhaseTransverseDifferentiationCore
end DGBOZK
