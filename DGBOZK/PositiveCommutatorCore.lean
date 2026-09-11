/-
# Algebraic core of the localized positive commutator

This module audits the exact sign-sensitive algebra used in
`lem:positive-comm` of the cleaned DGBOZK manuscript.

It verifies:

* the Fourier-symbol identity behind
  `[∂x ∂y², b] = b' ∂y²`;
* the two negative signs in the longitudinal operator
  `L₊^long = -Dₓ^α ∂x`;
* the positive sign obtained from the exact difference formula;
* the numerator identity in the two-component elliptic parametrix;
* nonnegativity of the displayed positive density; and
* the elementary final absorption step.

It does not prove the Wiener-algebra estimate `eq:D-wiener`, the
continuous-shift covering, weighted multiplier bounds, Fourier inversion,
or the integrations by parts. Those remain analytic inputs in the trust
boundary.
-/

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DGBOZK
namespace PositiveCommutatorCore

section CommutatorSymbols

variable {R : Type*} [CommRing R]

/--
Fourier-symbol form of

`[∂x ∂y², b] = b' ∂y²`.

Since `b` depends only on `x`, multiplication by `b` preserves the
transverse frequency. The difference of the two longitudinal symbols is
therefore exactly the symbol of `b'`.
-/
theorem transverse_commutator_symbol
    (I xi xiPrime eta : R) :
    (I * xi) * (I * eta) ^ 2
        - (I * xiPrime) * (I * eta) ^ 2
      =
    (I * (xi - xiPrime)) * (I * eta) ^ 2 := by
  ring

/--
The two negative signs in

`- [L₊^long, b]`, where `L₊^long = -Op(ell)`,

produce the positive commutator associated with `Op(ell)`.
-/
theorem longitudinal_double_negative
    (I p pPrime : R) :
    -((-I * p) - (-I * pPrime))
      = I * p - I * pPrime := by
  ring

/--
Exact sign in the longitudinal commutator kernel.

Here `p - pPrime = (xi - xiPrime) K` is the exact phase-difference
factorization and

`I (xi - xiPrime) bHat`

is the Fourier transform of `b'`. The conclusion confirms that no
additional minus sign occurs in the positive kernel.
-/
theorem longitudinal_commutator_kernel_sign
    (I bHat p pPrime xi xiPrime kernel : R)
    (hdifference :
      p - pPrime = (xi - xiPrime) * kernel) :
    bHat * (-((-I * p) - (-I * pPrime)))
      =
    (I * (xi - xiPrime) * bHat) * kernel := by
  calc
    bHat * (-((-I * p) - (-I * pPrime)))
        = bHat * (I * p - I * pPrime) := by
            ring
    _ = bHat * (I * (p - pPrime)) := by
          ring
    _ = bHat * (I * ((xi - xiPrime) * kernel)) := by
          rw [hdifference]
    _ = (I * (xi - xiPrime) * bHat) * kernel := by
          ring

end CommutatorSymbols

section Parametrix

/--
Numerator identity for the two-component parametrix.

In the manuscript one takes

`a = sqrt(alpha + 1) |xi|^(alpha/2)`

and the transverse derivative has symbol `I eta`. The assumption
`I² = -1` turns the transverse product into `eta²`.
-/
theorem parametrix_numerator_identity
    {F : Type*} [Field F]
    (I a eta : F)
    (hI : I ^ 2 = -1) :
    a * a + (-I * eta) * (I * eta)
      = a ^ 2 + eta ^ 2 := by
  calc
    a * a + (-I * eta) * (I * eta)
        = a ^ 2 - I ^ 2 * eta ^ 2 := by
            ring
    _ = a ^ 2 + eta ^ 2 := by
          rw [hI]
          ring

/--
Exact parametrix identity in inverse-symbol form.

`vInv` represents the reciprocal of

`V² = a² + eta²`.

Thus the two multiplier components reconstruct the identity symbol.
Writing the inverse as an explicit hypothesis avoids hiding the
nonvanishing condition on the high annulus.
-/
theorem two_component_parametrix_identity
    {F : Type*} [Field F]
    (I a eta vInv : F)
    (hI : I ^ 2 = -1)
    (hinverse :
      vInv * (a ^ 2 + eta ^ 2) = 1) :
    (vInv * a) * a
        + (vInv * (-I * eta)) * (I * eta)
      = 1 := by
  calc
    (vInv * a) * a
          + (vInv * (-I * eta)) * (I * eta)
        =
      vInv * (a * a + (-I * eta) * (I * eta)) := by
        ring
    _ = vInv * (a ^ 2 + eta ^ 2) := by
          rw [parametrix_numerator_identity I a eta hI]
    _ = 1 := hinverse

end Parametrix

section PositivityAndAbsorption

/--
The principal density in `lem:positive-comm` is nonnegative once its
longitudinal coefficient is nonnegative.
-/
theorem positive_density_nonneg
    {coefficient longitudinal transverse : ℝ}
    (hcoefficient : 0 ≤ coefficient) :
    0 ≤ coefficient * longitudinal ^ 2 + transverse ^ 2 := by
  exact add_nonneg
    (mul_nonneg hcoefficient (sq_nonneg longitudinal))
    (sq_nonneg transverse)

/--
An error bounded by at most one half of a nonnegative positive form can
be absorbed, leaving at least one half of that form.
-/
theorem absorb_half_of_positive_form
    {positiveForm error coefficient : ℝ}
    (hpositive : 0 ≤ positiveForm)
    (herror : error ≤ coefficient * positiveForm)
    (hcoefficient : coefficient ≤ 1 / 2) :
    positiveForm - error ≥ positiveForm / 2 := by
  have hscaled :
      coefficient * positiveForm ≤ (1 / 2 : ℝ) * positiveForm := by
    exact mul_le_mul_of_nonneg_right hcoefficient hpositive
  linarith

end PositivityAndAbsorption

end PositiveCommutatorCore
end DGBOZK
