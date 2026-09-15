/-
# Exact algebra for the transverse focusing resonance

This module audits the sign-sensitive polynomial identities in
`lem:resonance-transverse` and in the discussion of the exact reflection
resonance.

It does not prove the analytic multiplier estimates or the all-orders
Marcinkiewicz bounds. Those remain outside the targeted Lean verification.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
The longitudinal contribution to the focusing resonance

  omega_-(a,b) + omega_-(xi,eta) - omega_-(xi+a,eta+b).

The terms involving the transverse variables are separated below.
-/
noncomputable def longitudinalPart
    (alpha a xi : ℝ) : ℝ :=
  -a * |a| ^ alpha
    - xi * |xi| ^ alpha
    + (xi + a) * |xi + a| ^ alpha

/-- The exact transverse polynomial contribution to the resonance. -/
def transversePart
    (xi eta a b : ℝ) : ℝ :=
  a * b ^ 2
    + xi * eta ^ 2
    - (xi + a) * (eta + b) ^ 2

/-- The algebraic focusing resonance, split into longitudinal and transverse parts. -/
noncomputable def resonanceCore
    (alpha a b xi eta : ℝ) : ℝ :=
  longitudinalPart alpha a xi
    + transversePart xi eta a b

/-- All transverse terms except the principal contribution `-xi * b^2`. -/
def transverseError
    (xi eta a b : ℝ) : ℝ :=
  -2 * xi * eta * b
    - a * eta ^ 2
    - 2 * a * eta * b

/--
Exact expansion used in the proof of `lem:resonance-transverse`:

  a b^2 + xi eta^2 - (xi+a)(eta+b)^2
    = -xi b^2 - 2 xi eta b - a eta^2 - 2 a eta b.
-/
theorem transversePart_expansion
    (xi eta a b : ℝ) :
    transversePart xi eta a b =
      -xi * b ^ 2
        - 2 * xi * eta * b
        - a * eta ^ 2
        - 2 * a * eta * b := by
  unfold transversePart
  ring

/-- Separation of the principal term from the complete error. -/
theorem resonanceCore_decomposition
    (alpha a b xi eta : ℝ) :
    resonanceCore alpha a b xi eta =
      -xi * b ^ 2
        + (longitudinalPart alpha a xi
          + transverseError xi eta a b) := by
  unfold resonanceCore transversePart transverseError
  ring

/--
The transverse reflection `a=0`, `b=-2 eta` is exactly resonant.
This validates the sign in `eq:exact-resonance`.
-/
theorem exact_reflection_resonance
    (alpha xi eta : ℝ) :
    resonanceCore alpha 0 (-2 * eta) xi eta = 0 := by
  simp [resonanceCore, longitudinalPart, transversePart]
  ring

/--
The cross-chart example `a=0`, `b=-3 eta` is nonzero algebraically:

  Omega = -3 xi eta^2.

Thus it is not part of the exact reflection resonance unless
`xi=0` or `eta=0`.
-/
theorem crossChart_resonance
    (alpha xi eta : ℝ) :
    resonanceCore alpha 0 (-3 * eta) xi eta =
      -3 * xi * eta ^ 2 := by
  simp [resonanceCore, longitudinalPart, transversePart]
  ring

/-- The cross-chart example is nonresonant when `xi` and `eta` are nonzero. -/
theorem crossChart_resonance_ne_zero
    {alpha xi eta : ℝ}
    (hxi : xi ≠ 0)
    (heta : eta ≠ 0) :
    resonanceCore alpha 0 (-3 * eta) xi eta ≠ 0 := by
  rw [crossChart_resonance]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) hxi)
    (pow_ne_zero 2 heta)

end ResonanceTransverse
end DGBOZK
