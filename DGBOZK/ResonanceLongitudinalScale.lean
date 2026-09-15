/-
# Longitudinal scale conversion for the transverse resonance

This module proves the ordered-algebra step converting a universal
fractional phase-increment estimate into the `N b^2` bound required by
the transverse-resonance absorption argument.

It does not yet prove the universal fractional increment estimate

  |L_alpha(a,xi)|
    <= C_alpha |a| (|xi|^alpha + |a|^alpha).

That analytic estimate remains an explicit hypothesis here and will be
treated in a separate module.
-/

import DGBOZK.ResonanceTransverseCore
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
Abstract scale-conversion lemma.

The quantities `xiPow`, `aPow`, and `Npow` represent, respectively,

  |xi|^alpha, |a|^alpha, and N^alpha.

Keeping them abstract makes the ordered-algebra argument independent of
the implementation details of real powers.
-/
theorem longitudinal_bound_from_abstract_scales
    {alpha a xi b N Npow xiPow aPow : ℝ}
    {C eps cXi cA kappa : ℝ}
    (hC : 0 ≤ C)
    (heps : 0 ≤ eps)
    (hcXi : 0 ≤ cXi)
    (hcA : 0 ≤ cA)
    (hN : 0 ≤ N)
    (hxiPowNonneg : 0 ≤ xiPow)
    (haPowNonneg : 0 ≤ aPow)
    (hUniversal :
      |longitudinalPart alpha a xi|
        ≤ C * |a| * (xiPow + aPow))
    (hxiScale :
      xiPow ≤ cXi * Npow)
    (haScale :
      aPow ≤ cA * Npow)
    (ha :
      |a| ≤ eps * N)
    (hNscale :
      Npow ≤ kappa * b ^ 2) :
    |longitudinalPart alpha a xi|
      ≤
    (C * eps * (cXi + cA) * kappa)
      * (N * b ^ 2) := by
  have hsumNonneg :
      0 ≤ xiPow + aPow := by
    exact add_nonneg hxiPowNonneg haPowNonneg

  have hcoefficientNonneg :
      0 ≤ cXi + cA := by
    exact add_nonneg hcXi hcA

  have hepsN :
      0 ≤ eps * N := by
    exact mul_nonneg heps hN

  have hsumScale :
      xiPow + aPow
        ≤ (cXi + cA) * Npow := by
    calc
      xiPow + aPow
          ≤ cXi * Npow + cA * Npow := by
            exact add_le_add hxiScale haScale
      _ = (cXi + cA) * Npow := by
            ring

  have hproductScale :
      |a| * (xiPow + aPow)
        ≤
      (eps * N) * ((cXi + cA) * Npow) := by
    exact mul_le_mul ha hsumScale hsumNonneg hepsN

  have hNNpow :
      N * Npow
        ≤ N * (kappa * b ^ 2) := by
    exact mul_le_mul_of_nonneg_left hNscale hN

  have hscale :
      (eps * N) * ((cXi + cA) * Npow)
        ≤
      (eps * (cXi + cA) * kappa)
        * (N * b ^ 2) := by
    calc
      (eps * N) * ((cXi + cA) * Npow)
          =
        (eps * (cXi + cA)) * (N * Npow) := by
          ring
      _ ≤
        (eps * (cXi + cA))
          * (N * (kappa * b ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            hNNpow
            (mul_nonneg heps hcoefficientNonneg)
      _ =
        (eps * (cXi + cA) * kappa)
          * (N * b ^ 2) := by
          ring

  calc
    |longitudinalPart alpha a xi|
        ≤ C * |a| * (xiPow + aPow) :=
      hUniversal
    _ =
        C * (|a| * (xiPow + aPow)) := by
      ring
    _ ≤
        C * ((eps * N) * ((cXi + cA) * Npow)) := by
      exact mul_le_mul_of_nonneg_left hproductScale hC
    _ ≤
        C *
          ((eps * (cXi + cA) * kappa)
            * (N * b ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hscale hC
    _ =
        (C * eps * (cXi + cA) * kappa)
          * (N * b ^ 2) := by
      ring

/--
Concrete real-power version.

This is the exact bridge needed by `ResonanceTransverseConclusion`.
The hypotheses `hxiScale` and `haScale` record the consequences of
frequency localization, while `hNscale` is the missing relation between
the longitudinal and transverse scales.
-/
theorem longitudinal_bound_from_power_scales
    {alpha a xi b N : ℝ}
    {C eps cXi cA kappa : ℝ}
    (hC : 0 ≤ C)
    (heps : 0 ≤ eps)
    (hcXi : 0 ≤ cXi)
    (hcA : 0 ≤ cA)
    (hN : 0 ≤ N)
    (hUniversal :
      |longitudinalPart alpha a xi|
        ≤
      C * |a| * (|xi| ^ alpha + |a| ^ alpha))
    (hxiScale :
      |xi| ^ alpha ≤ cXi * N ^ alpha)
    (haScale :
      |a| ^ alpha ≤ cA * N ^ alpha)
    (ha :
      |a| ≤ eps * N)
    (hNscale :
      N ^ alpha ≤ kappa * b ^ 2) :
    |longitudinalPart alpha a xi|
      ≤
    (C * eps * (cXi + cA) * kappa)
      * (N * b ^ 2) := by
  exact longitudinal_bound_from_abstract_scales
    hC
    heps
    hcXi
    hcA
    hN
    (Real.rpow_nonneg (abs_nonneg xi) alpha)
    (Real.rpow_nonneg (abs_nonneg a) alpha)
    hUniversal
    hxiScale
    haScale
    ha
    hNscale

end ResonanceTransverse
end DGBOZK
