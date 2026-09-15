/-
# Conversion from the transverse mu-scale to the resonance b-scale

This module proves

  N^(alpha/2) <= Cmu * mu,
  C1 * mu <= |b|

implies

  N^alpha <= (Cmu / C1)^2 * b^2.

It then combines this fact with `ResonanceLongitudinalScale` to produce
the longitudinal `N b^2` error bound.
-/

import DGBOZK.ResonanceLongitudinalScale
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
Abstract squared-scale transfer.

Here `Nhalf` represents `N^(alpha/2)` and `Npow` represents `N^alpha`.
The identity `Npow = Nhalf^2` is supplied explicitly.
-/
theorem mu_scale_square_bound
    {Nhalf Npow mu b Cmu C1 : ℝ}
    (hNhalf : 0 ≤ Nhalf)
    (hCmu : 0 ≤ Cmu)
    (hC1 : 0 < C1)
    (hNpow : Npow = Nhalf ^ 2)
    (hNmu : Nhalf ≤ Cmu * mu)
    (hb : C1 * mu ≤ |b|) :
    Npow ≤ (Cmu / C1) ^ 2 * b ^ 2 := by
  have hleft :
      C1 * Nhalf ≤ Cmu * |b| := by
    calc
      C1 * Nhalf
          ≤ C1 * (Cmu * mu) := by
            exact mul_le_mul_of_nonneg_left hNmu hC1.le
      _ = Cmu * (C1 * mu) := by
            ring
      _ ≤ Cmu * |b| := by
            exact mul_le_mul_of_nonneg_left hb hCmu

  have hleftNonneg :
      0 ≤ C1 * Nhalf := by
    exact mul_nonneg hC1.le hNhalf

  have hrightNonneg :
      0 ≤ Cmu * |b| := by
    exact mul_nonneg hCmu (abs_nonneg b)

  have hproduct :
      0 ≤
        (Cmu * |b| - C1 * Nhalf)
          * (Cmu * |b| + C1 * Nhalf) := by
    exact mul_nonneg
      (sub_nonneg.mpr hleft)
      (add_nonneg hrightNonneg hleftNonneg)

  have hsquares :
      (C1 * Nhalf) ^ 2
        ≤ (Cmu * |b|) ^ 2 := by
    nlinarith

  have hscaled :
      C1 ^ 2 * Npow
        ≤ Cmu ^ 2 * b ^ 2 := by
    calc
      C1 ^ 2 * Npow
          = (C1 * Nhalf) ^ 2 := by
            rw [hNpow]
            ring
      _ ≤ (Cmu * |b|) ^ 2 :=
        hsquares
      _ = Cmu ^ 2 * |b| ^ 2 := by
        ring
      _ = Cmu ^ 2 * b ^ 2 := by
        rw [sq_abs]

  have hC1sq :
      0 < C1 ^ 2 := by
    positivity

  have hdiv :
      Npow ≤ (Cmu ^ 2 * b ^ 2) / C1 ^ 2 := by
    apply (le_div_iff₀ hC1sq).2
    simpa [mul_comm] using hscaled

  calc
    Npow
        ≤ (Cmu ^ 2 * b ^ 2) / C1 ^ 2 :=
      hdiv
    _ = (Cmu / C1) ^ 2 * b ^ 2 := by
      field_simp [ne_of_gt hC1]

/--
Concrete real-power version of the transverse-scale implication.
-/
theorem rpow_mu_scale_bound
    {alpha N mu b Cmu C1 : ℝ}
    (hN : 0 ≤ N)
    (hCmu : 0 ≤ Cmu)
    (hC1 : 0 < C1)
    (hNmu :
      N ^ (alpha / 2) ≤ Cmu * mu)
    (hb :
      C1 * mu ≤ |b|) :
    N ^ alpha ≤ (Cmu / C1) ^ 2 * b ^ 2 := by
  have hhalfNonneg :
      0 ≤ N ^ (alpha / 2) := by
    exact Real.rpow_nonneg hN (alpha / 2)

  have hexponent :
      alpha = (alpha / 2) * 2 := by
    ring

  have hrewrite :
      N ^ alpha = N ^ ((alpha / 2) * 2) :=
    congrArg (fun exponent : ℝ => N ^ exponent) hexponent

  have hpower :
      N ^ alpha = (N ^ (alpha / 2)) ^ 2 := by
    calc
      N ^ alpha
          = N ^ ((alpha / 2) * 2) :=
            hrewrite
      _ = (N ^ (alpha / 2)) ^ (2 : ℝ) := by
            rw [Real.rpow_mul hN]
      _ = (N ^ (alpha / 2)) ^ 2 := by
            rw [Real.rpow_two]

  exact mu_scale_square_bound
    hhalfNonneg
    hCmu
    hC1
    hpower
    hNmu
    hb

/--
Complete conversion of the universal fractional increment estimate into
the longitudinal `N b^2` bound using the transverse `mu` scale.
-/
theorem longitudinal_bound_from_mu_scale
    {alpha a xi b N mu : ℝ}
    {C eps cXi cA Cmu C1 : ℝ}
    (hC : 0 ≤ C)
    (heps : 0 ≤ eps)
    (hcXi : 0 ≤ cXi)
    (hcA : 0 ≤ cA)
    (hN : 0 ≤ N)
    (hCmu : 0 ≤ Cmu)
    (hC1 : 0 < C1)
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
    (hNmu :
      N ^ (alpha / 2) ≤ Cmu * mu)
    (hb :
      C1 * mu ≤ |b|) :
    |longitudinalPart alpha a xi|
      ≤
    (C * eps * (cXi + cA) * (Cmu / C1) ^ 2)
      * (N * b ^ 2) := by
  have hNscale :
      N ^ alpha
        ≤ (Cmu / C1) ^ 2 * b ^ 2 :=
    rpow_mu_scale_bound
      hN
      hCmu
      hC1
      hNmu
      hb

  exact longitudinal_bound_from_power_scales
    hC
    heps
    hcXi
    hcA
    hN
    hUniversal
    hxiScale
    haScale
    ha
    hNscale

end ResonanceTransverse
end DGBOZK
