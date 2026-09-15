/-
# Closure of the fractional longitudinal resonance estimate

This module combines:

* the universal fractional phase-increment estimate;
* ordinary longitudinal frequency localization;
* the relation between the longitudinal and transverse scales; and
* the large-transverse lower bound.

Consequently, the former hypothesis `hLong` can be derived from explicit
scale assumptions rather than supplied independently.
-/

import DGBOZK.FractionalPhaseSecantCore
import DGBOZK.ResonanceMuScale
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
The complete longitudinal estimate from the natural frequency and
transverse-scale assumptions.

The ordinary bounds

  |xi| <= cXi N,
  |a|  <= eps N

are converted into their `alpha`-power versions internally.
-/
theorem longitudinal_bound_from_frequency_mu_scales
    {alpha a xi b N mu : ℝ}
    {eps cXi Cmu C1 : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (heps : 0 ≤ eps)
    (hcXi : 0 ≤ cXi)
    (hN : 0 ≤ N)
    (hCmu : 0 ≤ Cmu)
    (hC1 : 0 < C1)
    (hxi :
      |xi| ≤ cXi * N)
    (ha :
      |a| ≤ eps * N)
    (hNmu :
      N ^ (alpha / 2) ≤ Cmu * mu)
    (hb :
      C1 * mu ≤ |b|) :
    |longitudinalPart alpha a xi|
      ≤
    (((alpha + 1) * 2 + 1)
        * eps
        * (cXi ^ alpha + eps ^ alpha)
        * (Cmu / C1) ^ 2)
      * (N * b ^ 2) := by
  have halphaNonneg : 0 ≤ alpha :=
    le_trans zero_le_one halphaOne

  have hUniversal :
      |longitudinalPart alpha a xi|
        ≤
      ((alpha + 1) * 2 + 1)
        * |a| * (|xi| ^ alpha + |a| ^ alpha) :=
    longitudinal_increment_universal
      halphaOne halphaTwo

  have hxiScale :
      |xi| ^ alpha
        ≤ cXi ^ alpha * N ^ alpha := by
    calc
      |xi| ^ alpha
          ≤ (cXi * N) ^ alpha :=
        Real.rpow_le_rpow
          (abs_nonneg xi)
          hxi
          halphaNonneg
      _ = cXi ^ alpha * N ^ alpha :=
        Real.mul_rpow hcXi hN

  have haScale :
      |a| ^ alpha
        ≤ eps ^ alpha * N ^ alpha := by
    calc
      |a| ^ alpha
          ≤ (eps * N) ^ alpha :=
        Real.rpow_le_rpow
          (abs_nonneg a)
          ha
          halphaNonneg
      _ = eps ^ alpha * N ^ alpha :=
        Real.mul_rpow heps hN

  have hC :
      0 ≤ (alpha + 1) * 2 + 1 := by
    linarith

  exact longitudinal_bound_from_mu_scale
    (C := (alpha + 1) * 2 + 1)
    (eps := eps)
    (cXi := cXi ^ alpha)
    (cA := eps ^ alpha)
    (Cmu := Cmu)
    (C1 := C1)
    hC
    heps
    (Real.rpow_nonneg hcXi alpha)
    (Real.rpow_nonneg heps alpha)
    hN
    hCmu
    hC1
    hUniversal
    hxiScale
    haScale
    ha
    hNmu
    hb

/--
A direct replacement for an `hLong`-style hypothesis.

Once `eLong` dominates the explicit scale coefficient, the desired
longitudinal error estimate follows.
-/
theorem longitudinal_hLong_from_frequency_mu_scales
    {alpha a xi b N mu eLong : ℝ}
    {eps cXi Cmu C1 : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (heps : 0 ≤ eps)
    (hcXi : 0 ≤ cXi)
    (hN : 0 ≤ N)
    (hCmu : 0 ≤ Cmu)
    (hC1 : 0 < C1)
    (hxi :
      |xi| ≤ cXi * N)
    (ha :
      |a| ≤ eps * N)
    (hNmu :
      N ^ (alpha / 2) ≤ Cmu * mu)
    (hb :
      C1 * mu ≤ |b|)
    (hsmall :
      ((alpha + 1) * 2 + 1)
          * eps
          * (cXi ^ alpha + eps ^ alpha)
          * (Cmu / C1) ^ 2
        ≤ eLong) :
    |longitudinalPart alpha a xi|
      ≤ eLong * (N * b ^ 2) := by
  have hbound :=
    longitudinal_bound_from_frequency_mu_scales
      halphaOne
      halphaTwo
      heps
      hcXi
      hN
      hCmu
      hC1
      hxi
      ha
      hNmu
      hb

  have hNb : 0 ≤ N * b ^ 2 :=
    mul_nonneg hN (sq_nonneg b)

  exact hbound.trans
    (mul_le_mul_of_nonneg_right hsmall hNb)

end ResonanceTransverse
end DGBOZK
