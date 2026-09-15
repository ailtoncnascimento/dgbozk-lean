/-
# Transverse resonance conclusion with longitudinal scale closure

This module strengthens `resonance_transverse_sector_conclusion`.

The longitudinal estimate is no longer supplied as an independent
hypothesis. It is derived from:

* `1 <= alpha <= 2`;
* longitudinal frequency localization;
* smallness of the longitudinal increment;
* `N^(alpha/2) <= Cmu * mu`; and
* the large-transverse condition `C1 * mu <= |b|`.

The resulting smallness condition displays the complete longitudinal
error coefficient explicitly.
-/

import DGBOZK.ResonanceTransverseConclusion
import DGBOZK.ResonanceLongitudinalClosure

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
Corrected transverse-resonance conclusion.

Unlike `resonance_transverse_sector_conclusion`, this theorem has no
free `hLong` hypothesis. The required longitudinal bound is derived
internally from the frequency and transverse-scale assumptions.
-/
theorem resonance_transverse_sector_conclusion_from_mu_scale
    {alpha a b xi eta N mu : ℝ}
    {cMinus cPlus Ceta Cmu C1 eps : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hN : 0 ≤ N)
    (hcMinus : 0 ≤ cMinus)
    (hcPlus : 0 ≤ cPlus)
    (hCeta : 0 ≤ Ceta)
    (hCmu : 0 ≤ Cmu)
    (hC1 : 0 < C1)
    (heps : 0 ≤ eps)
    (hxiLow :
      cMinus * N ≤ |xi|)
    (hxiHigh :
      |xi| ≤ cPlus * N)
    (hetaBand :
      |eta| ≤ Ceta * mu)
    (hbLarge :
      C1 * mu ≤ |b|)
    (ha :
      |a| ≤ eps * N)
    (hNmu :
      N ^ (alpha / 2) ≤ Cmu * mu)
    (hsmall :
      ((alpha + 1) * 2 + 1)
            * eps
            * (cPlus ^ alpha + eps ^ alpha)
            * (Cmu / C1) ^ 2
        + 2 * cPlus * (Ceta / C1)
        + eps * (Ceta / C1) ^ 2
        + 2 * eps * (Ceta / C1)
        ≤ cMinus / 2) :
    (cMinus / 2) * N * b ^ 2
        ≤ |resonanceCore alpha a b xi eta|
      ∧
    (cMinus / 2) * C1 * N * mu * |b|
        ≤ |resonanceCore alpha a b xi eta| := by
  have hLong :
      |longitudinalPart alpha a xi|
        ≤
      (((alpha + 1) * 2 + 1)
          * eps
          * (cPlus ^ alpha + eps ^ alpha)
          * (Cmu / C1) ^ 2)
        * (N * b ^ 2) :=
    longitudinal_bound_from_frequency_mu_scales
      halphaOne
      halphaTwo
      heps
      hcPlus
      hN
      hCmu
      hC1
      hxiHigh
      ha
      hNmu
      hbLarge

  exact resonance_transverse_sector_conclusion
    (eLong :=
      ((alpha + 1) * 2 + 1)
        * eps
        * (cPlus ^ alpha + eps ^ alpha)
        * (Cmu / C1) ^ 2)
    hN
    hcMinus
    hcPlus
    hCeta
    hC1
    heps
    hxiLow
    hxiHigh
    hetaBand
    hbLarge
    ha
    hLong
    hsmall

end ResonanceTransverse
end DGBOZK
