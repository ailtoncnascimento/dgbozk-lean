/-
# Targeted conclusion of the transverse resonance estimate

This module combines:

* the exact transverse-resonance expansion;
* the large-transverse scale conversion;
* the three polynomial component estimates; and
* the reverse-triangle absorption argument.

The longitudinal fractional phase increment remains an explicit analytic
hypothesis. No multiplier or all-orders Marcinkiewicz estimate is claimed.
-/

import DGBOZK.ResonanceTransverseComponents

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
The resonance lower bound expressed using the relative transverse parameter

  |eta| <= q |b|.

All polynomial error terms are derived internally. The only remaining
component estimate supplied as a hypothesis is the longitudinal fractional
phase increment.
-/
theorem resonance_lower_bound_of_relative_sector
    {alpha a b xi eta N cMinus cPlus eps q eLong : ℝ}
    (hN : 0 ≤ N)
    (hcPlus : 0 ≤ cPlus)
    (heps : 0 ≤ eps)
    (hq : 0 ≤ q)
    (hxiLow : cMinus * N ≤ |xi|)
    (hxiHigh : |xi| ≤ cPlus * N)
    (ha : |a| ≤ eps * N)
    (heta : |eta| ≤ q * |b|)
    (hLong :
      |longitudinalPart alpha a xi|
        ≤ eLong * (N * b ^ 2))
    (hsmall :
      eLong
        + 2 * cPlus * q
        + eps * q ^ 2
        + 2 * eps * q
        ≤ cMinus / 2) :
    (cMinus / 2) * N * b ^ 2
      ≤ |resonanceCore alpha a b xi eta| := by
  exact resonance_lower_bound_of_component_bounds
    hN
    hxiLow
    hLong
    (cross_error_bound
      hN hcPlus hq hxiHigh heta)
    (eta_square_error_bound
      hN heps hq ha heta)
    (mixed_error_bound
      hN heps hq ha heta)
    hsmall

/--
Large-transverse conclusion in the original variables.

From

  |eta| <= Ceta mu,
  C1 mu <= |b|,

we set `q = Ceta / C1`. Under the explicit coefficient-smallness condition,
the resonance controls both `N b^2` and `C1 N mu |b|`.
-/
theorem resonance_transverse_sector_conclusion
    {alpha a b xi eta N mu : ℝ}
    {cMinus cPlus Ceta C1 eps eLong : ℝ}
    (hN : 0 ≤ N)
    (hcMinus : 0 ≤ cMinus)
    (hcPlus : 0 ≤ cPlus)
    (hCeta : 0 ≤ Ceta)
    (hC1 : 0 < C1)
    (heps : 0 ≤ eps)
    (hxiLow : cMinus * N ≤ |xi|)
    (hxiHigh : |xi| ≤ cPlus * N)
    (hetaBand : |eta| ≤ Ceta * mu)
    (hbLarge : C1 * mu ≤ |b|)
    (ha : |a| ≤ eps * N)
    (hLong :
      |longitudinalPart alpha a xi|
        ≤ eLong * (N * b ^ 2))
    (hsmall :
      eLong
        + 2 * cPlus * (Ceta / C1)
        + eps * (Ceta / C1) ^ 2
        + 2 * eps * (Ceta / C1)
        ≤ cMinus / 2) :
    (cMinus / 2) * N * b ^ 2
        ≤ |resonanceCore alpha a b xi eta|
      ∧
    (cMinus / 2) * C1 * N * mu * |b|
        ≤ |resonanceCore alpha a b xi eta| := by
  have hq :
      0 ≤ Ceta / C1 :=
    div_nonneg hCeta (le_of_lt hC1)

  have hetaRelative :
      |eta| ≤ (Ceta / C1) * |b| :=
    eta_le_ratio_mul_abs_b
      hCeta hC1 hetaBand hbLarge

  have hquadratic :
      (cMinus / 2) * N * b ^ 2
        ≤ |resonanceCore alpha a b xi eta| :=
    resonance_lower_bound_of_relative_sector
      hN
      hcPlus
      heps
      hq
      hxiLow
      hxiHigh
      ha
      hetaRelative
      hLong
      hsmall

  have hcStar :
      0 ≤ cMinus / 2 := by
    positivity

  have hlinearScale :
      (cMinus / 2) * C1 * N * mu * |b|
        ≤ (cMinus / 2) * N * b ^ 2 :=
    transverse_square_controls_linear_scale
      hcStar hN hbLarge

  exact ⟨hquadratic, hlinearScale.trans hquadratic⟩

end ResonanceTransverse
end DGBOZK
