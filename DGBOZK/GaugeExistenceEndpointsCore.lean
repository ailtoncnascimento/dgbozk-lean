/-
# Endpoint inequalities for existence of the anisotropic gauge

For nonzero `(xi, eta)` and `1 <= alpha <= 2`, define

  E = |xi|^alpha + eta^2

and

  F(rho) = xi^2 / rho^(2 / alpha) + eta^2 / rho.

This module proves

  F(E) <= 1 <= F(E / 2).

These are the endpoint signs needed for an intermediate-value proof of
existence of a positive solution of the gauge equation.
-/

import DGBOZK.GaugeUniquenessCore

set_option autoImplicit false

namespace DGBOZK
namespace GaugeExistenceEndpointsCore

open GaugeEquationCore
open GaugeLowerEquivalenceCore
open GaugeUpperEquivalenceCore

/-- The exact anisotropic energy used to bracket the gauge root. -/
noncomputable def anisotropicEnergy
    (alpha xi eta : ℝ) : ℝ :=
  |xi| ^ alpha + eta ^ 2

/-- The left side of the gauge defining equation. -/
noncomputable def gaugeLeftSide
    (alpha xi eta rho : ℝ) : ℝ :=
  xi ^ 2 / rho ^ (2 / alpha) + eta ^ 2 / rho

/--
The anisotropic energy is positive away from the origin.
-/
theorem anisotropicEnergy_pos
    {alpha xi eta : ℝ}
    (halpha : 0 < alpha)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    0 < anisotropicEnergy alpha xi eta := by
  have hxNonneg :
      0 ≤ |xi| ^ alpha :=
    Real.rpow_nonneg (abs_nonneg xi) alpha
  have hetaNonneg :
      0 ≤ eta ^ 2 :=
    sq_nonneg eta
  by_contra hnot
  have hEnergyNonpos :
      anisotropicEnergy alpha xi eta ≤ 0 :=
    le_of_not_gt hnot
  have hxZero :
      |xi| ^ alpha = 0 := by
    unfold anisotropicEnergy at hEnergyNonpos
    linarith
  have hetaSquareZero :
      eta ^ 2 = 0 := by
    unfold anisotropicEnergy at hEnergyNonpos
    linarith
  have habsXiZero :
      |xi| = 0 :=
    ((Real.rpow_eq_zero_iff_of_nonneg
      (abs_nonneg xi)).mp hxZero).1
  have hxiZero : xi = 0 :=
    abs_eq_zero.mp habsXiZero
  have hetaZero : eta = 0 := by
    nlinarith
  exact hnonzero ⟨hxiZero, hetaZero⟩

/--
At the upper endpoint `E`, the defining left side is at most one.
-/
theorem gaugeLeftSide_energy_le_one
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    gaugeLeftSide alpha xi eta
        (anisotropicEnergy alpha xi eta)
      ≤ 1 := by
  have halpha : 0 < alpha :=
    lt_of_lt_of_le zero_lt_one halphaOne
  have hEnergyPos :
      0 < anisotropicEnergy alpha xi eta :=
    anisotropicEnergy_pos halpha hnonzero
  have hpNonneg :
      0 ≤ |xi| ^ alpha :=
    Real.rpow_nonneg (abs_nonneg xi) alpha
  have hpUpper :
      |xi| ^ alpha
        ≤ anisotropicEnergy alpha xi eta := by
    unfold anisotropicEnergy
    linarith [sq_nonneg eta]
  have hbeta :
      1 ≤ 2 / alpha := by
    apply (le_div_iff₀ halpha).2
    simpa using halphaTwo
  have hPowerBound :
      (|xi| ^ alpha / anisotropicEnergy alpha xi eta)
          ^ (2 / alpha)
        ≤
      |xi| ^ alpha / anisotropicEnergy alpha xi eta :=
    normalized_ratio_rpow_le_self
      hEnergyPos hpNonneg hpUpper hbeta
  have hRewrite :
      gaugeLeftSide alpha xi eta
          (anisotropicEnergy alpha xi eta)
        =
      (|xi| ^ alpha / anisotropicEnergy alpha xi eta)
          ^ (2 / alpha)
        + eta ^ 2 / anisotropicEnergy alpha xi eta := by
    unfold gaugeLeftSide
    rw [normalized_longitudinal_term halpha hEnergyPos]
  have hRatioSum :
      |xi| ^ alpha / anisotropicEnergy alpha xi eta
          + eta ^ 2 / anisotropicEnergy alpha xi eta
        = 1 := by
    rw [← add_div]
    change
      anisotropicEnergy alpha xi eta
          / anisotropicEnergy alpha xi eta
        = 1
    exact div_self (ne_of_gt hEnergyPos)
  rw [hRewrite]
  linarith

/--
At the lower endpoint `E / 2`, the defining left side is at least one.
-/
theorem one_le_gaugeLeftSide_half_energy
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    1 ≤
      gaugeLeftSide alpha xi eta
        (anisotropicEnergy alpha xi eta / 2) := by
  have halpha : 0 < alpha :=
    lt_of_lt_of_le zero_lt_one halphaOne
  have hEnergyPos :
      0 < anisotropicEnergy alpha xi eta :=
    anisotropicEnergy_pos halpha hnonzero
  have hHalfPos :
      0 < anisotropicEnergy alpha xi eta / 2 := by
    linarith
  have hbetaPos :
      0 < 2 / alpha :=
    div_pos (by norm_num) halpha
  have hRewrite :
      gaugeLeftSide alpha xi eta
          (anisotropicEnergy alpha xi eta / 2)
        =
      (|xi| ^ alpha
          / (anisotropicEnergy alpha xi eta / 2))
          ^ (2 / alpha)
        + eta ^ 2
          / (anisotropicEnergy alpha xi eta / 2) := by
    unfold gaugeLeftSide
    rw [normalized_longitudinal_term halpha hHalfPos]
  rw [hRewrite]
  have hpNonneg :
      0 ≤ |xi| ^ alpha :=
    Real.rpow_nonneg (abs_nonneg xi) alpha
  have hetaNonneg :
      0 ≤ eta ^ 2 :=
    sq_nonneg eta
  rcases le_total (|xi| ^ alpha) (eta ^ 2) with hpLe | hetaLe
  · have hHalfLe :
        anisotropicEnergy alpha xi eta / 2
          ≤ eta ^ 2 := by
      unfold anisotropicEnergy
      linarith
    have hTransverse :
        1 ≤ eta ^ 2
          / (anisotropicEnergy alpha xi eta / 2) := by
      apply (le_div_iff₀ hHalfPos).2
      simpa using hHalfLe
    have hLongitudinalNonneg :
        0 ≤
          (|xi| ^ alpha
            / (anisotropicEnergy alpha xi eta / 2))
            ^ (2 / alpha) :=
      Real.rpow_nonneg
        (div_nonneg hpNonneg (le_of_lt hHalfPos))
        _
    linarith
  · have hHalfLe :
        anisotropicEnergy alpha xi eta / 2
          ≤ |xi| ^ alpha := by
      unfold anisotropicEnergy
      linarith
    have hRatioOne :
        1 ≤ |xi| ^ alpha
          / (anisotropicEnergy alpha xi eta / 2) := by
      apply (le_div_iff₀ hHalfPos).2
      simpa using hHalfLe
    have hPowerOne :
        1 ≤
          (|xi| ^ alpha
            / (anisotropicEnergy alpha xi eta / 2))
            ^ (2 / alpha) := by
      have hRaised :=
        Real.rpow_le_rpow
          (show (0 : ℝ) ≤ 1 by norm_num)
          hRatioOne
          (le_of_lt hbetaPos)
      simpa using hRaised
    have hTransverseNonneg :
        0 ≤ eta ^ 2
          / (anisotropicEnergy alpha xi eta / 2) :=
      div_nonneg hetaNonneg (le_of_lt hHalfPos)
    linarith

end GaugeExistenceEndpointsCore
end DGBOZK
