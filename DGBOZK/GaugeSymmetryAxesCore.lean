/-
# Symmetry and axial identities of the anisotropic gauge

This module proves that the selected anisotropic gauge is even in both
frequency coordinates and has the exact axial values

  rho_alpha(xi, 0) = |xi|^alpha,
  rho_alpha(0, eta) = eta^2.

The proofs use invariance of the defining equation and uniqueness of its
positive root.
-/

import DGBOZK.GaugeFunctionCore

set_option autoImplicit false

namespace DGBOZK
namespace GaugeSymmetryAxesCore

open GaugeEquationCore
open GaugeFunctionCore
open GaugeLowerEquivalenceCore
open GaugeUpperEquivalenceCore
open GaugeUniquenessCore

/-- The selected gauge is even in the longitudinal coordinate. -/
theorem anisotropicGauge_neg_x
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2) :
    anisotropicGauge alpha (-xi) eta
      = anisotropicGauge alpha xi eta := by
  by_cases hzero : xi = 0 ∧ eta = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp
  · have hnegNonzero :
        ¬((-xi) = 0 ∧ eta = 0) := by
      rintro ⟨hxi, heta⟩
      apply hzero
      exact ⟨neg_eq_zero.mp hxi, heta⟩
    exact
      anisotropicGauge_eq_of_positive_solution
        halphaOne
        halphaTwo
        hnegNonzero
        (anisotropicGauge_pos
          halphaOne halphaTwo hzero)
        ((gaugeEquation_neg_x_iff
          alpha xi eta
          (anisotropicGauge alpha xi eta)).2
          (anisotropicGauge_equation
            halphaOne halphaTwo hzero))

/-- The selected gauge is even in the transverse coordinate. -/
theorem anisotropicGauge_neg_y
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2) :
    anisotropicGauge alpha xi (-eta)
      = anisotropicGauge alpha xi eta := by
  by_cases hzero : xi = 0 ∧ eta = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp
  · have hnegNonzero :
        ¬(xi = 0 ∧ (-eta) = 0) := by
      rintro ⟨hxi, heta⟩
      apply hzero
      exact ⟨hxi, neg_eq_zero.mp heta⟩
    exact
      anisotropicGauge_eq_of_positive_solution
        halphaOne
        halphaTwo
        hnegNonzero
        (anisotropicGauge_pos
          halphaOne halphaTwo hzero)
        ((gaugeEquation_neg_y_iff
          alpha xi eta
          (anisotropicGauge alpha xi eta)).2
          (anisotropicGauge_equation
            halphaOne halphaTwo hzero))

/-- The selected gauge is simultaneously even in both coordinates. -/
theorem anisotropicGauge_neg_both
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2) :
    anisotropicGauge alpha (-xi) (-eta)
      = anisotropicGauge alpha xi eta := by
  rw [
    anisotropicGauge_neg_y halphaOne halphaTwo,
    anisotropicGauge_neg_x halphaOne halphaTwo
  ]

/-- On the transverse axis, the gauge equals `eta^2`. -/
theorem anisotropicGauge_zero_x
    {alpha eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2) :
    anisotropicGauge alpha 0 eta
      = eta ^ 2 := by
  by_cases heta : eta = 0
  · subst eta
    simp [anisotropicGauge_origin]
  · have hnonzero :
        ¬((0 : ℝ) = 0 ∧ eta = 0) := by
      simp [heta]
    exact
      positive_root_eq_y_square_of_x_eq_zero
        (anisotropicGauge_pos
          halphaOne halphaTwo hnonzero)
        rfl
        (anisotropicGauge_equation
          halphaOne halphaTwo hnonzero)

/-- On the longitudinal axis, the gauge equals `|xi|^alpha`. -/
theorem anisotropicGauge_zero_y
    {alpha xi : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2) :
    anisotropicGauge alpha xi 0
      = |xi| ^ alpha := by
  by_cases hxi : xi = 0
  · subst xi
    have halpha : 0 < alpha :=
      lt_of_lt_of_le zero_lt_one halphaOne
    simp [
      anisotropicGauge_origin,
      Real.zero_rpow (ne_of_gt halpha)
    ]
  · have hnonzero :
        ¬(xi = 0 ∧ (0 : ℝ) = 0) := by
      simp [hxi]
    have halpha : 0 < alpha :=
      lt_of_lt_of_le zero_lt_one halphaOne
    have hCandidatePos :
        0 < |xi| ^ alpha :=
      Real.rpow_pos_of_pos
        (abs_pos.mpr hxi) alpha
    have hCollapse :
        (|xi| ^ alpha) ^ (2 / alpha)
          = xi ^ 2 :=
      abs_rpow_alpha_then_two_div_alpha halpha
    have hCandidateEquation :
        gaugeEquation alpha xi 0
          (|xi| ^ alpha) := by
      unfold gaugeEquation
      rw [hCollapse]
      simp [hxi]
    exact
      anisotropicGauge_eq_of_positive_solution
        halphaOne
        halphaTwo
        hnonzero
        hCandidatePos
        hCandidateEquation

end GaugeSymmetryAxesCore
end DGBOZK
