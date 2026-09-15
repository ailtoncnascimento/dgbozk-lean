/-
# Anisotropic homogeneity of the selected gauge

For `lambda > 0`, this module proves

  rho_alpha(lambda^(1/alpha) xi, lambda^(1/2) eta)
    = lambda rho_alpha(xi, eta).

The proof verifies that the right side satisfies the defining equation at
the scaled point and then uses uniqueness of the positive root.
-/

import DGBOZK.GaugeSymmetryAxesCore

set_option autoImplicit false

namespace DGBOZK
namespace GaugeHomogeneityCore

open GaugeEquationCore
open GaugeFunctionCore
open GaugeSymmetryAxesCore

/-- Squaring the longitudinal scaling factor produces `lambda^(2/alpha)`. -/
theorem longitudinal_scale_square
    {alpha scale : ℝ}
    (hscale : 0 < scale) :
    (scale ^ (1 / alpha)) ^ (2 : ℕ)
      = scale ^ (2 / alpha) := by
  calc
    (scale ^ (1 / alpha)) ^ (2 : ℕ)
        =
      scale ^ ((1 / alpha) * (2 : ℝ)) := by
        symm
        simpa using
          (Real.rpow_mul_natCast
            (le_of_lt hscale)
            (1 / alpha)
            2)
    _ = scale ^ (2 / alpha) := by
      congr 1
      ring

/-- Squaring the transverse scaling factor produces `lambda`. -/
theorem transverse_scale_square
    {scale : ℝ}
    (hscale : 0 < scale) :
    (scale ^ (1 / 2 : ℝ)) ^ (2 : ℕ)
      = scale := by
  calc
    (scale ^ (1 / 2 : ℝ)) ^ (2 : ℕ)
        =
      scale ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        symm
        simpa using
          (Real.rpow_mul_natCast
            (le_of_lt hscale)
            (1 / 2 : ℝ)
            2)
    _ = scale ^ (1 : ℝ) := by
      congr 1
      ring
    _ = scale := Real.rpow_one scale

/--
The selected gauge is anisotropically homogeneous of degree one.
-/
theorem anisotropicGauge_homogeneous
    {alpha xi eta scale : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hscale : 0 < scale) :
    anisotropicGauge alpha
        (scale ^ (1 / alpha) * xi)
        (scale ^ (1 / 2 : ℝ) * eta)
      =
    scale * anisotropicGauge alpha xi eta := by
  by_cases hzero : xi = 0 ∧ eta = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [anisotropicGauge_origin]
  · have hscaleXPos :
        0 < scale ^ (1 / alpha) :=
      Real.rpow_pos_of_pos hscale _
    have hscaleYPos :
        0 < scale ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hscale _
    have hscaledNonzero :
        ¬(scale ^ (1 / alpha) * xi = 0
          ∧ scale ^ (1 / 2 : ℝ) * eta = 0) := by
      rintro ⟨hx, hy⟩
      apply hzero
      constructor
      · exact
          (mul_eq_zero.mp hx).resolve_left
            (ne_of_gt hscaleXPos)
      · exact
          (mul_eq_zero.mp hy).resolve_left
            (ne_of_gt hscaleYPos)
    have hrhoPos :
        0 < anisotropicGauge alpha xi eta :=
      anisotropicGauge_pos
        halphaOne halphaTwo hzero
    have hCandidatePos :
        0 <
          scale * anisotropicGauge alpha xi eta :=
      mul_pos hscale hrhoPos
    have hScaleRho :
        (scale * anisotropicGauge alpha xi eta)
            ^ (2 / alpha)
          =
        scale ^ (2 / alpha)
          * anisotropicGauge alpha xi eta
              ^ (2 / alpha) := by
      rw [
        Real.mul_rpow
          (le_of_lt hscale)
          (le_of_lt hrhoPos)
      ]
    have hScaleX :
        (scale ^ (1 / alpha) * xi) ^ 2
          =
        scale ^ (2 / alpha) * xi ^ 2 := by
      rw [mul_pow, longitudinal_scale_square hscale]
    have hScaleY :
        (scale ^ (1 / 2 : ℝ) * eta) ^ 2
          =
        scale * eta ^ 2 := by
      rw [mul_pow, transverse_scale_square hscale]
    have hScalePowPos :
        0 < scale ^ (2 / alpha) :=
      Real.rpow_pos_of_pos hscale _
    have hRhoPowPos :
        0 <
          anisotropicGauge alpha xi eta
            ^ (2 / alpha) :=
      Real.rpow_pos_of_pos hrhoPos _
    have hLongitudinalCancel :
        (scale ^ (2 / alpha) * xi ^ 2)
              /
            (scale ^ (2 / alpha)
              * anisotropicGauge alpha xi eta
                  ^ (2 / alpha))
          =
        xi ^ 2
              /
            anisotropicGauge alpha xi eta
              ^ (2 / alpha) := by
      field_simp [
        ne_of_gt hScalePowPos,
        ne_of_gt hRhoPowPos
      ]
      ring
    have hTransverseCancel :
        (scale * eta ^ 2)
              /
            (scale * anisotropicGauge alpha xi eta)
          =
        eta ^ 2
              /
            anisotropicGauge alpha xi eta := by
      field_simp [
        ne_of_gt hscale,
        ne_of_gt hrhoPos
      ]
      ring
    have hCandidateEquation :
        gaugeEquation alpha
          (scale ^ (1 / alpha) * xi)
          (scale ^ (1 / 2 : ℝ) * eta)
          (scale * anisotropicGauge alpha xi eta) := by
      have hOriginal :
          gaugeEquation alpha xi eta
            (anisotropicGauge alpha xi eta) :=
        anisotropicGauge_equation
          halphaOne halphaTwo hzero
      unfold gaugeEquation at hOriginal ⊢
      rw [hScaleX, hScaleY, hScaleRho]
      rw [hLongitudinalCancel, hTransverseCancel]
      exact hOriginal
    exact
      anisotropicGauge_eq_of_positive_solution
        halphaOne
        halphaTwo
        hscaledNonzero
        hCandidatePos
        hCandidateEquation

end GaugeHomogeneityCore
end DGBOZK
