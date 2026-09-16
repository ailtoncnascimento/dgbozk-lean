/-
# Implicit denominator for the anisotropic gauge

For the scalar gauge equation

  xi^2 / rho^(2 / alpha) + eta^2 / rho = 1,

the denominator occurring in implicit differentiation is

  D = (2 / alpha) * xi^2 / rho^(2 / alpha)
        + eta^2 / rho.

On the manuscript range `1 <= alpha <= 2`, this module proves

  1 <= D <= 2.

Consequently, the derivative of the defining residual in the radial
variable is strictly negative and hence nondegenerate.

The module also solves the two formal first-order differentiated equations
for the longitudinal and transverse derivatives.

It does not prove differentiability of the choice-defined gauge, invoke an
implicit-function theorem, or establish higher-order symbol estimates.
Those remain analytic inputs.
-/

import DGBOZK.GaugeHomogeneityCore
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace GaugeImplicitCore

open GaugeEquationCore
open GaugeFunctionCore

/--
The positive denominator that occurs after differentiating the gauge
equation with respect to the radial variable.
-/
noncomputable def gaugeRadialDenominator
    (alpha xi eta rho : ℝ) : ℝ :=
  (2 / alpha)
      * (xi ^ 2 / rho ^ (2 / alpha))
    + eta ^ 2 / rho

/--
For `1 <= alpha <= 2`, the implicit denominator belongs to `[1,2]`.

This is the precise scalar nondegeneracy behind the smooth-gauge
construction: the two normalized summands are nonnegative and add to one,
while the longitudinal coefficient `2 / alpha` also belongs to `[1,2]`.
-/
theorem gaugeRadialDenominator_mem_Icc
    {alpha xi eta rho : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    1 ≤ gaugeRadialDenominator alpha xi eta rho
      ∧
    gaugeRadialDenominator alpha xi eta rho ≤ 2 := by
  have halphaPos : 0 < alpha :=
    lt_of_lt_of_le zero_lt_one halphaOne

  obtain ⟨⟨hLongNonneg, _⟩, ⟨hTransNonneg, _⟩⟩ :=
    normalized_terms_mem_unit_interval hrho hEquation

  have hCoefficientLower :
      1 ≤ 2 / alpha := by
    apply (le_div_iff₀ halphaPos).2
    simpa using halphaTwo

  have hCoefficientUpper :
      2 / alpha ≤ 2 := by
    apply (div_le_iff₀ halphaPos).2
    nlinarith

  have hLongLower :
      xi ^ 2 / rho ^ (2 / alpha)
        ≤
      (2 / alpha)
        * (xi ^ 2 / rho ^ (2 / alpha)) := by
    simpa using
      mul_le_mul_of_nonneg_right
        hCoefficientLower
        hLongNonneg

  have hLongUpper :
      (2 / alpha)
          * (xi ^ 2 / rho ^ (2 / alpha))
        ≤
      2 * (xi ^ 2 / rho ^ (2 / alpha)) := by
    exact
      mul_le_mul_of_nonneg_right
        hCoefficientUpper
        hLongNonneg

  have hTransUpper :
      eta ^ 2 / rho ≤ 2 * (eta ^ 2 / rho) := by
    nlinarith

  have hSum :
      xi ^ 2 / rho ^ (2 / alpha)
          + eta ^ 2 / rho
        =
      1 := by
    simpa [gaugeEquation] using hEquation

  constructor
  · dsimp [gaugeRadialDenominator]
    linarith
  · dsimp [gaugeRadialDenominator]
    linarith

/-- The implicit denominator is strictly positive. -/
theorem gaugeRadialDenominator_pos
    {alpha xi eta rho : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    0 < gaugeRadialDenominator alpha xi eta rho := by
  have hBounds :=
    gaugeRadialDenominator_mem_Icc
      halphaOne halphaTwo hrho hEquation
  exact lt_of_lt_of_le zero_lt_one hBounds.1

/-- The implicit denominator cannot vanish. -/
theorem gaugeRadialDenominator_ne_zero
    {alpha xi eta rho : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    gaugeRadialDenominator alpha xi eta rho ≠ 0 :=
  ne_of_gt
    (gaugeRadialDenominator_pos
      halphaOne halphaTwo hrho hEquation)

/--
The radial derivative of the defining residual, written in factored form.
-/
noncomputable def gaugeRadialDerivative
    (alpha xi eta rho : ℝ) : ℝ :=
  -(gaugeRadialDenominator alpha xi eta rho / rho)

/--
The radial derivative of the defining residual is strictly negative.
This is the scalar transversality needed by the implicit-function argument.
-/
theorem gaugeRadialDerivative_neg
    {alpha xi eta rho : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    gaugeRadialDerivative alpha xi eta rho < 0 := by
  have hDenominatorPos :
      0 < gaugeRadialDenominator alpha xi eta rho :=
    gaugeRadialDenominator_pos
      halphaOne halphaTwo hrho hEquation

  have hQuotientPos :
      0 <
        gaugeRadialDenominator alpha xi eta rho / rho :=
    div_pos hDenominatorPos hrho

  dsimp [gaugeRadialDerivative]
  linarith

/--
Exact solution of the formal longitudinal differentiated equation.

The hypothesis is the identity obtained after differentiating the defining
equation with respect to `xi`. No differentiability claim is hidden here.
-/
theorem longitudinal_implicit_derivative_formula
    {alpha xi eta rho dXi : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho)
    (hDifferentiated :
      2 * xi / rho ^ (2 / alpha)
        -
      (gaugeRadialDenominator alpha xi eta rho / rho)
        * dXi
        =
      0) :
    dXi
      =
    (2 * xi * rho)
      /
    (rho ^ (2 / alpha)
      * gaugeRadialDenominator alpha xi eta rho) := by
  have hDenominatorPos :
      0 < gaugeRadialDenominator alpha xi eta rho :=
    gaugeRadialDenominator_pos
      halphaOne halphaTwo hrho hEquation

  have hPowerPos :
      0 < rho ^ (2 / alpha) :=
    Real.rpow_pos_of_pos hrho _

  have hRhoNe : rho ≠ 0 := ne_of_gt hrho
  have hPowerNe : rho ^ (2 / alpha) ≠ 0 :=
    ne_of_gt hPowerPos
  have hDenominatorNe :
      gaugeRadialDenominator alpha xi eta rho ≠ 0 :=
    ne_of_gt hDenominatorPos

  have hNested :
      dXi
        =
      (2 * xi / rho ^ (2 / alpha))
        /
      (gaugeRadialDenominator alpha xi eta rho / rho) := by
    apply
      (eq_div_iff
        (div_ne_zero hDenominatorNe hRhoNe)).2
    calc
      dXi
          * (gaugeRadialDenominator alpha xi eta rho / rho)
          =
        (gaugeRadialDenominator alpha xi eta rho / rho)
          * dXi := by
            ring
      _ = 2 * xi / rho ^ (2 / alpha) := by
            linarith

  calc
    dXi
        =
      (2 * xi / rho ^ (2 / alpha))
        /
      (gaugeRadialDenominator alpha xi eta rho / rho) :=
        hNested
    _ =
      (2 * xi * rho)
        /
      (rho ^ (2 / alpha)
        * gaugeRadialDenominator alpha xi eta rho) := by
          field_simp [
            hRhoNe,
            hPowerNe,
            hDenominatorNe
          ]

/--
Exact solution of the formal transverse differentiated equation.

The cancellation of the common radial factor yields the particularly simple
formula `dEta = 2 eta / D`.
-/
theorem transverse_implicit_derivative_formula
    {alpha xi eta rho dEta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho)
    (hDifferentiated :
      2 * eta / rho
        -
      (gaugeRadialDenominator alpha xi eta rho / rho)
        * dEta
        =
      0) :
    dEta
      =
    2 * eta
      / gaugeRadialDenominator alpha xi eta rho := by
  have hDenominatorPos :
      0 < gaugeRadialDenominator alpha xi eta rho :=
    gaugeRadialDenominator_pos
      halphaOne halphaTwo hrho hEquation

  have hRhoNe : rho ≠ 0 := ne_of_gt hrho
  have hDenominatorNe :
      gaugeRadialDenominator alpha xi eta rho ≠ 0 :=
    ne_of_gt hDenominatorPos

  have hNested :
      dEta
        =
      (2 * eta / rho)
        /
      (gaugeRadialDenominator alpha xi eta rho / rho) := by
    apply
      (eq_div_iff
        (div_ne_zero hDenominatorNe hRhoNe)).2
    calc
      dEta
          * (gaugeRadialDenominator alpha xi eta rho / rho)
          =
        (gaugeRadialDenominator alpha xi eta rho / rho)
          * dEta := by
            ring
      _ = 2 * eta / rho := by
            linarith

  calc
    dEta
        =
      (2 * eta / rho)
        /
      (gaugeRadialDenominator alpha xi eta rho / rho) :=
        hNested
    _ =
      2 * eta
        / gaugeRadialDenominator alpha xi eta rho := by
          field_simp [
            hRhoNe,
            hDenominatorNe
          ]

/--
For the constructed anisotropic gauge, the implicit denominator lies in
`[1,2]` at every nonzero frequency point.
-/
theorem anisotropicGauge_radialDenominator_mem_Icc
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    1 ≤
        gaugeRadialDenominator alpha xi eta
          (anisotropicGauge alpha xi eta)
      ∧
    gaugeRadialDenominator alpha xi eta
        (anisotropicGauge alpha xi eta)
      ≤ 2 := by
  exact
    gaugeRadialDenominator_mem_Icc
      halphaOne
      halphaTwo
      (anisotropicGauge_pos
        halphaOne halphaTwo hnonzero)
      (anisotropicGauge_equation
        halphaOne halphaTwo hnonzero)

/--
For the constructed gauge, the radial derivative of the defining residual is
strictly negative away from the origin.
-/
theorem anisotropicGauge_radialDerivative_neg
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    gaugeRadialDerivative alpha xi eta
        (anisotropicGauge alpha xi eta)
      < 0 := by
  exact
    gaugeRadialDerivative_neg
      halphaOne
      halphaTwo
      (anisotropicGauge_pos
        halphaOne halphaTwo hnonzero)
      (anisotropicGauge_equation
        halphaOne halphaTwo hnonzero)

end GaugeImplicitCore
end DGBOZK
