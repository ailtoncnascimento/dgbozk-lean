/-
# Uniqueness of the positive anisotropic-gauge root

For `alpha > 0`, this module proves that the equation

  xi^2 / rho^(2 / alpha) + eta^2 / rho = 1

has at most one positive solution `rho`.

The proof separates the axis `xi = 0` from the case `xi != 0`. Off that
axis, the longitudinal normalized term is strictly decreasing in `rho`,
while the transverse term is nonincreasing.

Existence and smooth dependence of the root are not claimed here.
-/

import DGBOZK.GaugeUpperEquivalenceCore

set_option autoImplicit false

namespace DGBOZK
namespace GaugeUniquenessCore

open GaugeEquationCore

/--
When `xi` is nonzero, the left side of the gauge equation strictly decreases
as the positive radial variable increases.
-/
theorem gauge_sum_strict_decrease_of_x_ne_zero
    {alpha xi eta rhoOne rhoTwo : ℝ}
    (halpha : 0 < alpha)
    (hrhoOne : 0 < rhoOne)
    (hxi : xi ≠ 0)
    (hrho : rhoOne < rhoTwo) :
    xi ^ 2 / rhoTwo ^ (2 / alpha)
          + eta ^ 2 / rhoTwo
      <
    xi ^ 2 / rhoOne ^ (2 / alpha)
          + eta ^ 2 / rhoOne := by
  have hExponent :
      0 < 2 / alpha := by
    exact div_pos (by norm_num) halpha
  have hRpowStrict :
      rhoOne ^ (2 / alpha)
        < rhoTwo ^ (2 / alpha) :=
    Real.rpow_lt_rpow
      (le_of_lt hrhoOne)
      hrho
      hExponent
  have hRpowOnePos :
      0 < rhoOne ^ (2 / alpha) :=
    Real.rpow_pos_of_pos hrhoOne _
  have hxSquarePos :
      0 < xi ^ 2 :=
    sq_pos_of_ne_zero hxi
  have hxStrict :
      xi ^ 2 / rhoTwo ^ (2 / alpha)
        <
      xi ^ 2 / rhoOne ^ (2 / alpha) :=
    div_lt_div_of_pos_left
      hxSquarePos
      hRpowOnePos
      hRpowStrict
  have hetaWeak :
      eta ^ 2 / rhoTwo
        ≤ eta ^ 2 / rhoOne :=
    div_le_div_of_nonneg_left
      (sq_nonneg eta)
      hrhoOne
      (le_of_lt hrho)
  linarith

/--
On the transverse axis `xi = 0`, every positive solution is `eta^2`.
-/
theorem positive_root_eq_y_square_of_x_eq_zero
    {alpha xi eta rho : ℝ}
    (hrho : 0 < rho)
    (hxi : xi = 0)
    (hEquation : gaugeEquation alpha xi eta rho) :
    rho = eta ^ 2 := by
  subst xi
  have hReduced :
      eta ^ 2 / rho = 1 := by
    simpa [gaugeEquation] using hEquation
  have heta :
      eta ^ 2 = rho :=
    (div_eq_one_iff_eq (ne_of_gt hrho)).mp hReduced
  exact heta.symm

/--
The defining equation has at most one positive root.
-/
theorem positive_root_unique
    {alpha xi eta rhoOne rhoTwo : ℝ}
    (halpha : 0 < alpha)
    (hrhoOne : 0 < rhoOne)
    (hrhoTwo : 0 < rhoTwo)
    (hEquationOne :
      gaugeEquation alpha xi eta rhoOne)
    (hEquationTwo :
      gaugeEquation alpha xi eta rhoTwo) :
    rhoOne = rhoTwo := by
  by_cases hxi : xi = 0
  · calc
      rhoOne = eta ^ 2 :=
        positive_root_eq_y_square_of_x_eq_zero
          hrhoOne hxi hEquationOne
      _ = rhoTwo := by
        symm
        exact
          positive_root_eq_y_square_of_x_eq_zero
            hrhoTwo hxi hEquationTwo
  · apply le_antisymm
    · by_contra hnot
      have hlt : rhoTwo < rhoOne :=
        lt_of_not_ge hnot
      have hStrict :=
        gauge_sum_strict_decrease_of_x_ne_zero
          (eta := eta)
          halpha hrhoTwo hxi hlt
      have hOne :
          xi ^ 2 / rhoOne ^ (2 / alpha)
                + eta ^ 2 / rhoOne
            = 1 :=
        hEquationOne
      have hTwo :
          xi ^ 2 / rhoTwo ^ (2 / alpha)
                + eta ^ 2 / rhoTwo
            = 1 :=
        hEquationTwo
      linarith
    · by_contra hnot
      have hlt : rhoOne < rhoTwo :=
        lt_of_not_ge hnot
      have hStrict :=
        gauge_sum_strict_decrease_of_x_ne_zero
          (eta := eta)
          halpha hrhoOne hxi hlt
      have hOne :
          xi ^ 2 / rhoOne ^ (2 / alpha)
                + eta ^ 2 / rhoOne
            = 1 :=
        hEquationOne
      have hTwo :
          xi ^ 2 / rhoTwo ^ (2 / alpha)
                + eta ^ 2 / rhoTwo
            = 1 :=
        hEquationTwo
      linarith

end GaugeUniquenessCore
end DGBOZK
