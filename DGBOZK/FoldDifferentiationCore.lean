/-
# Genuine derivatives of the reduced fold phase

For the reduced phase

  Psi(xi) = x xi + t xi^(alpha+1) - y^2 / (4 t xi),

this module defines the actual first-derivative expression `Psi1` and proves,
on `xi > 0` and `t != 0`, the derivative chain

  Psi  -->  Psi1  -->  Psi2  -->  Psi3.

Thus the formulas called `Psi2` and `Psi3` in `Fold.lean` are no longer
differentiation black boxes.
-/

import DGBOZK.Fold
import DGBOZK.PhaseLongitudinalDifferentiationCore
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace FoldDifferentiationCore

open PhaseLongitudinalDifferentiationCore

/--
The first derivative expression for the reduced phase.
-/
noncomputable def Psi1
    (alpha x y t xi : ℝ) : ℝ :=
  x
    + t * (alpha + 1) * xi ^ alpha
    + y ^ 2 / (4 * t * xi ^ 2)

/--
Derivative of the real power `xi^(alpha+1)` on the positive half-line.
-/
theorem hasDerivAt_rpow_add_one_of_pos
    {alpha xi : ℝ}
    (hxi : 0 < xi) :
    HasDerivAt
      (fun xiVariable : ℝ =>
        xiVariable ^ (alpha + 1))
      ((alpha + 1) * xi ^ alpha)
      xi := by
  have h :=
    hasDerivAt_positive_rpow
      (alpha := alpha + 1)
      hxi
  have hexponent :
      alpha + 1 - 1 = alpha := by
    ring
  rw [hexponent] at h
  exact h

/--
Derivative of `xi^(alpha-1)` on the positive half-line.
-/
theorem hasDerivAt_rpow_sub_one_of_pos
    {alpha xi : ℝ}
    (hxi : 0 < xi) :
    HasDerivAt
      (fun xiVariable : ℝ =>
        xiVariable ^ (alpha - 1))
      ((alpha - 1) * xi ^ (alpha - 2))
      xi := by
  have h :=
    hasDerivAt_positive_rpow
      (alpha := alpha - 1)
      hxi
  have hexponent :
      alpha - 1 - 1 = alpha - 2 := by
    ring
  rw [hexponent] at h
  exact h

/--
The displayed expression `Psi1` is the genuine first derivative of `Psi`.
-/
theorem hasDerivAt_Psi
    {alpha x y t xi : ℝ}
    (hxi : 0 < xi)
    (ht : t ≠ 0) :
    HasDerivAt
      (fun xiVariable =>
        Psi alpha x y t xiVariable)
      (Psi1 alpha x y t xi)
      xi := by
  have hxiNe : xi ≠ 0 :=
    ne_of_gt hxi

  have hLinear :
      HasDerivAt
        (fun xiVariable : ℝ =>
          x * xiVariable)
        x
        xi := by
    simpa using
      (hasDerivAt_id xi).const_mul x

  have hPower :
      HasDerivAt
        (fun xiVariable : ℝ =>
          xiVariable ^ (alpha + 1))
        ((alpha + 1) * xi ^ alpha)
        xi :=
    hasDerivAt_rpow_add_one_of_pos hxi

  have hDispersive :
      HasDerivAt
        (fun xiVariable : ℝ =>
          t * xiVariable ^ (alpha + 1))
        (t * ((alpha + 1) * xi ^ alpha))
        xi :=
    hPower.const_mul t

  have hNumerator :
      HasDerivAt
        (fun _xiVariable : ℝ =>
          y ^ 2)
        0
        xi :=
    hasDerivAt_const xi (y ^ 2)

  have hDenominator :
      HasDerivAt
        (fun xiVariable : ℝ =>
          4 * t * xiVariable)
        (4 * t)
        xi := by
    simpa using
      (hasDerivAt_id xi).const_mul (4 * t)

  have hDenominatorNe :
      4 * t * xi ≠ 0 := by
    exact
      mul_ne_zero
        (mul_ne_zero (by norm_num) ht)
        hxiNe

  have hQuotient :
      HasDerivAt
        (fun xiVariable : ℝ =>
          y ^ 2 / (4 * t * xiVariable))
        ((0 * (4 * t * xi)
            - y ^ 2 * (4 * t))
          / (4 * t * xi) ^ 2)
        xi :=
    hNumerator.div
      hDenominator
      hDenominatorNe

  have hRaw :
      HasDerivAt
        (fun xiVariable : ℝ =>
          x * xiVariable
            + t * xiVariable ^ (alpha + 1)
            - y ^ 2 / (4 * t * xiVariable))
        (x
          + t * ((alpha + 1) * xi ^ alpha)
          -
          ((0 * (4 * t * xi)
              - y ^ 2 * (4 * t))
            / (4 * t * xi) ^ 2))
        xi :=
    (hLinear.add hDispersive).sub hQuotient

  have hCoefficient :
      x
          + t * ((alpha + 1) * xi ^ alpha)
          -
          ((0 * (4 * t * xi)
              - y ^ 2 * (4 * t))
            / (4 * t * xi) ^ 2)
        =
      Psi1 alpha x y t xi := by
    unfold Psi1
    field_simp [ht, hxiNe]
    ring

  rw [hCoefficient] at hRaw
  simpa [Psi] using hRaw

/--
The displayed expression `Psi2` is the genuine derivative of `Psi1`.
-/
theorem hasDerivAt_Psi1
    {alpha x y t xi : ℝ}
    (hxi : 0 < xi)
    (ht : t ≠ 0) :
    HasDerivAt
      (fun xiVariable =>
        Psi1 alpha x y t xiVariable)
      (Psi2 alpha y t xi)
      xi := by
  have hxiNe : xi ≠ 0 :=
    ne_of_gt hxi

  have hConstant :
      HasDerivAt
        (fun _xiVariable : ℝ => x)
        0
        xi :=
    hasDerivAt_const xi x

  have hPower :
      HasDerivAt
        (fun xiVariable : ℝ =>
          xiVariable ^ alpha)
        (alpha * xi ^ (alpha - 1))
        xi :=
    hasDerivAt_positive_rpow hxi

  have hDispersive :
      HasDerivAt
        (fun xiVariable : ℝ =>
          (t * (alpha + 1))
            * xiVariable ^ alpha)
        ((t * (alpha + 1))
          * (alpha * xi ^ (alpha - 1)))
        xi :=
    hPower.const_mul (t * (alpha + 1))

  have hSquare :
      HasDerivAt
        (fun xiVariable : ℝ =>
          xiVariable ^ (2 : ℕ))
        (2 * xi)
        xi := by
    convert
      (hasDerivAt_id xi).pow 2
      using 1 <;>
      norm_num <;>
      ring

  have hDenominator :
      HasDerivAt
        (fun xiVariable : ℝ =>
          4 * t * xiVariable ^ (2 : ℕ))
        ((4 * t) * (2 * xi))
        xi :=
    hSquare.const_mul (4 * t)

  have hNumerator :
      HasDerivAt
        (fun _xiVariable : ℝ =>
          y ^ 2)
        0
        xi :=
    hasDerivAt_const xi (y ^ 2)

  have hDenominatorNe :
      4 * t * xi ^ (2 : ℕ) ≠ 0 := by
    exact
      mul_ne_zero
        (mul_ne_zero (by norm_num) ht)
        (pow_ne_zero 2 hxiNe)

  have hQuotient :
      HasDerivAt
        (fun xiVariable : ℝ =>
          y ^ 2
            / (4 * t * xiVariable ^ (2 : ℕ)))
        ((0 * (4 * t * xi ^ (2 : ℕ))
            - y ^ 2 * ((4 * t) * (2 * xi)))
          / (4 * t * xi ^ (2 : ℕ)) ^ 2)
        xi :=
    hNumerator.div
      hDenominator
      hDenominatorNe

  have hRaw :
      HasDerivAt
        (fun xiVariable : ℝ =>
          x
            + (t * (alpha + 1))
                * xiVariable ^ alpha
            + y ^ 2
                / (4 * t * xiVariable ^ (2 : ℕ)))
        (0
          + (t * (alpha + 1))
              * (alpha * xi ^ (alpha - 1))
          +
          ((0 * (4 * t * xi ^ (2 : ℕ))
              - y ^ 2 * ((4 * t) * (2 * xi)))
            / (4 * t * xi ^ (2 : ℕ)) ^ 2))
        xi :=
    (hConstant.add hDispersive).add hQuotient

  have hCoefficient :
      0
          + (t * (alpha + 1))
              * (alpha * xi ^ (alpha - 1))
          +
          ((0 * (4 * t * xi ^ (2 : ℕ))
              - y ^ 2 * ((4 * t) * (2 * xi)))
            / (4 * t * xi ^ (2 : ℕ)) ^ 2)
        =
      Psi2 alpha y t xi := by
    unfold Psi2
    field_simp [ht, hxiNe]
    ring

  rw [hCoefficient] at hRaw
  simpa [Psi1] using hRaw

/--
The displayed expression `Psi3` is the genuine derivative of `Psi2`.
-/
theorem hasDerivAt_Psi2
    {alpha y t xi : ℝ}
    (hxi : 0 < xi)
    (ht : t ≠ 0) :
    HasDerivAt
      (fun xiVariable =>
        Psi2 alpha y t xiVariable)
      (Psi3 alpha y t xi)
      xi := by
  have hxiNe : xi ≠ 0 :=
    ne_of_gt hxi

  have hPower :
      HasDerivAt
        (fun xiVariable : ℝ =>
          xiVariable ^ (alpha - 1))
        ((alpha - 1) * xi ^ (alpha - 2))
        xi :=
    hasDerivAt_rpow_sub_one_of_pos hxi

  have hDispersive :
      HasDerivAt
        (fun xiVariable : ℝ =>
          (t * (alpha * (alpha + 1)))
            * xiVariable ^ (alpha - 1))
        ((t * (alpha * (alpha + 1)))
          * ((alpha - 1) * xi ^ (alpha - 2)))
        xi :=
    hPower.const_mul
      (t * (alpha * (alpha + 1)))

  have hCube :
      HasDerivAt
        (fun xiVariable : ℝ =>
          xiVariable ^ (3 : ℕ))
        (3 * xi ^ (2 : ℕ))
        xi := by
    convert
      (hasDerivAt_id xi).pow 3
      using 1 <;>
      norm_num <;>
      ring

  have hDenominator :
      HasDerivAt
        (fun xiVariable : ℝ =>
          2 * t * xiVariable ^ (3 : ℕ))
        ((2 * t) * (3 * xi ^ (2 : ℕ)))
        xi :=
    hCube.const_mul (2 * t)

  have hNumerator :
      HasDerivAt
        (fun _xiVariable : ℝ =>
          y ^ 2)
        0
        xi :=
    hasDerivAt_const xi (y ^ 2)

  have hDenominatorNe :
      2 * t * xi ^ (3 : ℕ) ≠ 0 := by
    exact
      mul_ne_zero
        (mul_ne_zero (by norm_num) ht)
        (pow_ne_zero 3 hxiNe)

  have hQuotient :
      HasDerivAt
        (fun xiVariable : ℝ =>
          y ^ 2
            / (2 * t * xiVariable ^ (3 : ℕ)))
        ((0 * (2 * t * xi ^ (3 : ℕ))
            - y ^ 2
                * ((2 * t) * (3 * xi ^ (2 : ℕ))))
          / (2 * t * xi ^ (3 : ℕ)) ^ 2)
        xi :=
    hNumerator.div
      hDenominator
      hDenominatorNe

  have hRaw :
      HasDerivAt
        (fun xiVariable : ℝ =>
          (t * (alpha * (alpha + 1)))
              * xiVariable ^ (alpha - 1)
            - y ^ 2
                / (2 * t * xiVariable ^ (3 : ℕ)))
        ((t * (alpha * (alpha + 1)))
            * ((alpha - 1) * xi ^ (alpha - 2))
          -
          ((0 * (2 * t * xi ^ (3 : ℕ))
              - y ^ 2
                  * ((2 * t) * (3 * xi ^ (2 : ℕ))))
            / (2 * t * xi ^ (3 : ℕ)) ^ 2))
        xi :=
    hDispersive.sub hQuotient

  have hCoefficient :
      (t * (alpha * (alpha + 1)))
            * ((alpha - 1) * xi ^ (alpha - 2))
          -
          ((0 * (2 * t * xi ^ (3 : ℕ))
              - y ^ 2
                  * ((2 * t) * (3 * xi ^ (2 : ℕ))))
            / (2 * t * xi ^ (3 : ℕ)) ^ 2)
        =
      Psi3 alpha y t xi := by
    unfold Psi3
    field_simp [ht, hxiNe]
    ring

  rw [hCoefficient] at hRaw
  simpa [Psi2] using hRaw

/-- The Lean derivative of `Psi` equals `Psi1`. -/
theorem deriv_Psi_eq_Psi1
    {alpha x y t xi : ℝ}
    (hxi : 0 < xi)
    (ht : t ≠ 0) :
    deriv
        (fun xiVariable =>
          Psi alpha x y t xiVariable)
        xi
      =
    Psi1 alpha x y t xi :=
  (hasDerivAt_Psi hxi ht).deriv

/-- The Lean derivative of `Psi1` equals `Psi2`. -/
theorem deriv_Psi1_eq_Psi2
    {alpha x y t xi : ℝ}
    (hxi : 0 < xi)
    (ht : t ≠ 0) :
    deriv
        (fun xiVariable =>
          Psi1 alpha x y t xiVariable)
        xi
      =
    Psi2 alpha y t xi :=
  (hasDerivAt_Psi1 hxi ht).deriv

/-- The Lean derivative of `Psi2` equals `Psi3`. -/
theorem deriv_Psi2_eq_Psi3
    {alpha y t xi : ℝ}
    (hxi : 0 < xi)
    (ht : t ≠ 0) :
    deriv
        (fun xiVariable =>
          Psi2 alpha y t xiVariable)
        xi
      =
    Psi3 alpha y t xi :=
  (hasDerivAt_Psi2 hxi ht).deriv

end FoldDifferentiationCore
end DGBOZK
