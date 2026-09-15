/-
# Polynomial component bounds in the large-transverse sector

This module derives the three polynomial error estimates used in
`lem:resonance-transverse`. The fractional longitudinal increment is not
treated here and remains an explicit analytic input.
-/

import DGBOZK.ResonanceTransverseSector
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/-- Product comparison for three real factors. -/
theorem abs_mul_three_le
    {x y z X Y Z : ℝ}
    (hx : |x| ≤ X)
    (hy : |y| ≤ Y)
    (hz : |z| ≤ Z)
    (hX : 0 ≤ X)
    (hY : 0 ≤ Y) :
    |x * y * z| ≤ X * Y * Z := by
  have hxy :
      |x| * |y| ≤ X * Y :=
    mul_le_mul hx hy (abs_nonneg y) hX

  have hxyz :
      (|x| * |y|) * |z| ≤ (X * Y) * Z :=
    mul_le_mul hxy hz (abs_nonneg z)
      (mul_nonneg hX hY)

  simpa only [abs_mul] using hxyz

/--
The error `-2 xi eta b` is bounded by
`2 cPlus q N b^2` whenever

  |xi| <= cPlus N,
  |eta| <= q |b|.
-/
theorem cross_error_bound
    {xi eta b cPlus q N : ℝ}
    (hN : 0 ≤ N)
    (hcPlus : 0 ≤ cPlus)
    (hq : 0 ≤ q)
    (hxi : |xi| ≤ cPlus * N)
    (heta : |eta| ≤ q * |b|) :
    |-(2 * xi * eta * b)|
      ≤ (2 * cPlus * q) * (N * b ^ 2) := by
  have hXN :
      0 ≤ cPlus * N :=
    mul_nonneg hcPlus hN

  have hqb :
      0 ≤ q * |b| :=
    mul_nonneg hq (abs_nonneg b)

  have hprod :
      |xi * eta * b|
        ≤ (cPlus * N) * (q * |b|) * |b| :=
    abs_mul_three_le
      hxi heta (le_rfl : |b| ≤ |b|)
      hXN hqb

  have hscaled :
      2 * |xi * eta * b|
        ≤ 2 * ((cPlus * N) * (q * |b|) * |b|) :=
    mul_le_mul_of_nonneg_left hprod
      (by norm_num)

  have hb2 :
      |b| * |b| = b ^ 2 := by
    rw [← sq_abs]
    ring

  calc
    |-(2 * xi * eta * b)|
        = 2 * |xi * eta * b| := by
      simp only [abs_neg, abs_mul]
      norm_num <;> ring
    _ ≤ 2 * ((cPlus * N) * (q * |b|) * |b|) :=
      hscaled
    _ = 2 * cPlus * N * q * (|b| * |b|) := by
      ring
    _ = (2 * cPlus * q) * (N * b ^ 2) := by
      rw [hb2]
      ring

/--
The error `-a eta^2` is bounded by
`eps q^2 N b^2` whenever

  |a| <= eps N,
  |eta| <= q |b|.
-/
theorem eta_square_error_bound
    {a eta b eps q N : ℝ}
    (hN : 0 ≤ N)
    (heps : 0 ≤ eps)
    (hq : 0 ≤ q)
    (ha : |a| ≤ eps * N)
    (heta : |eta| ≤ q * |b|) :
    |-(a * eta ^ 2)|
      ≤ (eps * q ^ 2) * (N * b ^ 2) := by
  have hepsN :
      0 ≤ eps * N :=
    mul_nonneg heps hN

  have hqb :
      0 ≤ q * |b| :=
    mul_nonneg hq (abs_nonneg b)

  have hprod :
      |a * eta * eta|
        ≤ (eps * N) * (q * |b|) * (q * |b|) :=
    abs_mul_three_le
      ha heta heta hepsN hqb

  have hb2 :
      |b| * |b| = b ^ 2 := by
    rw [← sq_abs]
    ring

  calc
    |-(a * eta ^ 2)|
        = |a * eta * eta| := by
      simp only [abs_neg, pow_two]
      ring
    _ ≤ (eps * N) * (q * |b|) * (q * |b|) :=
      hprod
    _ = eps * N * q ^ 2 * (|b| * |b|) := by
      ring
    _ = (eps * q ^ 2) * (N * b ^ 2) := by
      rw [hb2]
      ring

/--
The error `-2 a eta b` is bounded by
`2 eps q N b^2` whenever

  |a| <= eps N,
  |eta| <= q |b|.
-/
theorem mixed_error_bound
    {a eta b eps q N : ℝ}
    (hN : 0 ≤ N)
    (heps : 0 ≤ eps)
    (hq : 0 ≤ q)
    (ha : |a| ≤ eps * N)
    (heta : |eta| ≤ q * |b|) :
    |-(2 * a * eta * b)|
      ≤ (2 * eps * q) * (N * b ^ 2) := by
  have hepsN :
      0 ≤ eps * N :=
    mul_nonneg heps hN

  have hqb :
      0 ≤ q * |b| :=
    mul_nonneg hq (abs_nonneg b)

  have hprod :
      |a * eta * b|
        ≤ (eps * N) * (q * |b|) * |b| :=
    abs_mul_three_le
      ha heta (le_rfl : |b| ≤ |b|)
      hepsN hqb

  have hscaled :
      2 * |a * eta * b|
        ≤ 2 * ((eps * N) * (q * |b|) * |b|) :=
    mul_le_mul_of_nonneg_left hprod
      (by norm_num)

  have hb2 :
      |b| * |b| = b ^ 2 := by
    rw [← sq_abs]
    ring

  calc
    |-(2 * a * eta * b)|
        = 2 * |a * eta * b| := by
      simp only [abs_neg, abs_mul]
      norm_num <;> ring
    _ ≤ 2 * ((eps * N) * (q * |b|) * |b|) :=
      hscaled
    _ = 2 * eps * N * q * (|b| * |b|) := by
      ring
    _ = (2 * eps * q) * (N * b ^ 2) := by
      rw [hb2]
      ring

end ResonanceTransverse
end DGBOZK
