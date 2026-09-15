/-
# Quantitative assembly for the transverse resonance bound

This module checks the reverse-triangle and error-absorption argument behind

  |Omega| >= (cMinus / 2) N b^2.

The individual longitudinal and transverse component estimates are explicit
hypotheses. Their analytic derivation from the transition-band and sector
conditions is not asserted here.
-/

import DGBOZK.ResonanceTransverseCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/-- The absolute value of a sum of four terms is bounded by the sum of
their individual bounds. -/
theorem abs_sum_four_le
    (x1 x2 x3 x4 B1 B2 B3 B4 : ℝ)
    (h1 : |x1| ≤ B1)
    (h2 : |x2| ≤ B2)
    (h3 : |x3| ≤ B3)
    (h4 : |x4| ≤ B4) :
    |x1 + x2 + x3 + x4| ≤ B1 + B2 + B3 + B4 := by
  have h12 :
      |x1 + x2| ≤ |x1| + |x2| :=
    abs_add x1 x2
  have h123 :
      |x1 + x2 + x3| ≤ |x1 + x2| + |x3| :=
    abs_add (x1 + x2) x3
  have h1234 :
      |x1 + x2 + x3 + x4|
        ≤ |x1 + x2 + x3| + |x4| :=
    abs_add (x1 + x2 + x3) x4
  linarith

/--
Abstract dominant-term absorption.

If `Omega = M + E`, the principal term has size at least `P`, and the
error has size at most `P/2`, then `|Omega| >= P/2`.
-/
theorem dominant_term_absorption
    {M E Omega P : ℝ}
    (hprincipal : P ≤ |M|)
    (herror : |E| ≤ P / 2)
    (hdecomp : Omega = M + E) :
    P / 2 ≤ |Omega| := by
  have hMrep :
      M = Omega + (-E) := by
    rw [hdecomp]
    ring

  have htriangle :
      |M| ≤ |Omega| + |E| := by
    rw [hMrep]
    calc
      |Omega + -E| ≤ |Omega| + |-E| :=
        abs_add Omega (-E)
      _ = |Omega| + |E| := by
        rw [abs_neg]

  linarith

/--
Quantitative lower bound for the transverse resonance from four explicit
component estimates.

The four assumed error bounds correspond respectively to

* the longitudinal phase increment;
* `-2 xi eta b`;
* `-a eta^2`;
* `-2 a eta b`.

The coefficient smallness condition is exactly the absorption requirement.
-/
theorem resonance_lower_bound_of_component_bounds
    {alpha a b xi eta N cMinus : ℝ}
    {eLong eCross eEtaSq eMixed : ℝ}
    (hN : 0 ≤ N)
    (hxi : cMinus * N ≤ |xi|)
    (hLong :
      |longitudinalPart alpha a xi|
        ≤ eLong * (N * b ^ 2))
    (hCross :
      |-(2 * xi * eta * b)|
        ≤ eCross * (N * b ^ 2))
    (hEtaSq :
      |-(a * eta ^ 2)|
        ≤ eEtaSq * (N * b ^ 2))
    (hMixed :
      |-(2 * a * eta * b)|
        ≤ eMixed * (N * b ^ 2))
    (hsmall :
      eLong + eCross + eEtaSq + eMixed
        ≤ cMinus / 2) :
    (cMinus / 2) * N * b ^ 2
      ≤ |resonanceCore alpha a b xi eta| := by
  let P0 : ℝ := N * b ^ 2

  have hP0 :
      0 ≤ P0 := by
    dsimp [P0]
    exact mul_nonneg hN (sq_nonneg b)

  have hsum :
      |longitudinalPart alpha a xi
        + (-(2 * xi * eta * b))
        + (-(a * eta ^ 2))
        + (-(2 * a * eta * b))|
      ≤
        eLong * P0
        + eCross * P0
        + eEtaSq * P0
        + eMixed * P0 := by
    exact abs_sum_four_le
      (longitudinalPart alpha a xi)
      (-(2 * xi * eta * b))
      (-(a * eta ^ 2))
      (-(2 * a * eta * b))
      (eLong * P0)
      (eCross * P0)
      (eEtaSq * P0)
      (eMixed * P0)
      hLong hCross hEtaSq hMixed

  let E : ℝ :=
    longitudinalPart alpha a xi
      + transverseError xi eta a b

  have herror :
      |E|
        ≤ (eLong + eCross + eEtaSq + eMixed) * P0 := by
    calc
      |E| =
          |longitudinalPart alpha a xi
            + (-(2 * xi * eta * b))
            + (-(a * eta ^ 2))
            + (-(2 * a * eta * b))| := by
        dsimp [E]
        unfold transverseError
        congr 1
        ring
      _ ≤
          eLong * P0
            + eCross * P0
            + eEtaSq * P0
            + eMixed * P0 :=
        hsum
      _ =
          (eLong + eCross + eEtaSq + eMixed) * P0 := by
        ring

  have herrorHalf :
      |E| ≤ (cMinus * P0) / 2 := by
    calc
      |E|
          ≤ (eLong + eCross + eEtaSq + eMixed) * P0 :=
        herror
      _ ≤ (cMinus / 2) * P0 :=
        mul_le_mul_of_nonneg_right hsmall hP0
      _ = (cMinus * P0) / 2 := by
        ring

  have hprincipal :
      cMinus * P0 ≤ |-xi * b ^ 2| := by
    dsimp [P0]
    calc
      cMinus * (N * b ^ 2)
          = (cMinus * N) * b ^ 2 := by
        ring
      _ ≤ |xi| * b ^ 2 :=
        mul_le_mul_of_nonneg_right hxi (sq_nonneg b)
      _ = |-xi * b ^ 2| := by
        rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg b)]

  have hdecomp :
      resonanceCore alpha a b xi eta =
        (-xi * b ^ 2) + E := by
    dsimp [E]
    exact resonanceCore_decomposition
      alpha a b xi eta

  have hfinal :
      (cMinus * P0) / 2
        ≤ |resonanceCore alpha a b xi eta| :=
    dominant_term_absorption
      hprincipal herrorHalf hdecomp

  calc
    (cMinus / 2) * N * b ^ 2
        = (cMinus * P0) / 2 := by
      dsimp [P0]
      ring
    _ ≤ |resonanceCore alpha a b xi eta| :=
      hfinal

end ResonanceTransverse
end DGBOZK
