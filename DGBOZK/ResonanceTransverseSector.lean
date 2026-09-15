/-
# Elementary scale consequences of the large-transverse sector

This module formalizes the elementary conversions associated with

  |eta| <= Ceta * mu,
  C1 * mu <= |b|.

These estimates are used in the proof of `lem:resonance-transverse`.
No fractional phase estimate is asserted here.
-/

import DGBOZK.ResonanceTransverseBounds
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK
namespace ResonanceTransverse

/--
The large-transverse condition converts the transition-band bound on `eta`
into a bound relative to `|b|`.
-/
theorem eta_le_ratio_mul_abs_b
    {eta b Ceta C1 mu : ℝ}
    (hCeta : 0 ≤ Ceta)
    (hC1 : 0 < C1)
    (heta : |eta| ≤ Ceta * mu)
    (hb : C1 * mu ≤ |b|) :
    |eta| ≤ (Ceta / C1) * |b| := by
  have hmu :
      mu ≤ |b| / C1 := by
    apply (le_div_iff₀ hC1).2
    simpa [mul_comm] using hb

  calc
    |eta| ≤ Ceta * mu :=
      heta
    _ ≤ Ceta * (|b| / C1) :=
      mul_le_mul_of_nonneg_left hmu hCeta
    _ = (Ceta / C1) * |b| := by
      ring

/--
If `C1 * mu <= |b|`, then one factor of `|b|` may be converted into
`C1 * mu`. This proves the second inequality in
`eq:resonance-transverse`.
-/
theorem transverse_square_controls_linear_scale
    {b cStar C1 N mu : ℝ}
    (hcStar : 0 ≤ cStar)
    (hN : 0 ≤ N)
    (hb : C1 * mu ≤ |b|) :
    cStar * C1 * N * mu * |b|
      ≤ cStar * N * b ^ 2 := by
  have hbnonneg :
      0 ≤ |b| :=
    abs_nonneg b

  have hbase :
      C1 * mu * |b| ≤ |b| * |b| :=
    mul_le_mul_of_nonneg_right hb hbnonneg

  have hfactor :
      0 ≤ cStar * N :=
    mul_nonneg hcStar hN

  have hscaled :
      (cStar * N) * (C1 * mu * |b|)
        ≤ (cStar * N) * (|b| * |b|) :=
    mul_le_mul_of_nonneg_left hbase hfactor

  have hb2 :
      b ^ 2 = |b| * |b| := by
    rw [← sq_abs]
    ring

  calc
    cStar * C1 * N * mu * |b|
        = (cStar * N) * (C1 * mu * |b|) := by
      ring
    _ ≤ (cStar * N) * (|b| * |b|) :=
      hscaled
    _ = cStar * N * b ^ 2 := by
      rw [← hb2]

end ResonanceTransverse
end DGBOZK
