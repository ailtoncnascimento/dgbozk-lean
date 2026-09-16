import DGBOZK.Foundations.Coordinates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Anisotropic Littlewood--Paley geometry

This file formalizes the frequency regions underlying the DGBOZK dyadic
decomposition. The anisotropic symbol is rho_alpha(xi, eta) =
|xi| ^ alpha + eta ^ 2.

The definitions below deliberately separate the geometry of the dyadic
regions from the later analytic construction of smooth Fourier multipliers.
No partition of unity or Lp multiplier estimate is asserted here.
-/

open Set

namespace DGBOZK
namespace Foundations

/-- Frequencies with anisotropic size at most H. -/
def lowFrequencyRegion (alpha H : ℝ) : Set FrequencySpace :=
  {zeta | anisotropicSymbol alpha zeta ≤ H}

/-- The closed anisotropic annulus H / 2 ≤ rho_alpha ≤ 2 H. -/
def dyadicAnnulus (alpha H : ℝ) : Set FrequencySpace :=
  {zeta | H / 2 ≤ anisotropicSymbol alpha zeta ∧
    anisotropicSymbol alpha zeta ≤ 2 * H}

@[simp] theorem mem_lowFrequencyRegion
    (alpha H : ℝ) (zeta : FrequencySpace) :
    zeta ∈ lowFrequencyRegion alpha H ↔
      anisotropicSymbol alpha zeta ≤ H :=
  Iff.rfl

@[simp] theorem mem_dyadicAnnulus
    (alpha H : ℝ) (zeta : FrequencySpace) :
    zeta ∈ dyadicAnnulus alpha H ↔
      H / 2 ≤ anisotropicSymbol alpha zeta ∧
        anisotropicSymbol alpha zeta ≤ 2 * H :=
  Iff.rfl

/-- Low-frequency regions increase with the cutoff scale. -/
theorem lowFrequencyRegion_mono
    {alpha H K : ℝ} (hHK : H ≤ K) :
    lowFrequencyRegion alpha H ⊆ lowFrequencyRegion alpha K := by
  intro zeta hzeta
  exact hzeta.trans hHK

/-- Every H-annulus is contained in the low-frequency region at scale 2H. -/
theorem dyadicAnnulus_subset_lowFrequencyRegion
    (alpha H : ℝ) :
    dyadicAnnulus alpha H ⊆ lowFrequencyRegion alpha (2 * H) := by
  intro zeta hzeta
  exact hzeta.2

/-- A nonempty dyadic annulus necessarily has nonnegative scale. -/
theorem dyadicAnnulus_scale_nonneg
    {alpha H : ℝ} {zeta : FrequencySpace}
    (hzeta : zeta ∈ dyadicAnnulus alpha H) :
    0 ≤ H := by
  have hrho : 0 ≤ anisotropicSymbol alpha zeta :=
    anisotropicSymbol_nonneg alpha zeta
  nlinarith [hzeta.2]

/-- The longitudinal part of the symbol is bounded by the full symbol. -/
theorem xiPower_le_anisotropicSymbol
    (alpha : ℝ) (zeta : FrequencySpace) :
    |xiCoord zeta| ^ alpha ≤ anisotropicSymbol alpha zeta := by
  unfold anisotropicSymbol
  exact le_add_of_nonneg_right (sq_nonneg (etaCoord zeta))

/-- The transverse part of the symbol is bounded by the full symbol. -/
theorem etaSq_le_anisotropicSymbol
    (alpha : ℝ) (zeta : FrequencySpace) :
    etaCoord zeta ^ 2 ≤ anisotropicSymbol alpha zeta := by
  unfold anisotropicSymbol
  exact le_add_of_nonneg_left
    (Real.rpow_nonneg (abs_nonneg (xiCoord zeta)) alpha)

theorem xiPower_le_of_mem_lowFrequencyRegion
    {alpha H : ℝ} {zeta : FrequencySpace}
    (hzeta : zeta ∈ lowFrequencyRegion alpha H) :
    |xiCoord zeta| ^ alpha ≤ H :=
  (xiPower_le_anisotropicSymbol alpha zeta).trans hzeta

theorem etaSq_le_of_mem_lowFrequencyRegion
    {alpha H : ℝ} {zeta : FrequencySpace}
    (hzeta : zeta ∈ lowFrequencyRegion alpha H) :
    etaCoord zeta ^ 2 ≤ H :=
  (etaSq_le_anisotropicSymbol alpha zeta).trans hzeta

theorem xiPower_le_of_mem_dyadicAnnulus
    {alpha H : ℝ} {zeta : FrequencySpace}
    (hzeta : zeta ∈ dyadicAnnulus alpha H) :
    |xiCoord zeta| ^ alpha ≤ 2 * H :=
  (xiPower_le_anisotropicSymbol alpha zeta).trans hzeta.2

theorem etaSq_le_of_mem_dyadicAnnulus
    {alpha H : ℝ} {zeta : FrequencySpace}
    (hzeta : zeta ∈ dyadicAnnulus alpha H) :
    etaCoord zeta ^ 2 ≤ 2 * H :=
  (etaSq_le_anisotropicSymbol alpha zeta).trans hzeta.2

/-- The high-frequency dyadic scales used in the manuscript. -/
def dyadicScale (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k

theorem dyadicScale_pos (k : ℕ) :
    0 < dyadicScale k := by
  exact pow_pos (by norm_num) k

@[simp] theorem dyadicScale_zero :
    dyadicScale 0 = 1 := by
  simp [dyadicScale]

theorem dyadicScale_succ (k : ℕ) :
    dyadicScale (k + 1) = 2 * dyadicScale k := by
  simp [dyadicScale, pow_succ, mul_comm]

end Foundations
end DGBOZK
