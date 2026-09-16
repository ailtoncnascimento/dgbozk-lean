import DGBOZK.Foundations.LittlewoodPaley
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth scalar cutoffs for anisotropic Littlewood--Paley symbols

This file separates two logically different ingredients:

* a one-dimensional smooth cutoff profile;
* the anisotropic frequency symbols obtained by composing that profile with
  rho_alpha.

The structure records the exact support and range properties needed below.
It does not assert that the composed anisotropic symbol is globally smooth:
for nonintegral alpha, this requires a separate argument near xi = 0.
No Fourier multiplier or Lp estimate is claimed in this file.
-/

open Set
open scoped BigOperators

namespace DGBOZK
namespace Foundations
noncomputable section

/-- A smooth real cutoff equal to one on (-infinity, 1] and zero on [2, infinity). -/
structure SmoothCutoffProfile where
  toFun : ℝ → ℝ
  contDiff_toFun : ContDiff ℝ (↑(⊤ : ℕ∞)) toFun
  eq_one_of_le_one : ∀ {s : ℝ}, s ≤ 1 → toFun s = 1
  eq_zero_of_two_le : ∀ {s : ℝ}, 2 ≤ s → toFun s = 0
  nonneg : ∀ s : ℝ, 0 ≤ toFun s
  le_one : ∀ s : ℝ, toFun s ≤ 1

instance : CoeFun SmoothCutoffProfile (fun _ => ℝ → ℝ) :=
  ⟨SmoothCutoffProfile.toFun⟩

/-- The low-pass symbol chi(rho_alpha / H). -/
def lowPassSymbol
    (chi : SmoothCutoffProfile) (alpha H : ℝ)
    (zeta : FrequencySpace) : ℝ :=
  chi (anisotropicSymbol alpha zeta / H)

/-- The band-pass symbol chi(rho_alpha / H) - chi(rho_alpha / (H / 2)). -/
def bandPassSymbol
    (chi : SmoothCutoffProfile) (alpha H : ℝ)
    (zeta : FrequencySpace) : ℝ :=
  lowPassSymbol chi alpha H zeta -
    lowPassSymbol chi alpha (H / 2) zeta

/-- Frequencies where the band-pass symbol is nonzero. -/
def bandPassActiveSet
    (chi : SmoothCutoffProfile) (alpha H : ℝ) :
    Set FrequencySpace :=
  {zeta | bandPassSymbol chi alpha H zeta ≠ 0}

@[simp] theorem mem_bandPassActiveSet
    (chi : SmoothCutoffProfile) (alpha H : ℝ)
    (zeta : FrequencySpace) :
    zeta ∈ bandPassActiveSet chi alpha H ↔
      bandPassSymbol chi alpha H zeta ≠ 0 :=
  Iff.rfl

theorem lowPassSymbol_nonneg
    (chi : SmoothCutoffProfile) (alpha H : ℝ)
    (zeta : FrequencySpace) :
    0 ≤ lowPassSymbol chi alpha H zeta :=
  chi.nonneg _

theorem lowPassSymbol_le_one
    (chi : SmoothCutoffProfile) (alpha H : ℝ)
    (zeta : FrequencySpace) :
    lowPassSymbol chi alpha H zeta ≤ 1 :=
  chi.le_one _

theorem lowPassSymbol_eq_one_of_le
    (chi : SmoothCutoffProfile) {alpha H : ℝ}
    {zeta : FrequencySpace} (hH : 0 < H)
    (hzeta : anisotropicSymbol alpha zeta ≤ H) :
    lowPassSymbol chi alpha H zeta = 1 := by
  apply chi.eq_one_of_le_one
  exact (div_le_iff₀ hH).2 (by simpa using hzeta)

theorem lowPassSymbol_eq_zero_of_two_le
    (chi : SmoothCutoffProfile) {alpha H : ℝ}
    {zeta : FrequencySpace} (hH : 0 < H)
    (hzeta : 2 * H ≤ anisotropicSymbol alpha zeta) :
    lowPassSymbol chi alpha H zeta = 0 := by
  apply chi.eq_zero_of_two_le
  exact (le_div_iff₀ hH).2 hzeta

theorem bandPassSymbol_eq_zero_of_le
    (chi : SmoothCutoffProfile) {alpha H : ℝ}
    {zeta : FrequencySpace} (hH : 0 < H)
    (hzeta : anisotropicSymbol alpha zeta ≤ H / 2) :
    bandPassSymbol chi alpha H zeta = 0 := by
  have hHhalf : 0 < H / 2 := by linarith
  have hzetaH : anisotropicSymbol alpha zeta ≤ H := by linarith
  unfold bandPassSymbol
  rw [lowPassSymbol_eq_one_of_le chi hH hzetaH]
  rw [lowPassSymbol_eq_one_of_le chi hHhalf hzeta]
  norm_num

theorem bandPassSymbol_eq_zero_of_two_le
    (chi : SmoothCutoffProfile) {alpha H : ℝ}
    {zeta : FrequencySpace} (hH : 0 < H)
    (hzeta : 2 * H ≤ anisotropicSymbol alpha zeta) :
    bandPassSymbol chi alpha H zeta = 0 := by
  have hHhalf : 0 < H / 2 := by linarith
  have hzetaHalf :
      2 * (H / 2) ≤ anisotropicSymbol alpha zeta := by
    linarith
  unfold bandPassSymbol
  rw [lowPassSymbol_eq_zero_of_two_le chi hH hzeta]
  rw [lowPassSymbol_eq_zero_of_two_le chi hHhalf hzetaHalf]
  norm_num

/-- Nonzero band-pass symbols are confined to the closed dyadic annulus. -/
theorem bandPassActiveSet_subset_dyadicAnnulus
    (chi : SmoothCutoffProfile) {alpha H : ℝ}
    (hH : 0 < H) :
    bandPassActiveSet chi alpha H ⊆ dyadicAnnulus alpha H := by
  intro zeta hzeta
  constructor
  · have hnot :
        ¬ anisotropicSymbol alpha zeta ≤ H / 2 := by
      intro hlow
      exact hzeta (bandPassSymbol_eq_zero_of_le chi hH hlow)
    exact (lt_of_not_ge hnot).le
  · have hnot :
        ¬ 2 * H ≤ anisotropicSymbol alpha zeta := by
      intro hhigh
      exact hzeta (bandPassSymbol_eq_zero_of_two_le chi hH hhigh)
    exact (lt_of_not_ge hnot).le

theorem bandPassSymbol_le_one
    (chi : SmoothCutoffProfile) (alpha H : ℝ)
    (zeta : FrequencySpace) :
    bandPassSymbol chi alpha H zeta ≤ 1 := by
  have hleft :=
    chi.le_one (anisotropicSymbol alpha zeta / H)
  have hright :=
    chi.nonneg (anisotropicSymbol alpha zeta / (H / 2))
  unfold bandPassSymbol lowPassSymbol
  linarith

theorem neg_one_le_bandPassSymbol
    (chi : SmoothCutoffProfile) (alpha H : ℝ)
    (zeta : FrequencySpace) :
    -1 ≤ bandPassSymbol chi alpha H zeta := by
  have hleft :=
    chi.nonneg (anisotropicSymbol alpha zeta / H)
  have hright :=
    chi.le_one (anisotropicSymbol alpha zeta / (H / 2))
  unfold bandPassSymbol lowPassSymbol
  linarith

/-- The low-pass symbol at the kth dyadic scale. -/
def dyadicLowPassSymbol
    (chi : SmoothCutoffProfile) (alpha : ℝ) (k : ℕ)
    (zeta : FrequencySpace) : ℝ :=
  lowPassSymbol chi alpha (dyadicScale k) zeta

/-- The difference of two consecutive dyadic low-pass symbols. -/
def dyadicBandSymbol
    (chi : SmoothCutoffProfile) (alpha : ℝ) (k : ℕ)
    (zeta : FrequencySpace) : ℝ :=
  dyadicLowPassSymbol chi alpha (k + 1) zeta -
    dyadicLowPassSymbol chi alpha k zeta

theorem dyadicBandSymbol_eq_bandPassSymbol
    (chi : SmoothCutoffProfile) (alpha : ℝ) (k : ℕ)
    (zeta : FrequencySpace) :
    dyadicBandSymbol chi alpha k zeta =
      bandPassSymbol chi alpha (dyadicScale (k + 1)) zeta := by
  have hscale :
      dyadicScale (k + 1) / 2 = dyadicScale k := by
    rw [dyadicScale_succ]
    ring
  unfold dyadicBandSymbol dyadicLowPassSymbol bandPassSymbol
  rw [hscale]

/-- Consecutive dyadic differences telescope exactly. -/
theorem sum_dyadicBandSymbol
    (chi : SmoothCutoffProfile) (alpha : ℝ)
    (n : ℕ) (zeta : FrequencySpace) :
    Finset.sum (Finset.range n) (fun k => dyadicBandSymbol chi alpha k zeta) =
      dyadicLowPassSymbol chi alpha n zeta -
        dyadicLowPassSymbol chi alpha 0 zeta := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold dyadicBandSymbol
      ring

/-- Each dyadic difference is supported in its expected anisotropic annulus. -/
theorem dyadicBandActive_subset_dyadicAnnulus
    (chi : SmoothCutoffProfile) (alpha : ℝ) (k : ℕ) :
    {zeta | dyadicBandSymbol chi alpha k zeta ≠ 0} ⊆
      dyadicAnnulus alpha (dyadicScale (k + 1)) := by
  intro zeta hzeta
  apply bandPassActiveSet_subset_dyadicAnnulus chi
    (dyadicScale_pos (k + 1))
  change bandPassSymbol chi alpha (dyadicScale (k + 1)) zeta ≠ 0
  rwa [← dyadicBandSymbol_eq_bandPassSymbol]

end
end Foundations
end DGBOZK
