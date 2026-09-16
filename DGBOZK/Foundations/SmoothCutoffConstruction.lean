import DGBOZK.Foundations.DyadicCutoffs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith

/-!
# Construction of the standard smooth cutoff

Mathlib's `Real.smoothTransition` is zero on `(-infinity, 0]`, one on
`[1, infinity)`, takes values in `[0, 1]`, and is infinitely smooth.
Composing it with `s |-> 2 - s` gives the decreasing cutoff required by the
anisotropic Littlewood--Paley decomposition.
-/

namespace DGBOZK
namespace Foundations

noncomputable section

/-- The canonical decreasing cutoff used by the dyadic decomposition. -/
def standardSmoothCutoffProfile : SmoothCutoffProfile where
  toFun := fun s => Real.smoothTransition (2 - s)
  contDiff_toFun := by
    have hAffine : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s : ℝ => (2 : ℝ) - s) :=
      contDiff_const.sub contDiff_id
    simpa only [Function.comp_apply] using
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hAffine
  eq_one_of_le_one := by
    intro s hs
    apply Real.smoothTransition.one_of_one_le
    linarith
  eq_zero_of_two_le := by
    intro s hs
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  nonneg := by
    intro s
    exact Real.smoothTransition.nonneg (2 - s)
  le_one := by
    intro s
    exact Real.smoothTransition.le_one (2 - s)

@[simp] theorem standardSmoothCutoffProfile_apply (s : ℝ) :
    standardSmoothCutoffProfile s =
      Real.smoothTransition (2 - s) :=
  rfl

/-- The cutoff profile required by the dyadic theory is explicitly defined. -/
theorem smoothCutoffProfile_nonempty : Nonempty SmoothCutoffProfile :=
  ⟨standardSmoothCutoffProfile⟩

/-- The canonical cutoff is decreasing. -/
theorem standardSmoothCutoffProfile_antitone :
    Antitone standardSmoothCutoffProfile := by
  intro a b hab
  change Real.smoothTransition (2 - b) ≤
    Real.smoothTransition (2 - a)
  apply Real.smoothTransition.monotone
  linarith

/-- The standard band symbol has the established annular localization. -/
theorem standardBandPassActiveSet_subset_dyadicAnnulus
    {alpha H : ℝ} (hH : 0 < H) :
    bandPassActiveSet standardSmoothCutoffProfile alpha H ⊆
      dyadicAnnulus alpha H :=
  bandPassActiveSet_subset_dyadicAnnulus
    standardSmoothCutoffProfile hH

end
end Foundations
end DGBOZK
