/-
# Focusing threshold in the cleaned manuscript

This file checks only the scalar parameter arithmetic behind the focusing
regularity threshold.  It does not assert the transition commutator estimate,
the refined linear estimate, or the nonlinear energy inequality.
-/
import DGBOZK.Exponents
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK

/-- The focusing Sobolev threshold in the cleaned manuscript. -/
noncomputable def sMinus (α : ℝ) : ℝ := 3 / 2 - α / 4

theorem sMinus_eq (α : ℝ) : sMinus α = (6 - α) / 4 := by
  unfold sMinus
  ring

@[simp] theorem sMinus_one : sMinus 1 = 5 / 4 := by
  unfold sMinus
  norm_num

@[simp] theorem sMinus_two : sMinus 2 = 1 := by
  unfold sMinus
  norm_num

theorem sMinus_strictAnti : StrictAnti sMinus := by
  intro α β hαβ
  unfold sMinus
  linarith

/-- Derivative loss in the direct focusing transition estimate. -/
noncomputable def directLoss (α : ℝ) : ℝ := 1 / 2 - α / 4

theorem sMinus_eq_one_add_directLoss (α : ℝ) :
    sMinus α = 1 + directLoss α := by
  unfold sMinus directLoss
  ring

theorem directLoss_pos {α : ℝ} (hα : α < 2) : 0 < directLoss α := by
  unfold directLoss
  linarith

/-- The exponent comparison appearing after the direct transition commutator
is reduced to its exact scalar form. -/
theorem direct_commutator_gap_iff {α s τ : ℝ} :
    2 * τ + 1 - α / 2 ≤ 2 * s ↔ τ ≤ s - 1 / 2 + α / 4 := by
  constructor <;> intro h <;> linarith

/-- There is a Sobolev exponent τ strictly above one and below the direct
commutator ceiling exactly when s is above the focusing threshold. -/
theorem exists_admissible_tau_iff {α s : ℝ} :
    (∃ τ : ℝ, 1 < τ ∧ τ ≤ s - 1 / 2 + α / 4) ↔ sMinus α < s := by
  constructor
  · rintro ⟨τ, hτ1, hτ2⟩
    unfold sMinus
    linarith
  · intro hs
    refine ⟨(1 + (s - 1 / 2 + α / 4)) / 2, ?_, ?_⟩
    · unfold sMinus at hs
      linarith
    · unfold sMinus at hs
      linarith

/-- A canonical positive amount by which the focusing index is lowered from s. -/
noncomputable def focusingEps0 (α : ℝ) : ℝ := directLoss α

/-- The corresponding intermediate energy exponent. -/
noncomputable def focusingTau (α s : ℝ) : ℝ := s - focusingEps0 α

theorem focusingTau_eq (α s : ℝ) :
    focusingTau α s = s - 1 / 2 + α / 4 := by
  unfold focusingTau focusingEps0 directLoss
  ring

theorem focusing_eps0_window {α s : ℝ} (hα : α < 2)
    (hs : sMinus α < s) :
    0 < focusingEps0 α ∧ 1 < s - focusingEps0 α := by
  constructor
  · exact directLoss_pos hα
  · rw [sMinus_eq_one_add_directLoss α] at hs
    unfold focusingEps0
    linarith

theorem focusing_tau_admissible {α s : ℝ} (hα : α < 2)
    (hs : sMinus α < s) :
    1 < focusingTau α s ∧ focusingTau α s ≤ s - 1 / 2 + α / 4 := by
  have hw := focusing_eps0_window hα hs
  constructor
  · exact hw.2
  · rw [focusingTau_eq]

/-- Once τ is fixed, there is a positive refined-estimate slack epsilon below
both occurrences of the common exponent S0. -/
theorem exists_refined_epsilon {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 2)
    (hs : sMinus α < s) :
    ∃ ε : ℝ, 0 < ε ∧ S0 α + ε < focusingTau α s ∧
      (1 / 2 + ε) + nu α < focusingTau α s := by
  have hτ : 1 < focusingTau α s := (focusing_tau_admissible hα2 hs).1
  have hS : S0 α ≤ 1 := S0_le_one hα1
  have hgap : S0 α < focusingTau α s := lt_of_le_of_lt hS hτ
  refine ⟨(focusingTau α s - S0 α) / 2, by linarith, ?_, ?_⟩
  · linarith
  · have hid : (1 / 2 + (focusingTau α s - S0 α) / 2) + nu α =
        S0 α + (focusingTau α s - S0 α) / 2 := by
      unfold nu S0
      ring
    rw [hid]
    linarith

/-- Complete scalar parameter package used by the cleaned focusing argument. -/
theorem focusing_parameter_package {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 2)
    (hs : sMinus α < s) :
    0 < focusingEps0 α ∧
    1 < focusingTau α s ∧
    focusingTau α s ≤ s - 1 / 2 + α / 4 ∧
    ∃ ε : ℝ, 0 < ε ∧ S0 α + ε < focusingTau α s ∧
      (1 / 2 + ε) + nu α < focusingTau α s := by
  obtain ⟨hε0, hτ⟩ := focusing_eps0_window hα2 hs
  have hceiling := (focusing_tau_admissible hα2 hs).2
  exact ⟨hε0, hτ, hceiling, exists_refined_epsilon hα1 hα2 hs⟩

end DGBOZK
