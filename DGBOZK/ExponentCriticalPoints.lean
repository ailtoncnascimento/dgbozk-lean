/-
# Two exponent-level critical points not yet in the library (proposal)

1. `eq:magic`: the fold block exponent of `prop:ell-blocks`, computed from the
   abstract `TT*` lemma with `γ = 5/6`, `Λ = H^{-(2α-1)/(6α)}`, `m = H^{d_α}`,
   coincides with the nondegenerate exponent `E⁺_α(p)` for every `p`.
   The manuscript calls this "the exact reason why the Hessian fold is
   invisible at the level of the algebraic frequency exponent".

2. `eq:residual-count`: a residual `H⁻¹ T_b[∂^A v, ∂^B z', ∂^C z]` with one
   `∂ₓ` and two `∂_y` in total, `p` of the `∂ₓ` and `q` of the `∂_y` on the low
   factor, has dyadic exponent `(p-1)/α + q/2`; it is nonnegative exactly in the
   admissible cases `p = 1` or `q = 2` (for `1 ≤ α < 2`).  This is the
   classification that decides which terms need the cubic correction.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK.ExponentCritical

/-- Anisotropic dimension `d_α = 1/α + 1/2`. -/
noncomputable def dA (α : ℝ) : ℝ := 1 / α + 1 / 2

/-- `E⁺_α(p)` of `eq:E-both`. -/
noncomputable def Eplus (α p : ℝ) : ℝ := (α + 2) / (4 * α) - (α + 1) / (α * p)

/-- Block exponent from `lem:abstract`: `m^{1/2 - 1/(γp)} Λ^{1/(γp)}` with
`m = H^{mExp}`, `Λ = H^{-lamExp}`. -/
noncomputable def blockExp (mExp lamExp γ p : ℝ) : ℝ :=
  mExp * (1 / 2 - 1 / (γ * p)) - lamExp * (1 / (γ * p))

/-- Off the fold: `γ = 1`, `Λ = H^{-1/2}`. -/
theorem regular_block_exponent {α p : ℝ} (hα : α ≠ 0) (hp : p ≠ 0) :
    blockExp (dA α) (1 / 2) 1 p = Eplus α p := by
  unfold blockExp dA Eplus
  field_simp
  ring

/-- **`eq:magic`.**  On the fold: `γ = 5/6`, `Λ = H^{-(2α-1)/(6α)}`. -/
theorem fold_block_exponent {α p : ℝ} (hα : α ≠ 0) (hp : p ≠ 0) :
    blockExp (dA α) ((2 * α - 1) / (6 * α)) (5 / 6) p = Eplus α p := by
  unfold blockExp dA Eplus
  field_simp
  ring

/-- Dyadic exponent of a residual with `p` longitudinal and `q` transverse
derivatives on the low factor. -/
noncomputable def residualExp (α : ℝ) (p q : ℕ) : ℝ := ((p : ℝ) - 1) / α + (q : ℝ) / 2

/-- **`eq:residual-count`.**  For `1 ≤ α < 2`, `p ≤ 1`, `q ≤ 2`, the exponent is
nonnegative iff `p = 1` or `q = 2`. -/
theorem residual_admissible_iff {α : ℝ} (h1 : 1 ≤ α) (h2 : α < 2)
    (p q : ℕ) (hp : p ≤ 1) (hq : q ≤ 2) :
    0 ≤ residualExp α p q ↔ (p = 1 ∨ q = 2) := by
  have hpos : 0 < α := by linarith
  have ht : α * (1 / α) = 1 := by field_simp
  have hinv : 0 < 1 / α := by positivity
  have hle : 1 / α ≤ 1 := by nlinarith
  have hgt : 1 / 2 < 1 / α := by nlinarith
  have e00 : residualExp α 0 0 = -(1 / α) := by unfold residualExp; push_cast; ring
  have e01 : residualExp α 0 1 = 1 / 2 - 1 / α := by unfold residualExp; push_cast; ring
  have e02 : residualExp α 0 2 = 1 - 1 / α := by unfold residualExp; push_cast; ring
  have e1 : ∀ k : ℕ, residualExp α 1 k = (k : ℝ) / 2 := by
    intro k; unfold residualExp; push_cast; ring
  interval_cases p <;> interval_cases q
  · rw [e00]; constructor
    · intro h; linarith
    · intro h; omega
  · rw [e01]; constructor
    · intro h; linarith
    · intro h; omega
  · rw [e02]; exact ⟨fun _ => Or.inr rfl, fun _ => by linarith⟩
  · rw [e1]; exact ⟨fun _ => Or.inl rfl, fun _ => by positivity⟩
  · rw [e1]; exact ⟨fun _ => Or.inl rfl, fun _ => by positivity⟩
  · rw [e1]; exact ⟨fun _ => Or.inl rfl, fun _ => by positivity⟩

end DGBOZK.ExponentCritical
