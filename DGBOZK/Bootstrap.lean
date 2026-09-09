/-
# §8–§9.  The a priori system: parameter consistency and the small-data closure

Formalizes two things from

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*:

1. **The defocusing parameter choice is not vacuous.**  Its proof opens with
   "Choose `ε₀ > 0` with `r⁺_α + 4ε₀ < r` and
   `𝖪_α + ε₀ < r⁺_α`."
   Whether such an `ε₀` exists at all is a genuine constraint: it requires
   `𝖪_α < r⁺_α`, which holds only because of the second identity of
   `(eq:binding-ell)`.  Every admissibility inequality the proof then invokes is
   derived here from that single choice.

2. **The small-data bootstrap `(eq:small-bootstrap)` closes.**  The inequality
   `X ≤ C₀e₀ + C₁(X^{3/2} + X² + X^{5/2})` is shown to force `X ≤ 2C₀e₀` below
   an explicit barrier — the algebraic content of the continuity argument, with
   no topology and no black boxes.

Everything in this file is proved outright.
-/
import DGBOZK.Exponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace DGBOZK

open Real

/-! ## The bootstrap barrier, `(eq:small-bootstrap)` -/

/-- **The small-data closure.**  Suppose `X` satisfies the bootstrap inequality
`X ≤ C₀e₀ + C₁(X^{3/2} + X² + X^{5/2})` and lies below a barrier `M` on which
the nonlinear coefficient `C₁(M^{1/2} + M + M^{3/2})` is at most `1/2`.  Then
`X ≤ 2C₀e₀`.

This is the algebraic heart of §9.1: the continuity argument in the paper
supplies `X(T) ≤ M` for `T` in a relatively open and closed subset of `[0,T]`,
and this lemma is what converts that into the stated conclusion
`X(T) ≤ 2C₀e₀`. -/
theorem bootstrap_closure {C₀ C₁ e₀ M X : ℝ}
    (hC₁ : 0 ≤ C₁) (hX0 : 0 ≤ X) (hXM : X ≤ M)
    (hbarrier : C₁ * (M ^ (1/2 : ℝ) + M + M ^ (3/2 : ℝ)) ≤ 1/2)
    (hineq : X ≤ C₀ * e₀ + C₁ * (X ^ (3/2 : ℝ) + X ^ (2 : ℝ) + X ^ (5/2 : ℝ))) :
    X ≤ 2 * (C₀ * e₀) := by
  rcases eq_or_lt_of_le hX0 with hzero | hXpos
  · -- `X = 0`: the conclusion needs `0 ≤ C₀e₀`, which follows from `hineq`.
    have h0 : (0:ℝ) ^ (3/2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
    have h1 : (0:ℝ) ^ (2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
    have h2 : (0:ℝ) ^ (5/2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
    rw [← hzero] at hineq
    rw [h0, h1, h2] at hineq
    linarith
  · have hM : 0 < M := lt_of_lt_of_le hXpos hXM
    -- split off one factor of `X` from each power
    have e32 : X ^ (3/2 : ℝ) = X * X ^ (1/2 : ℝ) := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hXpos, Real.rpow_one]
    have e2 : X ^ (2 : ℝ) = X * X := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hXpos, Real.rpow_one]
    have e52 : X ^ (5/2 : ℝ) = X * X ^ (3/2 : ℝ) := by
      rw [show (5/2 : ℝ) = 1 + 3/2 by norm_num, Real.rpow_add hXpos, Real.rpow_one]
    have m1 : X ^ (1/2 : ℝ) ≤ M ^ (1/2 : ℝ) := Real.rpow_le_rpow hX0 hXM (by norm_num)
    have m3 : X ^ (3/2 : ℝ) ≤ M ^ (3/2 : ℝ) := Real.rpow_le_rpow hX0 hXM (by norm_num)
    have key : X ^ (3/2 : ℝ) + X ^ (2 : ℝ) + X ^ (5/2 : ℝ)
        ≤ X * (M ^ (1/2 : ℝ) + M + M ^ (3/2 : ℝ)) := by
      rw [e32, e2, e52]
      nlinarith [m1, m3, hXM, hX0]
    have step : C₁ * (X ^ (3/2 : ℝ) + X ^ (2 : ℝ) + X ^ (5/2 : ℝ))
        ≤ X * (C₁ * (M ^ (1/2 : ℝ) + M + M ^ (3/2 : ℝ))) := by
      nlinarith [key, hC₁]
    have half : X * (C₁ * (M ^ (1/2 : ℝ) + M + M ^ (3/2 : ℝ))) ≤ X * (1/2) :=
      mul_le_mul_of_nonneg_left hbarrier hX0
    linarith

/-! ## Consistency of the defocusing parameter choices -/

/-- **Defocusing case.**  For `1 ≤ α < 4/3` and any `r > r⁺_α` there really is an
`ε₀ > 0` with

  `r⁺_α + 4ε₀ < r`  and  `𝖪_α + ε₀ < r⁺_α`.

The second condition is available **only** because `𝖪_α < r⁺_α`, i.e. because
`𝖱_{α,1} − 𝖪_α = 5(2−α)/(24α) > 0`. -/
theorem exists_eps_defocusing {α r : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 4/3)
    (hr : rPlus α < r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ rPlus α + 4 * ε₀ < r ∧ Kfold α + ε₀ < rPlus α := by
  have hαpos : (0:ℝ) < α := by linarith
  have hK : Kfold α < rPlus α := by
    rw [rPlus_eq_R1]
    exact Kfold_lt_R1 hαpos (by linarith)
  set ε₀ := min ((r - rPlus α) / 8) ((rPlus α - Kfold α) / 2) with hε
  have h1 : 0 < (r - rPlus α) / 8 := by linarith
  have h2 : 0 < (rPlus α - Kfold α) / 2 := by linarith
  refine ⟨ε₀, lt_min h1 h2, ?_, ?_⟩
  · have : ε₀ ≤ (r - rPlus α) / 8 := min_le_left _ _
    linarith
  · have : ε₀ ≤ (rPlus α - Kfold α) / 2 := min_le_right _ _
    linarith

/-! ## The defocusing admissibility inequalities

With `τ = r − ε₀` and `ε₀` as above, the proof of `Prop:coupled` applies
`Prop:ell-product` twice, at `γ = r⁺_α − δ_α + 2ε₀` and at `γ = κ_α + ε₀`.  Both
applications require `γ ≥ 0` and `γ + δ_α < τ`.  Both are derived here.
-/

/-- Every hypothesis `Prop:ell-product` needs, for both of its applications in
the proof of `Prop:coupled`, follows from the single choice of `ε₀`. -/
theorem coupled_admissible_defocusing {α r ε₀ : ℝ}
    (hα1 : 1 ≤ α) (hα2 : α < 4/3)
    (hε : 0 < ε₀) (h1 : rPlus α + 4 * ε₀ < r) (h2 : Kfold α + ε₀ < rPlus α) :
    -- with τ = r − ε₀, γ₁ = r⁺_α − δ_α + 2ε₀, γ₂ = κ_α + ε₀.
    -- The `2ε₀` is what the ℓ¹ form of `(eq:refined-ell-opt)` costs: its
    -- forcing exponent is `r⁺_α − δ_α + 2ε` when applied with `ε = ε₀`.
    (0 < r - ε₀ ∧ r - ε₀ ≤ r) ∧
    (0 ≤ rPlus α - delta α + 2 * ε₀ ∧
      (rPlus α - delta α + 2 * ε₀) + delta α < r - ε₀) ∧
    (0 ≤ kappa α + ε₀ ∧ (kappa α + ε₀) + delta α < r - ε₀) ∧
    (dAniso α / 2 < r - ε₀) := by
  have hαpos : (0:ℝ) < α := by linarith
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hmargin : dAniso α / 2 < rPlus α := algebra_margin_on_range hα1 hα2
  have hδpos : 0 < rPlus α - delta α := rPlus_sub_delta_pos hαpos
  have hκpos : 0 < kappa α := lt_trans (by norm_num) (kappa_gt_quarter hαpos)
  have hKδ : Kfold α = kappa α + delta α := Kfold_eq_kappa_add_delta hαne
  have hdA : 0 < dAniso α := by
    unfold dAniso
    have : 0 < 1 / α := by positivity
    linarith
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩, by linarith⟩

end DGBOZK
