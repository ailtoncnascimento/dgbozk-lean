/-
# §3.  `Lemma lem:fold` — the defocusing degeneracy is a fold, uniformly in `α`

Formalizes the reduced-phase identities of `Lemma lem:fold` in

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*.

Fix `t ≠ 0` and `ξ > 0`, integrate the kernel of `U_+(t)` first in `η`, and let
`η_* = −y/(2tξ)` be the stationary point.  The reduced phase is

  `Ψ(ξ) = xξ + tξ^{α+1} − y²/(4tξ)`

and the lemma asserts the two identities

  `Ψ''(ξ)  = (t/2ξ) · det D²ω_+(ξ, η_*)`,
  `Ψ'''(ξ) = t[ α(α+1)(α−1)ξ^{α−2} + 6η_*²/ξ² ]`,

together with the nondegeneracy `Ψ'''|_{Γ⁺_α} = t α(α+1)(α+2) ξ^{α−2} ≠ 0`.

## What is black-boxed

`[BB-DIFF]`: the elementary derivative formulas

  `Ψ''(ξ)  = t α(α+1) ξ^{α−1} − y²/(2tξ³)`,
  `Ψ'''(ξ) = t α(α+1)(α−1) ξ^{α−2} + 3y²/(2tξ⁴)`,

which the paper obtains by differentiating `Ψ` twice and three times.  These are
introduced as definitions.

## What is proved

Everything downstream: the substitution `y = −2tξη_*`, the identification with
`det D²ω_+`, the value on `Γ⁺_α`, the same-sign property for `α ≥ 1`, the
quantitative lower bound, and the fact that the `α = 1` case (where the first
term of `Ψ'''` vanishes identically) is still covered.

The substitution step is where a sign error would live, and it is precisely what
is machine-checked here: the reader may verify that `Ψ''` picks up
`−2tη_*²/ξ` and `Ψ'''` picks up `+6tη_*²/ξ²`, with the factors `2` and `6`
coming out of `4t²ξ²/(2tξ³)` and `3·4t²ξ²/(2tξ⁴)` respectively.
-/
import DGBOZK.Phase

set_option autoImplicit false

namespace DGBOZK

open Real

variable {α x y t ξ ηs : ℝ}

/-! ## The reduced phase and its derivatives -/

/-- `Ψ(ξ) = xξ + tξ^{α+1} − y²/(4tξ)`, the reduced phase of `lem:fold`. -/
noncomputable def Psi (α x y t ξ : ℝ) : ℝ := x * ξ + t * ξ ^ (α + 1) - y ^ 2 / (4 * t * ξ)

/-- `Ψ''(ξ) = tα(α+1)ξ^{α−1} − y²/(2tξ³)`.  **[BB-DIFF]** -/
noncomputable def Psi2 (α y t ξ : ℝ) : ℝ :=
  t * (α * (α + 1)) * ξ ^ (α - 1) - y ^ 2 / (2 * t * ξ ^ 3)

/-- `Ψ'''(ξ) = tα(α+1)(α−1)ξ^{α−2} + 3y²/(2tξ⁴)`.  **[BB-DIFF]** -/
noncomputable def Psi3 (α y t ξ : ℝ) : ℝ :=
  t * (α * (α + 1) * (α - 1)) * ξ ^ (α - 2) + 3 * y ^ 2 / (2 * t * ξ ^ 4)

/-! ## Exponent arithmetic for the substitution -/

theorem rpow_sub_two_mul_sq {ξ : ℝ} (hξ : 0 < ξ) (α : ℝ) : ξ ^ (α - 2) * ξ ^ 2 = ξ ^ α := by
  have h2 : ξ ^ (2:ℝ) = ξ ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have h := (Real.rpow_add hξ (α - 2) 2).symm
  rw [h2] at h
  rw [h]
  norm_num

theorem rpow_alpha_div_sq {ξ : ℝ} (hξ : 0 < ξ) (α : ℝ) : ξ ^ α / ξ ^ 2 = ξ ^ (α - 2) := by
  have h := rpow_sub_two_mul_sq hξ α
  field_simp [pow_ne_zero 2 (ne_of_gt hξ)]
  linarith [h]

theorem rpow_alpha_div {ξ : ℝ} (hξ : 0 < ξ) (α : ℝ) : ξ ^ α / ξ = ξ ^ (α - 1) := by
  have h := rpow_sub_one_mul hξ α
  field_simp
  linarith [h]

/-! ## The two identities of `lem:fold` -/

/-- **First identity.**  With `η_*` the stationary point, i.e. `y = −2tξη_*`,

  `Ψ''(ξ) = (t/(2ξ)) · det D²ω_+(ξ, η_*)`.

This is the assertion that the second derivative of the reduced phase *is* the
Hessian determinant of the full phase, up to the explicit factor `t/(2ξ)`. -/
theorem Psi2_eq_hessDet (hξ : 0 < ξ) (ht : t ≠ 0) (hy : y = -2 * t * ξ * ηs) :
    Psi2 α y t ξ = (t / (2 * ξ)) * hessDet α 1 ξ ηs := by
  subst hy
  unfold Psi2 hessDet
  have hξ' : ξ ≠ 0 := ne_of_gt hξ
  have hxa : ξ ^ (α - 1) * ξ = ξ ^ α := rpow_sub_one_mul hξ α
  rw [← hxa]
  field_simp
  ring

/-- **Second identity.**  With `y = −2tξη_*`,

  `Ψ'''(ξ) = t[ α(α+1)(α−1)ξ^{α−2} + 6η_*²/ξ² ]`.

The coefficient `6` is the one produced by `3·(4t²ξ²)/(2tξ⁴)`. -/
theorem Psi3_substituted (hξ : 0 < ξ) (ht : t ≠ 0) (hy : y = -2 * t * ξ * ηs) :
    Psi3 α y t ξ = t * (α * (α + 1) * (α - 1) * ξ ^ (α - 2) + 6 * ηs ^ 2 / ξ ^ 2) := by
  subst hy
  unfold Psi3
  have hξ' : ξ ≠ 0 := ne_of_gt hξ
  field_simp
  ring

/-! ## Behaviour on the fold curve `Γ⁺_α = {2η² = α(α+1)ξ^α}` -/

/-- **The nondegeneracy on the fold.**  On `Γ⁺_α`,

  `Ψ'''(ξ) = t α(α+1)(α+2) ξ^{α−2}`,

so the third derivative is nonzero there for every `α ≥ 1`: the degeneracy is a
**fold**, not a cusp.  The coefficient `α+2 = (α−1) + 3` is the sum of the two
contributions, and the `3` comes from `6η_*²/ξ² = 3α(α+1)ξ^{α−2}` on `Γ⁺_α`. -/
theorem Psi3_on_gamma_plus (hξ : 0 < ξ) (ht : t ≠ 0) (hy : y = -2 * t * ξ * ηs)
    (hΓ : 2 * ηs ^ 2 = α * (α + 1) * ξ ^ α) :
    Psi3 α y t ξ = t * (α * (α + 1) * (α + 2)) * ξ ^ (α - 2) := by
  rw [Psi3_substituted hξ ht hy]
  have hξ2 : (ξ:ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hξ)
  have hdiv : ξ ^ α / ξ ^ 2 = ξ ^ (α - 2) := rpow_alpha_div_sq hξ α
  have h6 : 6 * ηs ^ 2 / ξ ^ 2 = 3 * (α * (α + 1)) * (ξ ^ α / ξ ^ 2) := by
    field_simp
    linarith [hΓ]
  rw [h6, hdiv]
  ring

/-- The fold is nondegenerate: on `Γ⁺_α` with `t ≠ 0`, `ξ > 0`, `α ≥ 1`, one has
`Ψ'''(ξ) ≠ 0`. -/
theorem Psi3_ne_zero_on_gamma_plus (hξ : 0 < ξ) (ht : t ≠ 0) (hα : 1 ≤ α)
    (hy : y = -2 * t * ξ * ηs) (hΓ : 2 * ηs ^ 2 = α * (α + 1) * ξ ^ α) :
    Psi3 α y t ξ ≠ 0 := by
  rw [Psi3_on_gamma_plus hξ ht hy hΓ]
  have hpow : (0:ℝ) < ξ ^ (α - 2) := Real.rpow_pos_of_pos hξ _
  have hcoef : (0:ℝ) < α * (α + 1) * (α + 2) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  exact mul_ne_zero (mul_ne_zero ht (ne_of_gt hcoef)) (ne_of_gt hpow)

/-! ## The same-sign property and the quantitative lower bound -/

/-- For `α ≥ 1`, `ξ > 0` and `t > 0`, **both** terms of `Ψ'''` are nonnegative.
This is the paper's observation that they cannot cancel. -/
theorem Psi3_terms_same_sign (hξ : 0 < ξ) (ht : 0 < t) (hα : 1 ≤ α) (ηs : ℝ) :
    0 ≤ t * (α * (α + 1) * (α - 1)) * ξ ^ (α - 2) ∧ 0 ≤ t * (6 * ηs ^ 2 / ξ ^ 2) := by
  have hpow : (0:ℝ) < ξ ^ (α - 2) := Real.rpow_pos_of_pos hξ _
  have hcoef : (0:ℝ) ≤ α * (α + 1) * (α - 1) :=
    mul_nonneg (le_of_lt (mul_pos (by linarith) (by linarith))) (by linarith)
  constructor
  · positivity
  · have : (0:ℝ) < ξ ^ 2 := by positivity
    positivity

/-- **The uniform lower bound.**  If `η_*² ≥ c ξ^α` with `c > 0`, then
`Ψ'''(ξ) ≥ 6c·t·ξ^{α−2}`.  In particular the bound is uniform in `α ∈ [1,2]`,
and it survives at `α = 1`, where the first term of `Ψ'''` vanishes identically
— the second term alone carries it.  This is the assertion
`|Ψ'''(ξ)| ≳_α |t| ξ^{α−2}` whenever `η_*² ≳ ξ^α`. -/
theorem Psi3_lower_bound (hξ : 0 < ξ) (ht : 0 < t) (hα : 1 ≤ α) {c : ℝ} (_hc : 0 < c)
    (hy : y = -2 * t * ξ * ηs) (hηs : c * ξ ^ α ≤ ηs ^ 2) :
    6 * c * t * ξ ^ (α - 2) ≤ Psi3 α y t ξ := by
  rw [Psi3_substituted hξ (ne_of_gt ht) hy]
  have hξ2 : (0:ℝ) < ξ ^ 2 := by positivity
  have hpow : (0:ℝ) < ξ ^ (α - 2) := Real.rpow_pos_of_pos hξ _
  have hdiv : ξ ^ α / ξ ^ 2 = ξ ^ (α - 2) := rpow_alpha_div_sq hξ α
  have hstep : 6 * c * ξ ^ (α - 2) ≤ 6 * ηs ^ 2 / ξ ^ 2 := by
    rw [← hdiv]
    have hinv : (0:ℝ) < (ξ ^ 2)⁻¹ := by positivity
    have hnum : (0:ℝ) ≤ 6 * ηs ^ 2 - 6 * c * ξ ^ α := by linarith
    have hmul : (0:ℝ) ≤ (6 * ηs ^ 2 - 6 * c * ξ ^ α) * (ξ ^ 2)⁻¹ :=
      mul_nonneg hnum (le_of_lt hinv)
    simp only [div_eq_mul_inv]
    linarith [hmul]
  have hcoef : (0:ℝ) ≤ α * (α + 1) * (α - 1) :=
    mul_nonneg (le_of_lt (mul_pos (by linarith) (by linarith))) (by linarith)
  have hfirst : (0:ℝ) ≤ α * (α + 1) * (α - 1) * ξ ^ (α - 2) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hstep (le_of_lt ht)
  have h2 := mul_nonneg (le_of_lt ht) hfirst
  nlinarith [h1, h2]

/-- The `α = 1` endpoint, stated separately because it is the case the paper
singles out: the first term of `Ψ'''` vanishes identically and the bound comes
entirely from the transverse contribution. -/
theorem Psi3_at_alpha_one (hξ : 0 < ξ) (ht : t ≠ 0) (hy : y = -2 * t * ξ * ηs) :
    Psi3 1 y t ξ = t * (6 * ηs ^ 2 / ξ ^ 2) := by
  rw [Psi3_substituted hξ ht hy]
  norm_num

/-- At `α = 1` on the fold curve the value is `6tξ^{-1}`, matching
`tα(α+1)(α+2)ξ^{α−2} = 6tξ^{-1}`. -/
theorem Psi3_on_gamma_plus_alpha_one (hξ : 0 < ξ) (ht : t ≠ 0)
    (hy : y = -2 * t * ξ * ηs) (hΓ : 2 * ηs ^ 2 = 1 * (1 + 1) * ξ ^ (1:ℝ)) :
    Psi3 1 y t ξ = t * 6 * ξ ^ ((1:ℝ) - 2) := by
  rw [Psi3_on_gamma_plus hξ ht hy hΓ]
  norm_num

end DGBOZK
