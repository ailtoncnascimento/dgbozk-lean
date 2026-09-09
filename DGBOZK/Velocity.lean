/-
# §3.  `Lemma lem:velocity` — the sharp focusing group-velocity lower bound

Formalizes the quantitative content of `Lemma lem:velocity` in

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*:

  "For every `α ∈ [1,2]` and every `N ≥ 2` one has `|∇ω_-(ζ)| ≳_α N^α` on
   `|ζ| ∼ N`, the order `N^α` is attained when `|ξ| ∼ N` and `η = 0` and is
   therefore sharp."

This is the estimate that produces the focusing deficit `ν_α = 1 − α/2`.
In the cleaned manuscript it contributes to the direct transition estimate
and hence to the threshold `s > 3/2 − α/4`.

## The structure of the proof, and where `α ≤ 2` enters

The longitudinal velocity `∂_ξω_- = η² − (α+1)ξ^α` **vanishes** on the
characteristic curve `Γ⁻_α`, so no lower bound can come from it alone.  The
paper's dichotomy is: either one is far from `Γ⁻_α`, and `|∂_ξω_-| ≳ ξ^α`, or
one is near it, and then `η² ∼ ξ^α`, so that the *transverse* velocity
`|∂_ηω_-| = 2|ξη| ∼ ξ^{1+α/2}` takes over.

The transverse branch is only good enough because

  `1 + α/2 ≥ α  ⟺  α ≤ 2`,

which is exactly the paper's "`|2ξη| ∼ N^{1+α/2} ≥ N^α` because `α ≤ 2`".  At
`α = 2` the two branches balance; that is the ZK endpoint, and it is the reason
the focusing result stops there.

Everything below is proved outright, on the half-plane `ξ > 0`, with the
explicit constant `1`.
-/
import DGBOZK.Phase

set_option autoImplicit false

namespace DGBOZK

open Real

variable {α ξ η : ℝ}

/-! ## The exponent comparison -/

/-- `α ≤ 1 + α/2` iff `α ≤ 2`.  This single inequality is what makes the
transverse branch usable, and it is why the focusing analysis is confined to
`α ≤ 2`. -/
theorem alpha_le_one_add_half : α ≤ 1 + α/2 ↔ α ≤ 2 := by constructor <;> intro h <;> linarith

/-- `ξ^α ≤ ξ^{1+α/2}` for `ξ ≥ 1` and `α ≤ 2`: the transverse gain dominates the
longitudinal scale. -/
theorem transverse_gain (hξ : 1 ≤ ξ) (hα2 : α ≤ 2) : ξ ^ α ≤ ξ ^ (1 + α/2) :=
  Real.rpow_le_rpow_of_exponent_le hξ (by linarith)

/-- `(ξ^{α/2})² = ξ^α`. -/
theorem sq_rpow_half (hξ : 0 < ξ) (α : ℝ) : (ξ ^ (α/2)) ^ (2:ℕ) = ξ ^ α := by
  rw [← Real.rpow_natCast (ξ ^ (α/2)) 2, ← Real.rpow_mul (le_of_lt hξ)]
  congr 1
  push_cast
  ring

/-! ## The dichotomy -/

/-- **The dichotomy of `lem:velocity`.**  Either the focusing longitudinal
velocity is elliptic at the scale `ξ^α`, or one is in the transition region and
`η²` is comparable to `ξ^α`. -/
theorem velocity_dichotomy (_hξ : 0 < ξ) (α η : ℝ) :
    (α + 1) / 2 * ξ ^ α ≤ |velX α (-1) ξ η| ∨ (α + 1) / 2 * ξ ^ α ≤ η ^ 2 := by
  rw [velX_focusing]
  by_cases h : (α + 1) / 2 * ξ ^ α ≤ |η ^ 2 - (α + 1) * ξ ^ α|
  · exact Or.inl h
  · right
    push_neg at h
    have h1 : |η ^ 2 - (α + 1) * ξ ^ α| < (α + 1) / 2 * ξ ^ α := h
    have h2 : -((α + 1) / 2 * ξ ^ α) < η ^ 2 - (α + 1) * ξ ^ α :=
      neg_lt_of_abs_lt h1
    linarith

/-! ## The lower bound -/

/-- **`Lemma lem:velocity`, lower bound.**  For `1 ≤ α ≤ 2` and `ξ ≥ 1`,

  `ξ^α ≤ |∂_ξω_-(ξ,η)| + |∂_ηω_-(ξ,η)|`

for **every** `η`, with constant `1`.  In particular the total group velocity
never degenerates below the order `ξ^α`, even though each component
individually vanishes somewhere. -/
theorem velocity_lower_bound (hξ : 1 ≤ ξ) (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (η : ℝ) :
    ξ ^ α ≤ |velX α (-1) ξ η| + |velY ξ η| := by
  have hξ0 : (0:ℝ) < ξ := by linarith
  have hxa : (0:ℝ) < ξ ^ α := Real.rpow_pos_of_pos hξ0 α
  have hxh : (0:ℝ) < ξ ^ (α/2) := Real.rpow_pos_of_pos hξ0 _
  rcases velocity_dichotomy hξ0 α η with h | h
  · -- away from `Γ⁻_α`: the longitudinal velocity alone suffices,
    -- since `(α+1)/2 ≥ 1` for `α ≥ 1`.
    have : ξ ^ α ≤ (α + 1) / 2 * ξ ^ α := by nlinarith
    have hy : (0:ℝ) ≤ |velY ξ η| := abs_nonneg _
    linarith
  · -- near `Γ⁻_α`: the transverse velocity takes over.
    have hstep : ξ ^ α ≤ η ^ 2 := by nlinarith
    -- hence `|η| ≥ ξ^{α/2}`
    have hsq : (ξ ^ (α/2)) ^ (2:ℕ) = ξ ^ α := sq_rpow_half hξ0 α
    have habs : ξ ^ (α/2) ≤ |η| := by
      have h1 : (ξ ^ (α/2)) ^ (2:ℕ) ≤ |η| ^ (2:ℕ) := by
        rw [hsq, sq_abs]; exact hstep
      nlinarith [abs_nonneg η, hxh, h1]
    -- so `|∂_ηω_-| = 2ξ|η| ≥ 2ξ^{1+α/2} ≥ 2ξ^α ≥ ξ^α`
    have hvy : |velY ξ η| = 2 * ξ * |η| := by
      unfold velY
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hξ0]
    have hprod : ξ * ξ ^ (α/2) = ξ ^ (1 + α/2) := by
      have h := Real.rpow_add hξ0 1 (α/2)
      rw [Real.rpow_one] at h
      exact h.symm
    have hgain : ξ ^ α ≤ ξ ^ (1 + α/2) := transverse_gain hξ hα2
    have hchain : ξ ^ α ≤ 2 * ξ * |η| := by
      have : ξ * ξ ^ (α/2) ≤ ξ * |η| := mul_le_mul_of_nonneg_left habs (le_of_lt hξ0)
      rw [hprod] at this
      linarith
    have hx : (0:ℝ) ≤ |velX α (-1) ξ η| := abs_nonneg _
    rw [hvy]
    linarith

/-! ## Sharpness -/

/-- **Sharpness.**  At `η = 0` the total velocity is exactly `(α+1)ξ^α`, so the
order `ξ^α` in `velocity_lower_bound` is attained and cannot be improved.  This
is the paper's "the order `N^α` is attained when `|ξ| ∼ N` and `η = 0`". -/
theorem velocity_sharp (hξ : 0 < ξ) (hα1 : 1 ≤ α) :
    |velX α (-1) ξ 0| + |velY ξ 0| = (α + 1) * ξ ^ α := by
  have hxa : (0:ℝ) < ξ ^ α := Real.rpow_pos_of_pos hξ α
  rw [velX_focusing]
  unfold velY
  have h1 : |(0:ℝ) ^ 2 - (α + 1) * ξ ^ α| = (α + 1) * ξ ^ α := by
    have : (0:ℝ) ^ 2 - (α + 1) * ξ ^ α = -((α + 1) * ξ ^ α) := by ring
    rw [this, abs_neg, abs_of_pos]
    nlinarith
  rw [h1]
  simp

/-- The transverse velocity vanishes identically on `η = 0`, so the bound really
does come from the longitudinal component there — the two degeneracies of the
focusing phase never occur at the same point. -/
theorem velY_zero (ξ : ℝ) : velY ξ 0 = 0 := by unfold velY; ring

end DGBOZK
