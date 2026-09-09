/-
# §3.  The sign-dependent phase geometry

Formalizes `(eq:grad-ell)`, `(eq:grad-hyp)` and `Proposition prop:exchange` of

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*.

The phase is `ω_σ(ξ,η) = ξ(η² + σ|ξ|^α)`, `σ ∈ {±1}`, and the whole paper is
organized around the *exchange of degeneracies* between the two signs.  Getting
a sign wrong in `∇ω_σ` or in `det D²ω_σ` would invert that exchange and
invalidate the architecture of the paper, so this is the first thing worth
machine-checking.

## What is proved and what is assumed

Following Terence Tao's conditional-formalization strategy, the *differentiation
step* is the declared black box.  Concretely: the first- and second-order
partial derivatives of `ω_σ` are introduced as **definitions** matching the
formulas displayed in the paper, and everything downstream is then proved.  The
one genuine consistency check available at this level — that the displayed
determinant really is `∂²_ξ ω · ∂²_η ω − (∂_ξ∂_η ω)²` computed from the
displayed second derivatives — *is* carried out, and it is a real check, since
it exercises the exponent bookkeeping `ξ^{α−1} · ξ = ξ^α`.

See `DGBOZK/BlackBoxes.lean` for the precise statement of `[BB-DIFF]`.

Throughout we work on the half-plane `ξ > 0`, exactly as the paper does ("on
each half-plane `±ξ > 0`"); the case `ξ < 0` follows by the reflection
`(ξ,η,x,y,t) ↦ (−ξ,η,−x,y,t)` recorded in the proof of `lem:fold`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace DGBOZK

open Real

/-! ## The anisotropic weight and the phase -/

/-- `ρ_α(ξ,η) = |ξ|^α + η²`, `(eq:rho)`. -/
noncomputable def rho (α ξ η : ℝ) : ℝ := |ξ| ^ α + η ^ 2

/-- `ω_σ(ξ,η) = ξ(η² + σ|ξ|^α)`, `(eq:propagator)`. -/
noncomputable def omega (α σ ξ η : ℝ) : ℝ := ξ * (η ^ 2 + σ * |ξ| ^ α)

theorem rho_pos {α ξ η : ℝ} (hξ : 0 < ξ) : 0 < rho α ξ η := by
  unfold rho
  have : (0:ℝ) < |ξ| ^ α := Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_gt hξ)) α
  positivity

/-- On the half-plane `ξ > 0` the phase is `ξ(η² + σ ξ^α)`. -/
theorem omega_of_pos {α σ ξ η : ℝ} (hξ : 0 < ξ) :
    omega α σ ξ η = ξ * (η ^ 2 + σ * ξ ^ α) := by
  unfold omega; rw [abs_of_pos hξ]

theorem rho_of_pos {α ξ η : ℝ} (hξ : 0 < ξ) : rho α ξ η = ξ ^ α + η ^ 2 := by
  unfold rho; rw [abs_of_pos hξ]

/-! ## The derivatives displayed in `(eq:grad-ell)` and `(eq:grad-hyp)`

A single `σ`-parametrized family reproduces *both* displayed lines of the paper.
That the two lines of the paper are the `σ = +1` and `σ = −1` instances of one
formula is itself a check worth recording: see `velX_defocusing`,
`velX_focusing`, `hessDet_defocusing`, `hessDet_focusing` below.
-/

section HalfPlane

variable {α σ ξ η : ℝ}

/-- `∂_ξ ω_σ = σ(α+1)ξ^α + η²`, the longitudinal group velocity, `ξ > 0`.
**[BB-DIFF]** -/
noncomputable def velX (α σ ξ η : ℝ) : ℝ := σ * (α + 1) * ξ ^ α + η ^ 2

/-- `∂_η ω_σ = 2ξη`, the transverse group velocity.  **[BB-DIFF]** -/
noncomputable def velY (ξ η : ℝ) : ℝ := 2 * ξ * η

/-- `∂²_ξ ω_σ = σ α(α+1) ξ^{α−1}`.  **[BB-DIFF]** -/
noncomputable def hessXX (α σ ξ : ℝ) : ℝ := σ * (α * (α + 1)) * ξ ^ (α - 1)

/-- `∂_ξ∂_η ω_σ = 2η`.  **[BB-DIFF]** -/
noncomputable def hessXY (η : ℝ) : ℝ := 2 * η

/-- `∂²_η ω_σ = 2ξ`.  **[BB-DIFF]** -/
noncomputable def hessYY (ξ : ℝ) : ℝ := 2 * ξ

/-- `det D²ω_σ = 2σα(α+1)ξ^α − 4η²`, as displayed in `(eq:grad-ell)` /
`(eq:grad-hyp)`. -/
noncomputable def hessDet (α σ ξ η : ℝ) : ℝ := σ * (2 * α * (α + 1)) * ξ ^ α - 4 * η ^ 2

/-- The exponent identity underlying the determinant computation. -/
theorem rpow_sub_one_mul {ξ : ℝ} (hξ : 0 < ξ) (α : ℝ) : ξ ^ (α - 1) * ξ = ξ ^ α := by
  have h := (Real.rpow_add hξ (α - 1) 1).symm
  rw [Real.rpow_one] at h
  rw [h]
  norm_num

/-- **Consistency of the displayed determinant with the displayed Hessian
entries.**  This is the one part of the differentiation step that can be checked
without differentiating, and it is exactly where the exponent `α−1` has to
combine correctly with the factor `ξ` from `∂²_η ω`. -/
theorem hessDet_eq_det (hξ : 0 < ξ) (α σ η : ℝ) :
    hessDet α σ ξ η = hessXX α σ ξ * hessYY ξ - hessXY η ^ 2 := by
  unfold hessDet hessXX hessYY hessXY
  have h : ξ ^ (α - 1) * ξ = ξ ^ α := rpow_sub_one_mul hξ α
  rw [← h]
  ring

/-! ### The two signs, as displayed in the paper -/

/-- `(eq:grad-ell)`: `∇ω_+ = ((α+1)ξ^α + η², 2ξη)`. -/
theorem velX_defocusing (α ξ η : ℝ) : velX α 1 ξ η = (α + 1) * ξ ^ α + η ^ 2 := by
  unfold velX; ring

/-- `(eq:grad-hyp)`: `∇ω_- = (η² − (α+1)ξ^α, 2ξη)`. -/
theorem velX_focusing (α ξ η : ℝ) : velX α (-1) ξ η = η ^ 2 - (α + 1) * ξ ^ α := by
  unfold velX; ring

/-- `(eq:grad-ell)`: `det D²ω_+ = 2α(α+1)ξ^α − 4η²`. -/
theorem hessDet_defocusing (α ξ η : ℝ) :
    hessDet α 1 ξ η = 2 * α * (α + 1) * ξ ^ α - 4 * η ^ 2 := by
  unfold hessDet; ring

/-- `(eq:grad-hyp)`: `det D²ω_- = −2α(α+1)ξ^α − 4η²`.  Both terms have the same
sign — this is the assertion the focusing analysis rests on. -/
theorem hessDet_focusing (α ξ η : ℝ) :
    hessDet α (-1) ξ η = -(2 * α * (α + 1) * ξ ^ α) - 4 * η ^ 2 := by
  unfold hessDet; ring

end HalfPlane

/-! ## `Proposition prop:exchange`: the exchange of degeneracies

The defocusing phase has an **elliptic longitudinal velocity** and a **vanishing
Hessian determinant** on a curve; the focusing phase has a **Hessian determinant
of constant sign** and a **longitudinal velocity vanishing** on a curve.  Each
sign realizes exactly one of the two possible degeneracies.
-/

section Exchange

variable {α ξ η : ℝ}

/-! ### Defocusing: elliptic longitudinal velocity -/

/-- `∂_ξ ω_+ ∼ ρ_α`, with the explicit two-sided constants `1` and `α+1`. -/
theorem velX_defocusing_comparable (hξ : 0 < ξ) (hα : 1 ≤ α) :
    rho α ξ η ≤ velX α 1 ξ η ∧ velX α 1 ξ η ≤ (α + 1) * rho α ξ η := by
  have hxa : (0:ℝ) < ξ ^ α := Real.rpow_pos_of_pos hξ α
  rw [rho_of_pos hξ, velX_defocusing]
  constructor
  · nlinarith [sq_nonneg η, hxa]
  · nlinarith [sq_nonneg η, hxa]

/-- In particular `∂_ξ ω_+ > 0` everywhere on `ξ > 0`: the defocusing
longitudinal velocity never vanishes. -/
theorem velX_defocusing_pos (hξ : 0 < ξ) (hα : 1 ≤ α) : 0 < velX α 1 ξ η := by
  have h := (velX_defocusing_comparable (η := η) hξ hα).1
  have := rho_pos (α := α) (η := η) hξ
  linarith

/-! ### Defocusing: the Hessian fold `Γ⁺_α = {2η² = α(α+1)|ξ|^α}` -/

/-- The vanishing locus of `det D²ω_+` is exactly `Γ⁺_α`. -/
theorem hessDet_defocusing_eq_zero_iff (_hξ : 0 < ξ) :
    hessDet α 1 ξ η = 0 ↔ 2 * η ^ 2 = α * (α + 1) * ξ ^ α := by
  rw [hessDet_defocusing]
  constructor <;> intro h <;> linarith

/-- On `Γ⁺_α` one has `|ξ|^α ∼ η² ∼ ρ_α`, the statement used in the proof of
`prop:exchange` to conclude that `Γ⁺_α ∩ 𝒜_H` traverses the corner block. -/
theorem gamma_plus_balanced (hξ : 0 < ξ) (_hα : 1 ≤ α)
    (hΓ : 2 * η ^ 2 = α * (α + 1) * ξ ^ α) :
    η ^ 2 = (α * (α + 1) / 2) * ξ ^ α ∧
    rho α ξ η = (1 + α * (α + 1) / 2) * ξ ^ α := by
  have h1 : η ^ 2 = (α * (α + 1) / 2) * ξ ^ α := by linarith
  refine ⟨h1, ?_⟩
  rw [rho_of_pos hξ, h1]; ring

/-- Transversality of the fold: `∂_ξ(det D²ω_+) = 2α²(α+1)ξ^{α−1} ≠ 0`.
**[BB-DIFF]** for the derivative formula; the nonvanishing is proved. -/
noncomputable def dHessDetDefocusing (α ξ : ℝ) : ℝ := 2 * α ^ 2 * (α + 1) * ξ ^ (α - 1)

theorem dHessDetDefocusing_pos (hξ : 0 < ξ) (hα : 1 ≤ α) :
    0 < dHessDetDefocusing α ξ := by
  unfold dHessDetDefocusing
  have hp : (0:ℝ) < ξ ^ (α - 1) := Real.rpow_pos_of_pos hξ _
  have hc : (0:ℝ) < 2 * α ^ 2 * (α + 1) := by nlinarith
  exact mul_pos hc hp

/-! ### Focusing: Hessian determinant of constant sign, comparable to `ρ_α` -/

/-- `det D²ω_-` is strictly negative on `ξ > 0`, `α ≥ 1`: the two terms have the
same sign, so there is **no fold** for the focusing phase. -/
theorem hessDet_focusing_neg (hξ : 0 < ξ) (hα : 1 ≤ α) : hessDet α (-1) ξ η < 0 := by
  rw [hessDet_focusing]
  have hxa : (0:ℝ) < ξ ^ α := Real.rpow_pos_of_pos hξ α
  have hc : (0:ℝ) < 2 * α * (α + 1) := by nlinarith
  have hpos : (0:ℝ) < 2 * α * (α + 1) * ξ ^ α := mul_pos hc hxa
  linarith [sq_nonneg η]

/-- `|det D²ω_-| ∼ |ξ|^α + η² = ρ_α`, with explicit constants `2` and
`2α(α+1) + 4`.  This is the "uniform linear curvature" of the focusing phase. -/
theorem hessDet_focusing_comparable (hξ : 0 < ξ) (hα : 1 ≤ α) :
    2 * rho α ξ η ≤ |hessDet α (-1) ξ η| ∧
    |hessDet α (-1) ξ η| ≤ (2 * α * (α + 1) + 4) * rho α ξ η := by
  have hxa : (0:ℝ) < ξ ^ α := Real.rpow_pos_of_pos hξ α
  have hneg : hessDet α (-1) ξ η < 0 := hessDet_focusing_neg hξ hα
  have habs : |hessDet α (-1) ξ η| = 2 * α * (α + 1) * ξ ^ α + 4 * η ^ 2 := by
    rw [abs_of_neg hneg, hessDet_focusing]; ring
  rw [habs, rho_of_pos hξ]
  have hlow : (0:ℝ) ≤ (α * (α + 1) - 1) * ξ ^ α :=
    mul_nonneg (by nlinarith) (le_of_lt hxa)
  have hhigh : (0:ℝ) ≤ (2 * α * (α + 1)) * η ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg η)
  constructor
  · linarith [hlow, sq_nonneg η]
  · linarith [hhigh, hxa]

/-! ### Focusing: the characteristic curve `Γ⁻_α = {η² = (α+1)|ξ|^α}` -/

/-- The vanishing locus of the focusing longitudinal velocity is exactly
`Γ⁻_α`. -/
theorem velX_focusing_eq_zero_iff (_hξ : 0 < ξ) :
    velX α (-1) ξ η = 0 ↔ η ^ 2 = (α + 1) * ξ ^ α := by
  rw [velX_focusing]
  constructor <;> intro h <;> linarith

/-- On `Γ⁻_α` the transverse velocity is elliptic: `|∂_η ω_-| = 2|ξη| > 0`,
since `η ≠ 0` there. -/
theorem velY_ne_zero_on_gamma_minus (hξ : 0 < ξ) (hα : 1 ≤ α)
    (hΓ : η ^ 2 = (α + 1) * ξ ^ α) : velY ξ η ≠ 0 := by
  have hxa : (0:ℝ) < ξ ^ α := Real.rpow_pos_of_pos hξ α
  have hη2 : 0 < η ^ 2 := by nlinarith
  have hη : η ≠ 0 := by
    intro h; rw [h] at hη2; simp at hη2
  unfold velY
  exact mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt hξ)) hη

/-- The focusing phase has **no** fold: `det D²ω_-` never vanishes. -/
theorem hessDet_focusing_ne_zero (hξ : 0 < ξ) (hα : 1 ≤ α) :
    hessDet α (-1) ξ η ≠ 0 := ne_of_lt (hessDet_focusing_neg hξ hα)

/-- The defocusing phase has **no** velocity degeneracy: `∂_ξ ω_+` never
vanishes. -/
theorem velX_defocusing_ne_zero (hξ : 0 < ξ) (hα : 1 ≤ α) :
    velX α 1 ξ η ≠ 0 := ne_of_gt (velX_defocusing_pos hξ hα)

end Exchange

/-! ## The statement of `prop:exchange`, assembled

For `1 ≤ α` and on the half-plane `ξ > 0`:

* the **defocusing** phase has elliptic longitudinal velocity
  (`∂_ξω_+ ∼ ρ_α > 0`, never zero) and a determinant vanishing exactly on
  `Γ⁺_α = {2η² = α(α+1)ξ^α}`;
* the **focusing** phase has a determinant of constant sign with
  `|det D²ω_-| ∼ ρ_α` (never zero) and a longitudinal velocity vanishing
  exactly on `Γ⁻_α = {η² = (α+1)ξ^α}`, on which the transverse velocity is
  nonzero.

Each sign realizes exactly one degeneracy, and they are different ones.
-/
theorem exchange_of_degeneracies {α ξ η : ℝ} (hξ : 0 < ξ) (hα : 1 ≤ α) :
    -- defocusing: velocity elliptic, determinant degenerates on Γ⁺
    (0 < velX α 1 ξ η) ∧
    (hessDet α 1 ξ η = 0 ↔ 2 * η ^ 2 = α * (α + 1) * ξ ^ α) ∧
    -- focusing: determinant elliptic, velocity degenerates on Γ⁻
    (hessDet α (-1) ξ η ≠ 0) ∧
    (velX α (-1) ξ η = 0 ↔ η ^ 2 = (α + 1) * ξ ^ α) :=
  ⟨velX_defocusing_pos hξ hα,
   hessDet_defocusing_eq_zero_iff hξ,
   hessDet_focusing_ne_zero hξ hα,
   velX_focusing_eq_zero_iff hξ⟩

end DGBOZK
