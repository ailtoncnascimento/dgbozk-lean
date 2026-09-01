/-
# Exponent arithmetic for the two-sign dispersion-generalized BO–ZK equations

This file formalizes, with **no black boxes at all**, every numerical exponent
appearing in

  A. C. Nascimento, *Local well-posedness for two-sign dispersion-generalized
  Benjamin–Ono–Zakharov–Kuznetsov equations*.

Nothing here is deep.  That is precisely the point.  These are the quantities on
which every threshold in the paper depends; they are produced in the text by a
chain of substitutions carried out by hand; and a single slip would silently
change a stated theorem without disturbing anything else.  Every identity below
is verified by `ring` / `field_simp` over `ℝ`, *uniformly in the dispersion
parameter* `α`, not at sample values.

Labels `(eq:...)` refer to the equation labels of the LaTeX source.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace DGBOZK

/-! ## §1.5  The two smoothing deficits, `(eq:deficits)` and `(eq:measure)` -/

/-- `δ_α = 1/α − 1/2`.  Defocusing deficit, anisotropic scale. -/
noncomputable def delta (α : ℝ) : ℝ := 1 / α - 1 / 2

/-- `ν_α = 1 − α/2`.  Focusing deficit, isotropic scale. -/
noncomputable def nu (α : ℝ) : ℝ := 1 - α / 2

/-- `d_α = 1/α + 1/2`, the anisotropic dimension: `|𝒜_H| ∼ H^{d_α}`. -/
noncomputable def dAniso (α : ℝ) : ℝ := 1 / α + 1 / 2

/-- `(eq:deficits)`, first form. -/
theorem delta_eq {α : ℝ} (hα : α ≠ 0) : delta α = (2 - α) / (2 * α) := by
  unfold delta
  rw [div_sub_div _ _ hα (two_ne_zero : (2:ℝ) ≠ 0)]
  congr 1 <;> ring

/-- `(eq:deficits)`, second form: `ν_α = α δ_α`. -/
theorem nu_eq_alpha_mul_delta {α : ℝ} (hα : α ≠ 0) : nu α = α * delta α := by
  unfold nu delta; field_simp; ring

theorem delta_pos {α : ℝ} (h₁ : 0 < α) (h₂ : α < 2) : 0 < delta α := by
  rw [delta_eq (ne_of_gt h₁)]
  apply div_pos <;> linarith

theorem nu_pos {α : ℝ} (h : α < 2) : 0 < nu α := by unfold nu; linarith

theorem nu_nonneg {α : ℝ} (h : α ≤ 2) : 0 ≤ nu α := by unfold nu; linarith

/-! ## §1.5  The maximal-function exponent, `(eq:intro-maximal-def)` -/

/-- `κ_α = 1/2 − (2α−1)/(12α)`, the defocusing mixed maximal exponent. -/
noncomputable def kappa (α : ℝ) : ℝ := 1 / 2 - (2 * α - 1) / (12 * α)

/-- The paper's second displayed form of `κ_α`. -/
theorem kappa_eq {α : ℝ} (hα : α ≠ 0) : kappa α = (4 * α + 1) / (12 * α) := by
  unfold kappa; field_simp; ring

/-- "The static exponent is `1/4`, and the excess `κ_α − 1/4 = (α+1)/(12α)` is
exactly the fold deficit." -/
theorem kappa_sub_quarter {α : ℝ} (hα : α ≠ 0) :
    kappa α - 1 / 4 = (α + 1) / (12 * α) := by
  unfold kappa; field_simp; ring

theorem kappa_gt_quarter {α : ℝ} (hα : 0 < α) : 1 / 4 < kappa α := by
  have h : kappa α - 1 / 4 = (α + 1) / (12 * α) := kappa_sub_quarter (ne_of_gt hα)
  have : 0 < (α + 1) / (12 * α) := by apply div_pos <;> linarith
  linarith

/-! ## §1.6  Block exponents and the admissible endpoint, `(eq:E-both)`, `(eq:pstar)` -/

/-- `E⁺_α(p) = (α+2)/(4α) − (α+1)/(αp)`, the defocusing block exponent. -/
noncomputable def Eplus (α p : ℝ) : ℝ := (α + 2) / (4 * α) - (α + 1) / (α * p)

/-- `E⁻_α(p) = (α+2)/4 − (α+1)/p`, the focusing block exponent. -/
noncomputable def Eminus (α p : ℝ) : ℝ := (α + 2) / 4 - (α + 1) / p

/-- `p*_α = 4(α+1)/(α+2)`, the spatial-`L^∞` endpoint. -/
noncomputable def pStar (α : ℝ) : ℝ := 4 * (α + 1) / (α + 2)

theorem pStar_pos {α : ℝ} (hα : 0 < α) : 0 < pStar α := by
  unfold pStar; apply div_pos <;> linarith

/-- Both block exponents vanish at `p*_α`.  This is the assertion of
`(eq:pstar)`; note it holds for *both* signs with the same `p*`. -/
theorem Eplus_pStar {α : ℝ} (hα : 0 < α) : Eplus α (pStar α) = 0 := by
  unfold Eplus pStar
  have h2 : α + 2 ≠ 0 := by positivity
  have h1 : α + 1 ≠ 0 := by positivity
  have hα' : α ≠ 0 := ne_of_gt hα
  field_simp
  ring

theorem Eminus_pStar {α : ℝ} (hα : 0 < α) : Eminus α (pStar α) = 0 := by
  unfold Eminus pStar
  have h2 : α + 2 ≠ 0 := by positivity
  have h1 : α + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem pStar_one : pStar 1 = 8 / 3 := by unfold pStar; norm_num

theorem pStar_two : pStar 2 = 3 := by unfold pStar; norm_num

/-! ## §1.6  Short-time exponents, `(eq:ab)` -/

/-- `a⁺_ϑ(p) = 1/α + E⁺_α(p) + ϑ/p`. -/
noncomputable def aPlus (α ϑ p : ℝ) : ℝ := 1 / α + Eplus α p + ϑ / p

/-- `b⁺_ϑ(p) = a⁺_ϑ(p) − ϑ`. -/
noncomputable def bPlus (α ϑ p : ℝ) : ℝ := aPlus α ϑ p - ϑ

/-- `a⁻_ϑ(p) = 1 + E⁻_α(p) + ϑ/p`. -/
noncomputable def aMinus (α ϑ p : ℝ) : ℝ := 1 + Eminus α p + ϑ / p

/-- `b⁻_ϑ(p) = a⁻_ϑ(p) − ϑ`. -/
noncomputable def bMinus (α ϑ p : ℝ) : ℝ := aMinus α ϑ p - ϑ

/-- `(eq:theta-star)`, defocusing: `ϑ = δ_α` is exactly the balance
`a⁺_ϑ = b⁺_ϑ + δ_α`.  (Definitional, recorded for completeness.) -/
theorem balance_plus (α ϑ p : ℝ) : aPlus α ϑ p = bPlus α ϑ p + ϑ := by
  unfold bPlus; ring

theorem balance_minus (α ϑ p : ℝ) : aMinus α ϑ p = bMinus α ϑ p + ϑ := by
  unfold bMinus; ring

/-- Monotonicity of `a⁺_ϑ` in `p`, the step the paper justifies by
`∂_p a⁺_ϑ(p) = p^{-2}((α+1)/α − ϑ) > 0`.  Here it is proved as an exact
algebraic inequality, with no differentiation. -/
theorem aPlus_strictMono {α ϑ p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hpq : p < q)
    (hϑ : ϑ < (α + 1) / α) : aPlus α ϑ p < aPlus α ϑ q := by
  have hq : 0 < q := lt_trans hp hpq
  have hα' : α ≠ 0 := ne_of_gt hα
  have key : aPlus α ϑ q - aPlus α ϑ p = ((α + 1) / α - ϑ) * (1 / p - 1 / q) := by
    unfold aPlus Eplus
    field_simp
    ring
  have h1 : 0 < (α + 1) / α - ϑ := by linarith
  have h2 : 1 / q < 1 / p := by
    apply one_div_lt_one_div_of_lt hp hpq
  nlinarith [key, h1, h2]

/-- Monotonicity of `a⁻_ϑ` in `p`, from `∂_p a⁻_ϑ(p) = p^{-2}(α+1-ϑ) > 0`. -/
theorem aMinus_strictMono {α ϑ p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hϑ : ϑ < α + 1) : aMinus α ϑ p < aMinus α ϑ q := by
  have hq : 0 < q := lt_trans hp hpq
  have key : aMinus α ϑ q - aMinus α ϑ p = ((α + 1) - ϑ) * (1 / p - 1 / q) := by
    unfold aMinus Eminus
    field_simp
    ring
  have h1 : 0 < (α + 1) - ϑ := by linarith
  have h2 : 1 / q < 1 / p := one_div_lt_one_div_of_lt hp hpq
  nlinarith [key, h1, h2]

/-! ## §1.6  The three defocusing exponents, `(eq:three-ell)`, `(eq:binding-ell)` -/

/-- `𝖱_{α,0} = (3−α)/(2α)`: the defocusing branch away from the fold, `p ↓ 2`. -/
noncomputable def R0 (α : ℝ) : ℝ := (3 - α) / (2 * α)

/-- `𝖱_{α,1} = 3(4−α)/(8α)`: the defocusing fold branch, `p ↓ 12/5`. -/
noncomputable def R1 (α : ℝ) : ℝ := 3 * (4 - α) / (8 * α)

/-- `𝖪_α = (13−2α)/(12α)`: the maximal-estimate contribution. -/
noncomputable def Kfold (α : ℝ) : ℝ := (13 - 2 * α) / (12 * α)

/-- `𝖲_{α,0} = (3−α)/2`, `(eq:three-hyp)`. -/
noncomputable def S0 (α : ℝ) : ℝ := (3 - α) / 2

/-- **The regular defocusing branch.**  `a⁺_{δ_α}(2) = (3−α)/(2α) = 𝖱_{α,0}`.
This is the first assertion of the proof of `Prop:refined-opt`. -/
theorem aPlus_delta_two {α : ℝ} (hα : 0 < α) : aPlus α (delta α) 2 = R0 α := by
  unfold aPlus Eplus delta R0
  have hα' : α ≠ 0 := ne_of_gt hα
  field_simp
  ring

/-- **The defocusing fold branch.**  `a⁺_{δ_α}(12/5) = 3(4−α)/(8α) = 𝖱_{α,1}`.
This is the exponent that becomes the main threshold `r⁺_α`. -/
theorem aPlus_delta_twelveFifths {α : ℝ} (hα : 0 < α) :
    aPlus α (delta α) (12 / 5) = R1 α := by
  unfold aPlus Eplus delta R1
  have hα' : α ≠ 0 := ne_of_gt hα
  field_simp
  ring

/-- `𝖪_α = κ_α + δ_α`: the maximal exponent plus the defocusing deficit.
This is the quantity that must be admissible in `Prop:coupled`. -/
theorem Kfold_eq_kappa_add_delta {α : ℝ} (hα : α ≠ 0) :
    Kfold α = kappa α + delta α := by
  unfold Kfold kappa delta; field_simp; ring

/-- `(eq:binding-ell)`, first identity: the fold costs exactly `1/8`, **uniformly
in `α`**.  This is the single most load-bearing arithmetic claim of the
defocusing analysis: it is what makes the fold branch binding. -/
theorem R1_sub_R0 {α : ℝ} (hα : α ≠ 0) : R1 α - R0 α = 1 / 8 := by
  unfold R1 R0; field_simp; ring

/-- `(eq:binding-ell)`, second identity. -/
theorem R1_sub_Kfold {α : ℝ} (hα : α ≠ 0) :
    R1 α - Kfold α = 5 * (2 - α) / (24 * α) := by
  unfold R1 Kfold; field_simp; ring

/-- The maximal contribution is strictly below the fold threshold on the whole
range `1 ≤ α < 2`.  This is what licenses the choice of `γ = κ_α + ε₀` in the
second line of `Prop:coupled`. -/
theorem Kfold_lt_R1 {α : ℝ} (h₁ : 0 < α) (h₂ : α < 2) : Kfold α < R1 α := by
  have h : R1 α - Kfold α = 5 * (2 - α) / (24 * α) := R1_sub_Kfold (ne_of_gt h₁)
  have : 0 < 5 * (2 - α) / (24 * α) := by apply div_pos <;> linarith
  linarith

/-! ## §1.6  The focusing exponents, `(eq:three-hyp)` -/

/-- `a⁻_{ν_α}(2) = (3−α)/2 = 𝖲_{α,0}`. -/
theorem aMinus_nu_two {α : ℝ} : aMinus α (nu α) 2 = S0 α := by
  unfold aMinus Eminus nu S0; ring

/-- `b⁻_{ν_α}(2) = 1/2 = 𝖲_{α,1}`, the focusing forcing exponent. -/
theorem bMinus_nu_two {α : ℝ} : bMinus α (nu α) 2 = 1 / 2 := by
  unfold bMinus aMinus Eminus nu; ring

/-- The focusing exponents are at most one on `1 ≤ α`, which is why the strict
normal-form condition `s > 1` is the binding one. -/
theorem S0_le_one {α : ℝ} (h : 1 ≤ α) : S0 α ≤ 1 := by unfold S0; linarith

/-! ## §1.5  The main thresholds and the comparison with Ribaud–Vento -/

/-- `r⁺_α = 3(4−α)/(8α)`, the threshold of Theorem 1.1(ii), `(eq:rdef)`. -/
noncomputable def rPlus (α : ℝ) : ℝ := 3 * (4 - α) / (8 * α)

/-- `r̃_α = 2/α − 3/4`, the threshold of Ribaud–Vento (2017). -/
noncomputable def rRV (α : ℝ) : ℝ := 2 / α - 3 / 4

theorem rPlus_eq_R1 (α : ℝ) : rPlus α = R1 α := rfl

/-- `(eq:RV-comparison)`: `r⁺_α − r̃_α = (3α−4)/(8α)`.  Sign-sensitive: the whole
claim of improvement is the sign of the numerator. -/
theorem rPlus_sub_rRV {α : ℝ} (hα : α ≠ 0) :
    rPlus α - rRV α = (3 * α - 4) / (8 * α) := by
  unfold rPlus rRV; field_simp; ring

/-- **The improvement.**  On `1 ≤ α < 4/3` the new threshold is strictly lower
than that of Ribaud–Vento. -/
theorem rPlus_lt_rRV {α : ℝ} (h₁ : 0 < α) (h₂ : α < 4 / 3) : rPlus α < rRV α := by
  have h : rPlus α - rRV α = (3 * α - 4) / (8 * α) := rPlus_sub_rRV (ne_of_gt h₁)
  have hnum : 3 * α - 4 < 0 := by linarith
  have hden : (0:ℝ) < 8 * α := by linarith
  have : (3 * α - 4) / (8 * α) < 0 := div_neg_of_neg_of_pos hnum hden
  linarith

/-- At `α = 4/3` the two exponents coincide. -/
theorem rPlus_eq_rRV_at_four_thirds : rPlus (4 / 3) = rRV (4 / 3) := by
  unfold rPlus rRV; norm_num

/-- The BO–ZK endpoint values quoted in the text: `9/8` against `5/4`. -/
theorem rPlus_one : rPlus 1 = 9 / 8 := by unfold rPlus; norm_num

theorem rRV_one : rRV 1 = 5 / 4 := by unfold rRV; norm_num

/-- "`r⁺_α < 1/2` only when `α > 12/7`", the statement behind the paper's
refusal to claim any enlargement of the global range. -/
theorem rPlus_lt_half_iff {α : ℝ} (hα : 0 < α) : rPlus α < 1 / 2 ↔ 12 / 7 < α := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have key : 1 / 2 - rPlus α = (14 * α - 24) / (16 * α) := by
    unfold rPlus; field_simp; ring
  have h16 : (0:ℝ) < 16 * α := by linarith
  constructor
  · intro h
    have hpos : 0 < (14 * α - 24) / (16 * α) := by linarith
    have hmul : (14 * α - 24) / (16 * α) * (16 * α) = 14 * α - 24 := by
      field_simp
    nlinarith [mul_pos hpos h16]
  · intro h
    have hnum : 0 < 14 * α - 24 := by linarith
    have : 0 < (14 * α - 24) / (16 * α) := div_pos hnum h16
    linarith

/-! ## §1.3 and §9.2  Scaling, criticality and the lifespan exponent -/

/-- The exponent in `‖u_λ(0)‖_{Ė^r_α} = λ^{αr + 3α/4 − 1/2}‖u_0‖`,
`(eq:hom-scaling)`. -/
noncomputable def scalingExp (α r : ℝ) : ℝ := α * r + 3 * α / 4 - 1 / 2

/-- `r_c = 1/(2α) − 3/4`, the scaling-critical anisotropic index. -/
noncomputable def rCrit (α : ℝ) : ℝ := 1 / (2 * α) - 3 / 4

/-- `r_c` is exactly the zero of the scaling exponent. -/
theorem scalingExp_rCrit {α : ℝ} (hα : α ≠ 0) : scalingExp α (rCrit α) = 0 := by
  unfold scalingExp rCrit; field_simp; ring

/-- `r_c < 0` on the range `1 ≤ α` used in the paper: the problem is subcritical
in `E^r_α` for every `r ≥ 0`, as asserted after `(eq:hom-scaling)`.

Note the hypothesis is `1 ≤ α`, not merely `α > 0`: for `α ≤ 2/3` one has
`r_c ≥ 0`.  The paper's range `1 ≤ α ≤ 2` is comfortably inside. -/
theorem rCrit_neg {α : ℝ} (hα : 1 ≤ α) : rCrit α < 0 := by
  unfold rCrit
  have h : 1 / (2 * α) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- The lifespan exponent `4(α+1)/(3α−2)` of `(eq:intro-lifespan)`. -/
noncomputable def lifespanExp (α : ℝ) : ℝ := 4 * (α + 1) / (3 * α - 2)

/-- The exponent in the scaling parameter `λ = c(1+R)^{-4/(3α−2)}`,
`(eq:lambda-choice)`. -/
noncomputable def lambdaExp (α : ℝ) : ℝ := 4 / (3 * α - 2)

/-- Undoing the scaling multiplies the lifespan exponent by `α+1`:
`T ∼ λ^{α+1}` gives exactly `(eq:lifespan)`. -/
theorem lifespanExp_eq (α : ℝ) : lifespanExp α = (α + 1) * lambdaExp α := by
  unfold lifespanExp lambdaExp; ring

/-- "at `α = 1` the exponent is `8`." -/
theorem lifespanExp_one : lifespanExp 1 = 8 := by unfold lifespanExp; norm_num

/-- `3α − 2 > 0` for `α ≥ 1`, the legitimacy condition for `(eq:lambda-choice)`. -/
theorem three_alpha_sub_two_pos {α : ℝ} (h : 1 ≤ α) : 0 < 3 * α - 2 := by linarith

/-! ## §8  Admissibility margins used by `Prop:coupled`

These are the inequalities the paper asserts in passing when it applies the
product estimates.  They are the ones a referee would have to check by hand.
-/

/-- The exponent `γ = r⁺_α − δ_α` used in the first line of `Prop:coupled` is
nonnegative, as `Prop:ell-product` requires.  Indeed `r⁺_α − δ_α = (4+α)/(8α)`. -/
theorem rPlus_sub_delta {α : ℝ} (hα : α ≠ 0) :
    rPlus α - delta α = (4 + α) / (8 * α) := by
  unfold rPlus delta; field_simp; ring

theorem rPlus_sub_delta_pos {α : ℝ} (hα : 0 < α) : 0 < rPlus α - delta α := by
  rw [rPlus_sub_delta (ne_of_gt hα)]
  apply div_pos <;> linarith

/-- **The algebra margin of `Prop:ell-smoothing`.**  The smoothing lemma needs
`τ > d_α/2` (the point at which `E^τ_α` is an algebra and embeds in `L^∞`), and
`τ` may be taken just above `r⁺_α`.  So one needs `r⁺_α > d_α/2`, i.e.
`(8 − 5α)/(8α) > 0`, i.e. `α < 8/5`.  The defocusing range `α < 4/3` is
comfortably inside it — but note the margin closes at `8/5`, not at `2`. -/
theorem rPlus_sub_dAniso_half {α : ℝ} (hα : α ≠ 0) :
    rPlus α - dAniso α / 2 = (8 - 5 * α) / (8 * α) := by
  unfold rPlus dAniso; field_simp; ring

theorem algebra_margin {α : ℝ} (h₁ : 0 < α) (h₂ : α < 8 / 5) :
    dAniso α / 2 < rPlus α := by
  have h : rPlus α - dAniso α / 2 = (8 - 5 * α) / (8 * α) :=
    rPlus_sub_dAniso_half (ne_of_gt h₁)
  have : 0 < (8 - 5 * α) / (8 * α) := by apply div_pos <;> linarith
  linarith

/-- The range actually used in Theorem 1.1(ii) sits strictly inside the algebra
margin. -/
theorem algebra_margin_on_range {α : ℝ} (h₁ : 1 ≤ α) (h₂ : α < 4 / 3) :
    dAniso α / 2 < rPlus α :=
  algebra_margin (by linarith) (by linarith)


end DGBOZK
