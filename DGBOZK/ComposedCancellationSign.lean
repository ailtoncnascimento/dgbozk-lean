/-
# Composed sign of the localized cubic cancellation (proposal)

The existing library checks the trilinear identity (`TrilinearCancellationCore`)
and a constant-weight flow identity (`Cancellation`) separately.  The step the
manuscript itself singles out as sign-critical (`rem:correction-sign`) is the
*composition*:

1. the bad piece of the low–high nonlinearity produced by the expansion
   `eq:LP-Taylor` is `iξ · H⁻¹ b η e₃` (high input frequency `(ξ,η) = (a₂,b₂)`,
   low frequency `(a,b) = (a₁,b₁)`);
2. the equation `∂ₜu = -𝓛₊u - u uₓ` puts it into `∂ₜ z_H` with a minus sign, and
   `d/dt ∫ b z_H² = 2 ∫ b z_H ∂ₜ z_H` doubles it;
3. the correction `-H⁻¹ T[v, z', z]` differentiated along `∂ₜu = -∂ₓ∂_y²u`
   contributes `+H⁻¹ Σⱼ (D on slot j)`;
4. the weight `b = e^{iρx}` gives `T' = iρ T` and the constraint
   `a₁ + a₂ + a₃ + ρ = 0`.

The theorem below checks, with `I² = -1` used exactly once, that the sum of
(2) and (3) equals the right-hand side of `eq:cancellation-computation`
(common factors `H⁻¹ e₃` removed).  A sign error at any of the four steps makes
it fail.
-/
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace DGBOZK.ComposedCancellation

variable {R : Type*} [CommRing R]

/-- Symbol of the bad term in `d/dt ∫ b z_H²` produced by steps (1)–(2):
`2 · (−(i a₂) · b₁ · b₂)`. -/
def badSym (I a₂ b₁ b₂ : R) : R := 2 * (-((I * a₂) * b₁ * b₂))

/-- Symbol of `d/dt (−H⁻¹ T[v,z',z])` along the transverse flow, step (3). -/
def corrSym (I a₁ a₂ a₃ b₁ b₂ b₃ : R) : R :=
  (I * a₁) * (I * b₁) ^ 2 + (I * a₂) * (I * b₂) ^ 2 + (I * a₃) * (I * b₃) ^ 2

/-- Right-hand side of `eq:cancellation-computation` in symbol form:
`T[∂^A v, ∂^B z', ∂^C z] ↦ (∂^A)(∂^B)(∂^C)` and `T' ↦ (iρ) · T`. -/
def residualSym (I a₁ a₂ a₃ b₁ b₂ b₃ ρ : R) : R :=
  -2 * (I * b₁) ^ 2 * (I * a₂) - (I * b₁) ^ 2 * (I * a₃)
    + (I * a₁) * (I * b₂) * (I * b₃) + (I * a₁) * (I * b₁) * (I * b₃)
    - (I * ρ) * (I * b₁) ^ 2 + (I * ρ) * (I * b₁) * (I * b₃)
    + (I * ρ) * (I * b₂) * (I * b₃)

/-- **Composed cancellation.**  With the manuscript's signs, the bad term plus
the transverse derivative of the correction is exactly the listed residual; no
`T[v_y, z'_{xy}, z]` or `T[v_y, z'_y, z_x]` survives. -/
theorem composed_cancellation (I a₁ a₂ a₃ b₁ b₂ b₃ ρ : R)
    (hI : I ^ 2 = -1) (ha : a₁ + a₂ + a₃ + ρ = 0) (hb : b₁ + b₂ + b₃ = 0) :
    badSym I a₂ b₁ b₂ + corrSym I a₁ a₂ a₃ b₁ b₂ b₃
      = residualSym I a₁ a₂ a₃ b₁ b₂ b₃ ρ := by
  have ha3 : a₃ = -ρ - a₁ - a₂ := by linear_combination ha
  have hb3 : b₃ = -b₁ - b₂ := by linear_combination hb
  subst ha3
  subst hb3
  unfold badSym corrSym residualSym
  linear_combination (-2 * I * a₂ * b₁ * b₂) * hI

/-- With the opposite (positive) correction the bad term is doubled rather than
cancelled: the difference from the residual is `2 · badSym`, which is not
identically zero. -/
theorem wrong_sign_doubles (I a₁ a₂ a₃ b₁ b₂ b₃ ρ : R)
    (hI : I ^ 2 = -1) (ha : a₁ + a₂ + a₃ + ρ = 0) (hb : b₁ + b₂ + b₃ = 0) :
    badSym I a₂ b₁ b₂ - corrSym I a₁ a₂ a₃ b₁ b₂ b₃
      = 2 * badSym I a₂ b₁ b₂ - residualSym I a₁ a₂ a₃ b₁ b₂ b₃ ρ := by
  have h := composed_cancellation I a₁ a₂ a₃ b₁ b₂ b₃ ρ hI ha hb
  linear_combination -h

end DGBOZK.ComposedCancellation
