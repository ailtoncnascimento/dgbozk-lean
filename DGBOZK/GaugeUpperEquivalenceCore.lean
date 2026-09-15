/-
# Upper equivalence bound for the anisotropic gauge

For `1 <= alpha <= 2`, this module proves from the defining equation

  xi^2 / rho^(2 / alpha) + eta^2 / rho = 1

that

  rho <= |xi|^alpha + eta^2.

Together with `GaugeLowerEquivalenceCore`, this completes the scalar
two-sided estimate in `eq:gauge-equiv`.

Existence, uniqueness, smoothness, homogeneity and derivative estimates for
the gauge remain outside this module.
-/

import DGBOZK.GaugeLowerEquivalenceCore

set_option autoImplicit false

namespace DGBOZK
namespace GaugeUpperEquivalenceCore

open GaugeEquationCore
open GaugeLowerEquivalenceCore

/--
The iterated real power in the longitudinal normalized term collapses to
the ordinary square.
-/
theorem abs_rpow_alpha_then_two_div_alpha
    {alpha xi : ℝ}
    (halpha : 0 < alpha) :
    (|xi| ^ alpha) ^ (2 / alpha)
      = xi ^ 2 := by
  have hexponent :
      alpha * (2 / alpha) = (2 : ℝ) := by
    field_simp [ne_of_gt halpha]
  calc
    (|xi| ^ alpha) ^ (2 / alpha)
        =
      |xi| ^ (alpha * (2 / alpha)) := by
        rw [Real.rpow_mul (abs_nonneg xi)]
    _ = |xi| ^ (2 : ℝ) := by
      rw [hexponent]
    _ = |xi| ^ (2 : ℕ) := Real.rpow_two |xi|
    _ = xi ^ 2 := sq_abs xi

/--
Rewriting of the normalized longitudinal summand in terms of
`|xi|^alpha / rho`.
-/
theorem normalized_longitudinal_term
    {alpha xi rho : ℝ}
    (halpha : 0 < alpha)
    (hrho : 0 < rho) :
    (|xi| ^ alpha / rho) ^ (2 / alpha)
      =
    xi ^ 2 / rho ^ (2 / alpha) := by
  calc
    (|xi| ^ alpha / rho) ^ (2 / alpha)
        =
      (|xi| ^ alpha) ^ (2 / alpha)
        / rho ^ (2 / alpha) := by
          rw [Real.div_rpow
            (Real.rpow_nonneg (abs_nonneg xi) alpha)
            (le_of_lt hrho)]
    _ =
      xi ^ 2 / rho ^ (2 / alpha) := by
        rw [abs_rpow_alpha_then_two_div_alpha halpha]

/--
If `0 <= p <= rho` and `1 <= beta`, then the normalized ratio satisfies

  (p / rho)^beta <= p / rho.
-/
theorem normalized_ratio_rpow_le_self
    {p rho beta : ℝ}
    (hrho : 0 < rho)
    (hpNonneg : 0 ≤ p)
    (hpUpper : p ≤ rho)
    (hbeta : 1 ≤ beta) :
    (p / rho) ^ beta ≤ p / rho := by
  have hratioNonneg :
      0 ≤ p / rho :=
    div_nonneg hpNonneg (le_of_lt hrho)
  have hratioUpper :
      p / rho ≤ 1 := by
    exact (div_le_one hrho).2 hpUpper
  by_cases hpZero : p = 0
  · subst p
    have hbetaPos : 0 < beta :=
      lt_of_lt_of_le zero_lt_one hbeta
    simp [Real.zero_rpow (ne_of_gt hbetaPos)]
  · have hpPos : 0 < p :=
      lt_of_le_of_ne hpNonneg (Ne.symm hpZero)
    have hratioPos : 0 < p / rho :=
      div_pos hpPos hrho
    calc
      (p / rho) ^ beta
          ≤ (p / rho) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge
          hratioPos hratioUpper hbeta
      _ = p / rho := Real.rpow_one (p / rho)

/--
The upper half of the gauge equivalence:

  rho <= |xi|^alpha + eta^2.
-/
theorem rho_le_energy
    {alpha xi eta rho : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    rho ≤ |xi| ^ alpha + eta ^ 2 := by
  have halpha : 0 < alpha :=
    lt_of_lt_of_le zero_lt_one halphaOne
  have hpNonneg :
      0 ≤ |xi| ^ alpha :=
    Real.rpow_nonneg (abs_nonneg xi) alpha
  have hpUpper :
      |xi| ^ alpha ≤ rho :=
    abs_x_rpow_le_rho halpha hrho hEquation
  have hbeta :
      1 ≤ 2 / alpha := by
    apply (le_div_iff₀ halpha).2
    simpa using halphaTwo
  have hpowerBound :
      (|xi| ^ alpha / rho) ^ (2 / alpha)
        ≤ |xi| ^ alpha / rho :=
    normalized_ratio_rpow_le_self
      hrho hpNonneg hpUpper hbeta
  have hNormalizedEquation :
      (|xi| ^ alpha / rho) ^ (2 / alpha)
          + eta ^ 2 / rho
        = 1 := by
    calc
      (|xi| ^ alpha / rho) ^ (2 / alpha)
            + eta ^ 2 / rho
          =
        xi ^ 2 / rho ^ (2 / alpha)
            + eta ^ 2 / rho := by
              rw [normalized_longitudinal_term halpha hrho]
      _ = 1 := hEquation
  have hOneLe :
      1 ≤ |xi| ^ alpha / rho + eta ^ 2 / rho := by
    linarith
  have hCombined :
      |xi| ^ alpha / rho + eta ^ 2 / rho
        =
      (|xi| ^ alpha + eta ^ 2) / rho := by
    field_simp [ne_of_gt hrho]
  rw [hCombined] at hOneLe
  have hScaled :=
    (le_div_iff₀ hrho).mp hOneLe
  simpa using hScaled

/--
The complete scalar two-sided comparison in `eq:gauge-equiv`.
-/
theorem gauge_energy_equivalence
    {alpha xi eta rho : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    (1 / 2 : ℝ) * (|xi| ^ alpha + eta ^ 2)
        ≤ rho
      ∧
    rho ≤ |xi| ^ alpha + eta ^ 2 := by
  have halpha : 0 < alpha :=
    lt_of_lt_of_le zero_lt_one halphaOne
  exact ⟨
    half_energy_le_rho halpha hrho hEquation,
    rho_le_energy halphaOne halphaTwo hrho hEquation
  ⟩

end GaugeUpperEquivalenceCore
end DGBOZK
