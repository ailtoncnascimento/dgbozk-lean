/-
# The anisotropic gauge as an actual function

Using existence and uniqueness of the positive root, this module defines

  anisotropicGauge alpha xi eta

for all real parameters. On the manuscript range `1 <= alpha <= 2`, it is
the unique positive solution of the defining equation away from the origin;
at the origin it is defined to be zero.

This module proves the defining equation, positivity, uniqueness
characterization, and two-sided energy comparison for the resulting function.
-/

import DGBOZK.GaugeExistenceCore

set_option autoImplicit false

namespace DGBOZK
namespace GaugeFunctionCore

open GaugeEquationCore
open GaugeLowerEquivalenceCore
open GaugeUpperEquivalenceCore
open GaugeExistenceCore

/-- The parameter and nonzero-point conditions under which a positive root exists. -/
def ValidGaugePoint
    (alpha xi eta : ℝ) : Prop :=
  1 ≤ alpha
    ∧ alpha ≤ 2
    ∧ ¬(xi = 0 ∧ eta = 0)

/--
The anisotropic gauge. Outside the valid parameter/nonzero-point region it is
set to zero; on the valid region it is the positive root supplied by the
existence theorem.
-/
noncomputable def anisotropicGauge
    (alpha xi eta : ℝ) : ℝ := by
  classical
  exact
    if h : ValidGaugePoint alpha xi eta then
      Classical.choose
        (exists_positive_gauge_root
          h.1 h.2.1 h.2.2)
    else
      0

/-- The manuscript hypotheses produce a valid gauge point. -/
theorem validGaugePoint
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    ValidGaugePoint alpha xi eta :=
  ⟨halphaOne, halphaTwo, hnonzero⟩

/-- The gauge is zero at the spatial-frequency origin. -/
theorem anisotropicGauge_origin
    (alpha : ℝ) :
    anisotropicGauge alpha 0 0 = 0 := by
  classical
  simp [anisotropicGauge, ValidGaugePoint]

/-- The selected gauge is positive away from the origin. -/
theorem anisotropicGauge_pos
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    0 < anisotropicGauge alpha xi eta := by
  classical
  have hvalid :
      ValidGaugePoint alpha xi eta :=
    validGaugePoint halphaOne halphaTwo hnonzero
  rw [anisotropicGauge, dif_pos hvalid]
  exact
    (Classical.choose_spec
      (exists_positive_gauge_root
        hvalid.1 hvalid.2.1 hvalid.2.2)).1

/-- The selected gauge satisfies the defining equation. -/
theorem anisotropicGauge_equation
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    gaugeEquation alpha xi eta
      (anisotropicGauge alpha xi eta) := by
  classical
  have hvalid :
      ValidGaugePoint alpha xi eta :=
    validGaugePoint halphaOne halphaTwo hnonzero
  rw [anisotropicGauge, dif_pos hvalid]
  exact
    (Classical.choose_spec
      (exists_positive_gauge_root
        hvalid.1 hvalid.2.1 hvalid.2.2)).2

/--
Any positive solution of the gauge equation equals the selected gauge.
-/
theorem anisotropicGauge_eq_of_positive_solution
    {alpha xi eta rho : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0))
    (hrho : 0 < rho)
    (hEquation : gaugeEquation alpha xi eta rho) :
    anisotropicGauge alpha xi eta = rho := by
  exact
    GaugeUniquenessCore.positive_root_unique
      (lt_of_lt_of_le zero_lt_one halphaOne)
      (anisotropicGauge_pos
        halphaOne halphaTwo hnonzero)
      hrho
      (anisotropicGauge_equation
        halphaOne halphaTwo hnonzero)
      hEquation

/--
The selected gauge satisfies the complete scalar comparison from
`eq:gauge-equiv`.
-/
theorem anisotropicGauge_energy_equivalence
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    (1 / 2 : ℝ) * (|xi| ^ alpha + eta ^ 2)
        ≤ anisotropicGauge alpha xi eta
      ∧
    anisotropicGauge alpha xi eta
        ≤ |xi| ^ alpha + eta ^ 2 := by
  exact
    gauge_energy_equivalence
      halphaOne
      halphaTwo
      (anisotropicGauge_pos
        halphaOne halphaTwo hnonzero)
      (anisotropicGauge_equation
        halphaOne halphaTwo hnonzero)

end GaugeFunctionCore
end DGBOZK
