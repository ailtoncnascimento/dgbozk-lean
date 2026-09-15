/-
# Existence and uniqueness of the positive anisotropic-gauge root

For `1 <= alpha <= 2` and `(xi, eta) != (0, 0)`, this module proves that
there exists a unique positive `rho` satisfying

  xi^2 / rho^(2 / alpha) + eta^2 / rho = 1.

Existence follows from continuity on the explicit interval

  [E / 2, E],  E = |xi|^alpha + eta^2,

and the endpoint inequalities proved in `GaugeExistenceEndpointsCore`.
Uniqueness is supplied by `GaugeUniquenessCore`.

Smooth dependence on `(xi, eta)` is not claimed here.
-/

import DGBOZK.GaugeExistenceEndpointsCore
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace DGBOZK
namespace GaugeExistenceCore

open Set
open GaugeEquationCore
open GaugeExistenceEndpointsCore
open GaugeUniquenessCore

/--
The gauge left side is continuous on every closed interval whose left
endpoint is strictly positive.
-/
theorem gaugeLeftSide_continuousOn
    {alpha xi eta a b : ℝ}
    (ha : 0 < a) :
    ContinuousOn
      (fun rho => gaugeLeftSide alpha xi eta rho)
      (Icc a b) := by
  have hId :
      ContinuousOn (fun rho : ℝ => rho) (Icc a b) :=
    continuous_id.continuousOn
  have hRpow :
      ContinuousOn
        (fun rho : ℝ => rho ^ (2 / alpha))
        (Icc a b) :=
    hId.rpow_const (fun rho hrho => by
      left
      exact ne_of_gt (lt_of_lt_of_le ha hrho.1))
  have hConstX :
      ContinuousOn
        (fun _ : ℝ => xi ^ 2)
        (Icc a b) :=
    continuous_const.continuousOn
  have hConstY :
      ContinuousOn
        (fun _ : ℝ => eta ^ 2)
        (Icc a b) :=
    continuous_const.continuousOn
  have hLongitudinal :
      ContinuousOn
        (fun rho : ℝ =>
          xi ^ 2 / rho ^ (2 / alpha))
        (Icc a b) :=
    hConstX.div hRpow (fun rho hrho => by
      have hrhoPos :
          0 < rho :=
        lt_of_lt_of_le ha hrho.1
      exact ne_of_gt (Real.rpow_pos_of_pos hrhoPos _))
  have hTransverse :
      ContinuousOn
        (fun rho : ℝ => eta ^ 2 / rho)
        (Icc a b) :=
    hConstY.div hId (fun rho hrho => by
      exact ne_of_gt (lt_of_lt_of_le ha hrho.1))
  simpa [gaugeLeftSide] using
    hLongitudinal.add hTransverse

/--
Existence of a positive root of the gauge equation.
-/
theorem exists_positive_gauge_root
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    ∃ rho : ℝ,
      0 < rho
        ∧ gaugeEquation alpha xi eta rho := by
  have halpha : 0 < alpha :=
    lt_of_lt_of_le zero_lt_one halphaOne
  have hEnergyPos :
      0 < anisotropicEnergy alpha xi eta :=
    anisotropicEnergy_pos halpha hnonzero
  have hHalfPos :
      0 < anisotropicEnergy alpha xi eta / 2 := by
    linarith
  have hInterval :
      anisotropicEnergy alpha xi eta / 2
        ≤ anisotropicEnergy alpha xi eta := by
    linarith
  have hContinuous :
      ContinuousOn
        (fun rho =>
          gaugeLeftSide alpha xi eta rho)
        (Icc
          (anisotropicEnergy alpha xi eta / 2)
          (anisotropicEnergy alpha xi eta)) :=
    gaugeLeftSide_continuousOn hHalfPos
  have hUpper :
      gaugeLeftSide alpha xi eta
          (anisotropicEnergy alpha xi eta)
        ≤ 1 :=
    gaugeLeftSide_energy_le_one
      halphaOne halphaTwo hnonzero
  have hLower :
      1 ≤
        gaugeLeftSide alpha xi eta
          (anisotropicEnergy alpha xi eta / 2) :=
    one_le_gaugeLeftSide_half_energy
      halphaOne halphaTwo hnonzero
  have hValue :
      (1 : ℝ) ∈
        Icc
          (gaugeLeftSide alpha xi eta
            (anisotropicEnergy alpha xi eta))
          (gaugeLeftSide alpha xi eta
            (anisotropicEnergy alpha xi eta / 2)) :=
    ⟨hUpper, hLower⟩
  have hImage :
      (1 : ℝ) ∈
        (fun rho =>
          gaugeLeftSide alpha xi eta rho) ''
          Icc
            (anisotropicEnergy alpha xi eta / 2)
            (anisotropicEnergy alpha xi eta) :=
    intermediate_value_Icc'
      hInterval hContinuous hValue
  obtain ⟨rho, hrhoInterval, hrhoEquation⟩ :=
    hImage
  refine ⟨rho, ?_, ?_⟩
  · exact
      lt_of_lt_of_le hHalfPos hrhoInterval.1
  · simpa [gaugeEquation, gaugeLeftSide] using
      hrhoEquation

/--
Existence and uniqueness of the positive gauge root.
-/
theorem existsUnique_positive_gauge_root
    {alpha xi eta : ℝ}
    (halphaOne : 1 ≤ alpha)
    (halphaTwo : alpha ≤ 2)
    (hnonzero : ¬(xi = 0 ∧ eta = 0)) :
    ∃! rho : ℝ,
      0 < rho
        ∧ gaugeEquation alpha xi eta rho := by
  obtain ⟨rho, hrhoPos, hrhoEquation⟩ :=
    exists_positive_gauge_root
      halphaOne halphaTwo hnonzero
  refine ⟨rho, ⟨hrhoPos, hrhoEquation⟩, ?_⟩
  intro candidate hCandidate
  exact
    positive_root_unique
      (lt_of_lt_of_le zero_lt_one halphaOne)
      hCandidate.1
      hrhoPos
      hCandidate.2
      hrhoEquation

end GaugeExistenceCore
end DGBOZK
