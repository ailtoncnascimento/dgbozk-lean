import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Ring

/-!
# DGBOZK coordinates

This file fixes the physical and frequency coordinates used by the manuscript.
Both spaces are represented by the Euclidean plane `EuclideanSpace ℝ (Fin 2)`;
the two aliases are kept distinct at the level of exposition, although they
are definitionally equal in Lean.
-/

set_option autoImplicit false

namespace DGBOZK
namespace Foundations

/-- Physical space, with coordinates `(x,y)`. -/
abbrev PhysicalSpace := EuclideanSpace ℝ (Fin 2)

/-- Frequency space, with coordinates `(ξ,η)`. -/
abbrev FrequencySpace := EuclideanSpace ℝ (Fin 2)

/-- Schwartz test functions on the physical space. -/
abbrev TestFunction := SchwartzMap PhysicalSpace ℂ

/-- Construct a physical point from its two coordinates. -/
def physicalPoint (x y : ℝ) : PhysicalSpace := !₂[x, y]

/-- Construct a frequency from its two coordinates. -/
def frequencyPoint (ξ η : ℝ) : FrequencySpace := !₂[ξ, η]

/-- The `x` coordinate of a physical point. -/
def xCoord (z : PhysicalSpace) : ℝ := z.ofLp 0

/-- The `y` coordinate of a physical point. -/
def yCoord (z : PhysicalSpace) : ℝ := z.ofLp 1

/-- The `ξ` coordinate of a frequency. -/
def xiCoord (ζ : FrequencySpace) : ℝ := ζ.ofLp 0

/-- The `η` coordinate of a frequency. -/
def etaCoord (ζ : FrequencySpace) : ℝ := ζ.ofLp 1

/-- The phase pairing `x ξ + y η` used throughout the manuscript. -/
def phasePairing (z : PhysicalSpace) (ζ : FrequencySpace) : ℝ :=
  xCoord z * xiCoord ζ + yCoord z * etaCoord ζ

@[simp] theorem xCoord_physicalPoint (x y : ℝ) :
    xCoord (physicalPoint x y) = x := by
  simp [xCoord, physicalPoint]

@[simp] theorem yCoord_physicalPoint (x y : ℝ) :
    yCoord (physicalPoint x y) = y := by
  simp [yCoord, physicalPoint]

@[simp] theorem xiCoord_frequencyPoint (ξ η : ℝ) :
    xiCoord (frequencyPoint ξ η) = ξ := by
  simp [xiCoord, frequencyPoint]

@[simp] theorem etaCoord_frequencyPoint (ξ η : ℝ) :
    etaCoord (frequencyPoint ξ η) = η := by
  simp [etaCoord, frequencyPoint]

@[simp] theorem phasePairing_points (x y ξ η : ℝ) :
    phasePairing (physicalPoint x y) (frequencyPoint ξ η) =
      x * ξ + y * η := by
  simp [phasePairing]

@[simp] theorem phasePairing_zero_left (ζ : FrequencySpace) :
    phasePairing (0 : PhysicalSpace) ζ = 0 := by
  simp [phasePairing, xCoord, yCoord]

@[simp] theorem phasePairing_zero_right (z : PhysicalSpace) :
    phasePairing z (0 : FrequencySpace) = 0 := by
  simp [phasePairing, xiCoord, etaCoord]

theorem phasePairing_add_left
    (z₁ z₂ : PhysicalSpace) (ζ : FrequencySpace) :
    phasePairing (z₁ + z₂) ζ =
      phasePairing z₁ ζ + phasePairing z₂ ζ := by
  simp [phasePairing, xCoord, yCoord, xiCoord, etaCoord]
  ring

theorem phasePairing_add_right
    (z : PhysicalSpace) (ζ₁ ζ₂ : FrequencySpace) :
    phasePairing z (ζ₁ + ζ₂) =
      phasePairing z ζ₁ + phasePairing z ζ₂ := by
  simp [phasePairing, xCoord, yCoord, xiCoord, etaCoord]
  ring

/-- The anisotropic symbol `ρ_α(ξ,η)=|ξ|^α+η²` from the manuscript. -/
noncomputable def anisotropicSymbol
    (α : ℝ) (ζ : FrequencySpace) : ℝ :=
  |xiCoord ζ| ^ α + etaCoord ζ ^ 2

@[simp] theorem anisotropicSymbol_point (α ξ η : ℝ) :
    anisotropicSymbol α (frequencyPoint ξ η) =
      |ξ| ^ α + η ^ 2 := by
  simp [anisotropicSymbol]

theorem anisotropicSymbol_nonneg (α : ℝ) (ζ : FrequencySpace) :
    0 ≤ anisotropicSymbol α ζ := by
  exact add_nonneg
    (Real.rpow_nonneg (abs_nonneg _) α)
    (sq_nonneg _)

end Foundations
end DGBOZK
