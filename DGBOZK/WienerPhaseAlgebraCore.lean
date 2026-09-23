import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Finite algebraic core of the localized Wiener phase

The manuscript's `lem:wiener-phase` uses the nonunital Wiener algebra through
its unitization. This module isolates the norm estimates for the finite
partial sums of its exponential series. The abstract algebra `A` is intended
to be that unitization; the identification with the concrete Fourier algebra,
and the time-maximal kernel estimate are not proved here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace DGBOZK.WienerPhaseAlgebraCore

variable {A : Type*} [NormedRing A]

/-- The coefficient of order `n` before applying the time-dependent scalar
factor. The cutoff is on the left, so no commutativity is needed. -/
theorem norm_cutoff_mul_power_le (χ F : A) (n : ℕ) :
    ‖χ * F ^ n‖ ≤ ‖χ‖ * ‖F‖ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ‖χ * F ^ (n + 1)‖ = ‖(χ * F ^ n) * F‖ := by
          rw [pow_succ, mul_assoc]
        _ ≤ ‖χ * F ^ n‖ * ‖F‖ := norm_mul_le _ _
        _ ≤ (‖χ‖ * ‖F‖ ^ n) * ‖F‖ :=
          mul_le_mul_of_nonneg_right ih (norm_nonneg F)
        _ = ‖χ‖ * ‖F‖ ^ (n + 1) := by rw [pow_succ, mul_assoc]

variable [NormedAlgebra ℂ A]

/-- Scalar coefficients can be inserted without losing the product bound. -/
theorem norm_scalar_cutoff_mul_power_le (χ F : A) (a : ℂ) (n : ℕ) :
    ‖a • (χ * F ^ n)‖ ≤ ‖a‖ * (‖χ‖ * ‖F‖ ^ n) := by
  calc
    ‖a • (χ * F ^ n)‖ ≤ ‖a‖ * ‖χ * F ^ n‖ := norm_smul_le _ _
    _ ≤ ‖a‖ * (‖χ‖ * ‖F‖ ^ n) :=
      mul_le_mul_of_nonneg_left (norm_cutoff_mul_power_le χ F n) (norm_nonneg a)

/-- A finite polynomial phase is bounded by the corresponding sum of scalar
majorants. The exponential coefficients are a later specialization. -/
theorem norm_finite_localized_phase_le
    (χ F : A) (c : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, c n • (χ * F ^ n)‖ ≤
      ∑ n ∈ Finset.range N, ‖c n‖ * (‖χ‖ * ‖F‖ ^ n) := by
  calc
    ‖∑ n ∈ Finset.range N, c n • (χ * F ^ n)‖ ≤
        ∑ n ∈ Finset.range N, ‖c n • (χ * F ^ n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, ‖c n‖ * (‖χ‖ * ‖F‖ ^ n) :=
      Finset.sum_le_sum (fun n _ => norm_scalar_cutoff_mul_power_le χ F (c n) n)


section InfiniteExponential

variable [CompleteSpace A]

/-- Multiplication by a cutoff preserves the sum of the exponential series
in a complex Banach algebra. The concrete Wiener identification remains open. -/
theorem localized_exp_hasSum (χ F : A) (t : ℂ) :
    HasSum
      (fun n : ℕ => χ * ((n.factorial : ℂ)⁻¹ • (t • F) ^ n))
      (χ * NormedSpace.exp ℂ (t • F)) := by
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (t • F)).mul_left χ

end InfiniteExponential


section TimeDerivative

variable [CompleteSpace A]

/-- Abstract complex-time derivative of the localized exponential.
The real-time Wiener phase remains a further specialization. -/
theorem hasDerivAt_localized_exp (χ F : A) (t : ℂ) :
    HasDerivAt
      (fun z : ℂ => χ * NormedSpace.exp ℂ (z • F))
      (χ * (NormedSpace.exp ℂ (t • F) * F)) t := by
  exact (hasDerivAt_exp_smul_const F t).const_mul χ

end TimeDerivative

end DGBOZK.WienerPhaseAlgebraCore
