/-
# Finite frequency-envelope calculus

This module formalizes the discrete algebra used after the
frequency-resolved energy inequality in the cleaned manuscript.

The index type is finite, as it is for each smooth frequency-truncated
approximation. The block-energy system and its weighted kernel estimate
remain explicit hypotheses.
-/
import DGBOZK.EnergyEnvelope
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace DGBOZK
namespace FrequencyEnvelope

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The squared finite frequency envelope associated with a weight kernel. -/
def envelopeSq (w : ι → ι → ℝ) (a : ι → ℝ) (k : ι) : ℝ :=
  ∑ l, w k l * (a l) ^ 2

/-- A nonnegative kernel produces a nonnegative squared envelope. -/
theorem envelopeSq_nonneg
    {w : ι → ι → ℝ} {a : ι → ℝ}
    (hw : ∀ k l, 0 ≤ w k l) (k : ι) :
    0 ≤ envelopeSq w a k := by
  unfold envelopeSq
  exact Finset.sum_nonneg fun l _ =>
    mul_nonneg (hw k l) (sq_nonneg (a l))

/-- Slow variation of the kernel passes to the squared envelope. -/
theorem envelopeSq_slowVariation
    {w : ι → ι → ℝ} {a : ι → ℝ}
    {R : ι → ι → ℝ}
    (hw : ∀ k l m, w k m ≤ R k l * w l m)
    (k l : ι) :
    envelopeSq w a k ≤ R k l * envelopeSq w a l := by
  unfold envelopeSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  calc
    w k m * (a m) ^ 2
        ≤ (R k l * w l m) * (a m) ^ 2 :=
      mul_le_mul_of_nonneg_right (hw k l m) (sq_nonneg (a m))
    _ = R k l * (w l m * (a m) ^ 2) := by
      ring

/-- A column-sum estimate gives the finite squared ell-two bound. -/
theorem sum_envelopeSq_le
    {w : ι → ι → ℝ} {a : ι → ℝ} {Cw : ℝ}
    (hcolumn : ∀ l, ∑ k, w k l ≤ Cw) :
    ∑ k, envelopeSq w a k ≤ Cw * ∑ l, (a l) ^ 2 := by
  unfold envelopeSq
  calc
    (∑ k, ∑ l, w k l * (a l) ^ 2)
        = ∑ l, (∑ k, w k l) * (a l) ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
    _ ≤ ∑ l, Cw * (a l) ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_right
        (hcolumn l) (sq_nonneg (a l))
    _ = Cw * ∑ l, (a l) ^ 2 := by
      rw [Finset.mul_sum]

/-- A pointwise normalized block bound passes through a nonnegative kernel. -/
theorem weighted_block_sum_le
    {Y cSq : ι → ℝ} {B : ι → ι → ℝ} {Z : ℝ}
    (hB : ∀ k l, 0 ≤ B k l)
    (hmajor : ∀ l, (Y l) ^ 2 ≤ Z * cSq l)
    (k : ι) :
    (∑ l, B k l * (Y l) ^ 2)
      ≤ Z * ∑ l, B k l * cSq l := by
  calc
    (∑ l, B k l * (Y l) ^ 2)
        ≤ ∑ l, B k l * (Z * cSq l) := by
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left
        (hmajor l) (hB k l)
    _ = ∑ l, Z * (B k l * cSq l) := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = Z * ∑ l, B k l * cSq l := by
      rw [Finset.mul_sum]

/--
Finite frequency-envelope propagation from the block system.

The number `Z` represents the largest normalized squared block.
Its existence is kept explicit in `hattain`; it will be constructed
from a finite maximum in the next refinement of this module.
-/
theorem finite_envelope_propagation
    {a Y cSq : ι → ℝ}
    {B : ι → ι → ℝ}
    {C₀ Θ Cβ Z : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hΘ : 0 ≤ Θ)
    (hZ : 0 ≤ Z)
    (hcSq : ∀ k, 0 < cSq k)
    (hdatum : ∀ k, (a k) ^ 2 ≤ cSq k)
    (hB : ∀ k l, 0 ≤ B k l)
    (hrow : ∀ k,
      ∑ l, B k l * cSq l ≤ Cβ * cSq k)
    (hsystem : ∀ k,
      (Y k) ^ 2
        ≤ C₀ * (a k) ^ 2
          + Θ * ∑ l, B k l * (Y l) ^ 2)
    (hmajor : ∀ k,
      (Y k) ^ 2 ≤ Z * cSq k)
    (hattain : ∃ k,
      (Y k) ^ 2 = Z * cSq k)
    (hsmall : Θ * Cβ ≤ 1 / 2) :
    ∀ k, (Y k) ^ 2 ≤ 2 * C₀ * cSq k := by
  rcases hattain with ⟨k₀, hk₀⟩

  have hsum :
      (∑ l, B k₀ l * (Y l) ^ 2)
        ≤ Z * ∑ l, B k₀ l * cSq l :=
    weighted_block_sum_le hB hmajor k₀

  have hsumRow :
      (∑ l, B k₀ l * (Y l) ^ 2)
        ≤ Z * (Cβ * cSq k₀) :=
    hsum.trans
      (mul_le_mul_of_nonneg_left (hrow k₀) hZ)

  have hdata :
      C₀ * (a k₀) ^ 2 ≤ C₀ * cSq k₀ :=
    mul_le_mul_of_nonneg_left (hdatum k₀) hC₀

  have hscaled :
      Z * cSq k₀
        ≤ (C₀ + Θ * Cβ * Z) * cSq k₀ := by
    rw [← hk₀]
    calc
      (Y k₀) ^ 2
          ≤ C₀ * (a k₀) ^ 2
            + Θ * ∑ l, B k₀ l * (Y l) ^ 2 :=
        hsystem k₀
      _ ≤ C₀ * cSq k₀
            + Θ * (Z * (Cβ * cSq k₀)) :=
        add_le_add hdata
          (mul_le_mul_of_nonneg_left hsumRow hΘ)
      _ = (C₀ + Θ * Cβ * Z) * cSq k₀ := by
        ring

  have hscalar :
      Z ≤ C₀ + Θ * Cβ * Z :=
    (mul_le_mul_right (hcSq k₀)).mp hscaled

  have hZbound : Z ≤ 2 * C₀ :=
    quadratic_envelope_closure hZ hsmall hscalar

  intro k
  exact (hmajor k).trans
    (mul_le_mul_of_nonneg_right
      hZbound (le_of_lt (hcSq k)))

end

end FrequencyEnvelope
end DGBOZK
