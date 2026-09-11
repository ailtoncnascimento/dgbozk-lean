/-
# Construction of the maximal normalized frequency block

For a nonempty finite frequency truncation, this module constructs the
largest normalized squared block

  Z = max_k (Y k)^2 / cSq k

and applies the previously verified finite-envelope propagation theorem.

No PDE estimate is asserted here. The frequency-resolved block system and
the weighted kernel estimate remain explicit hypotheses.
-/

import DGBOZK.FrequencyEnvelope

set_option autoImplicit false

namespace DGBOZK
namespace FrequencyEnvelope

noncomputable section

variable {ι : Type*} [Fintype ι]

/--
Finite envelope propagation with the maximal normalized block constructed
internally.

The assumption `[Nonempty ι]` records that the finite frequency truncation
contains at least one block.
-/
theorem finite_envelope_propagation_from_system
    [Nonempty ι]
    {a Y cSq : ι → ℝ}
    {B : ι → ι → ℝ}
    {C₀ Θ Cβ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hΘ : 0 ≤ Θ)
    (hcSq : ∀ k, 0 < cSq k)
    (hdatum : ∀ k, (a k) ^ 2 ≤ cSq k)
    (hB : ∀ k l, 0 ≤ B k l)
    (hrow : ∀ k,
      ∑ l, B k l * cSq l ≤ Cβ * cSq k)
    (hsystem : ∀ k,
      (Y k) ^ 2
        ≤ C₀ * (a k) ^ 2
          + Θ * ∑ l, B k l * (Y l) ^ 2)
    (hsmall : Θ * Cβ ≤ 1 / 2) :
    ∀ k, (Y k) ^ 2 ≤ 2 * C₀ * cSq k := by
  classical

  let q : ι → ℝ :=
    fun k => (Y k) ^ 2 / cSq k

  let kbase : ι :=
    Classical.choice (inferInstance : Nonempty ι)

  have hvalues :
      (Finset.univ.image q).Nonempty := by
    refine ⟨q kbase, ?_⟩
    exact Finset.mem_image.mpr
      ⟨kbase, Finset.mem_univ kbase, rfl⟩

  let Z : ℝ :=
    (Finset.univ.image q).max' hvalues

  have hq_le (k : ι) :
      q k ≤ Z := by
    have hk :
        q k ∈ Finset.univ.image q :=
      Finset.mem_image.mpr
        ⟨k, Finset.mem_univ k, rfl⟩
    simpa [Z] using
      (Finset.le_max' (Finset.univ.image q) (q k) hk)

  have hZmem :
      Z ∈ Finset.univ.image q := by
    simpa [Z] using
      (Finset.max'_mem (Finset.univ.image q) hvalues)

  rcases Finset.mem_image.mp hZmem with
    ⟨k₀, hk₀mem, hk₀⟩

  have hZ : 0 ≤ Z := by
    rw [← hk₀]
    dsimp [q]
    exact div_nonneg
      (sq_nonneg (Y k₀))
      (le_of_lt (hcSq k₀))

  have hmajor :
      ∀ k, (Y k) ^ 2 ≤ Z * cSq k := by
    intro k
    have hratio :
        (Y k) ^ 2 / cSq k ≤ Z := by
      simpa [q] using hq_le k
    exact (div_le_iff₀ (hcSq k)).mp hratio

  have hattain :
      ∃ k, (Y k) ^ 2 = Z * cSq k := by
    refine ⟨k₀, ?_⟩
    have hratio :
        (Y k₀) ^ 2 / cSq k₀ = Z := by
      simpa [q] using hk₀
    exact
      (div_eq_iff (ne_of_gt (hcSq k₀))).mp hratio

  exact finite_envelope_propagation
    hC₀ hΘ hZ hcSq hdatum hB hrow
    hsystem hmajor hattain hsmall

end

end FrequencyEnvelope
end DGBOZK
