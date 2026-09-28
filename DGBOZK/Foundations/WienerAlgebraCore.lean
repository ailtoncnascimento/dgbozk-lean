import Mathlib

/-!
# Wiener-algebra estimates (`lem:wiener`, `eq:wiener-average`, `lem:wiener-phase`)

This module proves, without additional hypotheses, the Wiener-algebra lemmas of
the manuscript:

* `inWiener_abs_rpow_mul_schwartz`, `inWiener_mul_abs_rpow_mul_schwartz`:
  `|ξ|^α χ ∈ A(ℝ)` and `ξ|ξ|^α χ ∈ A(ℝ)` for every `α > 0` and every Schwartz `χ`
  (first part of `lem:wiener`);
* `wienerAverage_uniform`, `wienerAverage_integral`: the two bounds of
  `eq:wiener-average` in `A(ℝ²)` for compactly supported `χ₁, χ₂`;
* `IsWienerKernel.mul`, `IsWienerKernel.exp_mul`: `A(ℝ)` is an algebra, and
  `‖χ e^{c m}‖_A ≤ ‖χ‖_A e^{|c| ‖m‖_A}` (exponentials in the unitization);
* `hasDerivAt_wienerPhase`, `wienerPhase`: `lem:wiener-phase`, with a bound on
  the `t`-derivative that is uniform in `|t| ≤ 1` (this implies the integral
  bound stated in the manuscript).

## Normalization
We use Mathlib's Fourier transform
  `Real.fourierIntegral k w = ∫ x, exp(-2πi x w) k x`.
The manuscript uses `∫ exp(-i x ξ) k x`, i.e. `ξ = 2π w`; membership in the
Wiener algebra is invariant under this dilation, with the same norm.  On `ℝ²`
the transform is written in coordinates `(a, b) = (ς, ξ)`.

## Proof strategy
The dyadic argument of the manuscript is replaced by subordination: for
`0 < α < 2` and every real `w`,
  `∫₀^∞ (1 - cos(2π t w)) t^(-1-α) dt = I_α (2π)^α |w|^α`,
where `I_α = ∫₀^∞ (1 - cos t) t^(-1-α) dt ∈ (0, ∞)`.
If `g = 𝓕⁻¹ χ` with `χ` Schwartz, the second difference
  `D_t g = g - (g(·+t) + g(·-t))/2`
has Fourier transform `(1 - cos(2π t w)) χ(w)` and `‖D_t g‖₁ ≤ C min(1, t²)`.
Hence `k = (I_α (2π)^α)⁻¹ ∫₀^∞ t^(-1-α) D_t g dt` is integrable and
`𝓕 k = |w|^α χ` by Fubini.  For `α ≥ 2` write `|w|^α = |w|^(α-2) w²`.
The two-dimensional bounds expand `G(ξ + sς) = ∫ Ǧ(y) e^{-2πi y(ξ + sς)} dy`
with `G = |·|^α ψ`, `ψ = 1` on the relevant compact set.  The phase lemma uses
convolution of kernels and the exponential series summed in `L¹(ℝ)`.
-/

noncomputable section

open MeasureTheory Real

set_option autoImplicit false

namespace DGBOZK.Foundations.WienerAlgebraCore

/-! ## 1. The Wiener algebra on `ℝ` -/

/-- `k` is an integrable kernel whose (Mathlib-normalized) Fourier transform
is `m`. -/
structure IsWienerKernel (m k : ℝ → ℂ) : Prop where
  integrable : Integrable k
  fourier_eq : ∀ w, m w = Real.fourierIntegral k w

/-- `m ∈ A(ℝ)`. -/
abbrev InWiener (m : ℝ → ℂ) : Prop :=
  ∃ k : ℝ → ℂ, IsWienerKernel m k

/-- `‖m‖_{A(ℝ)} ≤ C`. -/
abbrev WienerBound (m : ℝ → ℂ) (C : ℝ) : Prop :=
  ∃ k : ℝ → ℂ, IsWienerKernel m k ∧ ∫ x, ‖k x‖ ≤ C

/-- Changing the multiplier and the kernel pointwise. -/
theorem IsWienerKernel.congr {m m' k k' : ℝ → ℂ} (h : IsWienerKernel m k)
    (hm : ∀ w, m w = m' w) (hk : ∀ x, k x = k' x) :
    IsWienerKernel m' k' := by
  have hkk : k = k' := funext hk
  subst hkk
  exact ⟨h.integrable, fun w => (hm w).symm.trans (h.fourier_eq w)⟩

/-- Sum of two Wiener kernels. -/
theorem IsWienerKernel.add {m₁ m₂ k₁ k₂ : ℝ → ℂ}
    (h₁ : IsWienerKernel m₁ k₁) (h₂ : IsWienerKernel m₂ k₂) :
    IsWienerKernel (fun w => m₁ w + m₂ w) (fun x => k₁ x + k₂ x) := by
  refine ⟨h₁.integrable.add h₂.integrable, fun w => ?_⟩
  beta_reduce
  rw [h₁.fourier_eq w, h₂.fourier_eq w]
  simp only [Real.fourierIntegral_eq, smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).2 h₁.integrable)
    ((Real.fourierIntegral_convergent_iff w).2 h₂.integrable)]

/-- Scalar multiple of a Wiener kernel. -/
theorem IsWienerKernel.const_mul {m k : ℝ → ℂ} (c : ℂ)
    (h : IsWienerKernel m k) :
    IsWienerKernel (fun w => c * m w) (fun x => c * k x) := by
  refine ⟨h.integrable.const_mul c, fun w => ?_⟩
  beta_reduce
  rw [h.fourier_eq w]
  simp only [Real.fourierIntegral_eq, ← smul_eq_mul (a := c), smul_comm _ c,
    integral_smul]

/-- Translation of the kernel becomes modulation of the multiplier. -/
theorem fourierIntegral_comp_add_const (g : ℝ → ℂ) (t w : ℝ) :
    Real.fourierIntegral (fun x => g (x + t)) w =
      Complex.exp (↑(2 * π * t * w) * Complex.I) * Real.fourierIntegral g w := by
  simp only [Real.fourierIntegral_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun v : ℝ => Complex.exp (↑(-2 * π * (v - t) * w) * Complex.I) * g v) t
  simp only [add_sub_cancel_right] at h
  rw [h]
  congr 1
  funext v
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem IsWienerKernel.comp_add_right {m k : ℝ → ℂ} (t : ℝ)
    (h : IsWienerKernel m k) :
    IsWienerKernel (fun w => Complex.exp (↑(2 * π * t * w) * Complex.I) * m w)
      (fun x => k (x + t)) := by
  refine ⟨h.integrable.comp_add_right t, fun w => ?_⟩
  beta_reduce
  rw [h.fourier_eq w]
  exact (fourierIntegral_comp_add_const k t w).symm

theorem inWiener_add {m₁ m₂ : ℝ → ℂ}
    (h₁ : InWiener m₁) (h₂ : InWiener m₂) :
    InWiener (fun w => m₁ w + m₂ w) := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  exact ⟨_, hk₁.add hk₂⟩

theorem inWiener_const_mul (c : ℂ) {m : ℝ → ℂ} (h : InWiener m) :
    InWiener (fun w => c * m w) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨_, hk.const_mul c⟩

/-- Schwartz functions belong to `A(ℝ)`, with kernel `𝓕⁻¹ χ`. -/
theorem isWienerKernel_schwartz (χ : SchwartzMap ℝ ℂ) :
    IsWienerKernel (fun w => χ w) (Real.fourierIntegralInv (χ : ℝ → ℂ)) := by
  have hsymm := SchwartzMap.fourierTransformCLE_symm_apply ℂ χ
  refine ⟨?_, fun w => ?_⟩
  · rw [← hsymm]
    exact SchwartzMap.integrable _
  · have hF : Integrable (Real.fourierIntegral (χ : ℝ → ℂ)) := by
      simpa using (SchwartzMap.fourierTransformCLE ℂ χ).integrable
    have hinv := Continuous.fourier_inversion_inv χ.continuous χ.integrable hF
    exact (congrFun hinv w).symm

theorem inWiener_schwartz (χ : SchwartzMap ℝ ℂ) :
    InWiener (fun w => χ w) :=
  ⟨_, isWienerKernel_schwartz χ⟩

/-! ## 2. The scalar subordination identity -/

/-- `I_α = ∫₀^∞ (1 - cos t) t^(-1-α) dt`. -/
def subordConst (α : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (1 - Real.cos t) * t ^ (-1 - α)

theorem integrableOn_one_sub_cos_rpow {α : ℝ} (h0 : 0 < α) (h2 : α < 2) :
    IntegrableOn (fun t : ℝ => (1 - Real.cos t) * t ^ (-1 - α))
      (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => (1 - Real.cos t) * t ^ (-1 - α))
      (Set.Ioi 0) :=
    (continuous_const.sub Real.continuous_cos).continuousOn.mul
      (continuousOn_id.rpow_const (fun x hx => Or.inl hx.ne'))
  -- near the origin: `0 ≤ 1 - cos t ≤ t^2/2`, so the integrand is `≤ t^(1-α)/2`
  have hA : IntegrableOn (fun t : ℝ => (1 - Real.cos t) * t ^ (-1 - α))
      (Set.Ioc 0 1) := by
    have hg : IntegrableOn (fun t : ℝ => (1 / 2 : ℝ) * t ^ (1 - α))
        (Set.Ioc 0 1) :=
      Integrable.const_mul
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
          (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 1 - α)))
        (1 / 2)
    refine Integrable.mono' hg
      ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ht.1
    have hc1 : 0 ≤ 1 - Real.cos t := by linarith [Real.cos_le_one t]
    have hc2 : 1 - Real.cos t ≤ t ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
    have hp : 0 < t ^ (-1 - α) := Real.rpow_pos_of_pos htpos _
    have hpow : t ^ (1 - α) = t ^ 2 * t ^ (-1 - α) := by
      rw [← Real.rpow_two, ← Real.rpow_add htpos]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc1 hp.le), hpow]
    nlinarith [mul_le_mul_of_nonneg_right hc2 hp.le]
  -- at infinity: `0 ≤ 1 - cos t ≤ 2`
  have hB : IntegrableOn (fun t : ℝ => (1 - Real.cos t) * t ^ (-1 - α))
      (Set.Ioi 1) := by
    have hg : IntegrableOn (fun t : ℝ => (2 : ℝ) * t ^ (-1 - α)) (Set.Ioi 1) :=
      Integrable.const_mul
        (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - α < -1) zero_lt_one) 2
    refine Integrable.mono' hg
      ((hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hp : 0 < t ^ (-1 - α) := Real.rpow_pos_of_pos htpos _
    have hc1 : 0 ≤ 1 - Real.cos t := by linarith [Real.cos_le_one t]
    have hc2 : 1 - Real.cos t ≤ 2 := by linarith [Real.neg_one_le_cos t]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc1 hp.le)]
    nlinarith [mul_le_mul_of_nonneg_right hc2 hp.le]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact hA.union hB

theorem subordConst_pos {α : ℝ} (h0 : 0 < α) (h2 : α < 2) :
    0 < subordConst α := by
  have hint := integrableOn_one_sub_cos_rpow h0 h2
  have hpos : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      0 < (1 - Real.cos t) * t ^ (-1 - α) := by
    intro t ht
    have hpi : |t| ≤ π := by
      rw [abs_of_pos ht.1]
      linarith [Real.pi_gt_three, ht.2]
    have hcos := Real.cos_le_one_sub_mul_cos_sq hpi
    have hsq : 0 < 2 / π ^ 2 * t ^ 2 :=
      mul_pos (div_pos two_pos (pow_pos Real.pi_pos 2)) (pow_pos ht.1 2)
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos ht.1 _)
  have h01 : 0 < ∫ t in (0 : ℝ)..1, (1 - Real.cos t) * t ^ (-1 - α) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ hpos zero_lt_one
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  rw [intervalIntegral.integral_of_le zero_le_one] at h01
  refine lt_of_lt_of_le h01 ?_
  unfold subordConst
  have hnn : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ (1 - Real.cos t) * t ^ (-1 - α) :=
    fun t ht => mul_nonneg (by linarith [Real.cos_le_one t])
      (Real.rpow_pos_of_pos ht _).le
  exact setIntegral_mono_set hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hnn))
    Set.Ioc_subset_Ioi_self.eventuallyLE

theorem subord_identity {α : ℝ} (h0 : 0 < α) (_h2 : α < 2) (w : ℝ) :
    (∫ t in Set.Ioi (0 : ℝ),
        (1 - Real.cos (2 * π * t * w)) * t ^ (-1 - α)) =
      subordConst α * (2 * π) ^ α * |w| ^ α := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Real.zero_rpow h0.ne']
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = 2 * π * |w| := ⟨_, rfl⟩
  have hb : 0 < b := by
    rw [hb_def]
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 hw)
  have hcos : ∀ t : ℝ, Real.cos (2 * π * t * w) = Real.cos (b * t) := by
    intro t
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · rw [hb_def, abs_of_neg hneg, ← Real.cos_neg]
      congr 1
      ring
    · rw [hb_def, abs_of_pos hpos]
      congr 1
      ring
  have hP : 0 < b ^ (-1 - α) := Real.rpow_pos_of_pos hb _
  have hmain :
      (∫ t in Set.Ioi (0 : ℝ),
          (1 - Real.cos (2 * π * t * w)) * t ^ (-1 - α)) =
        b⁻¹ * (subordConst α / b ^ (-1 - α)) := by
    have h1 :
        (∫ t in Set.Ioi (0 : ℝ),
            (1 - Real.cos (2 * π * t * w)) * t ^ (-1 - α)) =
          ∫ t in Set.Ioi (0 : ℝ),
            (1 - Real.cos (b * t)) * (b * t / b) ^ (-1 - α) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      show (1 - Real.cos (2 * π * t * w)) * t ^ (-1 - α) =
        (1 - Real.cos (b * t)) * (b * t / b) ^ (-1 - α)
      rw [hcos t, mul_div_cancel_left₀ t hb.ne']
    rw [h1, integral_comp_mul_left_Ioi
        (fun u : ℝ => (1 - Real.cos u) * (u / b) ^ (-1 - α)) 0 hb,
      mul_zero, smul_eq_mul, subordConst, ← integral_div]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    show (1 - Real.cos u) * (u / b) ^ (-1 - α) =
      (1 - Real.cos u) * u ^ (-1 - α) / b ^ (-1 - α)
    rw [Real.div_rpow (le_of_lt hu) hb.le]
    ring
  have hkey : b ^ (-1 - α) * b ^ α = b⁻¹ := by
    rw [← Real.rpow_add hb, show (-1 - α + α : ℝ) = -1 by ring,
      Real.rpow_neg_one]
  rw [hmain, mul_assoc (subordConst α),
    ← Real.mul_rpow (mul_pos two_pos Real.pi_pos).le (abs_nonneg w), ← hb_def,
    ← hkey]
  calc b ^ (-1 - α) * b ^ α * (subordConst α / b ^ (-1 - α))
      = subordConst α * b ^ α * (b ^ (-1 - α) / b ^ (-1 - α)) := by ring
    _ = subordConst α * b ^ α := by rw [div_self hP.ne', mul_one]

/-! ## 3. Second differences -/

/-- `D_t g = g - (g(·+t) + g(·-t))/2`. -/
def secondDiff (g : ℝ → ℂ) (t x : ℝ) : ℂ :=
  g x - (g (x + t) + g (x - t)) / 2

/-- The second difference of a Wiener kernel has multiplier
`(1 - cos(2π t w)) m(w)`. -/
theorem IsWienerKernel.secondDiff {m k : ℝ → ℂ} (h : IsWienerKernel m k)
    (t : ℝ) :
    IsWienerKernel
      (fun w => ((1 - Real.cos (2 * π * t * w) : ℝ) : ℂ) * m w)
      (DGBOZK.Foundations.WienerAlgebraCore.secondDiff k t) := by
  have hplus := (h.comp_add_right t).const_mul (-(1 / 2 : ℂ))
  have hminus := (h.comp_add_right (-t)).const_mul (-(1 / 2 : ℂ))
  have hsum := h.add (hplus.add hminus)
  refine hsum.congr (fun w => ?_) (fun x => ?_)
  · beta_reduce
    have hneg : ((2 * π * -t * w : ℝ) : ℂ) = -((2 * π * t * w : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hneg, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos,
      Complex.cos]
    ring
  · beta_reduce
    rw [show x + -t = x - t from (sub_eq_add_neg x t).symm]
    simp only [DGBOZK.Foundations.WienerAlgebraCore.secondDiff]
    ring

/-- Pointwise bound `‖D_t g(x)‖ ≤ M t²` when `‖g''‖ ≤ M` on `[x - t, x + t]`. -/
theorem norm_secondDiff_le_of_deriv2 {g g' g'' : ℝ → ℂ}
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : ∀ y, HasDerivAt g' (g'' y) y)
    {x t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ y ∈ Set.Icc (x - t) (x + t), ‖g'' y‖ ≤ M) :
    ‖secondDiff g t x‖ ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x ⟨by linarith, by linarith⟩)
  -- first step: `‖g'(x + s) - g'(x - s)‖ ≤ 2 M s` for `0 ≤ s ≤ t`
  have hstep : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖g' (x + s) - g' (x - s)‖ ≤ M * (2 * s) := by
    intro s hs
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun r => g' (x - s + r)) (f' := fun r => g'' (x - s + r))
      (a := 0) (b := 2 * s) (C := M)
      (fun r _ => (HasDerivAt.comp_const_add (x - s) r (hg' (x - s + r))).hasDerivWithinAt)
      (fun r hr => hM _ ⟨by linarith [hr.1, hs.2], by linarith [hr.2, hs.2]⟩)
      (2 * s) ⟨by linarith [hs.1], le_refl _⟩
    simp only [add_zero, sub_zero] at key
    rwa [show x - s + 2 * s = x + s by ring] at key
  -- second step: integrate the first step in `s`
  have hh : ∀ s : ℝ, HasDerivAt (fun s => g (x + s) + g (x - s))
      (g' (x + s) - g' (x - s)) s := by
    intro s
    have h1 := HasDerivAt.comp_const_add x s (hg (x + s))
    have h2 := HasDerivAt.comp_const_sub x s (hg (x - s))
    exact (h1.add h2).congr_deriv (sub_eq_add_neg _ _).symm
  have key2 := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => g (x + s) + g (x - s)) (f' := fun s => g' (x + s) - g' (x - s))
    (a := 0) (b := t) (C := M * (2 * t))
    (fun s _ => (hh s).hasDerivWithinAt)
    (fun s hs => (hstep s ⟨hs.1, hs.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hM0))
    t ⟨ht, le_refl t⟩
  simp only [add_zero, sub_zero] at key2
  have e2 : secondDiff g t x = -((g (x + t) + g (x - t) - (g x + g x)) / 2) := by
    simp only [secondDiff]
    ring
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e2, norm_neg, norm_div, h2]
  nlinarith [key2]

/-- Quadratic decay of a Schwartz function on `ℝ`. -/
theorem schwartz_decay_two (G : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ, ∀ y : ℝ, (1 + |y|) ^ 2 * ‖G y‖ ≤ K := by
  refine ⟨2 * (SchwartzMap.seminorm ℝ 0 0 G + SchwartzMap.seminorm ℝ 2 0 G),
    fun y => ?_⟩
  have a0 := SchwartzMap.norm_le_seminorm ℝ G y
  have a2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ G 2 y
  rw [Real.norm_eq_abs] at a2
  nlinarith [mul_nonneg (sq_nonneg (|y| - 1)) (norm_nonneg (G y)), abs_nonneg y]

/-- `‖D_t g‖₁ ≤ C min(1, t²)` for `g` integrable with `g''` of quadratic decay. -/
theorem integral_norm_secondDiff_le_aux {g g' g'' : ℝ → ℂ}
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : ∀ y, HasDerivAt g' (g'' y) y)
    (hint : Integrable g) {K : ℝ} (hK : ∀ y, (1 + |y|) ^ 2 * ‖g'' y‖ ≤ K) :
    ∃ C : ℝ, ∀ t : ℝ, (∫ x, ‖secondDiff g t x‖) ≤ C * min 1 (t ^ 2) := by
  have hI : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num [Module.finrank_self])
  -- `g''` near `x` is bounded by `4K (1 + |x|)^(-2)`
  have hpt : ∀ x y : ℝ, |y - x| ≤ 1 →
      ‖g'' y‖ ≤ 4 * K * (1 + ‖x‖) ^ (-(2 : ℝ)) := by
    intro x y hxy
    have hKy := hK y
    have hx1 : |x| ≤ |y| + 1 := by
      have h := abs_sub_abs_le_abs_sub x y
      rw [abs_sub_comm x y] at h
      linarith
    have hn := norm_nonneg (g'' y)
    have e : (1 + ‖x‖) ^ (-(2 : ℝ)) = 1 / (1 + |x|) ^ 2 := by
      rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, one_div]
    rw [e, mul_one_div, le_div_iff₀ (by positivity)]
    have h1 : 1 + |x| ≤ 2 * (1 + |y|) := by linarith [abs_nonneg y]
    have h3 : (1 + |x|) * (1 + |x|) ≤ (2 * (1 + |y|)) * (2 * (1 + |y|)) :=
      mul_le_mul h1 h1 (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h3 hn]
  refine ⟨max (2 * ∫ x, ‖g x‖) (4 * K * ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))), ?_⟩
  have key : ∀ s : ℝ, 0 ≤ s → (∫ x, ‖secondDiff g s x‖) ≤
      max (2 * ∫ x, ‖g x‖) (4 * K * ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))) *
        min 1 (s ^ 2) := by
    intro s hs
    rcases le_or_gt s 1 with hs1 | hs1
    · -- small `s`: Taylor bound
      have hb : ∀ x, ‖secondDiff g s x‖ ≤
          s ^ 2 * (4 * K * (1 + ‖x‖) ^ (-(2 : ℝ))) := by
        intro x
        rw [mul_comm (s ^ 2)]
        refine norm_secondDiff_le_of_deriv2 hg hg' hs (fun y hy => hpt x y ?_)
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2]
      have hmaj : Integrable
          (fun x : ℝ => s ^ 2 * (4 * K * (1 + ‖x‖) ^ (-(2 : ℝ)))) :=
        (hI.const_mul (4 * K)).const_mul (s ^ 2)
      have h1 : (∫ x, ‖secondDiff g s x‖) ≤
          s ^ 2 * (4 * K * ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))) := by
        calc (∫ x, ‖secondDiff g s x‖)
            ≤ ∫ x : ℝ, s ^ 2 * (4 * K * (1 + ‖x‖) ^ (-(2 : ℝ))) :=
              integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun x => norm_nonneg _) hmaj
                (Filter.Eventually.of_forall hb)
          _ = s ^ 2 * (4 * K * ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))) := by
              rw [integral_const_mul, integral_const_mul]
      have hmin : min 1 (s ^ 2) = s ^ 2 := min_eq_right (by nlinarith)
      rw [hmin]
      nlinarith [mul_le_mul_of_nonneg_right
        (le_max_right (2 * ∫ x, ‖g x‖) (4 * K * ∫ x : ℝ, (1 + ‖x‖) ^ (-(2 : ℝ))))
        (sq_nonneg s)]
    · -- large `s`: translation invariance
      have hgn : Integrable (fun x => ‖g x‖) := hint.norm
      have hp1 : Integrable (fun x => ‖g (x + s)‖) := (hint.comp_add_right s).norm
      have hp2 : Integrable (fun x => ‖g (x - s)‖) := (hint.comp_sub_right s).norm
      have hdiv : Integrable (fun x => (‖g (x + s)‖ + ‖g (x - s)‖) / 2) :=
        (hp1.add hp2).div_const 2
      have hsum : Integrable
          (fun x => ‖g x‖ + (‖g (x + s)‖ + ‖g (x - s)‖) / 2) := hgn.add hdiv
      have hb : ∀ x, ‖secondDiff g s x‖ ≤
          ‖g x‖ + (‖g (x + s)‖ + ‖g (x - s)‖) / 2 := by
        intro x
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        have := norm_add_le (g (x + s)) (g (x - s))
        calc ‖secondDiff g s x‖ ≤ ‖g x‖ + ‖(g (x + s) + g (x - s)) / 2‖ :=
              norm_sub_le _ _
          _ = ‖g x‖ + ‖g (x + s) + g (x - s)‖ / 2 := by rw [norm_div, h2]
          _ ≤ ‖g x‖ + (‖g (x + s)‖ + ‖g (x - s)‖) / 2 := by linarith
      have e1 : (∫ x, ‖g (x + s)‖) = ∫ x, ‖g x‖ :=
        integral_add_right_eq_self (fun x => ‖g x‖) s
      have e2 : (∫ x, ‖g (x - s)‖) = ∫ x, ‖g x‖ :=
        integral_sub_right_eq_self (fun x => ‖g x‖) s
      have h1 : (∫ x, ‖secondDiff g s x‖) ≤ 2 * ∫ x, ‖g x‖ := by
        calc (∫ x, ‖secondDiff g s x‖)
            ≤ ∫ x, (‖g x‖ + (‖g (x + s)‖ + ‖g (x - s)‖) / 2) :=
              integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun x => norm_nonneg _) hsum
                (Filter.Eventually.of_forall hb)
          _ = (∫ x, ‖g x‖) + ((∫ x, ‖g (x + s)‖) + ∫ x, ‖g (x - s)‖) / 2 := by
              rw [integral_add hgn hdiv, integral_div, integral_add hp1 hp2]
          _ = 2 * ∫ x, ‖g x‖ := by rw [e1, e2]; ring
      have hmin : min 1 (s ^ 2) = 1 := min_eq_left (by nlinarith)
      rw [hmin, mul_one]
      exact h1.trans (le_max_left _ _)
  intro t
  have hsym : ∀ x, secondDiff g |t| x = secondDiff g t x := by
    intro x
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht]
      simp only [secondDiff]
      rw [show x + -t = x - t by ring, show x - -t = x + t by ring]
      ring
  have hfun : (fun x => ‖secondDiff g t x‖) = fun x => ‖secondDiff g |t| x‖ :=
    funext fun x => by rw [hsym]
  rw [hfun, ← sq_abs t]
  exact key |t| (abs_nonneg t)

/-- Section 3 for Schwartz functions: `‖D_t g‖₁ ≤ C min(1, t²)`. -/
theorem integral_norm_secondDiff_le (g : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, ∀ t : ℝ,
      (∫ x, ‖secondDiff (fun y => g y) t x‖) ≤ C * min 1 (t ^ 2) := by
  have hd1 : ∀ y, HasDerivAt (fun y => g y) (SchwartzMap.derivCLM ℝ g y) y :=
    fun y => by
      rw [SchwartzMap.derivCLM_apply]
      exact g.differentiableAt.hasDerivAt
  have hd2 : ∀ y, HasDerivAt (fun y => SchwartzMap.derivCLM ℝ g y)
      (SchwartzMap.derivCLM ℝ (SchwartzMap.derivCLM ℝ g) y) y :=
    fun y => by
      rw [SchwartzMap.derivCLM_apply ℝ (SchwartzMap.derivCLM ℝ g)]
      exact (SchwartzMap.derivCLM ℝ g).differentiableAt.hasDerivAt
  obtain ⟨K, hK⟩ :=
    schwartz_decay_two (SchwartzMap.derivCLM ℝ (SchwartzMap.derivCLM ℝ g))
  exact integral_norm_secondDiff_le_aux hd1 hd2 g.integrable hK

/-! ## 4. Main one-dimensional statements -/

/-- `t^(-1-α) min(1, t²)` is integrable on `(0, ∞)` for `0 < α < 2`. -/
theorem integrableOn_rpow_mul_min {α : ℝ} (h0 : 0 < α) (h2 : α < 2) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - α) * min 1 (t ^ 2)) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-1 - α) * min 1 (t ^ 2))
      (Set.Ioi 0) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl hx.ne')).mul
      (continuous_const.min (continuous_pow 2)).continuousOn
  have hA : IntegrableOn (fun t : ℝ => t ^ (-1 - α) * min 1 (t ^ 2))
      (Set.Ioc 0 1) := by
    have hg : IntegrableOn (fun t : ℝ => t ^ (1 - α)) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 1 - α))
    refine Integrable.mono' hg
      ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ht.1
    have hp : 0 < t ^ (-1 - α) := Real.rpow_pos_of_pos htpos _
    have hm0 : 0 ≤ min 1 (t ^ 2) := le_min zero_le_one (sq_nonneg t)
    have hpow : t ^ (1 - α) = t ^ (-1 - α) * t ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_add htpos]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.le hm0), hpow]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hp.le
  have hB : IntegrableOn (fun t : ℝ => t ^ (-1 - α) * min 1 (t ^ 2))
      (Set.Ioi 1) := by
    have hg : IntegrableOn (fun t : ℝ => t ^ (-1 - α)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -1 - α < -1) zero_lt_one
    refine Integrable.mono' hg
      ((hcont.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hp : 0 < t ^ (-1 - α) := Real.rpow_pos_of_pos htpos _
    have hm0 : 0 ≤ min 1 (t ^ 2) := le_min zero_le_one (sq_nonneg t)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.le hm0)]
    calc t ^ (-1 - α) * min 1 (t ^ 2) ≤ t ^ (-1 - α) * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hp.le
      _ = t ^ (-1 - α) := mul_one _
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact hA.union hB

/-- The integrand `(t, x) ↦ t^(-1-α) D_t g(x)` of the subordination kernel. -/
def subordKernel (α : ℝ) (g : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.1 ^ (-1 - α) : ℝ) : ℂ) * secondDiff g p.1 p.2

/-- A Schwartz multiplier has a Schwartz kernel. -/
theorem exists_schwartz_kernel (χ : SchwartzMap ℝ ℂ) :
    ∃ ψ : SchwartzMap ℝ ℂ, IsWienerKernel (fun w => χ w) (fun y => ψ y) :=
  ⟨(SchwartzMap.fourierTransformCLE ℂ).symm χ,
    (isWienerKernel_schwartz χ).congr (fun _ => rfl)
      (fun x => by rw [SchwartzMap.fourierTransformCLE_symm_apply])⟩

/-- Tonelli: the subordination integrand is integrable on `(0,∞) × ℝ`. -/
theorem integrable_subordKernel {α : ℝ} (h0 : 0 < α) (h2 : α < 2)
    {m g : ℝ → ℂ} (hg : IsWienerKernel m g) (hgc : Continuous g) {C : ℝ}
    (hC : ∀ t : ℝ, (∫ x, ‖secondDiff g t x‖) ≤ C * min 1 (t ^ 2)) :
    Integrable (subordKernel α g)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure ℝ)) := by
  have hcont : Continuous (fun p : ℝ × ℝ => secondDiff g p.1 p.2) := by
    simp only [secondDiff]
    exact (hgc.comp continuous_snd).sub
      (((hgc.comp (continuous_snd.add continuous_fst)).add
        (hgc.comp (continuous_snd.sub continuous_fst))).div_const 2)
  have hpow : Measurable (fun p : ℝ × ℝ => p.1 ^ (-1 - α)) :=
    measurable_fst.pow_const (-1 - α)
  have hFm : AEStronglyMeasurable (subordKernel α g)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure ℝ)) :=
    ((Complex.measurable_ofReal.comp hpow).mul hcont.measurable).aestronglyMeasurable
  rw [integrable_prod_iff hFm]
  refine ⟨Filter.Eventually.of_forall fun t =>
    (hg.secondDiff t).integrable.const_mul ((t ^ (-1 - α) : ℝ) : ℂ), ?_⟩
  refine Integrable.mono' ((integrableOn_rpow_mul_min h0 h2).const_mul C)
    hFm.norm.integral_prod_right' ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  show ‖∫ x, ‖subordKernel α g (t, x)‖‖ ≤ C * (t ^ (-1 - α) * min 1 (t ^ 2))
  have hp : 0 < t ^ (-1 - α) := Real.rpow_pos_of_pos ht _
  have hfun : (fun x => ‖subordKernel α g (t, x)‖) =
      fun x => t ^ (-1 - α) * ‖secondDiff g t x‖ := by
    funext x
    show ‖((t ^ (-1 - α) : ℝ) : ℂ) * secondDiff g t x‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
  rw [hfun, integral_const_mul, Real.norm_of_nonneg
    (mul_nonneg hp.le (integral_nonneg fun x => norm_nonneg _))]
  calc t ^ (-1 - α) * ∫ x, ‖secondDiff g t x‖
      ≤ t ^ (-1 - α) * (C * min 1 (t ^ 2)) :=
        mul_le_mul_of_nonneg_left (hC t) hp.le
    _ = C * (t ^ (-1 - α) * min 1 (t ^ 2)) := by ring

/-- `lem:wiener` for `0 < α < 2`, by subordination. -/
theorem inWiener_abs_rpow_mul_schwartz_of_lt_two
    {α : ℝ} (h0 : 0 < α) (h2 : α < 2) (χ : SchwartzMap ℝ ℂ) :
    InWiener (fun w => ((|w| ^ α : ℝ) : ℂ) * χ w) := by
  obtain ⟨ψ, hψ⟩ := exists_schwartz_kernel χ
  obtain ⟨C, hC⟩ := integral_norm_secondDiff_le ψ
  have hFint := integrable_subordKernel h0 h2 hψ ψ.continuous hC
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = subordConst α * (2 * π) ^ α := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hc_def]
    exact mul_pos (subordConst_pos h0 h2)
      (Real.rpow_pos_of_pos (mul_pos two_pos Real.pi_pos) α)
  refine ⟨fun x => ((c⁻¹ : ℝ) : ℂ) *
      ∫ t in Set.Ioi (0 : ℝ), subordKernel α (fun y => ψ y) (t, x), ?_, ?_⟩
  · exact hFint.integral_prod_right.const_mul ((c⁻¹ : ℝ) : ℂ)
  intro w
  -- Fubini: the phase times the integrand is integrable on `ℝ × (0,∞)`
  have hG : Integrable (Function.uncurry fun (v : ℝ) (t : ℝ) =>
      Complex.exp (↑(-2 * π * v * w) * Complex.I) *
        subordKernel α (fun y => ψ y) (t, v))
      ((volume : Measure ℝ).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hs := hFint.swap
    have hph : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (↑(-2 * π * p.1 * w) * Complex.I)) := by fun_prop
    refine hs.norm.mono' (hph.aestronglyMeasurable.mul hs.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    show ‖Complex.exp (↑(-2 * π * p.1 * w) * Complex.I) *
        subordKernel α (fun y => ψ y) (p.2, p.1)‖ ≤
      ‖subordKernel α (fun y => ψ y) (p.2, p.1)‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  -- the inner `x`-integral is the Fourier transform of `D_t ψ`
  have hB : ∀ t : ℝ, (∫ v, Complex.exp (↑(-2 * π * v * w) * Complex.I) *
      subordKernel α (fun y => ψ y) (t, v)) =
      (((1 - Real.cos (2 * π * t * w)) * t ^ (-1 - α) : ℝ) : ℂ) * χ w := by
    intro t
    have hF := (hψ.secondDiff t).fourier_eq w
    rw [Real.fourierIntegral_real_eq_integral_exp_smul] at hF
    simp only [smul_eq_mul] at hF
    have hfun : (fun v => Complex.exp (↑(-2 * π * v * w) * Complex.I) *
        subordKernel α (fun y => ψ y) (t, v)) =
        fun v => ((t ^ (-1 - α) : ℝ) : ℂ) *
          (Complex.exp (↑(-2 * π * v * w) * Complex.I) *
            secondDiff (fun y => ψ y) t v) := by
      funext v
      show Complex.exp (↑(-2 * π * v * w) * Complex.I) *
          (((t ^ (-1 - α) : ℝ) : ℂ) * secondDiff (fun y => ψ y) t v) = _
      ring
    rw [hfun, integral_const_mul, ← hF]
    push_cast
    ring
  have hA : ∀ v : ℝ, Complex.exp (↑(-2 * π * v * w) * Complex.I) *
      (((c⁻¹ : ℝ) : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        subordKernel α (fun y => ψ y) (t, v)) =
      ((c⁻¹ : ℝ) : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (↑(-2 * π * v * w) * Complex.I) *
          subordKernel α (fun y => ψ y) (t, v) := by
    intro v
    rw [integral_const_mul]
    ring
  have hcw : c⁻¹ * (subordConst α * (2 * π) ^ α * |w| ^ α) = |w| ^ α := by
    rw [← hc_def, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  rw [Real.fourierIntegral_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, hA]
  rw [integral_const_mul, integral_integral_swap hG]
  simp only [hB]
  rw [integral_mul_const, integral_complex_ofReal, subord_identity h0 h2 w,
    ← mul_assoc, ← Complex.ofReal_mul, hcw]

/-- Multiplication by the coordinate, `χ ↦ w χ(w)`, on Schwartz space. -/
def mulX (χ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    Complex.ofRealCLM.hasTemperateGrowth χ

theorem mulX_apply (χ : SchwartzMap ℝ ℂ) (w : ℝ) :
    mulX χ w = χ w * (w : ℂ) := rfl

/-- First assertion of `lem:wiener`: `|·|^α χ ∈ A(ℝ)` for every `α > 0`. -/
theorem inWiener_abs_rpow_mul_schwartz
    {α : ℝ} (h0 : 0 < α) (χ : SchwartzMap ℝ ℂ) :
    InWiener (fun w => ((|w| ^ α : ℝ) : ℂ) * χ w) := by
  -- induction: `|w|^α χ = |w|^(α-2) (w² χ)` and `w² χ` is Schwartz
  suffices H : ∀ n : ℕ, ∀ β : ℝ, 0 < β → β < 2 * ((n : ℝ) + 1) →
      ∀ φ : SchwartzMap ℝ ℂ, InWiener (fun w => ((|w| ^ β : ℝ) : ℂ) * φ w) by
    obtain ⟨n, hn⟩ := exists_nat_gt (α / 2)
    exact H n α h0 (by linarith) χ
  intro n
  induction n with
  | zero =>
    intro β hβ0 hβ2 φ
    exact inWiener_abs_rpow_mul_schwartz_of_lt_two hβ0
      (by push_cast at hβ2; linarith) φ
  | succ n ih =>
    intro β hβ0 hβ2 φ
    rcases lt_or_ge β 2 with hβ | hβ
    · exact inWiener_abs_rpow_mul_schwartz_of_lt_two hβ0 hβ φ
    rcases eq_or_lt_of_le hβ with heq | hgt
    · -- `β = 2`: the multiplier is the Schwartz function `w² φ`
      obtain ⟨k, hk⟩ := inWiener_schwartz (mulX (mulX φ))
      refine ⟨k, hk.congr (fun w => ?_) (fun _ => rfl)⟩
      simp only [mulX_apply]
      rw [← heq, Real.rpow_two, sq_abs]
      push_cast
      ring
    · -- `β > 2`: apply the induction hypothesis to `β - 2` and `w² φ`
      obtain ⟨k, hk⟩ := ih (β - 2) (by linarith) (by push_cast at hβ2; linarith)
        (mulX (mulX φ))
      refine ⟨k, hk.congr (fun w => ?_) (fun _ => rfl)⟩
      simp only [mulX_apply]
      rcases eq_or_ne w 0 with hw | hw
      · subst hw
        simp [Real.zero_rpow hβ0.ne']
      · have hwpos : 0 < |w| := abs_pos.2 hw
        have e : |w| ^ β = |w| ^ (β - 2) * w ^ 2 := by
          rw [← sq_abs w, ← Real.rpow_two, ← Real.rpow_add hwpos]
          congr 1
          ring
        rw [e]
        push_cast
        ring

/-- Second assertion of `lem:wiener`: `ξ|ξ|^α χ ∈ A(ℝ)`. -/
theorem inWiener_mul_abs_rpow_mul_schwartz
    {α : ℝ} (h0 : 0 < α) (χ : SchwartzMap ℝ ℂ) :
    InWiener (fun w => (w : ℂ) * ((|w| ^ α : ℝ) : ℂ) * χ w) := by
  obtain ⟨k, hk⟩ := inWiener_abs_rpow_mul_schwartz h0 (mulX χ)
  refine ⟨k, hk.congr (fun w => ?_) (fun _ => rfl)⟩
  simp only [mulX_apply]
  ring

/-! ## 5. The two-dimensional averages (`eq:wiener-average`)

Coordinates on `ℝ²` are `(a, b) = (ς, ξ)`.  The Fourier transform on `ℝ²`
is written in coordinates, with the measure `volume.prod volume`. -/

/-- The character `p ↦ exp(-2πi (p₁ a + p₂ b))` of `ℝ²`. -/
def phase2 (a b : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (↑(-2 * π * (p.1 * a + p.2 * b)) * Complex.I)

theorem norm_phase2 (a b : ℝ) (p : ℝ × ℝ) : ‖phase2 a b p‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem phase2_eq (a b : ℝ) (p : ℝ × ℝ) :
    phase2 a b p = Complex.exp (↑(-2 * π * p.1 * a) * Complex.I) *
      Complex.exp (↑(-2 * π * p.2 * b) * Complex.I) := by
  unfold phase2
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_phase2 (a b : ℝ) : Continuous (phase2 a b) := by
  unfold phase2
  fun_prop

/-- `m ∈ A(ℝ²)` with `‖m‖_A ≤ C`. -/
def WienerBound2 (m : ℝ → ℝ → ℂ) (C : ℝ) : Prop :=
  ∃ k : ℝ × ℝ → ℂ, Integrable k ((volume : Measure ℝ).prod volume) ∧
    (∀ a b, m a b = ∫ p, phase2 a b p * k p ∂((volume : Measure ℝ).prod volume)) ∧
    ∫ p, ‖k p‖ ∂((volume : Measure ℝ).prod volume) ≤ C

/-- Translating a kernel by `c` modulates its multiplier. -/
theorem integral_exp_mul_comp_sub {m ψ : ℝ → ℂ} (h : IsWienerKernel m ψ)
    (c a : ℝ) :
    (∫ x, Complex.exp (↑(-2 * π * x * a) * Complex.I) * ψ (x - c)) =
      Complex.exp (↑(-2 * π * c * a) * Complex.I) * m a := by
  have h1 := fourierIntegral_comp_add_const ψ (-c) a
  rw [Real.fourierIntegral_real_eq_integral_exp_smul] at h1
  simp only [smul_eq_mul, ← sub_eq_add_neg] at h1
  rw [h1, ← h.fourier_eq a, show (2 * π * -c * a : ℝ) = -2 * π * c * a by ring]

/-- The support of a compactly supported function on `ℝ` is bounded. -/
theorem exists_abs_le_of_hasCompactSupport {f : ℝ → ℂ}
    (hf : HasCompactSupport f) : ∃ R : ℝ, ∀ a, f a ≠ 0 → |a| ≤ R := by
  obtain ⟨r, hr⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨r, fun a ha => ?_⟩
  have h := hr (subset_tsupport f ha)
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at h
  exact h

/-- A smooth bump on `ℝ` equal to one on `[-R, R]`. -/
def bumpR (R : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨max R 1, max R 1 + 1, lt_max_of_lt_right zero_lt_one, lt_add_one _⟩

/-- The bump `bumpR R` as a Schwartz function. -/
def schwartzBump (R : ℝ) : SchwartzMap ℝ ℂ where
  toFun u := Complex.ofRealCLM (bumpR R u)
  smooth' := Complex.ofRealCLM.contDiff.comp (bumpR R).contDiff
  decay' := by
    intro k n
    have hf : ContDiff ℝ n (fun u : ℝ => Complex.ofRealCLM (bumpR R u)) :=
      Complex.ofRealCLM.contDiff.comp (bumpR R).contDiff
    have hc : HasCompactSupport (fun u : ℝ => Complex.ofRealCLM (bumpR R u)) :=
      (bumpR R).hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)
    have hg : HasCompactSupport (fun x : ℝ => ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun u : ℝ => Complex.ofRealCLM (bumpR R u)) x‖) :=
      ((hc.iteratedFDeriv n).norm).mul_left (f := fun x : ℝ => ‖x‖ ^ k)
    have hgc : Continuous (fun x : ℝ => ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (fun u : ℝ => Complex.ofRealCLM (bumpR R u)) x‖) :=
      (continuous_norm.pow k).mul hf.continuous_iteratedFDeriv'.norm
    obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hg
    exact ⟨C, fun x => (Real.le_norm_self _).trans (hC x)⟩

theorem schwartzBump_apply (R u : ℝ) :
    schwartzBump R u = ((bumpR R u : ℝ) : ℂ) :=
  Complex.ofRealCLM_apply _

theorem schwartzBump_eq_one {R u : ℝ} (h : |u| ≤ R) : schwartzBump R u = 1 := by
  have h1 : bumpR R u = 1 := (bumpR R).one_of_mem_closedBall (by
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact h.trans (le_max_left _ _))
  rw [schwartzBump_apply, h1, Complex.ofReal_one]

/-- The integrand `(y, p) ↦ g(y) ψ₁(p₁ - s y) ψ₂(p₂ - y)` of the kernel of
`χ₁(a) χ₂(b) G(b + s a)`. -/
def avgKernel (g ψ₁ ψ₂ : ℝ → ℂ) (s : ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  g q.1 * (ψ₁ (q.2.1 - s * q.1) * ψ₂ (q.2.2 - q.1))

theorem integral_norm_avgKernel (g : ℝ → ℂ) (ψ₁ ψ₂ : SchwartzMap ℝ ℂ)
    (s y : ℝ) :
    (∫ p : ℝ × ℝ, ‖avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)‖
        ∂((volume : Measure ℝ).prod volume)) =
      ‖g y‖ * ((∫ x, ‖ψ₁ x‖) * ∫ x, ‖ψ₂ x‖) := by
  have hfun : (fun p : ℝ × ℝ =>
      ‖avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)‖) =
      fun p => ‖g y‖ * (‖ψ₁ (p.1 - s * y)‖ * ‖ψ₂ (p.2 - y)‖) := by
    funext p
    simp only [avgKernel, norm_mul]
  rw [hfun, integral_const_mul,
    integral_prod_mul (fun x => ‖ψ₁ (x - s * y)‖) (fun x => ‖ψ₂ (x - y)‖),
    integral_sub_right_eq_self (fun x => ‖ψ₁ x‖) (s * y),
    integral_sub_right_eq_self (fun x => ‖ψ₂ x‖) y]

theorem integrable_avgKernel {g : ℝ → ℂ} (hg : Integrable g)
    (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) (s : ℝ) :
    Integrable (avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
  have hm : AEStronglyMeasurable (avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) := by
    have h1 : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => g q.1)
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)) :=
      hg.aestronglyMeasurable.comp_fst
    have h2 : Continuous (fun q : ℝ × (ℝ × ℝ) =>
        ψ₁ (q.2.1 - s * q.1) * ψ₂ (q.2.2 - q.1)) :=
      (ψ₁.continuous.comp (by fun_prop)).mul (ψ₂.continuous.comp (by fun_prop))
    exact h1.mul h2.aestronglyMeasurable
  rw [integrable_prod_iff hm]
  constructor
  · exact Filter.Eventually.of_forall fun y =>
      (((ψ₁.integrable (μ := volume)).comp_sub_right (s * y)).mul_prod
        ((ψ₂.integrable (μ := volume)).comp_sub_right y)).const_mul (g y)
  · have hfun : (fun y => ∫ p : ℝ × ℝ, ‖avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)‖
        ∂((volume : Measure ℝ).prod volume)) =
        fun y => ‖g y‖ * ((∫ x, ‖ψ₁ x‖) * ∫ x, ‖ψ₂ x‖) :=
      funext fun y => integral_norm_avgKernel g ψ₁ ψ₂ s y
    rw [hfun]
    exact hg.norm.mul_const _

/-- First half of `eq:wiener-average`: a bound uniform in `s ∈ [0,1]`. -/
theorem wienerAverage_uniform {α : ℝ} (h0 : 0 < α)
    (χ₁ χ₂ : SchwartzMap ℝ ℂ)
    (hc₁ : HasCompactSupport (fun w => χ₁ w))
    (hc₂ : HasCompactSupport (fun w => χ₂ w)) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      WienerBound2
        (fun a b => χ₁ a * χ₂ b * ((|b + s * a| ^ α : ℝ) : ℂ)) C := by
  obtain ⟨R₁, hR₁⟩ := exists_abs_le_of_hasCompactSupport hc₁
  obtain ⟨R₂, hR₂⟩ := exists_abs_le_of_hasCompactSupport hc₂
  obtain ⟨g, hg⟩ := inWiener_abs_rpow_mul_schwartz h0 (schwartzBump (R₁ + R₂))
  obtain ⟨ψ₁, hψ₁⟩ := exists_schwartz_kernel χ₁
  obtain ⟨ψ₂, hψ₂⟩ := exists_schwartz_kernel χ₂
  refine ⟨(∫ y, ‖g y‖) * ((∫ x, ‖ψ₁ x‖) * ∫ x, ‖ψ₂ x‖), fun s hs => ?_⟩
  have hH := integrable_avgKernel hg.integrable ψ₁ ψ₂ s
  refine ⟨fun p => ∫ y : ℝ, avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p),
    hH.integral_prod_right, fun a b => ?_, ?_⟩
  · -- the Fourier identity, by Fubini
    have hE : Integrable (Function.uncurry fun (p : ℝ × ℝ) (y : ℝ) =>
        phase2 a b p * avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p))
        (((volume : Measure ℝ).prod volume).prod volume) := by
      have hs' := hH.swap
      refine hs'.norm.mono'
        (((continuous_phase2 a b).comp continuous_fst).aestronglyMeasurable.mul
          hs'.aestronglyMeasurable) (Filter.Eventually.of_forall fun q => ?_)
      show ‖phase2 a b q.1 *
          avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (q.2, q.1)‖ ≤
        ‖avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (q.2, q.1)‖
      rw [norm_mul, norm_phase2, one_mul]
    have hinner : ∀ y : ℝ, (∫ p : ℝ × ℝ, phase2 a b p *
        avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)
          ∂((volume : Measure ℝ).prod volume)) =
        g y * ((Complex.exp (↑(-2 * π * (s * y) * a) * Complex.I) * χ₁ a) *
          (Complex.exp (↑(-2 * π * y * b) * Complex.I) * χ₂ b)) := by
      intro y
      have hfun : (fun p : ℝ × ℝ => phase2 a b p *
          avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)) =
          fun p => g y *
            ((Complex.exp (↑(-2 * π * p.1 * a) * Complex.I) * ψ₁ (p.1 - s * y)) *
              (Complex.exp (↑(-2 * π * p.2 * b) * Complex.I) * ψ₂ (p.2 - y))) := by
        funext p
        simp only [avgKernel, phase2_eq]
        ring
      rw [hfun, integral_const_mul,
        integral_prod_mul
          (fun x => Complex.exp (↑(-2 * π * x * a) * Complex.I) * ψ₁ (x - s * y))
          (fun x => Complex.exp (↑(-2 * π * x * b) * Complex.I) * ψ₂ (x - y)),
        integral_exp_mul_comp_sub hψ₁ (s * y) a, integral_exp_mul_comp_sub hψ₂ y b]
    have hG := hg.fourier_eq (b + s * a)
    rw [Real.fourierIntegral_real_eq_integral_exp_smul] at hG
    simp only [smul_eq_mul] at hG
    have hfun2 : (fun p : ℝ × ℝ => phase2 a b p *
        ∫ y : ℝ, avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)) =
        fun p => ∫ y : ℝ, phase2 a b p *
          avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p) :=
      funext fun p => (integral_const_mul _ _).symm
    have hfun3 : (fun y : ℝ => ∫ p : ℝ × ℝ, phase2 a b p *
        avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)
          ∂((volume : Measure ℝ).prod volume)) =
        fun y => (χ₁ a * χ₂ b) *
          (Complex.exp (↑(-2 * π * y * (b + s * a)) * Complex.I) * g y) := by
      funext y
      rw [hinner y, show Complex.exp (↑(-2 * π * y * (b + s * a)) * Complex.I) =
          Complex.exp (↑(-2 * π * (s * y) * a) * Complex.I) *
            Complex.exp (↑(-2 * π * y * b) * Complex.I) by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring]
      ring
    show χ₁ a * χ₂ b * ((|b + s * a| ^ α : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, phase2 a b p *
        (∫ y : ℝ, avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p))
          ∂((volume : Measure ℝ).prod volume)
    rw [hfun2, integral_integral_swap hE, hfun3, integral_const_mul, ← hG]
    by_cases hz : χ₁ a * χ₂ b = 0
    · rw [hz]
      ring
    · obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 hz
      have hA := hR₁ a ha
      have hB := hR₂ b hb
      have hbound : |b + s * a| ≤ R₁ + R₂ := by
        obtain ⟨ha1, ha2⟩ := abs_le.1 hA
        obtain ⟨hb1, hb2⟩ := abs_le.1 hB
        have hR1 : 0 ≤ R₁ := (abs_nonneg a).trans hA
        rw [abs_le]
        constructor <;>
          nlinarith [mul_nonneg hs.1 (by linarith : (0 : ℝ) ≤ a + R₁),
            mul_nonneg hs.1 (by linarith : (0 : ℝ) ≤ R₁ - a),
            mul_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hR1]
      rw [schwartzBump_eq_one hbound, mul_one]
  · -- the norm bound, by Tonelli
    calc (∫ p : ℝ × ℝ, ‖∫ y : ℝ, avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)‖
          ∂((volume : Measure ℝ).prod volume))
        ≤ ∫ p : ℝ × ℝ, (∫ y : ℝ, ‖avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)‖)
          ∂((volume : Measure ℝ).prod volume) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
            hH.norm.integral_prod_right
            (Filter.Eventually.of_forall fun p => norm_integral_le_integral_norm _)
      _ = ∫ y : ℝ, ∫ p : ℝ × ℝ, ‖avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)‖
          ∂((volume : Measure ℝ).prod volume) :=
          (integral_integral_swap (f := fun y p =>
            ‖avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)‖) hH.norm).symm
      _ = ∫ y, ‖g y‖ * ((∫ x, ‖ψ₁ x‖) * ∫ x, ‖ψ₂ x‖) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y =>
            integral_norm_avgKernel g ψ₁ ψ₂ s y)
      _ = (∫ y, ‖g y‖) * ((∫ x, ‖ψ₁ x‖) * ∫ x, ‖ψ₂ x‖) := integral_mul_const _ _

/-- The inner `p`-integral in the Fourier identity for `avgKernel`. -/
theorem integral_phase2_avgKernel (g : ℝ → ℂ) {m₁ m₂ : ℝ → ℂ}
    {ψ₁ ψ₂ : SchwartzMap ℝ ℂ}
    (hψ₁ : IsWienerKernel m₁ (fun y => ψ₁ y)) (hψ₂ : IsWienerKernel m₂ (fun y => ψ₂ y))
    (a b s y : ℝ) :
    (∫ p : ℝ × ℝ, phase2 a b p *
        avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)
          ∂((volume : Measure ℝ).prod volume)) =
      g y * ((Complex.exp (↑(-2 * π * (s * y) * a) * Complex.I) * m₁ a) *
        (Complex.exp (↑(-2 * π * y * b) * Complex.I) * m₂ b)) := by
  have hfun : (fun p : ℝ × ℝ => phase2 a b p *
      avgKernel g (fun y => ψ₁ y) (fun y => ψ₂ y) s (y, p)) =
      fun p => g y *
        ((Complex.exp (↑(-2 * π * p.1 * a) * Complex.I) * ψ₁ (p.1 - s * y)) *
          (Complex.exp (↑(-2 * π * p.2 * b) * Complex.I) * ψ₂ (p.2 - y))) := by
    funext p
    simp only [avgKernel, phase2_eq]
    ring
  rw [hfun, integral_const_mul,
    integral_prod_mul
      (fun x => Complex.exp (↑(-2 * π * x * a) * Complex.I) * ψ₁ (x - s * y))
      (fun x => Complex.exp (↑(-2 * π * x * b) * Complex.I) * ψ₂ (x - y)),
    integral_exp_mul_comp_sub hψ₁ (s * y) a, integral_exp_mul_comp_sub hψ₂ y b]

/-- The outer `y`-integral: it produces `χ₁(a) χ₂(b) |b + s a|^α`. -/
theorem integral_avg_symbol {α R₁ R₂ s : ℝ} {g : ℝ → ℂ} (χ₁ χ₂ : SchwartzMap ℝ ℂ)
    (hg : IsWienerKernel
      (fun w => ((|w| ^ α : ℝ) : ℂ) * schwartzBump (R₁ + R₂) w) g)
    (hR₁ : ∀ a, χ₁ a ≠ 0 → |a| ≤ R₁) (hR₂ : ∀ b, χ₂ b ≠ 0 → |b| ≤ R₂)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (a b : ℝ) :
    (∫ y, g y * ((Complex.exp (↑(-2 * π * (s * y) * a) * Complex.I) * χ₁ a) *
        (Complex.exp (↑(-2 * π * y * b) * Complex.I) * χ₂ b))) =
      χ₁ a * χ₂ b * ((|b + s * a| ^ α : ℝ) : ℂ) := by
  have hG := hg.fourier_eq (b + s * a)
  rw [Real.fourierIntegral_real_eq_integral_exp_smul] at hG
  simp only [smul_eq_mul] at hG
  have hfun : (fun y : ℝ => g y *
      ((Complex.exp (↑(-2 * π * (s * y) * a) * Complex.I) * χ₁ a) *
        (Complex.exp (↑(-2 * π * y * b) * Complex.I) * χ₂ b))) =
      fun y => (χ₁ a * χ₂ b) *
        (Complex.exp (↑(-2 * π * y * (b + s * a)) * Complex.I) * g y) := by
    funext y
    rw [show Complex.exp (↑(-2 * π * y * (b + s * a)) * Complex.I) =
        Complex.exp (↑(-2 * π * (s * y) * a) * Complex.I) *
          Complex.exp (↑(-2 * π * y * b) * Complex.I) by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring]
    ring
  rw [hfun, integral_const_mul, ← hG]
  by_cases hz : χ₁ a * χ₂ b = 0
  · rw [hz]
    ring
  · obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 hz
    have hA := hR₁ a ha
    have hB := hR₂ b hb
    have hbound : |b + s * a| ≤ R₁ + R₂ := by
      obtain ⟨ha1, ha2⟩ := abs_le.1 hA
      obtain ⟨hb1, hb2⟩ := abs_le.1 hB
      have hR1 : 0 ≤ R₁ := (abs_nonneg a).trans hA
      rw [abs_le]
      constructor <;>
        nlinarith [mul_nonneg hs.1 (by linarith : (0 : ℝ) ≤ a + R₁),
          mul_nonneg hs.1 (by linarith : (0 : ℝ) ≤ R₁ - a),
          mul_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hR1]
    rw [schwartzBump_eq_one hbound, mul_one]

/-- The integrand of the averaged kernel, as a function of `((s, y), p)`. -/
def avgKernel3 (g ψ₁ ψ₂ : ℝ → ℂ) (w : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ :=
  avgKernel g ψ₁ ψ₂ w.1.1 (w.1.2, w.2)

theorem integrable_avgKernel3 {g : ℝ → ℂ} (hg : Integrable g)
    (ψ₁ ψ₂ : SchwartzMap ℝ ℂ) :
    Integrable (avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y))
      (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)).prod
        ((volume : Measure ℝ).prod volume)) := by
  have hm : AEStronglyMeasurable (avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y))
      (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)).prod
        ((volume : Measure ℝ).prod volume)) := by
    have h1 : AEStronglyMeasurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => g w.1.2)
        (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)).prod
          ((volume : Measure ℝ).prod volume)) :=
      (hg.aestronglyMeasurable.comp_snd
        (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))).comp_fst
    have h2 : Continuous (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
        ψ₁ (w.2.1 - w.1.1 * w.1.2) * ψ₂ (w.2.2 - w.1.2)) :=
      (ψ₁.continuous.comp (by fun_prop)).mul (ψ₂.continuous.comp (by fun_prop))
    exact h1.mul h2.aestronglyMeasurable
  rw [integrable_prod_iff hm]
  constructor
  · exact Filter.Eventually.of_forall fun z =>
      (((ψ₁.integrable (μ := volume)).comp_sub_right (z.1 * z.2)).mul_prod
        ((ψ₂.integrable (μ := volume)).comp_sub_right z.2)).const_mul (g z.2)
  · have hfun : (fun z : ℝ × ℝ =>
        ∫ p : ℝ × ℝ, ‖avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p)‖
          ∂((volume : Measure ℝ).prod volume)) =
        fun z => ‖g z.2‖ * ((∫ x, ‖ψ₁ x‖) * ∫ x, ‖ψ₂ x‖) :=
      funext fun z => integral_norm_avgKernel g ψ₁ ψ₂ z.1 z.2
    rw [hfun]
    exact ((integrable_const (1 : ℝ)).mul_prod
      (hg.norm.mul_const ((∫ x, ‖ψ₁ x‖) * ∫ x, ‖ψ₂ x‖))).congr
      (Filter.Eventually.of_forall fun z => one_mul _)

/-- Second half of `eq:wiener-average`: the `s`-average belongs to `A(ℝ²)`.
The kernel is `∫₀¹ k_s ds`; its norm is finite since the kernel is integrable. -/
theorem wienerAverage_integral {α : ℝ} (h0 : 0 < α)
    (χ₁ χ₂ : SchwartzMap ℝ ℂ)
    (hc₁ : HasCompactSupport (fun w => χ₁ w))
    (hc₂ : HasCompactSupport (fun w => χ₂ w)) :
    ∃ C : ℝ,
      WienerBound2
        (fun a b => χ₁ a * χ₂ b *
          ∫ s in (0 : ℝ)..1, ((|b + s * a| ^ α : ℝ) : ℂ)) C := by
  obtain ⟨R₁, hR₁⟩ := exists_abs_le_of_hasCompactSupport hc₁
  obtain ⟨R₂, hR₂⟩ := exists_abs_le_of_hasCompactSupport hc₂
  obtain ⟨g, hg⟩ := inWiener_abs_rpow_mul_schwartz h0 (schwartzBump (R₁ + R₂))
  obtain ⟨ψ₁, hψ₁⟩ := exists_schwartz_kernel χ₁
  obtain ⟨ψ₂, hψ₂⟩ := exists_schwartz_kernel χ₂
  have hΦ := integrable_avgKernel3 hg.integrable ψ₁ ψ₂
  refine ⟨∫ p : ℝ × ℝ,
      ‖∫ z : ℝ × ℝ, avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p)
        ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ))‖
        ∂((volume : Measure ℝ).prod volume),
    fun p => ∫ z : ℝ × ℝ, avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p)
        ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)),
    hΦ.integral_prod_right, fun a b => ?_, le_rfl⟩
  have hE : Integrable (Function.uncurry fun (p : ℝ × ℝ) (z : ℝ × ℝ) =>
      phase2 a b p * avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p))
      (((volume : Measure ℝ).prod volume).prod
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ))) := by
    have hs' := hΦ.swap
    refine hs'.norm.mono'
      (((continuous_phase2 a b).comp continuous_fst).aestronglyMeasurable.mul
        hs'.aestronglyMeasurable) (Filter.Eventually.of_forall fun q => ?_)
    show ‖phase2 a b q.1 *
        avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (q.2, q.1)‖ ≤
      ‖avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (q.2, q.1)‖
    rw [norm_mul, norm_phase2, one_mul]
  have hfunB : (fun z : ℝ × ℝ => ∫ p : ℝ × ℝ, phase2 a b p *
      avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p)
        ∂((volume : Measure ℝ).prod volume)) =
      fun z => g z.2 *
        ((Complex.exp (↑(-2 * π * (z.1 * z.2) * a) * Complex.I) * χ₁ a) *
          (Complex.exp (↑(-2 * π * z.2 * b) * Complex.I) * χ₂ b)) :=
    funext fun z => integral_phase2_avgKernel g hψ₁ hψ₂ a b z.1 z.2
  have hIz : Integrable (fun z : ℝ × ℝ => g z.2 *
      ((Complex.exp (↑(-2 * π * (z.1 * z.2) * a) * Complex.I) * χ₁ a) *
        (Complex.exp (↑(-2 * π * z.2 * b) * Complex.I) * χ₂ b)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)) := by
    rw [← hfunB]
    exact hE.integral_prod_right
  have hfunA : (fun p : ℝ × ℝ => phase2 a b p *
      ∫ z : ℝ × ℝ, avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p)
        ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ))) =
      fun p => ∫ z : ℝ × ℝ, phase2 a b p *
        avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p)
          ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)) :=
    funext fun p => (integral_const_mul _ _).symm
  show χ₁ a * χ₂ b * (∫ s in (0 : ℝ)..1, ((|b + s * a| ^ α : ℝ) : ℂ)) =
    ∫ p : ℝ × ℝ, phase2 a b p *
      (∫ z : ℝ × ℝ, avgKernel3 g (fun y => ψ₁ y) (fun y => ψ₂ y) (z, p)
        ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)))
      ∂((volume : Measure ℝ).prod volume)
  rw [hfunA, integral_integral_swap hE, hfunB, integral_prod _ hIz,
    intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  exact (integral_avg_symbol χ₁ χ₂ hg hR₁ hR₂ ⟨hs.1.le, hs.2⟩ a b).symm

/-! ## 6. Products and exponentials in `A(ℝ)` (towards `lem:wiener-phase`) -/

/-- Modulating an integrable function keeps it integrable. -/
theorem integrable_exp_mul {f : ℝ → ℂ} (hf : Integrable f) (w : ℝ) :
    Integrable (fun x => Complex.exp (↑(-2 * π * x * w) * Complex.I) * f x) := by
  have hc : Continuous (fun x : ℝ => Complex.exp (↑(-2 * π * x * w) * Complex.I)) := by
    fun_prop
  refine hf.norm.mono' (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Convolution of kernels on `ℝ`. -/
def conv (k₁ k₂ : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, k₁ y * k₂ (x - y)

theorem integrable_conv_integrand {k₁ k₂ : ℝ → ℂ} (h₁ : Integrable k₁)
    (h₂ : Integrable k₂) :
    Integrable (fun p : ℝ × ℝ => k₁ p.2 * k₂ (p.1 - p.2))
      ((volume : Measure ℝ).prod volume) :=
  h₁.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) h₂

theorem integral_norm_conv_le {k₁ k₂ : ℝ → ℂ} (h₁ : Integrable k₁)
    (h₂ : Integrable k₂) :
    (∫ x, ‖conv k₁ k₂ x‖) ≤ (∫ y, ‖k₁ y‖) * ∫ x, ‖k₂ x‖ := by
  have hP := integrable_conv_integrand h₁ h₂
  calc (∫ x, ‖conv k₁ k₂ x‖)
      ≤ ∫ x : ℝ, (∫ y : ℝ, ‖k₁ y * k₂ (x - y)‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          hP.norm.integral_prod_left
          (Filter.Eventually.of_forall fun x => norm_integral_le_integral_norm _)
    _ = ∫ y : ℝ, (∫ x : ℝ, ‖k₁ y * k₂ (x - y)‖) :=
        integral_integral_swap (f := fun x y => ‖k₁ y * k₂ (x - y)‖) hP.norm
    _ = ∫ y : ℝ, ‖k₁ y‖ * ∫ x, ‖k₂ x‖ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          simp only [norm_mul]
          rw [integral_const_mul, integral_sub_right_eq_self (fun x => ‖k₂ x‖) y])
    _ = (∫ y, ‖k₁ y‖) * ∫ x, ‖k₂ x‖ := integral_mul_const _ _

/-- `A(ℝ)` is an algebra: the product of multipliers has the convolution kernel. -/
theorem IsWienerKernel.mul {m₁ m₂ k₁ k₂ : ℝ → ℂ} (h₁ : IsWienerKernel m₁ k₁)
    (h₂ : IsWienerKernel m₂ k₂) :
    IsWienerKernel (fun w => m₁ w * m₂ w) (conv k₁ k₂) := by
  have hP := integrable_conv_integrand h₁.integrable h₂.integrable
  refine ⟨hP.integral_prod_left, fun w => ?_⟩
  have hE : Integrable (Function.uncurry fun (x y : ℝ) =>
      Complex.exp (↑(-2 * π * x * w) * Complex.I) * (k₁ y * k₂ (x - y)))
      ((volume : Measure ℝ).prod volume) := by
    have hph : Continuous (fun q : ℝ × ℝ =>
        Complex.exp (↑(-2 * π * q.1 * w) * Complex.I)) := by fun_prop
    refine hP.norm.mono' (hph.aestronglyMeasurable.mul hP.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => ?_)
    show ‖Complex.exp (↑(-2 * π * q.1 * w) * Complex.I) * (k₁ q.2 * k₂ (q.1 - q.2))‖ ≤
      ‖k₁ q.2 * k₂ (q.1 - q.2)‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hfun : (fun x => Complex.exp (↑(-2 * π * x * w) * Complex.I) * conv k₁ k₂ x) =
      fun x => ∫ y, Complex.exp (↑(-2 * π * x * w) * Complex.I) * (k₁ y * k₂ (x - y)) :=
    funext fun x => (integral_const_mul _ _).symm
  have hinner : (fun y : ℝ => ∫ x : ℝ,
      Complex.exp (↑(-2 * π * x * w) * Complex.I) * (k₁ y * k₂ (x - y))) =
      fun y => (Complex.exp (↑(-2 * π * y * w) * Complex.I) * k₁ y) * m₂ w := by
    funext y
    rw [show (fun x : ℝ => Complex.exp (↑(-2 * π * x * w) * Complex.I) *
        (k₁ y * k₂ (x - y))) =
        fun x => k₁ y * (Complex.exp (↑(-2 * π * x * w) * Complex.I) * k₂ (x - y)) from
      funext fun x => by ring, integral_const_mul, integral_exp_mul_comp_sub h₂ y w]
    ring
  have hF := h₁.fourier_eq w
  rw [Real.fourierIntegral_real_eq_integral_exp_smul] at hF
  simp only [smul_eq_mul] at hF
  show m₁ w * m₂ w = Real.fourierIntegral (conv k₁ k₂) w
  rw [Real.fourierIntegral_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [hfun, integral_integral_swap hE, hinner, integral_mul_const, ← hF]

/-- `convPow k κ j = k ⋆ ⋯ ⋆ k ⋆ κ` (`j` factors `k`). -/
def convPow (k κ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => κ
  | j + 1 => conv k (convPow k κ j)

theorem isWienerKernel_convPow {m k n κ : ℝ → ℂ} (hk : IsWienerKernel m k)
    (hκ : IsWienerKernel n κ) :
    ∀ j : ℕ, IsWienerKernel (fun w => m w ^ j * n w) (convPow k κ j)
  | 0 => hκ.congr (fun w => by simp) (fun _ => rfl)
  | j + 1 => (hk.mul (isWienerKernel_convPow hk hκ j)).congr
      (fun w => by simp only [pow_succ]; ring) (fun _ => rfl)

theorem integral_norm_convPow_le {m k n κ : ℝ → ℂ} (hk : IsWienerKernel m k)
    (hκ : IsWienerKernel n κ) :
    ∀ j : ℕ, (∫ x, ‖convPow k κ j x‖) ≤ (∫ x, ‖k x‖) ^ j * ∫ x, ‖κ x‖
  | 0 => by simp [convPow]
  | j + 1 => by
    calc (∫ x, ‖convPow k κ (j + 1) x‖) = ∫ x, ‖conv k (convPow k κ j) x‖ := rfl
      _ ≤ (∫ x, ‖k x‖) * ∫ x, ‖convPow k κ j x‖ :=
          integral_norm_conv_le hk.integrable (isWienerKernel_convPow hk hκ j).integrable
      _ ≤ (∫ x, ‖k x‖) * ((∫ x, ‖k x‖) ^ j * ∫ x, ‖κ x‖) :=
          mul_le_mul_of_nonneg_left (integral_norm_convPow_le hk hκ j)
            (integral_nonneg fun _ => norm_nonneg _)
      _ = (∫ x, ‖k x‖) ^ (j + 1) * ∫ x, ‖κ x‖ := by ring

/-- The Fourier transform at `w`, as a continuous linear functional on `L¹(ℝ)`. -/
def fourierL1 (w : ℝ) : (ℝ →₁[(volume : Measure ℝ)] ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * f x
      map_add' := fun f g => by
        show (∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * (f + g) x) =
          (∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * f x) +
            ∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * g x
        rw [← integral_add (integrable_exp_mul (L1.integrable_coeFn f) w)
          (integrable_exp_mul (L1.integrable_coeFn g) w)]
        refine integral_congr_ae ((Lp.coeFn_add f g).mono fun x hx => ?_)
        simp only [hx, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        show (∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * (c • f) x) =
          c • ∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * f x
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ((Lp.coeFn_smul c f).mono fun x hx => ?_)
        simp only [hx, Pi.smul_apply, smul_eq_mul]
        ring }
    1 (fun f => by
      show ‖∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * f x‖ ≤ 1 * ‖f‖
      rw [one_mul, L1.norm_eq_integral_norm]
      refine (norm_integral_le_integral_norm _).trans
        (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)))
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul])

theorem fourierL1_apply (w : ℝ) (f : ℝ →₁[(volume : Measure ℝ)] ℂ) :
    fourierL1 w f = ∫ x, Complex.exp (↑(-2 * π * x * w) * Complex.I) * f x := rfl

theorem fourierL1_toL1 {m k : ℝ → ℂ} (h : IsWienerKernel m k) (w : ℝ) :
    fourierL1 w (h.integrable.toL1 k) = m w := by
  rw [fourierL1_apply]
  have hF := h.fourier_eq w
  rw [Real.fourierIntegral_real_eq_integral_exp_smul] at hF
  simp only [smul_eq_mul] at hF
  rw [hF]
  exact integral_congr_ae (h.integrable.coeFn_toL1.mono fun x hx => by simp only [hx])

/-- Exponentials in the unitization: `χ e^{c m} ∈ A(ℝ)` with
`‖χ e^{c m}‖_A ≤ ‖χ‖_A e^{|c| ‖m‖_A}`. -/
theorem IsWienerKernel.exp_mul {m k n κ : ℝ → ℂ} (hk : IsWienerKernel m k)
    (hκ : IsWienerKernel n κ) (c : ℂ) :
    ∃ K : ℝ → ℂ, IsWienerKernel (fun w => Complex.exp (c * m w) * n w) K ∧
      ∫ x, ‖K x‖ ≤ (∫ x, ‖κ x‖) * Real.exp (‖c‖ * ∫ x, ‖k x‖) := by
  have hP := isWienerKernel_convPow hk hκ
  obtain ⟨v, hv_def⟩ : ∃ v : ℕ → (ℝ →₁[(volume : Measure ℝ)] ℂ),
      v = fun j => (c ^ j / (j.factorial : ℂ)) • (hP j).integrable.toL1 (convPow k κ j) :=
    ⟨_, rfl⟩
  have hvj : ∀ j, v j =
      (c ^ j / (j.factorial : ℂ)) • (hP j).integrable.toL1 (convPow k κ j) :=
    fun j => by rw [hv_def]
  have hbound : ∀ j, ‖v j‖ ≤
      (‖c‖ * ∫ x, ‖k x‖) ^ j / (j.factorial : ℝ) * ∫ x, ‖κ x‖ := by
    intro j
    rw [hvj, norm_smul, L1.norm_of_fun_eq_integral_norm, norm_div, norm_pow,
      Complex.norm_natCast]
    have hA : 0 ≤ ‖c‖ ^ j / (j.factorial : ℝ) := by positivity
    calc ‖c‖ ^ j / (j.factorial : ℝ) * ∫ x, ‖convPow k κ j x‖
        ≤ ‖c‖ ^ j / (j.factorial : ℝ) * ((∫ x, ‖k x‖) ^ j * ∫ x, ‖κ x‖) :=
          mul_le_mul_of_nonneg_left (integral_norm_convPow_le hk hκ j) hA
      _ = (‖c‖ * ∫ x, ‖k x‖) ^ j / (j.factorial : ℝ) * ∫ x, ‖κ x‖ := by ring
  have hsum : Summable (fun j : ℕ =>
      (‖c‖ * ∫ x, ‖k x‖) ^ j / (j.factorial : ℝ) * ∫ x, ‖κ x‖) :=
    (Real.summable_pow_div_factorial _).mul_right _
  have hv : Summable v := Summable.of_norm_bounded hsum hbound
  have hvn : Summable (fun j => ‖v j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound hsum
  refine ⟨fun x => (∑' j, v j) x, ⟨L1.integrable_coeFn _, fun w => ?_⟩, ?_⟩
  · have hterm : ∀ j, fourierL1 w (v j) =
        c ^ j / (j.factorial : ℂ) * (m w ^ j * n w) := by
      intro j
      rw [hvj, map_smul, smul_eq_mul, fourierL1_toL1 (hP j) w]
    show Complex.exp (c * m w) * n w =
      Real.fourierIntegral (fun x => (∑' j, v j) x) w
    rw [Real.fourierIntegral_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    rw [← fourierL1_apply, (fourierL1 w).map_tsum hv, tsum_congr hterm,
      Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_right]
    exact tsum_congr fun j => by ring
  · calc (∫ x, ‖(∑' j, v j) x‖) = ‖∑' j, v j‖ := (L1.norm_eq_integral_norm _).symm
      _ ≤ ∑' j, ‖v j‖ := norm_tsum_le_tsum_norm hvn
      _ ≤ ∑' j : ℕ, (‖c‖ * ∫ x, ‖k x‖) ^ j / (j.factorial : ℝ) * ∫ x, ‖κ x‖ :=
          Summable.tsum_le_tsum hbound hvn hsum
      _ = (∫ x, ‖κ x‖) * Real.exp (‖c‖ * ∫ x, ‖k x‖) := by
          rw [tsum_mul_right, mul_comm (∑' j : ℕ, (‖c‖ * ∫ x, ‖k x‖) ^ j /
            (j.factorial : ℝ)) (∫ x, ‖κ x‖), Real.exp_eq_exp_ℝ,
            NormedSpace.exp_eq_tsum_div]

/-! ## 7. `lem:wiener-phase` -/

/-- The `t`-derivative of `χ(ξ) e^{-itξ|ξ|^α}` is `-iξ|ξ|^α χ(ξ) e^{-itξ|ξ|^α}`. -/
theorem hasDerivAt_wienerPhase (α : ℝ) (χ : ℝ → ℂ) (w t : ℝ) :
    HasDerivAt (fun s : ℝ => χ w *
        Complex.exp (-(s : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ))))
      (-Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)) * χ w *
        Complex.exp (-(t : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))) t := by
  have hf : (fun s : ℝ => χ w *
      Complex.exp (-(s : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))) =
      fun s : ℝ => χ w *
        Complex.exp ((s : ℂ) * (-Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))) :=
    funext fun s => by
      rw [show -(s : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)) =
        (s : ℂ) * (-Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ))) by ring]
  rw [show -(t : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)) =
    (t : ℂ) * (-Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ))) by ring, hf]
  have h := (((hasDerivAt_id' t : HasDerivAt (fun x : ℝ => x) 1 t).ofReal_comp.mul_const
    (-Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))).cexp).const_mul (χ w)
  exact h.congr_deriv (by simp only [Complex.ofReal_one]; ring)

/-- `lem:wiener-phase`: for `χ` compactly supported,
`χ(ξ) e^{-itξ|ξ|^α}` and its `t`-derivative are bounded in `A(ℝ)` uniformly in
`|t| ≤ 1`.  The uniform bound on the derivative implies
`∫_{-1}^{1} ‖∂_t(χ e^{-itξ|ξ|^α})‖_A dt < ∞`. -/
theorem wienerPhase {α : ℝ} (h0 : 0 < α) (χ : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (fun w => χ w)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      WienerBound (fun w => χ w *
        Complex.exp (-(t : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))) C ∧
      WienerBound (fun w => -Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)) * χ w *
        Complex.exp (-(t : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))) C := by
  obtain ⟨R, hR⟩ := exists_abs_le_of_hasCompactSupport hc
  obtain ⟨k, hk⟩ := inWiener_mul_abs_rpow_mul_schwartz h0 (schwartzBump R)
  obtain ⟨ψ, hψ⟩ := exists_schwartz_kernel χ
  have hκ := (hk.mul hψ).const_mul (-Complex.I)
  refine ⟨max ((∫ x, ‖ψ x‖) * Real.exp (∫ x, ‖k x‖))
      ((∫ x, ‖-Complex.I * conv k (fun y => ψ y) x‖) * Real.exp (∫ x, ‖k x‖)),
    fun t ht => ?_⟩
  have hct : ‖-(t : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    exact abs_le.2 ⟨ht.1, ht.2⟩
  have hA : 0 ≤ ∫ x, ‖k x‖ := integral_nonneg fun _ => norm_nonneg _
  have hexp : Real.exp (‖-(t : ℂ) * Complex.I‖ * ∫ x, ‖k x‖) ≤ Real.exp (∫ x, ‖k x‖) :=
    Real.exp_le_exp.2 (mul_le_of_le_one_left hA hct)
  obtain ⟨K₁, hK₁, hK₁n⟩ := hk.exp_mul hψ (-(t : ℂ) * Complex.I)
  obtain ⟨K₂, hK₂, hK₂n⟩ := hk.exp_mul hκ (-(t : ℂ) * Complex.I)
  constructor
  · refine ⟨K₁, hK₁.congr (fun w => ?_) (fun _ => rfl), ?_⟩
    · show Complex.exp (-(t : ℂ) * Complex.I *
          ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ) * schwartzBump R w)) * χ w =
        χ w * Complex.exp (-(t : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))
      by_cases hχ : χ w = 0
      · simp [hχ]
      · rw [schwartzBump_eq_one (hR w hχ), mul_one]
        ring
    · exact hK₁n.trans ((mul_le_mul_of_nonneg_left hexp
        (integral_nonneg fun _ => norm_nonneg _)).trans (le_max_left _ _))
  · refine ⟨K₂, hK₂.congr (fun w => ?_) (fun _ => rfl), ?_⟩
    · show Complex.exp (-(t : ℂ) * Complex.I *
          ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ) * schwartzBump R w)) *
          (-Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ) * schwartzBump R w * χ w)) =
        -Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)) * χ w *
          Complex.exp (-(t : ℂ) * Complex.I * ((w : ℂ) * ((|w| ^ α : ℝ) : ℂ)))
      by_cases hχ : χ w = 0
      · simp [hχ]
      · rw [schwartzBump_eq_one (hR w hχ), mul_one]
        ring
    · exact hK₂n.trans ((mul_le_mul_of_nonneg_left hexp
        (integral_nonneg fun _ => norm_nonneg _)).trans (le_max_right _ _))

end DGBOZK.Foundations.WienerAlgebraCore
