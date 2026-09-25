import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import LCHSWiener.OscillatoryIntegral

noncomputable section

open Set MeasureTheory intervalIntegral

namespace LCHSWiener

/-!
# The explicit kernel as a Laplace-band double integral

This file converts the sinc kernel into the form used by Fubini.  The basic
pointwise identity is

  exp (-(s + i(z+t)) x)
    = exp(-i z x) * exp(-s x) * exp(-i t x).

Integrating in `t` over `[-r,r]` and using the oscillatory-integral lemma turns
this into the kernel from `HalfLineKernel.lean`.
-/

/-- The elementary two-variable Laplace integrand. -/
def shiftedRectangleIntegrand (s : ℝ) (z : ℂ) (t x : ℝ) : ℂ :=
  Complex.exp (-shiftedRate s z t * (x : ℂ))

lemma continuous_shiftedRectangleIntegrand (s : ℝ) (z : ℂ) :
    Continuous (fun p : ℝ × ℝ => shiftedRectangleIntegrand s z p.1 p.2) := by
  unfold shiftedRectangleIntegrand shiftedRate
  fun_prop

lemma shiftedRectangleIntegrand_eq_factors
    (s : ℝ) (z : ℂ) (t x : ℝ) :
    shiftedRectangleIntegrand s z t x =
      halfLineCharacter z x * (Real.exp (-s * x) : ℂ) *
        Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := by
  unfold shiftedRectangleIntegrand halfLineCharacter shiftedRate
  rw [← Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_shiftedRectangleIntegrand
    (s : ℝ) (z : ℂ) (t x : ℝ) :
    ‖shiftedRectangleIntegrand s z t x‖ =
      Real.exp (-(s - z.im) * x) := by
  rw [shiftedRectangleIntegrand, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, shiftedRate_re]
  ring

lemma norm_shiftedRectangleIntegrand_le_exp
    {s : ℝ} {z : ℂ} (hz : z.im ≤ 0) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖shiftedRectangleIntegrand s z t x‖ ≤ Real.exp (-s * x) := by
  rw [norm_shiftedRectangleIntegrand]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Integrating the shifted Laplace kernel in the band variable produces the
sinc factor. -/
theorem intervalIntegral_shiftedRectangleIntegrand
    (r s : ℝ) (z : ℂ) (x : ℝ) :
    (∫ t : ℝ in -r..r, shiftedRectangleIntegrand s z t x) =
      halfLineCharacter z x * (Real.exp (-s * x) : ℂ) *
        ((2 * r * Real.sinc (r * x) : ℝ) : ℂ) := by
  have hpoint : ∀ t : ℝ,
      shiftedRectangleIntegrand s z t x =
        (halfLineCharacter z x * (Real.exp (-s * x) : ℂ)) *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := by
    intro t
    simpa [mul_assoc] using shiftedRectangleIntegrand_eq_factors s z t x
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral_exp_neg_I_mul_eq_sinc]

/-- On the positive half-line, the original kernel integrand is exactly
`-c` times the finite-band Laplace integral. -/
theorem character_mul_kernelCore_eq_bandIntegral
    {r c s x : ℝ} (hx : 0 < x) (z : ℂ) :
    halfLineCharacter z x * halfLineKernelCore r c s x =
      (-(c : ℂ)) *
        (∫ t : ℝ in -r..r, shiftedRectangleIntegrand s z t x) := by
  rw [intervalIntegral_shiftedRectangleIntegrand]
  unfold halfLineKernelCore
  push_cast
  rw [Complex.ofReal_exp]
  ring

/-- The full kernel transform is the positive-half-line integral of the kernel
core, because the kernel was defined by an indicator of `Ioi 0`. -/
theorem halfLineKernelTransform_eq_Ioi
    (r c s : ℝ) (z : ℂ) :
    halfLineKernelTransform r c s z =
      ∫ x : ℝ in Set.Ioi 0,
        halfLineCharacter z x * halfLineKernelCore r c s x := by
  unfold halfLineKernelTransform halfLineKernel
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  congr 1
  funext x
  by_cases hx : x ∈ Set.Ioi (0 : ℝ)
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_not_mem hx]

/-- A compact-frequency indicator used as a separable integrable majorant. -/
def bandOne (r : ℝ) : ℝ → ℝ :=
  (Set.Ioc (-r) r).indicator (fun _ => (1 : ℝ))

/-- Exponential decay on the positive half-line. -/
def positiveDecay (s : ℝ) : ℝ → ℝ :=
  (Set.Ioi (0 : ℝ)).indicator (fun x => Real.exp (-s * x))

lemma integrable_bandOne (r : ℝ) : Integrable (bandOne r) volume := by
  have hOn : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (-r) r) volume := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      measurable_const.aestronglyMeasurable 1 ?_
    filter_upwards with x
    simp
  exact hOn.integrable_indicator measurableSet_Ioc

lemma integrable_positiveDecay {s : ℝ} (hs : 0 < s) :
    Integrable (positiveDecay s) volume := by
  have hOn : IntegrableOn (fun x : ℝ => Real.exp ((-s) * x))
      (Set.Ioi 0) volume := integrableOn_exp_mul_Ioi (by linarith) 0
  have hi := hOn.integrable_indicator measurableSet_Ioi
  simpa [positiveDecay, neg_mul] using hi

/-- The cut-off rectangle integrand used in the full-space form of Fubini. -/
def shiftedRectangleCutoff (r s : ℝ) (z : ℂ) : ℝ × ℝ → ℂ :=
  (Set.Ioc (-r) r ×ˢ Set.Ioi (0 : ℝ)).indicator
    (fun p => shiftedRectangleIntegrand s z p.1 p.2)

lemma aestronglyMeasurable_shiftedRectangleCutoff
    (r s : ℝ) (z : ℂ) :
    AEStronglyMeasurable (shiftedRectangleCutoff r s z) (volume.prod volume) := by
  unfold shiftedRectangleCutoff
  exact (continuous_shiftedRectangleIntegrand s z).aestronglyMeasurable.indicator
    (measurableSet_Ioc.prod measurableSet_Ioi)

/-- Absolute integrability of the double-integral kernel.  The majorant is the
product of a compact-band indicator and `exp(-s x)` on the positive half-line.
-/
theorem integrable_shiftedRectangleCutoff
    {r s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) :
    Integrable (shiftedRectangleCutoff r s z) (volume.prod volume) := by
  have hmajor : Integrable
      (fun p : ℝ × ℝ => bandOne r p.1 * positiveDecay s p.2)
      (volume.prod volume) :=
    (integrable_bandOne r).mul_prod (integrable_positiveDecay hs)
  apply hmajor.mono'
  · exact aestronglyMeasurable_shiftedRectangleCutoff r s z
  · filter_upwards with p
    rcases p with ⟨t, x⟩
    by_cases ht : t ∈ Set.Ioc (-r) r
    · by_cases hx : x ∈ Set.Ioi (0 : ℝ)
      · have hx0 : 0 ≤ x := le_of_lt hx
        have hnorm := norm_shiftedRectangleIntegrand_le_exp hz t hx0
        simpa [shiftedRectangleCutoff, bandOne, positiveDecay, ht, hx,
          Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hnorm
      · simp [shiftedRectangleCutoff, bandOne, positiveDecay, ht, hx]
    · simp [shiftedRectangleCutoff, bandOne, positiveDecay, ht]


/-- Integrating the cut-off rectangle first in the positive-half-line variable. -/
theorem integral_shiftedRectangleCutoff_in_x
    {r s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) (t : ℝ) :
    (∫ x : ℝ, shiftedRectangleCutoff r s z (t, x)) =
      (Set.Ioc (-r) r).indicator
        (fun u : ℝ => (shiftedRate s z u)⁻¹) t := by
  by_cases ht : t ∈ Set.Ioc (-r) r
  · have hfun :
        (fun x : ℝ => shiftedRectangleCutoff r s z (t, x)) =
          (Set.Ioi (0 : ℝ)).indicator
            (fun x : ℝ => shiftedRectangleIntegrand s z t x) := by
      funext x
      by_cases hx : x ∈ Set.Ioi (0 : ℝ)
      · simp [shiftedRectangleCutoff, ht, hx]
      · simp [shiftedRectangleCutoff, ht, hx]
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [Set.indicator_of_mem ht]
    exact integral_exp_neg_shiftedRate_Ioi hs hz t
  · have hfun :
        (fun x : ℝ => shiftedRectangleCutoff r s z (t, x)) = 0 := by
      funext x
      simp [shiftedRectangleCutoff, ht]
    rw [hfun, integral_zero]
    simp [Set.indicator_of_not_mem ht]

/-- Integrating the cut-off rectangle first in the compact band variable. -/
theorem integral_shiftedRectangleCutoff_in_t
    {r s : ℝ} (hr : 0 < r) (z : ℂ) (x : ℝ) :
    (∫ t : ℝ, shiftedRectangleCutoff r s z (t, x)) =
      (Set.Ioi (0 : ℝ)).indicator
        (fun y : ℝ =>
          ∫ t : ℝ in -r..r, shiftedRectangleIntegrand s z t y) x := by
  by_cases hx : x ∈ Set.Ioi (0 : ℝ)
  · have hfun :
        (fun t : ℝ => shiftedRectangleCutoff r s z (t, x)) =
          (Set.Ioc (-r) r).indicator
            (fun t : ℝ => shiftedRectangleIntegrand s z t x) := by
      funext t
      by_cases ht : t ∈ Set.Ioc (-r) r
      · simp [shiftedRectangleCutoff, ht, hx]
      · simp [shiftedRectangleCutoff, ht, hx]
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [Set.indicator_of_mem hx]
    rw [← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  · have hfun :
        (fun t : ℝ => shiftedRectangleCutoff r s z (t, x)) = 0 := by
      funext t
      simp [shiftedRectangleCutoff, hx]
    rw [hfun, integral_zero]
    simp [Set.indicator_of_not_mem hx]

/-- Fubini in the exact form needed for the Wiener representation. -/
theorem Ioi_integral_band_eq_band_integral_Ioi
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    (∫ x : ℝ in Set.Ioi 0,
        ∫ t : ℝ in -r..r, shiftedRectangleIntegrand s z t x) =
      ∫ t : ℝ in -r..r, (shiftedRate s z t)⁻¹ := by
  have hInt := integrable_shiftedRectangleCutoff (r := r) hs hz
  have hswap :
      (∫ t : ℝ, ∫ x : ℝ, shiftedRectangleCutoff r s z (t, x)) =
        ∫ x : ℝ, ∫ t : ℝ, shiftedRectangleCutoff r s z (t, x) := by
    exact MeasureTheory.integral_integral_swap (by simpa using hInt)
  have hleft :
      (∫ t : ℝ, ∫ x : ℝ, shiftedRectangleCutoff r s z (t, x)) =
        ∫ t : ℝ in -r..r, (shiftedRate s z t)⁻¹ := by
    simp_rw [integral_shiftedRectangleCutoff_in_x hs hz]
    rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  have hright :
      (∫ x : ℝ, ∫ t : ℝ, shiftedRectangleCutoff r s z (t, x)) =
        ∫ x : ℝ in Set.Ioi 0,
          ∫ t : ℝ in -r..r, shiftedRectangleIntegrand s z t x := by
    simp_rw [integral_shiftedRectangleCutoff_in_t hr z]
    rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [hleft, hright] at hswap
  exact hswap.symm

/-- The Fourier-Laplace transform of the explicit sinc kernel is the finite
logarithmic band integral. -/
theorem halfLineKernelTransform_eq_neg_c_mul_bandIntegral
    {r c s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    halfLineKernelTransform r c s z =
      (-(c : ℂ)) *
        (∫ t : ℝ in -r..r, (shiftedRate s z t)⁻¹) := by
  rw [halfLineKernelTransform_eq_Ioi]
  have hpoint : ∀ x ∈ Set.Ioi (0 : ℝ),
      halfLineCharacter z x * halfLineKernelCore r c s x =
        (-(c : ℂ)) *
          (∫ t : ℝ in -r..r, shiftedRectangleIntegrand s z t x) := by
    intro x hx
    exact character_mul_kernelCore_eq_bandIntegral hx z
  have hcongr :
      (∫ x : ℝ in Set.Ioi 0,
        halfLineCharacter z x * halfLineKernelCore r c s x) =
        ∫ x : ℝ in Set.Ioi 0,
          (-(c : ℂ)) *
            (∫ t : ℝ in -r..r, shiftedRectangleIntegrand s z t x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact hpoint x hx
  rw [hcongr]
  rw [MeasureTheory.integral_const_mul]
  rw [Ioi_integral_band_eq_band_integral_Ioi hr hs hz]

/-- Closed logarithmic form of the explicit kernel transform. -/
theorem halfLineKernelTransform_eq_log_difference
    {r c s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    halfLineKernelTransform r c s z =
      Complex.I * (c : ℂ) *
        (Complex.log (shiftedRate s z r) -
          Complex.log (shiftedRate s z (-r))) := by
  rw [halfLineKernelTransform_eq_neg_c_mul_bandIntegral hr hs hz]
  rw [symmetric_interval_inv_shiftedRate hs hz]
  ring

/-- Main transform identity for Section 3.2: exponentiating the explicit
positive-half-line transform gives the shifted dual function. -/
theorem exp_halfLineKernelTransform_eq_dualPhiC_shift
    {r c s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    Complex.exp (halfLineKernelTransform r c s z) =
      dualPhiC r c (z - Complex.I * (s : ℂ)) := by
  rw [halfLineKernelTransform_eq_log_difference hr hs hz]
  unfold dualPhiC
  rw [log_dualMobius_shift hr hs hz]
  congr 1
  push_cast
  ring

end LCHSWiener
