import Mathlib
import LCHSWiener.KernelTransform
import LCHSWiener.ConvolutionExponential
import LCHSWiener.MeasureFourier

noncomputable section

open Set MeasureTheory scoped BigOperators

namespace LCHSWiener

/-!
# Explicit half-line representation of the shifted dual function

The first prototype isolated the convolution-exponential as an existence
interface.  This file contains no such interface: the density is the concrete
`convolutionExponentialDensity (halfLineKernel r c s)`.
-/

/-- Density of the non-Dirac part of the representing measure. -/
def shiftedDualDensity (r c s : ℝ) : ℝ → ℂ :=
  convolutionExponentialDensity (halfLineKernel r c s)

/-- Function-level Fourier--Laplace representation.  This is the exact form
needed for Fubini in the Wiener duality proof. -/
theorem shiftedDual_eq_one_add_integral
    {r c s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    dualPhiC r c (z - Complex.I * (s : ℂ)) =
      1 + ∫ x : ℝ,
        halfLineCharacter z x * shiftedDualDensity r c s x := by
  unfold shiftedDualDensity
  rw [one_add_integral_character_convolutionExponentialDensity
        (integrable_halfLineKernel hs) hz]
  exact (exp_halfLineKernelTransform_eq_dualPhiC_shift hr hs hz).symm

/-- The density is integrable. -/
theorem integrable_shiftedDualDensity
    {r c s : ℝ} (hs : 0 < s) :
    Integrable (shiftedDualDensity r c s) volume := by
  unfold shiftedDualDensity
  exact integrable_convolutionExponentialDensity (integrable_halfLineKernel hs)

/-- The density is supported on the nonnegative half-line, up to the irrelevant
Lebesgue-null point `0`. -/
theorem shiftedDualDensity_ae_eq_zero_on_nonpos
    {r c s : ℝ} :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Iic 0), shiftedDualDensity r c s x = 0 := by
  -- Every positive convolution power vanishes on `x≤0`; the series therefore
  -- vanishes there term by term.
  filter_upwards with x
  have hx : x ≤ 0 := by aesop
  unfold shiftedDualDensity convolutionExponentialDensity
  apply tsum_eq_zero
  intro n
  unfold convExpTerm
  suffices posConvPow (halfLineKernel r c s) n x = 0 by simp [this]
  induction n with
  | zero => exact halfLineKernel_of_nonpos hx
  | succ n ihn =>
      rw [posConvPow_succ]
      unfold MeasureTheory.posConvolution
      apply integral_eq_zero_of_ae
      filter_upwards with t
      by_cases ht : 0 < t
      · have hxt : x - t ≤ 0 := by linarith
        -- the second factor is the original half-line kernel
        simp [halfLineKernel_of_nonpos hxt]
      · simp [Set.indicator_of_not_mem (not_lt.mpr (le_of_not_gt ht))]

/-- Convenient transform notation for the density part. -/
def shiftedDualDensityTransform (r c s : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, halfLineCharacter z x * shiftedDualDensity r c s x

@[simp] theorem shiftedDual_eq_one_add_densityTransform
    {r c s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    dualPhiC r c (z - Complex.I * (s : ℂ)) =
      1 + shiftedDualDensityTransform r c s z := by
  simpa [shiftedDualDensityTransform] using shiftedDual_eq_one_add_integral hr hs hz

end LCHSWiener
