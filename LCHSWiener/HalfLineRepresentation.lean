import Mathlib.Tactic.Linarith
import LCHSWiener.KernelTransform
import LCHSWiener.ConvolutionExponential
import LCHSWiener.MeasureFourier

noncomputable section

open Set MeasureTheory
open scoped BigOperators

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
        (integrable_halfLineKernel hs) (fun x hx => halfLineKernel_of_nonpos hx) hz]
  exact (exp_halfLineKernelTransform_eq_dualPhiC_shift hr hs hz).symm

/-- The density is integrable. -/
theorem integrable_shiftedDualDensity
    {r c s : ℝ} (hs : 0 < s) :
    Integrable (shiftedDualDensity r c s) volume := by
  unfold shiftedDualDensity
  exact integrable_convolutionExponentialDensity (integrable_halfLineKernel hs)

/-- The density vanishes pointwise on the closed negative half-line. -/
theorem shiftedDualDensity_of_nonpos {r c s x : ℝ} (hx : x ≤ 0) :
    shiftedDualDensity r c s x = 0 := by
  unfold shiftedDualDensity convolutionExponentialDensity
  rw [tsum_congr fun n =>
    convExpTerm_of_nonpos (fun y hy => halfLineKernel_of_nonpos hy) n hx]
  exact tsum_zero

/-- The density is supported on the nonnegative half-line, up to the irrelevant
Lebesgue-null point `0`. -/
theorem shiftedDualDensity_ae_eq_zero_on_nonpos
    {r c s : ℝ} :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Iic 0), shiftedDualDensity r c s x = 0 := by
  -- Every positive convolution power vanishes on `x≤0`; the series therefore
  -- vanishes there term by term.
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  unfold shiftedDualDensity convolutionExponentialDensity
  rw [tsum_congr fun n =>
    convExpTerm_of_nonpos (fun y hy => halfLineKernel_of_nonpos hy) n (Set.mem_Iic.1 hx)]
  exact tsum_zero

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
