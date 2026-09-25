import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LCHSWiener.DualFunction

noncomputable section

open Set MeasureTheory

namespace LCHSWiener

/-!
# The explicit half-line kernel behind Section 3.2

For `r,c,s > 0` we use the integrable kernel

  h_{r,c,s}(x) = -2 c r exp(-s x) sinc(r x),   x > 0,
                  0,                            x <= 0.

Since `r * sinc(r x) = sin(r x) / x` away from zero, this is the regularized
version of

  -2 c exp(-s x) sin(r x) / x.

The point of introducing `Real.sinc` is that all estimates at the origin become
routine and no removable-singularity argument is needed.  This file proves the
support, measurability and L1 facts needed later for the convolution-exponential
construction of the representing measure.
-/

/-- The continuous expression before cutting it off to the positive half-line. -/
def halfLineKernelCore (r c s : ℝ) (x : ℝ) : ℂ :=
  (((-2 * c * r) * Real.exp (-s * x) * Real.sinc (r * x) : ℝ) : ℂ)

/-- The positive-half-line kernel.  The value at zero is irrelevant for all
Lebesgue-integral statements, so we use `Ioi 0`. -/
def halfLineKernel (r c s : ℝ) : ℝ → ℂ :=
  (Set.Ioi (0 : ℝ)).indicator (halfLineKernelCore r c s)

/-- Fourier-Laplace character in the convention of the note. -/
def halfLineCharacter (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * z * (x : ℂ))

/-- Fourier-Laplace transform of the explicit half-line kernel. -/
def halfLineKernelTransform (r c s : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, halfLineCharacter z x * halfLineKernel r c s x

lemma continuous_halfLineKernelCore (r c s : ℝ) :
    Continuous (halfLineKernelCore r c s) := by
  unfold halfLineKernelCore
  fun_prop

lemma aestronglyMeasurable_halfLineKernel (r c s : ℝ) :
    AEStronglyMeasurable (halfLineKernel r c s) volume := by
  unfold halfLineKernel
  exact (continuous_halfLineKernelCore r c s).aestronglyMeasurable.indicator measurableSet_Ioi

@[simp] lemma halfLineKernel_of_nonpos {r c s x : ℝ} (hx : x ≤ 0) :
    halfLineKernel r c s x = 0 := by
  simp [halfLineKernel, not_lt.mpr hx]

@[simp] lemma halfLineKernel_of_pos {r c s x : ℝ} (hx : 0 < x) :
    halfLineKernel r c s x = halfLineKernelCore r c s x := by
  simp [halfLineKernel, hx]

/-- Pointwise support is contained in the nonnegative half-line. -/
lemma support_halfLineKernel_subset (r c s : ℝ) :
    Function.support (halfLineKernel r c s) ⊆ Set.Ici 0 := by
  intro x hx
  simp only [Set.mem_Ici]
  by_contra hnonneg
  have hx0 : x ≤ 0 := le_of_not_ge hnonneg
  exact hx (halfLineKernel_of_nonpos hx0)

/-- Uniform sinc estimate used for every L1 bound below. -/
lemma norm_halfLineKernelCore_le (r c s x : ℝ) :
    ‖halfLineKernelCore r c s x‖ ≤
      |(-2 * c * r : ℝ)| * Real.exp (-s * x) := by
  have hsinc : |Real.sinc (r * x)| ≤ 1 := Real.abs_sinc_le_one _
  have hcoef : 0 ≤ |(-2 * c * r : ℝ)| := abs_nonneg _
  have hexp : 0 ≤ Real.exp (-s * x) := (Real.exp_pos _).le
  rw [halfLineKernelCore, Complex.norm_real]
  simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |(-2 * c * r : ℝ)| * Real.exp (-s * x) * |Real.sinc (r * x)|
        ≤ |(-2 * c * r : ℝ)| * Real.exp (-s * x) * 1 :=
          mul_le_mul_of_nonneg_left hsinc (mul_nonneg hcoef hexp)
    _ = |(-2 * c * r : ℝ)| * Real.exp (-s * x) := by ring

/-- The cut-off kernel satisfies the same exponential majorant on `x>0`. -/
lemma norm_halfLineKernel_le_of_pos {r c s x : ℝ} (hx : 0 < x) :
    ‖halfLineKernel r c s x‖ ≤
      |(-2 * c * r : ℝ)| * Real.exp (-s * x) := by
  rw [halfLineKernel_of_pos hx]
  exact norm_halfLineKernelCore_le r c s x

/-- The explicit half-line kernel is absolutely integrable for every `s>0`. -/
theorem integrable_halfLineKernel {r c s : ℝ} (hs : 0 < s) :
    Integrable (halfLineKernel r c s) volume := by
  rw [halfLineKernel, integrable_indicator_iff measurableSet_Ioi]
  have hexpOn : IntegrableOn (fun x : ℝ => Real.exp ((-s) * x)) (Set.Ioi 0) volume :=
    integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  have hexp : Integrable (fun x : ℝ => Real.exp ((-s) * x))
      (volume.restrict (Set.Ioi 0)) := hexpOn
  have hmajor : Integrable
      (fun x : ℝ => |(-2 * c * r : ℝ)| * Real.exp ((-s) * x))
      (volume.restrict (Set.Ioi 0)) := by
    apply Integrable.const_mul
    exact hexp
  apply hmajor.mono'
  · exact (continuous_halfLineKernelCore r c s).aestronglyMeasurable
  · filter_upwards with x
    simpa [neg_mul] using norm_halfLineKernelCore_le r c s x

/-- Exact norm of the Fourier-Laplace character. -/
lemma norm_halfLineCharacter (z : ℂ) (x : ℝ) :
    ‖halfLineCharacter z x‖ = Real.exp (z.im * x) := by
  rw [halfLineCharacter, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
  ring

/-- In the closed lower half-plane the character has norm at most one for
nonnegative time. -/
lemma norm_halfLineCharacter_le_one {z : ℂ} {x : ℝ}
    (hz : z.im ≤ 0) (hx : 0 ≤ x) :
    ‖halfLineCharacter z x‖ ≤ 1 := by
  rw [norm_halfLineCharacter, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma continuous_halfLineCharacter (z : ℂ) :
    Continuous (halfLineCharacter z) := by
  unfold halfLineCharacter
  fun_prop

/-- For `Im z <= 0`, the kernel times the character is integrable.  This is
exactly the convergence domain needed later: real `z=k` and `z=-i`. -/
theorem integrable_halfLineCharacter_mul_kernel
    {r c s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) :
    Integrable (fun x : ℝ => halfLineCharacter z x * halfLineKernel r c s x) volume := by
  have hk : Integrable (halfLineKernel r c s) volume := integrable_halfLineKernel hs
  have hmajor : Integrable (fun x : ℝ => ‖halfLineKernel r c s x‖) volume := hk.norm
  have hmeasChar : AEStronglyMeasurable (halfLineCharacter z) volume :=
    (continuous_halfLineCharacter z).aestronglyMeasurable
  have hmeasKernel : AEStronglyMeasurable (halfLineKernel r c s) volume :=
    aestronglyMeasurable_halfLineKernel r c s
  apply hmajor.mono'
  · exact hmeasChar.mul hmeasKernel
  · filter_upwards with x
    by_cases hx : 0 < x
    · rw [norm_mul]
      have hchar : ‖halfLineCharacter z x‖ ≤ 1 :=
        norm_halfLineCharacter_le_one hz (le_of_lt hx)
      have hknonneg : 0 ≤ ‖halfLineKernel r c s x‖ := norm_nonneg _
      nlinarith
    · have hx0 : x ≤ 0 := le_of_not_gt hx
      simp [halfLineKernel_of_nonpos hx0]

/-- The transform is therefore a genuine Bochner integral on the entire closed
lower half-plane. -/
lemma halfLineKernelTransform_integrable
    {r c s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) :
    Integrable (fun x : ℝ => halfLineCharacter z x * halfLineKernel r c s x) volume :=
  integrable_halfLineCharacter_mul_kernel hs hz

/-- Away from zero, the sinc form agrees with the paper's `sin(rx)/x` kernel. -/
lemma halfLineKernelCore_eq_sin_div {r c s x : ℝ} (hx : x ≠ 0) :
    halfLineKernelCore r c s x =
      (((-2 * c) * Real.exp (-s * x) * (Real.sin (r * x) / x) : ℝ) : ℂ) := by
  by_cases hr : r = 0
  · subst r
    simp [halfLineKernelCore]
  · rw [halfLineKernelCore, Real.sinc_of_ne_zero (mul_ne_zero hr hx)]
    push_cast
    field_simp [hx]
    ring

end LCHSWiener
