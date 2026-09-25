import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
import LCHSWiener.ShiftedRateBranch

noncomputable section

open Set MeasureTheory intervalIntegral

namespace LCHSWiener

/-!
# A finite-band oscillatory integral

The identity

  int_{-r}^r exp (-i t x) dt = 2 r sinc (r x)

lets us rewrite the explicit sinc kernel as a finite-band average of elementary
Laplace kernels.  This is the form in which Fubini is used in Section 3.2.
-/

lemma neg_I_mul_real_ne_zero {x : ℝ} (hx : x ≠ 0) :
    -Complex.I * (x : ℂ) ≠ 0 := by
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hx)

lemma exp_neg_I_mul_real (y : ℝ) :
    Complex.exp (-Complex.I * (y : ℂ)) =
      (Real.cos y : ℂ) - (Real.sin y : ℂ) * Complex.I := by
  rw [show -Complex.I * (y : ℂ) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma exp_I_mul_real (y : ℝ) :
    Complex.exp (Complex.I * (y : ℂ)) =
      (Real.cos y : ℂ) + (Real.sin y : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_ofReal_mul_I]

/-- Exact finite-band Fourier integral in the convention of the note. -/
theorem intervalIntegral_exp_neg_I_mul_eq_sinc (r x : ℝ) :
    (∫ t : ℝ in -r..r,
      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) =
      ((2 * r * Real.sinc (r * x) : ℝ) : ℂ) := by
  by_cases hr : r = 0
  · subst r
    simp
  by_cases hx : x = 0
  · subst x
    simp
    ring
  have hc : -Complex.I * (x : ℂ) ≠ 0 := neg_I_mul_real_ne_zero hx
  have hform :
      (∫ t : ℝ in -r..r,
        Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) =
        (Complex.exp ((-Complex.I * (x : ℂ)) * (r : ℂ)) -
          Complex.exp ((-Complex.I * (x : ℂ)) * (-r : ℂ))) /
            (-Complex.I * (x : ℂ)) := by
    have hfun : (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) =
        fun t : ℝ => Complex.exp ((-Complex.I * (x : ℂ)) * (t : ℂ)) := by
      funext t
      ring_nf
    rw [hfun, integral_exp_mul_complex hc]
    push_cast
    rfl
  rw [hform]
  have hpos :
      Complex.exp ((-Complex.I * (x : ℂ)) * (r : ℂ)) =
        (Real.cos (r * x) : ℂ) -
          (Real.sin (r * x) : ℂ) * Complex.I := by
    rw [← exp_neg_I_mul_real (r * x)]
    push_cast
    ring_nf
  have hneg :
      Complex.exp ((-Complex.I * (x : ℂ)) * (-r : ℂ)) =
        (Real.cos (r * x) : ℂ) +
          (Real.sin (r * x) : ℂ) * Complex.I := by
    rw [← exp_I_mul_real (r * x)]
    push_cast
    ring_nf
  rw [hpos, hneg]
  have hrx : r * x ≠ 0 := mul_ne_zero hr hx
  rw [Real.sinc_of_ne_zero hrx, div_eq_iff hc]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  push_cast
  field_simp
  ring

/-- The identity in the exact scalar-factor form used by `halfLineKernel`. -/
theorem two_mul_mul_sinc_eq_intervalIntegral (r x : ℝ) :
    (((2 * r * Real.sinc (r * x) : ℝ) : ℂ)) =
      ∫ t : ℝ in -r..r,
        Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := by
  symm
  exact intervalIntegral_exp_neg_I_mul_eq_sinc r x

end LCHSWiener
