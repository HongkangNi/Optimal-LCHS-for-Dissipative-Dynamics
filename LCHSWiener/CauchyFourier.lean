import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace LCHSWiener

open MeasureTheory Real Set FourierTransform

/-- The two-sided exponential `v ↦ e^{-|v|}` as a complex-valued function. -/
def expNegAbsC (v : ℝ) : ℂ := ((Real.exp (-|v|) : ℝ) : ℂ)

lemma continuous_expNegAbsC : Continuous expNegAbsC := by
  unfold expNegAbsC; fun_prop

/-- Integrand of the Fourier transform of `expNegAbsC` at frequency `w`. -/
lemma fourierIntegrand_Ioi (w v : ℝ) (hv : v ∈ Ioi (0:ℝ)) :
    Complex.exp (↑(-2 * π * v * w) * Complex.I) • expNegAbsC v =
      Complex.exp ((-1 - 2 * π * w * Complex.I) * v) := by
  have hv' : |v| = v := abs_of_pos hv
  simp only [expNegAbsC, hv', smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma fourierIntegrand_Iic (w v : ℝ) (hv : v ∈ Iic (0:ℝ)) :
    Complex.exp (↑(-2 * π * v * w) * Complex.I) • expNegAbsC v =
      Complex.exp ((1 - 2 * π * w * Complex.I) * v) := by
  have hv' : |v| = -v := abs_of_nonpos hv
  simp only [expNegAbsC, hv', smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integrableOn_fourierIntegrand_Ioi (w : ℝ) :
    IntegrableOn (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • expNegAbsC v)
      (Ioi 0) := by
  refine (integrableOn_exp_mul_complex_Ioi (a := -1 - 2 * π * w * Complex.I) ?_ 0).congr_fun
    (fun v hv => (fourierIntegrand_Ioi w v hv).symm) measurableSet_Ioi
  simp

lemma integrableOn_fourierIntegrand_Iic (w : ℝ) :
    IntegrableOn (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • expNegAbsC v)
      (Iic 0) := by
  refine (integrableOn_exp_mul_complex_Iic (a := 1 - 2 * π * w * Complex.I) ?_ 0).congr_fun
    (fun v hv => (fourierIntegrand_Iic w v hv).symm) measurableSet_Iic
  simp

lemma integrable_expNegAbsC : Integrable expNegAbsC := by
  have h : Integrable (fun v : ℝ => Complex.exp (↑(-2 * π * v * 0) * Complex.I) •
      expNegAbsC v) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
    exact ⟨integrableOn_fourierIntegrand_Iic 0, integrableOn_fourierIntegrand_Ioi 0⟩
  simpa using h

lemma fourier_expNegAbsC (w : ℝ) :
    𝓕 expNegAbsC w = (((2 / (1 + (2 * π * w) ^ 2)) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    ← intervalIntegral.integral_Iic_add_Ioi (b := 0) (integrableOn_fourierIntegrand_Iic w)
      (integrableOn_fourierIntegrand_Ioi w),
    setIntegral_congr_fun measurableSet_Iic (fun v hv => fourierIntegrand_Iic w v hv),
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => fourierIntegrand_Ioi w v hv),
    integral_exp_mul_complex_Iic (by simp), integral_exp_mul_complex_Ioi (by simp)]
  have h1 : (1 - 2 * π * w * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : (-1 - 2 * π * w * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h3 : ((1 + (2 * π * w) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + (2 * π * w) ^ 2 : ℝ) ≠ 0)
  push_cast at h3 ⊢
  simp only [mul_zero, Complex.exp_zero]
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma integrable_fourier_expNegAbsC : Integrable (𝓕 expNegAbsC) := by
  have : Integrable (fun w : ℝ => 2 * (1 + (2 * π * w) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' (by positivity : (2 * π) ≠ 0)).const_mul 2
  have h := this.ofReal (𝕜 := ℂ)
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [fourier_expNegAbsC, div_eq_mul_inv]
  rfl

lemma fourierInv_fourier_expNegAbsC (t : ℝ) :
    ∫ w : ℝ, Complex.exp (↑(2 * π * w * t) * Complex.I) *
        (((2 / (1 + (2 * π * w) ^ 2)) : ℝ) : ℂ) = ((Real.exp (-|t|) : ℝ) : ℂ) := by
  have h := congrFun (continuous_expNegAbsC.fourierInv_fourier_eq integrable_expNegAbsC
    integrable_fourier_expNegAbsC) t
  rw [fourierInv_eq'] at h
  simp only [fourier_expNegAbsC, smul_eq_mul] at h
  rw [← expNegAbsC, ← h]
  congr 1
  ext w
  congr 3
  rw [Real.inner_apply]; push_cast; ring

lemma integrable_exp_mul_cauchy (t : ℝ) :
    MeasureTheory.Integrable (fun k : ℝ => Complex.exp (-Complex.I * (k:ℂ) * (t:ℂ)) *
        (((1 / (Real.pi * (1 + k^2))) : ℝ) : ℂ)) := by
  have hi : Integrable (fun k : ℝ => (((1 / (Real.pi * (1 + k^2))) : ℝ) : ℂ)) := by
    have : Integrable (fun k : ℝ => π⁻¹ * (1 + k ^ 2)⁻¹) :=
      integrable_inv_one_add_sq.const_mul π⁻¹
    refine (this.ofReal (𝕜 := ℂ)).congr (Filter.Eventually.of_forall fun k => ?_)
    simp only [one_div, mul_inv]
    rfl
  refine hi.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun k => ?_)
  · exact (by fun_prop : Continuous fun k : ℝ =>
      Complex.exp (-Complex.I * (k:ℂ) * (t:ℂ))).aestronglyMeasurable
  · rw [Complex.norm_exp]
    simp

/-- Fourier transform of the Cauchy density: `∫ e^{-ikt} /(π(1+k²)) dk = e^{-|t|}`. -/
theorem integral_exp_mul_cauchy (t : ℝ) :
    ∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (t:ℂ)) *
        (((1 / (Real.pi * (1 + k^2))) : ℝ) : ℂ) =
      ((Real.exp (-|t|) : ℝ) : ℂ) := by
  set h : ℝ → ℂ := fun k => Complex.exp (-Complex.I * (k:ℂ) * (t:ℂ)) *
        (((1 / (Real.pi * (1 + k^2))) : ℝ) : ℂ) with hh
  have hc := Measure.integral_comp_mul_left h (-(2 * π))
  have hpi : (0:ℝ) < 2 * π := by positivity
  rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hpi)] at hc
  have key : ∫ k, h k = ∫ w : ℝ, ((2 * π : ℝ) : ℂ) * h (-(2 * π) * w) := by
    rw [integral_const_mul, hc, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hpi.ne', Complex.ofReal_one, one_mul]
  rw [key, ← fourierInv_fourier_expNegAbsC t]
  congr 1
  ext w
  simp only [hh]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have h3 : ((1 + (2 * π * w) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + (2 * π * w) ^ 2 : ℝ) ≠ 0)
  push_cast at h3 ⊢
  have h4 : (1 + (-(2 * (π:ℂ) * w)) ^ 2) ≠ 0 := by rwa [neg_sq]
  rw [show -Complex.I * (-(2 * (π:ℂ)) * w) * t = (2 * π * w * t) * Complex.I by ring]
  field_simp

end LCHSWiener
