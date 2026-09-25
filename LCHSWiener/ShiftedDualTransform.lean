import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LCHSWiener.HalfLineKernel

noncomputable section

open Set MeasureTheory intervalIntegral

namespace LCHSWiener

/-!
# The logarithmic transform of the shifted dual function

This file isolates the elementary Laplace/logarithm calculation used in the
Wiener proof.  For `s > 0` and `Im z <= 0` put

  A(t) = s + i (z+t).

Then `Re A(t) = s - Im z > 0`, so the principal logarithm is analytic along
the whole real `t`-path.  The two key identities are

  int_0^infty exp (-A(t) x) dx = 1 / A(t)

and

  int_{-r}^r 1 / A(t) dt
    = -i (log A(r) - log A(-r)).

These are the finite-dimensional analytic ingredients behind the explicit
positive-half-line kernel introduced in `HalfLineKernel.lean`.
-/

/-- `s + i(z+t)`, the Laplace rate naturally produced by shifting `z` by
`-i s`. -/
def shiftedRate (s : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (s : ℂ) + Complex.I * (z + (t : ℂ))

@[simp] lemma shiftedRate_re (s : ℝ) (z : ℂ) (t : ℝ) :
    (shiftedRate s z t).re = s - z.im := by
  simp [shiftedRate, Complex.mul_re, sub_eq_add_neg]

@[simp] lemma shiftedRate_im (s : ℝ) (z : ℂ) (t : ℝ) :
    (shiftedRate s z t).im = z.re + t := by
  simp [shiftedRate, Complex.mul_im]

lemma shiftedRate_re_pos {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0)
    (t : ℝ) : 0 < (shiftedRate s z t).re := by
  rw [shiftedRate_re]
  linarith

lemma shiftedRate_mem_slitPlane {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≤ 0) (t : ℝ) : shiftedRate s z t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (shiftedRate_re_pos hs hz t)

lemma shiftedRate_ne_zero {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≤ 0) (t : ℝ) : shiftedRate s z t ≠ 0 :=
  Complex.slitPlane_ne_zero (shiftedRate_mem_slitPlane hs hz t)

lemma neg_shiftedRate_re_neg {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≤ 0) (t : ℝ) : (-shiftedRate s z t).re < 0 := by
  change -(shiftedRate s z t).re < 0
  rw [shiftedRate_re]
  linarith

lemma continuous_shiftedRate (s : ℝ) (z : ℂ) :
    Continuous (shiftedRate s z) := by
  unfold shiftedRate
  fun_prop

/-- The affine real path `t -> s + i(z+t)` has derivative `i`. -/
lemma hasDerivAt_shiftedRate (s : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (shiftedRate s z) Complex.I t := by
  have hreal : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have hsum : HasDerivAt (fun u : ℝ => z + (u : ℂ)) 1 t := by
    simpa [add_comm] using hreal.add_const z
  have hmul : HasDerivAt (fun u : ℝ => Complex.I * (z + (u : ℂ))) Complex.I t := by
    simpa using hsum.const_mul Complex.I
  change HasDerivAt
    (fun u : ℝ => (s : ℂ) + Complex.I * (z + (u : ℂ))) Complex.I t
  convert (hasDerivAt_const t (s : ℂ)).add hmul using 1
  simp

/-- Along the shifted-rate path, the principal logarithm has derivative
`i / A(t)`. -/
lemma hasDerivAt_log_shiftedRate {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≤ 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.log (shiftedRate s z u))
      (Complex.I / shiftedRate s z t) t := by
  exact (hasDerivAt_shiftedRate s z t).clog_real
    (shiftedRate_mem_slitPlane hs hz t)

lemma continuous_inv_shiftedRate {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≤ 0) :
    Continuous (fun t : ℝ => (shiftedRate s z t)⁻¹) := by
  exact (continuous_shiftedRate s z).inv₀
    (fun t => shiftedRate_ne_zero hs hz t)

lemma intervalIntegrable_inv_shiftedRate {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≤ 0) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (shiftedRate s z t)⁻¹) volume a b :=
  (continuous_inv_shiftedRate hs hz).intervalIntegrable a b

/-- Fundamental theorem of calculus for the logarithm of the shifted rate. -/
theorem intervalIntegral_inv_shiftedRate
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) (a b : ℝ) :
    (∫ t : ℝ in a..b, (shiftedRate s z t)⁻¹) =
      -Complex.I *
        (Complex.log (shiftedRate s z b) -
          Complex.log (shiftedRate s z a)) := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => Complex.log (shiftedRate s z u))
        (Complex.I / shiftedRate s z t) t := by
    intro t ht
    exact hasDerivAt_log_shiftedRate hs hz t
  have hintInv : IntervalIntegrable
      (fun t : ℝ => (shiftedRate s z t)⁻¹) volume a b :=
    intervalIntegrable_inv_shiftedRate hs hz a b
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.I / shiftedRate s z t) volume a b := by
    simpa [div_eq_mul_inv] using hintInv.const_mul Complex.I
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hpull :
      (∫ t : ℝ in a..b, Complex.I / shiftedRate s z t) =
        Complex.I * (∫ t : ℝ in a..b, (shiftedRate s z t)⁻¹) := by
    simp [div_eq_mul_inv, intervalIntegral.integral_const_mul]
  rw [hpull] at hFTC
  calc
    (∫ t : ℝ in a..b, (shiftedRate s z t)⁻¹)
        = (-Complex.I * Complex.I) *
            (∫ t : ℝ in a..b, (shiftedRate s z t)⁻¹) := by simp
    _ = -Complex.I *
          (Complex.I * (∫ t : ℝ in a..b, (shiftedRate s z t)⁻¹)) := by ring
    _ = -Complex.I *
          (Complex.log (shiftedRate s z b) -
            Complex.log (shiftedRate s z a)) := by rw [hFTC]

/-- The elementary one-sided Laplace integral for the shifted rate. -/
theorem integral_exp_neg_shiftedRate_Ioi
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) (t : ℝ) :
    (∫ x : ℝ in Set.Ioi 0,
      Complex.exp (-shiftedRate s z t * (x : ℂ))) =
      (shiftedRate s z t)⁻¹ := by
  have hneg : (-shiftedRate s z t).re < 0 :=
    neg_shiftedRate_re_neg hs hz t
  rw [integral_exp_mul_complex_Ioi hneg 0]
  simp

/-- Integrability companion to `integral_exp_neg_shiftedRate_Ioi`. -/
theorem integrableOn_exp_neg_shiftedRate_Ioi
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) (t : ℝ) :
    IntegrableOn
      (fun x : ℝ => Complex.exp (-shiftedRate s z t * (x : ℂ)))
      (Set.Ioi 0) volume := by
  exact integrableOn_exp_mul_complex_Ioi
    (neg_shiftedRate_re_neg hs hz t) 0

/-- The Mobius factor of the shifted dual function, expressed through the two
endpoint Laplace rates.  This is a purely algebraic identity. -/
lemma dualMobius_shift_eq_rate_ratio
    {r s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) :
    dualMobius r (z - Complex.I * (s : ℂ)) =
      - shiftedRate s z (-r) / shiftedRate s z r := by
  have hp : shiftedRate s z r ≠ 0 := shiftedRate_ne_zero hs hz r
  have hrel : shiftedRate s z r =
      Complex.I * ((r : ℂ) + z - Complex.I * (s : ℂ)) := by
    unfold shiftedRate
    linear_combination (s : ℂ) * Complex.I_sq
  have hnrel : shiftedRate s z (-r) =
      Complex.I * ((-r : ℂ) + z - Complex.I * (s : ℂ)) := by
    unfold shiftedRate
    push_cast
    linear_combination (s : ℂ) * Complex.I_sq
  have hden : (r : ℂ) + z - Complex.I * (s : ℂ) ≠ 0 := by
    intro h
    apply hp
    rw [hrel, h]
    simp
  rw [hrel, hnrel]
  unfold dualMobius
  have hden' : (r : ℂ) + (z - Complex.I * (s : ℂ)) ≠ 0 := by
    rwa [← add_sub_assoc]
  rw [div_eq_div_iff hden' (mul_ne_zero Complex.I_ne_zero hden)]
  ring

/-- The finite-interval logarithmic integral in the symmetric form needed by
the explicit kernel. -/
theorem symmetric_interval_inv_shiftedRate
    {r s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) :
    (∫ t : ℝ in -r..r, (shiftedRate s z t)⁻¹) =
      -Complex.I *
        (Complex.log (shiftedRate s z r) -
          Complex.log (shiftedRate s z (-r))) := by
  simpa using intervalIntegral_inv_shiftedRate hs hz (-r) r

end LCHSWiener
