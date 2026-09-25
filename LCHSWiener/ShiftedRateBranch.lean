import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import LCHSWiener.ShiftedDualTransform

noncomputable section

open Set

namespace LCHSWiener

/-!
# The principal-log branch identity for the shifted rate

For

  A(t) = s + i (z+t),

with `s > 0` and `Im z <= 0`, every `A(t)` lies in the open right half-plane.
If `r > 0`, the arguments of `A(-r)` and `A(r)` both lie in
`(-pi/2,pi/2)`, and the latter is strictly larger.  Consequently

  log (-A(-r)/A(r))
    = log A(-r) - log A(r) + pi i

for the principal logarithm.  This is precisely the branch correction needed
when identifying the explicit half-line transform with the dual function.
-/

lemma shiftedRate_abs_arg_lt_pi_div_two
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) (t : ℝ) :
    |(shiftedRate s z t).arg| < Real.pi / 2 := by
  rw [Complex.abs_arg_lt_pi_div_two_iff]
  exact Or.inl (shiftedRate_re_pos hs hz t)

lemma shiftedRate_arg_mem_Ioo
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) (t : ℝ) :
    (shiftedRate s z t).arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have h := shiftedRate_abs_arg_lt_pi_div_two hs hz t
  exact (abs_lt.mp h)

lemma tan_arg_shiftedRate
    {s : ℝ} (_hs : 0 < s) {z : ℂ} (_hz : z.im ≤ 0) (t : ℝ) :
    Real.tan (shiftedRate s z t).arg = (z.re + t) / (s - z.im) := by
  rw [Complex.tan_arg, shiftedRate_im, shiftedRate_re]

lemma shiftedRate_arg_strictMono {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    StrictMono (fun t : ℝ => (shiftedRate s z t).arg) := by
  intro a b hab
  have hden : 0 < s - z.im := by linarith
  have htan :
      Real.tan (shiftedRate s z a).arg <
        Real.tan (shiftedRate s z b).arg := by
    rw [tan_arg_shiftedRate hs hz a, tan_arg_shiftedRate hs hz b]
    exact (div_lt_div_iff_of_pos_right hden).2 (by linarith)
  have ha := shiftedRate_arg_mem_Ioo hs hz a
  have hb := shiftedRate_arg_mem_Ioo hs hz b
  by_contra hnot
  have hba : (shiftedRate s z b).arg ≤ (shiftedRate s z a).arg :=
    le_of_not_gt hnot
  rcases hba.lt_or_eq with hlt | heq
  · have hrev := Real.strictMonoOn_tan hb ha hlt
    exact (not_lt_of_ge (le_of_lt htan)) hrev
  · rw [heq] at htan
    exact (lt_irrefl _ htan)

lemma shiftedRate_arg_neg_r_lt_arg_r
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    (shiftedRate s z (-r)).arg < (shiftedRate s z r).arg := by
  exact shiftedRate_arg_strictMono hs hz (by linarith)

/-- The imaginary part of the candidate principal logarithm. -/
lemma shiftedLogCandidate_im (r s : ℝ) (z : ℂ) :
    (Complex.log (shiftedRate s z (-r)) -
        Complex.log (shiftedRate s z r) +
        (Real.pi : ℂ) * Complex.I).im =
      (shiftedRate s z (-r)).arg -
        (shiftedRate s z r).arg + Real.pi := by
  simp [Complex.log_im]

lemma shiftedLogCandidate_im_le_pi
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    (Complex.log (shiftedRate s z (-r)) -
        Complex.log (shiftedRate s z r) +
        (Real.pi : ℂ) * Complex.I).im ≤ Real.pi := by
  rw [shiftedLogCandidate_im]
  have h := shiftedRate_arg_neg_r_lt_arg_r hr hs hz
  linarith

lemma neg_pi_lt_shiftedLogCandidate_im
    {r s : ℝ} (_hr : 0 < r) (_hs : 0 < s)
    {z : ℂ} (_hz : z.im ≤ 0) :
    -Real.pi <
      (Complex.log (shiftedRate s z (-r)) -
        Complex.log (shiftedRate s z r) +
        (Real.pi : ℂ) * Complex.I).im := by
  rw [shiftedLogCandidate_im]
  have hdiff := Complex.abs_arg_sub_arg_lt
    (shiftedRate s z (-r)) (shiftedRate s z r)
  have hleft :
      -2 * Real.pi <
        (shiftedRate s z (-r)).arg - (shiftedRate s z r).arg := by
    linarith [(abs_lt.mp hdiff).1]
  linarith

lemma exp_pi_mul_I :
    Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
  rw [Complex.exp_mul_I]
  simp

lemma exp_shiftedLogCandidate
    {r s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≤ 0) :
    Complex.exp
        (Complex.log (shiftedRate s z (-r)) -
          Complex.log (shiftedRate s z r) +
          (Real.pi : ℂ) * Complex.I) =
      -shiftedRate s z (-r) / shiftedRate s z r := by
  have hm : shiftedRate s z (-r) ≠ 0 := shiftedRate_ne_zero hs hz (-r)
  have hp : shiftedRate s z r ≠ 0 := shiftedRate_ne_zero hs hz r
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_log hm,
    Complex.exp_log hp, exp_pi_mul_I]
  field_simp [hp]

/-- Exact principal-log identity used in Section 3.2. -/
theorem log_neg_shiftedRate_div
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    Complex.log (-shiftedRate s z (-r) / shiftedRate s z r) =
      Complex.log (shiftedRate s z (-r)) -
        Complex.log (shiftedRate s z r) +
        (Real.pi : ℂ) * Complex.I := by
  let w : ℂ :=
    Complex.log (shiftedRate s z (-r)) -
      Complex.log (shiftedRate s z r) +
      (Real.pi : ℂ) * Complex.I
  have hwlo : -Real.pi < w.im := by
    simpa [w] using neg_pi_lt_shiftedLogCandidate_im hr hs hz
  have hwhi : w.im ≤ Real.pi := by
    simpa [w] using shiftedLogCandidate_im_le_pi hr hs hz
  have hexp : Complex.exp w =
      -shiftedRate s z (-r) / shiftedRate s z r := by
    simpa [w] using exp_shiftedLogCandidate (r := r) hs hz
  calc
    Complex.log (-shiftedRate s z (-r) / shiftedRate s z r)
        = Complex.log (Complex.exp w) := by rw [hexp]
    _ = w := Complex.log_exp hwlo hwhi
    _ = _ := rfl

/-- The same identity written directly for the Mobius factor appearing in the
shifted dual function. -/
theorem log_dualMobius_shift
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ 0) :
    Complex.log (dualMobius r (z - Complex.I * (s : ℂ))) =
      Complex.log (shiftedRate s z (-r)) -
        Complex.log (shiftedRate s z r) +
        (Real.pi : ℂ) * Complex.I := by
  rw [dualMobius_shift_eq_rate_ratio hs hz]
  exact log_neg_shiftedRate_div hr hs hz

end LCHSWiener
