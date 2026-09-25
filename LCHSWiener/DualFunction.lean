import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import LCHSWiener.Core

noncomputable section

open Set

namespace LCHSWiener

/-!
# The dual function from Section 3.1

This file formalizes the elementary complex-variable identities behind

  Phi_{R,c}(z) = exp (-pi*c - i*c*Log ((R-z)/(R+z))).

We use Mathlib's principal `Complex.log`.  On the open lower half-plane the
Mobius factor `(R-z)/(R+z)` lies in the open upper half-plane (for `R > 0`),
so its principal argument is in `(0, pi)`.  Hence this is exactly the branch
of `Log` used in the note.

The parameter used in the note is `a = exp (-pi*c)`.  The final theorem
`dualPhiC_neg_I` proves the exact value

  Phi_{R,c}(-i) = a^(p_R).

There are no axioms or placeholders in this file.
-/

/-- The open lower half-plane. -/
def lowerHalfPlane : Set ℂ := {z : ℂ | z.im < 0}

/-- The Mobius factor `(R-z)/(R+z)` occurring in the dual function. -/
def dualMobius (R : ℝ) (z : ℂ) : ℂ :=
  ((R : ℂ) - z) / ((R : ℂ) + z)

/-- The `c`-parametrized dual function.  Here `a = exp (-pi*c)`. -/
def dualPhiC (R c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
    (-(Real.pi * c : ℝ) - Complex.I * (c : ℂ) * Complex.log (dualMobius R z))

/-- The real parameter `a = exp (-pi*c)`. -/
def dualA (c : ℝ) : ℝ := Real.exp (-Real.pi * c)

@[simp] lemma dualA_pos (c : ℝ) : 0 < dualA c := by
  simp [dualA, Real.exp_pos]

lemma dualA_le_one {c : ℝ} (hc : 0 ≤ c) : dualA c ≤ 1 := by
  rw [dualA, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by positivity)

lemma neg_I_mem_lowerHalfPlane : -Complex.I ∈ lowerHalfPlane := by
  simp [lowerHalfPlane]

/-- The denominator cannot vanish in the strict lower half-plane. -/
lemma dualMobius_den_ne_zero {R : ℝ} {z : ℂ}
    (hz : z.im < 0) : (R : ℂ) + z ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

/--
Imaginary part of the Mobius map.  Written with `normSq` to avoid square
roots; this is the identity

  Im ((R-z)/(R+z)) = -2 R Im(z) / |R+z|^2.
-/
lemma dualMobius_im_formula {R : ℝ} {z : ℂ} (hz : z.im < 0) :
    (dualMobius R z).im =
      (-2 * R * z.im) / Complex.normSq ((R : ℂ) + z) := by
  have hden : (R : ℂ) + z ≠ 0 := dualMobius_den_ne_zero hz
  rw [dualMobius, div_eq_mul_inv]
  rw [Complex.inv_def]
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im]
  have hns : Complex.normSq ((R : ℂ) + z) ≠ 0 := by
    exact (Complex.normSq_ne_zero).2 hden
  field_simp [hns]
  ring

/-- For `R>0`, the Mobius map sends the strict lower half-plane to the
strict upper half-plane. -/
lemma dualMobius_im_pos {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z.im < 0) : 0 < (dualMobius R z).im := by
  rw [dualMobius_im_formula hz]
  have hden : (R : ℂ) + z ≠ 0 := dualMobius_den_ne_zero hz
  have hns : 0 < Complex.normSq ((R : ℂ) + z) :=
    (Complex.normSq_pos).2 hden
  exact div_pos (by positivity) hns

/-- The Mobius factor belongs to the principal-log slit plane on the lower
half-plane. -/
lemma dualMobius_mem_slitPlane {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z.im < 0) : dualMobius R z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inr (ne_of_gt (dualMobius_im_pos hR hz))

/-- On the lower half-plane, the principal argument of the Mobius factor is
strictly between `0` and `pi`.  Thus Mathlib's principal `Complex.log` is the
branch required by the note. -/
lemma dualMobius_arg_mem {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z.im < 0) :
    0 < (dualMobius R z).arg ∧ (dualMobius R z).arg < Real.pi := by
  have him : 0 < (dualMobius R z).im := dualMobius_im_pos hR hz
  constructor
  · have hnonneg : 0 ≤ (dualMobius R z).arg :=
      (Complex.arg_nonneg_iff).2 (le_of_lt him)
    refine lt_of_le_of_ne hnonneg ?_
    intro hzero
    have hs : Real.sin (dualMobius R z).arg = 0 := by rw [hzero, Real.sin_zero]
    rw [Complex.sin_arg] at hs
    have hn : 0 < ‖dualMobius R z‖ := norm_pos_iff.mpr (by
      intro hm
      have := congrArg Complex.im hm
      simp [him.ne'] at this)
    have : (dualMobius R z).im = 0 := by
      apply (div_eq_zero_iff).mp at hs
      rcases hs with hs | hs
      · exact hs
      · exact False.elim (hn.ne' hs)
    linarith
  · exact (Complex.arg_lt_pi_iff).2 (Or.inr (ne_of_gt him))

/-- The Mobius map is analytic at every point of the lower half-plane. -/
lemma analyticAt_dualMobius_of_den_ne {R : ℝ} {z : ℂ}
    (hden : (R : ℂ) + z ≠ 0) : AnalyticAt ℂ (dualMobius R) z := by
  rw [dualMobius]
  exact (analyticAt_const.sub analyticAt_id).div
    (analyticAt_const.add analyticAt_id) hden

lemma analyticAt_dualMobius {R : ℝ} {z : ℂ} (hz : z.im < 0) :
    AnalyticAt ℂ (dualMobius R) z :=
  analyticAt_dualMobius_of_den_ne (dualMobius_den_ne_zero hz)

/-- The chosen principal logarithm of the Mobius factor is analytic throughout
our lower-half-plane domain. -/
lemma analyticAt_log_dualMobius {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hz : z.im < 0) :
    AnalyticAt ℂ (fun w : ℂ => Complex.log (dualMobius R w)) z := by
  exact (analyticAt_dualMobius hz).clog (dualMobius_mem_slitPlane hR hz)

/-- `Phi_{R,c}` is analytic on the strict lower half-plane. -/
theorem analyticOnNhd_dualPhiC {R c : ℝ} (hR : 0 < R) :
    AnalyticOnNhd ℂ (dualPhiC R c) lowerHalfPlane := by
  intro z hz
  have hz' : z.im < 0 := hz
  have hlog := analyticAt_log_dualMobius hR hz'
  rw [dualPhiC]
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (-(Real.pi * c : ℝ) : ℂ)) z :=
    analyticAt_const
  have hmul : AnalyticAt ℂ
      (fun w : ℂ => Complex.I * (c : ℂ) * Complex.log (dualMobius R w)) z := by
    exact (analyticAt_const.mul analyticAt_const).mul hlog
  exact (hconst.sub hmul).cexp'

/-- Exact norm formula for the dual function in terms of the principal
argument of the Mobius factor. -/
lemma norm_dualPhiC (R c : ℝ) (z : ℂ) :
    ‖dualPhiC R c z‖ =
      Real.exp (-Real.pi * c + c * (dualMobius R z).arg) := by
  rw [dualPhiC, Complex.norm_exp]
  congr 1
  rw [Complex.log_im]
  simp [Complex.mul_re]
  ring

/-- The `H^infty` bound from (3.6): in the strict lower half-plane,
`|Phi| <= 1` whenever `c >= 0`. -/
lemma norm_dualPhiC_le_one {R c : ℝ} {z : ℂ}
    (hR : 0 < R) (hc : 0 ≤ c) (hz : z.im < 0) :
    ‖dualPhiC R c z‖ ≤ 1 := by
  rw [norm_dualPhiC, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have harg := (dualMobius_arg_mem hR hz).2
  nlinarith [Real.pi_pos]

/-- On a real point strictly inside `(-R,R)`, the Mobius factor is a positive
real number. -/
lemma dualMobius_real_pos {R k : ℝ} (hk : |k| < R) :
    0 < ((R - k) / (R + k)) := by
  have hklo : -R < k := (abs_lt.mp hk).1
  have hkhi : k < R := (abs_lt.mp hk).2
  exact div_pos (sub_pos.mpr hkhi) (add_pos_of_neg_lt_left hklo)

/-- Inside the interval, the principal argument is zero. -/
lemma dualMobius_arg_real_inside {R k : ℝ} (hk : |k| < R) :
    (dualMobius R (k : ℂ)).arg = 0 := by
  have hp : 0 < (R - k) / (R + k) := dualMobius_real_pos hk
  have heq : dualMobius R (k : ℂ) = (((R - k) / (R + k) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [dualMobius]
  rw [heq]
  exact Complex.arg_ofReal_of_nonneg (le_of_lt hp)

/-- Boundary modulus on the interior of the truncation interval:
`|Phi(k)| = exp(-pi*c) = a`. -/
lemma norm_dualPhiC_real_inside {R c k : ℝ} (hk : |k| < R) :
    ‖dualPhiC R c (k : ℂ)‖ = dualA c := by
  rw [norm_dualPhiC, dualMobius_arg_real_inside hk]
  simp [dualA]


/-- At a real point strictly inside `(-R,R)`, the denominator of the Mobius
map is nonzero. -/
lemma dualMobius_den_ne_zero_real_inside {R k : ℝ} (hk : |k| < R) :
    (R : ℂ) + (k : ℂ) ≠ 0 := by
  have hklo : -R < k := (abs_lt.mp hk).1
  have hpos : 0 < R + k := by linarith
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

/-- The dual function extends analytically through every real point strictly
inside the truncation interval.  This is the form used after replacing `R`
by `r > R` in Section 3.2. -/
theorem analyticAt_dualPhiC_real_inside {R c k : ℝ} (hk : |k| < R) :
    AnalyticAt ℂ (dualPhiC R c) (k : ℂ) := by
  have hmob : AnalyticAt ℂ (dualMobius R) (k : ℂ) :=
    analyticAt_dualMobius_of_den_ne (dualMobius_den_ne_zero_real_inside hk)
  have hp : 0 < (R - k) / (R + k) := dualMobius_real_pos hk
  have heq : dualMobius R (k : ℂ) = (((R - k) / (R + k) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [dualMobius]
  have hslit : dualMobius R (k : ℂ) ∈ Complex.slitPlane := by
    rw [heq, Complex.ofReal_mem_slitPlane]
    exact hp
  have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log (dualMobius R w)) (k : ℂ) :=
    hmob.clog hslit
  have hconst : AnalyticAt ℂ
      (fun _ : ℂ => (-(Real.pi * c : ℝ) : ℂ)) (k : ℂ) := analyticAt_const
  have hmul : AnalyticAt ℂ
      (fun w : ℂ => Complex.I * (c : ℂ) * Complex.log (dualMobius R w)) (k : ℂ) := by
    exact (analyticAt_const.mul analyticAt_const).mul hlog
  simpa [dualPhiC] using (hconst.sub hmul).cexp'

/-- In particular the boundary-value function is continuous at each real
point strictly inside `(-R,R)`. -/
theorem continuousAt_dualPhiC_real_inside {R c k : ℝ} (hk : |k| < R) :
    ContinuousAt (dualPhiC R c) (k : ℂ) :=
  (analyticAt_dualPhiC_real_inside (c := c) hk).continuousAt

/-- If `r > R`, then `Phi_{r,c}` is analytic at every real point of the
closed interval `[-R,R]`. -/
theorem analyticAt_dualPhiC_on_smaller_closed_interval
    {R r c k : ℝ} (hRr : R < r) (hk : |k| ≤ R) :
    AnalyticAt ℂ (dualPhiC r c) (k : ℂ) := by
  apply analyticAt_dualPhiC_real_inside
  exact lt_of_le_of_lt hk hRr

/-- For a real point outside `[-R,R]`, the Mobius factor is negative. -/
lemma dualMobius_real_neg {R k : ℝ} (hR : 0 < R) (hk : R < |k|) :
    (R - k) / (R + k) < 0 := by
  rcases lt_or_gt_of_ne (ne_of_gt hR) k with hkneg | hkpos
  · have hkabs : |k| = -k := abs_of_neg hkneg
    rw [hkabs] at hk
    have hnum : 0 < R - k := by linarith
    have hden : R + k < 0 := by linarith
    exact div_neg_of_pos_of_neg hnum hden
  · have hkabs : |k| = k := abs_of_pos hkpos
    rw [hkabs] at hk
    have hnum : R - k < 0 := by linarith
    have hden : 0 < R + k := by linarith
    exact div_neg_of_neg_of_pos hnum hden

/-- Outside the interval, the principal argument is `pi`. -/
lemma dualMobius_arg_real_outside {R k : ℝ}
    (hR : 0 < R) (hk : R < |k|) :
    (dualMobius R (k : ℂ)).arg = Real.pi := by
  have hn : (R - k) / (R + k) < 0 := dualMobius_real_neg hR hk
  have heq : dualMobius R (k : ℂ) = (((R - k) / (R + k) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [dualMobius]
  rw [heq]
  exact Complex.arg_ofReal_of_neg hn

/-- Boundary modulus outside the truncation interval: `|Phi(k)| = 1`. -/
lemma norm_dualPhiC_real_outside {R c k : ℝ}
    (hR : 0 < R) (hk : R < |k|) :
    ‖dualPhiC R c (k : ℂ)‖ = 1 := by
  rw [norm_dualPhiC, dualMobius_arg_real_outside hR hk]
  rw [← Real.exp_zero]
  congr 1
  ring

/-- The value of the Mobius factor at `-i`. -/
lemma dualMobius_neg_I (R : ℝ) :
    dualMobius R (-Complex.I) = ((R : ℂ) + Complex.I) / ((R : ℂ) - Complex.I) := by
  simp [dualMobius]

/-- Its norm at `-i` is one. -/
lemma norm_dualMobius_neg_I {R : ℝ} (hR : 0 < R) :
    ‖dualMobius R (-Complex.I)‖ = 1 := by
  rw [dualMobius_neg_I, norm_div]
  have h1 : ‖(R : ℂ) + Complex.I‖ = Real.sqrt (R^2 + 1) := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply]
  have h2 : ‖(R : ℂ) - Complex.I‖ = Real.sqrt (R^2 + 1) := by
    rw [Complex.norm_def]
    simp [Complex.normSq_apply]
  rw [h1, h2]
  have hs : Real.sqrt (R ^ 2 + 1) ≠ 0 := by positivity
  exact div_self hs

/-- Real part of the Mobius factor at `-i`. -/
lemma dualMobius_neg_I_re {R : ℝ} (hR : 0 < R) :
    (dualMobius R (-Complex.I)).re = (R^2 - 1) / (R^2 + 1) := by
  rw [dualMobius_neg_I, Complex.div_re]
  simp [Complex.normSq_apply]
  ring

/-- The elementary double-angle identity needed to identify the argument at
`-i`. -/
lemma cos_two_arctan_inv {R : ℝ} (hR : 0 < R) :
    Real.cos (2 * Real.arctan R⁻¹) = (R^2 - 1) / (R^2 + 1) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hden : R ^ 2 + 1 ≠ 0 := by positivity
  field_simp [hR0, hden]
  ring

/-- The exact principal argument of the Mobius factor at `-i`. -/
lemma dualMobius_arg_neg_I {R : ℝ} (hR : 0 < R) :
    (dualMobius R (-Complex.I)).arg = 2 * Real.arctan R⁻¹ := by
  have him : 0 < (dualMobius R (-Complex.I)).im := by
    apply dualMobius_im_pos hR
    simp
  rw [Complex.arg_of_im_pos him]
  rw [norm_dualMobius_neg_I hR, div_one, dualMobius_neg_I_re hR]
  rw [← cos_two_arctan_inv hR]
  apply Real.arccos_cos
  · have hi : 0 < R⁻¹ := inv_pos.mpr hR
    have ha : 0 < Real.arctan R⁻¹ := (Real.arctan_pos).2 hi
    linarith
  · have ha : Real.arctan R⁻¹ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    linarith

/-- At `-i`, the principal log is purely imaginary with the exact argument
`2 arctan(1/R)`. -/
lemma log_dualMobius_neg_I {R : ℝ} (hR : 0 < R) :
    Complex.log (dualMobius R (-Complex.I)) =
      (2 * Real.arctan R⁻¹ : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [Complex.log_re, norm_dualMobius_neg_I hR]
    simp
  · rw [Complex.log_im, dualMobius_arg_neg_I hR]
    simp

/-- `2 arctan(1/R) = pi q_R`. -/
lemma two_arctan_inv_eq_pi_mul_qR {R : ℝ} (hR : 0 < R) :
    2 * Real.arctan R⁻¹ = Real.pi * qR R := by
  rw [qR_eq_arctan_inv hR]
  field_simp [Real.pi_ne_zero]
  ring

/-- Exact value in (3.6): if `a = exp(-pi*c)`, then
`Phi_{R,c}(-i) = a^(p_R)`. -/
theorem dualPhiC_neg_I {R c : ℝ} (hR : 0 < R) :
    dualPhiC R c (-Complex.I) = (((dualA c) ^ (pR R) : ℝ) : ℂ) := by
  rw [dualPhiC, log_dualMobius_neg_I hR]
  have htheta := two_arctan_inv_eq_pi_mul_qR hR
  have hpq := pR_add_qR R
  have hexponent :
      (-(Real.pi * c : ℂ) - Complex.I * (c : ℂ) *
          ((2 * Real.arctan R⁻¹ : ℝ) * Complex.I)) =
        (((-Real.pi * c) * pR R : ℝ) : ℂ) := by
    push_cast
    rw [htheta]
    simp [Complex.I_mul_I]
    have hp : pR R = 1 - qR R := by linarith
    rw [hp]
    ring
  rw [hexponent, ← Complex.ofReal_exp]
  norm_cast
  rw [dualA, ← Real.exp_mul]

/-- The exact statement of (3.6), collected in one theorem.  Endpoint values
`k = +/-R` are intentionally excluded, exactly as in the note. -/
theorem dualPhiC_properties {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) :
    AnalyticOnNhd ℂ (dualPhiC R c) lowerHalfPlane ∧
    (∀ z ∈ lowerHalfPlane, ‖dualPhiC R c z‖ ≤ 1) ∧
    (∀ k : ℝ, |k| < R → ‖dualPhiC R c (k : ℂ)‖ = dualA c) ∧
    (∀ k : ℝ, R < |k| → ‖dualPhiC R c (k : ℂ)‖ = 1) ∧
    dualPhiC R c (-Complex.I) = (((dualA c) ^ (pR R) : ℝ) : ℂ) := by
  refine ⟨analyticOnNhd_dualPhiC hR, ?_, ?_, ?_, dualPhiC_neg_I hR⟩
  · intro z hz
    exact norm_dualPhiC_le_one hR hc hz
  · intro k hk
    exact norm_dualPhiC_real_inside hk
  · intro k hk
    exact norm_dualPhiC_real_outside hR hk

end LCHSWiener
