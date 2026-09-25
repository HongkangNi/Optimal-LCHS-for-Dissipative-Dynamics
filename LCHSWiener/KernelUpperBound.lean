import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import LCHSWiener.Core
import LCHSWiener.DualFunction
import LCHSWiener.DensityMeasure
import LCHSWiener.WienerDualBound

noncomputable section

open Set MeasureTheory Filter intervalIntegral scoped Topology

namespace LCHSWiener

/-!
# Sharp explicit upper bound

This file formalizes the Wiener part of Section 3.3.  We use the lower-side
boundary value of

  exp(pi*C*q_R) / (pi(1+z^2)) * exp(i*C*Log((R-z)/(R+z))).

Closing a rectangle in the lower half-plane gives its half-line Fourier
transform.  The only pole enclosed is `-i`; its residue is normalized so that
the full boundary measure has transform `exp(-x)` for `x >= 0`.  Splitting the
boundary measure into `|k|<R` and `|k|>R` gives the approximant and its residual.
-/

/-- Cauchy density. -/
def cauchyDensity (k : ℝ) : ℝ := 1 / (Real.pi * (1 + k^2))

lemma cauchyDensity_nonneg (k : ℝ) : 0 ≤ cauchyDensity k := by
  unfold cauchyDensity
  positivity

lemma integrable_cauchyDensity : Integrable cauchyDensity volume := by
  simpa [cauchyDensity, ProbabilityTheory.cauchyPDFReal] using
    (ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := (1 : NNReal)))

/-- Mass of the central Cauchy interval. -/
theorem integral_cauchyDensity_Icc {R : ℝ} (hR : 0 ≤ R) :
    ∫ k in Set.Icc (-R) R, cauchyDensity k = pR R := by
  rw [← intervalIntegral.integral_of_le (by linarith)]
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => Real.arctan x / Real.pi)
        (1 / (Real.pi * (1+x^2))) x := by
    intro x
    convert (Real.hasDerivAt_arctan x).div_const Real.pi using 1 <;>
      field_simp [Real.pi_ne_zero] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  simp [cauchyDensity, pR, Real.arctan_neg]
  ring

/-- Cauchy mass outside the truncation interval. -/
theorem integral_cauchyDensity_compl_Icc {R : ℝ} (hR : 0 ≤ R) :
    ∫ k in (Set.Icc (-R) R)ᶜ, cauchyDensity k = qR R := by
  have hall : ∫ k : ℝ, cauchyDensity k = 1 := by
    simpa [cauchyDensity, ProbabilityTheory.cauchyPDFReal] using
      ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 (γ := (1 : NNReal))
        (by norm_num)
  have hsplit := integral_add_compl (μ := volume)
    (integrable_cauchyDensity.integrableOn)
    (MeasurableSet.Icc : MeasurableSet (Set.Icc (-R) R))
  rw [integral_cauchyDensity_Icc hR, hall] at hsplit
  linarith [pR_add_qR R]

/-- Lower-half-plane boundary logarithm of `(R-z)/(R+z)` on the real axis.
The values at the two endpoints are irrelevant for Lebesgue integration. -/
def lowerBoundaryLog (R k : ℝ) : ℂ :=
  if |k| < R then
    (Real.log ((R-k)/(R+k)) : ℂ)
  else if k = R ∨ k = -R then 0
  else
    (Real.log |(R-k)/(R+k)| : ℂ) + (Real.pi : ℂ) * Complex.I

/-- Full boundary density used by the contour argument. -/
def fullOuterDensity (R C : ℝ) (k : ℝ) : ℂ :=
  (Real.exp (Real.pi*C*qR R) * cauchyDensity k : ℝ) *
    Complex.exp (Complex.I * (C:ℂ) * lowerBoundaryLog R k)

/-- Truncated approximant density. -/
def innerOuterDensity (R C : ℝ) (k : ℝ) : ℂ :=
  (Set.Ioo (-R) R).indicator (fullOuterDensity R C) k

/-- Residual/tail density. -/
def tailOuterDensity (R C : ℝ) (k : ℝ) : ℂ :=
  ((Set.Icc (-R) R)ᶜ).indicator (fullOuterDensity R C) k

lemma lowerBoundaryLog_inside {R k : ℝ} (hk : |k| < R) :
    lowerBoundaryLog R k = (Real.log ((R-k)/(R+k)) : ℂ) := by
  simp [lowerBoundaryLog, hk]

lemma lowerBoundaryLog_outside_im {R k : ℝ}
    (hk : R < |k|) : (lowerBoundaryLog R k).im = Real.pi := by
  have hkR : k ≠ R := by
    intro h; subst h; simpa [abs_of_nonneg (le_of_lt hk)] using hk
  have hknR : k ≠ -R := by
    intro h; subst h; simpa [abs_neg] using hk
  simp [lowerBoundaryLog, not_lt.mpr hk.le, hkR, hknR]

lemma norm_fullOuterDensity_inside {R C k : ℝ}
    (hk : |k| < R) :
    ‖fullOuterDensity R C k‖ =
      Real.exp (Real.pi*C*qR R) * cauchyDensity k := by
  rw [fullOuterDensity, lowerBoundaryLog_inside hk, norm_mul,
    Complex.norm_real, Complex.norm_exp]
  have : (Complex.I * (C:ℂ) *
      (Real.log ((R-k)/(R+k)) : ℂ)).re = 0 := by simp
  rw [this, Real.exp_zero]
  simp [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (cauchyDensity_nonneg k))]

lemma norm_fullOuterDensity_outside {R C k : ℝ}
    (hC : 0 ≤ C) (hk : R < |k|) :
    ‖fullOuterDensity R C k‖ =
      Real.exp (-Real.pi*C*pR R) * cauchyDensity k := by
  rw [fullOuterDensity, norm_mul, Complex.norm_real, Complex.norm_exp]
  have him := lowerBoundaryLog_outside_im (R:=R) (k:=k) hk
  have hre : (Complex.I * (C:ℂ) * lowerBoundaryLog R k).re = -C*Real.pi := by
    simp [Complex.mul_re, him]
    ring
  rw [hre]
  have hq : qR R = 1 - pR R := rfl
  have hexp : Real.exp (Real.pi*C*qR R) * Real.exp (-C*Real.pi) =
      Real.exp (-Real.pi*C*pR R) := by
    rw [← Real.exp_add]
    congr 1
    rw [hq]
    ring
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (cauchyDensity_nonneg k)), hexp]

lemma integrable_fullOuterDensity {R C : ℝ} (hC : 0 ≤ C) :
    Integrable (fullOuterDensity R C) volume := by
  apply Integrable.mono' (integrable_cauchyDensity.const_mul
    (Real.exp (Real.pi*C*qR R) + Real.exp (-Real.pi*C*pR R)))
  · fun_prop
  · filter_upwards with k
    by_cases hk : |k| < R
    · rw [norm_fullOuterDensity_inside hk]
      have : Real.exp (Real.pi*C*qR R) ≤
          Real.exp (Real.pi*C*qR R) + Real.exp (-Real.pi*C*pR R) := by positivity
      simpa [norm_mul, abs_of_nonneg (cauchyDensity_nonneg k)] using
        mul_le_mul_of_nonneg_right this (cauchyDensity_nonneg k)
    · by_cases he : |k| = R
      · subst_vars
        simp [fullOuterDensity, cauchyDensity_nonneg]
      · have hk' : R < |k| := lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm he)
        rw [norm_fullOuterDensity_outside hC hk']
        have : Real.exp (-Real.pi*C*pR R) ≤
          Real.exp (Real.pi*C*qR R) + Real.exp (-Real.pi*C*pR R) := by positivity
        simpa [norm_mul, abs_of_nonneg (cauchyDensity_nonneg k)] using
          mul_le_mul_of_nonneg_right this (cauchyDensity_nonneg k)

lemma integrable_innerOuterDensity {R C : ℝ} (hC : 0 ≤ C) :
    Integrable (innerOuterDensity R C) volume := by
  exact (integrable_fullOuterDensity hC).indicator measurableSet_Ioo

lemma integrable_tailOuterDensity {R C : ℝ} (hC : 0 ≤ C) :
    Integrable (tailOuterDensity R C) volume := by
  exact (integrable_fullOuterDensity hC).indicator MeasurableSet.Icc.compl

/-- L1 mass of the inner density. -/
theorem integral_norm_innerOuterDensity
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    ∫ k, ‖innerOuterDensity R C k‖ =
      pR R * Real.exp (Real.pi*C*qR R) := by
  rw [innerOuterDensity, ← integral_indicator measurableSet_Ioo]
  have hAE : ∀ᵐ k ∂volume.restrict (Set.Ioo (-R) R),
      ‖fullOuterDensity R C k‖ =
        Real.exp (Real.pi*C*qR R) * cauchyDensity k := by
    filter_upwards with k hk
    rw [norm_fullOuterDensity_inside]
    exact abs_lt.mpr hk
  rw [integral_congr_ae hAE]
  rw [MeasureTheory.integral_const_mul]
  have hIoo : ∫ k in Set.Ioo (-R) R, cauchyDensity k = pR R := by
    rw [← integral_cauchyDensity_Icc hR.le]
    apply integral_congr_ae
    filter_upwards with k
    by_cases hk : k = -R ∨ k = R <;> simp [hk]
  rw [hIoo]
  ring

/-- L1 mass of the tail density. -/
theorem integral_norm_tailOuterDensity
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    ∫ k, ‖tailOuterDensity R C k‖ =
      qR R * Real.exp (-Real.pi*C*pR R) := by
  rw [tailOuterDensity, ← integral_indicator MeasurableSet.Icc.compl]
  have hAE : ∀ᵐ k ∂volume.restrict ((Set.Icc (-R) R)ᶜ),
      ‖fullOuterDensity R C k‖ =
        Real.exp (-Real.pi*C*pR R) * cauchyDensity k := by
    filter_upwards with k hk
    have habs : R < |k| := by
      simpa [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] using hk
    exact norm_fullOuterDensity_outside hC habs
  rw [integral_congr_ae hAE, MeasureTheory.integral_const_mul,
    integral_cauchyDensity_compl_Icc hR.le]
  ring

/-- Meromorphic integrand used in the lower rectangle. -/
def contourKernel (R C x : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I*z*(x:ℂ)) *
    ((Real.exp (Real.pi*C*qR R) : ℂ) /
      ((Real.pi:ℂ) * (1+z^2))) *
    Complex.exp (Complex.I*(C:ℂ)*Complex.log (dualMobius R z))

/-- The residue normalization at the unique enclosed pole `-i`. -/
lemma contourKernel_residue_neg_I
    {R C x : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
      (∮ z in C(-Complex.I, (1/2:ℝ)), contourKernel R C x z) =
      Complex.exp (-(x:ℂ)) := by
  -- Factor `1+z^2=(z-i)(z+i)`.  On a small circle about `-i` all other
  -- factors are holomorphic.  Cauchy's integral formula evaluates the simple
  -- pole.  `dualPhiC_neg_I` supplies exactly the normalization
  -- `exp(pi*C*q_R)` needed to make the residue one.
  have hdisc : Metric.closedBall (-Complex.I) (1/2:ℝ) ⊆
      {z : ℂ | z ≠ Complex.I ∧ z ≠ (-R:ℂ) ∧ z ≠ (R:ℂ)} := by
    intro z hz
    have hzdist : dist z (-Complex.I) ≤ 1/2 := hz
    constructor
    · intro h; subst z; norm_num at hzdist
    constructor <;> intro h <;> subst z <;>
      simpa [Complex.dist_eq, hR.ne'] using hzdist
  have hhol : DiffContOnCl ℂ
      (fun z => Complex.exp (-Complex.I*z*(x:ℂ)) *
        ((Real.exp (Real.pi*C*qR R) : ℂ) /
          ((Real.pi:ℂ) * (z-Complex.I))) *
        Complex.exp (Complex.I*(C:ℂ)*Complex.log (dualMobius R z)))
      (Metric.ball (-Complex.I) (1/2:ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    fun_prop
  have hcauchy := hhol.two_pi_I_inv_smul_circleIntegral_sub_inv_smul
    (w := -Complex.I) (by norm_num)
  have hphi := dualPhiC_neg_I hR (c:=C)
  -- Unfold the regular factor at `-i` and simplify.
  simpa [contourKernel, div_eq_mul_inv, one_add_sq_factor,
    hphi, dualA, qR, pR_add_qR R] using hcauchy

/-- Full lower boundary transform.  This is the contour step of Section 3.3.
The proof uses rectangles with horizontal sides at `0` and `-T`, detours the
single pole `-i` by a fixed small circle, and then lets both horizontal width
and depth tend to infinity.  The vertical and lower sides vanish by the
Cauchy denominator and the factor `exp(-i z x)`; dominated convergence gives
the lower-side boundary values at the two logarithmic branch points. -/
theorem integral_fullOuterDensity_character
    {R C x : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    ∫ k : ℝ,
      Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ)) * fullOuterDensity R C k =
      Complex.exp (-(x:ℂ)) := by
  let F : ℂ → ℂ := contourKernel R C x
  have hFanalytic : DifferentiableOn ℂ F
      (lowerHalfPlane \ {-Complex.I}) := by
    intro z hz
    have hzim : z.im < 0 := hz.1
    have hzne : z ≠ -Complex.I := by simpa using hz.2
    unfold F contourKernel
    have hm := analyticAt_log_dualMobius hR hzim
    fun_prop
  have hrect : ∀ T : ℝ, 2 < T →
      (∫ t : ℝ in -T..T, F (t - Complex.I*(1/T:ℂ))) =
        2*(Real.pi:ℂ)*Complex.I*Complex.exp (-(x:ℂ)) +
        (∫ t : ℝ in -T..T, F (t - Complex.I*(T:ℂ))) +
        Complex.I * (∫ y : ℝ in (1/T)..T, F (T-Complex.I*(y:ℂ))) -
        Complex.I * (∫ y : ℝ in (1/T)..T, F (-T-Complex.I*(y:ℂ))) := by
    intro T hT
    -- Apply Cauchy--Goursat to the rectangle after removing a small circle
    -- around `-i`, then insert the circle value from the residue lemma.
    have hcg := Complex.integral_boundary_rect_eq_zero_of_differentiableOn_off_countable
      F (-T-Complex.I*(T:ℂ)) (T-Complex.I*(1/T:ℂ))
      ({-Complex.I} : Set ℂ) (Set.countable_singleton _)
    have hres := contourKernel_residue_neg_I hR hC hx
    simpa [F, Complex.smul_def] using sub_eq_iff_eq_add.mpr
      (by linear_combination hcg + (2*(Real.pi:ℂ)*Complex.I) * hres)
  have htop : Tendsto
      (fun n : ℕ => ∫ k : ℝ in (-(n+3:ℝ))..(n+3:ℝ),
        F (k-Complex.I*((1/(n+3:ℝ)):ℂ)))
      atTop
      (nhds (∫ k : ℝ,
        Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*fullOuterDensity R C k)) := by
    -- The boundary value is dominated by an integrable multiple of
    -- `(1+k^2)^{-1}` uniformly for sufficiently small shifts.
    apply tendsto_setIntegral_univ_of_monotone
    · exact integrable_fullOuterDensity hC |>.mul_left
        (by fun_prop)
    · filter_upwards with k
      exact tendsto_nhdsWithin_iff.2 ⟨by fun_prop, eventually_of_forall fun _ => trivial⟩
  have hbottom : Tendsto
      (fun n : ℕ => ∫ k : ℝ in (-(n+3:ℝ))..(n+3:ℝ),
        F (k-Complex.I*((n+3:ℝ):ℂ))) atTop (nhds 0) := by
    apply tendsto_zero_of_norm_tendsto_zero
    have hbound : ∀ n,
      ‖∫ k : ℝ in (-(n+3:ℝ))..(n+3:ℝ),
        F (k-Complex.I*((n+3:ℝ):ℂ))‖ ≤
        (2*(n+3)) * Real.exp (-(n+3)*x) /
          (Real.pi*((n+3)^2-1)) * Real.exp (Real.pi*C*qR R) := by
      intro n
      apply norm_intervalIntegral_le_of_norm_le_const
      intro k hk
      unfold F contourKernel
      have : ‖Complex.exp (-Complex.I*(k-Complex.I*((n+3:ℝ):ℂ))*(x:ℂ))‖ =
          Real.exp (-(n+3)*x) := by rw [Complex.norm_exp]; simp; ring_nf
      rw [norm_mul, this]
      gcongr <;> positivity
    exact squeeze_zero' (fun n => norm_nonneg _) hbound
      (by positivity)
  have hvertical : Tendsto
      (fun n : ℕ =>
        Complex.I*(∫ y : ℝ in (1/(n+3:ℝ))..(n+3:ℝ),
          F ((n+3)-Complex.I*(y:ℂ))) -
        Complex.I*(∫ y : ℝ in (1/(n+3:ℝ))..(n+3:ℝ),
          F (-(n+3)-Complex.I*(y:ℂ))))
      atTop (nhds 0) := by
    apply tendsto_zero_of_norm_tendsto_zero
    have hbound : ∀ n,
      ‖Complex.I*(∫ y : ℝ in (1/(n+3:ℝ))..(n+3:ℝ),
          F ((n+3)-Complex.I*(y:ℂ))) -
        Complex.I*(∫ y : ℝ in (1/(n+3:ℝ))..(n+3:ℝ),
          F (-(n+3)-Complex.I*(y:ℂ)))‖ ≤
        4 * Real.exp (Real.pi*C*qR R) / (Real.pi*(n+3)) := by
      intro n
      calc
        _ ≤ ‖∫ y : ℝ in (1/(n+3:ℝ))..(n+3:ℝ),
              F ((n+3)-Complex.I*(y:ℂ))‖ +
            ‖∫ y : ℝ in (1/(n+3:ℝ))..(n+3:ℝ),
              F (-(n+3)-Complex.I*(y:ℂ))‖ := by simpa using norm_sub_le _ _
        _ ≤ _ := by
          apply add_le_add <;>
            apply norm_intervalIntegral_le_of_norm_le_const <;>
            intro y hy <;> unfold F contourKernel <;> gcongr <;> positivity
    exact squeeze_zero' (fun n => norm_nonneg _) hbound (by positivity)
  have hlimit := tendsto_congr' (eventually_of_forall fun n =>
    hrect (n+3) (by positivity))
  have := hlimit.trans
    ((tendsto_const_nhds.add hbottom).add hvertical)
  have htop' := htop
  rw [show 2*(Real.pi:ℂ)*Complex.I*Complex.exp (-(x:ℂ)) /
      (2*(Real.pi:ℂ)*Complex.I) = Complex.exp (-(x:ℂ)) by
      field_simp [Real.pi_ne_zero, Complex.I_ne_zero]]
  exact tendsto_nhds_unique htop' this

/-- The inner and outer densities split the full boundary density a.e. -/
lemma fullOuterDensity_eq_inner_add_tail_ae {R C : ℝ} :
    fullOuterDensity R C =ᵐ[volume]
      fun k => innerOuterDensity R C k + tailOuterDensity R C k := by
  filter_upwards with k
  by_cases hinside : k ∈ Set.Ioo (-R) R
  · simp [innerOuterDensity, tailOuterDensity, hinside,
      Set.mem_Icc, hinside.1.le, hinside.2.le]
  · by_cases hend : k = -R ∨ k = R
    · rcases hend with rfl | rfl <;> simp [innerOuterDensity, tailOuterDensity]
    · have hout : k ∈ (Set.Icc (-R) R)ᶜ := by
        simp only [Set.mem_compl_iff, Set.mem_Icc]
        by_contra h
        push_neg at h
        exact hinside ⟨lt_of_le_of_ne h.1 (Ne.symm (by simpa using hend)),
          lt_of_le_of_ne h.2 (by simpa [or_comm] using hend)⟩
      simp [innerOuterDensity, tailOuterDensity, hinside, hout]

/-- Concrete sharp witness supplied by the outer kernel. -/
theorem outer_kernel_witness
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    ∃ mu nu : FiniteCMeasure,
      SupportedIn R mu ∧
      tv mu ≤ pR R * Real.exp (Real.pi*C*qR R) ∧
      RepresentsResidual mu nu ∧
      tv nu ≤ qR R * Real.exp (-Real.pi*C*pR R) := by
  let f := innerOuterDensity R C
  let g := tailOuterDensity R C
  have hf : Integrable f volume := integrable_innerOuterDensity hC
  have hg : Integrable g volume := integrable_tailOuterDensity hC
  let mu := finiteCMeasureOfDensity f hf
  let nu := finiteCMeasureOfDensity g hg
  refine ⟨mu, nu, ?_, ?_, ?_, ?_⟩
  · apply supportedIn_finiteCMeasureOfDensity hf
    filter_upwards with k hk
    simp [f, innerOuterDensity]
  · calc
      tv mu ≤ ∫ k, ‖f k‖ := tv_finiteCMeasureOfDensity_le hf
      _ = pR R * Real.exp (Real.pi*C*qR R) :=
        integral_norm_innerOuterDensity hR hC
  · intro x hx
    have hchar : ∀ h : ℝ → ℂ, Integrable h volume →
        Integrable (fun k => Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*h k) volume := by
      intro h hh
      apply hh.mono'
      · fun_prop
      · filter_upwards with k
        simp [norm_mul]
    rw [fsTransform_finiteCMeasureOfDensity hf x (hchar f hf)]
    rw [fsTransform_finiteCMeasureOfDensity hg x (hchar g hg)]
    have hfull := integral_fullOuterDensity_character hR hC hx
    have hsplit :
        (∫ k, Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*fullOuterDensity R C k) =
        (∫ k, Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*f k) +
        (∫ k, Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*g k) := by
      rw [← integral_add (hchar f hf) (hchar g hg)]
      apply integral_congr_ae
      filter_upwards [fullOuterDensity_eq_inner_add_tail_ae (R:=R) (C:=C)] with k hk
      rw [hk]
      ring
    rw [hfull] at hsplit
    linear_combination hsplit
  · calc
      tv nu ≤ ∫ k, ‖g k‖ := tv_finiteCMeasureOfDensity_le hg
      _ = qR R * Real.exp (-Real.pi*C*pR R) :=
        integral_norm_tailOuterDensity hR hC

/-- High-mass upper branch. -/
theorem wiener_upper_high
    {R lam : ℝ} (hR : 0 < R) (hlam : pR R ≤ lam) :
    ∀ eps > 0, ∃ e ∈ wienerCosts R lam,
      e < qR R * (pR R/lam)^(pR R/qR R) + eps := by
  intro eps heps
  have hp := pR_pos hR
  have hq := qR_pos hR
  have hlam0 : 0 < lam := lt_of_lt_of_le hp hlam
  let C : ℝ := Real.log (lam / pR R) / (Real.pi*qR R)
  have hratio : 1 ≤ lam / pR R := (le_div_iff₀ hp).2 (by simpa [mul_comm] using hlam)
  have hC : 0 ≤ C := by
    unfold C
    exact div_nonneg (Real.log_nonneg hratio) (mul_nonneg Real.pi_pos.le hq.le)
  obtain ⟨mu,nu,hsupp,hmu,hres,hnu⟩ := outer_kernel_witness hR hC
  have hmuEq : pR R * Real.exp (Real.pi*C*qR R) = lam := by
    rw [show Real.pi*C*qR R = Real.log (lam/pR R) by
      unfold C; field_simp [Real.pi_ne_zero, ne_of_gt hq]; ring]
    rw [Real.exp_log (div_pos hlam0 hp)]
    field_simp [ne_of_gt hp]
  have hnuEq : qR R * Real.exp (-Real.pi*C*pR R) =
      qR R * (pR R/lam)^(pR R/qR R) := by
    have hpos : 0 < pR R/lam := div_pos hp hlam0
    rw [show -Real.pi*C*pR R = Real.log (pR R/lam) * (pR R/qR R) by
      unfold C
      rw [Real.log_div (ne_of_gt hlam0) (ne_of_gt hp),
        Real.log_div (ne_of_gt hp) (ne_of_gt hlam0)]
      field_simp [Real.pi_ne_zero, ne_of_gt hq]
      ring]
    rw [Real.rpow_def_of_pos hpos]
    congr 2
    ring
  refine ⟨tv nu, ?_, ?_⟩
  · exact ⟨mu,nu,hsupp,by simpa [hmuEq] using hmu,hres,rfl⟩
  · rw [← hnuEq]
    linarith

/-- Low-mass upper branch, obtained from the `C=0` Cauchy witness by scaling
only the inner interval. -/
theorem wiener_upper_low
    {R lam : ℝ} (hR : 0 < R) (hlam0 : 0 ≤ lam) (hlam : lam ≤ pR R) :
    ∀ eps > 0, ∃ e ∈ wienerCosts R lam, e < 1-lam+eps := by
  intro eps heps
  have hp := pR_pos hR
  let alpha := lam / pR R
  have ha0 : 0 ≤ alpha := div_nonneg hlam0 hp.le
  have ha1 : alpha ≤ 1 := (div_le_one hp).2 hlam
  let rhoIn : ℝ → ℂ := fun k =>
    (alpha:ℂ) * (Set.Ioo (-R) R).indicator (fun t => (cauchyDensity t : ℂ)) k
  let rhoOut : ℝ → ℂ := fun k =>
    (((1-alpha):ℂ) * (Set.Ioo (-R) R).indicator
      (fun t => (cauchyDensity t : ℂ)) k) +
      ((Set.Icc (-R) R)ᶜ).indicator (fun t => (cauchyDensity t : ℂ)) k
  have hin : Integrable rhoIn volume := by
    unfold rhoIn
    exact ((integrable_cauchyDensity.ofReal.indicator measurableSet_Ioo).const_mul _)
  have hout : Integrable rhoOut volume := by
    unfold rhoOut
    exact (((integrable_cauchyDensity.ofReal.indicator measurableSet_Ioo).const_mul _).add
      (integrable_cauchyDensity.ofReal.indicator MeasurableSet.Icc.compl))
  let mu := finiteCMeasureOfDensity rhoIn hin
  let nu := finiteCMeasureOfDensity rhoOut hout
  have hsupp : SupportedIn R mu := by
    apply supportedIn_finiteCMeasureOfDensity hin
    filter_upwards with k
    simp [rhoIn]
  have hmu : tv mu ≤ lam := by
    calc
      tv mu ≤ ∫ k, ‖rhoIn k‖ := tv_finiteCMeasureOfDensity_le hin
      _ = alpha * pR R := by
        rw [rhoIn]
        simp_rw [norm_mul, Complex.norm_real,
          abs_of_nonneg ha0, Set.norm_indicator]
        rw [← integral_indicator measurableSet_Ioo,
          integral_cauchyDensity_Icc hR.le]
      _ = lam := by field_simp [ne_of_gt hp]
  have hres : RepresentsResidual mu nu := by
    intro x hx
    have hfull := integral_fullOuterDensity_character hR (C:=0) (by positivity) hx
    have hchar : ∀ h : ℝ → ℂ, Integrable h volume →
        Integrable (fun k => Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*h k) volume := by
      intro h hh
      apply hh.mono' <;> try fun_prop
      filter_upwards with k
      simp [norm_mul]
    rw [fsTransform_finiteCMeasureOfDensity hin x (hchar rhoIn hin)]
    rw [fsTransform_finiteCMeasureOfDensity hout x (hchar rhoOut hout)]
    have hfull0 : fullOuterDensity R 0 =ᵐ[volume]
        fun k => (cauchyDensity k : ℂ) := by
      filter_upwards with k
      simp [fullOuterDensity]
    rw [integral_congr_ae (hfull0.fun_comp fun z =>
      Complex.exp (-Complex.I*(z:ℂ)*(x:ℂ))*z)] at hfull
    have hpartition : ∀ᵐ k ∂volume,
        (cauchyDensity k : ℂ) = rhoIn k + rhoOut k := by
      filter_upwards with k
      by_cases hk : k ∈ Set.Ioo (-R) R
      · simp [rhoIn,rhoOut,hk, Set.mem_Icc, hk.1.le,hk.2.le]
        ring
      · by_cases he : k = -R ∨ k = R
        · rcases he with rfl|rfl <;> simp [rhoIn,rhoOut]
        · have houtside : k ∈ (Set.Icc (-R) R)ᶜ := by
            simp only [Set.mem_compl_iff, Set.mem_Icc]
            by_contra h
            push_neg at h
            exact hk ⟨lt_of_le_of_ne h.1 (Ne.symm (by simpa using he)),
              lt_of_le_of_ne h.2 (by simpa [or_comm] using he)⟩
          simp [rhoIn,rhoOut,hk,houtside]
    have hsplit :
        (∫ k, Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*(cauchyDensity k:ℂ)) =
          (∫ k, Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*rhoIn k) +
          (∫ k, Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ))*rhoOut k) := by
      rw [← integral_add (hchar rhoIn hin) (hchar rhoOut hout)]
      apply integral_congr_ae
      filter_upwards [hpartition] with k hk
      rw [hk]
      ring
    rw [hfull] at hsplit
    linear_combination hsplit
  have hnu : tv nu ≤ 1-lam := by
    calc
      tv nu ≤ ∫ k, ‖rhoOut k‖ := tv_finiteCMeasureOfDensity_le hout
      _ = (1-alpha)*pR R + qR R := by
        unfold rhoOut
        have hnonneg : 0 ≤ 1-alpha := sub_nonneg.mpr ha1
        rw [integral_add]
        · simp_rw [norm_mul, Complex.norm_real, abs_of_nonneg hnonneg,
            Set.norm_indicator]
          rw [← integral_indicator measurableSet_Ioo,
            integral_cauchyDensity_Icc hR.le]
        · simp_rw [Set.norm_indicator, Complex.norm_real,
            abs_of_nonneg (cauchyDensity_nonneg _)]
          rw [← integral_indicator MeasurableSet.Icc.compl,
            integral_cauchyDensity_compl_Icc hR.le]
        · exact ((integrable_cauchyDensity.indicator measurableSet_Ioo).norm.const_mul _)
        · exact (integrable_cauchyDensity.indicator MeasurableSet.Icc.compl).norm
      _ = 1-lam := by
        rw [pR_add_qR]
        unfold alpha
        field_simp [ne_of_gt hp]
        ring
  refine ⟨tv nu, ⟨mu,nu,hsupp,hmu,hres,rfl⟩, ?_⟩
  linarith

end LCHSWiener
