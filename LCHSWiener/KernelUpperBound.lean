import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import LCHSWiener.Core
import LCHSWiener.DualFunction
import LCHSWiener.DensityMeasure
import LCHSWiener.WienerDualBound
import LCHSWiener.CauchyFourier

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LCHSWiener

/-!
# Sharp explicit upper bound

This file formalizes the Wiener part of Section 3.3.  The boundary density is

  w_{R,C}(k) = exp(pi*C*q_R) * exp(-pi*C) * Phi_{R,-C}(k) / (pi(1+k^2)),

i.e. the Cauchy density times the lower-side boundary value of
`exp(i*C*Log((R-z)/(R+z)))`, normalised so that its half-line Fourier transform
is `exp(-x)`.  Instead of a contour integral we use the half-line
representation `Phi_{R,-C}(z-is) = 1 + ∫_0^∞ e^{-izy} G(y) dy` from
`HalfLineRepresentation.lean`, the Fourier transform of the Cauchy density,
Fubini, and dominated convergence as `s -> 0`.  Splitting the boundary measure
into `|k|<R` and `|k|>R` gives the approximant and its residual.
-/

/-- Cauchy density. -/
def cauchyDensity (k : ℝ) : ℝ := 1 / (Real.pi * (1 + k^2))

lemma cauchyDensity_nonneg (k : ℝ) : 0 ≤ cauchyDensity k := by
  unfold cauchyDensity
  positivity

lemma cauchyDensity_eq_cauchyPDFReal (k : ℝ) :
    cauchyDensity k = ProbabilityTheory.cauchyPDFReal 0 1 k := by
  rw [ProbabilityTheory.cauchyPDFReal_def', cauchyDensity]
  simp [mul_comm]

lemma integrable_cauchyDensity : Integrable cauchyDensity volume := by
  have h := ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := (1 : NNReal))
  exact h.congr (Eventually.of_forall fun k => (cauchyDensity_eq_cauchyPDFReal k).symm)

lemma continuous_cauchyDensity : Continuous cauchyDensity := by
  unfold cauchyDensity
  refine continuous_const.div (by fun_prop) fun k => ?_
  positivity

/-- Mass of the central Cauchy interval. -/
theorem integral_cauchyDensity_Icc {R : ℝ} (hR : 0 ≤ R) :
    ∫ k in Set.Icc (-R) R, cauchyDensity k = pR R := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hderiv : ∀ x ∈ Set.uIcc (-R) R,
      HasDerivAt (fun x : ℝ => Real.arctan x / Real.pi) (cauchyDensity x) x := by
    intro x _
    have h := (Real.hasDerivAt_arctan x).div_const Real.pi
    convert h using 1
    unfold cauchyDensity
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuous_cauchyDensity.intervalIntegrable _ _)]
  simp only [Real.arctan_neg, pR]
  ring

/-- Cauchy mass outside the truncation interval. -/
theorem integral_cauchyDensity_compl_Icc {R : ℝ} (hR : 0 ≤ R) :
    ∫ k in (Set.Icc (-R) R)ᶜ, cauchyDensity k = qR R := by
  have hall : ∫ k : ℝ, cauchyDensity k = 1 := by
    simp_rw [cauchyDensity_eq_cauchyPDFReal]
    exact ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 (by norm_num)
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Icc (a := -R) (b := R))
    integrable_cauchyDensity
  rw [integral_cauchyDensity_Icc hR, hall] at hsplit
  simp only [qR]
  linarith

/-- The normalising constant `exp(pi*C*q) * exp(-pi*C) = exp(-pi*C*p)`. -/
def outerConst (R C : ℝ) : ℝ := Real.exp (Real.pi*C*qR R) * Real.exp (-(Real.pi*C))

lemma outerConst_pos (R C : ℝ) : 0 < outerConst R C := by
  unfold outerConst; positivity

/-- Full boundary density. -/
def fullOuterDensity (R C : ℝ) (k : ℝ) : ℂ :=
  ((outerConst R C * cauchyDensity k : ℝ) : ℂ) * dualPhiC R (-C) (k:ℂ)

/-- Truncated approximant density. -/
def innerOuterDensity (R C : ℝ) (k : ℝ) : ℂ :=
  (Set.Ioo (-R) R).indicator (fullOuterDensity R C) k

/-- Residual/tail density. -/
def tailOuterDensity (R C : ℝ) (k : ℝ) : ℂ :=
  ((Set.Icc (-R) R)ᶜ).indicator (fullOuterDensity R C) k

lemma measurable_dualPhiC_real (R c : ℝ) : Measurable fun k : ℝ => dualPhiC R c (k:ℂ) := by
  unfold dualPhiC dualMobius
  fun_prop

lemma norm_dualPhiC_neg_le {R C : ℝ} (hC : 0 ≤ C) (z : ℂ) :
    ‖dualPhiC R (-C) z‖ ≤ Real.exp (2 * (Real.pi * C)) := by
  rw [norm_dualPhiC]
  apply Real.exp_le_exp.mpr
  have h1 := Complex.neg_pi_lt_arg (dualMobius R z)
  nlinarith

lemma norm_fullOuterDensity_inside {R C k : ℝ}
    (hk : |k| < R) :
    ‖fullOuterDensity R C k‖ =
      Real.exp (Real.pi*C*qR R) * cauchyDensity k := by
  rw [fullOuterDensity, norm_mul, norm_dualPhiC_real_inside hk, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (outerConst_pos R C).le (cauchyDensity_nonneg k))]
  unfold outerConst dualA
  rw [show Real.exp (Real.pi * C * qR R) * Real.exp (-(Real.pi * C)) * cauchyDensity k *
      Real.exp (-Real.pi * -C) = Real.exp (Real.pi * C * qR R) * cauchyDensity k *
        (Real.exp (-(Real.pi * C)) * Real.exp (Real.pi * C)) by ring_nf,
    ← Real.exp_add]
  simp

lemma norm_fullOuterDensity_outside {R C k : ℝ}
    (hR : 0 < R) (hk : R < |k|) :
    ‖fullOuterDensity R C k‖ =
      Real.exp (-Real.pi*C*pR R) * cauchyDensity k := by
  rw [fullOuterDensity, norm_mul, norm_dualPhiC_real_outside hR hk, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (outerConst_pos R C).le (cauchyDensity_nonneg k)),
    mul_one]
  unfold outerConst
  rw [← Real.exp_add]
  congr 2
  simp only [qR]
  ring

lemma integrable_fullOuterDensity {R C : ℝ} (hC : 0 ≤ C) :
    Integrable (fullOuterDensity R C) volume := by
  refine Integrable.mono' (integrable_cauchyDensity.const_mul
    (outerConst R C * Real.exp (2 * (Real.pi * C)))) ?_ (Eventually.of_forall fun k => ?_)
  · unfold fullOuterDensity
    exact ((Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_cauchyDensity)).aestronglyMeasurable).mul
      (measurable_dualPhiC_real R (-C)).aestronglyMeasurable
  · rw [fullOuterDensity, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (outerConst_pos R C).le (cauchyDensity_nonneg k))]
    calc outerConst R C * cauchyDensity k * ‖dualPhiC R (-C) (k:ℂ)‖
        ≤ outerConst R C * cauchyDensity k * Real.exp (2 * (Real.pi * C)) :=
          mul_le_mul_of_nonneg_left (norm_dualPhiC_neg_le hC _)
            (mul_nonneg (outerConst_pos R C).le (cauchyDensity_nonneg k))
      _ = outerConst R C * Real.exp (2 * (Real.pi * C)) * cauchyDensity k := by ring

lemma integrable_innerOuterDensity {R C : ℝ} (hC : 0 ≤ C) :
    Integrable (innerOuterDensity R C) volume :=
  (integrable_fullOuterDensity hC).indicator measurableSet_Ioo

lemma integrable_tailOuterDensity {R C : ℝ} (hC : 0 ≤ C) :
    Integrable (tailOuterDensity R C) volume :=
  (integrable_fullOuterDensity hC).indicator measurableSet_Icc.compl

/-- L1 mass of the inner density. -/
theorem integral_norm_innerOuterDensity
    {R C : ℝ} (hR : 0 < R) :
    ∫ k, ‖innerOuterDensity R C k‖ =
      pR R * Real.exp (Real.pi*C*qR R) := by
  have hfun : (fun k => ‖innerOuterDensity R C k‖) =
      (Set.Ioo (-R) R).indicator (fun k => Real.exp (Real.pi*C*qR R) * cauchyDensity k) := by
    funext k
    by_cases hk : k ∈ Set.Ioo (-R) R
    · simp only [innerOuterDensity, Set.indicator_of_mem hk]
      exact norm_fullOuterDensity_inside (abs_lt.2 hk)
    · simp [innerOuterDensity, Set.indicator_of_notMem hk]
  rw [hfun, integral_indicator measurableSet_Ioo, integral_const_mul,
    ← integral_Icc_eq_integral_Ioo, integral_cauchyDensity_Icc hR.le]
  ring

/-- L1 mass of the tail density. -/
theorem integral_norm_tailOuterDensity
    {R C : ℝ} (hR : 0 < R) :
    ∫ k, ‖tailOuterDensity R C k‖ =
      qR R * Real.exp (-Real.pi*C*pR R) := by
  have hfun : (fun k => ‖tailOuterDensity R C k‖) =
      ((Set.Icc (-R) R)ᶜ).indicator
        (fun k => Real.exp (-Real.pi*C*pR R) * cauchyDensity k) := by
    funext k
    by_cases hk : k ∈ (Set.Icc (-R) R)ᶜ
    · simp only [tailOuterDensity, Set.indicator_of_mem hk]
      have habs : R < |k| := by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hk
        rcases hk with hk | hk
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact hk
      exact norm_fullOuterDensity_outside hR habs
    · simp [tailOuterDensity, Set.indicator_of_notMem hk]
  rw [hfun, integral_indicator measurableSet_Icc.compl, integral_const_mul,
    integral_cauchyDensity_compl_Icc hR.le]
  ring

/-! ### The half-line Fourier transform of the boundary density -/

lemma cauchy_char (t : ℝ) :
    ∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (t:ℂ)) * (cauchyDensity k : ℂ) =
      Complex.exp (-((|t| : ℝ) : ℂ)) := by
  have h := integral_exp_mul_cauchy t
  simp only [cauchyDensity]
  rw [h, Complex.ofReal_exp]
  push_cast
  rfl

lemma integrable_cauchy_char (t : ℝ) :
    Integrable fun k : ℝ => Complex.exp (-Complex.I * (k:ℂ) * (t:ℂ)) * (cauchyDensity k : ℂ) :=
  integrable_exp_mul_cauchy t

/-- Fixed-shift identity:
`∫ e^{-ikx} ρ(k) Φ(k - is) dk = e^{-x} Φ(-i - is)` for `x ≥ 0`. -/
theorem cauchy_shifted_identity {R c s x : ℝ} (hR : 0 < R) (hs : 0 < s) (hx : 0 ≤ x) :
    ∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) *
        ((cauchyDensity k : ℂ) * dualPhiC R c ((k:ℂ) - Complex.I * (s:ℂ))) =
      Complex.exp (-(x:ℂ)) * dualPhiC R c (-Complex.I - Complex.I * (s:ℂ)) := by
  set G := shiftedDualDensity R c s with hGdef
  have hG : Integrable G volume := integrable_shiftedDualDensity hs
  have hG0 : ∀ y ≤ 0, G y = 0 := fun y hy => shiftedDualDensity_of_nonpos hy
  have hΦ : ∀ k : ℝ, dualPhiC R c ((k:ℂ) - Complex.I * (s:ℂ)) =
      1 + ∫ y : ℝ, halfLineCharacter (k:ℂ) y * G y :=
    fun k => shiftedDual_eq_one_add_integral hR hs (by simp)
  have hΦI : dualPhiC R c (-Complex.I - Complex.I * (s:ℂ)) =
      1 + ∫ y : ℝ, Complex.exp (-(y:ℂ)) * G y := by
    rw [shiftedDual_eq_one_add_integral hR hs (z := -Complex.I) (by simp)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [halfLineCharacter]
    congr 2
    ring_nf
    simp
  -- the product integrand
  let H : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (-Complex.I * (p.1:ℂ) * (x:ℂ)) * (cauchyDensity p.1 : ℂ) *
      (halfLineCharacter (p.1:ℂ) p.2 * G p.2)
  have hnormχ : ∀ k y : ℝ, ‖halfLineCharacter (k:ℂ) y‖ = 1 := by
    intro k y; rw [norm_halfLineCharacter]; simp
  have hnormE : ∀ k : ℝ, ‖Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ))‖ = 1 := by
    intro k; rw [Complex.norm_exp]; simp
  have hH : Integrable H (volume.prod volume) := by
    refine Integrable.mono' (integrable_cauchyDensity.mul_prod hG.norm) ?_
      (Eventually.of_forall fun p => ?_)
    · refine AEStronglyMeasurable.mul ?_ ?_
      · exact ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (-Complex.I * (p.1:ℂ) * (x:ℂ))).mul
          (Complex.continuous_ofReal.comp
            (continuous_cauchyDensity.comp continuous_fst))).aestronglyMeasurable
      · refine AEStronglyMeasurable.mul ?_ hG.aestronglyMeasurable.comp_snd
        exact (Continuous.aestronglyMeasurable (by unfold halfLineCharacter; fun_prop))
    · simp only [H, norm_mul, hnormχ, hnormE, Complex.norm_real,
        Real.norm_of_nonneg (cauchyDensity_nonneg _)]
      ring_nf
      exact le_rfl
  have hinner : ∀ y : ℝ, ∫ k : ℝ, H (k, y) = Complex.exp (-(x:ℂ)) *
      (Complex.exp (-(y:ℂ)) * G y) := by
    intro y
    by_cases hy : 0 < y
    · have hfun : (fun k : ℝ => H (k, y)) = fun k : ℝ => G y *
          (Complex.exp (-Complex.I * (k:ℂ) * ((x + y : ℝ) : ℂ)) * (cauchyDensity k : ℂ)) := by
        funext k
        simp only [H, halfLineCharacter]
        rw [show Complex.exp (-Complex.I * (k:ℂ) * ((x + y : ℝ) : ℂ)) =
          Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) * Complex.exp (-Complex.I * (k:ℂ) * (y:ℂ)) by
            rw [← Complex.exp_add]; push_cast; ring_nf]
        ring
      rw [hfun, integral_const_mul, cauchy_char, abs_of_pos (by linarith : (0:ℝ) < x + y)]
      push_cast
      rw [neg_add, Complex.exp_add]
      ring
    · have hy0 : G y = 0 := hG0 y (le_of_not_gt hy)
      simp [H, hy0]
  have hfubini : ∫ k : ℝ, ∫ y : ℝ, H (k, y) = ∫ y : ℝ, ∫ k : ℝ, H (k, y) :=
    integral_integral_swap hH
  have hlhs : ∀ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) *
      ((cauchyDensity k : ℂ) * dualPhiC R c ((k:ℂ) - Complex.I * (s:ℂ))) =
      Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) * (cauchyDensity k : ℂ) +
        ∫ y : ℝ, H (k, y) := by
    intro k
    rw [hΦ k, show (∫ y : ℝ, H (k, y)) = (Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) *
        (cauchyDensity k : ℂ)) * ∫ y : ℝ, halfLineCharacter (k:ℂ) y * G y by
      simp only [H]; exact integral_const_mul _ _]
    ring
  simp_rw [hlhs]
  rw [integral_add (integrable_cauchy_char x) hH.integral_prod_left, hfubini, cauchy_char,
    abs_of_nonneg hx]
  simp_rw [hinner]
  rw [integral_const_mul, hΦI]
  ring

/-- One-sided boundary continuity of the dual function at a real point
outside `[-R,R]`. -/
lemma tendsto_dualPhiC_outside {R c k : ℝ} (hR : 0 < R) (hk : R < |k|)
    {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) (hu0 : ∀ n, 0 < u n) :
    Tendsto (fun n => dualPhiC R c ((k:ℂ) - Complex.I * (u n : ℂ))) atTop
      (𝓝 (dualPhiC R c (k:ℂ))) := by
  have hk0 : (R:ℂ) + (k:ℂ) ≠ 0 := by
    intro h
    have : R + k = 0 := by exact_mod_cast h
    have : k = -R := by linarith
    rw [this, abs_neg, abs_of_pos hR] at hk
    exact lt_irrefl _ hk
  have hz : Tendsto (fun n => (k:ℂ) - Complex.I * (u n : ℂ)) atTop (𝓝 (k:ℂ)) := by
    have hu' : Tendsto (fun n => (u n : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp hu
    simpa using (tendsto_const_nhds (x := (k:ℂ))).sub
      ((tendsto_const_nhds (x := Complex.I)).mul hu')
  have hM : Tendsto (fun n => dualMobius R ((k:ℂ) - Complex.I * (u n : ℂ))) atTop
      (𝓝[{w : ℂ | 0 ≤ w.im}] (dualMobius R (k:ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(analyticAt_dualMobius_of_den_ne hk0).continuousAt.tendsto.comp hz,
      Eventually.of_forall fun n => ?_⟩
    exact (dualMobius_im_pos hR (by simp [hu0 n])).le
  have hreal : dualMobius R (k:ℂ) = (((R - k) / (R + k) : ℝ) : ℂ) := by
    unfold dualMobius; push_cast; rfl
  have hneg := dualMobius_real_neg hR hk
  have hlog := (Complex.continuousWithinAt_log_of_re_neg_of_im_zero
    (z := dualMobius R (k:ℂ)) (by rw [hreal, Complex.ofReal_re]; exact hneg)
    (by rw [hreal, Complex.ofReal_im])).tendsto.comp hM
  unfold dualPhiC
  exact (Complex.continuous_exp.tendsto _).comp
    ((tendsto_const_nhds).sub ((tendsto_const_nhds).mul hlog))

/-- Main transform identity: the full boundary density has half-line
Fourier transform `exp(-x)`. -/
theorem integral_fullOuterDensity_character
    {R C x : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    ∫ k : ℝ,
      Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ)) * fullOuterDensity R C k =
      Complex.exp (-(x:ℂ)) := by
  let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hu0 : ∀ n, 0 < u n := fun n => one_div_pos.mpr (by positivity)
  have hz : Tendsto (fun n => (u n : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hu
  -- limit of the left-hand sides
  have hL : Tendsto (fun n => ∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) *
        ((cauchyDensity k : ℂ) * dualPhiC R (-C) ((k:ℂ) - Complex.I * (u n : ℂ))))
      atTop (𝓝 (∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) *
        ((cauchyDensity k : ℂ) * dualPhiC R (-C) (k:ℂ)))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun k => cauchyDensity k * Real.exp (Real.pi * C)) (fun n => ?_)
      (integrable_cauchyDensity.mul_const _) (fun n => Eventually.of_forall fun k => ?_) ?_
    · refine (Continuous.aestronglyMeasurable ?_)
      refine (by fun_prop : Continuous fun k : ℝ => Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ))).mul
        ((Complex.continuous_ofReal.comp continuous_cauchyDensity).mul
          (continuous_dualPhiC_shift hR (hu0 n)))
    · rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_of_nonneg (cauchyDensity_nonneg k)]
      have hre : (-Complex.I * (k:ℂ) * (x:ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero, one_mul]
      refine mul_le_mul_of_nonneg_left ?_ (cauchyDensity_nonneg k)
      rw [norm_dualPhiC]
      apply Real.exp_le_exp.mpr
      have harg := (dualMobius_arg_mem (R := R) hR
        (z := (k:ℂ) - Complex.I * (u n : ℂ)) (by simp [hu0 n])).1
      nlinarith
    · have hae : ∀ᵐ k : ℝ ∂volume, k ∉ ({R, -R} : Set ℝ) :=
        (Set.toFinite _).countable.ae_notMem volume
      filter_upwards [hae] with k hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
      refine tendsto_const_nhds.mul (tendsto_const_nhds.mul ?_)
      rcases lt_trichotomy |k| R with hlt | heq | hgt
      · have hzk : Tendsto (fun n => (k:ℂ) - Complex.I * (u n : ℂ)) atTop (𝓝 (k:ℂ)) := by
          simpa using (tendsto_const_nhds (x := (k:ℂ))).sub
            ((tendsto_const_nhds (x := Complex.I)).mul hz)
        exact (continuousAt_dualPhiC_real_inside (c := -C) hlt).tendsto.comp hzk
      · exfalso
        rcases abs_eq (hR.le) |>.1 heq with h | h
        · exact hk.1 h
        · exact hk.2 h
      · exact tendsto_dualPhiC_outside hR hgt hu hu0
  -- limit of the right-hand sides
  have hRt : Tendsto (fun n => Complex.exp (-(x:ℂ)) *
        dualPhiC R (-C) (-Complex.I - Complex.I * (u n : ℂ)))
      atTop (𝓝 (Complex.exp (-(x:ℂ)) * dualPhiC R (-C) (-Complex.I))) := by
    have harg : Tendsto (fun n => -Complex.I - Complex.I * (u n : ℂ)) atTop (𝓝 (-Complex.I)) := by
      simpa using (tendsto_const_nhds (x := -Complex.I)).sub
        ((tendsto_const_nhds (x := Complex.I)).mul hz)
    exact tendsto_const_nhds.mul (((analyticOnNhd_dualPhiC hR) (-Complex.I)
      neg_I_mem_lowerHalfPlane).continuousAt.tendsto.comp harg)
  have hlim : ∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) *
        ((cauchyDensity k : ℂ) * dualPhiC R (-C) (k:ℂ)) =
      Complex.exp (-(x:ℂ)) * dualPhiC R (-C) (-Complex.I) := by
    refine tendsto_nhds_unique hL ?_
    refine hRt.congr fun n => ?_
    exact (cauchy_shifted_identity hR (hu0 n) hx).symm
  -- normalisation
  have hnorm : (outerConst R C : ℂ) * dualPhiC R (-C) (-Complex.I) = 1 := by
    rw [dualPhiC_neg_I hR, ← Complex.ofReal_mul]
    unfold outerConst dualA
    rw [show -Real.pi * -C = Real.pi * C by ring, ← Real.exp_mul, ← Real.exp_add,
      ← Real.exp_add]
    have hpq := pR_add_qR R
    rw [show Real.pi * C * qR R + -(Real.pi * C) + Real.pi * C * pR R = 0 by
      linear_combination (Real.pi * C) * hpq]
    simp
  have hfun : (fun k : ℝ => Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ)) * fullOuterDensity R C k) =
      fun k : ℝ => (outerConst R C : ℂ) * (Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) *
        ((cauchyDensity k : ℂ) * dualPhiC R (-C) (k:ℂ))) := by
    funext k
    simp only [fullOuterDensity]
    push_cast
    ring
  rw [hfun, integral_const_mul, hlim]
  linear_combination (Complex.exp (-(x:ℂ))) * hnorm

/-- The inner and outer densities split the full boundary density a.e. -/
lemma fullOuterDensity_eq_inner_add_tail_ae {R C : ℝ} :
    fullOuterDensity R C =ᵐ[volume]
      fun k => innerOuterDensity R C k + tailOuterDensity R C k := by
  have hae : ∀ᵐ k : ℝ ∂volume, k ∉ ({R, -R} : Set ℝ) :=
    (Set.toFinite _).countable.ae_notMem volume
  filter_upwards [hae] with k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
  by_cases hinside : k ∈ Set.Ioo (-R) R
  · have hnot : k ∉ (Set.Icc (-R) R)ᶜ := by
      simp only [Set.mem_compl_iff, not_not]
      exact Set.Ioo_subset_Icc_self hinside
    simp [innerOuterDensity, tailOuterDensity, Set.indicator_of_mem hinside,
      Set.indicator_of_notMem hnot]
  · have hout : k ∈ (Set.Icc (-R) R)ᶜ := by
      intro hmem
      apply hinside
      exact ⟨lt_of_le_of_ne hmem.1 (fun h => hk.2 h.symm),
        lt_of_le_of_ne hmem.2 hk.1⟩
    simp [innerOuterDensity, tailOuterDensity, Set.indicator_of_notMem hinside,
      Set.indicator_of_mem hout]

/-- Characters times an integrable density are integrable. -/
lemma integrable_char_mul {h : ℝ → ℂ} (hh : Integrable h volume) (x : ℝ) :
    Integrable (fun k : ℝ => Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ)) * h k) volume := by
  refine hh.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun k => ?_)
  rw [Complex.norm_exp]
  simp

/-- Density measures whose densities add up (a.e.) to a density with transform
`exp(-x)` on the half-line give a residual representation. -/
lemma representsResidual_of_density_split {f g F : ℝ → ℂ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hsplit : F =ᵐ[volume] fun k => f k + g k)
    (hF : ∀ x : ℝ, 0 ≤ x →
      ∫ k : ℝ, Complex.exp (-Complex.I*(k:ℂ)*(x:ℂ)) * F k = Complex.exp (-(x:ℂ))) :
    RepresentsResidual (finiteCMeasureOfDensity f hf) (finiteCMeasureOfDensity g hg) := by
  intro x hx
  rw [fsTransform_finiteCMeasureOfDensity hf x (integrable_char_mul hf x),
    fsTransform_finiteCMeasureOfDensity hg x (integrable_char_mul hg x), ← hF x hx,
    ← integral_sub (integrable_char_mul (hf.add hg) x |>.congr ?_) (integrable_char_mul hf x)]
  · refine integral_congr_ae ?_
    filter_upwards [hsplit] with k hk
    rw [hk]
    ring
  · filter_upwards [hsplit] with k hk
    rw [hk]
    rfl

/-- Concrete sharp witness supplied by the outer kernel. -/
theorem outer_kernel_witness
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    ∃ mu nu : FiniteCMeasure,
      SupportedIn R mu ∧
      tv mu ≤ pR R * Real.exp (Real.pi*C*qR R) ∧
      RepresentsResidual mu nu ∧
      tv nu ≤ qR R * Real.exp (-Real.pi*C*pR R) := by
  have hf : Integrable (innerOuterDensity R C) volume := integrable_innerOuterDensity hC
  have hg : Integrable (tailOuterDensity R C) volume := integrable_tailOuterDensity hC
  refine ⟨finiteCMeasureOfDensity _ hf, finiteCMeasureOfDensity _ hg, ?_, ?_, ?_, ?_⟩
  · apply supportedIn_finiteCMeasureOfDensity hf
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with k hk
    have hk' : k ∉ Set.Ioo (-R) R := fun h => hk (Set.Ioo_subset_Icc_self h)
    simp [innerOuterDensity, Set.indicator_of_notMem hk']
  · calc
      tv (finiteCMeasureOfDensity _ hf) ≤ ∫ k, ‖innerOuterDensity R C k‖ :=
        tv_finiteCMeasureOfDensity_le hf
      _ = pR R * Real.exp (Real.pi*C*qR R) := integral_norm_innerOuterDensity hR
  · exact representsResidual_of_density_split hf hg fullOuterDensity_eq_inner_add_tail_ae
      fun x hx => integral_fullOuterDensity_character hR hC hx
  · calc
      tv (finiteCMeasureOfDensity _ hg) ≤ ∫ k, ‖tailOuterDensity R C k‖ :=
        tv_finiteCMeasureOfDensity_le hg
      _ = qR R * Real.exp (-Real.pi*C*pR R) := integral_norm_tailOuterDensity hR

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
      unfold C; field_simp [Real.pi_ne_zero, ne_of_gt hq]]
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
  set alpha := lam / pR R with halpha
  have ha0 : 0 ≤ alpha := div_nonneg hlam0 hp.le
  have ha1 : alpha ≤ 1 := (div_le_one hp).2 hlam
  let rhoC : ℝ → ℂ := fun k => (cauchyDensity k : ℂ)
  have hrho : Integrable rhoC volume := integrable_cauchyDensity.ofReal
  let inner : ℝ → ℂ := (Set.Ioo (-R) R).indicator rhoC
  let outer : ℝ → ℂ := ((Set.Icc (-R) R)ᶜ).indicator rhoC
  have hinner : Integrable inner volume := hrho.indicator measurableSet_Ioo
  have houter : Integrable outer volume := hrho.indicator measurableSet_Icc.compl
  let rhoIn : ℝ → ℂ := fun k => (alpha:ℂ) * inner k
  let rhoOut : ℝ → ℂ := fun k => ((1-alpha : ℝ):ℂ) * inner k + outer k
  have hin : Integrable rhoIn volume := hinner.const_mul _
  have hout : Integrable rhoOut volume := (hinner.const_mul _).add houter
  have hnormInner : ∫ k, ‖inner k‖ = pR R := by
    have : (fun k => ‖inner k‖) = (Set.Ioo (-R) R).indicator cauchyDensity := by
      funext k
      by_cases hk : k ∈ Set.Ioo (-R) R
      · simp [inner, rhoC, Set.indicator_of_mem hk, cauchyDensity_nonneg]
      · simp [inner, Set.indicator_of_notMem hk]
    rw [this, integral_indicator measurableSet_Ioo, ← integral_Icc_eq_integral_Ioo,
      integral_cauchyDensity_Icc hR.le]
  have hnormOuter : ∫ k, ‖outer k‖ = qR R := by
    have : (fun k => ‖outer k‖) = ((Set.Icc (-R) R)ᶜ).indicator cauchyDensity := by
      funext k
      by_cases hk : k ∈ (Set.Icc (-R) R)ᶜ
      · simp [outer, rhoC, Set.indicator_of_mem hk, cauchyDensity_nonneg]
      · simp [outer, Set.indicator_of_notMem hk]
    rw [this, integral_indicator measurableSet_Icc.compl, integral_cauchyDensity_compl_Icc hR.le]
  let mu := finiteCMeasureOfDensity rhoIn hin
  let nu := finiteCMeasureOfDensity rhoOut hout
  have hsupp : SupportedIn R mu := by
    apply supportedIn_finiteCMeasureOfDensity hin
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with k hk
    have hk' : k ∉ Set.Ioo (-R) R := fun h => hk (Set.Ioo_subset_Icc_self h)
    simp [rhoIn, inner, Set.indicator_of_notMem hk']
  have hmu : tv mu ≤ lam := by
    calc
      tv mu ≤ ∫ k, ‖rhoIn k‖ := tv_finiteCMeasureOfDensity_le hin
      _ = alpha * pR R := by
        simp only [rhoIn, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
        rw [integral_const_mul, hnormInner]
      _ = lam := by rw [halpha]; field_simp
  have hsplit : rhoC =ᵐ[volume] fun k => rhoIn k + rhoOut k := by
    have hae : ∀ᵐ k : ℝ ∂volume, k ∉ ({R, -R} : Set ℝ) :=
      (Set.toFinite _).countable.ae_notMem volume
    filter_upwards [hae] with k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
    by_cases hinside : k ∈ Set.Ioo (-R) R
    · have hnot : k ∉ (Set.Icc (-R) R)ᶜ := by
        simp only [Set.mem_compl_iff, not_not]
        exact Set.Ioo_subset_Icc_self hinside
      simp only [rhoIn, rhoOut, inner, outer, Set.indicator_of_mem hinside,
        Set.indicator_of_notMem hnot]
      push_cast
      ring
    · have hout' : k ∈ (Set.Icc (-R) R)ᶜ := by
        intro hmem
        apply hinside
        exact ⟨lt_of_le_of_ne hmem.1 (fun h => hk.2 h.symm), lt_of_le_of_ne hmem.2 hk.1⟩
      simp [rhoIn, rhoOut, inner, outer, Set.indicator_of_notMem hinside,
        Set.indicator_of_mem hout']
  have hres : RepresentsResidual mu nu := by
    refine representsResidual_of_density_split hin hout hsplit fun x hx => ?_
    simp only [rhoC]
    rw [cauchy_char, abs_of_nonneg hx]
  have hnu : tv nu ≤ 1-lam := by
    calc
      tv nu ≤ ∫ k, ‖rhoOut k‖ := tv_finiteCMeasureOfDensity_le hout
      _ ≤ ∫ k, ((1-alpha) * ‖inner k‖ + ‖outer k‖) := by
        refine integral_mono hout.norm ((hinner.norm.const_mul _).add houter.norm) fun k => ?_
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr ha1)]
      _ = (1-alpha)*pR R + qR R := by
        rw [integral_add (hinner.norm.const_mul _) houter.norm, integral_const_mul,
          hnormInner, hnormOuter]
      _ = 1-lam := by
        have hpq := pR_add_qR R
        rw [halpha]
        field_simp
        linarith
  refine ⟨tv nu, ⟨mu,nu,hsupp,hmu,hres,rfl⟩, ?_⟩
  linarith

end LCHSWiener
