import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LCHSWiener.Core
import LCHSWiener.DualFunction
import LCHSWiener.HalfLineRepresentation
import LCHSWiener.VectorMeasureFubini

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LCHSWiener

/-!
# The Wiener dual lower bound

This file formalizes Section 3.2.  For `r>R` and `s>0` we insert the explicit
half-line representation of `Phi_{r,c}(.-is)` into the residual identity and
use the Fubini theorem from `VectorMeasureFubini.lean`.  We then send `s -> 0`
and `r -> R` by dominated convergence.  No boundary atom assumption is needed.
-/

lemma norm_cmul_le : ‖cmul‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℂ

/-- A uniform bound on the integrand bounds the vector integral by the total
variation. -/
lemma norm_vectorIntegral_le_mul_tv (mu : FiniteCMeasure) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ᵐ k ∂mu.1.variation, ‖f k‖ ≤ C) :
    ‖∫ᵛ k : ℝ, f k ∂[cmul; mu.1]‖ ≤ C * tv mu := by
  refine (MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const h).trans ?_
  have hv : 0 ≤ mu.1.variation.real univ := measureReal_nonneg
  calc C * ‖cmul‖ * mu.1.variation.real univ ≤ C * 1 * mu.1.variation.real univ := by
        gcongr
        exact norm_cmul_le
    _ = C * tv mu := by simp [tv, Measure.real]

/-- A measure supported in `[-R,R]` is carried by `[-R,R]`. -/
lemma ae_mem_Icc_of_supportedIn {R : ℝ} {mu : FiniteCMeasure} (hsupp : SupportedIn R mu) :
    ∀ᵐ k : ℝ ∂mu.1.variation, k ∈ Set.Icc (-R) R :=
  ae_iff.2 hsupp

/-- All characters are integrable against a finite complex measure. -/
lemma vectorIntegrable_character (mu : FiniteCMeasure) (x : ℝ) :
    mu.1.Integrable (fun k : ℝ => realCharacter k x) := by
  refine Integrable.mono' (integrable_const (1:ℝ)) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by unfold realCharacter; fun_prop))
  · filter_upwards with k
    exact (norm_realCharacter k x).le

/-- Norm of an FS transform is bounded by the total variation. -/
theorem norm_fsTransform_le_tv (mu : FiniteCMeasure) (x : ℝ) :
    ‖fsTransform mu x‖ ≤ tv mu := by
  unfold fsTransform
  have h := norm_vectorIntegral_le_mul_tv mu zero_le_one (f := fun k : ℝ =>
    Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))) (by
      filter_upwards with k
      exact (norm_realCharacter k x).le)
  simpa using h

/-- The shifted dual function is continuous along horizontal lines strictly
below the real axis. -/
lemma continuous_dualPhiC_shift {r c s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Continuous fun k : ℝ => dualPhiC r c ((k:ℂ) - Complex.I * (s:ℂ)) := by
  refine (analyticOnNhd_dualPhiC (c := c) hr).continuousOn.comp_continuous
    (by fun_prop) fun k => ?_
  show ((k:ℂ) - Complex.I * (s:ℂ)).im < 0
  simp [hs]

lemma norm_dualPhiC_shift_le_one {r c s : ℝ} (hr : 0 < r) (hc : 0 ≤ c) (hs : 0 < s)
    (k : ℝ) : ‖dualPhiC r c ((k:ℂ) - Complex.I * (s:ℂ))‖ ≤ 1 :=
  norm_dualPhiC_le_one hr hc (by simp [hs])

/-- The dual identity before taking `s -> 0`. -/
theorem shifted_dual_residual_identity
    {r c s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {mu nu : FiniteCMeasure}
    (hres : RepresentsResidual mu nu) :
    dualPhiC r c (-Complex.I - Complex.I * (s:ℂ)) -
      (∫ᵛ k : ℝ,
        dualPhiC r c ((k:ℂ) - Complex.I * (s:ℂ)) ∂[cmul; mu.1]) =
      ∫ᵛ k : ℝ,
        dualPhiC r c ((k:ℂ) - Complex.I * (s:ℂ)) ∂[cmul; nu.1] := by
  let G := shiftedDualDensity r c s
  have hG : Integrable G volume := integrable_shiftedDualDensity hs
  have hG0 : ∀ x ≤ 0, G x = 0 := fun x hx => shiftedDualDensity_of_nonpos hx
  let F : ℝ → ℂ := fun k => ∫ x : ℝ, G x * halfLineCharacter (k:ℂ) x
  have hPhiReal : ∀ k : ℝ,
      dualPhiC r c ((k:ℂ) - Complex.I*(s:ℂ)) = 1 + F k := by
    intro k
    rw [shiftedDual_eq_one_add_integral hr hs (z := (k:ℂ)) (by simp)]
    simp_rw [F, mul_comm (G _)]
    rfl
  have hPhiI :
      dualPhiC r c (-Complex.I - Complex.I*(s:ℂ)) =
        1 + ∫ x : ℝ, G x * Complex.exp (-(x:ℂ)) := by
    have hz : (-Complex.I : ℂ).im ≤ 0 := by norm_num
    rw [shiftedDual_eq_one_add_integral hr hs (z := -Complex.I) hz]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [halfLineCharacter, G]
    rw [mul_comm]
    congr 2
    ring_nf
    simp
  -- `F` is bounded and continuous, hence integrable for every finite measure.
  have hFb : ∀ k, ‖F k‖ ≤ ∫ x, ‖G x‖ := by
    intro k
    simpa [realCharacter_eq_halfLineCharacter] using norm_integral_mul_realCharacter_le hG k
  have hFc : Continuous F := by
    refine continuous_of_dominated (bound := fun x => ‖G x‖) ?_ ?_ hG.norm ?_
    · intro k
      exact hG.aestronglyMeasurable.mul
        (continuous_halfLineCharacter (k:ℂ)).aestronglyMeasurable
    · intro k
      filter_upwards with x
      rw [norm_mul, ← realCharacter_eq_halfLineCharacter, norm_realCharacter, mul_one]
    · filter_upwards with x
      exact continuous_const.mul (by unfold halfLineCharacter; fun_prop)
  have hFint : ∀ m : FiniteCMeasure, m.1.Integrable F := fun m =>
    Integrable.mono' (integrable_const (∫ x, ‖G x‖)) hFc.aestronglyMeasurable
      (Eventually.of_forall hFb)
  have hsplit : ∀ m : FiniteCMeasure,
      ∫ᵛ k : ℝ, dualPhiC r c ((k:ℂ) - Complex.I * (s:ℂ)) ∂[cmul; m.1] =
        m.1 univ + ∫ᵛ k : ℝ, F k ∂[cmul; m.1] := by
    intro m
    simp_rw [hPhiReal]
    rw [MeasureTheory.VectorMeasure.integral_fun_add (integrable_const _) (hFint m),
      MeasureTheory.VectorMeasure.integral_const]
    simp [cmul]
  have hswap : ∀ m : FiniteCMeasure,
      ∫ x : ℝ, G x * fsTransform m x = ∫ᵛ k : ℝ, F k ∂[cmul; m.1] :=
    fun m => integral_mul_fsTransform_swap_halfLine m hG
  have hfs0 : ∀ m : FiniteCMeasure, fsTransform m 0 = m.1 univ := by
    intro m
    unfold fsTransform
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [MeasureTheory.VectorMeasure.integral_const]
    simp [cmul]
  have h0 : 1 - mu.1 univ = nu.1 univ := by
    have := hres 0 le_rfl
    rwa [hfs0, hfs0, Complex.ofReal_zero, neg_zero, Complex.exp_zero] at this
  -- Integrate the residual identity against `G`, which lives on `x > 0`.
  have hbdd : ∀ m : FiniteCMeasure, Integrable (fun x => G x * fsTransform m x) volume :=
    fun m => hG.mul_bdd (continuous_fsTransform m).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_fsTransform_le_tv m x)
  have hexp : Integrable (fun x : ℝ => G x * Complex.exp (-(x:ℂ))) volume := by
    refine Integrable.mono' hG.norm (hG.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(x:ℂ))).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    by_cases hx : 0 < x
    · rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [Complex.norm_exp]
      simp only [Complex.neg_re, Complex.ofReal_re]
      exact Real.exp_le_one_iff.2 (by linarith)
    · simp [hG0 x (le_of_not_gt hx)]
  have hresInt :
      ∫ x : ℝ, G x * fsTransform nu x =
        (∫ x : ℝ, G x * Complex.exp (-(x:ℂ))) - ∫ x : ℝ, G x * fsTransform mu x := by
    rw [← integral_sub hexp (hbdd mu)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : 0 ≤ x
    · simp only [← hres x hx, mul_sub]
    · simp [hG0 x (le_of_not_ge hx)]
  rw [hPhiI, hsplit mu, hsplit nu, ← hswap mu, ← hswap nu, hresInt, ← h0]
  ring

/-- Dominated convergence of the shifted dual vector integral as `s -> 0+`,
provided the measure is supported in a strictly smaller interval `[-R,R]`.
The strict inequality `R < r` is exactly what avoids the two branch points
`±r`. -/
theorem tendsto_shifted_dual_vectorIntegral_supported
    {R r c : ℝ} (hR : 0 < R) (hRr : R < r) (hc : 0 ≤ c)
    (mu : FiniteCMeasure) (hsupp : SupportedIn R mu) :
    Tendsto
      (fun n : ℕ =>
        ∫ᵛ k : ℝ,
          dualPhiC r c ((k:ℂ) - Complex.I * (((1/(n+1:ℝ)):ℝ):ℂ)) ∂[cmul; mu.1])
      atTop
      (nhds (∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul; mu.1])) := by
  have hr : 0 < r := lt_trans hR hRr
  have hs : ∀ n : ℕ, 0 < 1/(n+1:ℝ) := fun n => one_div_pos.mpr (by positivity)
  apply MeasureTheory.VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := mu.1) (B := cmul) (bound := fun _ => (1:ℝ))
  · intro n
    exact (continuous_dualPhiC_shift hr (hs n)).aestronglyMeasurable
  · exact integrable_const (1:ℝ)
  · intro n
    exact Eventually.of_forall (norm_dualPhiC_shift_le_one hr hc (hs n))
  · filter_upwards [ae_mem_Icc_of_supportedIn hsupp] with k hk
    have habs : |k| < r := by
      rw [abs_lt]
      constructor <;> linarith [hk.1, hk.2, hRr]
    have hcont := (continuousAt_dualPhiC_real_inside (R:=r) (c:=c) habs).tendsto
    have harg : Tendsto
        (fun n : ℕ => (k:ℂ) - Complex.I * (((1/(n+1:ℝ)):ℝ):ℂ))
        atTop (nhds (k:ℂ)) := by
      have hz : Tendsto (fun n : ℕ => (((1/(n+1:ℝ)) : ℝ) : ℂ)) atTop (nhds ((0:ℝ):ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      have := (tendsto_const_nhds (x := (k:ℂ))).sub
        ((tendsto_const_nhds (x := Complex.I)).mul hz)
      simpa using this
    exact hcont.comp harg

/-- For a residual representing measure `nu`, the *boundary* dual gap for
`mu` has norm at most `tv nu`.  Notice that `nu` is never evaluated at the
singular boundary points `±r`: only the shifted functions occur on the right
before the limiting norm estimate is taken. -/
theorem dual_residual_gap_norm_le_tv
    {R r c : ℝ} (hR : 0 < R) (hRr : R < r) (hc : 0 ≤ c)
    {mu nu : FiniteCMeasure}
    (hsupp : SupportedIn R mu)
    (hres : RepresentsResidual mu nu) :
    ‖dualPhiC r c (-Complex.I) -
      (∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul; mu.1])‖ ≤ tv nu := by
  have hr : 0 < r := lt_trans hR hRr
  have hs : ∀ n : ℕ, 0 < 1/(n+1:ℝ) := fun n => one_div_pos.mpr (by positivity)
  have hlhs_bound : ∀ n : ℕ,
      ‖dualPhiC r c (-Complex.I - Complex.I*(((1/(n+1:ℝ)):ℝ):ℂ)) -
        (∫ᵛ k : ℝ,
          dualPhiC r c ((k:ℂ)-Complex.I*(((1/(n+1:ℝ)):ℝ):ℂ)) ∂[cmul;mu.1])‖ ≤ tv nu := by
    intro n
    rw [shifted_dual_residual_identity hr (hs n) hres]
    simpa using norm_vectorIntegral_le_mul_tv nu zero_le_one
      (Eventually.of_forall (norm_dualPhiC_shift_le_one hr hc (hs n)))
  have hphi : Tendsto
      (fun n : ℕ => dualPhiC r c (-Complex.I-Complex.I*(((1/(n+1:ℝ)):ℝ):ℂ))) atTop
      (nhds (dualPhiC r c (-Complex.I))) := by
    have harg : Tendsto
        (fun n : ℕ => -Complex.I-Complex.I*(((1/(n+1:ℝ)):ℝ):ℂ)) atTop
        (nhds (-Complex.I)) := by
      have hz : Tendsto (fun n : ℕ => (((1/(n+1:ℝ)) : ℝ) : ℂ)) atTop (nhds ((0:ℝ):ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      have := (tendsto_const_nhds (x := -Complex.I)).sub
        ((tendsto_const_nhds (x := Complex.I)).mul hz)
      simpa using this
    exact ((analyticOnNhd_dualPhiC hr) (-Complex.I)
      neg_I_mem_lowerHalfPlane).continuousAt.tendsto.comp harg
  have hmu := tendsto_shifted_dual_vectorIntegral_supported hR hRr hc mu hsupp
  have hnorm := (hphi.sub hmu).norm
  exact le_of_tendsto hnorm (Eventually.of_forall hlhs_bound)

/-- Integral of the dual boundary value over a measure supported in `[-R,R]`. -/
theorem norm_integral_dual_le_dualA_mul_tv
    {R r c : ℝ} (_hR : 0 < R) (hRr : R < r)
    {mu : FiniteCMeasure} (hsupp : SupportedIn R mu) :
    ‖∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul; mu.1]‖
      ≤ dualA c * tv mu := by
  refine norm_vectorIntegral_le_mul_tv mu (dualA_pos c).le ?_
  filter_upwards [ae_mem_Icc_of_supportedIn hsupp] with k hk
  have habs : |k| < r := by
    rw [abs_lt]
    constructor <;> linarith [hk.1, hk.2, hRr]
  rw [norm_dualPhiC_real_inside habs]

/-- Sharp lower bound for a fixed dual parameter `c`. -/
theorem wiener_cost_lower_of_c
    {R lam e c : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (he : e ∈ wienerCosts R lam) :
    (dualA c)^(pR R) - dualA c * lam ≤ e := by
  rcases he with ⟨mu, nu, hsupp, htv, hres, rfl⟩
  have hfor : ∀ r, R < r →
      (dualA c)^(pR r) - dualA c * tv mu ≤ tv nu := by
    intro r hRr
    have hr : 0 < r := lt_trans hR hRr
    have hgap := dual_residual_gap_norm_le_tv hR hRr hc hsupp hres
    have hmu := norm_integral_dual_le_dualA_mul_tv (c := c) hR hRr hsupp
    have hphi : ‖dualPhiC r c (-Complex.I)‖ = (dualA c)^(pR r) := by
      rw [dualPhiC_neg_I hr]
      simpa using Real.rpow_nonneg (dualA_pos c).le _
    calc
      (dualA c)^(pR r) - dualA c * tv mu
          ≤ ‖dualPhiC r c (-Complex.I)‖ -
              ‖∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul;mu.1]‖ := by
                rw [hphi]
                linarith
      _ ≤ ‖dualPhiC r c (-Complex.I) -
              (∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul;mu.1])‖ :=
            norm_sub_norm_le _ _
      _ ≤ tv nu := hgap
  have hlim : Tendsto
      (fun n : ℕ => (dualA c)^(pR (R + 1/(n+1:ℝ))) - dualA c * tv mu)
      atTop
      (nhds ((dualA c)^(pR R) - dualA c * tv mu)) := by
    apply Tendsto.sub_const
    have hcont : Continuous fun r : ℝ => (dualA c)^(pR r) :=
      continuous_const.rpow pR_continuous fun _ => Or.inl (dualA_pos c).ne'
    have harg : Tendsto (fun n : ℕ => R + 1/(n+1:ℝ)) atTop (nhds R) := by
      simpa using (tendsto_const_nhds (x := R)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact (hcont.tendsto R).comp harg
  have hle : ∀ n : ℕ,
      (dualA c)^(pR (R+1/(n+1:ℝ))) - dualA c*tv mu ≤ tv nu := by
    intro n
    have : 0 < 1/(n+1:ℝ) := one_div_pos.mpr (by positivity)
    exact hfor _ (by linarith)
  have := le_of_tendsto hlim (Eventually.of_forall hle)
  have ha := (dualA_pos c).le
  have : dualA c * tv mu ≤ dualA c * lam := mul_le_mul_of_nonneg_left htv ha
  linarith

/-- Convert an arbitrary `a in (0,1]` to the `c>=0` parameter of the note. -/
def cOfA (a : ℝ) : ℝ := -Real.log a / Real.pi

lemma cOfA_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) : 0 ≤ cOfA a := by
  unfold cOfA
  have : Real.log a ≤ 0 := Real.log_nonpos ha0.le ha1
  exact div_nonneg (by linarith) Real.pi_pos.le

lemma dualA_cOfA {a : ℝ} (ha0 : 0 < a) : dualA (cOfA a) = a := by
  unfold dualA cOfA
  rw [show -Real.pi * (-Real.log a / Real.pi) = Real.log a by
    field_simp [Real.pi_ne_zero]]
  exact Real.exp_log ha0

/-- The basic dual inequality `(3.8)`. -/
theorem wiener_cost_lower_of_a
    {R lam e a : ℝ} (hR : 0 < R) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (he : e ∈ wienerCosts R lam) :
    a^(pR R) - a*lam ≤ e := by
  have h := wiener_cost_lower_of_c hR (cOfA_nonneg ha0 ha1) he
  simpa [dualA_cOfA ha0] using h

/-- Low-`lambda` branch of the sharp lower bound. -/
theorem wiener_lower_low
    {R lam e : ℝ} (hR : 0 < R) (_hlam : lam ≤ pR R)
    (he : e ∈ wienerCosts R lam) :
    1-lam ≤ e := by
  simpa using wiener_cost_lower_of_a hR (a:=1) zero_lt_one le_rfl he

/-- High-`lambda` branch of the sharp lower bound. -/
theorem wiener_lower_high
    {R lam e : ℝ} (hR : 0 < R) (hlam : pR R ≤ lam)
    (he : e ∈ wienerCosts R lam) :
    qR R * (pR R / lam)^(pR R / qR R) ≤ e := by
  have hp := pR_pos hR
  have hq := qR_pos hR
  have hlam0 : 0 < lam := lt_of_lt_of_le hp hlam
  let a : ℝ := (pR R / lam)^(1/qR R)
  have ha0 : 0 < a := Real.rpow_pos_of_pos (div_pos hp hlam0) _
  have ha1 : a ≤ 1 := by
    apply Real.rpow_le_one (div_nonneg hp.le hlam0.le)
    · exact (div_le_one hlam0).2 hlam
    · positivity
  have h := wiener_cost_lower_of_a hR ha0 ha1 he
  have halg := high_test_point (p:=pR R) (q:=qR R) (lam:=lam)
      hp hq (pR_add_qR R) hlam
  simpa [a, halg] using h

end LCHSWiener
