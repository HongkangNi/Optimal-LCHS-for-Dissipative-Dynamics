import Mathlib
import LCHSWiener.Core
import LCHSWiener.DualFunction
import LCHSWiener.HalfLineRepresentation
import LCHSWiener.VectorMeasureFubini

noncomputable section

open Set MeasureTheory Filter scoped Topology

namespace LCHSWiener

/-!
# The Wiener dual lower bound

This file formalizes Section 3.2.  For `r>R` and `s>0` we insert the explicit
half-line representation of `Phi_{r,c}(.-is)` into the residual identity and
use the Fubini theorem from `VectorMeasureFubini.lean`.  We then send `s -> 0`
and `r -> R` by dominated convergence.  No boundary atom assumption is needed.
-/

lemma norm_cmul : ‖cmul‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp [cmul])
  · have h := ContinuousLinearMap.le_opNorm cmul (1:ℂ) (by norm_num)
    simpa [cmul] using h

/-- All characters are integrable against a finite complex measure. -/
lemma vectorIntegrable_character (mu : FiniteCMeasure) (x : ℝ) :
    mu.1.Integrable (fun k : ℝ => realCharacter k x) := by
  apply Integrable.mono' (integrable_const (1:ℂ) : Integrable (fun _ : ℝ => (1:ℂ)) mu.1.variation)
  · fun_prop
  · filter_upwards with k
    simp [norm_realCharacter]

/-- Norm of an FS transform is bounded by the total variation. -/
theorem norm_fsTransform_le_tv (mu : FiniteCMeasure) (x : ℝ) :
    ‖fsTransform mu x‖ ≤ tv mu := by
  unfold fsTransform tv
  have h := MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := mu.1) (B := cmul) (C := 1) (by
      filter_upwards with k
      simp [cmul])
  simpa [norm_cmul] using h

/-- The dual identity before taking `s -> 0`. -/
theorem shifted_dual_residual_identity
    {R r c s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {mu nu : FiniteCMeasure}
    (hres : RepresentsResidual mu nu) :
    dualPhiC r c (-Complex.I - Complex.I * (s:ℂ)) -
      (∫ᵛ k : ℝ,
        dualPhiC r c ((k:ℂ) - Complex.I * (s:ℂ)) ∂[cmul; mu.1]) =
      ∫ᵛ k : ℝ,
        dualPhiC r c ((k:ℂ) - Complex.I * (s:ℂ)) ∂[cmul; nu.1] := by
  let G := shiftedDualDensity r c s
  have hG : Integrable G volume := integrable_shiftedDualDensity hs
  have hPhiReal : ∀ k : ℝ,
      dualPhiC r c ((k:ℂ) - Complex.I*(s:ℂ)) =
        1 + ∫ x : ℝ, halfLineCharacter (k:ℂ) x * G x := by
    intro k
    simpa [G, mul_comm] using
      shiftedDual_eq_one_add_integral hr hs (z := (k:ℂ)) (by simp)
  have hPhiI :
      dualPhiC r c (-Complex.I - Complex.I*(s:ℂ)) =
        1 + ∫ x : ℝ, Complex.exp (-(x:ℂ)) * G x := by
    have hz : (-Complex.I : ℂ).im ≤ 0 := by norm_num
    have h := shiftedDual_eq_one_add_integral hr hs (z := -Complex.I) hz
    simpa [G, halfLineCharacter, mul_comm] using h
  rw [hPhiI]
  simp_rw [hPhiReal]
  rw [MeasureTheory.VectorMeasure.integral_fun_add]
  rw [MeasureTheory.VectorMeasure.integral_fun_add]
  simp only [MeasureTheory.VectorMeasure.integral_const]
  have hswap_mu := integral_mul_fsTransform_swap_halfLine mu hG
  have hswap_nu := integral_mul_fsTransform_swap_halfLine nu hG
  -- Insert the residual equality pointwise on `x >= 0`.  The density `G`
  -- vanishes on the negative half-line.
  have hresInt :
      ∫ x : ℝ, G x *
          (Complex.exp (-(x:ℂ)) - fsTransform mu x) =
        ∫ x : ℝ, G x * fsTransform nu x := by
    apply integral_congr_ae
    filter_upwards [shiftedDualDensity_ae_eq_zero_on_nonpos (r:=r) (c:=c) (s:=s)] with x hxG
    by_cases hx : 0 ≤ x
    · rw [hres x hx]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      have : G x = 0 := by
        simpa [G] using hxG
      simp [this]
  rw [hswap_mu] at hresInt
  rw [hswap_nu] at hresInt
  -- The `x=0` part of the residual supplies the two constant terms.
  have h0 := hres 0 le_rfl
  simp [fsTransform, realCharacter, cmul] at h0
  linear_combination hresInt + h0

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
          dualPhiC r c ((k:ℂ) - Complex.I * ((1/(n+1:ℝ)):ℂ)) ∂[cmul; mu.1])
      atTop
      (nhds (∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul; mu.1])) := by
  have hr : 0 < r := lt_trans hR hRr
  apply MeasureTheory.VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := mu.1) (B := cmul) (bound := fun _ => (1:ℝ))
  · intro n
    fun_prop
  · intro n
    filter_upwards with k
    apply norm_dualPhiC_le_one hr hc
    have hs : 0 < 1/(n+1:ℝ) := one_div_pos.mpr (by positivity)
    simp [hs]
  · exact integrable_const (1:ℝ)
  · have hmem : ∀ᵐ k : ℝ ∂mu.1.variation, k ∈ Set.Icc (-R) R := by
      rw [ae_iff]
      simpa [SupportedIn] using hsupp
    filter_upwards [hmem] with k hk
    have habs : |k| < r := by
      rw [abs_lt]
      constructor <;> linarith [hk.1, hk.2, hRr]
    have hcont := (continuousAt_dualPhiC_real_inside (R:=r) (c:=c) habs).tendsto
    have harg : Tendsto
        (fun n : ℕ => (k:ℂ) - Complex.I * ((1/(n+1:ℝ)):ℂ))
        atTop (nhds (k:ℂ)) := by
      have hz : Tendsto (fun n : ℕ => (1/(n+1:ℝ))) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hz.ofReal)
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
  let sn : ℕ → ℝ := fun n => 1/(n+1:ℝ)
  have hsn : ∀ n, 0 < sn n := fun n => one_div_pos.mpr (by positivity)
  let lhs : ℕ → ℂ := fun n =>
    dualPhiC r c (-Complex.I - Complex.I*(sn n:ℂ)) -
      (∫ᵛ k : ℝ,
        dualPhiC r c ((k:ℂ)-Complex.I*(sn n:ℂ)) ∂[cmul;mu.1])
  have hlhs_bound : ∀ n, ‖lhs n‖ ≤ tv nu := by
    intro n
    rw [show lhs n =
      ∫ᵛ k : ℝ,
        dualPhiC r c ((k:ℂ)-Complex.I*(sn n:ℂ)) ∂[cmul;nu.1] by
          exact shifted_dual_residual_identity hr (hsn n) hres]
    have hv := MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
      (μ:=nu.1) (B:=cmul) (C:=1) (by
        filter_upwards with k
        exact norm_dualPhiC_le_one hr hc (by simp [hsn n]))
    simpa [tv, norm_cmul] using hv
  have hphi : Tendsto
      (fun n : ℕ => dualPhiC r c (-Complex.I-Complex.I*(sn n:ℂ))) atTop
      (nhds (dualPhiC r c (-Complex.I))) := by
    have harg : Tendsto
        (fun n : ℕ => -Complex.I-Complex.I*(sn n:ℂ)) atTop
        (nhds (-Complex.I)) := by
      have hz : Tendsto sn atTop (nhds 0) := by
        simpa [sn] using tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hz.ofReal)
    exact ((analyticOnNhd_dualPhiC hr) (-Complex.I) neg_I_mem_lowerHalfPlane).continuousAt.tendsto.comp harg
  have hmu := tendsto_shifted_dual_vectorIntegral_supported hR hRr hc mu hsupp
  have hlhs : Tendsto lhs atTop
      (nhds (dualPhiC r c (-Complex.I) -
        (∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul;mu.1]))) := by
    exact hphi.sub hmu
  have hnorm := (continuous_norm.tendsto _).comp hlhs
  exact le_of_tendsto hnorm (Eventually.of_forall hlhs_bound)

/-- Integral of the dual boundary value over a measure supported in `[-R,R]`. -/
theorem norm_integral_dual_le_dualA_mul_tv
    {R r c : ℝ} (hR : 0 < R) (hRr : R < r) (hc : 0 ≤ c)
    {mu : FiniteCMeasure} (hsupp : SupportedIn R mu) :
    ‖∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul; mu.1]‖
      ≤ dualA c * tv mu := by
  have ha : 0 ≤ dualA c := (Real.exp_pos _).le
  have hmem : ∀ᵐ k : ℝ ∂mu.1.variation, k ∈ Set.Icc (-R) R := by
    rw [ae_iff]
    simpa [SupportedIn] using hsupp
  have hbound : ∀ᵐ k : ℝ ∂mu.1.variation,
      ‖dualPhiC r c (k:ℂ)‖ ≤ dualA c := by
    filter_upwards [hmem] with k hk
    have habs : |k| < r := by
      rw [abs_lt]
      constructor <;> linarith [hk.1, hk.2, hRr]
    rw [norm_dualPhiC_real_inside habs]
  have h := MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
    (μ:=mu.1) (B:=cmul) (C:=dualA c) hbound
  simpa [tv, norm_cmul] using h

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
    have hmu := norm_integral_dual_le_dualA_mul_tv hR hRr hc hsupp
    have hphi : ‖dualPhiC r c (-Complex.I)‖ = (dualA c)^(pR r) := by
      rw [dualPhiC_neg_I hr]
      simp
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
    apply Real.continuous_rpow.comp_tendsto
    · exact tendsto_const_nhds
    · exact pR_continuous.continuousAt.tendsto.comp
        (by simpa using tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
  have hle : ∀ n,
      (dualA c)^(pR (R+1/(n+1:ℝ))) - dualA c*tv mu ≤ tv nu := by
    intro n
    exact hfor _ (by positivity)
  have := le_of_tendsto hlim (Eventually.of_forall hle)
  calc
    (dualA c)^(pR R) - dualA c * lam
        ≤ (dualA c)^(pR R) - dualA c * tv mu := by
          have ha := (Real.exp_pos (-Real.pi*c)).le
          gcongr
    _ ≤ tv nu := this

/-- Convert an arbitrary `a in (0,1]` to the `c>=0` parameter of the note. -/
def cOfA (a : ℝ) : ℝ := -Real.log a / Real.pi

lemma cOfA_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) : 0 ≤ cOfA a := by
  unfold cOfA
  have : Real.log a ≤ 0 := (Real.log_nonpos ha0.le).2 ha1
  positivity

lemma dualA_cOfA {a : ℝ} (ha0 : 0 < a) : dualA (cOfA a) = a := by
  unfold dualA cOfA
  rw [show -Real.pi * (-Real.log a / Real.pi) = Real.log a by
    field_simp [Real.pi_ne_zero]; ring]
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
    {R lam e : ℝ} (hR : 0 < R) (hlam : lam ≤ pR R)
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
    · exact div_le_one hlam0.le |>.2 hlam
    · positivity
  have h := wiener_cost_lower_of_a hR ha0 ha1 he
  have halg := high_test_point (p:=pR R) (q:=qR R) (lam:=lam)
      hp hq (pR_add_qR R) hlam
  simpa [a, halg] using h

end LCHSWiener
