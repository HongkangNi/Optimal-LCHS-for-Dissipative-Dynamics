import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LCHSWiener.KernelUpperBound

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology

namespace LCHSWiener

/-!
# Poisson formula at `-i` for the lower half-plane

If `f` is bounded and continuous on the closed lower half-plane and complex
differentiable in the open lower half-plane, then

  f(-i) = ∫ f(k) / (π(1+k²)) dk.

The proof transports the mean value property on discs of radius `r < 1`
through the Cayley map `w ↦ -i(1+w)/(1-w)`, lets `r → 1` by dominated
convergence, and changes variables `θ = π - 2 arctan k` on the unit circle.
The function may take values in any complex Banach space; it is applied to
operator-valued functions in the matrix version of the theorem.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Cayley map from the unit disc onto the lower half-plane, with `0 ↦ -i`. -/
def cayleyLower (w : ℂ) : ℂ := -Complex.I * (1 + w) / (1 - w)

lemma cayleyLower_zero : cayleyLower 0 = -Complex.I := by
  simp [cayleyLower]

lemma cayleyLower_im (w : ℂ) :
    (cayleyLower w).im = -(1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  rw [cayleyLower, Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.normSq_apply]
  ring

lemma cayleyLower_im_nonpos {w : ℂ} (hw : ‖w‖ ≤ 1) : (cayleyLower w).im ≤ 0 := by
  rw [cayleyLower_im]
  have h1 : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Complex.normSq_nonneg _)

lemma cayleyLower_im_neg {w : ℂ} (hw : ‖w‖ < 1) : (cayleyLower w).im < 0 := by
  rw [cayleyLower_im]
  have h1 : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  have h2 : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.2 hw1
  exact div_neg_of_neg_of_pos (by linarith) h2

lemma differentiableAt_cayleyLower {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ cayleyLower w := by
  have hw1 : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  unfold cayleyLower
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)).div
    ((differentiableAt_const _).sub differentiableAt_id) hw1

lemma ne_one_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : w ≠ 1 := by
  rintro rfl
  simp at hw

/-- The circle parameter `θ = π - 2 arctan k`. -/
def circleParam (k : ℝ) : ℝ := Real.pi - 2 * Real.arctan k

lemma circleMap_circleParam (k : ℝ) :
    circleMap 0 1 (circleParam k) = ((k:ℂ) + Complex.I) / ((k:ℂ) - Complex.I) := by
  have hk : (k:ℂ) - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rw [eq_div_iff hk, circleMap, circleParam]
  simp only [zero_add, Complex.ofReal_one, one_mul]
  have hcos := Real.cos_sq_arctan k
  have hsc : Real.sin (Real.arctan k) * Real.cos (Real.arctan k) = k / (1 + k^2) := by
    rw [Real.sin_arctan, Real.cos_arctan]
    have hpos : 0 < 1 + k^2 := by positivity
    field_simp
    rw [Real.sq_sqrt hpos.le]
  have hexp : Complex.exp (((Real.pi - 2 * Real.arctan k : ℝ) : ℂ) * Complex.I) =
      (((1 - k^2) / (1 + k^2) : ℝ) : ℂ) * (-1) + (((2 * k) / (1 + k^2) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_two_mul, Real.sin_two_mul]
    have hpos : 0 < 1 + k^2 := by positivity
    have hc2 : 2 * Real.cos (Real.arctan k) ^ 2 - 1 = (1 - k^2) / (1 + k^2) := by
      rw [hcos]; field_simp; ring
    have hs2 : 2 * Real.sin (Real.arctan k) * Real.cos (Real.arctan k) = 2 * k / (1 + k^2) := by
      rw [mul_assoc, hsc]; ring
    rw [hc2, hs2]
    push_cast
    ring
  rw [hexp]
  have hpos : (1 + (k:ℂ)^2) ≠ 0 := by
    have : (0:ℝ) < 1 + k^2 := by positivity
    exact_mod_cast this.ne'
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma cayleyLower_circleMap_circleParam (k : ℝ) :
    cayleyLower (circleMap 0 1 (circleParam k)) = k := by
  rw [circleMap_circleParam, cayleyLower]
  have hk : (k:ℂ) - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have h2 : (1 : ℂ) - ((k:ℂ) + Complex.I) / ((k:ℂ) - Complex.I) ≠ 0 := by
    rw [one_sub_div hk]
    refine div_ne_zero ?_ hk
    ring_nf
    simp
  rw [div_eq_iff h2, one_sub_div hk, one_add_div hk]
  field_simp
  ring_nf

lemma range_circleParam : Set.range circleParam = Set.Ioo 0 (2 * Real.pi) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    have h := Real.arctan_mem_Ioo k
    simp only [circleParam, Set.mem_Ioo]
    constructor <;> linarith [h.1, h.2]
  · intro hx
    refine ⟨Real.tan ((Real.pi - x) / 2), ?_⟩
    have ha : (Real.pi - x) / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [hx.1, hx.2]
    simp only [circleParam]
    rw [Real.arctan_tan ha.1 ha.2]
    ring

lemma hasDerivAt_circleParam (k : ℝ) :
    HasDerivAt circleParam (-(2 / (1 + k^2))) k := by
  have h := ((Real.hasDerivAt_arctan k).const_mul 2).const_sub Real.pi
  unfold circleParam
  convert h using 1
  ring

lemma injective_circleParam : Function.Injective circleParam := by
  intro a b h
  simp only [circleParam] at h
  exact Real.arctan_injective (by linarith)

/-- **Poisson formula at `-i`** for bounded holomorphic functions on the lower
half-plane that are continuous up to the real axis. -/
theorem poisson_lowerHalfPlane {f : ℂ → E} {M : ℝ}
    (hcont : ContinuousOn f {z : ℂ | z.im ≤ 0})
    (hdiff : DifferentiableOn ℂ f {z : ℂ | z.im < 0})
    (hbd : ∀ z : ℂ, z.im ≤ 0 → ‖f z‖ ≤ M) :
    ∫ k : ℝ, (cauchyDensity k : ℂ) • f k = f (-Complex.I) := by
  simp_rw [Complex.coe_smul]
  let g : ℂ → E := fun w => f (cayleyLower w)
  have hopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  -- `g` is holomorphic on the open unit disc
  have hgdiff : DifferentiableOn ℂ g (ball 0 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    have hf : DifferentiableAt ℂ f (cayleyLower w) :=
      (hdiff _ (cayleyLower_im_neg hw')).differentiableAt (hopen.mem_nhds (cayleyLower_im_neg hw'))
    exact (hf.comp w (differentiableAt_cayleyLower (ne_one_of_norm_lt_one hw'))).differentiableWithinAt
  -- mean value property on circles of radius `r < 1`
  have hmv : ∀ r : ℝ, 0 < r → r < 1 →
      (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap 0 r θ) = f (-Complex.I) := by
    intro r hr0 hr1
    have hdc : DiffContOnCl ℂ g (ball 0 |r|) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by rw [abs_of_pos hr0]; exact hr0.ne')]
      exact hgdiff.mono (closedBall_subset_ball (by rw [abs_of_pos hr0]; exact hr1))
    have := hdc.circleAverage
    rw [Real.circleAverage_def] at this
    rw [this]
    simp [g, cayleyLower_zero]
  -- pass to the limit `r → 1`
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n:ℝ) + 2)
  have hr0 : ∀ n, 0 < r n := by
    intro n
    have : 1 / ((n:ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    simp only [r]; linarith
  have hr1 : ∀ n, r n < 1 := by
    intro n
    have : 0 < 1 / ((n:ℝ) + 2) := by positivity
    simp only [r]; linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 2)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := this.comp (tendsto_add_atTop_nat 1)
      refine h2.congr fun n => ?_
      simp only [Function.comp, Nat.cast_add, Nat.cast_one]
      ring_nf
    simpa [r] using (tendsto_const_nhds (x := (1:ℝ))).sub h
  have hlim : Tendsto (fun n => ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap 0 (r n) θ)) atTop
      (𝓝 (∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap 0 1 θ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun n => ?_) (Eventually.of_forall fun n => ?_)
      intervalIntegrable_const ?_
    · -- measurability: continuous integrand
      refine (ContinuousOn.comp_continuous (hgdiff.continuousOn) (continuous_circleMap 0 (r n))
        fun θ => ?_).aestronglyMeasurable
      simp [abs_of_pos (hr0 n), hr1 n]
    · refine Eventually.of_forall fun θ _ => hbd _ (cayleyLower_im_nonpos ?_)
      simp [abs_of_pos (hr0 n), (hr1 n).le]
    · -- pointwise convergence away from `θ = 2π`
      have hae : ∀ᵐ θ : ℝ ∂volume, θ ≠ 2 * Real.pi := by
        simpa using (Set.countable_singleton (2 * Real.pi)).ae_notMem volume
      filter_upwards [hae] with θ hθ hθmem
      rw [Set.uIoc_of_le (by positivity)] at hθmem
      have hθ' : θ ∈ Set.Ioo 0 (2 * Real.pi) := ⟨hθmem.1, lt_of_le_of_ne hθmem.2 hθ⟩
      have hw1 : circleMap 0 1 θ ≠ 1 := by
        rw [circleMap]
        simp only [zero_add, Complex.ofReal_one, one_mul]
        intro h
        rw [Complex.exp_eq_one_iff] at h
        obtain ⟨n, hn⟩ := h
        have him := congrArg Complex.im hn
        simp at him
        have hθn : θ = n * (2 * Real.pi) := by linarith
        have h1 : (0:ℝ) < n := by
          by_contra hle
          push Not at hle
          nlinarith [hθ'.1, Real.pi_pos]
        have h2 : (n:ℝ) < 1 := by
          by_contra hle
          push Not at hle
          nlinarith [hθ'.2, Real.pi_pos]
        have : (0:ℤ) < n := by exact_mod_cast h1
        have : n < (1:ℤ) := by exact_mod_cast h2
        omega
      have hcirc : Tendsto (fun n => circleMap 0 (r n) θ) atTop (𝓝 (circleMap 0 1 θ)) := by
        have hc : Continuous fun R : ℝ => circleMap 0 R θ := by
          unfold circleMap; fun_prop
        exact (hc.tendsto 1).comp hrlim
      have hcay : Tendsto (fun n => cayleyLower (circleMap 0 (r n) θ)) atTop
          (𝓝[{z : ℂ | z.im ≤ 0}] cayleyLower (circleMap 0 1 θ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨
          ((differentiableAt_cayleyLower hw1).continuousAt.tendsto).comp hcirc,
          Eventually.of_forall fun n => cayleyLower_im_nonpos ?_⟩
        simp [abs_of_pos (hr0 n), (hr1 n).le]
      have hmem : cayleyLower (circleMap 0 1 θ) ∈ {z : ℂ | z.im ≤ 0} :=
        cayleyLower_im_nonpos (by simp)
      exact ((hcont _ hmem).tendsto).comp hcay
  have hboundary : (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap 0 1 θ) =
      f (-Complex.I) := by
    have h := (hlim.const_smul ((2 * Real.pi)⁻¹ : ℝ))
    have hconst : (fun n => (2 * Real.pi)⁻¹ •
        ∫ θ in (0:ℝ)..2 * Real.pi, g (circleMap 0 (r n) θ)) = fun _ => f (-Complex.I) :=
      funext fun n => hmv (r n) (hr0 n) (hr1 n)
    rw [hconst] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- change of variables on the circle
  have hcov : ∫ θ in Set.Ioo 0 (2 * Real.pi), g (circleMap 0 1 θ) =
      ∫ k : ℝ, (2 / (1 + k^2)) • f k := by
    have h := integral_image_eq_integral_abs_deriv_smul (s := Set.univ) (f := circleParam)
      (f' := fun k => -(2 / (1 + k^2))) MeasurableSet.univ
      (fun k _ => (hasDerivAt_circleParam k).hasDerivWithinAt)
      (injective_circleParam.injOn) (fun θ => g (circleMap 0 1 θ))
    rw [Set.image_univ, range_circleParam, Measure.restrict_univ] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [g, cayleyLower_circleMap_circleParam]
    congr 1
    rw [abs_neg, abs_of_pos (by positivity)]
  rw [← hboundary, intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo,
    hcov, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [smul_smul, cauchyDensity]
  congr 1
  field_simp

end LCHSWiener
