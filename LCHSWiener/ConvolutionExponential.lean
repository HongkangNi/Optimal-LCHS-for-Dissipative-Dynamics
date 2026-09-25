import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import LCHSWiener.HalfLineKernel
import LCHSWiener.MeasureFourier

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LCHSWiener

/-!
# The positive-half-line convolution exponential

This file replaces the abstract existence statement that appeared in the first
prototype of `HalfLineRepresentation.lean` by an explicit `L¹` construction.
For an integrable `h` supported in `(0,+∞)` we form

  h₁ = h,
  hₙ₊₁ = hₙ *_+ h,
  G_h = ∑_{n≥0} hₙ₊₁/(n+1)!.

The standard `L¹` convolution estimate implies absolute convergence.  The
Laplace character `χ_z(x)=exp(-izx)` is multiplicative on addition, so its
integral against `hₙ` is the corresponding power of the transform of `h`.
Consequently

  1 + ∫ χ_z G_h = exp(∫ χ_z h).

Only Mathlib's positive convolution, Bochner integration and summable-series
machinery are used.
-/

/-- Positive convolution powers.  The index is shifted: `posConvPow h 0 = h`. -/
def posConvPow (h : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => h
  | n + 1 => MeasureTheory.posConvolution (posConvPow h n) h cmul volume

@[simp] theorem posConvPow_zero (h : ℝ → ℂ) : posConvPow h 0 = h := rfl

@[simp] theorem posConvPow_succ (h : ℝ → ℂ) (n : ℕ) :
    posConvPow h (n+1) = MeasureTheory.posConvolution (posConvPow h n) h cmul volume := rfl

/-- A positive convolution vanishes on the closed negative half-line. -/
lemma posConvolution_of_nonpos {f g : ℝ → ℂ} {x : ℝ} (hx : x ≤ 0) :
    MeasureTheory.posConvolution f g cmul volume x = 0 := by
  unfold MeasureTheory.posConvolution
  exact Set.indicator_of_notMem (by simpa using hx) _

/-- Positive convolution powers of a function supported in `(0,∞)` are again
supported there. -/
lemma posConvPow_of_nonpos {h : ℝ → ℂ} (hsupp : ∀ x ≤ 0, h x = 0) :
    ∀ n : ℕ, ∀ x ≤ 0, posConvPow h n x = 0 := by
  intro n x hx
  cases n with
  | zero => exact hsupp x hx
  | succ n => exact posConvolution_of_nonpos hx

/-- For a function vanishing on `(-∞,0]`, the whole-line integral is the
half-line integral. -/
lemma integral_eq_setIntegral_Ioi_of_nonpos {F : ℝ → ℂ} (hF : ∀ x ≤ 0, F x = 0) :
    ∫ x, F x = ∫ x in Set.Ioi (0:ℝ), F x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  exact hF x (by simpa using hx)

/-- Norm estimate for one positive convolution, in whole-line `L¹` norms. -/
theorem integral_norm_posConvolution_le
    {f g : ℝ → ℂ} (hf : Integrable f volume) (hg : Integrable g volume) :
    ∫ x, ‖MeasureTheory.posConvolution f g cmul volume x‖
      ≤ (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  have hconv := MeasureTheory.integrable_posConvolution hf.integrableOn hg.integrableOn cmul
    (μ := volume)
  have hconvN := MeasureTheory.integrable_posConvolution hf.norm.integrableOn
    hg.norm.integrableOn (ContinuousLinearMap.mul ℝ ℝ) (μ := volume)
  have hprod := MeasureTheory.integral_posConvolution hf.norm.integrableOn
    hg.norm.integrableOn (ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
  simp only [ContinuousLinearMap.mul_apply'] at hprod
  have hsupp : ∫ x, ‖MeasureTheory.posConvolution f g cmul volume x‖ =
      ∫ x in Set.Ioi (0:ℝ), ‖MeasureTheory.posConvolution f g cmul volume x‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    simp [posConvolution_of_nonpos (show x ≤ 0 by simpa using hx)]
  have hstep : ∫ x in Set.Ioi (0:ℝ), ‖MeasureTheory.posConvolution f g cmul volume x‖ ≤
      (∫ x in Set.Ioi (0:ℝ), ‖f x‖) * (∫ x in Set.Ioi (0:ℝ), ‖g x‖) := by
    rw [← hprod]
    refine setIntegral_mono_on hconv.norm.integrableOn ?_ measurableSet_Ioi ?_
    · refine hconvN.integrableOn.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp [MeasureTheory.posConvolution, Set.indicator_of_mem hx]
    · intro x hx
      have hx0 : (0:ℝ) ≤ x := le_of_lt hx
      simp only [MeasureTheory.posConvolution, Set.indicator_of_mem hx]
      refine (intervalIntegral.norm_integral_le_integral_norm hx0).trans (le_of_eq ?_)
      congr 1
      funext t
      simp [cmul]
  have hfI : ∫ x in Set.Ioi (0:ℝ), ‖f x‖ ≤ ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have hgI : ∫ x in Set.Ioi (0:ℝ), ‖g x‖ ≤ ∫ x, ‖g x‖ :=
    setIntegral_le_integral hg.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  rw [hsupp]
  refine hstep.trans (mul_le_mul hfI hgI (integral_nonneg fun _ => norm_nonneg _)
    (integral_nonneg fun _ => norm_nonneg _))

/-- Every positive convolution power is integrable. -/
theorem integrable_posConvPow
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    ∀ n : ℕ, Integrable (posConvPow h n) volume := by
  intro n
  induction n with
  | zero => simpa using hh
  | succ n ihn =>
      exact MeasureTheory.integrable_posConvolution ihn.integrableOn hh.integrableOn cmul

/-- The `L¹` norm of the `n+1`-st power is bounded by the corresponding
scalar power. -/
theorem integral_norm_posConvPow_le
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    ∀ n : ℕ, ∫ x, ‖posConvPow h n x‖ ≤ (∫ x, ‖h x‖) ^ (n+1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
      rw [posConvPow_succ]
      calc
        ∫ x, ‖MeasureTheory.posConvolution (posConvPow h n) h cmul volume x‖
            ≤ (∫ x, ‖posConvPow h n x‖) * ∫ x, ‖h x‖ :=
              integral_norm_posConvolution_le (integrable_posConvPow hh n) hh
        _ ≤ (∫ x, ‖h x‖)^(n+1) * ∫ x, ‖h x‖ :=
              mul_le_mul_of_nonneg_right ihn (integral_nonneg fun _ => norm_nonneg _)
        _ = (∫ x, ‖h x‖)^((n+1)+1) := by ring

/-- Coefficient used in the convolution exponential. -/
def convExpTerm (h : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ((n+1 : ℕ).factorial : ℂ)⁻¹ * posConvPow h n x

/-- The absolutely convergent density part of the convolution exponential. -/
def convolutionExponentialDensity (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, convExpTerm h n x

lemma integrable_convExpTerm {h : ℝ → ℂ} (hh : Integrable h volume) (n : ℕ) :
    Integrable (convExpTerm h n) volume := by
  unfold convExpTerm
  exact (integrable_posConvPow hh n).const_mul _

lemma convExpTerm_of_nonpos {h : ℝ → ℂ} (hsupp : ∀ x ≤ 0, h x = 0)
    (n : ℕ) {x : ℝ} (hx : x ≤ 0) : convExpTerm h n x = 0 := by
  simp [convExpTerm, posConvPow_of_nonpos hsupp n x hx]

/-- The sum of integrals of norms of the terms is finite. -/
theorem summable_integral_norm_convExpTerm
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    Summable (fun n : ℕ => ∫ x, ‖convExpTerm h n x‖) := by
  let A : ℝ := ∫ x, ‖h x‖
  have hbound : ∀ n : ℕ,
      ∫ x, ‖convExpTerm h n x‖ ≤ A^(n+1) / (n+1).factorial := by
    intro n
    unfold convExpTerm
    simp only [norm_mul, norm_inv, Complex.norm_natCast]
    rw [integral_const_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (integral_norm_posConvPow_le hh n) (by positivity)
  have hseries : Summable (fun n : ℕ => A^(n+1) / (n+1).factorial) := by
    have hexp : Summable (fun m : ℕ => A^m / m.factorial) := Real.summable_pow_div_factorial A
    exact hexp.comp_injective (Nat.succ_injective)
  exact Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _)
    hbound hseries

/-- The series of lintegrals of the terms is finite. -/
lemma tsum_lintegral_enorm_convExpTerm_ne_top
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    ∑' n : ℕ, ∫⁻ x, ‖convExpTerm h n x‖ₑ ≠ ⊤ := by
  have heq : ∀ n, ∫⁻ x, ‖convExpTerm h n x‖ₑ =
      ENNReal.ofReal (∫ x, ‖convExpTerm h n x‖) := fun n =>
    (ofReal_integral_norm_eq_lintegral_enorm (integrable_convExpTerm hh n)).symm
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _)
    (summable_integral_norm_convExpTerm hh)]
  exact ENNReal.ofReal_ne_top

/-- The convolution-exponential density is integrable. -/
theorem integrable_convolutionExponentialDensity
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    Integrable (convolutionExponentialDensity h) volume := by
  have hmeas : ∀ n, AEStronglyMeasurable (convExpTerm h n) volume :=
    fun n => (integrable_convExpTerm hh n).aestronglyMeasurable
  have htop := tsum_lintegral_enorm_convExpTerm_ne_top hh
  have hlint : ∫⁻ x, ∑' n, ‖convExpTerm h n x‖ₑ ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hmeas n).enorm]
    exact htop
  -- almost every point has an absolutely summable series
  have hae : ∀ᵐ x ∂volume, Summable fun n => convExpTerm h n x := by
    filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum fun n => (hmeas n).enorm) hlint]
      with x hx
    refine Summable.of_norm ?_
    have hx' : ∑' n, (‖convExpTerm h n x‖₊ : ENNReal) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hx')
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun N x => ∑ n ∈ Finset.range N, convExpTerm h n x)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => hmeas n) ?_
    filter_upwards [hae] with x hx
    exact hx.hasSum.tendsto_sum_nat
  · unfold HasFiniteIntegral convolutionExponentialDensity
    exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm)
      (lt_top_iff_ne_top.2 hlint)

/-- Interchange the convolution-exponential series and a multiplier bounded
by one on the positive half-line. -/
theorem integral_mul_convolutionExponentialDensity_eq_tsum
    {h : ℝ → ℂ} (hh : Integrable h volume) (hsupp : ∀ x ≤ 0, h x = 0)
    {m : ℝ → ℂ}
    (hm : AEStronglyMeasurable m volume)
    (hmb : ∀ x, 0 < x → ‖m x‖ ≤ 1) :
    ∫ x, m x * convolutionExponentialDensity h x =
      ∑' n : ℕ, ∫ x, m x * convExpTerm h n x := by
  unfold convolutionExponentialDensity
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => m x * convExpTerm h n x) volume :=
    fun n => hm.mul (integrable_convExpTerm hh n).aestronglyMeasurable
  have hle : ∀ n x, ‖m x * convExpTerm h n x‖ₑ ≤ ‖convExpTerm h n x‖ₑ := by
    intro n x
    by_cases hx : 0 < x
    · rw [enorm_mul]
      calc ‖m x‖ₑ * ‖convExpTerm h n x‖ₑ ≤ 1 * ‖convExpTerm h n x‖ₑ := by
            gcongr
            rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (hmb x hx)
        _ = ‖convExpTerm h n x‖ₑ := one_mul _
    · simp [convExpTerm_of_nonpos hsupp n (le_of_not_gt hx)]
  have htop : ∑' n, ∫⁻ x, ‖m x * convExpTerm h n x‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top (tsum_lintegral_enorm_convExpTerm_ne_top hh)
      (ENNReal.tsum_le_tsum fun n => lintegral_mono fun x => hle n x)
  simp_rw [← tsum_mul_left]
  exact integral_tsum hmeas htop

/-- Multiplicativity of the half-line character. -/
lemma halfLineCharacter_add (z : ℂ) (x y : ℝ) :
    halfLineCharacter z (x+y) = halfLineCharacter z x * halfLineCharacter z y := by
  unfold halfLineCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integrableOn_character_mul
    {f : ℝ → ℂ} (hf : Integrable f volume) {z : ℂ} (hz : z.im ≤ 0) :
    IntegrableOn (fun x => halfLineCharacter z x * f x) (Set.Ioi 0) volume := by
  refine Integrable.mono' hf.norm.integrableOn
    ((continuous_halfLineCharacter z).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_halfLineCharacter_le_one hz (le_of_lt hx))

/-- Transform of one positive convolution is the product of transforms. -/
theorem integral_character_posConvolution
    {f g : ℝ → ℂ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hfs : ∀ x ≤ 0, f x = 0) (hgs : ∀ x ≤ 0, g x = 0)
    {z : ℂ} (hz : z.im ≤ 0) :
    ∫ x, halfLineCharacter z x *
        MeasureTheory.posConvolution f g cmul volume x =
      (∫ x, halfLineCharacter z x * f x) *
      (∫ x, halfLineCharacter z x * g x) := by
  have hconv := MeasureTheory.integral_posConvolution (μ := volume) (ν := volume)
    (integrableOn_character_mul hf hz) (integrableOn_character_mul hg hz) cmul
  have hz0 : ∀ F : ℝ → ℂ, (∀ x ≤ 0, F x = 0) →
      ∀ x ≤ 0, halfLineCharacter z x * F x = 0 := fun F hF x hx => by
    rw [hF x hx, mul_zero]
  rw [integral_eq_setIntegral_Ioi_of_nonpos
      (hz0 _ fun x hx => posConvolution_of_nonpos hx),
    integral_eq_setIntegral_Ioi_of_nonpos (hz0 f hfs),
    integral_eq_setIntegral_Ioi_of_nonpos (hz0 g hgs)]
  refine Eq.trans ?_ hconv
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [MeasureTheory.posConvolution, Set.indicator_of_mem hx]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hsplit : halfLineCharacter z x = halfLineCharacter z t * halfLineCharacter z (x - t) := by
    rw [← halfLineCharacter_add]
    ring_nf
  simp only [cmul, ContinuousLinearMap.mul_apply', hsplit]
  ring

/-- Character transform of each convolution power. -/
theorem integral_character_posConvPow
    {h : ℝ → ℂ} (hh : Integrable h volume) (hsupp : ∀ x ≤ 0, h x = 0)
    {z : ℂ} (hz : z.im ≤ 0) :
    ∀ n : ℕ,
      ∫ x, halfLineCharacter z x * posConvPow h n x =
        (∫ x, halfLineCharacter z x * h x)^(n+1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
      rw [posConvPow_succ,
        integral_character_posConvolution (integrable_posConvPow hh n) hh
          (posConvPow_of_nonpos hsupp n) hsupp hz,
        ihn]
      ring

/-- Transform of the `n`th exponential-series term. -/
theorem integral_character_convExpTerm
    {h : ℝ → ℂ} (hh : Integrable h volume) (hsupp : ∀ x ≤ 0, h x = 0)
    {z : ℂ} (hz : z.im ≤ 0) (n : ℕ) :
    ∫ x, halfLineCharacter z x * convExpTerm h n x =
      (∫ x, halfLineCharacter z x * h x)^(n+1) /
        (n+1).factorial := by
  unfold convExpTerm
  simp_rw [mul_left_comm (halfLineCharacter z _)]
  rw [integral_const_mul, integral_character_posConvPow hh hsupp hz n, div_eq_inv_mul]

/-- Main convolution-exponential identity. -/
theorem one_add_integral_character_convolutionExponentialDensity
    {h : ℝ → ℂ} (hh : Integrable h volume) (hsupp : ∀ x ≤ 0, h x = 0)
    {z : ℂ} (hz : z.im ≤ 0) :
    1 + ∫ x, halfLineCharacter z x * convolutionExponentialDensity h x =
      Complex.exp (∫ x, halfLineCharacter z x * h x) := by
  rw [integral_mul_convolutionExponentialDensity_eq_tsum hh hsupp
    (continuous_halfLineCharacter z).aestronglyMeasurable
    (fun x hx => norm_halfLineCharacter_le_one hz (le_of_lt hx))]
  simp_rw [integral_character_convExpTerm hh hsupp hz]
  set a := ∫ x, halfLineCharacter z x * h x
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  dsimp only
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).2 (NormedSpace.expSeries_div_summable a))]
  simp

end LCHSWiener
