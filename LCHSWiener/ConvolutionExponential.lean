import Mathlib
import LCHSWiener.HalfLineKernel

noncomputable section

open Set MeasureTheory scoped BigOperators

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

/-- `L¹` mass on the positive half-line. -/
def posL1 (h : ℝ → ℂ) : ℝ := ∫ x in Set.Ioi (0:ℝ), ‖h x‖

lemma posL1_nonneg (h : ℝ → ℂ) : 0 ≤ posL1 h := by
  unfold posL1
  exact integral_nonneg fun _ => norm_nonneg _

/-- Norm estimate for one positive convolution. -/
theorem integral_norm_posConvolution_le
    {f g : ℝ → ℂ}
    (hf : IntegrableOn f (Set.Ioi 0) volume)
    (hg : IntegrableOn g (Set.Ioi 0) volume) :
    ∫ x in Set.Ioi (0:ℝ),
        ‖MeasureTheory.posConvolution f g cmul volume x‖
      ≤ (∫ x in Set.Ioi (0:ℝ), ‖f x‖) *
        (∫ x in Set.Ioi (0:ℝ), ‖g x‖) := by
  have hconv := MeasureTheory.integrable_posConvolution hf hg cmul
  have hpoint : ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioi 0),
      ‖MeasureTheory.posConvolution f g cmul volume x‖ ≤
        ∫ t in Set.Ioi (0:ℝ), ‖f t‖ * ‖g (x-t)‖ := by
    filter_upwards with x
    unfold MeasureTheory.posConvolution
    rw [norm_integral_le_of_norm_le]
    · exact le_rfl
    · filter_upwards with t
      simp only [cmul, ContinuousLinearMap.coe_mul', norm_mul]
  calc
    ∫ x in Set.Ioi (0:ℝ), ‖MeasureTheory.posConvolution f g cmul volume x‖
        ≤ ∫ x in Set.Ioi (0:ℝ),
            (∫ t in Set.Ioi (0:ℝ), ‖f t‖ * ‖g (x-t)‖) :=
          integral_mono_ae hconv.norm.integrableOn
            ((hf.norm.mul_left hg.norm).integral_prod_right.integrableOn) hpoint
    _ = (∫ x in Set.Ioi (0:ℝ), ‖f x‖) *
        (∫ x in Set.Ioi (0:ℝ), ‖g x‖) := by
      simpa using
        (MeasureTheory.integral_posConvolution hf.norm hg.norm
          (ContinuousLinearMap.mul ℝ ℝ))

/-- Every positive convolution power is integrable. -/
theorem integrable_posConvPow
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    ∀ n : ℕ, Integrable (posConvPow h n) volume := by
  intro n
  induction n with
  | zero => simpa using hh
  | succ n ihn =>
      exact MeasureTheory.integrable_posConvolution ihn.integrableOn hh.integrableOn cmul

/-- The positive `L¹` norm of the `n+1`-st power is bounded by the
corresponding scalar power. -/
theorem posL1_posConvPow_le
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    ∀ n : ℕ, posL1 (posConvPow h n) ≤ (posL1 h) ^ (n+1) := by
  intro n
  induction n with
  | zero => simp [posL1]
  | succ n ihn =>
      rw [posConvPow_succ]
      calc
        posL1 (MeasureTheory.posConvolution (posConvPow h n) h cmul volume)
            ≤ posL1 (posConvPow h n) * posL1 h := by
              exact integral_norm_posConvolution_le
                (integrable_posConvPow hh n).integrableOn hh.integrableOn
        _ ≤ (posL1 h)^(n+1) * posL1 h := by
              exact mul_le_mul_of_nonneg_right ihn (posL1_nonneg h)
        _ = (posL1 h)^((n+1)+1) := by ring

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

/-- The sum of integrals of norms of the terms is finite. -/
theorem summable_integral_norm_convExpTerm
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    Summable (fun n : ℕ => ∫ x, ‖convExpTerm h n x‖) := by
  let A : ℝ := ∫ x, ‖h x‖
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hbound : ∀ n : ℕ,
      ∫ x, ‖convExpTerm h n x‖ ≤ A^(n+1) / (n+1).factorial := by
    intro n
    unfold convExpTerm
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hp := posL1_posConvPow_le hh n
    have hsupp : ∫ x, ‖posConvPow h n x‖ = posL1 (posConvPow h n) := by
      -- positive convolution powers vanish a.e. outside the positive half-line
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · simp [hx]
      · have hx' : x ≤ 0 := le_of_not_gt hx
        simp [Set.indicator_of_not_mem (not_lt.mpr hx')]
    rw [hsupp]
    calc
      ‖(((n+1 : ℕ).factorial : ℂ))⁻¹‖ * posL1 (posConvPow h n)
          ≤ ((n+1).factorial : ℝ)⁻¹ * (posL1 h)^(n+1) := by
            gcongr
      _ ≤ ((n+1).factorial : ℝ)⁻¹ * A^(n+1) := by
            gcongr
            unfold posL1
            exact integral_mono_measure (Measure.restrict_le_self)
      _ = A^(n+1) / (n+1).factorial := by
            rw [div_eq_mul_inv]
            ring
  have hseries : Summable (fun n : ℕ => A^(n+1) / (n+1).factorial) := by
    have hexp : Summable (fun m : ℕ => A^m / m.factorial) := Real.summable_pow_div_factorial A
    exact hexp.comp_injective (Nat.succ_injective)
  exact Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _)
    hbound hseries

/-- The convolution-exponential density is integrable. -/
theorem integrable_convolutionExponentialDensity
    {h : ℝ → ℂ} (hh : Integrable h volume) :
    Integrable (convolutionExponentialDensity h) volume := by
  unfold convolutionExponentialDensity
  exact MeasureTheory.integrable_tsum
    (fun n => (integrable_convExpTerm hh n).aestronglyMeasurable)
    (summable_integral_norm_convExpTerm hh)

/-- Interchange the convolution-exponential series and a bounded multiplier. -/
theorem integral_mul_convolutionExponentialDensity_eq_tsum
    {h : ℝ → ℂ} (hh : Integrable h volume)
    {m : ℝ → ℂ}
    (hm : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x : ℝ ∂volume, ‖m x‖ ≤ 1) :
    ∫ x, m x * convolutionExponentialDensity h x =
      ∑' n : ℕ, ∫ x, m x * convExpTerm h n x := by
  unfold convolutionExponentialDensity
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => m x * convExpTerm h n x) volume := by
    intro n
    exact hm.mul (integrable_convExpTerm hh n).aestronglyMeasurable
  have hsum : Summable (fun n => ∫ x, ‖m x * convExpTerm h n x‖) := by
    apply (summable_integral_norm_convExpTerm hh).of_norm_bounded
    intro n
    apply integral_mono_ae
    · exact (integrable_convExpTerm hh n).norm
    · exact ((integrable_convExpTerm hh n).norm.mono' (hmeas n).norm (by
        filter_upwards [hmb] with x hx
        simp only [norm_mul]
        nlinarith)).integrable
    · filter_upwards [hmb] with x hx
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
  exact MeasureTheory.integral_tsum hmeas hsum

/-- Multiplicativity of the half-line character. -/
lemma halfLineCharacter_add (z : ℂ) (x y : ℝ) :
    halfLineCharacter z (x+y) = halfLineCharacter z x * halfLineCharacter z y := by
  unfold halfLineCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Transform of one positive convolution is the product of transforms. -/
theorem integral_character_posConvolution
    {f g : ℝ → ℂ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    {z : ℂ} (hz : z.im ≤ 0) :
    ∫ x, halfLineCharacter z x *
        MeasureTheory.posConvolution f g cmul volume x =
      (∫ x, halfLineCharacter z x * f x) *
      (∫ x, halfLineCharacter z x * g x) := by
  have hfi : IntegrableOn (fun x => halfLineCharacter z x * f x) (Set.Ioi 0) volume := by
    apply hf.integrableOn.mono'
    · exact (continuous_halfLineCharacter z).aestronglyMeasurable.mul hf.aestronglyMeasurable
    · filter_upwards with x
      by_cases hx : 0 ≤ x
      · simpa [norm_mul] using mul_le_mul_of_nonneg_right
          (norm_halfLineCharacter_le_one hz hx) (norm_nonneg (f x))
      · simp
  have hgi : IntegrableOn (fun x => halfLineCharacter z x * g x) (Set.Ioi 0) volume := by
    apply hg.integrableOn.mono'
    · exact (continuous_halfLineCharacter z).aestronglyMeasurable.mul hg.aestronglyMeasurable
    · filter_upwards with x
      by_cases hx : 0 ≤ x
      · simpa [norm_mul] using mul_le_mul_of_nonneg_right
          (norm_halfLineCharacter_le_one hz hx) (norm_nonneg (g x))
      · simp
  have hconv := MeasureTheory.integral_posConvolution hfi hgi cmul
  -- Expand the definition of positive convolution and use χ(x)=χ(t)χ(x-t).
  simpa [MeasureTheory.posConvolution, cmul, halfLineCharacter_add,
    integral_indicator measurableSet_Ioi] using hconv

/-- Character transform of each convolution power. -/
theorem integral_character_posConvPow
    {h : ℝ → ℂ} (hh : Integrable h volume)
    {z : ℂ} (hz : z.im ≤ 0) :
    ∀ n : ℕ,
      ∫ x, halfLineCharacter z x * posConvPow h n x =
        (∫ x, halfLineCharacter z x * h x)^(n+1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
      rw [posConvPow_succ,
        integral_character_posConvolution (integrable_posConvPow hh n) hh hz,
        ihn]
      ring

/-- Transform of the `n`th exponential-series term. -/
theorem integral_character_convExpTerm
    {h : ℝ → ℂ} (hh : Integrable h volume)
    {z : ℂ} (hz : z.im ≤ 0) (n : ℕ) :
    ∫ x, halfLineCharacter z x * convExpTerm h n x =
      (∫ x, halfLineCharacter z x * h x)^(n+1) /
        (n+1).factorial := by
  unfold convExpTerm
  rw [← integral_const_mul]
  rw [integral_character_posConvPow hh hz n]
  push_cast
  field_simp

/-- Main convolution-exponential identity. -/
theorem one_add_integral_character_convolutionExponentialDensity
    {h : ℝ → ℂ} (hh : Integrable h volume)
    {z : ℂ} (hz : z.im ≤ 0) :
    1 + ∫ x, halfLineCharacter z x * convolutionExponentialDensity h x =
      Complex.exp (∫ x, halfLineCharacter z x * h x) := by
  rw [integral_mul_convolutionExponentialDensity_eq_tsum hh
    (continuous_halfLineCharacter z).aestronglyMeasurable]
  · rw [show (∑' n : ℕ,
        ∫ x, halfLineCharacter z x * convExpTerm h n x) =
        ∑' n : ℕ,
          (∫ x, halfLineCharacter z x * h x)^(n+1) / (n+1).factorial by
          congr 1
          funext n
          exact integral_character_convExpTerm hh hz n]
    rw [Complex.exp_eq_tsum_div_factorial]
    rw [← tsum_nat_add 1]
    simp
  · filter_upwards with x
    by_cases hx : 0 ≤ x
    · exact norm_halfLineCharacter_le_one hz hx
    · simp [halfLineCharacter, Complex.norm_exp]

end LCHSWiener
