import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.VectorMeasure.Prod
import Mathlib.Tactic.FunProp
import LCHSWiener.MeasureFourier
import LCHSWiener.HalfLineKernel
import LCHSWiener.DensityMeasure

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LCHSWiener

/-!
# A Fubini lemma for a finite complex measure

The `L¹` function `g` is turned into the finite complex measure `g dx`
(`finiteCMeasureOfDensity`), after which Mathlib's Fubini theorem for two
vector measures of finite variation (`VectorMeasure.integral_integral_swap`)
performs the interchange.
-/

/-- Real-frequency Fourier character. -/
def realCharacter (k x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ))

@[simp] lemma realCharacter_eq_halfLineCharacter (k x : ℝ) :
    realCharacter k x = halfLineCharacter (k:ℂ) x := by
  simp [realCharacter, halfLineCharacter]

lemma norm_realCharacter (k x : ℝ) : ‖realCharacter k x‖ = 1 := by
  rw [realCharacter, Complex.norm_exp]
  simp

lemma continuous_realCharacter_uncurry :
    Continuous fun p : ℝ × ℝ => realCharacter p.1 p.2 := by
  unfold realCharacter
  fun_prop

/-- The Fourier integral of an `L¹` function is uniformly bounded by its
`L¹` norm. -/
theorem norm_integral_mul_realCharacter_le
    {g : ℝ → ℂ} (_hg : Integrable g volume) (k : ℝ) :
    ‖∫ x, g x * realCharacter k x‖ ≤ ∫ x, ‖g x‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with x
  rw [norm_mul, norm_realCharacter, mul_one]

instance isFiniteMeasure_variation (mu : FiniteCMeasure) :
    IsFiniteMeasure mu.1.variation :=
  ⟨lt_top_iff_ne_top.2 mu.2⟩

lemma continuous_fsTransform (mu : FiniteCMeasure) : Continuous (fsTransform mu) := by
  unfold fsTransform
  refine VectorMeasure.continuous_of_dominated (bound := fun _ => 1) ?_ ?_ ?_ ?_
  · intro x
    exact (Continuous.aestronglyMeasurable (by fun_prop))
  · intro x
    filter_upwards with k
    simpa [realCharacter] using (norm_realCharacter k x).le
  · exact integrable_const 1
  · filter_upwards with k
    fun_prop

lemma norm_fsTransform_le (mu : FiniteCMeasure) (x : ℝ) :
    ‖fsTransform mu x‖ ≤ 1 * ‖cmul‖ * mu.1.variation.real univ := by
  unfold fsTransform
  apply VectorMeasure.norm_integral_le_of_norm_le_const
  filter_upwards with k
  simpa [realCharacter] using (norm_realCharacter k x).le

/-- Finite-complex-measure Fubini for the kernel `g(x)e^{-ikx}`. -/
theorem integral_mul_fsTransform_swap
    (mu : FiniteCMeasure) {g : ℝ → ℂ} (hg : Integrable g volume) :
    ∫ x : ℝ, g x * fsTransform mu x =
      ∫ᵛ k : ℝ, (∫ x : ℝ, g x * realCharacter k x) ∂[cmul; mu.1] := by
  let rho := finiteCMeasureOfDensity g hg
  -- Step 1: the outer Lebesgue integral is a vector integral against `g dx`.
  have h1 : ∫ x : ℝ, g x * fsTransform mu x =
      ∫ᵛ x : ℝ, fsTransform mu x ∂[cmul; rho.1] := by
    rw [vectorIntegral_density_eq hg (continuous_fsTransform mu).stronglyMeasurable
      (norm_fsTransform_le mu)]
    simp_rw [mul_comm]
  -- Step 2: the inner Lebesgue integral likewise.
  have h2 : ∀ k : ℝ, ∫ x : ℝ, g x * realCharacter k x =
      ∫ᵛ x : ℝ, realCharacter k x ∂[cmul; rho.1] := by
    intro k
    rw [vectorIntegral_density_eq hg (C := 1)
      (by unfold realCharacter; fun_prop : Continuous fun x => realCharacter k x).stronglyMeasurable
      (fun x => (norm_realCharacter k x).le)]
    simp_rw [mul_comm]
  -- Step 3: Fubini for the two finite complex measures.
  have hint : Integrable (Function.uncurry fun (x k : ℝ) => realCharacter k x)
      (rho.1.variation.prod mu.1.variation) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (continuous_realCharacter_uncurry.comp continuous_swap).aestronglyMeasurable
    · filter_upwards with p
      exact (norm_realCharacter _ _).le
  rw [h1]
  simp_rw [h2]
  unfold fsTransform
  exact VectorMeasure.integral_integral_swap (B := cmul) (C := cmul) (A := cmul) (D := cmul)
    hint (fun a b c => by simp [cmul]; ring)

/-- The same swap written with `halfLineCharacter` for a real frequency. -/
theorem integral_mul_fsTransform_swap_halfLine
    (mu : FiniteCMeasure) {g : ℝ → ℂ} (hg : Integrable g volume) :
    ∫ x : ℝ, g x * fsTransform mu x =
      ∫ᵛ k : ℝ,
        (∫ x : ℝ, g x * halfLineCharacter (k:ℂ) x) ∂[cmul; mu.1] := by
  simpa [realCharacter_eq_halfLineCharacter] using integral_mul_fsTransform_swap mu hg

end LCHSWiener
