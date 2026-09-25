import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LCHSWiener.MeasureFourier

noncomputable section

open Set MeasureTheory

namespace LCHSWiener

/-!
# Finite complex measures coming from L1 densities

The upper-bound construction uses absolutely continuous complex measures.
This file packages an integrable density `f : ℝ → ℂ` as a `FiniteCMeasure`
and records the only estimates needed later: support, total variation, and
Fourier--Stieltjes evaluation.
-/

/-- The complex vector measure with Lebesgue density `f`. -/
def densityVectorMeasure (f : ℝ → ℂ) : CMeasure :=
  volume.withDensityᵥ f

/-- The positive measure with density `‖f‖`. -/
def normDensityMeasure (f : ℝ → ℂ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal ‖f x‖)

lemma enorm_densityVectorMeasure_apply_le
    {f : ℝ → ℂ} (hf : Integrable f volume)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ‖densityVectorMeasure f s‖ₑ ≤ normDensityMeasure f s := by
  rw [densityVectorMeasure, MeasureTheory.withDensityᵥ_apply hf hs]
  rw [normDensityMeasure, MeasureTheory.withDensity_apply _ hs]
  calc
    ‖∫ x in s, f x‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ :=
      MeasureTheory.enorm_integral_le_lintegral_enorm
    _ = ∫⁻ x in s, ENNReal.ofReal ‖f x‖ := by
      apply lintegral_congr
      filter_upwards with x
      simp

lemma variation_densityVectorMeasure_le
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    (densityVectorMeasure f).variation ≤ normDensityMeasure f := by
  apply MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le
  intro s hs
  exact enorm_densityVectorMeasure_apply_le hf hs

lemma normDensityMeasure_univ_ne_top
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    normDensityMeasure f Set.univ ≠ ⊤ := by
  rw [normDensityMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simpa using hf.hasFiniteIntegral

/-- An integrable complex density gives a finite complex measure. -/
def finiteCMeasureOfDensity (f : ℝ → ℂ) (hf : Integrable f volume) : FiniteCMeasure :=
  ⟨densityVectorMeasure f, by
    intro htop
    have hle := measure_mono_null
      (variation_densityVectorMeasure_le hf)
      (normDensityMeasure_univ_ne_top hf)
    exact hle (by simpa [htop])⟩

/-- Total variation of a density measure is at most the L1 norm of the density. -/
theorem tv_finiteCMeasureOfDensity_le
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    tv (finiteCMeasureOfDensity f hf) ≤ ∫ x, ‖f x‖ := by
  unfold tv finiteCMeasureOfDensity
  have hle := variation_densityVectorMeasure_le hf
  have hu := hle Set.univ
  have hfin : normDensityMeasure f Set.univ ≠ ⊤ := normDensityMeasure_univ_ne_top hf
  have hto := ENNReal.toReal_le_toReal hu (by
    exact ne_top_of_le_ne_top hfin hu) hfin
  rw [normDensityMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ] at hto
  simpa [MeasureTheory.lintegral_norm_eq_integral_norm hf] using hto

/-- If an integrable density vanishes a.e. off `[-R,R]`, then the associated
finite complex measure is supported in that interval. -/
theorem supportedIn_finiteCMeasureOfDensity
    {R : ℝ} {f : ℝ → ℂ} (hf : Integrable f volume)
    (hsupp : f =ᵐ[volume.restrict ((Set.Icc (-R) R)ᶜ)] 0) :
    SupportedIn R (finiteCMeasureOfDensity f hf) := by
  unfold SupportedIn
  have hvar := variation_densityVectorMeasure_le hf
  apply le_antisymm
  · calc
      (densityVectorMeasure f).variation ((Set.Icc (-R) R)ᶜ)
          ≤ normDensityMeasure f ((Set.Icc (-R) R)ᶜ) := hvar _
      _ = 0 := by
        rw [normDensityMeasure, MeasureTheory.withDensity_apply _
          (MeasurableSet.Icc.compl)]
        apply lintegral_eq_zero
        filter_upwards [hsupp] with x hx
        simp [hx]
  · exact bot_le

/-- Vector integration against a density measure reduces to the ordinary
Bochner integral of the product. -/
theorem vectorIntegral_density_eq
    {f g : ℝ → ℂ} (hf : Integrable f volume)
    (hg : Integrable (fun x => g x * f x) volume) :
    (∫ᵛ x : ℝ, g x ∂[cmul; (finiteCMeasureOfDensity f hf).1]) =
      ∫ x : ℝ, g x * f x := by
  -- Both sides are continuous in `g`; it is enough to prove the statement on
  -- integrable simple functions.  Mathlib's vector integral construction is
  -- precisely the continuous extension used by `withDensityᵥ`.
  rw [finiteCMeasureOfDensity, densityVectorMeasure]
  exact MeasureTheory.VectorMeasure.integral_withDensityᵥ
    (μ := volume) (f := f) (g := g) (B := cmul) hf hg

/-- Fourier--Stieltjes transform of a density measure. -/
theorem fsTransform_finiteCMeasureOfDensity
    {f : ℝ → ℂ} (hf : Integrable f volume) (x : ℝ)
    (hfx : Integrable (fun k =>
      Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) * f k) volume) :
    fsTransform (finiteCMeasureOfDensity f hf) x =
      ∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) * f k := by
  unfold fsTransform
  exact vectorIntegral_density_eq hf hfx

end LCHSWiener
