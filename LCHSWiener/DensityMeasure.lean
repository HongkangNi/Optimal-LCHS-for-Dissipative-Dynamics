import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
  (volume : Measure ℝ).withDensityᵥ f

/-- The positive measure with density `‖f‖`. -/
def normDensityMeasure (f : ℝ → ℂ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity (fun x => ‖f x‖ₑ)

lemma variation_densityVectorMeasure
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    (densityVectorMeasure f).variation = normDensityMeasure f := by
  exact MeasureTheory.Measure.variation_withDensityᵥ hf

lemma normDensityMeasure_univ_ne_top
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    normDensityMeasure f Set.univ ≠ ⊤ := by
  rw [normDensityMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using (hasFiniteIntegral_iff_enorm.mp hf.2).ne

/-- An integrable complex density gives a finite complex measure. -/
def finiteCMeasureOfDensity (f : ℝ → ℂ) (hf : Integrable f volume) : FiniteCMeasure :=
  ⟨densityVectorMeasure f, by
    rw [variation_densityVectorMeasure hf]
    exact normDensityMeasure_univ_ne_top hf⟩

/-- Total variation of a density measure is at most the L1 norm of the density. -/
theorem tv_finiteCMeasureOfDensity_le
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    tv (finiteCMeasureOfDensity f hf) ≤ ∫ x, ‖f x‖ := by
  unfold tv finiteCMeasureOfDensity
  rw [variation_densityVectorMeasure hf]
  have hfin : normDensityMeasure f Set.univ ≠ ⊤ := normDensityMeasure_univ_ne_top hf
  rw [normDensityMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]

/-- If an integrable density vanishes a.e. off `[-R,R]`, then the associated
finite complex measure is supported in that interval. -/
theorem supportedIn_finiteCMeasureOfDensity
    {R : ℝ} {f : ℝ → ℂ} (hf : Integrable f volume)
    (hsupp : f =ᵐ[volume.restrict ((Set.Icc (-R) R)ᶜ)] 0) :
    SupportedIn R (finiteCMeasureOfDensity f hf) := by
  unfold SupportedIn
  change (densityVectorMeasure f).variation ((Set.Icc (-R) R)ᶜ) = 0
  rw [variation_densityVectorMeasure hf, normDensityMeasure,
    MeasureTheory.withDensity_apply _ measurableSet_Icc.compl]
  exact lintegral_eq_zero_of_ae_eq_zero (hsupp.mono fun x hx => by simp [hx])

instance isFiniteMeasure_normDensityMeasure
    {f : ℝ → ℂ} [Fact (Integrable f volume)] :
    IsFiniteMeasure (normDensityMeasure f) :=
  ⟨lt_top_iff_ne_top.2 (normDensityMeasure_univ_ne_top (Fact.out))⟩

/-- Vector integration of a simple function against a density measure. -/
lemma vectorIntegral_density_simpleFunc
    {f : ℝ → ℂ} (hf : Integrable f volume) (φ : SimpleFunc ℝ ℂ) :
    (∫ᵛ x : ℝ, φ x ∂[cmul; densityVectorMeasure f]) = ∫ x : ℝ, φ x * f x := by
  have : Fact (Integrable f volume) := ⟨hf⟩
  have hvar := variation_densityVectorMeasure hf
  have hint : ∀ ψ : SimpleFunc ℝ ℂ, (densityVectorMeasure f).Integrable ψ := by
    intro ψ
    change Integrable ψ (densityVectorMeasure f).variation
    rw [hvar]
    exact SimpleFunc.integrable_of_isFiniteMeasure ψ
  have hint' : ∀ ψ : SimpleFunc ℝ ℂ, Integrable (fun x => ψ x * f x) volume := by
    intro ψ
    obtain ⟨C, hC⟩ := ψ.exists_forall_norm_le
    exact hf.bdd_mul ψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  induction φ using SimpleFunc.induction with
  | const c hs =>
    rename_i s
    simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
    classical
    have hsfin : (densityVectorMeasure f).variation s ≠ ⊤ := by
      rw [hvar]; exact measure_ne_top _ _
    rw [show (Function.const ℝ (0 : ℂ)) = 0 from rfl, Set.piecewise_eq_indicator,
      show Function.const ℝ c = fun _ => c from rfl,
      VectorMeasure.integral_eq_setToFun, setToFun_indicator_const _ hs hsfin c,
      transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply]
    have hfun : (fun x => s.indicator (fun _ => c) x * f x) =
        s.indicator (fun x => c * f x) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun, integral_indicator hs, densityVectorMeasure,
      MeasureTheory.withDensityᵥ_apply hf hs, integral_const_mul]
    simp [cmul]
  | add hdisj hφ hψ =>
    rename_i φ ψ
    simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
    rw [VectorMeasure.integral_fun_add (hint φ) (hint ψ), integral_add (hint' φ) (hint' ψ),
      hφ, hψ]

/-- Vector integration of a bounded measurable function against a density
measure reduces to the ordinary Bochner integral of the product. -/
theorem vectorIntegral_density_eq
    {f g : ℝ → ℂ} (hf : Integrable f volume)
    (hg : StronglyMeasurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x : ℝ, g x ∂[cmul; (finiteCMeasureOfDensity f hf).1]) =
      ∫ x : ℝ, g x * f x := by
  have : Fact (Integrable f volume) := ⟨hf⟩
  change (∫ᵛ x : ℝ, g x ∂[cmul; densityVectorMeasure f]) = _
  have hvar := variation_densityVectorMeasure hf
  have hC : 0 ≤ C := (norm_nonneg _).trans (hgC 0)
  let F : ℕ → SimpleFunc ℝ ℂ := hg.approxBounded C
  have hlim : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (g x)) :=
    fun x => hg.tendsto_approxBounded_of_norm_le (hgC x)
  have hbd : ∀ n x, ‖F n x‖ ≤ C := fun n x => hg.norm_approxBounded_le hC n x
  have h1 : Filter.Tendsto (fun n => ∫ᵛ x : ℝ, F n x ∂[cmul; densityVectorMeasure f])
      Filter.atTop (nhds (∫ᵛ x : ℝ, g x ∂[cmul; densityVectorMeasure f])) := by
    refine VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (F n).aestronglyMeasurable) ?_
      (fun n => Filter.Eventually.of_forall (hbd n)) (Filter.Eventually.of_forall hlim)
    rw [hvar]
    exact integrable_const C
  have h2 : Filter.Tendsto (fun n => ∫ x : ℝ, F n x * f x)
      Filter.atTop (nhds (∫ x : ℝ, g x * f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
      (fun n => ((F n).aestronglyMeasurable.mul hf.aestronglyMeasurable))
      (hf.norm.const_mul C) ?_ ?_
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbd n x) (norm_nonneg _)
    · exact Filter.Eventually.of_forall fun x => (hlim x).mul tendsto_const_nhds
  have heq : (fun n => ∫ᵛ x : ℝ, F n x ∂[cmul; densityVectorMeasure f]) =
      fun n => ∫ x : ℝ, F n x * f x :=
    funext fun n => vectorIntegral_density_simpleFunc hf (F n)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- Fourier--Stieltjes transform of a density measure. -/
theorem fsTransform_finiteCMeasureOfDensity
    {f : ℝ → ℂ} (hf : Integrable f volume) (x : ℝ)
    (_hfx : Integrable (fun k : ℝ =>
      Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) * f k) volume) :
    fsTransform (finiteCMeasureOfDensity f hf) x =
      ∫ k : ℝ, Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ)) * f k := by
  unfold fsTransform
  refine vectorIntegral_density_eq hf (C := 1) ?_ ?_
  · exact (by fun_prop : Continuous fun k : ℝ =>
      Complex.exp (-Complex.I * (k:ℂ) * (x:ℂ))).stronglyMeasurable
  · intro k
    rw [Complex.norm_exp]
    simp

end LCHSWiener
