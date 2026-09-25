import Mathlib
import LCHSWiener.MeasureFourier
import LCHSWiener.HalfLineKernel

noncomputable section

open Set MeasureTheory scoped BigOperators

namespace LCHSWiener

/-!
# A Fubini lemma for a finite complex measure

Mathlib's vector-measure integral is a continuous extension from integrable
simple functions.  The statement below is proved by the corresponding
`Integrable.induction`: indicator functions are immediate from
`VectorMeasure.integral_indicator₂`, addition is linear, and the closedness
step follows from the `L¹` norm estimate for the vector-measure integral.
This is exactly the amount of vector-measure Fubini needed in Section 3.2.
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

/-- The Fourier integral of an `L¹` function is uniformly bounded by its
`L¹` norm. -/
theorem norm_integral_mul_realCharacter_le
    {g : ℝ → ℂ} (hg : Integrable g volume) (k : ℝ) :
    ‖∫ x, g x * realCharacter k x‖ ≤ ∫ x, ‖g x‖ := by
  calc
    ‖∫ x, g x * realCharacter k x‖
        ≤ ∫ x, ‖g x * realCharacter k x‖ := norm_integral_le_of_norm_le (by
            exact (hg.mul_const _).norm)
    _ = ∫ x, ‖g x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [norm_mul, norm_realCharacter]

/-- Finite-complex-measure Fubini for the kernel `g(x)e^{-ikx}`. -/
theorem integral_mul_fsTransform_swap
    (mu : FiniteCMeasure) {g : ℝ → ℂ} (hg : Integrable g volume) :
    ∫ x : ℝ, g x * fsTransform mu x =
      ∫ᵛ k : ℝ, (∫ x : ℝ, g x * realCharacter k x) ∂[cmul; mu.1] := by
  classical
  let P : (ℝ → ℂ) → Prop := fun f =>
    (∫ x : ℝ, f x * fsTransform mu x) =
      ∫ᵛ k : ℝ, (∫ x : ℝ, f x * realCharacter k x) ∂[cmul; mu.1]
  apply MeasureTheory.Integrable.induction P
  · intro c s hs hsf
    -- Indicator functions reduce to the defining set integral, after which
    -- the two integrations are interchanged by the ordinary finite-measure
    -- Fubini theorem on `s × variation(mu)`.
    simp only [P]
    have hchar : ∀ k : ℝ, IntegrableOn (fun x : ℝ => c * realCharacter k x) s volume := by
      intro k
      exact (integrableOn_const.2 hsf.ne).mul_const _
    rw [integral_indicator hs]
    have hprod : Integrable
        (fun p : ℝ × ℝ =>
          ((s.indicator (fun _ : ℝ => c)) p.1) * realCharacter p.2 p.1)
        (volume.prod mu.1.variation) := by
      apply Integrable.mono'
        ((integrable_indicator_iff hs).2 (integrableOn_const.2 hsf.ne)).norm.prod_mul
        (by fun_prop)
      filter_upwards with p
      simp [norm_mul, norm_realCharacter]
    -- `setToFun` defining the vector integral agrees with its value on
    -- indicators; continuity then lets ordinary Fubini perform the swap.
    simpa [fsTransform, realCharacter, cmul, mul_assoc] using
      MeasureTheory.VectorMeasure.integral_indicator₂
        (fun _ : ℂ => fun k : ℝ => realCharacter k) s c
  · intro f g hdisj hf hg hPf hPg
    simp only [P] at hPf hPg ⊢
    rw [integral_add hf.mul_const hg.mul_const]
    rw [← hPf, ← hPg]
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (hf.mul_const _) (hg.mul_const _)]
  · -- Closedness in L¹.  Both sides are bounded linear functionals with
    -- operator norm at most `tv mu`.
    have hleft : Continuous fun (F : Lp ℂ 1 volume) =>
        ∫ x : ℝ, (F x) * fsTransform mu x := by
      apply continuous_of_linear_of_bound
      · intro f g; simp [add_mul, integral_add]
      · intro a f; simp [smul_mul_assoc, integral_smul]
      · refine ⟨tv mu, ?_⟩
        intro f
        have hfs : ∀ x : ℝ, ‖fsTransform mu x‖ ≤ tv mu := by
          intro x
          unfold fsTransform tv
          have h := MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
            (μ := mu.1) (B := cmul) (C := 1) (by
              filter_upwards with k
              simp [realCharacter, cmul])
          simpa [cmul] using h
        calc
          ‖∫ x : ℝ, (f x) * fsTransform mu x‖
              ≤ ∫ x : ℝ, ‖f x‖ * tv mu := by
                apply norm_integral_le_of_norm_le
                filter_upwards with x
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left (hfs x) (norm_nonneg _)
          _ = tv mu * ‖f‖ := by
                simp [Lp.norm_def, mul_comm]
    have hright : Continuous fun (F : Lp ℂ 1 volume) =>
        ∫ᵛ k : ℝ, (∫ x : ℝ, (F x) * realCharacter k x) ∂[cmul; mu.1] := by
      apply continuous_of_linear_of_bound
      · intro f g; simp [add_mul, integral_add, MeasureTheory.VectorMeasure.integral_fun_add]
      · intro a f; simp [smul_mul_assoc, integral_smul, MeasureTheory.VectorMeasure.integral_fun_smul]
      · refine ⟨tv mu, ?_⟩
        intro f
        have hk : ∀ k : ℝ,
            ‖∫ x : ℝ, (f x) * realCharacter k x‖ ≤ ‖f‖ := by
          intro k
          simpa [Lp.norm_def] using norm_integral_mul_realCharacter_le (Lp.integrable_coeFn f) k
        have hv := MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
          (μ := mu.1) (B := cmul) (C := ‖f‖) (by
            filter_upwards with k
            exact hk k)
        simpa [tv, cmul] using hv
    exact isClosed_eq hleft hright
  · intro f g hfg hf hPf
    simp only [P] at hPf ⊢
    have hleft : (fun x => g x * fsTransform mu x) =ᵐ[volume]
        (fun x => f x * fsTransform mu x) := hfg.fun_comp fun z => z * fsTransform mu _
    rw [integral_congr_ae hleft]
    have hfourier : ∀ k : ℝ,
        (∫ x, g x * realCharacter k x) =
        ∫ x, f x * realCharacter k x := by
      intro k
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      simp [hx]
    simp_rw [hfourier]
    exact hPf
  · exact hg

/-- The same swap written with `halfLineCharacter` for a real frequency. -/
theorem integral_mul_fsTransform_swap_halfLine
    (mu : FiniteCMeasure) {g : ℝ → ℂ} (hg : Integrable g volume) :
    ∫ x : ℝ, g x * fsTransform mu x =
      ∫ᵛ k : ℝ,
        (∫ x : ℝ, g x * halfLineCharacter (k:ℂ) x) ∂[cmul; mu.1] := by
  simpa [realCharacter_eq_halfLineCharacter] using integral_mul_fsTransform_swap mu hg

end LCHSWiener
