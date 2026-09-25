import LCHSWiener.HalfPlanePoisson
import LCHSWiener.OperatorLCHS

noncomputable section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace LCHSWiener

/-!
# Matrix LCHS identities and the matrix upper bound

For `X ⪰ 0` and `Y = Y*` of any finite dimension:

* `∫ ρ(k) e^{-i(kX+Y)} dk = e^{-(X+iY)}` for the Cauchy density `ρ`;
* `∫ w_{R,C}(k) e^{-i(kX+Y)} dk = e^{-(X+iY)}` for the full boundary density
  `w_{R,C} = fullOuterDensity R C` of Section 3.3.

Both follow from the lower half-plane Poisson formula, the second one after
shifting the dual factor to `Φ_{R,-C}(z - is)` and letting `s → 0`.  Splitting
`w_{R,C}` into its parts on `|k| < R` and `|k| > R` then bounds the
worst-case matrix error of the truncated kernel by the `L¹` mass of the tail.
-/

variable {d : ℕ} {X Y : Op d}

/-- Matrix LCHS identity for the Cauchy kernel. -/
theorem integral_cauchy_lchsEvol (hX : X.IsPositive) (hY : IsSelfAdjoint Y) :
    ∫ k : ℝ, (cauchyDensity k : ℂ) • lchsEvol X Y k = lchsEvol X Y (-Complex.I) :=
  poisson_lowerHalfPlane (M := 1) (continuous_lchsEvol X Y).continuousOn
    (differentiable_lchsEvol X Y).differentiableOn
    (fun _ hz => norm_lchsEvol_le_one hX hY hz)

/-- The shifted dual factor times the evolution, for the Poisson formula. -/
lemma poisson_shifted_dual {R C s : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hs : 0 < s)
    (hX : X.IsPositive) (hY : IsSelfAdjoint Y) :
    ∫ k : ℝ, (cauchyDensity k : ℂ) •
        (dualPhiC R (-C) ((k:ℂ) - Complex.I * (s:ℂ)) • lchsEvol X Y k) =
      dualPhiC R (-C) (-Complex.I - Complex.I * (s:ℂ)) • lchsEvol X Y (-Complex.I) := by
  have hshift : ∀ z : ℂ, z.im ≤ 0 → z - Complex.I * (s:ℂ) ∈ lowerHalfPlane := by
    intro z hz
    show (z - Complex.I * (s:ℂ)).im < 0
    simp; linarith
  have hΦ : AnalyticOnNhd ℂ (dualPhiC R (-C)) lowerHalfPlane := analyticOnNhd_dualPhiC hR
  have hcont : ContinuousOn (fun z : ℂ => dualPhiC R (-C) (z - Complex.I * (s:ℂ)) •
      lchsEvol X Y z) {z : ℂ | z.im ≤ 0} := by
    refine ContinuousOn.fun_smul ?_ (continuous_lchsEvol X Y).continuousOn
    intro z hz
    have hsc : Continuous fun w : ℂ => w - Complex.I * (s:ℂ) := by fun_prop
    exact (ContinuousAt.comp (g := dualPhiC R (-C)) (f := fun w : ℂ => w - Complex.I * (s:ℂ))
      (hΦ _ (hshift z hz)).continuousAt hsc.continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => dualPhiC R (-C) (z - Complex.I * (s:ℂ)) •
      lchsEvol X Y z) {z : ℂ | z.im < 0} := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.fun_smul ?_
      (differentiable_lchsEvol X Y z))
    exact DifferentiableAt.comp (g := dualPhiC R (-C)) z
      (hΦ _ (hshift z (le_of_lt hz))).differentiableAt
      ((differentiable_id.sub_const (Complex.I * (s:ℂ))) z)
  have h := poisson_lowerHalfPlane (M := Real.exp (2 * (Real.pi * C))) hcont hdiff
    (fun z hz => by
      rw [norm_smul]
      calc ‖dualPhiC R (-C) (z - Complex.I * (s:ℂ))‖ * ‖lchsEvol X Y z‖
          ≤ Real.exp (2 * (Real.pi * C)) * 1 :=
            mul_le_mul (norm_dualPhiC_neg_le hC _) (norm_lchsEvol_le_one hX hY hz)
              (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (2 * (Real.pi * C)) := mul_one _)
  exact h

/-- Pointwise boundary limit of the shifted dual factor, away from `±R`. -/
lemma tendsto_dualPhiC_shift {R c k : ℝ} (hR : 0 < R) (hk : k ≠ R ∧ k ≠ -R)
    {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) (hu0 : ∀ n, 0 < u n) :
    Tendsto (fun n => dualPhiC R c ((k:ℂ) - Complex.I * (u n : ℂ))) atTop
      (𝓝 (dualPhiC R c (k:ℂ))) := by
  rcases lt_trichotomy |k| R with hlt | heq | hgt
  · have hz : Tendsto (fun n => (u n : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp hu
    have hzk : Tendsto (fun n => (k:ℂ) - Complex.I * (u n : ℂ)) atTop (𝓝 (k:ℂ)) := by
      simpa using (tendsto_const_nhds (x := (k:ℂ))).sub
        ((tendsto_const_nhds (x := Complex.I)).mul hz)
    exact (continuousAt_dualPhiC_real_inside (c := c) hlt).tendsto.comp hzk
  · exfalso
    rcases (abs_eq hR.le).1 heq with h | h
    · exact hk.1 h
    · exact hk.2 h
  · exact tendsto_dualPhiC_outside hR hgt hu hu0

/-- `outerConst R C * Φ_{R,-C}(-i) = 1`. -/
lemma outerConst_mul_dualPhiC_neg_I {R C : ℝ} (hR : 0 < R) :
    (outerConst R C : ℂ) * dualPhiC R (-C) (-Complex.I) = 1 := by
  rw [dualPhiC_neg_I hR, ← Complex.ofReal_mul]
  unfold outerConst dualA
  rw [show -Real.pi * -C = Real.pi * C by ring, ← Real.exp_mul, ← Real.exp_add,
    ← Real.exp_add]
  have hpq := pR_add_qR R
  rw [show Real.pi * C * qR R + -(Real.pi * C) + Real.pi * C * pR R = 0 by
    linear_combination (Real.pi * C) * hpq]
  simp

/-- Matrix LCHS identity for the full boundary density `w_{R,C}`. -/
theorem integral_fullOuterDensity_lchsEvol {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hX : X.IsPositive) (hY : IsSelfAdjoint Y) :
    ∫ k : ℝ, fullOuterDensity R C k • lchsEvol X Y k = lchsEvol X Y (-Complex.I) := by
  let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hu : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hu0 : ∀ n, 0 < u n := fun n => one_div_pos.mpr (by positivity)
  have hz : Tendsto (fun n => (u n : ℂ)) atTop (𝓝 ((0:ℝ):ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hu
  have hL : Tendsto (fun n => ∫ k : ℝ, (cauchyDensity k : ℂ) •
        (dualPhiC R (-C) ((k:ℂ) - Complex.I * (u n : ℂ)) • lchsEvol X Y k))
      atTop (𝓝 (∫ k : ℝ, (cauchyDensity k : ℂ) •
        (dualPhiC R (-C) (k:ℂ) • lchsEvol X Y k))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun k => cauchyDensity k * Real.exp (2 * (Real.pi * C))) (fun n => ?_)
      (integrable_cauchyDensity.mul_const _) (fun n => Eventually.of_forall fun k => ?_) ?_
    · refine (Continuous.aestronglyMeasurable ?_)
      exact (Complex.continuous_ofReal.comp continuous_cauchyDensity).fun_smul
        ((continuous_dualPhiC_shift hR (hu0 n)).fun_smul (continuous_lchsEvol_real X Y))
    · rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (cauchyDensity_nonneg k)]
      refine mul_le_mul_of_nonneg_left ?_ (cauchyDensity_nonneg k)
      calc ‖dualPhiC R (-C) ((k:ℂ) - Complex.I * (u n : ℂ))‖ * ‖lchsEvol X Y k‖
          ≤ Real.exp (2 * (Real.pi * C)) * 1 :=
            mul_le_mul (norm_dualPhiC_neg_le hC _) (norm_lchsEvol_real_le_one hX hY k)
              (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (2 * (Real.pi * C)) := mul_one _
    · have hae : ∀ᵐ k : ℝ ∂volume, k ∉ ({R, -R} : Set ℝ) :=
        (Set.toFinite _).countable.ae_notMem volume
      filter_upwards [hae] with k hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hk
      exact tendsto_const_nhds.smul ((tendsto_dualPhiC_shift hR hk hu hu0).smul
        tendsto_const_nhds)
  have hRt : Tendsto (fun n => dualPhiC R (-C) (-Complex.I - Complex.I * (u n : ℂ)) •
        lchsEvol X Y (-Complex.I))
      atTop (𝓝 (dualPhiC R (-C) (-Complex.I) • lchsEvol X Y (-Complex.I))) := by
    have harg : Tendsto (fun n => -Complex.I - Complex.I * (u n : ℂ)) atTop (𝓝 (-Complex.I)) := by
      simpa using (tendsto_const_nhds (x := -Complex.I)).sub
        ((tendsto_const_nhds (x := Complex.I)).mul hz)
    exact ((((analyticOnNhd_dualPhiC hR) (-Complex.I)
      neg_I_mem_lowerHalfPlane).continuousAt.tendsto.comp harg)).smul tendsto_const_nhds
  have hlim : ∫ k : ℝ, (cauchyDensity k : ℂ) • (dualPhiC R (-C) (k:ℂ) • lchsEvol X Y k) =
      dualPhiC R (-C) (-Complex.I) • lchsEvol X Y (-Complex.I) := by
    refine tendsto_nhds_unique hL (hRt.congr fun n => ?_)
    exact (poisson_shifted_dual hR hC (hu0 n) hX hY).symm
  have hfun : (fun k : ℝ => fullOuterDensity R C k • lchsEvol X Y k) =
      fun k : ℝ => (outerConst R C : ℂ) • ((cauchyDensity k : ℂ) •
        (dualPhiC R (-C) (k:ℂ) • lchsEvol X Y k)) := by
    funext k
    rw [fullOuterDensity, smul_smul, smul_smul, Complex.ofReal_mul]
  rw [hfun, integral_smul, hlim, smul_smul, outerConst_mul_dualPhiC_neg_I hR, one_smul]

/-! ### Bounds on the worst-case matrix error -/

lemma norm_lchsResidual_le (μ : FiniteCMeasure) (hX : X.IsPositive) (hY : IsSelfAdjoint Y) :
    ‖lchsResidual μ X Y‖ ≤ 1 + tv μ := by
  rw [lchsResidual_eq]
  refine (norm_sub_le _ _).trans (add_le_add (norm_lchsEvol_le_one hX hY (by simp)) ?_)
  simpa using norm_vectorIntegral_smul_le μ zero_le_one
    (Eventually.of_forall fun k => norm_lchsEvol_real_le_one hX hY k)

lemma zero_mem_matrixErrorSet (μ : FiniteCMeasure) :
    ∃ e, e ∈ matrixErrorSet μ :=
  ⟨_, 0, 0, 0, ContinuousLinearMap.isPositive_zero, IsSelfAdjoint.zero _, rfl⟩

lemma bddAbove_matrixErrorSet (μ : FiniteCMeasure) : BddAbove (matrixErrorSet μ) := by
  refine ⟨1 + tv μ, ?_⟩
  rintro e ⟨d, X, Y, hX, hY, rfl⟩
  exact norm_lchsResidual_le μ hX hY

lemma le_matrixError {μ : FiniteCMeasure} (hX : X.IsPositive) (hY : IsSelfAdjoint Y) :
    ‖lchsResidual μ X Y‖ ≤ matrixError μ :=
  le_csSup (bddAbove_matrixErrorSet μ) ⟨d, X, Y, hX, hY, rfl⟩

lemma matrixError_le {μ : FiniteCMeasure} {B : ℝ}
    (h : ∀ (d : ℕ) (X Y : Op d), X.IsPositive → IsSelfAdjoint Y → ‖lchsResidual μ X Y‖ ≤ B) :
    matrixError μ ≤ B := by
  refine csSup_le (zero_mem_matrixErrorSet μ) ?_
  rintro e ⟨d, X, Y, hX, hY, rfl⟩
  exact h d X Y hX hY

/-- If an integrable kernel `w = f + g` reproduces `e^{-(X+iY)}` for every
admissible `X, Y`, then the truncated measure `f dk` has worst-case matrix error
at most `‖g‖₁`. -/
theorem matrixError_density_le {f g w : ℝ → ℂ} (hf : Integrable f volume)
    (hg : Integrable g volume) (hsplit : w =ᵐ[volume] fun k => f k + g k)
    (hw : ∀ (d : ℕ) (X Y : Op d), X.IsPositive → IsSelfAdjoint Y →
      ∫ k : ℝ, w k • lchsEvol X Y k = lchsEvol X Y (-Complex.I)) :
    matrixError (finiteCMeasureOfDensity f hf) ≤ ∫ k, ‖g k‖ := by
  refine matrixError_le fun d X Y hX hY => ?_
  have hU := continuous_lchsEvol_real X Y
  have hUb : ∀ k : ℝ, ‖lchsEvol X Y k‖ ≤ 1 := norm_lchsEvol_real_le_one hX hY
  have hint : ∀ h : ℝ → ℂ, Integrable h volume →
      Integrable (fun k : ℝ => h k • lchsEvol X Y k) volume :=
    fun h hh => hh.smul_bdd 1 hU.aestronglyMeasurable (Eventually.of_forall hUb)
  have hw' : Integrable w volume := (hf.add hg).congr hsplit.symm
  rw [lchsResidual_eq, vectorIntegral_density_eq_smul hf hU.stronglyMeasurable hUb,
    ← hw d X Y hX hY, ← integral_sub (hint w hw') (hint f hf)]
  have hcongr : (fun k : ℝ => w k • lchsEvol X Y k - f k • lchsEvol X Y k) =ᵐ[volume]
      fun k : ℝ => g k • lchsEvol X Y k := by
    filter_upwards [hsplit] with k hk
    rw [hk, add_smul (f k) (g k) (lchsEvol X Y k)]
    abel
  rw [integral_congr_ae hcongr]
  refine (norm_integral_le_integral_norm _).trans (integral_mono (hint g hg).norm hg.norm ?_)
  intro k
  simp only [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hUb k)

/-! ### The two upper-bound witnesses -/

/-- High-mass witness: the truncated outer kernel. -/
theorem matrix_outer_kernel_witness {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) :
    ∃ mu : FiniteCMeasure, SupportedIn R mu ∧
      tv mu ≤ pR R * Real.exp (Real.pi*C*qR R) ∧
      matrixError mu ≤ qR R * Real.exp (-Real.pi*C*pR R) := by
  have hf : Integrable (innerOuterDensity R C) volume := integrable_innerOuterDensity hC
  have hg : Integrable (tailOuterDensity R C) volume := integrable_tailOuterDensity hC
  refine ⟨finiteCMeasureOfDensity _ hf, ?_, ?_, ?_⟩
  · apply supportedIn_finiteCMeasureOfDensity hf
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with k hk
    have hk' : k ∉ Set.Ioo (-R) R := fun h => hk (Set.Ioo_subset_Icc_self h)
    simp [innerOuterDensity, Set.indicator_of_notMem hk']
  · calc
      tv (finiteCMeasureOfDensity _ hf) ≤ ∫ k, ‖innerOuterDensity R C k‖ :=
        tv_finiteCMeasureOfDensity_le hf
      _ = pR R * Real.exp (Real.pi*C*qR R) := integral_norm_innerOuterDensity hR
  · rw [← integral_norm_tailOuterDensity (C := C) hR]
    exact matrixError_density_le hf hg fullOuterDensity_eq_inner_add_tail_ae
      fun d X Y hX hY => integral_fullOuterDensity_lchsEvol hR hC hX hY

/-- Low-mass witness: the Cauchy kernel with its inner part scaled by
`α = λ / p_R`. -/
theorem matrix_low_witness {R lam : ℝ} (hR : 0 < R) (hlam0 : 0 ≤ lam) (hlam : lam ≤ pR R) :
    ∃ mu : FiniteCMeasure, SupportedIn R mu ∧ tv mu ≤ lam ∧ matrixError mu ≤ 1 - lam := by
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
  refine ⟨finiteCMeasureOfDensity rhoIn hin, ?_, ?_, ?_⟩
  · apply supportedIn_finiteCMeasureOfDensity hin
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with k hk
    have hk' : k ∉ Set.Ioo (-R) R := fun h => hk (Set.Ioo_subset_Icc_self h)
    simp [rhoIn, inner, Set.indicator_of_notMem hk']
  · calc
      tv (finiteCMeasureOfDensity rhoIn hin) ≤ ∫ k, ‖rhoIn k‖ := tv_finiteCMeasureOfDensity_le hin
      _ = alpha * pR R := by
        simp only [rhoIn, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
        rw [integral_const_mul, hnormInner]
      _ = lam := by rw [halpha]; field_simp
  · refine (matrixError_density_le hin hout hsplit fun d X Y hX hY => ?_).trans ?_
    · exact integral_cauchy_lchsEvol hX hY
    · calc ∫ k, ‖rhoOut k‖ ≤ ∫ k, ((1-alpha) * ‖inner k‖ + ‖outer k‖) := by
            refine integral_mono hout.norm ((hinner.norm.const_mul _).add houter.norm)
              fun k => ?_
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

end LCHSWiener
