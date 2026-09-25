import LCHSWiener.MatrixLCHS

noncomputable section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace LCHSWiener

/-!
# The matrix lower bound, assuming the realization lemma

From `RealizationLemma` we derive the dual inequality (3.7) of the note,

  𝓔(μ) ≥ |Φ(-i) - ∫ Φ dμ|,

and, with the dual functions `Φ = Φ_{r,c}`, `r > R`, the sharp lower bounds of
Section 3.1.
-/

/-- The dual inequality (3.7), assuming the realization lemma. -/
theorem dual_le_matrixError (hreal : RealizationLemma) {Φ : ℂ → ℂ} {K : Set ℝ}
    (hK : IsCompact K) (hΦ : AnalyticOnNhd ℂ Φ {z : ℂ | z.im < 0})
    (hKan : ∀ k ∈ K, AnalyticAt ℂ Φ (k:ℂ)) (hbd : ∀ z : ℂ, z.im < 0 → ‖Φ z‖ ≤ 1)
    (μ : FiniteCMeasure) (hμK : ∀ᵐ k ∂μ.1.variation, k ∈ K)
    (hint : μ.1.Integrable fun k : ℝ => Φ k) :
    ‖Φ (-Complex.I) - ∫ᵛ k : ℝ, Φ k ∂[cmul; μ.1]‖ ≤ matrixError μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have htv : 0 ≤ tv μ := ENNReal.toReal_nonneg
  set δ := ε / (1 + tv μ) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨d, X, Y, u, v, hX, hY, hu, hv, hKδ, hIδ⟩ := hreal Φ K hK hΦ hKan hbd δ hδ
  let L : Op d →L[ℂ] ℂ := (innerSL ℂ v).comp (ContinuousLinearMap.apply ℂ (Hd d) u)
  have hLapp : ∀ T : Op d, L T = ⟪v, T u⟫_ℂ := fun T => rfl
  have hU := continuous_lchsEvol_real X Y
  have hUb : ∀ k : ℝ, ‖lchsEvol X Y k‖ ≤ 1 := norm_lchsEvol_real_le_one hX hY
  -- the matrix element of the residual
  have hres : L (lchsResidual μ X Y) =
      ⟪v, lchsEvol X Y (-Complex.I) u⟫_ℂ - ∫ᵛ k : ℝ, ⟪v, lchsEvol X Y k u⟫_ℂ ∂[cmul; μ.1] := by
    rw [lchsResidual_eq, map_sub, clm_vectorIntegral_smul μ L hU.stronglyMeasurable hUb]
    rfl
  have hLres : ‖L (lchsResidual μ X Y)‖ ≤ matrixError μ := by
    refine le_trans ?_ (le_matrixError hX hY)
    rw [hLapp]
    calc ‖⟪v, lchsResidual μ X Y u⟫_ℂ‖ ≤ ‖v‖ * ‖lchsResidual μ X Y u‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖lchsResidual μ X Y‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖lchsResidual μ X Y‖ := by rw [hu, hv]; ring
  -- the matrix elements approximate `Φ` on `K`
  let m : ℝ → ℂ := fun k => ⟪v, lchsEvol X Y k u⟫_ℂ
  have hm_int : μ.1.Integrable m := by
    refine Integrable.mono' (integrable_const (1:ℝ)) ?_ (Eventually.of_forall fun k => ?_)
    · exact (L.continuous.comp hU).aestronglyMeasurable
    · calc ‖m k‖ = ‖L (lchsEvol X Y k)‖ := rfl
        _ ≤ ‖L‖ * ‖lchsEvol X Y k‖ := L.le_opNorm _
        _ ≤ 1 * 1 := by
            refine mul_le_mul ?_ (hUb k) (norm_nonneg _) zero_le_one
            refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
            rw [hLapp, one_mul]
            calc ‖⟪v, T u⟫_ℂ‖ ≤ ‖v‖ * ‖T u‖ := norm_inner_le_norm _ _
              _ ≤ ‖v‖ * (‖T‖ * ‖u‖) :=
                  mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
              _ = ‖T‖ := by rw [hu, hv]; ring
        _ = 1 := one_mul 1
  have hdiff : ‖∫ᵛ k : ℝ, (m k - Φ k) ∂[cmul; μ.1]‖ ≤ δ * tv μ := by
    refine norm_vectorIntegral_le_mul_tv μ hδ.le ?_
    filter_upwards [hμK] with k hk
    have := hKδ k hk
    rw [lchsEvol] at *
    exact this.le
  have hsplit : Φ (-Complex.I) - ∫ᵛ k : ℝ, Φ k ∂[cmul; μ.1] =
      -(⟪v, lchsEvol X Y (-Complex.I) u⟫_ℂ - Φ (-Complex.I)) + L (lchsResidual μ X Y) +
        ∫ᵛ k : ℝ, (m k - Φ k) ∂[cmul; μ.1] := by
    rw [hres, VectorMeasure.integral_fun_sub hm_int hint]
    ring
  have hI : ‖⟪v, lchsEvol X Y (-Complex.I) u⟫_ℂ - Φ (-Complex.I)‖ ≤ δ := by
    rw [lchsEvol_neg_I]
    exact hIδ.le
  rw [hsplit]
  calc ‖-(⟪v, lchsEvol X Y (-Complex.I) u⟫_ℂ - Φ (-Complex.I)) + L (lchsResidual μ X Y) +
          ∫ᵛ k : ℝ, (m k - Φ k) ∂[cmul; μ.1]‖
      ≤ δ + matrixError μ + δ * tv μ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (by rw [norm_neg]; exact hI) hLres)) hdiff)
    _ = matrixError μ + δ * (1 + tv μ) := by ring
    _ = matrixError μ + ε := by
        rw [hδdef, div_mul_cancel₀ _ (by linarith : (1 + tv μ) ≠ 0)]

/-- Integrability of the dual function against a measure supported in
`[-R,R]`, `R < r`. -/
lemma integrable_dualPhiC_of_supportedIn {R r c : ℝ} (hRr : R < r) {μ : FiniteCMeasure}
    (hsupp : SupportedIn R μ) : μ.1.Integrable fun k : ℝ => dualPhiC r c k := by
  refine Integrable.mono' (integrable_const (dualA c)) (measurable_dualPhiC_real r c).aestronglyMeasurable ?_
  filter_upwards [ae_mem_Icc_of_supportedIn hsupp] with k hk
  have habs : |k| < r := by
    rw [abs_lt]
    constructor <;> linarith [hk.1, hk.2]
  rw [norm_dualPhiC_real_inside habs]

/-- Sharp matrix lower bound for a fixed dual parameter `c`. -/
theorem matrix_lower_of_c (hreal : RealizationLemma) {R lam c : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    {μ : FiniteCMeasure} (hsupp : SupportedIn R μ) (htv : tv μ ≤ lam) :
    (dualA c)^(pR R) - dualA c * lam ≤ matrixError μ := by
  have hfor : ∀ r, R < r → (dualA c)^(pR r) - dualA c * tv μ ≤ matrixError μ := by
    intro r hRr
    have hr : 0 < r := lt_trans hR hRr
    have hgap := dual_le_matrixError hreal (Φ := dualPhiC r c) (K := Set.Icc (-R) R)
      isCompact_Icc (analyticOnNhd_dualPhiC hr)
      (fun k hk => analyticAt_dualPhiC_on_smaller_closed_interval hRr
        (abs_le.2 ⟨hk.1, hk.2⟩))
      (fun z hz => norm_dualPhiC_le_one hr hc hz) μ (ae_mem_Icc_of_supportedIn hsupp)
      (integrable_dualPhiC_of_supportedIn hRr hsupp)
    have hmu := norm_integral_dual_le_dualA_mul_tv (c := c) hR hRr hsupp
    have hphi : ‖dualPhiC r c (-Complex.I)‖ = (dualA c)^(pR r) := by
      rw [dualPhiC_neg_I hr]
      simpa using Real.rpow_nonneg (dualA_pos c).le _
    calc (dualA c)^(pR r) - dualA c * tv μ
        ≤ ‖dualPhiC r c (-Complex.I)‖ - ‖∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul; μ.1]‖ := by
          rw [hphi]; linarith
      _ ≤ ‖dualPhiC r c (-Complex.I) - ∫ᵛ k : ℝ, dualPhiC r c (k:ℂ) ∂[cmul; μ.1]‖ :=
          norm_sub_norm_le _ _
      _ ≤ matrixError μ := hgap
  have hlim : Tendsto (fun n : ℕ => (dualA c)^(pR (R + 1/(n+1:ℝ))) - dualA c * tv μ) atTop
      (𝓝 ((dualA c)^(pR R) - dualA c * tv μ)) := by
    apply Tendsto.sub_const
    have hcont : Continuous fun r : ℝ => (dualA c)^(pR r) :=
      continuous_const.rpow pR_continuous fun _ => Or.inl (dualA_pos c).ne'
    have harg : Tendsto (fun n : ℕ => R + 1/(n+1:ℝ)) atTop (𝓝 R) := by
      simpa using (tendsto_const_nhds (x := R)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact (hcont.tendsto R).comp harg
  have hle : ∀ n : ℕ, (dualA c)^(pR (R+1/(n+1:ℝ))) - dualA c * tv μ ≤ matrixError μ := by
    intro n
    have : 0 < 1/(n+1:ℝ) := one_div_pos.mpr (by positivity)
    exact hfor _ (by linarith)
  have := le_of_tendsto hlim (Eventually.of_forall hle)
  have : dualA c * tv μ ≤ dualA c * lam := mul_le_mul_of_nonneg_left htv (dualA_pos c).le
  linarith

/-- The basic dual inequality `(3.8)` in the matrix model. -/
theorem matrix_lower_of_a (hreal : RealizationLemma) {R lam a : ℝ} (hR : 0 < R)
    (ha0 : 0 < a) (ha1 : a ≤ 1) {μ : FiniteCMeasure} (hsupp : SupportedIn R μ)
    (htv : tv μ ≤ lam) :
    a^(pR R) - a*lam ≤ matrixError μ := by
  have h := matrix_lower_of_c hreal hR (cOfA_nonneg ha0 ha1) hsupp htv
  simpa [dualA_cOfA ha0] using h

/-- Low-`λ` branch of the matrix lower bound. -/
theorem matrix_lower_low (hreal : RealizationLemma) {R lam e : ℝ} (hR : 0 < R)
    (he : e ∈ matrixCosts R lam) : 1 - lam ≤ e := by
  rcases he with ⟨μ, hsupp, htv, rfl⟩
  simpa using matrix_lower_of_a hreal hR (a := 1) zero_lt_one le_rfl hsupp htv

/-- High-`λ` branch of the matrix lower bound. -/
theorem matrix_lower_high (hreal : RealizationLemma) {R lam e : ℝ} (hR : 0 < R)
    (hlam : pR R ≤ lam) (he : e ∈ matrixCosts R lam) :
    qR R * (pR R / lam)^(pR R / qR R) ≤ e := by
  rcases he with ⟨μ, hsupp, htv, rfl⟩
  have hp := pR_pos hR
  have hq := qR_pos hR
  have halg := high_test_point (p := pR R) (q := qR R) (lam := lam) hp hq (pR_add_qR R) hlam
  dsimp only at halg
  obtain ⟨ha0, ha1, heq⟩ := halg
  have h := matrix_lower_of_a hreal hR ha0 ha1 hsupp htv
  rwa [heq] at h

end LCHSWiener
