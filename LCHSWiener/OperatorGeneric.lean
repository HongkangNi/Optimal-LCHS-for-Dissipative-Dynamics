import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import LCHSWiener.MatrixTarget

noncomputable section

open Set Filter
open scoped InnerProductSpace Topology

namespace LCHSWiener

/-!
# Generic operator lemmas for the finite clock construction

On an arbitrary complex Hilbert space `E`:

* a dissipative operator generates a contraction semigroup;
* a Duhamel estimate: if `ψ' = -i(Gψ + r)` with `-iG` dissipative, then
  `‖ψ(τ) - e^{-iτG} ψ(0)‖ ≤ τ sup ‖r‖`;

and a transport lemma moving a realization on any finite-dimensional complex
inner product space to `ℂ^d`.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A dissipative operator generates a contraction. -/
theorem norm_exp_le_one_of_dissipative {A : E →L[ℂ] E}
    (hA : ∀ ξ : E, (⟪ξ, A ξ⟫_ℂ).re ≤ 0) : ‖NormedSpace.exp A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
  let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  let v : ℝ → E := fun t => NormedSpace.exp (t • A) ξ
  have hv : ∀ t, HasDerivAt v (A (v t)) t := by
    intro t
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
    let ev : (E →L[ℂ] E) →L[ℝ] E := (ContinuousLinearMap.apply ℂ E ξ).restrictScalars ℝ
    have h2 := ev.hasFDerivAt.comp_hasDerivAt t h
    have hval : ev (A * NormedSpace.exp (t • A)) = A (v t) := rfl
    rw [hval] at h2
    exact h2
  let φ : ℝ → ℝ := fun t => ‖v t‖ ^ 2
  have hφ : ∀ t, HasDerivAt φ (2 * ⟪v t, A (v t)⟫_ℝ) t := fun t => (hv t).norm_sq
  have hanti : AntitoneOn φ (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hφ t).continuousAt.continuousWithinAt
    · exact fun t _ => (hφ t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hφ t).deriv, real_inner_eq_re_inner ℂ]
      have h := hA (v t)
      rw [show RCLike.re ⟪v t, A (v t)⟫_ℂ = (⟪v t, A (v t)⟫_ℂ).re from rfl]
      nlinarith
  have h01 := hanti (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [φ, v, one_smul] at h01
  rw [show ((0:ℝ) • A) = 0 from zero_smul ℝ A, NormedSpace.exp_zero, one_apply_eq_self] at h01
  rw [one_mul]
  nlinarith [norm_nonneg (NormedSpace.exp A ξ), norm_nonneg ξ]

/-- **Duhamel estimate.**  If `ψ' = -i (G ψ + r)` and `-iG` is dissipative, then
`‖ψ(τ) - e^{-iτG} ψ(0)‖ ≤ τ ρ` where `ρ` bounds `‖r‖` on `[0, τ]`. -/
theorem duhamel_bound {G : E →L[ℂ] E}
    (hdiss : ∀ ξ : E, (⟪ξ, (-(Complex.I • G)) ξ⟫_ℂ).re ≤ 0)
    {ψ r : ℝ → E} {τ ρ : ℝ} (hτ : 0 ≤ τ)
    (hψ : ∀ t ∈ Icc 0 τ, HasDerivAt ψ (-(Complex.I • (G (ψ t) + r t))) t)
    (hr : ∀ t ∈ Icc 0 τ, ‖r t‖ ≤ ρ) :
    ‖ψ τ - NormedSpace.exp ((τ : ℂ) • (-(Complex.I • G))) (ψ 0)‖ ≤ τ * ρ := by
  set A : E →L[ℂ] E := -(Complex.I • G) with hAdef
  let W : ℝ → E →L[ℂ] E := fun u => NormedSpace.exp ((u : ℂ) • A)
  have hW : ∀ u : ℝ, 0 ≤ u → ‖W u‖ ≤ 1 := by
    intro u hu
    refine norm_exp_le_one_of_dissipative fun ξ => ?_
    have : (⟪ξ, ((u : ℂ) • A) ξ⟫_ℂ) = (u : ℂ) * ⟪ξ, A ξ⟫_ℂ := by
      rw [smul_apply, inner_smul_right]
    rw [this, Complex.re_ofReal_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hu (hdiss ξ)
  let F : ℝ → E := fun t => W (τ - t) (ψ t)
  have hWu : ∀ u : ℝ, HasDerivAt W (A * W u) u := by
    intro u
    have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℂ) A (u : ℂ)
    have := h1.scomp u Complex.ofRealCLM.hasDerivAt
    simpa [Function.comp_def, W] using this
  have hWd : ∀ t : ℝ, HasDerivAt (fun t => W (τ - t)) (-(A * W (τ - t))) t := by
    intro t
    have h2 : HasDerivAt (fun t : ℝ => τ - t) (-1) t := (hasDerivAt_id t).const_sub τ
    have := (hWu (τ - t)).scomp t h2
    simpa [Function.comp_def] using this
  have hF : ∀ t ∈ Icc 0 τ, HasDerivAt F (W (τ - t) (-(Complex.I • r t))) t := by
    intro t ht
    let RS : (E →L[ℂ] E) →L[ℝ] (E →L[ℝ] E) := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
    have hWR : HasDerivAt (fun t => RS (W (τ - t))) (RS (-(A * W (τ - t)))) t :=
      RS.hasFDerivAt.comp_hasDerivAt t (hWd t)
    have hprod := hWR.clm_apply (hψ t ht)
    have hcomm : A * W (τ - t) = W (τ - t) * A := by
      simp only [W]
      exact ((Commute.refl A).smul_right ((τ - t : ℝ) : ℂ)).exp_right.eq
    refine hprod.congr_deriv ?_
    show (-(A * W (τ - t))) (ψ t) + W (τ - t) (-(Complex.I • (G (ψ t) + r t))) =
      W (τ - t) (-(Complex.I • r t))
    rw [hcomm]
    simp only [hAdef, neg_apply, smul_apply, mul_apply_eq_comp, map_neg, map_smul, map_add,
      smul_add]
    abel
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := F) (a := 0) (b := τ) (C := ρ)
    (fun t ht => (hF t ht).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Icc 0 τ := Ico_subset_Icc_self ht
      calc ‖W (τ - t) (-(Complex.I • r t))‖ ≤ ‖W (τ - t)‖ * ‖-(Complex.I • r t)‖ :=
            (W (τ - t)).le_opNorm _
        _ ≤ 1 * ‖r t‖ := by
            refine mul_le_mul (hW _ (by linarith [ht'.2])) ?_ (norm_nonneg _) zero_le_one
            rw [norm_neg, norm_smul, Complex.norm_I, one_mul]
        _ ≤ ρ := by rw [one_mul]; exact hr t ht')
    τ (right_mem_Icc.2 hτ)
  simp only [F, W, sub_self, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_apply_eq_self,
    sub_zero] at hbound
  rwa [mul_comm] at hbound

/-- For `X ⪰ 0`, `Y = Y*` and `Im z ≤ 0`, the operator `-i(zX + Y)` is dissipative. -/
lemma re_inner_neg_I_smul_nonpos {X Y : E →L[ℂ] E} (hX : X.IsPositive) (hY : IsSelfAdjoint Y)
    {z : ℂ} (hz : z.im ≤ 0) (ξ : E) :
    (⟪ξ, (-(Complex.I • (z • X + Y))) ξ⟫_ℂ).re ≤ 0 := by
  have hreal : ∀ {T : E →L[ℂ] E}, IsSelfAdjoint T → ⟪ξ, T ξ⟫_ℂ = ((⟪ξ, T ξ⟫_ℂ).re : ℂ) := by
    intro T hT
    have hs := hT.isSymmetric
    have h1 : ⟪T ξ, ξ⟫_ℂ = ⟪ξ, T ξ⟫_ℂ := hs ξ ξ
    rw [← h1]
    exact (hs.coe_re_inner_apply_self ξ).symm
  have hXr := hreal hX.isSelfAdjoint
  have hYr := hreal hY
  have hXnn : 0 ≤ (⟪ξ, X ξ⟫_ℂ).re := by
    have := hX.2 ξ
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at this
    rw [← inner_conj_symm, RCLike.conj_re] at this
    exact this
  simp only [neg_apply, smul_apply, add_apply, inner_neg_right, inner_smul_right, inner_add_right]
  rw [hXr, hYr]
  simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  nlinarith

/-! ### Transport to `ℂ^d` -/

variable [FiniteDimensional ℂ E]

/-- A realization on a finite-dimensional complex inner product space gives one on
`ℂ^d`. -/
theorem exists_hd_of_finiteDimensional (X Y : E →L[ℂ] E) (u v : E) (hX : X.IsPositive)
    (hY : IsSelfAdjoint Y) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ (d : ℕ) (X' Y' : Op d) (u' v' : Hd d), X'.IsPositive ∧ IsSelfAdjoint Y' ∧
      ‖u'‖ = 1 ∧ ‖v'‖ = 1 ∧ ∀ z : ℂ,
        ⟪v', NormedSpace.exp (-(Complex.I • (z • X' + Y'))) u'⟫_ℂ =
          ⟪v, NormedSpace.exp (-(Complex.I • (z • X + Y))) u⟫_ℂ := by
  let e := (stdOrthonormalBasis ℂ E).repr
  let c := e.conjStarAlgEquiv
  have hc_cont : Continuous c := LinearMap.continuous_of_finiteDimensional c.toAlgEquiv.toLinearMap
  refine ⟨Module.finrank ℂ E, c X, c Y, e u, e v, ?_, ?_, by simpa using hu, by simpa using hv,
    fun z => ?_⟩
  · refine ⟨fun x y => ?_, fun x => ?_⟩
    · show ⟪e (X (e.symm x)), y⟫_ℂ = ⟪x, e (X (e.symm y))⟫_ℂ
      conv_lhs => rw [← e.apply_symm_apply y, e.inner_map_map]
      conv_rhs => rw [← e.apply_symm_apply x, e.inner_map_map]
      exact hX.1 _ _
    · have := hX.2 (e.symm x)
      simp only [ContinuousLinearMap.reApplyInnerSelf_apply] at this ⊢
      show 0 ≤ RCLike.re ⟪e (X (e.symm x)), x⟫_ℂ
      conv_rhs => rw [← e.apply_symm_apply x, e.inner_map_map]
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact this
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    show ⟪e (Y (e.symm x)), y⟫_ℂ = ⟪x, e (Y (e.symm y))⟫_ℂ
    conv_lhs => rw [← e.apply_symm_apply y, e.inner_map_map]
    conv_rhs => rw [← e.apply_symm_apply x, e.inner_map_map]
    exact hY.isSymmetric _ _
  · have hmap : c (-(Complex.I • (z • X + Y))) = -(Complex.I • (z • c X + c Y)) := by
      simp [map_neg, map_smul, map_add]
    rw [← hmap, ← NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) c hc_cont _
      (by rw [NormedSpace.expSeries_radius_eq_top]; simp)]
    show ⟪e v, e (NormedSpace.exp (-(Complex.I • (z • X + Y))) (e.symm (e u)))⟫_ℂ = _
    rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]

end LCHSWiener
