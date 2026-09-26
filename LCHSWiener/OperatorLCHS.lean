import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import LCHSWiener.MatrixTarget
import LCHSWiener.DensityMeasure
import LCHSWiener.VectorMeasureFubini

noncomputable section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace LCHSWiener

/-!
# Operator-valued LCHS evolutions

Basic facts about `e^{-i(zX+Y)}` for `X ⪰ 0`, `Y = Y*`:

* it is a contraction for `Im z ≤ 0` (a unitary for real `z`);
* it is complex differentiable in `z`;

and two facts about integrating operator-valued functions against a complex
measure with the pairing `smulPairing`.
-/

/-! Shortcut instances: the generic search for these on
`EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)` is slow enough to hit
the recursion limit inside larger proofs. -/
instance instModuleOp (d : ℕ) : Module ℂ (Op d) := inferInstance
instance instNormedSpaceOp (d : ℕ) : NormedSpace ℂ (Op d) := inferInstance
instance instNormedAlgebraOp (d : ℕ) : NormedAlgebra ℂ (Op d) := inferInstance
instance instCompleteSpaceOp (d : ℕ) : CompleteSpace (Op d) := inferInstance
instance instAlgebraOp (d : ℕ) : Algebra ℂ (Op d) := inferInstance
instance instRingOp (d : ℕ) : Ring (Op d) := inferInstance
instance instContinuousSMulOp (d : ℕ) : ContinuousSMul ℂ (Op d) := inferInstance
instance instContinuousMulOp (d : ℕ) : ContinuousMul (Op d) := inferInstance
instance instTopAddGroupOp (d : ℕ) : IsTopologicalAddGroup (Op d) := inferInstance

/-- `e^{-i(zX+Y)}`. -/
def lchsEvol {d : ℕ} (X Y : Op d) (z : ℂ) : Op d :=
  NormedSpace.exp (-(Complex.I • (z • X + Y)))

lemma lchsEvol_neg_I {d : ℕ} (X Y : Op d) :
    lchsEvol X Y (-Complex.I) = NormedSpace.exp (-(X + Complex.I • Y)) := by
  unfold lchsEvol
  congr 1
  rw [smul_add, smul_smul]
  simp

/-- A dissipative operator generates a contraction. -/
theorem norm_exp_le_one_of_re_inner_nonpos {d : ℕ} {A : Op d}
    (hA : ∀ ξ : Hd d, (⟪ξ, A ξ⟫_ℂ).re ≤ 0) : ‖NormedSpace.exp A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => ?_
  let v : ℝ → Hd d := fun t => NormedSpace.exp (t • A) ξ
  have hv : ∀ t, HasDerivAt v (A (v t)) t := by
    intro t
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t
    let ev : Op d →L[ℝ] Hd d :=
      (ContinuousLinearMap.apply ℂ (Hd d) ξ).restrictScalars ℝ
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
      rw [(hφ t).deriv]
      have key : ⟪v t, A (v t)⟫_ℝ = (⟪v t, A (v t)⟫_ℂ).re := by
        simp only [PiLp.inner_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.inner, RCLike.inner_apply]
      rw [key]
      nlinarith [hA (v t)]
  have h01 := hanti (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [φ, v, one_smul] at h01
  rw [show ((0:ℝ) • A) = 0 from zero_smul ℝ A, NormedSpace.exp_zero,
    one_apply_eq_self] at h01
  rw [one_mul]
  nlinarith [norm_nonneg (NormedSpace.exp A ξ), norm_nonneg ξ]

/-- For a self-adjoint operator, `⟪ξ, T ξ⟫` is real. -/
lemma inner_self_apply_eq_re {d : ℕ} {T : Op d} (hT : IsSelfAdjoint T) (ξ : Hd d) :
    ⟪ξ, T ξ⟫_ℂ = ((⟪ξ, T ξ⟫_ℂ).re : ℂ) := by
  have hs := hT.isSymmetric
  have h1 : ⟪T ξ, ξ⟫_ℂ = ⟪ξ, T ξ⟫_ℂ := hs ξ ξ
  rw [← h1]
  exact (hs.coe_re_inner_apply_self ξ).symm

lemma re_inner_lchsGenerator_nonpos {d : ℕ} {X Y : Op d} (hX : X.IsPositive)
    (hY : IsSelfAdjoint Y) {z : ℂ} (hz : z.im ≤ 0) (ξ : Hd d) :
    (⟪ξ, (-(Complex.I • (z • X + Y))) ξ⟫_ℂ).re ≤ 0 := by
  have hXs : IsSelfAdjoint X := hX.isSelfAdjoint
  have hXr := inner_self_apply_eq_re hXs ξ
  have hYr := inner_self_apply_eq_re hY ξ
  have hXnn : 0 ≤ (⟪ξ, X ξ⟫_ℂ).re := by
    have := hX.2 ξ
    rw [ContinuousLinearMap.reApplyInnerSelf_apply] at this
    rw [← inner_conj_symm, RCLike.conj_re] at this
    exact this
  simp only [neg_apply, smul_apply, add_apply, inner_neg_right, inner_smul_right,
    inner_add_right]
  rw [hXr, hYr]
  simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  nlinarith

/-- `‖e^{-i(zX+Y)}‖ ≤ 1` for `Im z ≤ 0`. -/
theorem norm_lchsEvol_le_one {d : ℕ} {X Y : Op d} (hX : X.IsPositive) (hY : IsSelfAdjoint Y)
    {z : ℂ} (hz : z.im ≤ 0) : ‖lchsEvol X Y z‖ ≤ 1 :=
  norm_exp_le_one_of_re_inner_nonpos (re_inner_lchsGenerator_nonpos hX hY hz)

lemma norm_lchsEvol_real_le_one {d : ℕ} {X Y : Op d} (hX : X.IsPositive) (hY : IsSelfAdjoint Y)
    (k : ℝ) : ‖lchsEvol X Y k‖ ≤ 1 :=
  norm_lchsEvol_le_one hX hY (by simp)

/-- `z ↦ e^{-i(zX+Y)}` is entire. -/
theorem differentiable_lchsEvol {d : ℕ} (X Y : Op d) : Differentiable ℂ (lchsEvol X Y) := by
  intro z
  have hexp : DifferentiableAt ℂ NormedSpace.exp (-(Complex.I • (z • X + Y))) :=
    (NormedSpace.analyticAt_exp_of_mem_ball (𝕂 := ℂ) _
      (by rw [NormedSpace.expSeries_radius_eq_top]; simp)).differentiableAt
  have hlin : DifferentiableAt ℂ (fun w : ℂ => -(Complex.I • (w • X + Y))) z :=
    (((differentiable_id.smul_const X).add_const Y).const_smul Complex.I).neg z
  exact hexp.comp z hlin

lemma continuous_lchsEvol {d : ℕ} (X Y : Op d) : Continuous (lchsEvol X Y) :=
  (differentiable_lchsEvol X Y).continuous

lemma continuous_lchsEvol_real {d : ℕ} (X Y : Op d) :
    Continuous fun k : ℝ => lchsEvol X Y k :=
  (continuous_lchsEvol X Y).comp Complex.continuous_ofReal

lemma lchsIntegral_eq {d : ℕ} (μ : FiniteCMeasure) (X Y : Op d) :
    lchsIntegral μ X Y = ∫ᵛ k : ℝ, lchsEvol X Y k ∂[smulPairing (Op d); μ.1] := rfl

lemma lchsResidual_eq {d : ℕ} (μ : FiniteCMeasure) (X Y : Op d) :
    lchsResidual μ X Y = lchsEvol X Y (-Complex.I) -
      ∫ᵛ k : ℝ, lchsEvol X Y k ∂[smulPairing (Op d); μ.1] := by
  rw [lchsResidual, lchsEvol_neg_I, lchsIntegral_eq]

/-! ### Integrals with the pairing `smulPairing` -/

section Pairing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
@[simp] lemma smulPairing_apply (e : E) (c : ℂ) : smulPairing E e c = c • e := rfl

omit [CompleteSpace E] in
lemma norm_smulPairing_le : ‖smulPairing E‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun e => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun c => ?_
  simp [norm_smul, mul_comm]

omit [CompleteSpace E] in
/-- Norm bound for a vector integral with the pairing `smulPairing`. -/
lemma norm_vectorIntegral_smul_le (μ : FiniteCMeasure) {g : ℝ → E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ k ∂μ.1.variation, ‖g k‖ ≤ C) :
    ‖∫ᵛ k : ℝ, g k ∂[smulPairing E; μ.1]‖ ≤ C * tv μ := by
  refine (MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const h).trans ?_
  have hv : 0 ≤ μ.1.variation.real univ := measureReal_nonneg
  calc C * ‖smulPairing E‖ * μ.1.variation.real univ
      ≤ C * 1 * μ.1.variation.real univ := by
        gcongr
        exact norm_smulPairing_le
    _ = C * tv μ := by simp [tv, Measure.real]

/-- The simple-function case of `vectorIntegral_density_eq_smul`. -/
lemma vectorIntegral_density_simpleFunc_smul
    {f : ℝ → ℂ} (hf : Integrable f volume) (φ : SimpleFunc ℝ E) :
    (∫ᵛ x : ℝ, φ x ∂[smulPairing E; densityVectorMeasure f]) = ∫ x : ℝ, f x • φ x := by
  have : Fact (Integrable f volume) := ⟨hf⟩
  have hvar := variation_densityVectorMeasure hf
  have hint : ∀ ψ : SimpleFunc ℝ E, (densityVectorMeasure f).Integrable ψ := by
    intro ψ
    change Integrable ψ (densityVectorMeasure f).variation
    rw [hvar]
    exact SimpleFunc.integrable_of_isFiniteMeasure ψ
  have hint' : ∀ ψ : SimpleFunc ℝ E, Integrable (fun x => f x • ψ x) volume := by
    intro ψ
    obtain ⟨C, hC⟩ := ψ.exists_forall_norm_le
    exact hf.smul_bdd C ψ.aestronglyMeasurable (Eventually.of_forall hC)
  induction φ using SimpleFunc.induction with
  | const c hs =>
    rename_i s
    simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
    classical
    have hsfin : (densityVectorMeasure f).variation s ≠ ⊤ := by
      rw [hvar]; exact measure_ne_top _ _
    rw [show (Function.const ℝ (0 : E)) = 0 from rfl, Set.piecewise_eq_indicator,
      show Function.const ℝ c = fun _ => c from rfl,
      VectorMeasure.integral_eq_setToFun, setToFun_indicator_const _ hs hsfin c,
      transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply]
    have hfun : (fun x => f x • s.indicator (fun _ => c) x) =
        s.indicator (fun x => f x • c) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun, integral_indicator hs, densityVectorMeasure,
      MeasureTheory.withDensityᵥ_apply hf hs, integral_smul_const]
    simp
  | add hdisj hφ hψ =>
    rename_i φ ψ
    simp only [SimpleFunc.coe_add, Pi.add_apply, smul_add]
    rw [VectorMeasure.integral_fun_add (hint φ) (hint ψ), integral_add (hint' φ) (hint' ψ),
      hφ, hψ]

/-- Integrating a bounded measurable operator-valued function against a density
measure gives the Bochner integral of the product. -/
theorem vectorIntegral_density_eq_smul
    {f : ℝ → ℂ} (hf : Integrable f volume) {g : ℝ → E} (hg : StronglyMeasurable g)
    {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x : ℝ, g x ∂[smulPairing E; (finiteCMeasureOfDensity f hf).1]) =
      ∫ x : ℝ, f x • g x := by
  have : Fact (Integrable f volume) := ⟨hf⟩
  change (∫ᵛ x : ℝ, g x ∂[smulPairing E; densityVectorMeasure f]) = _
  have hvar := variation_densityVectorMeasure hf
  have hC : 0 ≤ C := (norm_nonneg _).trans (hgC 0)
  let F : ℕ → SimpleFunc ℝ E := hg.approxBounded C
  have hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x)) :=
    fun x => hg.tendsto_approxBounded_of_norm_le (hgC x)
  have hbd : ∀ n x, ‖F n x‖ ≤ C := fun n x => hg.norm_approxBounded_le hC n x
  have h1 : Tendsto (fun n => ∫ᵛ x : ℝ, F n x ∂[smulPairing E; densityVectorMeasure f])
      atTop (𝓝 (∫ᵛ x : ℝ, g x ∂[smulPairing E; densityVectorMeasure f])) := by
    refine VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (F n).aestronglyMeasurable) ?_
      (fun n => Eventually.of_forall (hbd n)) (Eventually.of_forall hlim)
    rw [hvar]
    exact integrable_const C
  have h2 : Tendsto (fun n => ∫ x : ℝ, f x • F n x) atTop (𝓝 (∫ x : ℝ, f x • g x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * C)
      (fun n => hf.aestronglyMeasurable.smul (F n).aestronglyMeasurable)
      (hf.norm.mul_const C) ?_ ?_
    · intro n
      refine Eventually.of_forall fun x => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hbd n x) (norm_nonneg _)
    · exact Eventually.of_forall fun x => tendsto_const_nhds.smul (hlim x)
  have heq : (fun n => ∫ᵛ x : ℝ, F n x ∂[smulPairing E; densityVectorMeasure f]) =
      fun n => ∫ x : ℝ, f x • F n x :=
    funext fun n => vectorIntegral_density_simpleFunc_smul hf (F n)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- The simple-function case of `clm_vectorIntegral_smul`. -/
lemma clm_vectorIntegral_smul_simpleFunc (μ : FiniteCMeasure) (L : E →L[ℂ] ℂ)
    (φ : SimpleFunc ℝ E) :
    L (∫ᵛ x : ℝ, φ x ∂[smulPairing E; μ.1]) = ∫ᵛ x : ℝ, L (φ x) ∂[cmul; μ.1] := by
  have hint : ∀ ψ : SimpleFunc ℝ E, μ.1.Integrable ψ :=
    fun ψ => SimpleFunc.integrable_of_isFiniteMeasure ψ
  have hint' : ∀ ψ : SimpleFunc ℝ E, μ.1.Integrable fun x => L (ψ x) :=
    fun ψ => SimpleFunc.integrable_of_isFiniteMeasure (ψ.map L)
  induction φ using SimpleFunc.induction with
  | const c hs =>
    rename_i s
    simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
    classical
    have hsfin : μ.1.variation s ≠ ⊤ := measure_ne_top _ _
    rw [show (Function.const ℝ (0 : E)) = 0 from rfl, Set.piecewise_eq_indicator,
      show Function.const ℝ c = fun _ => c from rfl,
      VectorMeasure.integral_eq_setToFun, setToFun_indicator_const _ hs hsfin c,
      transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply]
    have hfun : (fun x => L (s.indicator (fun _ => c) x)) = s.indicator (fun _ => L c) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun, VectorMeasure.integral_eq_setToFun, setToFun_indicator_const _ hs hsfin (L c),
      transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply]
    simp [cmul, mul_comm]
  | add hdisj hφ hψ =>
    rename_i φ ψ
    simp only [SimpleFunc.coe_add, Pi.add_apply, map_add]
    rw [VectorMeasure.integral_fun_add (hint φ) (hint ψ), map_add,
      VectorMeasure.integral_fun_add (hint' φ) (hint' ψ), hφ, hψ]

/-- A continuous linear functional commutes with the vector integral of a
bounded measurable function. -/
theorem clm_vectorIntegral_smul (μ : FiniteCMeasure) (L : E →L[ℂ] ℂ)
    {g : ℝ → E} (hg : StronglyMeasurable g) {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) :
    L (∫ᵛ x : ℝ, g x ∂[smulPairing E; μ.1]) = ∫ᵛ x : ℝ, L (g x) ∂[cmul; μ.1] := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hgC 0)
  let F : ℕ → SimpleFunc ℝ E := hg.approxBounded C
  have hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x)) :=
    fun x => hg.tendsto_approxBounded_of_norm_le (hgC x)
  have hbd : ∀ n x, ‖F n x‖ ≤ C := fun n x => hg.norm_approxBounded_le hC n x
  have h1 : Tendsto (fun n => L (∫ᵛ x : ℝ, F n x ∂[smulPairing E; μ.1]))
      atTop (𝓝 (L (∫ᵛ x : ℝ, g x ∂[smulPairing E; μ.1]))) := by
    refine (L.continuous.tendsto _).comp ?_
    exact VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (F n).aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall (hbd n)) (Eventually.of_forall hlim)
  have h2 : Tendsto (fun n => ∫ᵛ x : ℝ, L (F n x) ∂[cmul; μ.1])
      atTop (𝓝 (∫ᵛ x : ℝ, L (g x) ∂[cmul; μ.1])) := by
    refine VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => ‖L‖ * C)
      (fun n => (L.continuous.comp_aestronglyMeasurable (F n).aestronglyMeasurable))
      (integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (L.continuous.tendsto _).comp (hlim x))
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbd n x) (norm_nonneg _))
  have heq : (fun n => L (∫ᵛ x : ℝ, F n x ∂[smulPairing E; μ.1])) =
      fun n => ∫ᵛ x : ℝ, L (F n x) ∂[cmul; μ.1] :=
    funext fun n => clm_vectorIntegral_smul_simpleFunc μ L (F n)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end Pairing

end LCHSWiener
