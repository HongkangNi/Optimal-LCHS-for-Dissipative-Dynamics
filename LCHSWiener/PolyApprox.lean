import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Algebra.Polynomial.Eval.Defs
import LCHSWiener.MatrixTarget

noncomputable section

open Set Filter Metric
open scoped Topology

namespace LCHSWiener

/-!
# Section 4.1: approximation by Schur polynomials

Let `Φ` be analytic and bounded by `1` on the lower half-plane and analytic at
every point of a compact `K ⊂ ℝ`.  With `Z = K ∪ {-i}` we find `h > 0` and a
polynomial `P` with `|P| ≤ 1` on the closed unit disc such that
`|P(e^{-ihz}) - Φ(z)| < δ` for all `z ∈ Z`.

The map `T_h(w) = -(2i/h)(1-w)/(1+w)` sends the unit disc to the lower
half-plane and satisfies `T_h(e^{-ihz}) = (2/h) tan(hz/2) → z` as `h → 0`.
The polynomial is a normalized Taylor truncation of `w ↦ Φ(T_h(ρw))`, `ρ < 1`.
-/

/-- The map `T_h(w) = -(2i/h)(1-w)/(1+w)` from the unit disc to the lower
half-plane. -/
def diskToLower (h : ℝ) (w : ℂ) : ℂ := -(2 * Complex.I / h) * ((1 - w) / (1 + w))

lemma diskToLower_im (h : ℝ) (w : ℂ) :
    (diskToLower h w).im = -(2 / h) * ((1 - Complex.normSq w) / Complex.normSq (1 + w)) := by
  rw [diskToLower, Complex.mul_im, Complex.div_re, Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
  norm_num
  ring_nf
  all_goals simp

lemma one_add_ne_zero_of_norm_lt_one {v : ℂ} (hv : ‖v‖ < 1) : 1 + v ≠ 0 := by
  intro h
  have : v = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at hv
  exact lt_irrefl _ hv

/-- `T_h` maps the open unit disc into the open lower half-plane. -/
lemma diskToLower_im_neg {h : ℝ} (hh : 0 < h) {v : ℂ} (hv : ‖v‖ < 1) :
    (diskToLower h v).im < 0 := by
  rw [diskToLower_im]
  have h1 : Complex.normSq v < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg v]
  have h2 : 0 < Complex.normSq (1 + v) := Complex.normSq_pos.2 (one_add_ne_zero_of_norm_lt_one hv)
  have h3 : 0 < (1 - Complex.normSq v) / Complex.normSq (1 + v) := div_pos (by linarith) h2
  have h4 : 0 < 2 / h := by positivity
  nlinarith

lemma differentiableAt_diskToLower (h : ℝ) {v : ℂ} (hv : 1 + v ≠ 0) :
    DifferentiableAt ℂ (diskToLower h) v := by
  unfold diskToLower
  exact (differentiableAt_const _).mul (((differentiableAt_const _).sub differentiableAt_id).div
    ((differentiableAt_const _).add differentiableAt_id) hv)

lemma continuousAt_diskToLower (h : ℝ) {v : ℂ} (hv : 1 + v ≠ 0) :
    ContinuousAt (diskToLower h) v :=
  (differentiableAt_diskToLower h hv).continuousAt

/-- `τ(h,z) = z · (tan u / u)` with `u = hz/2`, written with `dslope` so that it is
defined (and continuous) at `u = 0`. -/
def tanRatio (u : ℂ) : ℂ := dslope Complex.tan 0 u

lemma one_add_exp_ne_zero {u : ℂ} (hu : Complex.cos u ≠ 0) :
    1 + Complex.exp (-(2 * u) * Complex.I) ≠ 0 := by
  have hb : Complex.exp (-u * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hfac : 1 + Complex.exp (-(2 * u) * Complex.I) =
      2 * Complex.exp (-u * Complex.I) * Complex.cos u := by
    rw [Complex.cos, show -(2 * u) * Complex.I = -u * Complex.I + -u * Complex.I by ring,
      Complex.exp_add]
    have hab : Complex.exp (u * Complex.I) * Complex.exp (-u * Complex.I) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    linear_combination (-1:ℂ) * hab
  rw [hfac]
  exact mul_ne_zero (mul_ne_zero two_ne_zero hb) hu

/-- The exact identity `T_h(e^{-ihz}) = z · tanRatio(hz/2)` when `cos(hz/2) ≠ 0`. -/
lemma diskToLower_exp {h : ℝ} (hh : 0 < h) {z : ℂ} (hcos : Complex.cos (h * z / 2) ≠ 0) :
    diskToLower h (Complex.exp (-Complex.I * h * z)) = z * tanRatio (h * z / 2) := by
  set u : ℂ := h * z / 2 with hu
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh.ne'
  have hexp : Complex.exp (-Complex.I * h * z) = Complex.exp (-(2 * u) * Complex.I) := by
    rw [hu]; ring_nf
  have hden := one_add_exp_ne_zero hcos
  -- `(1 - e^{-2iu}) / (1 + e^{-2iu}) = i tan u`
  have hkey : (1 - Complex.exp (-(2 * u) * Complex.I)) / (1 + Complex.exp (-(2 * u) * Complex.I)) =
      Complex.I * Complex.tan u := by
    set a := Complex.exp (u * Complex.I) with ha
    set b := Complex.exp (-u * Complex.I) with hb
    have hab : a * b = 1 := by
      rw [ha, hb, ← Complex.exp_add]; ring_nf; simp
    have hb0 : b ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp (-(2 * u) * Complex.I) = b ^ 2 := by
      rw [hb, ← Complex.exp_nat_mul]; ring_nf
    have hapb : a + b ≠ 0 := by
      intro h0; apply hcos; rw [Complex.cos, ← ha, ← hb, h0, zero_div]
    have hn : 1 - b ^ 2 = b * (a - b) := by linear_combination (-1:ℂ) * hab
    have hd : 1 + b ^ 2 = b * (a + b) := by linear_combination (-1:ℂ) * hab
    rw [h2, hn, hd, mul_div_mul_left _ _ hb0, Complex.tan_eq_sin_div_cos, Complex.sin,
      Complex.cos]
    have hs : Complex.exp (-u * Complex.I) = b := rfl
    simp only [neg_mul] at hs ⊢
    rw [hs, ← ha]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexp, diskToLower, hkey]
  by_cases hu0 : u = 0
  · have hz : z = 0 := by
      rw [hu] at hu0
      have : (h : ℂ) * z = 0 := by linear_combination 2 * hu0
      exact (mul_eq_zero.1 this).resolve_left hh0
    simp [hz, hu0]
  · rw [tanRatio, dslope_of_ne _ hu0, slope_def_field, Complex.tan_zero, sub_zero, sub_zero]
    have hz : z ≠ 0 := by
      rintro rfl; apply hu0; rw [hu]; simp
    rw [hu]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

lemma continuousAt_tanRatio_zero : ContinuousAt tanRatio 0 := by
  unfold tanRatio
  exact (continuousAt_dslope_same).2
    (Complex.differentiableAt_tan.2 (by simp))

lemma tanRatio_zero : tanRatio 0 = 1 := by
  rw [tanRatio, dslope_same]
  have h := (Complex.hasDerivAt_tan (x := 0) (by simp)).deriv
  rw [h]
  simp

/-- `τ(h,z) → z` uniformly on bounded sets as `h → 0`, and `cos(hz/2) ≠ 0`. -/
lemma tanRatio_uniform {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ h0 > 0, ∀ h : ℝ, 0 < h → h < h0 → ∀ z : ℂ, ‖z‖ ≤ M →
      ‖z * tanRatio (h * z / 2) - z‖ < ε ∧ Complex.cos (h * z / 2) ≠ 0 := by
  have hc1 : ContinuousAt tanRatio 0 := continuousAt_tanRatio_zero
  have hc2 : ContinuousAt Complex.cos 0 := Complex.continuous_cos.continuousAt
  obtain ⟨r1, hr1, hball1⟩ := Metric.continuousAt_iff.1 hc1 (ε / (M + 1)) (by positivity)
  obtain ⟨r2, hr2, hball2⟩ := Metric.continuousAt_iff.1 hc2 (1/2) (by norm_num)
  refine ⟨min r1 r2 / (M + 1), by positivity, fun h hh hh0 z hz => ?_⟩
  have hu : dist (h * z / 2) 0 < min r1 r2 := by
    rw [dist_zero_right, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]
    have h2 : ‖(2:ℂ)‖ = 2 := by simp
    rw [h2]
    have hlt : h * ‖z‖ < min r1 r2 := by
      calc h * ‖z‖ ≤ h * M := mul_le_mul_of_nonneg_left hz hh.le
        _ ≤ h * (M + 1) := by nlinarith
        _ < min r1 r2 / (M + 1) * (M + 1) := by
            exact mul_lt_mul_of_pos_right hh0 (by positivity)
        _ = min r1 r2 := by field_simp
    have : 0 < min r1 r2 := lt_min hr1 hr2
    linarith
  constructor
  · have h1 := hball1 (lt_of_lt_of_le hu (min_le_left _ _))
    rw [tanRatio_zero, dist_eq_norm] at h1
    rw [show z * tanRatio (h * z / 2) - z = z * (tanRatio (h * z / 2) - 1) by ring, norm_mul]
    calc ‖z‖ * ‖tanRatio (h * z / 2) - 1‖ ≤ M * ‖tanRatio (h * z / 2) - 1‖ :=
          mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ (M + 1) * ‖tanRatio (h * z / 2) - 1‖ := by nlinarith [norm_nonneg (tanRatio (h * z / 2) - 1)]
      _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left h1 (by positivity)
      _ = ε := by field_simp
  · have h2 := hball2 (lt_of_lt_of_le hu (min_le_right _ _))
    rw [Complex.cos_zero, dist_eq_norm] at h2
    intro h0
    rw [h0, zero_sub, norm_neg, norm_one] at h2
    norm_num at h2

/-- The compact set `Z = K ∪ {-i}` on which the realization lemma asks for
approximation. -/
def realizationSet (K : Set ℝ) : Set ℂ := ((↑) '' K : Set ℂ) ∪ {-Complex.I}

lemma isCompact_realizationSet {K : Set ℝ} (hK : IsCompact K) :
    IsCompact (realizationSet K) :=
  (hK.image Complex.continuous_ofReal).union isCompact_singleton

lemma im_nonpos_of_mem_realizationSet {K : Set ℝ} {z : ℂ} (hz : z ∈ realizationSet K) :
    z.im ≤ 0 := by
  rcases hz with ⟨k, _, rfl⟩ | hz
  · simp
  · rw [Set.mem_singleton_iff.1 hz]; simp

lemma norm_exp_le_one_of_im_nonpos {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z.im ≤ 0) :
    ‖Complex.exp (-Complex.I * h * z)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have : (-Complex.I * h * z).re = h * z.im := by simp
  rw [this, Real.exp_le_one_iff]
  nlinarith

/-- Steps 3–4: a function holomorphic on a disc of radius `R > 1` and bounded by
`1` on the closed unit disc is approximated there by polynomials bounded by `1`. -/
lemma exists_poly_approx_on_disc {G : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hGd : DifferentiableOn ℂ G (closedBall 0 R)) (hG1 : ∀ v : ℂ, ‖v‖ ≤ 1 → ‖G v‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, (∀ v : ℂ, ‖v‖ ≤ 1 → ‖P.eval v‖ ≤ 1) ∧
      ∀ v : ℂ, ‖v‖ ≤ 1 → ‖P.eval v - G v‖ ≤ 2 * ε := by
  have hRpos : 0 < R := by linarith
  let Rn : NNReal := ⟨R, hRpos.le⟩
  have hps := DifferentiableOn.hasFPowerSeriesOnBall (R := Rn) (c := 0) hGd
    (by show (0:ℝ) < R; exact hRpos)
  set r' : ℝ := (1 + R) / 2 with hr'def
  have hr'pos : 0 < r' := by rw [hr'def]; linarith
  let r'n : NNReal := ⟨r', hr'pos.le⟩
  have hconv := hps.tendstoUniformlyOn (r' := r'n) (by
    show ((r'n : NNReal) : ENNReal) < ((Rn : NNReal) : ENNReal)
    rw [ENNReal.coe_lt_coe]; show r' < R; rw [hr'def]; linarith)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hconv ε hε).exists
  set p := cauchyPowerSeries G 0 Rn
  let Sp : Polynomial ℂ := ∑ k ∈ Finset.range n, Polynomial.C (p.coeff k) * Polynomial.X ^ k
  have hSp : ∀ v : ℂ, Sp.eval v = p.partialSum n v := by
    intro v
    simp only [Sp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hSG : ∀ v : ℂ, ‖v‖ ≤ 1 → ‖Sp.eval v - G v‖ < ε := by
    intro v hv
    have hvball : v ∈ ball (0:ℂ) r' := by
      rw [mem_ball_zero_iff]; rw [hr'def]; linarith
    have := hn v hvball
    rw [dist_comm, dist_eq_norm, zero_add] at this
    rw [hSp]
    exact this
  have h1ε : (0:ℝ) < 1 + ε := by linarith
  let P : Polynomial ℂ := Polynomial.C ((1 + ε : ℝ) : ℂ)⁻¹ * Sp
  have hPeval : ∀ v, P.eval v = ((1 + ε : ℝ) : ℂ)⁻¹ * Sp.eval v := by
    intro v; simp [P]
  have hnorm1ε : ‖(((1 + ε : ℝ) : ℂ))⁻¹‖ = (1 + ε)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg h1ε.le]
  have hSbd : ∀ v : ℂ, ‖v‖ ≤ 1 → ‖Sp.eval v‖ ≤ 1 + ε := by
    intro v hv
    calc ‖Sp.eval v‖ = ‖(Sp.eval v - G v) + G v‖ := by ring_nf
      _ ≤ ‖Sp.eval v - G v‖ + ‖G v‖ := norm_add_le _ _
      _ ≤ ε + 1 := add_le_add (hSG v hv).le (hG1 v hv)
      _ = 1 + ε := by ring
  refine ⟨P, fun v hv => ?_, fun v hv => ?_⟩
  · rw [hPeval, norm_mul, hnorm1ε]
    calc (1 + ε)⁻¹ * ‖Sp.eval v‖ ≤ (1 + ε)⁻¹ * (1 + ε) :=
          mul_le_mul_of_nonneg_left (hSbd v hv) (by positivity)
      _ = 1 := inv_mul_cancel₀ h1ε.ne'
  · have hPS : ‖P.eval v - Sp.eval v‖ ≤ ε := by
      rw [hPeval]
      have : ((1 + ε : ℝ) : ℂ)⁻¹ * Sp.eval v - Sp.eval v =
          -(((ε : ℝ) : ℂ) * ((1 + ε : ℝ) : ℂ)⁻¹) * Sp.eval v := by
        have hne : ((1 + ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1ε.ne'
        field_simp
        push_cast
        ring
      rw [this, norm_mul, norm_neg, norm_mul, hnorm1ε, Complex.norm_real,
        Real.norm_of_nonneg hε.le]
      calc ε * (1 + ε)⁻¹ * ‖Sp.eval v‖ ≤ ε * (1 + ε)⁻¹ * (1 + ε) :=
            mul_le_mul_of_nonneg_left (hSbd v hv) (by positivity)
        _ = ε := by field_simp
    calc ‖P.eval v - G v‖ = ‖(P.eval v - Sp.eval v) + (Sp.eval v - G v)‖ := by ring_nf
      _ ≤ ‖P.eval v - Sp.eval v‖ + ‖Sp.eval v - G v‖ := norm_add_le _ _
      _ ≤ ε + ε := add_le_add hPS (hSG v hv).le
      _ = 2 * ε := by ring

/-- Step 2: moving from the unit circle slightly inside the disc changes
`Φ ∘ T_h` uniformly little on a compact parameter set. -/
lemma exists_rho_close {Φ : ℂ → ℂ} {W : Set ℂ} {Z : Set ℂ} {h : ℝ} (hh : 0 < h)
    (hZc : IsCompact Z) (hLW : {z : ℂ | z.im < 0} ⊆ W) (hΦW : ∀ z ∈ W, ContinuousAt Φ z)
    {w : ℂ → ℂ} (hwc : Continuous w) (hw1 : ∀ z ∈ Z, ‖w z‖ ≤ 1)
    (hden : ∀ z ∈ Z, 1 + w z ≠ 0) (hTW : ∀ z ∈ Z, diskToLower h (w z) ∈ W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ z ∈ Z, ‖Φ (diskToLower h (ρ * w z)) - Φ (diskToLower h (w z))‖ < ε := by
  set S : Set (ℝ × ℂ) := Set.Icc (1/2 : ℝ) 1 ×ˢ Z
  have hSc : IsCompact S := isCompact_Icc.prod hZc
  have hFc : ContinuousOn (fun p : ℝ × ℂ => Φ (diskToLower h ((p.1 : ℂ) * w p.2))) S := by
    rintro ⟨ρ, z⟩ ⟨hρ, hz⟩
    have hρ0' : (1/2 : ℝ) ≤ ρ := hρ.1
    have hρ1' : ρ ≤ 1 := hρ.2
    have hinner : Continuous fun p : ℝ × ℂ => (p.1 : ℂ) * w p.2 := by fun_prop
    have hgood : 1 + (ρ : ℂ) * w z ≠ 0 ∧ diskToLower h ((ρ : ℂ) * w z) ∈ W := by
      rcases lt_or_eq_of_le hρ1' with hρ1 | hρ1
      · have hlt : ‖(ρ : ℂ) * w z‖ < 1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          calc ρ * ‖w z‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (hw1 z hz) (by linarith)
            _ < 1 := by linarith
        exact ⟨one_add_ne_zero_of_norm_lt_one hlt, hLW (diskToLower_im_neg hh hlt)⟩
      · subst hρ1
        rw [Complex.ofReal_one, one_mul]
        exact ⟨hden z hz, hTW z hz⟩
    have hT : ContinuousAt (fun p : ℝ × ℂ => diskToLower h ((p.1 : ℂ) * w p.2)) (ρ, z) :=
      ContinuousAt.comp_of_eq (g := diskToLower h) (f := fun p : ℝ × ℂ => (p.1 : ℂ) * w p.2)
        (continuousAt_diskToLower h hgood.1) hinner.continuousAt rfl
    exact (ContinuousAt.comp_of_eq (g := Φ)
      (f := fun p : ℝ × ℂ => diskToLower h ((p.1 : ℂ) * w p.2))
      (hΦW _ hgood.2) hT rfl).continuousWithinAt
  obtain ⟨θ2, hθ2, hθ2F⟩ := Metric.uniformContinuousOn_iff.1
    (hSc.uniformContinuousOn_of_continuous hFc) ε hε
  refine ⟨max (1/2) (1 - θ2 / 2), by positivity, max_lt (by norm_num) (by linarith),
    fun z hz => ?_⟩
  set ρ : ℝ := max (1/2) (1 - θ2 / 2) with hρdef
  have hρ1 : ρ < 1 := max_lt (by norm_num) (by linarith)
  have hmem1 : ((ρ, z) : ℝ × ℂ) ∈ S := ⟨⟨le_max_left _ _, hρ1.le⟩, hz⟩
  have hmem2 : ((1, z) : ℝ × ℂ) ∈ S := ⟨⟨by norm_num, le_rfl⟩, hz⟩
  have hdist : dist ((ρ, z) : ℝ × ℂ) (1, z) < θ2 := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_neg (by linarith)]
    have : 1 - ρ ≤ θ2 / 2 := by
      have := le_max_right (1/2 : ℝ) (1 - θ2 / 2); linarith
    rw [max_eq_left (by linarith)]
    linarith
  have := hθ2F _ hmem1 _ hmem2 hdist
  rw [dist_eq_norm] at this
  simpa using this

/-- **Section 4.1.**  Approximation of `Φ` on `K ∪ {-i}` by `P(e^{-ihz})` for a
polynomial `P` bounded by `1` on the closed unit disc. -/
theorem schur_polynomial_approx {Φ : ℂ → ℂ} {K : Set ℝ} (hK : IsCompact K)
    (hΦ : AnalyticOnNhd ℂ Φ {z : ℂ | z.im < 0}) (hKan : ∀ k ∈ K, AnalyticAt ℂ Φ (k:ℂ))
    (hbd : ∀ z : ℂ, z.im < 0 → ‖Φ z‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : ℝ, 0 < h ∧ ∃ P : Polynomial ℂ, (∀ w : ℂ, ‖w‖ ≤ 1 → ‖P.eval w‖ ≤ 1) ∧
      ∀ z ∈ realizationSet K, ‖P.eval (Complex.exp (-Complex.I * h * z)) - Φ z‖ < δ := by
  have hZc : IsCompact (realizationSet K) := isCompact_realizationSet hK
  -- the open set where `Φ` is continuous
  set W : Set ℂ := {z : ℂ | z.im < 0} ∪ {z : ℂ | AnalyticAt ℂ Φ z} with hWdef
  have hWo : IsOpen W :=
    (isOpen_lt Complex.continuous_im continuous_const).union (isOpen_analyticAt ℂ Φ)
  have hΦW : ∀ z ∈ W, ContinuousAt Φ z := by
    rintro z (hz | hz)
    · exact (hΦ z hz).continuousAt
    · exact hz.continuousAt
  have hZW : realizationSet K ⊆ W := by
    rintro z (⟨k, hk, rfl⟩ | hz)
    · exact Or.inr (hKan k hk)
    · rw [Set.mem_singleton_iff.1 hz]; left; show (-Complex.I).im < 0; simp
  obtain ⟨η, hη, hthick⟩ := hZc.exists_cthickening_subset_open hWo hZW
  have hNc : IsCompact (cthickening η (realizationSet K)) := hZc.cthickening
  have hΦN : ContinuousOn Φ (cthickening η (realizationSet K)) :=
    fun z hz => (hΦW z (hthick hz)).continuousWithinAt
  obtain ⟨θ, hθ, hθΦ⟩ := Metric.uniformContinuousOn_iff.1
    (hNc.uniformContinuousOn_of_continuous hΦN) (δ / 3) (by positivity)
  obtain ⟨M, hM⟩ := hZc.isBounded.exists_norm_le
  obtain ⟨h0, hh0, hτ⟩ := tanRatio_uniform (M := max M 0) (ε := min θ η) (le_max_right _ _)
    (lt_min hθ hη)
  set h : ℝ := h0 / 2 with hhdef
  have hh : 0 < h := by positivity
  have hhlt : h < h0 := by linarith
  have hzM : ∀ z ∈ realizationSet K, ‖z‖ ≤ max M 0 :=
    fun z hz => (hM z hz).trans (le_max_left _ _)
  have hwc : Continuous fun z : ℂ => Complex.exp (-Complex.I * h * z) := by fun_prop
  have hw1 : ∀ z ∈ realizationSet K, ‖Complex.exp (-Complex.I * h * z)‖ ≤ 1 :=
    fun z hz => norm_exp_le_one_of_im_nonpos hh (im_nonpos_of_mem_realizationSet hz)
  have hcos : ∀ z ∈ realizationSet K, Complex.cos (h * z / 2) ≠ 0 :=
    fun z hz => (hτ h hh hhlt z (hzM z hz)).2
  have hden : ∀ z ∈ realizationSet K, 1 + Complex.exp (-Complex.I * h * z) ≠ 0 := by
    intro z hz
    have := one_add_exp_ne_zero (hcos z hz)
    have heq : Complex.exp (-(2 * (h * z / 2)) * Complex.I) =
        Complex.exp (-Complex.I * h * z) := by ring_nf
    rwa [heq] at this
  have hT : ∀ z ∈ realizationSet K,
      diskToLower h (Complex.exp (-Complex.I * h * z)) = z * tanRatio (h * z / 2) :=
    fun z hz => diskToLower_exp hh (hcos z hz)
  have hTN : ∀ z ∈ realizationSet K,
      diskToLower h (Complex.exp (-Complex.I * h * z)) ∈ cthickening η (realizationSet K) := by
    intro z hz
    rw [hT z hz]
    refine mem_cthickening_of_dist_le _ z η _ hz ?_
    rw [dist_eq_norm]
    exact ((hτ h hh hhlt z (hzM z hz)).1.trans_le (min_le_right _ _)).le
  -- step 1
  have hstep1 : ∀ z ∈ realizationSet K,
      ‖Φ (diskToLower h (Complex.exp (-Complex.I * h * z))) - Φ z‖ < δ / 3 := by
    intro z hz
    rw [← dist_eq_norm]
    refine hθΦ _ (hTN z hz) z (self_subset_cthickening _ hz) ?_
    rw [hT z hz, dist_eq_norm]
    exact (hτ h hh hhlt z (hzM z hz)).1.trans_le (min_le_left _ _)
  -- step 2
  obtain ⟨ρ, hρ0, hρ1, hstep2⟩ := exists_rho_close (Φ := Φ) (W := W) hh hZc
    (fun z hz => Or.inl hz) hΦW hwc hw1 hden (fun z hz => hthick (hTN z hz))
    (ε := δ / 3) (by positivity)
  -- steps 3–4
  set R : ℝ := (1 + ρ⁻¹) / 2 with hRdef
  have hρinv : 1 < ρ⁻¹ := by rw [lt_inv_comm₀ one_pos hρ0, inv_one]; exact hρ1
  have hR1 : 1 < R := by rw [hRdef]; linarith
  have hρR : ρ * R < 1 := by
    rw [hRdef]
    have : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    nlinarith
  have hG_inner : ∀ v : ℂ, ‖v‖ ≤ R → ‖(ρ : ℂ) * v‖ < 1 := by
    intro v hv
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    calc ρ * ‖v‖ ≤ ρ * R := mul_le_mul_of_nonneg_left hv hρ0.le
      _ < 1 := hρR
  have hGd : DifferentiableOn ℂ (fun v : ℂ => Φ (diskToLower h (ρ * v))) (closedBall 0 R) := by
    intro v hv
    have hv' : ‖v‖ ≤ R := by simpa using hv
    have hlt := hG_inner v hv'
    have hΦd : DifferentiableAt ℂ Φ (diskToLower h ((ρ:ℂ) * v)) :=
      (hΦ _ (diskToLower_im_neg hh hlt)).differentiableAt
    exact (hΦd.comp v ((differentiableAt_diskToLower h (one_add_ne_zero_of_norm_lt_one hlt)).comp v
        ((differentiableAt_const _).mul differentiableAt_id))).differentiableWithinAt
  have hG1 : ∀ v : ℂ, ‖v‖ ≤ 1 → ‖Φ (diskToLower h (ρ * v))‖ ≤ 1 := by
    intro v hv
    exact hbd _ (diskToLower_im_neg hh (hG_inner v (by linarith)))
  obtain ⟨P, hPbd, hPG⟩ := exists_poly_approx_on_disc hR1 hGd hG1 (ε := δ / 12) (by positivity)
  refine ⟨h, hh, P, hPbd, fun z hz => ?_⟩
  have e1 := hPG _ (hw1 z hz)
  have e2 := hstep2 z hz
  have e3 := hstep1 z hz
  set v := Complex.exp (-Complex.I * h * z)
  calc ‖P.eval v - Φ z‖
      = ‖(P.eval v - Φ (diskToLower h (ρ * v))) +
          (Φ (diskToLower h (ρ * v)) - Φ (diskToLower h v)) +
          (Φ (diskToLower h v) - Φ z)‖ := by ring_nf
    _ ≤ ‖P.eval v - Φ (diskToLower h (ρ * v))‖ +
          ‖Φ (diskToLower h (ρ * v)) - Φ (diskToLower h v)‖ +
          ‖Φ (diskToLower h v) - Φ z‖ := norm_add₃_le
    _ < 2 * (δ / 12) + δ / 3 + δ / 3 := by linarith
    _ < δ := by linarith

end LCHSWiener
