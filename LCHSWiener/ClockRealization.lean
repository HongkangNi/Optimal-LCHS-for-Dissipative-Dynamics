import LCHSWiener.ClockDiscrete
import LCHSWiener.Realization
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

open Set Filter
open scoped InnerProductSpace Topology ComplexOrder

namespace LCHSWiener

/-!
# Section 4.3, part 3: the clock realization

The reference solution is `Ψ_z(t, s) = g(s - t) 𝒰_z(s) e₀`, a wave packet `g`
transported along the clock coordinate `s` while the pulses act on `ℂ²`.  It
satisfies `i ∂_t Ψ = -i ∂_s Ψ + (z L(s) + H(s)) Ψ`.  Sampling it on the grid
`s_j = jδ` gives an approximate solution of the finite system
`i ψ' = (D + z L_N + H_N) ψ`; the residual is the central-difference
consistency error, and the Duhamel estimate turns it into a uniform bound on the
matrix element.
-/

/-! ### The wave packet -/

/-- A smooth bump, `0` outside `(1, 2)` and `1` on `[5/4, 7/4]`. -/
def bump (s : ℝ) : ℝ := θ (4 * (s - 1)) * θ (4 * (2 - s))

/-- The derivative of `bump`. -/
def bumpD (s : ℝ) : ℝ :=
  4 * deriv θ (4 * (s - 1)) * θ (4 * (2 - s)) - 4 * θ (4 * (s - 1)) * deriv θ (4 * (2 - s))

lemma bump_hasDerivAt (s : ℝ) : HasDerivAt bump (bumpD s) s := by
  have h1 : HasDerivAt (fun s : ℝ => θ (4 * (s - 1))) (deriv θ (4 * (s - 1)) * 4) s := by
    have := (θ_hasDerivAt (4 * (s - 1))).comp s
      (((hasDerivAt_id s).sub_const 1).const_mul 4)
    convert this using 1 <;> first | rfl | ring
  have h2 : HasDerivAt (fun s : ℝ => θ (4 * (2 - s))) (deriv θ (4 * (2 - s)) * (-4)) s := by
    have := (θ_hasDerivAt (4 * (2 - s))).comp s
      (((hasDerivAt_id s).const_sub 2).const_mul 4)
    convert this using 1 <;> first | rfl | ring
  have key := (h1.mul h2).congr_deriv (show _ = bumpD s by unfold bumpD; ring)
  exact key

lemma continuous_bump : Continuous bump := by
  unfold bump
  exact (Real.smoothTransition.continuous.comp (by fun_prop)).mul
    (Real.smoothTransition.continuous.comp (by fun_prop))

lemma continuous_bumpD : Continuous bumpD := by
  unfold bumpD
  have hθ := Real.smoothTransition.continuous
  have hd := continuous_deriv_θ
  refine ((continuous_const.mul (hd.comp (by fun_prop))).mul (hθ.comp (by fun_prop))).sub
    ((continuous_const.mul (hθ.comp (by fun_prop))).mul (hd.comp (by fun_prop)))

lemma bump_of_le_one {s : ℝ} (hs : s ≤ 1) : bump s = 0 := by
  rw [bump, θ_of_nonpos (by linarith), zero_mul]

lemma bump_of_two_le {s : ℝ} (hs : 2 ≤ s) : bump s = 0 := by
  rw [bump, θ_of_nonpos (x := 4 * (2 - s)) (by linarith), mul_zero]

lemma bump_eq_one {s : ℝ} (h1 : 5 / 4 ≤ s) (h2 : s ≤ 7 / 4) : bump s = 1 := by
  rw [bump, θ_of_one_le (by linarith), θ_of_one_le (by linarith), one_mul]

lemma bump_nonneg (s : ℝ) : 0 ≤ bump s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma bump_le_one (s : ℝ) : bump s ≤ 1 := by
  unfold bump
  have h1 := Real.smoothTransition.le_one (4 * (s - 1))
  have h2 := Real.smoothTransition.le_one (4 * (2 - s))
  have h3 := Real.smoothTransition.nonneg (4 * (s - 1))
  have h4 := Real.smoothTransition.nonneg (4 * (2 - s))
  nlinarith

/-- The vector `|0⟩ ∈ ℂ²`. -/
def e0v : Hd 2 := EuclideanSpace.single 0 1

lemma norm_e0v : ‖e0v‖ = 1 := by simp [e0v]

/-! ### The reference solution -/

variable (ps : List Pulse)

/-- `Ψ_z(t, s) = g(s - t) 𝒰_z(s) e₀`. -/
def refSol (z : ℂ) (t s : ℝ) : Hd 2 := ((bump (s - t) : ℝ) : ℂ) • pulseProd ps 0 z s e0v

/-- `∂_s Ψ_z(t, s)`. -/
def refSolD (z : ℂ) (t s : ℝ) : Hd 2 :=
  ((bumpD (s - t) : ℝ) : ℂ) • pulseProd ps 0 z s e0v +
    ((bump (s - t) : ℝ) : ℂ) •
      ((-(Complex.I • (z • pulseL ps 0 s + pulseH ps 0 s)) * pulseProd ps 0 z s) e0v)

/-- `∂_t Ψ_z(t, s)`. -/
def refSolT (z : ℂ) (t s : ℝ) : Hd 2 := -(((bumpD (s - t) : ℝ) : ℂ) • pulseProd ps 0 z s e0v)

lemma refSol_hasDerivAt_s (z : ℂ) (t s : ℝ) :
    HasDerivAt (refSol ps z t) (refSolD ps z t s) s := by
  have hb : HasDerivAt (fun s : ℝ => ((bump (s - t) : ℝ) : ℂ)) ((bumpD (s - t) : ℝ) : ℂ) s :=
    ((bump_hasDerivAt (s - t)).comp_sub_const s t).ofReal_comp
  have hU := pulseProd_hasDerivAt ps 0 z s
  let ev : Op 2 →L[ℝ] Hd 2 := (ContinuousLinearMap.apply ℂ (Hd 2) e0v).restrictScalars ℝ
  have hUe : HasDerivAt (fun s => pulseProd ps 0 z s e0v)
      ((-(Complex.I • (z • pulseL ps 0 s + pulseH ps 0 s)) * pulseProd ps 0 z s) e0v) s :=
    ev.hasFDerivAt.comp_hasDerivAt s hU
  have key := (hb.smul hUe).congr_deriv (show _ = refSolD ps z t s by unfold refSolD; rw [add_comm])
  exact key

lemma refSol_hasDerivAt_t (z : ℂ) (t s : ℝ) :
    HasDerivAt (fun t => refSol ps z t s) (refSolT ps z t s) t := by
  have hb : HasDerivAt (fun t : ℝ => ((bump (s - t) : ℝ) : ℂ)) (-((bumpD (s - t) : ℝ) : ℂ)) t := by
    have := ((bump_hasDerivAt (s - t)).comp t ((hasDerivAt_id t).const_sub s)).ofReal_comp
    simpa using this
  have key := (hb.smul_const (pulseProd ps 0 z s e0v)).congr_deriv
    (show _ = refSolT ps z t s by unfold refSolT; rw [neg_smul])
  exact key

/-- The transport equation `i ∂_t Ψ = -i ∂_s Ψ + (z L + H) Ψ`. -/
lemma refSol_transport (z : ℂ) (t s : ℝ) :
    Complex.I • refSolT ps z t s =
      -(Complex.I • refSolD ps z t s) + (z • pulseL ps 0 s + pulseH ps 0 s) (refSol ps z t s) := by
  unfold refSolT refSolD refSol
  set v := pulseProd ps 0 z s e0v
  have hA : (-(Complex.I • (z • pulseL ps 0 s + pulseH ps 0 s)) * pulseProd ps 0 z s) e0v =
      -(Complex.I • (z • pulseL ps 0 s v + pulseH ps 0 s v)) := by
    rw [mul_apply_eq_comp]
    simp [v]
  rw [hA, map_smul, add_apply, smul_apply]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

lemma refSol_of_not_mem {z : ℂ} {t s : ℝ} (h : s - t ≤ 1 ∨ 2 ≤ s - t) : refSol ps z t s = 0 := by
  rcases h with h | h
  · simp [refSol, bump_of_le_one h]
  · simp [refSol, bump_of_two_le h]

lemma refSol_time_zero (z : ℂ) (s : ℝ) : refSol ps z 0 s = ((bump s : ℝ) : ℂ) • e0v := by
  by_cases hs : s ≤ 2
  · rw [refSol, sub_zero, pulseProd_of_le ps 0 z s (by simp [pulseStart]; linarith),
      one_apply_eq_self]
  · rw [refSol, sub_zero, bump_of_two_le (le_of_not_ge hs)]; simp

lemma refSol_late (z : ℂ) {t : ℝ} (ht : pulseStart ps.length - 2 ≤ t) (s : ℝ) :
    refSol ps z t s = ((bump (s - t) : ℝ) : ℂ) • endProd ps z e0v := by
  by_cases hs : s - t ≤ 1
  · rw [refSol, bump_of_le_one hs]; simp
  · rw [refSol, pulseProd_of_ge ps 0 z s (by rw [zero_add]; linarith)]

lemma continuous_refSolD :
    Continuous fun q : ℝ × ℝ × ℂ => refSolD ps q.2.2 q.1 q.2.1 := by
  have hU := continuous_pulseProd ps 0
  have hUq : Continuous fun q : ℝ × ℝ × ℂ => pulseProd ps 0 q.2.2 q.2.1 :=
    hU.comp ((continuous_snd.snd.prodMk continuous_snd.fst :
      Continuous fun q : ℝ × ℝ × ℂ => (q.2.2, q.2.1)))
  have hL : Continuous fun q : ℝ × ℝ × ℂ => pulseL ps 0 q.2.1 :=
    (continuous_pulseL ps 0).comp continuous_snd.fst
  have hH : Continuous fun q : ℝ × ℝ × ℂ => pulseH ps 0 q.2.1 :=
    (continuous_pulseH ps 0).comp continuous_snd.fst
  have hbD : Continuous fun q : ℝ × ℝ × ℂ => ((bumpD (q.2.1 - q.1) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_bumpD.comp (continuous_snd.fst.sub continuous_fst))
  have hb : Continuous fun q : ℝ × ℝ × ℂ => ((bump (q.2.1 - q.1) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_bump.comp (continuous_snd.fst.sub continuous_fst))
  have happ : Continuous fun T : Op 2 => T e0v := (ContinuousLinearMap.apply ℂ (Hd 2) e0v).continuous
  unfold refSolD
  refine (hbD.fun_smul (happ.comp hUq)).add (hb.fun_smul (happ.comp ?_))
  refine Continuous.mul ?_ hUq
  refine Continuous.neg (continuous_const.fun_smul ?_)
  exact (continuous_snd.snd.fun_smul hL).add hH

/-! ### Central differences -/

/-- The central-difference error is controlled by the modulus of continuity of `f'`. -/
lemma central_diff_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} (hf : ∀ y, HasDerivAt f (f' y) y) {s δ η : ℝ} (hδ : 0 < δ)
    (hη : ∀ y, |y - s| ≤ δ → ‖f' y - f' s‖ ≤ η) :
    ‖(f (s + δ) - f (s - δ)) - (2 * δ) • f' s‖ ≤ 2 * δ * η := by
  let G : ℝ → F := fun u => f (s + u) - u • f' s
  have hG : ∀ u ∈ Icc (-δ) δ, HasDerivWithinAt G (f' (s + u) - f' s) (Icc (-δ) δ) u := by
    intro u _
    have h1 := (hf (s + u)).comp_const_add s u
    have h2 := (hasDerivAt_id u).smul_const (f' s)
    have h3 := (h1.sub h2).congr_deriv (show _ = f' (s + u) - f' s by simp)
    exact h3.hasDerivWithinAt
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hG (fun u hu => by
    apply hη; rw [add_sub_cancel_left, abs_le]; exact ⟨hu.1, hu.2.le⟩) δ (right_mem_Icc.2 (by linarith))
  simp only [G] at hb
  convert hb using 1
  · congr 1
    rw [neg_smul, sub_neg_eq_add, two_mul, add_smul, ← sub_eq_add_neg]
    abel_nf
  · ring

/-- Complex-scalar form of `central_diff_bound`. -/
lemma central_diff_bound_complex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f f' : ℝ → F} (hf : ∀ y, HasDerivAt f (f' y) y) {s δ η : ℝ} (hδ : 0 < δ)
    (hη : ∀ y, |y - s| ≤ δ → ‖f' y - f' s‖ ≤ η) :
    ‖(f (s + δ) - f (s - δ)) - ((2 * δ : ℝ) : ℂ) • f' s‖ ≤ 2 * δ * η := by
  rw [Complex.coe_smul]
  exact central_diff_bound hf hδ hη

/-! ### The discrete evolution -/

variable (N : ℕ) [NeZero N]

/-- `G(z) = z L_N + (D + H_N)` on the clock space. -/
def clockGen (δ : ℝ) (z : ℂ) : ClockOp N :=
  z • blockDiag N (fun j => pulseL ps 0 ((j : ℕ) * δ)) +
    (centralDiff N δ + blockDiag N (fun j => pulseH ps 0 ((j : ℕ) * δ)))

omit [NeZero N] in
lemma sample_hasDerivAt (z : ℂ) (δ t : ℝ) :
    HasDerivAt (fun t => sample N δ (refSol ps z t)) (sample N δ (refSolT ps z t)) t := by
  let e : (Fin N → Hd 2) →L[ℝ] ClockSpace N :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => Hd 2)).symm :
      (Fin N → Hd 2) →L[ℂ] ClockSpace N).restrictScalars ℝ
  have hpi : HasDerivAt (fun t => fun j : Fin N => ((Real.sqrt δ : ℝ) : ℂ) • refSol ps z t ((j : ℕ) * δ))
      (fun j => ((Real.sqrt δ : ℝ) : ℂ) • refSolT ps z t ((j : ℕ) * δ)) t :=
    hasDerivAt_pi.2 fun j => by
      have := (refSol_hasDerivAt_t ps z t ((j : ℕ) * δ)).const_smul (((Real.sqrt δ : ℝ) : ℂ))
      exact this
  exact e.hasFDerivAt.comp_hasDerivAt t hpi

omit [NeZero N] in
lemma sample_add_one (hN : 2 ≤ N) {δ : ℝ} (f : ℝ → Hd 2) (hwrap : f 0 = f (N * δ))
    [NeZero N] (j : Fin N) :
    sample N δ f (j + 1) = ((Real.sqrt δ : ℝ) : ℂ) • f ((j : ℕ) * δ + δ) := by
  rw [sample_apply]
  congr 1
  by_cases h : (j : ℕ) + 1 < N
  · rw [Fin.val_add_one_of_lt' h]; push_cast; ring_nf
  · have hj : (j : ℕ) + 1 = N := by have := j.isLt; omega
    have hv : ((j + 1 : Fin N) : ℕ) = 0 := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N), hj, Nat.mod_self]
    rw [hv, Nat.cast_zero, zero_mul, hwrap]
    congr 1
    have hjN : (N : ℝ) = (j : ℕ) + 1 := by exact_mod_cast hj.symm
    rw [hjN]; ring

omit [NeZero N] in
lemma sample_sub_one (hN : 2 ≤ N) {δ : ℝ} (f : ℝ → Hd 2) (hwrap : f (-δ) = f ((N - 1 : ℕ) * δ))
    [NeZero N] (j : Fin N) :
    sample N δ f (j - 1) = ((Real.sqrt δ : ℝ) : ℂ) • f ((j : ℕ) * δ - δ) := by
  rw [sample_apply]
  congr 1
  by_cases hj : j = 0
  · subst hj
    have hv : (((0 : Fin N) - 1 : Fin N) : ℕ) = N - 1 := by
      rw [Fin.val_sub, Fin.val_zero, add_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N),
        Nat.mod_eq_of_lt (by omega)]
    rw [hv, ← hwrap, Fin.val_zero, Nat.cast_zero, zero_mul, zero_sub]
  · rw [Fin.val_sub_one_of_ne_zero hj]
    have h1 : 1 ≤ (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
      · exact absurd (Fin.ext h) hj
      · exact h
    rw [Nat.cast_sub h1]; push_cast; ring_nf

/-- The residual of the sampled reference solution is the central-difference error. -/
lemma residual_norm_le (hN : 2 ≤ N) {z : ℂ} {δ t η : ℝ} (hδ : 0 < δ)
    (hw1 : refSol ps z t 0 = refSol ps z t (N * δ))
    (hw2 : refSol ps z t (-δ) = refSol ps z t ((N - 1 : ℕ) * δ))
    (hη : ∀ j : Fin N, ∀ y, |y - (j : ℕ) * δ| ≤ δ →
      ‖refSolD ps z t y - refSolD ps z t ((j : ℕ) * δ)‖ ≤ η) :
    ‖Complex.I • sample N δ (refSolT ps z t) - clockGen ps N δ z (sample N δ (refSol ps z t))‖ ≤
      Real.sqrt (N * δ) * η := by
  have hη0 : 0 ≤ η := by
    have := hη ⟨0, Nat.pos_of_neZero N⟩ ((0 : ℕ) * δ) (by simp; linarith)
    simp at this; exact this
  have hcomp : ∀ j : Fin N, ‖(Complex.I • sample N δ (refSolT ps z t) -
      clockGen ps N δ z (sample N δ (refSol ps z t))) j‖ ≤ Real.sqrt δ * η := by
    intro j
    set sj : ℝ := (j : ℕ) * δ
    set c : ℂ := ((Real.sqrt δ : ℝ) : ℂ)
    have hG : clockGen ps N δ z (sample N δ (refSol ps z t)) j =
        z • pulseL ps 0 sj (c • refSol ps z t sj) +
          (((2 * Complex.I * δ)⁻¹ : ℂ) • (c • refSol ps z t (sj + δ) - c • refSol ps z t (sj - δ)) +
            pulseH ps 0 sj (c • refSol ps z t sj)) := by
      simp only [clockGen, add_apply, smul_apply,
        PiLp.add_apply, PiLp.smul_apply, blockDiag_apply, centralDiff_apply]
      rw [sample_add_one N hN _ hw1, sample_sub_one N hN _ hw2]
      rfl
    rw [PiLp.sub_apply, PiLp.smul_apply, hG, sample_apply]
    have htr := refSol_transport ps z t sj
    -- rewrite the residual as `c • (2iδ)⁻¹ • ((2δ) ∂_sΨ - (Ψ(s+δ) - Ψ(s-δ)))`
    have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
    have hkey : Complex.I • (c • refSolT ps z t sj) -
        (z • pulseL ps 0 sj (c • refSol ps z t sj) +
          (((2 * Complex.I * δ)⁻¹ : ℂ) • (c • refSol ps z t (sj + δ) - c • refSol ps z t (sj - δ)) +
            pulseH ps 0 sj (c • refSol ps z t sj))) =
        (c * (2 * Complex.I * δ)⁻¹) • (((2 * δ : ℝ) : ℂ) • refSolD ps z t sj -
          (refSol ps z t (sj + δ) - refSol ps z t (sj - δ))) := by
      rw [smul_comm Complex.I c, htr]
      simp only [map_smul, add_apply, smul_apply]
      have hI : (2 * Complex.I * (δ : ℂ))⁻¹ * (2 * (δ : ℂ)) = -Complex.I := by
        field_simp
        rw [Complex.I_sq]; ring
      push_cast
      match_scalars <;> (try ring1)
      rw [mul_assoc, hI]
    rw [hkey, norm_smul, norm_mul, norm_sub_rev]
    have hcd := central_diff_bound_complex (f := refSol ps z t) (f' := refSolD ps z t)
      (fun y => refSol_hasDerivAt_s ps z t y) (s := sj) hδ (hη j)
    have hc : ‖c‖ = Real.sqrt δ := by
      simp [c, Real.sqrt_nonneg]
    have hinv : ‖((2 * Complex.I * δ)⁻¹ : ℂ)‖ = (2 * δ)⁻¹ := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_of_nonneg hδ.le]
      norm_num
    rw [hc, hinv]
    calc Real.sqrt δ * (2 * δ)⁻¹ *
          ‖refSol ps z t (sj + δ) - refSol ps z t (sj - δ) - ((2 * δ : ℝ) : ℂ) • refSolD ps z t sj‖
        ≤ Real.sqrt δ * (2 * δ)⁻¹ * (2 * δ * η) :=
          mul_le_mul_of_nonneg_left hcd (by positivity)
      _ = Real.sqrt δ * η := by field_simp
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hη0, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [norm_sq_eq_sum]
  calc ∑ j, ‖(Complex.I • sample N δ (refSolT ps z t) -
        clockGen ps N δ z (sample N δ (refSol ps z t))) j‖ ^ 2
      ≤ ∑ _j : Fin N, (Real.sqrt δ * η) ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcomp j) 2
    _ = N * δ * η ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow,
          Real.sq_sqrt hδ.le]
        ring

/-! ### The initial and final wave packets -/

omit [NeZero N] in
lemma norm_sq_sample_smul {δ : ℝ} (hδ : 0 ≤ δ) (b : ℝ → ℝ) (w : Hd 2) :
    ‖sample N δ (fun s => ((b s : ℝ) : ℂ) • w)‖ ^ 2 = ∑ j : Fin N, δ * b ((j : ℕ) * δ) ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sample_apply, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hδ, Real.norm_eq_abs,
    sq_abs]
  ring

omit [NeZero N] in
lemma inner_sample_smul {δ : ℝ} (hδ : 0 ≤ δ) (b : ℝ → ℝ) (w : Hd 2) :
    ⟪sample N δ (fun s => ((b s : ℝ) : ℂ) • e0v), sample N δ (fun s => ((b s : ℝ) : ℂ) • w)⟫_ℂ =
      ((‖sample N δ (fun s => ((b s : ℝ) : ℂ) • e0v)‖ ^ 2 : ℝ) : ℂ) * ⟪e0v, w⟫_ℂ := by
  rw [inner_sample N hδ, norm_sq_sample_smul N hδ, norm_e0v, one_pow]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

lemma inner_e0v_toOp (A : M2) : ⟪e0v, toOp A e0v⟫_ℂ = A 0 0 := by
  rw [e0v, EuclideanSpace.inner_single_left, map_one, one_mul]
  show (WithLp.ofLp (toOp A (EuclideanSpace.single 0 1))) 0 = A 0 0
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, EuclideanSpace.single]

omit [NeZero N] in
/-- With `δ = 1/(4(m+1))`, the packet `bump` has discrete norm `≥ 1/2`. -/
lemma norm_sq_sample_bump_ge (m : ℕ) (hN : 7 * (m + 1) ≤ N) :
    1 / 2 ≤ ‖sample N (1 / (4 * ((m : ℝ) + 1))) (fun s => ((bump s : ℝ) : ℂ) • e0v)‖ ^ 2 := by
  set δ : ℝ := 1 / (4 * ((m : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  rw [norm_sq_sample_smul N hδ.le, norm_e0v, one_pow]
  let S : Finset (Fin N) := (Finset.range (2 * (m + 1))).attach.image
    (fun i => ⟨5 * (m + 1) + i.1, by have := Finset.mem_range.1 i.2; omega⟩)
  have hinj : ∀ a ∈ (Finset.range (2 * (m + 1))).attach, ∀ b ∈ (Finset.range (2 * (m + 1))).attach,
      (⟨5 * (m + 1) + a.1, by have := Finset.mem_range.1 a.2; omega⟩ : Fin N) =
        ⟨5 * (m + 1) + b.1, by have := Finset.mem_range.1 b.2; omega⟩ → a = b := by
    intro a _ b _ h
    have := congrArg Fin.val h
    simp at this
    exact this
  calc (1 : ℝ) / 2 = ∑ _i ∈ (Finset.range (2 * (m + 1))).attach, δ := by
        rw [Finset.sum_const, Finset.card_attach, Finset.card_range, nsmul_eq_mul, hδdef]
        push_cast; field_simp; ring
    _ = ∑ j ∈ S, δ * bump ((j : ℕ) * δ) ^ 2 * 1 := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi := Finset.mem_range.1 i.2
        rw [bump_eq_one, one_pow, mul_one, mul_one]
        · simp only [hδdef]
          push_cast
          rw [div_le_iff₀ (by positivity)]
          · have : (0:ℝ) ≤ i.1 := Nat.cast_nonneg _
            field_simp; nlinarith
        · simp only [hδdef]
          push_cast
          have : (i.1 : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1) := by exact_mod_cast hi
          field_simp; nlinarith
    _ ≤ ∑ j : Fin N, δ * bump ((j : ℕ) * δ) ^ 2 * 1 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => by have := bump_nonneg ((j : ℕ) * δ); positivity)

/-- Translating the packet by `τ = n₂ δ` (half the clock) does not change its norm. -/
lemma norm_sample_bump_shift (n2 : ℕ) (hn2 : 0 < n2) {δ : ℝ} (hδ : 0 < δ) (hτ : 2 ≤ n2 * δ)
    [NeZero (2 * n2)] :
    ‖sample (2 * n2) δ (fun s => ((bump (s - n2 * δ) : ℝ) : ℂ) • e0v)‖ =
      ‖sample (2 * n2) δ (fun s => ((bump s : ℝ) : ℂ) • e0v)‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_sample_smul _ hδ.le,
    norm_sq_sample_smul _ hδ.le]
  refine Fintype.sum_equiv (Equiv.addRight (⟨n2, by omega⟩ : Fin (2 * n2))) _ _ fun j => ?_
  rw [Equiv.coe_addRight]
  by_cases hj : (j : ℕ) < n2
  · have hv : ((j + ⟨n2, by omega⟩ : Fin (2 * n2)) : ℕ) = j + n2 := by
      rw [Fin.val_add]
      show ((j : ℕ) + n2) % (2 * n2) = (j : ℕ) + n2
      exact Nat.mod_eq_of_lt (by omega)
    rw [hv, bump_of_le_one, bump_of_two_le]
    · push_cast
      have : (0:ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
      nlinarith
    · have : ((j : ℕ) : ℝ) + 1 ≤ n2 := by exact_mod_cast hj
      nlinarith
  · have hv : ((j + ⟨n2, by omega⟩ : Fin (2 * n2)) : ℕ) = j - n2 := by
      rw [Fin.val_add]
      show ((j : ℕ) + n2) % (2 * n2) = (j : ℕ) - n2
      have := j.isLt
      rw [show (j : ℕ) + n2 = (j - n2) + 2 * n2 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hv, Nat.cast_sub (le_of_not_gt hj)]
    ring_nf

/-! ### The realization -/

set_option maxHeartbeats 1000000 in
/-- **Section 4.3.**  GQSP products are realized by `⟨v, e^{-i(zX+Y)} u⟩`. -/
theorem productRealization : ProductRealization := by
  intro V0 Vs hV0 hVs h hh Z hZ hZim ε hε
  set ps := gqspPulses h hh.le V0 Vs with hps
  set M : ℕ := ps.length
  set τ : ℝ := 2 * M + 4 with hτdef
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hτ4 : 4 ≤ τ := by rw [hτdef]; linarith
  set L : ℝ := 2 * τ with hLdef
  -- uniform continuity of `∂_s Ψ` on a compact set
  set K : Set (ℝ × ℝ × ℂ) := Icc 0 τ ×ˢ (Icc (-1) (L + 1) ×ˢ Z)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod hZ)
  have huc := hK.uniformContinuousOn_of_continuous (continuous_refSolD ps).continuousOn
  set η : ℝ := ε / (4 * τ * Real.sqrt L + 1) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ0, hδ0, hδ0K⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ0
  -- the grid
  set δ : ℝ := 1 / (4 * ((m : ℝ) + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ14 : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0:ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hδδ0 : δ < δ0 := by
    refine lt_of_le_of_lt ?_ hm
    rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  set n2 : ℕ := (2 * M + 4) * (4 * (m + 1)) with hn2def
  set N : ℕ := 2 * n2 with hNdef
  have hn2pos : 0 < n2 := by positivity
  have : NeZero N := ⟨by omega⟩
  have hN2 : 2 ≤ N := by omega
  have hN7 : 7 * (m + 1) ≤ N := by
    simp only [hNdef, hn2def]; nlinarith
  have hn2δ : (n2 : ℝ) * δ = τ := by
    simp only [hn2def, hδdef, hτdef]; push_cast; field_simp
  have hNδ : (N : ℝ) * δ = L := by
    simp only [hNdef, hLdef]; push_cast; rw [mul_assoc, hn2δ]
  -- the operators
  set Lop : Fin N → Op 2 := fun j => pulseL ps 0 ((j : ℕ) * δ)
  set Hop : Fin N → Op 2 := fun j => pulseH ps 0 ((j : ℕ) * δ)
  have hLb : (blockDiag N Lop).IsPositive := isPositive_blockDiag N fun j => isPositive_pulseL ps 0 _
  have hHb : IsSelfAdjoint (centralDiff N δ + blockDiag N Hop) := by
    have h1 := (isSelfAdjoint_centralDiff N δ).isSymmetric
    have h2 := (isSelfAdjoint_blockDiag N fun j => isSelfAdjoint_pulseH ps 0 ((j : ℕ) * δ)).isSymmetric
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    show ⟪centralDiff N δ x + blockDiag N Hop x, y⟫_ℂ = ⟪x, centralDiff N δ y + blockDiag N Hop y⟫_ℂ
    rw [inner_add_left, inner_add_right]
    exact congrArg₂ (· + ·) (h1 x y) (h2 x y)
  set X : ClockOp N := (τ : ℂ) • blockDiag N Lop
  set Y : ClockOp N := (τ : ℂ) • (centralDiff N δ + blockDiag N Hop)
  have hX : X.IsPositive := hLb.smul_of_nonneg (by exact_mod_cast (show (0:ℝ) ≤ τ by linarith))
  have hY : IsSelfAdjoint Y := by
    rw [IsSelfAdjoint, star_smul, hHb.star_eq]
    congr 1
    exact Complex.conj_ofReal _
  -- the initial and final packets
  set ψ0 := sample N δ (fun s => ((bump s : ℝ) : ℂ) • e0v)
  set ψh := sample N δ (fun s => ((bump (s - τ) : ℝ) : ℂ) • e0v)
  set σ := ‖ψ0‖ with hσdef
  have hσ2 : 1 / 2 ≤ σ ^ 2 := norm_sq_sample_bump_ge N m hN7
  have hσ : 0 < σ := by
    rcases (norm_nonneg ψ0).lt_or_eq with h' | h'
    · exact h'
    · rw [hσdef, ← h'] at hσ2; norm_num at hσ2
  have hσh : ‖ψh‖ = σ := by
    have := norm_sample_bump_shift n2 hn2pos hδ (by rw [hn2δ]; linarith)
    rw [hn2δ] at this
    exact this
  set u : ClockSpace N := ((σ : ℂ)⁻¹) • ψ0
  set v : ClockSpace N := ((σ : ℂ)⁻¹) • ψh
  have hσC : ‖((σ : ℂ)⁻¹)‖ = σ⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hσ.le]
  have hu : ‖u‖ = 1 := by rw [norm_smul, hσC, inv_mul_cancel₀ hσ.ne']
  have hv : ‖v‖ = 1 := by rw [norm_smul, hσC, hσh, inv_mul_cancel₀ hσ.ne']
  obtain ⟨d, X', Y', u', v', hX', hY', hu', hv', heq⟩ :=
    exists_hd_of_finiteDimensional X Y u v hX hY hu hv
  refine ⟨d, X', Y', u', v', hX', hY', hu', hv', fun z hz => ?_⟩
  rw [heq z]
  -- the Duhamel estimate for this `z`
  set G := clockGen ps N δ z with hGdef
  have hdiss : ∀ ξ : ClockSpace N, (⟪ξ, (-(Complex.I • G)) ξ⟫_ℂ).re ≤ 0 :=
    re_inner_neg_I_smul_nonpos hLb hHb (hZim z hz)
  set ψ : ℝ → ClockSpace N := fun t => sample N δ (refSol ps z t)
  set r : ℝ → ClockSpace N := fun t => Complex.I • sample N δ (refSolT ps z t) - G (ψ t)
  have hψ : ∀ t ∈ Icc 0 τ, HasDerivAt ψ (-(Complex.I • (G (ψ t) + r t))) t := by
    intro t _
    refine (sample_hasDerivAt ps N z δ t).congr_deriv ?_
    simp only [r, add_sub_cancel, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  have hr : ∀ t ∈ Icc 0 τ, ‖r t‖ ≤ Real.sqrt L * η := by
    intro t ht
    have hw1 : refSol ps z t 0 = refSol ps z t (N * δ) := by
      rw [refSol_of_not_mem ps (Or.inl (by linarith [ht.1])),
        refSol_of_not_mem ps (Or.inr (by rw [hNδ]; linarith [ht.2]))]
    have hw2 : refSol ps z t (-δ) = refSol ps z t ((N - 1 : ℕ) * δ) := by
      rw [refSol_of_not_mem ps (Or.inl (by linarith [ht.1])),
        refSol_of_not_mem ps (Or.inr (by
          rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one, sub_mul, one_mul, hNδ]
          linarith [ht.2]))]
    have hη' : ∀ j : Fin N, ∀ y, |y - (j : ℕ) * δ| ≤ δ →
        ‖refSolD ps z t y - refSolD ps z t ((j : ℕ) * δ)‖ ≤ η := by
      intro j y hy
      have hj0 : (0 : ℝ) ≤ (j : ℕ) * δ := by positivity
      have hjL : ((j : ℕ) : ℝ) * δ ≤ L := by
        rw [← hNδ]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast j.isLt.le) hδ.le
      have hy' := abs_le.1 hy
      have hmem1 : ((t, y, z) : ℝ × ℝ × ℂ) ∈ K :=
        ⟨ht, ⟨by linarith [hy'.1], by linarith [hy'.2]⟩, hz⟩
      have hmem2 : ((t, (j : ℕ) * δ, z) : ℝ × ℝ × ℂ) ∈ K :=
        ⟨ht, ⟨by linarith, by linarith⟩, hz⟩
      have hdist : dist ((t, y, z) : ℝ × ℝ × ℂ) (t, (j : ℕ) * δ, z) < δ0 := by
        rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, Real.dist_eq,
          max_eq_left (abs_nonneg (y - ((j : ℕ) : ℝ) * δ)),
          max_eq_right (abs_nonneg (y - ((j : ℕ) : ℝ) * δ))]
        linarith
      have := hδ0K _ hmem1 _ hmem2 hdist
      rw [dist_eq_norm] at this
      exact this.le
    have := residual_norm_le ps N hN2 hδ hw1 hw2 hη'
    rwa [hNδ] at this
  have hD := duhamel_bound hdiss (τ := τ) (by linarith) hψ hr
  -- identify the initial and final states
  have hψ0 : ψ 0 = ψ0 := by
    simp only [ψ, ψ0]
    congr 1
    funext s
    exact refSol_time_zero ps z s
  have hψτ : ψ τ = sample N δ (fun s => ((bump (s - τ) : ℝ) : ℂ) • endProd ps z e0v) := by
    simp only [ψ]
    congr 1
    funext s
    exact refSol_late ps z (by simp only [pulseStart, hτdef]; linarith) s
  have hexp : NormedSpace.exp (-(Complex.I • (z • X + Y))) =
      NormedSpace.exp ((τ : ℂ) • (-(Complex.I • G))) := by
    congr 1
    simp only [X, Y, hGdef, clockGen]
    module
  rw [hexp]
  set W := NormedSpace.exp ((τ : ℂ) • (-(Complex.I • G)))
  have hmain : ⟪ψh, ψ τ⟫_ℂ = ((σ ^ 2 : ℝ) : ℂ) * ⟪e0v, endProd ps z e0v⟫_ℂ := by
    rw [hψτ, inner_sample_smul N hδ.le (fun s => bump (s - τ)), ← hσh]
  have hU : ⟪e0v, endProd ps z e0v⟫_ℂ = gqspMat V0 Vs (Complex.exp (-Complex.I * h * z)) 0 0 := by
    rw [hps, endProd_gqspPulses h hh.le hV0 Vs hVs z, inner_e0v_toOp]
  have hid : ⟪v, W u⟫_ℂ - ⟪e0v, endProd ps z e0v⟫_ℂ =
      ((σ : ℂ)⁻¹ * (σ : ℂ)⁻¹) * ⟪ψh, W ψ0 - ψ τ⟫_ℂ := by
    have hσC0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    rw [inner_sub_right, hmain]
    simp only [u, v, inner_smul_left, map_smul, inner_smul_right, map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp
  rw [← hU, hid, norm_mul]
  have hinner : ‖⟪ψh, W ψ0 - ψ τ⟫_ℂ‖ ≤ σ * (τ * (Real.sqrt L * η)) := by
    calc ‖⟪ψh, W ψ0 - ψ τ⟫_ℂ‖ ≤ ‖ψh‖ * ‖W ψ0 - ψ τ‖ := norm_inner_le_norm _ _
      _ = σ * ‖ψ τ - W (ψ 0)‖ := by rw [hσh, norm_sub_rev, hψ0]
      _ ≤ σ * (τ * (Real.sqrt L * η)) := mul_le_mul_of_nonneg_left hD hσ.le
  have hσinv : ‖((σ : ℂ)⁻¹ * (σ : ℂ)⁻¹)‖ = σ⁻¹ * σ⁻¹ := by rw [norm_mul, hσC]
  rw [hσinv]
  have hσinv2 : σ⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hσ (by norm_num)]
    nlinarith
  have hsqrtL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  calc σ⁻¹ * σ⁻¹ * ‖⟪ψh, W ψ0 - ψ τ⟫_ℂ‖
      ≤ σ⁻¹ * σ⁻¹ * (σ * (τ * (Real.sqrt L * η))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = σ⁻¹ * (τ * (Real.sqrt L * η)) := by field_simp
    _ ≤ 2 * (τ * (Real.sqrt L * η)) :=
        mul_le_mul_of_nonneg_right hσinv2 (by positivity)
    _ < ε := by
        rw [hηdef]
        have hden : 0 < 4 * τ * Real.sqrt L + 1 := by positivity
        rw [show 2 * (τ * (Real.sqrt L * (ε / (4 * τ * Real.sqrt L + 1)))) =
          (2 * τ * Real.sqrt L * ε) / (4 * τ * Real.sqrt L + 1) by ring, div_lt_iff₀ hden]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ τ) hsqrtL]

/-- **The matrix version of Theorem 1** (unconditional). -/
theorem matrix_theorem1 : MatrixTheorem1Statement :=
  MatrixTheorem1_of_productRealization productRealization

#print axioms LCHSWiener.matrix_theorem1

end LCHSWiener
