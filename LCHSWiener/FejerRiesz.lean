import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

noncomputable section

open Polynomial

namespace LCHSWiener

/-!
# Fejér–Riesz factorization, strictly positive case

Let `g` be a complex polynomial of degree at most `2m` whose values on the unit
circle are `g(w) = w^m t(w)` with `t(w) > 0`.  Then `g(w) = w^m |Q(w)|²` on the
circle for some polynomial `Q` of degree at most `m`.

This is the complementary-polynomial step of the GQSP decomposition
(Section 4.2 of the note).  The proof peels off one pair of roots `r, 1/r̄` at a
time; strict positivity rules out roots on the circle.
-/

/-- The unit circle has infinitely many points. -/
lemma infinite_unitCircle : Set.Infinite {w : ℂ | ‖w‖ = 1} := by
  let f : ℕ → ℂ := fun n => ((1 - (n:ℂ)^2) + 2 * n * Complex.I) / (1 + (n:ℂ)^2)
  have hden : ∀ n : ℕ, (1 + (n:ℂ)^2) ≠ 0 := fun n => by
    have : (0:ℝ) < 1 + (n:ℝ)^2 := by positivity
    exact_mod_cast this.ne'
  have hre : ∀ n : ℕ, (f n).re = 2 / (1 + (n:ℝ)^2) - 1 := by
    intro n
    have h1 : f n = ((((1 - (n:ℝ)^2) / (1 + (n:ℝ)^2) : ℝ)) : ℂ) +
        (((2 * n / (1 + (n:ℝ)^2) : ℝ)) : ℂ) * Complex.I := by
      simp only [f]
      have hd := hden n
      push_cast
      field_simp
    rw [h1]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have : (0:ℝ) < 1 + (n:ℝ)^2 := by positivity
    field_simp
    ring
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg Complex.re hab
    rw [hre, hre] at h
    have ha : (0:ℝ) < 1 + (a:ℝ)^2 := by positivity
    have hb : (0:ℝ) < 1 + (b:ℝ)^2 := by positivity
    have : (1 + (a:ℝ)^2) = 1 + (b:ℝ)^2 := by
      field_simp at h
      linarith
    have : (a:ℝ)^2 = (b:ℝ)^2 := by linarith
    have : (a:ℝ) = b := by
      have := (sq_eq_sq₀ (Nat.cast_nonneg a) (Nat.cast_nonneg b)).1 this
      exact this
    exact_mod_cast this
  have hmem : ∀ n, f n ∈ {w : ℂ | ‖w‖ = 1} := by
    intro n
    show ‖f n‖ = 1
    simp only [f]
    rw [norm_div]
    have hnum : ‖(1 - (n:ℂ)^2) + 2 * n * Complex.I‖ = 1 + (n:ℝ)^2 := by
      have : (1 - (n:ℂ)^2) + 2 * n * Complex.I =
          (((1 - (n:ℝ)^2) : ℝ) : ℂ) + (((2 * n : ℝ)) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_add_mul_I,
        show (1 - (n:ℝ)^2) ^ 2 + (2 * n) ^ 2 = (1 + (n:ℝ)^2)^2 by ring]
      exact Real.sqrt_sq (by positivity)
    have hdn : ‖(1 + (n:ℂ)^2)‖ = 1 + (n:ℝ)^2 := by
      have : (1 + (n:ℂ)^2) = (((1 + (n:ℝ)^2) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hnum, hdn, div_self (by positivity)]
  exact Set.infinite_of_injective_forall_mem hinj hmem

/-- Two polynomials that agree on the unit circle are equal. -/
lemma poly_eq_of_eq_on_circle {p q : ℂ[X]} (h : ∀ w : ℂ, ‖w‖ = 1 → p.eval w = q.eval w) :
    p = q :=
  Polynomial.eq_of_infinite_eval_eq p q (infinite_unitCircle.mono fun w hw => h w hw)

/-- The conjugate-reflected polynomial `w^N · conj(p(1/w̄))`. -/
def conjRev (N : ℕ) (p : ℂ[X]) : ℂ[X] := reflect N (p.map (starRingEnd ℂ))

lemma eval_conjRev_mul_pow (N : ℕ) {p : ℂ[X]} (hp : p.natDegree ≤ N) {x : ℂ} (hx : x ≠ 0) :
    (conjRev N p).eval x⁻¹ * x ^ N = starRingEnd ℂ (p.eval (starRingEnd ℂ x)) := by
  let _ : Invertible x := invertibleOfNonzero hx
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) x N (p.map (starRingEnd ℂ))
    (by rw [natDegree_map]; exact hp)
  simp only [eval₂_id, invOf_eq_inv] at h
  rw [conjRev, h, eval_map, Polynomial.eval, Polynomial.hom_eval₂]
  simp

lemma conj_eq_inv_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : starRingEnd ℂ w = w⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]
  simp

lemma eval_conjRev_circle (N : ℕ) {p : ℂ[X]} (hp : p.natDegree ≤ N) {w : ℂ} (hw : ‖w‖ = 1) :
    (conjRev N p).eval w = w ^ N * starRingEnd ℂ (p.eval w) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hx : starRingEnd ℂ w ≠ 0 := by simpa using hw0
  have h := eval_conjRev_mul_pow N hp hx
  rw [Complex.conj_conj, conj_eq_inv_of_norm_one hw, inv_inv] at h
  have hwN : w ^ N * w⁻¹ ^ N = 1 := by rw [← mul_pow, mul_inv_cancel₀ hw0, one_pow]
  calc (conjRev N p).eval w = (conjRev N p).eval w * (w ^ N * w⁻¹ ^ N) := by rw [hwN, mul_one]
    _ = w ^ N * ((conjRev N p).eval w * w⁻¹ ^ N) := by ring
    _ = w ^ N * starRingEnd ℂ (p.eval w) := by rw [h]

lemma natDegree_conjRev_le (N : ℕ) {p : ℂ[X]} (hp : p.natDegree ≤ N) :
    (conjRev N p).natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [conjRev, coeff_reflect, revAt_eq_self_of_lt hi, coeff_map]
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hi), map_zero]

/-- The hypothesis of the strict Fejér–Riesz lemma: `g(w) = w^m t` with `t > 0`
on the unit circle. -/
def CirclePositive (m : ℕ) (g : ℂ[X]) : Prop :=
  ∀ w : ℂ, ‖w‖ = 1 → ∃ t : ℝ, 0 < t ∧ g.eval w = w ^ m * t

/-- Circle positivity forces the self-reciprocity `conjRev (2m) g = g`. -/
lemma conjRev_eq_self {m : ℕ} {g : ℂ[X]} (hdeg : g.natDegree ≤ 2 * m)
    (hpos : CirclePositive m g) : conjRev (2 * m) g = g := by
  refine poly_eq_of_eq_on_circle fun w hw => ?_
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  obtain ⟨t, _, ht⟩ := hpos w hw
  rw [eval_conjRev_circle _ hdeg hw, ht, map_mul, map_pow, conj_eq_inv_of_norm_one hw,
    Complex.conj_ofReal]
  have : w ^ (2 * m) * w⁻¹ ^ m = w ^ m := by
    rw [pow_mul', inv_pow, sq]
    field_simp
  linear_combination (t : ℂ) * this

/-- Roots of a self-reciprocal polynomial come in pairs `r, 1/r̄`. -/
lemma eval_inv_conj_eq_zero {N : ℕ} {g : ℂ[X]} (hdeg : g.natDegree ≤ N)
    (hsr : conjRev N g = g) {r : ℂ} (hr0 : r ≠ 0) (hroot : g.eval r = 0) :
    g.eval (starRingEnd ℂ r)⁻¹ = 0 := by
  have hx : starRingEnd ℂ r ≠ 0 := by simpa using hr0
  have h := eval_conjRev_mul_pow N hdeg hx
  rw [Complex.conj_conj, hroot, map_zero, hsr] at h
  exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ hx)

/-- **Fejér–Riesz, strictly positive case.** -/
theorem fejer_riesz_strict (m : ℕ) : ∀ g : ℂ[X], g.natDegree ≤ 2 * m → CirclePositive m g →
    ∃ Q : ℂ[X], Q.natDegree ≤ m ∧
      ∀ w : ℂ, ‖w‖ = 1 → g.eval w = w ^ m * ((‖Q.eval w‖ ^ 2 : ℝ) : ℂ) := by
  induction m with
  | zero =>
    intro g hdeg hpos
    have hg : g = C (g.coeff 0) := eq_C_of_natDegree_le_zero (by simpa using hdeg)
    obtain ⟨t, ht, h1⟩ := hpos 1 (by simp)
    rw [hg] at h1
    simp only [eval_C, one_pow, one_mul] at h1
    refine ⟨C (Real.sqrt t : ℂ), by simp, fun w _ => ?_⟩
    rw [hg, eval_C, eval_C, h1, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt ht.le]
    simp
  | succ m ih =>
    intro g hdeg hpos
    have hsr := conjRev_eq_self hdeg hpos
    have hne : ∀ w : ℂ, ‖w‖ = 1 → g.eval w ≠ 0 := by
      intro w hw h0
      obtain ⟨t, ht, htw⟩ := hpos w hw
      have hw0 : w ≠ 0 := by rintro rfl; simp at hw
      rw [htw] at h0
      exact (mul_ne_zero (pow_ne_zero _ hw0) (by exact_mod_cast ht.ne')) h0
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hne 1 (by simp) (by simp)
    by_cases hA : ∃ r : ℂ, r ≠ 0 ∧ g.eval r = 0
    · -- peel off the pair of roots `r, s = 1/r̄`
      obtain ⟨r, hr0, hroot⟩ := hA
      have hr1 : ‖r‖ ≠ 1 := fun h => hne r h hroot
      set s : ℂ := (starRingEnd ℂ r)⁻¹ with hsdef
      have hsroot : g.eval s = 0 := eval_inv_conj_eq_zero hdeg hsr hr0 hroot
      have hcr0 : starRingEnd ℂ r ≠ 0 := by simpa using hr0
      have hsr' : s ≠ r := by
        intro h
        apply hr1
        have h' : (starRingEnd ℂ r)⁻¹ = r := h
        have : starRingEnd ℂ r * r = 1 := by
          calc starRingEnd ℂ r * r = starRingEnd ℂ r * (starRingEnd ℂ r)⁻¹ := by rw [h']
            _ = 1 := mul_inv_cancel₀ hcr0
        rw [← Complex.normSq_eq_conj_mul_self] at this
        have h2 : ‖r‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast this
        nlinarith [norm_nonneg r]
      obtain ⟨g1, hg1⟩ : ∃ g1, g = (X - C r) * g1 :=
        ⟨g /ₘ (X - C r), (mul_divByMonic_eq_iff_isRoot.2 hroot).symm⟩
      have hg1s : g1.eval s = 0 := by
        have := hsroot
        rw [hg1, eval_mul] at this
        exact (mul_eq_zero.1 this).resolve_left (by simp [sub_eq_zero, hsr'])
      obtain ⟨g2, hg2⟩ : ∃ g2, g1 = (X - C s) * g2 :=
        ⟨g1 /ₘ (X - C s), (mul_divByMonic_eq_iff_isRoot.2 hg1s).symm⟩
      have hg2ne : g2 ≠ 0 := by rintro rfl; apply hg0; rw [hg1, hg2]; simp
      have hdeg2 : g2.natDegree ≤ 2 * m := by
        have h := hdeg
        rw [hg1, hg2, natDegree_mul (X_sub_C_ne_zero r) (mul_ne_zero (X_sub_C_ne_zero s) hg2ne),
          natDegree_mul (X_sub_C_ne_zero s) hg2ne, natDegree_X_sub_C, natDegree_X_sub_C] at h
        omega
      have hcr : starRingEnd ℂ r ≠ 0 := by simpa using hr0
      let g3 : ℂ[X] := C (-(starRingEnd ℂ r))⁻¹ * g2
      have hdeg3 : g3.natDegree ≤ 2 * m := by
        refine (natDegree_C_mul_le _ _).trans hdeg2
      -- the key identity on the circle
      have hcirc : ∀ w : ℂ, ‖w‖ = 1 →
          g.eval w = w * (Complex.normSq (w - r) : ℂ) * g3.eval w := by
        intro w hw
        have hw0 : w ≠ 0 := by rintro rfl; simp at hw
        have hcw := conj_eq_inv_of_norm_one hw
        rw [hg1, hg2]
        simp only [g3, eval_mul, eval_sub, eval_X, eval_C]
        rw [Complex.normSq_eq_conj_mul_self, map_sub, hcw, hsdef]
        field_simp
        ring
      have hpos3 : CirclePositive m g3 := by
        intro w hw
        have hw0 : w ≠ 0 := by rintro rfl; simp at hw
        obtain ⟨t, ht, htw⟩ := hpos w hw
        have hwr : w - r ≠ 0 := by
          intro h
          apply hr1
          rw [← sub_eq_zero.1 h, hw]
        have hns : 0 < Complex.normSq (w - r) := Complex.normSq_pos.2 hwr
        refine ⟨t / Complex.normSq (w - r), div_pos ht hns, ?_⟩
        have h := hcirc w hw
        rw [htw] at h
        have hns' : (Complex.normSq (w - r) : ℂ) ≠ 0 := by exact_mod_cast hns.ne'
        rw [pow_succ] at h
        have hne2 : w * (Complex.normSq (w - r) : ℂ) ≠ 0 := mul_ne_zero hw0 hns'
        refine mul_left_cancel₀ hne2 ?_
        rw [← h]
        push_cast
        field_simp
      obtain ⟨Q3, hQ3deg, hQ3⟩ := ih g3 hdeg3 hpos3
      refine ⟨(X - C r) * Q3, ?_, fun w hw => ?_⟩
      · refine (natDegree_mul_le).trans ?_
        rw [natDegree_X_sub_C]
        omega
      · rw [hcirc w hw, hQ3 w hw, eval_mul, eval_sub, eval_X, eval_C, norm_mul, mul_pow,
          Complex.normSq_eq_norm_sq, pow_succ]
        push_cast
        ring
    · -- all roots are `0`: `g = c X^a`, and self-reciprocity forces `a = m+1`
      push Not at hA
      obtain ⟨q, hq, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd g hg0 0
      set a := rootMultiplicity 0 g
      have hq0 : q.eval 0 ≠ 0 := by
        intro h; apply hndvd; exact dvd_iff_isRoot.2 h
      have hqdeg : q.natDegree = 0 := by
        by_contra hpos'
        obtain ⟨z, hz⟩ := Complex.exists_root (degree_pos_of_ne_zero_of_nonunit (p := q)
          (by intro h0; rw [h0] at hq0; simp at hq0) (by
            intro hu
            exact hpos' (natDegree_eq_zero_of_isUnit hu)))
        have hz0 : z ≠ 0 := by rintro rfl; exact hq0 hz
        apply hA z hz0
        rw [hq, eval_mul, IsRoot.def.1 hz, mul_zero]
      have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hqdeg
      set c := q.coeff 0
      have hc0 : c ≠ 0 := by
        intro h; apply hq0; rw [hqC, eval_C]; exact h
      have hgform : g = C c * X ^ a := by rw [hq, hqC, map_zero, sub_zero, mul_comm]
      have ha : a = m + 1 := by
        have hadeg : a ≤ 2 * (m + 1) := by
          have := hdeg
          rw [hgform, natDegree_C_mul_X_pow a c hc0] at this
          exact this
        have h := hsr
        rw [hgform, conjRev, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
          reflect_C_mul_X_pow, revAt_le hadeg] at h
        have hco := congrArg (fun p : ℂ[X] => p.coeff a) h
        simp only [coeff_C_mul_X_pow] at hco
        by_contra hne'
        have : a ≠ 2 * (m + 1) - a := by omega
        have hc : c = 0 := by simpa [this, eq_comm] using hco
        exact hc0 hc
      obtain ⟨t, ht, h1⟩ := hpos 1 (by simp)
      rw [hgform] at h1
      simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one, one_mul] at h1
      refine ⟨C (Real.sqrt t : ℂ), by simp, fun w _ => ?_⟩
      rw [hgform, ha, eval_mul, eval_C, eval_pow, eval_X, eval_C, h1, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ht.le]
      ring

end LCHSWiener
