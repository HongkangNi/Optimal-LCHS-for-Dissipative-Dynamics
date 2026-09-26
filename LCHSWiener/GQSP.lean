import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import LCHSWiener.FejerRiesz

noncomputable section

open Polynomial
open scoped Matrix

namespace LCHSWiener

/-!
# Section 4.2: the GQSP decomposition

If `P, Q` are polynomials of degree at most `m` with `|P|² + |Q|² = 1` on the
unit circle, then

  (P(w), Q(w))ᵀ = V_k D(w) V_{k-1} ⋯ D(w) V_0 e₀,   D(w) = diag(w, 1),

for 2×2 unitaries `V_j` (layer stripping).  Together with the strict
Fejér–Riesz lemma this realizes every polynomial with `|P| ≤ 1` on the closed
unit disc, up to an arbitrarily small scaling, as the matrix element
`⟨0| V_k D(w) ⋯ D(w) V_0 |0⟩`.
-/

/-- `2 × 2` complex matrices. -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The signal operator `D(w) = diag(w, 1)`. -/
def gqspD (w : ℂ) : M2 := !![w, 0; 0, 1]

/-- The GQSP product `V_k D(w) V_{k-1} ⋯ D(w) V_0` for the list `[V_k, …, V_1]`. -/
def gqspMat (V0 : M2) : List M2 → ℂ → M2
  | [], _ => V0
  | V :: Vs, w => V * gqspD w * gqspMat V0 Vs w

/-- The basis vector `|0⟩`. -/
def e0 : Fin 2 → ℂ := ![1, 0]

/-- The `SU(2)` matrix `[[α, -β̄], [β, ᾱ]]`. -/
def su2 (α β : ℂ) : M2 := !![α, -starRingEnd ℂ β; β, starRingEnd ℂ α]

/-- `V = [[α, -β̄], [β, ᾱ]]` with `|α|² + |β|² = 1`. -/
def IsSU2 (V : M2) : Prop :=
  ∃ α β : ℂ, Complex.normSq α + Complex.normSq β = 1 ∧ V = su2 α β

/-! ### The coefficient orthogonality -/

/-- From `|P|² + |Q|² = 1` on the circle: `(p₀, q₀) ⊥ (p_N, q_N)`. -/
lemma coeff_orthogonal {N : ℕ} (hN : 1 ≤ N) {P Q : ℂ[X]} (hP : P.natDegree ≤ N)
    (hQ : Q.natDegree ≤ N)
    (hcirc : ∀ w : ℂ, ‖w‖ = 1 → Complex.normSq (P.eval w) + Complex.normSq (Q.eval w) = 1) :
    P.coeff N * starRingEnd ℂ (P.coeff 0) + Q.coeff N * starRingEnd ℂ (Q.coeff 0) = 0 := by
  have hid : P * conjRev N P + Q * conjRev N Q = X ^ N := by
    refine poly_eq_of_eq_on_circle fun w hw => ?_
    rw [eval_add, eval_mul, eval_mul, eval_conjRev_circle N hP hw, eval_conjRev_circle N hQ hw,
      eval_pow, eval_X]
    have h := hcirc w hw
    have h' : ((Complex.normSq (P.eval w) + Complex.normSq (Q.eval w) : ℝ) : ℂ) = 1 := by
      rw [h]; simp
    push_cast at h'
    rw [← Complex.mul_conj, ← Complex.mul_conj] at h'
    linear_combination w ^ N * h'
  have hco := congrArg (fun p : ℂ[X] => p.coeff (N + N)) hid
  simp only [coeff_add, coeff_X_pow] at hco
  rw [coeff_mul_add_eq_of_natDegree_le hP (natDegree_conjRev_le N hP),
    coeff_mul_add_eq_of_natDegree_le hQ (natDegree_conjRev_le N hQ)] at hco
  have hrev : ∀ p : ℂ[X], (conjRev N p).coeff N = starRingEnd ℂ (p.coeff 0) := by
    intro p
    rw [conjRev, coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_map]
  rw [hrev, hrev] at hco
  simp only [show ¬ (N + N = N) by omega, ite_false] at hco
  exact hco

/-! ### Algebra of the stripping rotation -/

lemma normSq_rotation (a1 a2 x y : ℂ) :
    Complex.normSq (starRingEnd ℂ a1 * x + starRingEnd ℂ a2 * y) +
      Complex.normSq (-a2 * x + a1 * y) =
    (Complex.normSq a1 + Complex.normSq a2) * (Complex.normSq x + Complex.normSq y) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

/-- The unitary `(1/n) [[a₁, -ā₂], [a₂, ā₁]]`. -/
def stripRot (a1 a2 : ℂ) (n : ℝ) : M2 :=
  !![a1 / n, -starRingEnd ℂ a2 / n; a2 / n, starRingEnd ℂ a1 / n]

lemma stripRot_mem_unitary {a1 a2 : ℂ} {n : ℝ} (hn : 0 < n)
    (hn2 : n ^ 2 = Complex.normSq a1 + Complex.normSq a2) :
    stripRot a1 a2 n ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn2' : (n : ℂ) ^ 2 = starRingEnd ℂ a1 * a1 + starRingEnd ℂ a2 * a2 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast hn2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stripRot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.conj_ofReal] <;>
    (try field_simp) <;> (try rw [hn2']) <;> ring

/-! ### Layer stripping -/

/-- **GQSP decomposition** by layer stripping. -/
theorem gqsp_decomposition (m : ℕ) : ∀ P Q : ℂ[X], P.natDegree ≤ m → Q.natDegree ≤ m →
    (∀ w : ℂ, ‖w‖ = 1 → Complex.normSq (P.eval w) + Complex.normSq (Q.eval w) = 1) →
    ∃ (V0 : M2) (Vs : List M2), V0 ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (∀ V ∈ Vs, V ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ IsSU2 V0 ∧ (∀ V ∈ Vs, IsSU2 V) ∧
      ∀ w : ℂ, gqspMat V0 Vs w *ᵥ e0 = ![P.eval w, Q.eval w] := by
  induction m with
  | zero =>
    intro P Q hP hQ hcirc
    have hPC : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero hP
    have hQC : Q = C (Q.coeff 0) := eq_C_of_natDegree_le_zero hQ
    set p := P.coeff 0
    set q := Q.coeff 0
    have h1 := hcirc 1 (by simp)
    rw [hPC, hQC, eval_C, eval_C] at h1
    refine ⟨!![p, -starRingEnd ℂ q; q, starRingEnd ℂ p], [], ?_, by simp, ⟨p, q, h1, rfl⟩,
      by simp, fun w => ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      have h1' : starRingEnd ℂ p * p + starRingEnd ℂ q * q = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
        exact_mod_cast h1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
        (try rw [← h1']) <;> ring
    · rw [hPC, hQC]
      ext i
      fin_cases i <;> simp [gqspMat, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | succ m ih =>
    intro P Q hP hQ hcirc
    set a1 := P.coeff (m + 1)
    set a2 := Q.coeff (m + 1)
    by_cases ha : a1 = 0 ∧ a2 = 0
    · have hlow : ∀ R : ℂ[X], R.natDegree ≤ m + 1 → R.coeff (m + 1) = 0 → R.natDegree ≤ m := by
        intro R hR hc
        rw [natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rcases Nat.lt_or_ge (m + 1) N with h | h
        · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hR h)
        · have : N = m + 1 := by omega
          rw [this]; exact hc
      exact ih P Q (hlow P hP ha.1) (hlow Q hQ ha.2) hcirc
    · -- the stripping rotation
      have hA : 0 < Complex.normSq a1 + Complex.normSq a2 := by
        by_contra hle
        push Not at hle
        apply ha
        constructor
        · exact Complex.normSq_eq_zero.1 (le_antisymm (by linarith [Complex.normSq_nonneg a2])
            (Complex.normSq_nonneg _))
        · exact Complex.normSq_eq_zero.1 (le_antisymm (by linarith [Complex.normSq_nonneg a1])
            (Complex.normSq_nonneg _))
      set n : ℝ := Real.sqrt (Complex.normSq a1 + Complex.normSq a2)
      have hn : 0 < n := Real.sqrt_pos.2 hA
      have hn2 : n ^ 2 = Complex.normSq a1 + Complex.normSq a2 := Real.sq_sqrt hA.le
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      set P' : ℂ[X] := C (starRingEnd ℂ a1 / n) * P + C (starRingEnd ℂ a2 / n) * Q
      set Q' : ℂ[X] := C (-a2 / n) * P + C (a1 / n) * Q
      have horth := coeff_orthogonal (N := m + 1) (by omega) hP hQ hcirc
      have hP'0 : P'.coeff 0 = 0 := by
        simp only [P', coeff_add, coeff_C_mul]
        have := congrArg (starRingEnd ℂ) horth
        simp only [map_add, map_mul, Complex.conj_conj, map_zero] at this
        field_simp
        linear_combination this
      have hQ'top : Q'.coeff (m + 1) = 0 := by
        simp only [Q', coeff_add, coeff_C_mul]
        field_simp
        ring
      have hdegP' : P'.natDegree ≤ m + 1 :=
        (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hP)
          ((natDegree_C_mul_le _ _).trans hQ))
      have hdegQ' : Q'.natDegree ≤ m := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rcases Nat.lt_or_ge (m + 1) N with h | h
        · refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ h)
          exact (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hP)
            ((natDegree_C_mul_le _ _).trans hQ))
        · have : N = m + 1 := by omega
          rw [this]; exact hQ'top
      have hPsplit : P' = divX P' * X := by
        have := divX_mul_X_add P'
        rw [hP'0, map_zero, add_zero] at this
        exact this.symm
      have hdegP'' : (divX P').natDegree ≤ m := by
        rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      -- the reduced pair still satisfies the circle identity
      have hcirc' : ∀ w : ℂ, ‖w‖ = 1 →
          Complex.normSq ((divX P').eval w) + Complex.normSq (Q'.eval w) = 1 := by
        intro w hw
        have hw1 : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
        have hPw : Complex.normSq ((divX P').eval w) = Complex.normSq (P'.eval w) := by
          conv_rhs => rw [hPsplit]
          rw [eval_mul, eval_X, Complex.normSq_mul, hw1, mul_one]
        rw [hPw]
        have hrot := normSq_rotation a1 a2 (P.eval w) (Q.eval w)
        rw [hcirc w hw, mul_one, ← hn2] at hrot
        have hPe : P'.eval w = (starRingEnd ℂ a1 * P.eval w + starRingEnd ℂ a2 * Q.eval w) / n := by
          simp only [P', eval_add, eval_mul, eval_C]; ring
        have hQe : Q'.eval w = (-a2 * P.eval w + a1 * Q.eval w) / n := by
          simp only [Q', eval_add, eval_mul, eval_C]; ring
        rw [hPe, hQe, Complex.normSq_div, Complex.normSq_div, Complex.normSq_ofReal, ← add_div,
          hrot, sq, div_self (mul_ne_zero hn.ne' hn.ne')]
      obtain ⟨V0, Vs, hV0, hVs, hS0, hSs, hrep⟩ := ih (divX P') Q' hdegP'' hdegQ' hcirc'
      refine ⟨V0, stripRot a1 a2 n :: Vs, hV0, ?_, hS0, ?_, fun w => ?_⟩
      · intro V hV
        rcases List.mem_cons.1 hV with h | h
        · rw [h]; exact stripRot_mem_unitary hn hn2
        · exact hVs V h
      · intro V hV
        rcases List.mem_cons.1 hV with h | h
        · rw [h]
          refine ⟨a1 / n, a2 / n, ?_, ?_⟩
          · rw [Complex.normSq_div, Complex.normSq_div, Complex.normSq_ofReal, ← add_div, ← hn2,
              sq, div_self (mul_ne_zero hn.ne' hn.ne')]
          · ext i j
            fin_cases i <;> fin_cases j <;> simp [stripRot, su2, map_div₀, Complex.conj_ofReal]
            ring
        · exact hSs V h
      · have hstep : gqspMat V0 (stripRot a1 a2 n :: Vs) w *ᵥ e0 =
            stripRot a1 a2 n *ᵥ (gqspD w *ᵥ (gqspMat V0 Vs w *ᵥ e0)) := by
          simp only [gqspMat, Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hstep, hrep]
        have hn2c : (n : ℂ) ^ 2 = starRingEnd ℂ a1 * a1 + starRingEnd ℂ a2 * a2 := by
          rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
          exact_mod_cast hn2
        have hPw : P'.eval w = (divX P').eval w * w := by
          conv_lhs => rw [hPsplit]
          rw [eval_mul, eval_X]
        have hPe : P'.eval w = (starRingEnd ℂ a1 * P.eval w + starRingEnd ℂ a2 * Q.eval w) / n := by
          simp only [P', eval_add, eval_mul, eval_C]; ring
        have hQe : Q'.eval w = (-a2 * P.eval w + a1 * Q.eval w) / n := by
          simp only [Q', eval_add, eval_mul, eval_C]; ring
        ext i
        fin_cases i
        · simp only [gqspD, stripRot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          simp
          rw [mul_comm w, ← hPw, hPe, hQe]
          field_simp
          linear_combination (-(P.eval w)) * hn2c
        · simp only [gqspD, stripRot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          simp
          rw [mul_comm w, ← hPw, hPe, hQe]
          field_simp
          linear_combination (-(Q.eval w)) * hn2c

lemma gqspMat_mulVec_e0_zero (M : M2) : (M *ᵥ e0) 0 = M 0 0 := by
  simp [e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Section 4.2.**  Every polynomial with `|P| ≤ 1` on the closed unit disc is,
up to `ε`, the GQSP matrix element `⟨0| V_k D(w) ⋯ D(w) V_0 |0⟩`. -/
theorem gqsp_of_schur {P : ℂ[X]} (hP : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖P.eval w‖ ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ (V0 : M2) (Vs : List M2), V0 ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      (∀ V ∈ Vs, V ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ IsSU2 V0 ∧ (∀ V ∈ Vs, IsSU2 V) ∧
      ∀ w : ℂ, ‖w‖ ≤ 1 → ‖gqspMat V0 Vs w 0 0 - P.eval w‖ ≤ ε := by
  set m := P.natDegree
  set P1 : ℂ[X] := C ((1 - ε : ℝ) : ℂ) * P
  have hdeg1 : P1.natDegree ≤ m := natDegree_C_mul_le _ _
  set g : ℂ[X] := X ^ m - P1 * conjRev m P1
  have hdegg : g.natDegree ≤ 2 * m := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_X_pow]; omega
    · refine natDegree_mul_le.trans ?_
      have := natDegree_conjRev_le m hdeg1
      omega
  have hP1eval : ∀ w, P1.eval w = ((1 - ε : ℝ) : ℂ) * P.eval w := fun w => by simp [P1]
  have hP1sq : ∀ w : ℂ, ‖w‖ = 1 → Complex.normSq (P1.eval w) ≤ (1 - ε) ^ 2 := by
    intro w hw
    rw [hP1eval, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
    have h1 := hP w hw.le
    have : ‖P.eval w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (P.eval w)]
    nlinarith
  have hgw : ∀ w : ℂ, ‖w‖ = 1 → g.eval w = w ^ m * ((1 - Complex.normSq (P1.eval w) : ℝ) : ℂ) := by
    intro w hw
    rw [eval_sub, eval_mul, eval_conjRev_circle m hdeg1 hw, eval_pow, eval_X]
    push_cast
    rw [← Complex.mul_conj]
    ring
  have hpos : CirclePositive m g := by
    intro w hw
    refine ⟨1 - Complex.normSq (P1.eval w), ?_, hgw w hw⟩
    have := hP1sq w hw
    nlinarith
  obtain ⟨Q, hQdeg, hQ⟩ := fejer_riesz_strict m g hdegg hpos
  have hcirc : ∀ w : ℂ, ‖w‖ = 1 →
      Complex.normSq (P1.eval w) + Complex.normSq (Q.eval w) = 1 := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have h := hQ w hw
    rw [hgw w hw] at h
    have h2 := mul_left_cancel₀ (pow_ne_zero m hw0) h
    have h3 : (1 - Complex.normSq (P1.eval w)) = ‖Q.eval w‖ ^ 2 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq (Q.eval w)]
    linarith
  obtain ⟨V0, Vs, hV0, hVs, hS0, hSs, hrep⟩ := gqsp_decomposition m P1 Q hdeg1 hQdeg hcirc
  refine ⟨V0, Vs, hV0, hVs, hS0, hSs, fun w hw => ?_⟩
  have h0 : gqspMat V0 Vs w 0 0 = P1.eval w := by
    rw [← gqspMat_mulVec_e0_zero (gqspMat V0 Vs w), hrep]
    simp
  rw [h0, hP1eval]
  have : ((1 - ε : ℝ) : ℂ) * P.eval w - P.eval w = -((ε : ℂ) * P.eval w) := by push_cast; ring
  rw [this, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left (hP w hw) hε.le).trans (le_of_eq (mul_one ε))

end LCHSWiener
