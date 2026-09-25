import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open Set

namespace LCHSWiener

/-- `p_R = 2/pi * arctan R`. -/
def pR (R : ℝ) : ℝ := 2 * Real.arctan R / Real.pi

/-- `q_R = 1 - p_R`. -/
def qR (R : ℝ) : ℝ := 1 - pR R

lemma pR_pos {R : ℝ} (hR : 0 < R) : 0 < pR R := by
  rw [pR]
  have ha : 0 < Real.arctan R := (Real.arctan_pos).2 hR
  positivity

lemma pR_lt_one {R : ℝ} (hR : 0 < R) : pR R < 1 := by
  rw [pR]
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : Real.arctan R < Real.pi / 2 := Real.arctan_lt_pi_div_two R
  rw [div_lt_iff₀ hpi]
  linarith

lemma pR_le_one {R : ℝ} (hR : 0 < R) : pR R ≤ 1 := (pR_lt_one hR).le

lemma qR_pos {R : ℝ} (hR : 0 < R) : 0 < qR R := by
  rw [qR]
  linarith [pR_lt_one hR]

lemma pR_add_qR (R : ℝ) : pR R + qR R = 1 := by simp [qR]

lemma qR_eq_arctan_inv {R : ℝ} (hR : 0 < R) :
    qR R = 2 * Real.arctan R⁻¹ / Real.pi := by
  rw [qR, pR, Real.arctan_inv_of_pos hR]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hpi]

lemma pR_continuous : Continuous pR := by
  unfold pR
  fun_prop

lemma qR_continuous : Continuous qR := by
  change Continuous (fun R => 1 - pR R)
  exact continuous_const.sub pR_continuous

/-- The sharp piecewise value appearing in the theorem. -/
def sharpValue (p q lam : ℝ) : ℝ :=
  if lam ≤ p then 1 - lam else q * (p / lam) ^ (p / q)

/-- Algebra at the high-mass test point `a=(p/lam)^(1/q)`. -/
lemma high_test_point
    {p q lam : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1)
    (hlam : p ≤ lam) :
    let a : ℝ := (p / lam) ^ q⁻¹
    0 < a ∧ a ≤ 1 ∧
      a ^ p - a * lam = q * (p / lam) ^ (p / q) := by
  have hlampos : 0 < lam := lt_of_lt_of_le hp hlam
  have hx : 0 < p / lam := div_pos hp hlampos
  have hx0 : 0 ≤ p / lam := hx.le
  have hx1 : p / lam ≤ 1 := (div_le_one hlampos).2 hlam
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hlam0 : lam ≠ 0 := ne_of_gt hlampos
  have hqinv : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  let a : ℝ := (p / lam) ^ q⁻¹
  have ha0 : 0 < a := by
    dsimp [a]
    exact Real.rpow_pos_of_pos hx _
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact Real.rpow_le_one hx0 hx1 hqinv
  have hexp_mul : q⁻¹ * p = p / q := by
    simp [div_eq_mul_inv, mul_comm]
  have hap : a ^ p = (p / lam) ^ (p / q) := by
    dsimp [a]
    calc
      ((p / lam) ^ q⁻¹) ^ p = (p / lam) ^ (q⁻¹ * p) :=
        (Real.rpow_mul hx0 q⁻¹ p).symm
      _ = (p / lam) ^ (p / q) := by rw [hexp_mul]
  have hexp_split : q⁻¹ = p / q + 1 := by
    field_simp [hq0]
    linarith
  have hxlam : (p / lam) * lam = p := by field_simp [hlam0]
  refine ⟨ha0, ha1, ?_⟩
  rw [hap, hexp_split, Real.rpow_add hx]
  simp only [Real.rpow_one]
  rw [mul_assoc, hxlam]
  have hqeq : q = 1 - p := by linarith
  rw [hqeq]
  ring

/--
Order-theoretic minimax lemma with approximate upper witnesses.  This is the
form naturally produced by the `s ↓ 0` regularisation in the Wiener proof.
-/
theorem wiener_minimax_of_sharp_bounds
    {costs : ℝ → Set ℝ} {p q lam : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1)
    (hlam0 : 0 ≤ lam)
    (lower_lo : lam ≤ p → ∀ e ∈ costs lam, 1 - lam ≤ e)
    (lower_hi : p ≤ lam → ∀ e ∈ costs lam,
      q * (p / lam) ^ (p / q) ≤ e)
    (upper_lo : lam ≤ p → ∀ eps > 0, ∃ e ∈ costs lam, e < 1 - lam + eps)
    (upper_hi : p ≤ lam → ∀ eps > 0, ∃ e ∈ costs lam,
      e < q * (p / lam) ^ (p / q) + eps) :
    sInf (costs lam) = sharpValue p q lam := by
  by_cases hlamp : lam ≤ p
  · rw [sharpValue, if_pos hlamp]
    obtain ⟨e0, he0, _⟩ := upper_lo hlamp 1 zero_lt_one
    have hne : (costs lam).Nonempty := ⟨e0, he0⟩
    have hbdd : BddBelow (costs lam) := by
      refine ⟨1 - lam, ?_⟩
      intro x hx
      exact lower_lo hlamp x hx
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro eps heps
      obtain ⟨e, he, hlt⟩ := upper_lo hlamp eps heps
      exact (csInf_le hbdd he).trans hlt.le
    · apply le_csInf hne
      intro x hx
      exact lower_lo hlamp x hx
  · have hplam : p ≤ lam := le_of_not_ge hlamp
    rw [sharpValue, if_neg hlamp]
    obtain ⟨e0, he0, _⟩ := upper_hi hplam 1 zero_lt_one
    have hne : (costs lam).Nonempty := ⟨e0, he0⟩
    have hbdd : BddBelow (costs lam) := by
      refine ⟨q * (p / lam) ^ (p / q), ?_⟩
      intro x hx
      exact lower_hi hplam x hx
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro eps heps
      obtain ⟨e, he, hlt⟩ := upper_hi hplam eps heps
      exact (csInf_le hbdd he).trans hlt.le
    · apply le_csInf hne
      intro x hx
      exact lower_hi hplam x hx

end LCHSWiener
