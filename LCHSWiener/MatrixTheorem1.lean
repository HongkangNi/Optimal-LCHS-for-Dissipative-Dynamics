import LCHSWiener.MatrixLowerBound
import LCHSWiener.MatrixTarget

noncomputable section

namespace LCHSWiener

/-!
# The matrix version of Theorem 1, assuming the realization lemma

The upper bound (explicit kernels and the matrix LCHS identity) is proved
unconditionally in `MatrixLCHS.lean`.  The lower bound uses the realization
lemma of Section 4 (`RealizationLemma`), which is still to be formalized; this
file shows that it is the only missing ingredient.
-/

/-- Matrix version of Section 3, Theorem 1, assuming the realization lemma. -/
theorem matrix_theorem1_of_realization (hreal : RealizationLemma)
    (R lam : ℝ) (hR : 0 < R) (hlam0 : 0 ≤ lam) :
    matrixMinimax R lam = sharpValue (pR R) (qR R) lam := by
  unfold matrixMinimax
  have hp := pR_pos hR
  have hq := qR_pos hR
  apply wiener_minimax_of_sharp_bounds (costs := matrixCosts R) (p := pR R) (q := qR R)
    (lam := lam) hp hq (pR_add_qR R) hlam0
  · intro _ e he
    exact matrix_lower_low hreal hR he
  · intro hlam e he
    exact matrix_lower_high hreal hR hlam he
  · intro hlam eps heps
    obtain ⟨μ, hsupp, htv, herr⟩ := matrix_low_witness hR hlam0 hlam
    exact ⟨matrixError μ, ⟨μ, hsupp, htv, rfl⟩, by linarith⟩
  · intro hlam eps heps
    have hlampos : 0 < lam := lt_of_lt_of_le hp hlam
    let C : ℝ := Real.log (lam / pR R) / (Real.pi * qR R)
    have hratio : 1 ≤ lam / pR R := (le_div_iff₀ hp).2 (by simpa [mul_comm] using hlam)
    have hC : 0 ≤ C :=
      div_nonneg (Real.log_nonneg hratio) (mul_nonneg Real.pi_pos.le hq.le)
    obtain ⟨μ, hsupp, htv, herr⟩ := matrix_outer_kernel_witness hR hC
    have hmuEq : pR R * Real.exp (Real.pi*C*qR R) = lam := by
      rw [show Real.pi*C*qR R = Real.log (lam/pR R) by
        simp only [C]; field_simp [Real.pi_ne_zero, ne_of_gt hq]]
      rw [Real.exp_log (div_pos hlampos hp)]
      field_simp [ne_of_gt hp]
    have hnuEq : qR R * Real.exp (-Real.pi*C*pR R) = qR R * (pR R/lam)^(pR R/qR R) := by
      have hpos : 0 < pR R/lam := div_pos hp hlampos
      rw [show -Real.pi*C*pR R = Real.log (pR R/lam) * (pR R/qR R) by
        simp only [C]
        rw [Real.log_div (ne_of_gt hlampos) (ne_of_gt hp),
          Real.log_div (ne_of_gt hp) (ne_of_gt hlampos)]
        field_simp [Real.pi_ne_zero, ne_of_gt hq]
        ring]
      rw [Real.rpow_def_of_pos hpos]
    refine ⟨matrixError μ, ⟨μ, hsupp, by rw [← hmuEq]; exact htv, rfl⟩, ?_⟩
    rw [← hnuEq]
    linarith

/-- The proposition exported by `MatrixTarget.lean` follows from the realization
lemma. -/
theorem MatrixTheorem1_of_realization (hreal : RealizationLemma) : MatrixTheorem1Statement :=
  fun R lam hR hlam => matrix_theorem1_of_realization hreal R lam hR hlam

#print axioms LCHSWiener.MatrixTheorem1_of_realization

end LCHSWiener
