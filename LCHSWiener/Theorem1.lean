import LCHSWiener.Core
import LCHSWiener.MeasureFourier
import LCHSWiener.WienerDualBound
import LCHSWiener.KernelUpperBound
import LCHSWiener.Target

noncomputable section

namespace LCHSWiener

/-- Exact Wiener/Fourier--Stieltjes minimax theorem corresponding to Section 3,
Theorem 1 of the note. -/
theorem wiener_theorem1
    (R lam : ℝ) (hR : 0 < R) (hlam0 : 0 ≤ lam) :
    wienerMinimax R lam = sharpValue (pR R) (qR R) lam := by
  unfold wienerMinimax
  apply wiener_minimax_of_sharp_bounds
    (p := pR R) (q := qR R) (lam := lam)
  · exact pR_pos hR
  · exact qR_pos hR
  · exact pR_add_qR R
  · exact hlam0
  · intro hlam e he
    exact wiener_lower_low hR hlam he
  · intro hlam e he
    exact wiener_lower_high hR hlam he
  · intro hlam eps heps
    exact wiener_upper_low hR hlam0 hlam eps heps
  · intro hlam eps heps
    exact wiener_upper_high hR hlam eps heps

/-- The proposition exported by `Target.lean` is inhabited. -/
theorem WienerTheorem1 : WienerTheorem1Statement := by
  intro R lam hR hlam
  exact wiener_theorem1 R lam hR hlam

#print axioms LCHSWiener.wiener_theorem1
#print axioms LCHSWiener.WienerTheorem1

end LCHSWiener
