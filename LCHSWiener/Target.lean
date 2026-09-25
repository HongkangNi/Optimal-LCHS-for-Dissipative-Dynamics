import LCHSWiener.Core
import LCHSWiener.MeasureFourier

noncomputable section

namespace LCHSWiener

/--
The exact Wiener version of Section 3, Theorem 1, stated as a proposition.
The final project goal is to produce a theorem inhabiting this proposition.
-/
def WienerTheorem1Statement : Prop :=
  ∀ (R lam : ℝ), 0 < R → 0 ≤ lam →
    wienerMinimax R lam = sharpValue (pR R) (qR R) lam

end LCHSWiener
