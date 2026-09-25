import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open Set
open MeasureTheory
open scoped ENNReal

namespace LCHSWiener

abbrev CMeasure := MeasureTheory.ComplexMeasure ℝ

/-- A complex Borel measure with finite total variation. -/
def FiniteCMeasure := { μ : CMeasure // μ.variation Set.univ ≠ ∞ }

/-- Total-variation norm of a finite complex measure. -/
def tv (μ : FiniteCMeasure) : ℝ :=
  (μ.1.variation Set.univ).toReal

/-- Support condition used in the theorem, expressed via total variation. -/
def SupportedIn (R : ℝ) (μ : FiniteCMeasure) : Prop :=
  μ.1.variation ((Set.Icc (-R) R)ᶜ) = 0

/-- Complex multiplication, viewed as a real continuous bilinear pairing. -/
def cmul : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

/--
Fourier--Stieltjes transform in the convention of the note:
`FS μ x = ∫ exp(-i k x) dμ(k)`.
-/
def fsTransform (μ : FiniteCMeasure) (x : ℝ) : ℂ :=
  ∫ᵛ k : ℝ, Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ)) ∂[cmul; μ.1]

/-- A measure `nu` represents the half-line residual associated to `mu`. -/
def RepresentsResidual (μ ν : FiniteCMeasure) : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    Complex.exp (-(x : ℂ)) - fsTransform μ x = fsTransform ν x

/--
Attainable residual total-variation costs at parameters `(R, lambda)`.
This combines the outer infimum over `mu` with the inner local-Wiener
infimum over representing measures `nu`.
-/
def wienerCosts (R lam : ℝ) : Set ℝ :=
  { e | ∃ μ ν : FiniteCMeasure,
      SupportedIn R μ ∧ tv μ ≤ lam ∧ RepresentsResidual μ ν ∧ tv ν = e }

/-- Exact minimax value for the half-line Fourier--Stieltjes/Wiener problem. -/
def wienerMinimax (R lam : ℝ) : ℝ := sInf (wienerCosts R lam)

end LCHSWiener
