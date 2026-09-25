import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.Exponential
import LCHSWiener.Core
import LCHSWiener.MeasureFourier

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace LCHSWiener

/-!
# The matrix (operator) version of Section 3, Theorem 1

This file only contains definitions.  `MatrixTheorem1Statement` is the
matrix-model version of Theorem 1 of the note, eq. (3.3):

  inf_{supp μ ⊂ [-R,R], ‖μ‖_TV ≤ λ} 𝓔(μ) = sharpValue,
  𝓔(μ) = sup_{d, X ⪰ 0, Y = Y*} ‖e^{-(X+iY)} - ∫ e^{-i(kX+Y)} dμ(k)‖,

where `X, Y` range over `d × d` complex matrices (operators on `ℂ^d`) of every
finite dimension `d`, and the norm is the operator norm.

`RealizationLemma` is the "实现引理" of Section 4 of the note.
-/

/-- The Hilbert space `ℂ^d`. -/
abbrev Hd (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Linear operators on `ℂ^d`, i.e. `d × d` complex matrices, with the operator
norm. -/
abbrev Op (d : ℕ) := Hd d →L[ℂ] Hd d

/-- The pairing `(T, c) ↦ c • T`, used to integrate operator-valued functions
against a complex measure. -/
def smulPairing (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : E →L[ℝ] ℂ →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).flip

/-- `∫ e^{-i(kX+Y)} dμ(k)`. -/
def lchsIntegral {d : ℕ} (μ : FiniteCMeasure) (X Y : Op d) : Op d :=
  ∫ᵛ k : ℝ, NormedSpace.exp (-(Complex.I • ((k:ℂ) • X + Y))) ∂[smulPairing (Op d); μ.1]

/-- The LCHS residual `e^{-(X+iY)} - ∫ e^{-i(kX+Y)} dμ(k)`. -/
def lchsResidual {d : ℕ} (μ : FiniteCMeasure) (X Y : Op d) : Op d :=
  NormedSpace.exp (-(X + Complex.I • Y)) - lchsIntegral μ X Y

/-- All residual norms over every dimension `d`, every `X ⪰ 0` and every
self-adjoint `Y`. -/
def matrixErrorSet (μ : FiniteCMeasure) : Set ℝ :=
  { e | ∃ (d : ℕ) (X Y : Op d), X.IsPositive ∧ IsSelfAdjoint Y ∧
      e = ‖lchsResidual μ X Y‖ }

/-- The worst-case matrix error `𝓔(μ)`, eq. (3.1) of the note. -/
def matrixError (μ : FiniteCMeasure) : ℝ := sSup (matrixErrorSet μ)

/-- Attainable worst-case errors at parameters `(R, λ)`. -/
def matrixCosts (R lam : ℝ) : Set ℝ :=
  { e | ∃ μ : FiniteCMeasure, SupportedIn R μ ∧ tv μ ≤ lam ∧ matrixError μ = e }

/-- The minimax value on the left of eq. (3.3). -/
def matrixMinimax (R lam : ℝ) : ℝ := sInf (matrixCosts R lam)

/-- The matrix version of Theorem 1, eq. (3.3). -/
def MatrixTheorem1Statement : Prop :=
  ∀ (R lam : ℝ), 0 < R → 0 ≤ lam →
    matrixMinimax R lam = sharpValue (pR R) (qR R) lam

/-- The realization lemma of Section 4 (实现引理): a bounded analytic function
`Φ` on the lower half-plane, analytic near the compact set `K ⊂ ℝ`, is
approximated uniformly on `K` and at `-i` by matrix elements
`⟨v, e^{-i(kX+Y)} u⟩` with `X ⪰ 0`, `Y = Y*` and unit vectors `u, v`. -/
def RealizationLemma : Prop :=
  ∀ (Φ : ℂ → ℂ) (K : Set ℝ), IsCompact K →
    AnalyticOnNhd ℂ Φ {z : ℂ | z.im < 0} →
    (∀ k ∈ K, AnalyticAt ℂ Φ (k:ℂ)) →
    (∀ z : ℂ, z.im < 0 → ‖Φ z‖ ≤ 1) →
    ∀ δ > 0, ∃ (d : ℕ) (X Y : Op d) (u v : Hd d),
      X.IsPositive ∧ IsSelfAdjoint Y ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      (∀ k ∈ K, ‖⟪v, NormedSpace.exp (-(Complex.I • ((k:ℂ) • X + Y))) u⟫_ℂ - Φ k‖ < δ) ∧
      ‖⟪v, NormedSpace.exp (-(X + Complex.I • Y)) u⟫_ℂ - Φ (-Complex.I)‖ < δ

end LCHSWiener
