import LCHSWiener.PolyApprox
import LCHSWiener.OperatorLCHS
import LCHSWiener.MatrixTheorem1

noncomputable section

open scoped InnerProductSpace

namespace LCHSWiener

/-!
# Reducing the realization lemma to realizing Schur polynomials

Section 4.1 (`schur_polynomial_approx`) approximates `Φ` by `P(e^{-ihz})`.
What remains of the realization lemma, Sections 4.2–4.3 (GQSP decomposition
and the finite Fourier clock), is `PolynomialRealization`: every polynomial
bounded by `1` on the closed unit disc is realized, uniformly on compact
subsets of the closed lower half-plane, by matrix elements
`⟨v, e^{-i(zX+Y)} u⟩`.
-/

/-- Sections 4.2–4.3: matrix realization of `P(e^{-ihz})` for Schur
polynomials `P`. -/
def PolynomialRealization : Prop :=
  ∀ (P : Polynomial ℂ), (∀ w : ℂ, ‖w‖ ≤ 1 → ‖P.eval w‖ ≤ 1) →
    ∀ (h : ℝ), 0 < h → ∀ (Z : Set ℂ), IsCompact Z → (∀ z ∈ Z, z.im ≤ 0) →
    ∀ ε > 0, ∃ (d : ℕ) (X Y : Op d) (u v : Hd d),
      X.IsPositive ∧ IsSelfAdjoint Y ∧ ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      ∀ z ∈ Z, ‖⟪v, NormedSpace.exp (-(Complex.I • (z • X + Y))) u⟫_ℂ -
        P.eval (Complex.exp (-Complex.I * h * z))‖ < ε

/-- Section 4.1 reduces the realization lemma to `PolynomialRealization`. -/
theorem realizationLemma_of_polynomialRealization (hpoly : PolynomialRealization) :
    RealizationLemma := by
  intro Φ K hK hΦ hKan hbd δ hδ
  obtain ⟨h, hh, P, hPbd, hPapprox⟩ :=
    schur_polynomial_approx hK hΦ hKan hbd (δ := δ / 2) (by positivity)
  obtain ⟨d, X, Y, u, v, hX, hY, hu, hv, hreal⟩ :=
    hpoly P hPbd h hh (realizationSet K) (isCompact_realizationSet hK)
      (fun z hz => im_nonpos_of_mem_realizationSet hz) (δ / 2) (by positivity)
  have key : ∀ z ∈ realizationSet K,
      ‖⟪v, NormedSpace.exp (-(Complex.I • (z • X + Y))) u⟫_ℂ - Φ z‖ < δ := by
    intro z hz
    calc ‖⟪v, NormedSpace.exp (-(Complex.I • (z • X + Y))) u⟫_ℂ - Φ z‖
        = ‖(⟪v, NormedSpace.exp (-(Complex.I • (z • X + Y))) u⟫_ℂ -
            P.eval (Complex.exp (-Complex.I * h * z))) +
          (P.eval (Complex.exp (-Complex.I * h * z)) - Φ z)‖ := by ring_nf
      _ ≤ ‖⟪v, NormedSpace.exp (-(Complex.I • (z • X + Y))) u⟫_ℂ -
            P.eval (Complex.exp (-Complex.I * h * z))‖ +
          ‖P.eval (Complex.exp (-Complex.I * h * z)) - Φ z‖ := norm_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hreal z hz) (hPapprox z hz)
      _ = δ := by ring
  refine ⟨d, X, Y, u, v, hX, hY, hu, hv, fun k hk => key k (Or.inl ⟨k, hk, rfl⟩), ?_⟩
  have hI := key (-Complex.I) (Or.inr rfl)
  have heq : NormedSpace.exp (-(Complex.I • ((-Complex.I) • X + Y))) =
      NormedSpace.exp (-(X + Complex.I • Y)) := lchsEvol_neg_I X Y
  rwa [heq] at hI

/-- The matrix version of Theorem 1 follows from `PolynomialRealization`. -/
theorem MatrixTheorem1_of_polynomialRealization (hpoly : PolynomialRealization) :
    MatrixTheorem1Statement :=
  MatrixTheorem1_of_realization (realizationLemma_of_polynomialRealization hpoly)

end LCHSWiener
