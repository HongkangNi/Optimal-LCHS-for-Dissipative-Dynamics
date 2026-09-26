import LCHSWiener.ClockPulses

noncomputable section

open Set Filter
open scoped InnerProductSpace Topology ComplexOrder

namespace LCHSWiener

/-!
# Section 4.3, part 2: the finite clock

The clock space `ℂ^n ⊗ ℂ²` is `PiLp 2 (Fin n → ℂ²)`.  On it we use

* the cyclic shift `(Tψ)_j = ψ_{j+1}` and the central difference
  `D = (T - T⁻¹)/(2iδ)`, a self-adjoint discretization of `-i ∂_s`;
* block-diagonal operators `(Aψ)_j = A_j ψ_j`;
* the sampling map `(S f)_j = √δ f(jδ)`.

Unlike the Fourier differentiation matrix of `section4_finite_dimensional.tex`,
the central difference has a local consistency error controlled by the modulus
of continuity of `∂_s`, so no Fourier analysis is needed.
-/

/-- The clock space `ℂ^n ⊗ ℂ²`. -/
abbrev ClockSpace (n : ℕ) := PiLp 2 (fun _ : Fin n => Hd 2)

/-- Operators on the clock space. -/
abbrev ClockOp (n : ℕ) := ClockSpace n →L[ℂ] ClockSpace n

section Shift

variable (n : ℕ) [NeZero n]

/-- The forward cyclic shift `(Tψ)_j = ψ_{j+1}`. -/
def shiftIso : ClockSpace n ≃ₗᵢ[ℂ] ClockSpace n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ (Hd 2) (Equiv.subRight (1 : Fin n))

lemma shiftIso_apply (ψ : ClockSpace n) (j : Fin n) : shiftIso n ψ j = ψ (j + 1) := by
  simp [shiftIso, Equiv.piCongrLeft']

lemma shiftIso_symm_apply (ψ : ClockSpace n) (j : Fin n) : (shiftIso n).symm ψ j = ψ (j - 1) := by
  simp [shiftIso, Equiv.piCongrLeft']

/-- The central difference `D = (T - T⁻¹)/(2iδ)`. -/
def centralDiff (δ : ℝ) : ClockOp n :=
  ((2 * Complex.I * δ)⁻¹ : ℂ) •
    ((shiftIso n : ClockSpace n →L[ℂ] ClockSpace n) - ((shiftIso n).symm : ClockOp n))

lemma centralDiff_apply (δ : ℝ) (ψ : ClockSpace n) (j : Fin n) :
    centralDiff n δ ψ j = ((2 * Complex.I * δ)⁻¹ : ℂ) • (ψ (j + 1) - ψ (j - 1)) := by
  simp [centralDiff, shiftIso_apply, shiftIso_symm_apply]

lemma isSelfAdjoint_centralDiff (δ : ℝ) : IsSelfAdjoint (centralDiff n δ) := by
  rw [IsSelfAdjoint, centralDiff, star_smul, ContinuousLinearMap.star_eq_adjoint, map_sub,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm]
  have hc : star ((2 * Complex.I * δ)⁻¹ : ℂ) = -((2 * Complex.I * δ)⁻¹ : ℂ) := by
    rw [star_inv₀]
    simp [Complex.conj_ofReal]
  rw [hc]
  module

end Shift

variable (n : ℕ)

/-! ### Block-diagonal operators -/

/-- The block-diagonal operator `(Aψ)_j = A_j ψ_j`. -/
def blockDiagLin (A : Fin n → Op 2) : ClockSpace n →ₗ[ℂ] ClockSpace n where
  toFun ψ := WithLp.toLp 2 (fun j => A j (ψ j))
  map_add' x y := by ext j : 1; simp
  map_smul' c x := by ext j : 1; simp

/-- The block-diagonal operator `(Aψ)_j = A_j ψ_j`. -/
def blockDiag (A : Fin n → Op 2) : ClockOp n :=
  LinearMap.toContinuousLinearMap (blockDiagLin n A)

lemma blockDiag_apply (A : Fin n → Op 2) (ψ : ClockSpace n) (j : Fin n) :
    blockDiag n A ψ j = A j (ψ j) := rfl

lemma inner_blockDiag (A : Fin n → Op 2) (x y : ClockSpace n) :
    ⟪blockDiag n A x, y⟫_ℂ = ∑ j, ⟪A j (x j), y j⟫_ℂ := by
  rw [PiLp.inner_apply]; rfl

lemma isSelfAdjoint_blockDiag {A : Fin n → Op 2} (hA : ∀ j, IsSelfAdjoint (A j)) :
    IsSelfAdjoint (blockDiag n A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show ⟪blockDiag n A x, y⟫_ℂ = ⟪x, blockDiag n A y⟫_ℂ
  rw [inner_blockDiag, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => (hA j).isSymmetric _ _

lemma isPositive_blockDiag {A : Fin n → Op 2} (hA : ∀ j, (A j).IsPositive) :
    (blockDiag n A).IsPositive := by
  refine ⟨(isSelfAdjoint_blockDiag n fun j => (hA j).isSelfAdjoint).isSymmetric, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_blockDiag, map_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  have := (hA j).2 (x j)
  rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at this

/-! ### Sampling -/

/-- The sampling map `(S f)_j = √δ f(jδ)`. -/
def sample (δ : ℝ) (f : ℝ → Hd 2) : ClockSpace n :=
  WithLp.toLp 2 (fun j : Fin n => ((Real.sqrt δ : ℝ) : ℂ) • f ((j : ℕ) * δ))

lemma sample_apply (δ : ℝ) (f : ℝ → Hd 2) (j : Fin n) :
    sample n δ f j = ((Real.sqrt δ : ℝ) : ℂ) • f ((j : ℕ) * δ) := rfl

lemma inner_sample {δ : ℝ} (hδ : 0 ≤ δ) (f g : ℝ → Hd 2) :
    ⟪sample n δ f, sample n δ g⟫_ℂ = ∑ j : Fin n, (δ : ℂ) * ⟪f ((j : ℕ) * δ), g ((j : ℕ) * δ)⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sample_apply, sample_apply, inner_smul_left, inner_smul_right, ← mul_assoc]
  congr 1
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hδ]

lemma norm_sq_eq_sum {x : ClockSpace n} : ‖x‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

end LCHSWiener
