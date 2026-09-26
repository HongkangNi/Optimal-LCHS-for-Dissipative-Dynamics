import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Slope
import LCHSWiener.GQSP
import LCHSWiener.OperatorGeneric
import LCHSWiener.OperatorLCHS

noncomputable section

open Set Filter Matrix
open scoped InnerProductSpace Topology ComplexOrder

namespace LCHSWiener

/-!
# Section 4.3, part 1: pulse sequences

A GQSP product `V_k D(e^{-ihz}) ⋯ D(e^{-ihz}) V_0` is written as the end value of
a time-dependent evolution `𝒰_z(s)` on `ℂ²` driven by non-overlapping smooth
pulses: `𝒰_z'(s) = -i (z L(s) + H(s)) 𝒰_z(s)` with `L(s) ⪰ 0`, `H(s) = H(s)*`,
`𝒰_z(s) = 1` before the pulses and `𝒰_z(s) = V_k D ⋯ V_0` after them.

Each pulse is an explicit one-parameter path `x ↦ path z x` with a constant
generator, reparametrized by the smooth step `θ = smoothTransition`.  The
`SU(2)` factors are split into three pulses by Euler angles.
-/

/-- `2 × 2` matrices as operators on `ℂ²`. -/
abbrev toOp : M2 ≃⋆ₐ[ℂ] Op 2 := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)

/-! ### The smooth step -/

/-- The smooth step `θ`, `0` on `(-∞, 0]` and `1` on `[1, ∞)`. -/
abbrev θ : ℝ → ℝ := Real.smoothTransition

lemma θ_of_nonpos {x : ℝ} (hx : x ≤ 0) : θ x = 0 := Real.smoothTransition.zero_of_nonpos hx

lemma θ_of_one_le {x : ℝ} (hx : 1 ≤ x) : θ x = 1 := Real.smoothTransition.one_of_one_le hx

lemma θ_contDiff : ContDiff ℝ 1 θ := Real.smoothTransition.contDiff

lemma θ_differentiable : Differentiable ℝ θ := θ_contDiff.differentiable one_ne_zero

lemma θ_hasDerivAt (x : ℝ) : HasDerivAt θ (deriv θ x) x :=
  (θ_differentiable x).hasDerivAt

lemma continuous_deriv_θ : Continuous (deriv θ) := θ_contDiff.continuous_deriv le_rfl

lemma deriv_θ_nonneg (x : ℝ) : 0 ≤ deriv θ x := Real.smoothTransition.monotone.deriv_nonneg

lemma deriv_θ_of_one_lt {x : ℝ} (hx : 1 < x) : deriv θ x = 0 := by
  have h : θ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using θ_of_one_le hy.le
  rw [h.deriv_eq, deriv_const]

/-! ### Pulses -/

/-- A pulse: a path of `2 × 2` operators starting at `1` with constant generator
`-i (z L₀ + H₀)`, `L₀ ⪰ 0`, `H₀ = H₀*`. -/
structure Pulse where
  path : ℂ → ℝ → Op 2
  L0 : Op 2
  H0 : Op 2
  hL0 : L0.IsPositive
  hH0 : IsSelfAdjoint H0
  path_zero : ∀ z, path z 0 = 1
  hasDerivAt : ∀ (z : ℂ) (x : ℝ),
    HasDerivAt (path z) (-(Complex.I • (z • L0 + H0)) * path z x) x
  continuous : Continuous fun p : ℂ × ℝ => path p.1 p.2

/-! #### Diagonal pulses -/

/-- The diagonal operator `diag(a, b)`. -/
def diagOp (a b : ℂ) : Op 2 := toOp (diagonal ![a, b])

lemma diagOp_mul (a b c d : ℂ) : diagOp a b * diagOp c d = diagOp (a * c) (b * d) := by
  rw [diagOp, diagOp, diagOp, ← map_mul, diagonal_mul_diagonal]
  congr 2
  ext i; fin_cases i <;> simp

lemma diagOp_add (a b c d : ℂ) : diagOp a b + diagOp c d = diagOp (a + c) (b + d) := by
  rw [diagOp, diagOp, diagOp, ← map_add, diagonal_add]
  congr 2
  ext i; fin_cases i <;> simp

lemma smul_diagOp (c a b : ℂ) : c • diagOp a b = diagOp (c * a) (c * b) := by
  rw [diagOp, diagOp, ← map_smul]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma diagOp_one : diagOp 1 1 = 1 := by
  rw [diagOp, ← map_one toOp]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma diagOp_eq_add (a b : ℂ) : diagOp a b = a • diagOp 1 0 + b • diagOp 0 1 := by
  rw [smul_diagOp, smul_diagOp, diagOp_add]; simp

lemma isPositive_diagOp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (diagOp a b).IsPositive := by
  rw [diagOp, ← ContinuousLinearMap.isPositive_toLinearMap_iff,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.isPositive_toEuclideanLin_iff,
    posSemidef_diagonal_iff]
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

lemma isSelfAdjoint_diagOp (a b : ℝ) : IsSelfAdjoint (diagOp a b) := by
  refine IsSelfAdjoint.map toOp ?_
  rw [IsSelfAdjoint, star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.conj_ofReal]

lemma continuous_diagOp : Continuous fun p : ℂ × ℂ => diagOp p.1 p.2 := by
  have h : (fun p : ℂ × ℂ => diagOp p.1 p.2) =
      fun p => p.1 • diagOp 1 0 + p.2 • diagOp 0 1 := funext fun p => diagOp_eq_add _ _
  rw [h]
  fun_prop

lemma hasDerivAt_cexp_linear (c : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-Complex.I * x * c))
      (-Complex.I * c * Complex.exp (-Complex.I * x * c)) x := by
  have hlin : HasDerivAt (fun x : ℝ => -Complex.I * (x:ℂ) * c) (-Complex.I * c) x := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-Complex.I)).mul_const c
    simpa using this
  convert hlin.cexp using 1
  ring

/-- The path `x ↦ diag(e^{-ix(z l₀ + k₀)}, e^{-ix(z l₁ + k₁)})`. -/
def diagPath (l0 l1 k0 k1 : ℝ) (z : ℂ) (x : ℝ) : Op 2 :=
  diagOp (Complex.exp (-Complex.I * x * (z * l0 + k0)))
    (Complex.exp (-Complex.I * x * (z * l1 + k1)))

lemma diagPath_hasDerivAt (l0 l1 k0 k1 : ℝ) (z : ℂ) (x : ℝ) :
    HasDerivAt (diagPath l0 l1 k0 k1 z)
      (-(Complex.I • (z • diagOp l0 l1 + diagOp k0 k1)) * diagPath l0 l1 k0 k1 z x) x := by
  have h0 := hasDerivAt_cexp_linear (z * l0 + k0) x
  have h1 := hasDerivAt_cexp_linear (z * l1 + k1) x
  have hsum := (h0.smul_const (diagOp 1 0)).add (h1.smul_const (diagOp 0 1))
  have hfun : diagPath l0 l1 k0 k1 z =
      (fun y : ℝ => Complex.exp (-Complex.I * y * (z * l0 + k0)) • diagOp 1 0) +
      (fun y : ℝ => Complex.exp (-Complex.I * y * (z * l1 + k1)) • diagOp 0 1) := by
    funext y
    exact diagOp_eq_add _ _
  have hd : HasDerivAt (diagPath l0 l1 k0 k1 z)
      ((-Complex.I * (z * l0 + k0) * Complex.exp (-Complex.I * x * (z * l0 + k0))) • diagOp 1 0 +
        (-Complex.I * (z * l1 + k1) * Complex.exp (-Complex.I * x * (z * l1 + k1))) • diagOp 0 1)
      x := by
    rw [hfun]; exact hsum
  refine hd.congr_deriv ?_
  rw [diagPath]
  simp only [smul_diagOp, diagOp_add]
  rw [← neg_one_smul ℂ (diagOp _ _), smul_diagOp, diagOp_mul]
  congr 1 <;> ring

lemma continuous_diagPath (l0 l1 k0 k1 : ℝ) :
    Continuous fun p : ℂ × ℝ => diagPath l0 l1 k0 k1 p.1 p.2 := by
  have h : (fun p : ℂ × ℝ => diagPath l0 l1 k0 k1 p.1 p.2) =
      (fun q : ℂ × ℂ => diagOp q.1 q.2) ∘
        (fun p : ℂ × ℝ => (Complex.exp (-Complex.I * p.2 * (p.1 * l0 + k0)),
          Complex.exp (-Complex.I * p.2 * (p.1 * l1 + k1)))) := rfl
  rw [h]
  exact continuous_diagOp.comp (by fun_prop)

lemma diagPath_zero (l0 l1 k0 k1 : ℝ) (z : ℂ) : diagPath l0 l1 k0 k1 z 0 = 1 := by
  simp [diagPath, diagOp_one]

/-- The diagonal pulse with generator `z diag(l₀, l₁) + diag(k₀, k₁)`. -/
def diagPulse (l0 l1 k0 k1 : ℝ) (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) : Pulse where
  path := diagPath l0 l1 k0 k1
  L0 := diagOp l0 l1
  H0 := diagOp k0 k1
  hL0 := isPositive_diagOp hl0 hl1
  hH0 := isSelfAdjoint_diagOp k0 k1
  path_zero := diagPath_zero l0 l1 k0 k1
  hasDerivAt := diagPath_hasDerivAt l0 l1 k0 k1
  continuous := continuous_diagPath l0 l1 k0 k1

lemma diagPulse_path_one (l0 l1 k0 k1 : ℝ) (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (z : ℂ) :
    (diagPulse l0 l1 k0 k1 hl0 hl1).path z 1 =
      diagOp (Complex.exp (-Complex.I * (z * l0 + k0))) (Complex.exp (-Complex.I * (z * l1 + k1))) := by
  simp [diagPulse, diagPath]

/-! #### Rotation pulses -/

/-- `J = [[0, -1], [1, 0]]`. -/
def rotJ : Op 2 := toOp !![0, -1; 1, 0]

lemma rotJ_mul_self : rotJ * rotJ = -1 := by
  rw [rotJ, ← map_mul, ← map_one toOp, ← map_neg]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma isSelfAdjoint_I_smul_rotJ : IsSelfAdjoint (Complex.I • rotJ) := by
  rw [rotJ, ← map_smul]
  refine IsSelfAdjoint.map toOp ?_
  rw [IsSelfAdjoint, star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The path `x ↦ cos(xφ) 1 + sin(xφ) J`. -/
def rotPath (φ : ℝ) (_z : ℂ) (x : ℝ) : Op 2 :=
  (Real.cos (x * φ) : ℂ) • (1 : Op 2) + (Real.sin (x * φ) : ℂ) • rotJ

lemma rotPath_hasDerivAt (φ : ℝ) (z : ℂ) (x : ℝ) :
    HasDerivAt (rotPath φ z)
      (-(Complex.I • (z • (0 : Op 2) + (φ : ℂ) • (Complex.I • rotJ))) * rotPath φ z x) x := by
  have hc : HasDerivAt (fun x : ℝ => (Real.cos (x * φ) : ℂ)) (-(Real.sin (x * φ) * φ : ℝ)) x := by
    have := ((hasDerivAt_id x).mul_const φ).cos
    simpa using this.ofReal_comp
  have hs : HasDerivAt (fun x : ℝ => (Real.sin (x * φ) : ℂ)) ((Real.cos (x * φ) * φ : ℝ)) x := by
    have := ((hasDerivAt_id x).mul_const φ).sin
    simpa using this.ofReal_comp
  have hsum := (hc.smul_const (1 : Op 2)).add (hs.smul_const rotJ)
  have hd : HasDerivAt (rotPath φ z)
      ((-(Real.sin (x * φ) * φ : ℝ) : ℂ) • (1 : Op 2) + ((Real.cos (x * φ) * φ : ℝ) : ℂ) • rotJ)
      x := by
    have hfun : rotPath φ z = (fun y : ℝ => (Real.cos (y * φ) : ℂ) • (1 : Op 2)) +
        (fun y : ℝ => (Real.sin (y * φ) : ℂ) • rotJ) := rfl
    rw [hfun]; exact hsum
  refine hd.congr_deriv ?_
  have hgen : -(Complex.I • (z • (0 : Op 2) + (φ : ℂ) • (Complex.I • rotJ))) = (φ : ℂ) • rotJ := by
    rw [smul_zero, zero_add, smul_smul, smul_smul, ← neg_smul]
    congr 1
    rw [mul_comm Complex.I (φ : ℂ), mul_assoc, Complex.I_mul_I]
    ring
  rw [hgen, rotPath, mul_add, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Algebra.mul_smul_comm, mul_one, rotJ_mul_self, smul_smul, smul_smul]
  rw [show ((Real.cos (x * φ) * φ : ℝ) : ℂ) = (φ : ℂ) * Real.cos (x * φ) by push_cast; ring,
    smul_neg, ← neg_smul, add_comm]
  congr 2
  push_cast
  ring

lemma continuous_rotPath (φ : ℝ) : Continuous fun p : ℂ × ℝ => rotPath φ p.1 p.2 := by
  unfold rotPath
  fun_prop

lemma isSelfAdjoint_rotGen (φ : ℝ) : IsSelfAdjoint ((φ : ℂ) • (Complex.I • rotJ)) := by
  rw [rotJ, ← map_smul, ← map_smul]
  refine IsSelfAdjoint.map toOp ?_
  rw [IsSelfAdjoint, star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.conj_ofReal]

/-- The rotation pulse with generator `φ σ_y`, `σ_y = i J`. -/
def rotPulse (φ : ℝ) : Pulse where
  path := rotPath φ
  L0 := 0
  H0 := (φ : ℂ) • (Complex.I • rotJ)
  hL0 := ContinuousLinearMap.isPositive_zero
  hH0 := isSelfAdjoint_rotGen φ
  path_zero z := by simp [rotPath]
  hasDerivAt := rotPath_hasDerivAt φ
  continuous := continuous_rotPath φ

lemma rotPulse_path_one (φ : ℝ) (z : ℂ) :
    (rotPulse φ).path z 1 = toOp !![(Real.cos φ : ℂ), -(Real.sin φ : ℂ); Real.sin φ, Real.cos φ] := by
  simp only [rotPulse, rotPath, one_mul, rotJ]
  rw [← map_one toOp, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma deriv_θ_of_neg {x : ℝ} (hx : x < 0) : deriv θ x = 0 := by
  have h : θ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy using θ_of_nonpos hy.le
  rw [h.deriv_eq, deriv_const]

/-! ### Pulse sequences -/

/-- The `j`-th pulse acts on `[3 + 2j, 4 + 2j]`. -/
def pulseStart (j : ℕ) : ℝ := 3 + 2 * j

lemma pulseStart_mono {i j : ℕ} (h : i ≤ j) : pulseStart i ≤ pulseStart j := by
  unfold pulseStart; have : (i:ℝ) ≤ j := by exact_mod_cast h
  linarith

/-- `𝒰_z(s)`: the pulses `ps`, numbered from `j`, applied in order. -/
def pulseProd : List Pulse → ℕ → ℂ → ℝ → Op 2
  | [], _, _, _ => 1
  | p :: ps, j, z, s => pulseProd ps (j + 1) z s * p.path z (θ (s - pulseStart j))

/-- The positive part `L(s)` of the generator. -/
def pulseL : List Pulse → ℕ → ℝ → Op 2
  | [], _, _ => 0
  | p :: ps, j, s => ((deriv θ (s - pulseStart j) : ℝ) : ℂ) • p.L0 + pulseL ps (j + 1) s

/-- The self-adjoint part `H(s)` of the generator. -/
def pulseH : List Pulse → ℕ → ℝ → Op 2
  | [], _, _ => 0
  | p :: ps, j, s => ((deriv θ (s - pulseStart j) : ℝ) : ℂ) • p.H0 + pulseH ps (j + 1) s

/-- The end value: the product of all pulse endpoints. -/
def endProd : List Pulse → ℂ → Op 2
  | [], _ => 1
  | p :: ps, z => endProd ps z * p.path z 1

lemma endProd_append (l1 l2 : List Pulse) (z : ℂ) :
    endProd (l1 ++ l2) z = endProd l2 z * endProd l1 z := by
  induction l1 with
  | nil => simp [endProd]
  | cons p ps ih => simp [endProd, ih, mul_assoc]

lemma pulseProd_of_le : ∀ (ps : List Pulse) (j : ℕ) (z : ℂ) (s : ℝ),
    s ≤ pulseStart j → pulseProd ps j z s = 1
  | [], _, _, _, _ => rfl
  | p :: ps, j, z, s, h => by
    rw [pulseProd, pulseProd_of_le ps (j + 1) z s (h.trans (pulseStart_mono (by omega))),
      θ_of_nonpos (by linarith), p.path_zero, one_mul]

lemma pulseProd_of_ge : ∀ (ps : List Pulse) (j : ℕ) (z : ℂ) (s : ℝ),
    pulseStart (j + ps.length) - 1 ≤ s → pulseProd ps j z s = endProd ps z
  | [], _, _, _, _ => rfl
  | p :: ps, j, z, s, h => by
    have h' : pulseStart (j + 1 + ps.length) - 1 ≤ s := by
      simp only [List.length_cons] at h
      rwa [show j + 1 + ps.length = j + (ps.length + 1) by omega]
    rw [pulseProd, pulseProd_of_ge ps (j + 1) z s h', endProd]
    congr 2
    apply θ_of_one_le
    have hlen : (0:ℝ) ≤ ps.length := Nat.cast_nonneg _
    simp only [pulseStart, List.length_cons] at h ⊢
    push_cast at h
    linarith

lemma pulseL_of_lt : ∀ (ps : List Pulse) (j : ℕ) (s : ℝ), s < pulseStart j → pulseL ps j s = 0
  | [], _, _, _ => rfl
  | p :: ps, j, s, h => by
    rw [pulseL, pulseL_of_lt ps (j + 1) s (h.trans_le (pulseStart_mono (by omega))),
      deriv_θ_of_neg (by linarith)]
    simp

lemma pulseH_of_lt : ∀ (ps : List Pulse) (j : ℕ) (s : ℝ), s < pulseStart j → pulseH ps j s = 0
  | [], _, _, _ => rfl
  | p :: ps, j, s, h => by
    rw [pulseH, pulseH_of_lt ps (j + 1) s (h.trans_le (pulseStart_mono (by omega))),
      deriv_θ_of_neg (by linarith)]
    simp

lemma isPositive_pulseL : ∀ (ps : List Pulse) (j : ℕ) (s : ℝ), (pulseL ps j s).IsPositive
  | [], _, _ => ContinuousLinearMap.isPositive_zero
  | p :: ps, j, s => by
    rw [pulseL]
    refine (p.hL0.smul_of_nonneg ?_).add (isPositive_pulseL ps (j + 1) s)
    exact_mod_cast deriv_θ_nonneg _

lemma isSelfAdjoint_pulseH : ∀ (ps : List Pulse) (j : ℕ) (s : ℝ), IsSelfAdjoint (pulseH ps j s)
  | [], _, _ => IsSelfAdjoint.zero _
  | p :: ps, j, s => by
    rw [pulseH]
    refine IsSelfAdjoint.add ?_ (isSelfAdjoint_pulseH ps (j + 1) s)
    rw [IsSelfAdjoint, star_smul, p.hH0.star_eq]
    congr 1
    exact Complex.conj_ofReal _

lemma continuous_pulseL : ∀ (ps : List Pulse) (j : ℕ), Continuous (pulseL ps j)
  | [], _ => continuous_const
  | p :: ps, j => by
    have h1 : Continuous fun s : ℝ => ((deriv θ (s - pulseStart j) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_deriv_θ.comp (continuous_sub_right _))
    exact (h1.smul continuous_const).add (continuous_pulseL ps (j + 1))

lemma continuous_pulseH : ∀ (ps : List Pulse) (j : ℕ), Continuous (pulseH ps j)
  | [], _ => continuous_const
  | p :: ps, j => by
    have h1 : Continuous fun s : ℝ => ((deriv θ (s - pulseStart j) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_deriv_θ.comp (continuous_sub_right _))
    exact (h1.smul continuous_const).add (continuous_pulseH ps (j + 1))

lemma continuous_pulseProd : ∀ (ps : List Pulse) (j : ℕ),
    Continuous fun q : ℂ × ℝ => pulseProd ps j q.1 q.2
  | [], _ => continuous_const
  | p :: ps, j => by
    have h1 : Continuous fun q : ℂ × ℝ => p.path q.1 (θ (q.2 - pulseStart j)) :=
      p.continuous.comp (continuous_fst.prodMk
        (Real.smoothTransition.continuous.comp (continuous_snd.sub continuous_const)))
    exact (continuous_pulseProd ps (j + 1)).mul h1

/-- The evolution equation `𝒰_z' = -i (z L + H) 𝒰_z`. -/
lemma pulseProd_hasDerivAt : ∀ (ps : List Pulse) (j : ℕ) (z : ℂ) (s : ℝ),
    HasDerivAt (pulseProd ps j z)
      (-(Complex.I • (z • pulseL ps j s + pulseH ps j s)) * pulseProd ps j z s) s
  | [], j, z, s => by
    simp only [pulseProd, pulseL, pulseH, smul_zero, add_zero, neg_zero, zero_mul]
    exact hasDerivAt_const s (1 : Op 2)
  | p :: ps, j, z, s => by
    set a := pulseStart j
    set c : ℝ := deriv θ (s - a)
    set Q := pulseProd ps (j + 1) z
    set E : ℝ → Op 2 := fun s => p.path z (θ (s - a))
    set gp : Op 2 := -(Complex.I • (z • p.L0 + p.H0))
    set gQ : Op 2 := -(Complex.I • (z • pulseL ps (j + 1) s + pulseH ps (j + 1) s))
    have hQ : HasDerivAt Q (gQ * Q s) s := pulseProd_hasDerivAt ps (j + 1) z s
    have hθ : HasDerivAt (fun s : ℝ => θ (s - a)) c s := (θ_hasDerivAt (s - a)).comp_sub_const s a
    have hE : HasDerivAt E (c • (gp * E s)) s := by
      have := (p.hasDerivAt z (θ (s - a))).scomp s hθ
      simpa [E, gp, Function.comp_def] using this
    have hprod := hQ.mul hE
    -- only one pulse is active: either `c = 0` or `Q s = 1`
    have hkey : (c : ℂ) • (Q s * gp) = (c : ℂ) • (gp * Q s) := by
      by_cases hc : c = 0
      · simp [hc]
      · have hsa : s - a ≤ 1 := by
          by_contra h
          exact hc (deriv_θ_of_one_lt (by linarith))
        have hQ1 : Q s = 1 := pulseProd_of_le ps (j + 1) z s (by
          simp only [a, pulseStart] at hsa ⊢; push_cast; linarith)
        rw [hQ1, one_mul, mul_one]
    refine hprod.congr_deriv ?_
    show gQ * Q s * E s + Q s * (c • (gp * E s)) =
      -(Complex.I • (z • ((c : ℂ) • p.L0 + pulseL ps (j + 1) s) +
        ((c : ℂ) • p.H0 + pulseH ps (j + 1) s))) * (Q s * E s)
    have hgen : -(Complex.I • (z • ((c : ℂ) • p.L0 + pulseL ps (j + 1) s) +
        ((c : ℂ) • p.H0 + pulseH ps (j + 1) s))) = (c : ℂ) • gp + gQ := by
      simp only [gp, gQ]
      module
    have e1 : Q s * ((c : ℂ) • (gp * E s)) = ((c : ℂ) • (Q s * gp)) * E s := by
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_assoc]
    have e2 : ((c : ℂ) • gp + gQ) * (Q s * E s) = ((c : ℂ) • (gp * Q s)) * E s + gQ * Q s * E s := by
      rw [add_mul, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, mul_assoc, mul_assoc]
    rw [hgen, ← Complex.coe_smul, e1, hkey, e2]
    abel

/-! ### The GQSP pulse sequence -/

/-- The `D`-pulse with generator `z h |0⟩⟨0|`. -/
def dPulse (h : ℝ) (hh : 0 ≤ h) : Pulse := diagPulse h 0 0 0 hh le_rfl

lemma dPulse_path_one (h : ℝ) (hh : 0 ≤ h) (z : ℂ) :
    (dPulse h hh).path z 1 = toOp (gqspD (Complex.exp (-Complex.I * h * z))) := by
  rw [dPulse, diagPulse_path_one, diagOp]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [gqspD]; ring_nf

/-- The phase pulse `diag(e^{ix}, e^{-ix})`. -/
def phasePulse (x : ℝ) : Pulse := diagPulse 0 0 (-x) x le_rfl le_rfl

lemma phasePulse_path_one (x : ℝ) (z : ℂ) :
    (phasePulse x).path z 1 = diagOp (Complex.exp (Complex.I * x)) (Complex.exp (-(Complex.I * x))) := by
  rw [phasePulse, diagPulse_path_one]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The rotation matrix `[[cos φ, -sin φ], [sin φ, cos φ]]`. -/
def rotMat (φ : ℝ) : M2 := !![(Real.cos φ : ℂ), -(Real.sin φ : ℂ); Real.sin φ, Real.cos φ]

lemma exp_mul_mul_exp (x y r : ℝ) :
    Complex.exp (Complex.I * x) * (r : ℂ) * Complex.exp (Complex.I * y) =
      r * Complex.exp (((x + y : ℝ) : ℂ) * Complex.I) := by
  rw [mul_comm (Complex.exp _) (r : ℂ), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **Euler angles** for `SU(2)`. -/
lemma su2_euler {V : M2} (hV : IsSU2 V) : ∃ x y φ : ℝ,
    toOp V = diagOp (Complex.exp (Complex.I * x)) (Complex.exp (-(Complex.I * x))) *
      toOp (rotMat φ) * diagOp (Complex.exp (Complex.I * y)) (Complex.exp (-(Complex.I * y))) := by
  obtain ⟨α, β, hn, rfl⟩ := hV
  set c := ‖α‖
  set sn := ‖β‖
  have hc2 : c ^ 2 + sn ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; exact hn
  have hc0 : 0 ≤ c := norm_nonneg _
  have hs0 : 0 ≤ sn := norm_nonneg _
  have hc1 : c ≤ 1 := by nlinarith
  set φ := Real.arccos c
  have hcos : Real.cos φ = c := Real.cos_arccos (by linarith) hc1
  have hsin : Real.sin φ = sn := by
    rw [Real.sin_arccos, show 1 - c ^ 2 = sn ^ 2 by linarith, Real.sqrt_sq hs0]
  set a := Complex.arg α
  set b := Complex.arg β
  refine ⟨(a - b) / 2, (a + b) / 2, φ, ?_⟩
  have hα : α = (c : ℂ) * Complex.exp ((a : ℂ) * Complex.I) := (Complex.norm_mul_exp_arg_mul_I α).symm
  have hβ : β = (sn : ℂ) * Complex.exp ((b : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I β).symm
  have hconj : ∀ (r t : ℝ), starRingEnd ℂ ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      (r : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
    intro r t
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast; ring_nf
  rw [diagOp, diagOp, ← map_mul, ← map_mul]
  congr 1
  rw [hα, hβ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [su2, rotMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;> simp [hcos, hsin, hconj] <;>
    · rw [mul_right_comm, ← Complex.exp_add, mul_comm]
      congr 2
      ring

lemma rotPulse_path_one' (φ : ℝ) (z : ℂ) : (rotPulse φ).path z 1 = toOp (rotMat φ) :=
  rotPulse_path_one φ z

open Classical in
/-- The three Euler-angle pulses of an `SU(2)` factor (empty if `V` is not in `SU(2)` form). -/
def eulerPulses (V : M2) : List Pulse :=
  if h : IsSU2 V then
    [phasePulse (Classical.choose (Classical.choose_spec (su2_euler h))),
      rotPulse (Classical.choose (Classical.choose_spec (Classical.choose_spec (su2_euler h)))),
      phasePulse (Classical.choose (su2_euler h))]
  else []

lemma endProd_eulerPulses {V : M2} (h : IsSU2 V) (z : ℂ) : endProd (eulerPulses V) z = toOp V := by
  have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (su2_euler h)))
  simp only [eulerPulses, h, ↓reduceDIte, endProd, one_mul]
  rw [phasePulse_path_one, rotPulse_path_one', phasePulse_path_one]
  exact hspec.symm

/-- The pulse sequence realizing `V_k D ⋯ D V_0` (`D`-pulses carry `z h |0⟩⟨0|`). -/
def gqspPulses (h : ℝ) (hh : 0 ≤ h) (V0 : M2) : List M2 → List Pulse
  | [] => eulerPulses V0
  | V :: Vs => gqspPulses h hh V0 Vs ++ (dPulse h hh :: eulerPulses V)

lemma endProd_gqspPulses (h : ℝ) (hh : 0 ≤ h) {V0 : M2} (hV0 : IsSU2 V0) :
    ∀ (Vs : List M2), (∀ V ∈ Vs, IsSU2 V) → ∀ z : ℂ,
      endProd (gqspPulses h hh V0 Vs) z = toOp (gqspMat V0 Vs (Complex.exp (-Complex.I * h * z)))
  | [], _, z => endProd_eulerPulses hV0 z
  | V :: Vs, hVs, z => by
    rw [gqspPulses, endProd_append, endProd, endProd_eulerPulses (hVs V (List.mem_cons_self ..)),
      dPulse_path_one, endProd_gqspPulses h hh hV0 Vs (fun W hW => hVs W (List.mem_cons_of_mem _ hW)),
      gqspMat, map_mul, map_mul]

end LCHSWiener
