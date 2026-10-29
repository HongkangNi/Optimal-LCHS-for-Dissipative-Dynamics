# Optimal LCHS for Dissipative Dynamics

This repository contains Lean 4 proofs of two sharp minimax theorems for
linear combinations of Hamiltonian simulations (LCHS): a scalar
Wiener / Fourier--Stieltjes theorem and a theorem for dissipative dynamics
in every finite matrix dimension. Both statements are given below.

## Common definitions

Let $\mathcal M(\mathbb R)$ be the finite complex Borel measures on
$\mathbb R$. For $\mu\in\mathcal M(\mathbb R)$, write
$\|\mu\|_{\mathrm{TV}}=|\mu|(\mathbb R)$ for its total-variation norm.
For $R>0$ and $\lambda\ge0$, the admissible measures are

$$
\mathcal A_{R,\lambda}
=\left\lbrace\mu\in\mathcal M(\mathbb R):
|\mu|\bigl(\mathbb R\setminus[-R,R]\bigr)=0,
\quad \|\mu\|_{\mathrm{TV}}\le\lambda\right\rbrace.
$$

These measures may have complex weights; they need not be positive or have
total mass one. Define

$$
p_R=\frac{2}{\pi}\arctan R,\qquad q_R=1-p_R,
$$

so that $0<p_R,q_R<1$, and define the common sharp value

$$
S_R(\lambda)=
\begin{cases}
1-\lambda, & 0\le\lambda\le p_R,\\[4pt]
q_R\left(\dfrac{p_R}{\lambda}\right)^{p_R/q_R},
& \lambda>p_R.
\end{cases}
$$

In Lean these constants and the piecewise expression are
`pR R`, `qR R`, and `sharpValue (pR R) (qR R) lam`, respectively.

## Theorem 1: Wiener / Fourier--Stieltjes minimax value

Use the Fourier--Stieltjes convention

$$
\widehat\mu(x)=\int_{\mathbb R}e^{-ikx}\,d\mu(k),
\qquad x\in\mathbb R.
$$

Define the optimal residual representation cost by

$$
\mathcal W_R(\lambda)
=\inf\left\lbrace
\|\nu\|_{\mathrm{TV}}:
\begin{array}{l}
\mu\in\mathcal A_{R,\lambda},\quad \nu\in\mathcal M(\mathbb R),\\
\widehat\nu(x)=e^{-x}-\widehat\mu(x)
\quad\text{for every }x\ge0
\end{array}
\right\rbrace.
$$

The measure $\nu$ represents the residual on the nonnegative real axis.
It may be supported anywhere on $\mathbb R$. The quantity being minimized
is its total-variation norm.

**Theorem.** For every $R>0$ and $\lambda\ge0$,

$$
\boxed{\mathcal W_R(\lambda)=S_R(\lambda).}
$$

The definitions `fsTransform`, `RepresentsResidual`, `wienerCosts`, and
`wienerMinimax` are in
[`LCHSWiener/MeasureFourier.lean`](LCHSWiener/MeasureFourier.lean).
The exported theorem
[`LCHSWiener.wiener_theorem1`](LCHSWiener/Theorem1.lean) proves

```lean
wienerMinimax R lam = sharpValue (pR R) (qR R) lam
```

under the hypotheses `0 < R` and `0 ≤ lam`.
The packaged statement `WienerTheorem1Statement` is defined in
[`LCHSWiener/Target.lean`](LCHSWiener/Target.lean) and proved by
`LCHSWiener.WienerTheorem1`.

## Theorem 2: Matrix minimax value

For each positive integer $d$, let $X,Y$ be complex $d\times d$ matrices,
and write $*$ for conjugate transpose. The condition $X\succeq0$ means
that $X=X^*$ and
$v^*Xv\ge0$ for every $v\in\mathbb C^d$; require also $Y=Y^*$.
All matrix norms below are operator norms induced by the Euclidean norm
on $\mathbb C^d$.

For $\mu\in\mathcal M(\mathbb R)$, define its LCHS approximation and
worst-case error by

$$
L_\mu(X,Y)=\int_{\mathbb R}e^{-i(kX+Y)}\,d\mu(k)
$$

and

$$
\mathcal E(\mu)
=\sup_{\substack{d\ge1,\ X,Y\in\mathbb C^{d\times d}\\
                  X\succeq0,\ Y=Y^*}}
\left\|e^{-(X+iY)}-L_\mu(X,Y)\right\|_{\mathrm{op}}.
$$

The integral is a finite-dimensional operator-valued integral against the
complex measure $\mu$. The supremum ranges over all finite dimensions and
all such matrices, using a single measure $\mu$ throughout. Define

$$
\mathcal M_R(\lambda)
=\inf_{\mu\in\mathcal A_{R,\lambda}}\mathcal E(\mu).
$$

**Theorem.** For every $R>0$ and $\lambda\ge0$,

$$
\boxed{\mathcal M_R(\lambda)=S_R(\lambda).}
$$

The definitions `Op`, `lchsIntegral`, `lchsResidual`, `matrixError`,
`matrixCosts`, `matrixMinimax`, and the packaged statement
`MatrixTheorem1Statement` are in
[`LCHSWiener/MatrixTarget.lean`](LCHSWiener/MatrixTarget.lean).
The final exported theorem is

```lean
LCHSWiener.matrix_theorem1 : LCHSWiener.MatrixTheorem1Statement
```

in [`LCHSWiener/ClockRealization.lean`](LCHSWiener/ClockRealization.lean).
It proves

```lean
matrixMinimax R lam = sharpValue (pR R) (qR R) lam
```

for `0 < R` and `0 ≤ lam`. The realization property used in the
intermediate lower-bound argument is proved within the project.

## Proof structure

The Wiener theorem is assembled as follows:

1. `DualFunction.lean`: the dual Schur function and its boundary values.
2. `HalfLineKernel.lean`, `ShiftedDualTransform.lean`,
   `ShiftedRateBranch.lean`, `OscillatoryIntegral.lean`,
   `KernelTransform.lean`: the positive-half-line transform calculation.
3. `ConvolutionExponential.lean`: positive convolution exponentials in `L1`.
4. `HalfLineRepresentation.lean`: representation of the shifted dual
   function as a one-sided Fourier--Stieltjes transform.
5. `VectorMeasureFubini.lean`: Fubini interchange for finite complex measures.
6. `WienerDualBound.lean`: the dual lower bound in both parameter ranges.
7. `DensityMeasure.lean`: finite complex measures from integrable densities.
8. `CauchyFourier.lean`: the Fourier transform of the Cauchy density, obtained
   by Fourier inversion of `e^{-|x|}`.
9. `KernelUpperBound.lean`: explicit outer kernels and upper-bound witnesses,
   using the half-line representation, Fubini against the Cauchy density,
   and a regularization limit.
10. `Theorem1.lean`: combination of the sharp lower and upper bounds.

The matrix theorem uses the following additional components:

- `HalfPlanePoisson.lean`: the vector-valued Poisson formula at `-i` on
  the lower half-plane.
- `OperatorLCHS.lean`: contraction and analyticity of the matrix
  exponential on the lower half-plane, and operator-valued integrals.
- `MatrixLCHS.lean`: the LCHS identities for the Cauchy and outer kernels,
  and upper-bound witnesses.
- `MatrixLowerBound.lean`, `MatrixTheorem1.lean`: the sharp lower bound
  and minimax formula from the realization property `RealizationLemma`.
- `PolyApprox.lean`: polynomial approximation of bounded holomorphic
  functions using `P(e^{-ihz})`.
- `FejerRiesz.lean`: Fejér–Riesz factorization in the strictly positive case.
- `GQSP.lean`: polynomial approximation by matrix elements of products
  of two-dimensional unitaries and diagonal signal operators.
- `Realization.lean`: the implication chain
  `ProductRealization → PolynomialRealization → RealizationLemma → MatrixTheorem1Statement`.
- `OperatorGeneric.lean`: contraction semigroups, a Duhamel estimate, and
  reduction of finite-dimensional operators to matrices.
- `ClockPulses.lean`, `ClockDiscrete.lean`, `ClockRealization.lean`:
  a finite-clock construction proving `ProductRealization`, followed by
  the final theorem `matrix_theorem1`.

## How to check the proofs

The project pins Lean 4.34.0 in `lean-toolchain` and Mathlib v4.34.0
and its exact dependency revisions in `lake-manifest.json`.

1. Install [elan](https://lean-lang.org/install/), the Lean version manager.
   The Lean 4 VS Code extension can also install it for you.
2. Clone and build:

   ```bash
   git clone https://github.com/HongkangNi/Optimal-LCHS-for-Dissipative-Dynamics.git
   cd Optimal-LCHS-for-Dissipative-Dynamics
   lake exe cache get
   lake build
   ```

   These commands work on Windows, macOS, and Linux. The cache command
   downloads prebuilt Mathlib artifacts. Keep the checked-in toolchain and
   manifest; running `lake update` would change the dependency resolution.
3. Confirm that the build succeeds and inspect the printed axiom
   dependencies for the two main theorems:

   ```text
   'LCHSWiener.wiener_theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'LCHSWiener.matrix_theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

The source tree contains no `sorry`, `admit`, or project-local axiom
declarations. The files containing the two final proofs end with
`#print axioms` commands. Each main theorem should depend only on the three
standard Lean axioms shown above; `sorryAx` would indicate a placeholder.
To print these dependencies again after building, run:

```bash
lake env lean LCHSWiener/Theorem1.lean
lake env lean LCHSWiener/ClockRealization.lean
```

To review the formal statements and the definitions they use, start with:

- [`LCHSWiener/Core.lean`](LCHSWiener/Core.lean): `pR`, `qR`, `sharpValue`.
- [`LCHSWiener/MeasureFourier.lean`](LCHSWiener/MeasureFourier.lean):
  finite complex measures, support, Fourier--Stieltjes transforms, and
  `wienerMinimax`.
- [`LCHSWiener/Target.lean`](LCHSWiener/Target.lean):
  `WienerTheorem1Statement`.
- [`LCHSWiener/MatrixTarget.lean`](LCHSWiener/MatrixTarget.lean):
  the matrix model and `MatrixTheorem1Statement`.

After building, the Lean 4 VS Code extension also displays the checked
declarations and proof states.

### Optional Codespaces scripts

The `scripts/` directory provides helpers for builds in GitHub Codespaces.
`fast-build.sh` builds under `/tmp/lchs-fast` with sources symlinked back to
the workspace. It requires bash; the standard `lake build` command above
is sufficient on an ordinary machine, including Windows.

```bash
scripts/fast-build.sh
scripts/fast-build.sh LCHSWiener.KernelUpperBound
```

`lean-errors.sh` filters build output while developing proofs.
`save-build-snapshot.sh` saves the temporary build state for later restoration.
The scripts use generated files under `.lake/`; these artifacts are
recreated from the sources and locked dependencies.
