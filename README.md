# LCHS Wiener minimax formalization

This project is a source-complete Lean 4 formalization attempt of the Wiener /
Fourier--Stieltjes version of Section 3, Theorem 1 in the accompanying note.

## Target

For `R > 0` and `lam >= 0`, with

- `pR R = 2 * arctan R / pi`,
- `qR R = 1 - pR R`,

prove

```lean
wienerMinimax R lam =
  if lam <= pR R then 1 - lam
  else qR R * (pR R / lam) ^ (pR R / qR R)
```

The exported theorem is

```lean
LCHSWiener.wiener_theorem1
```

and the packaged proposition is inhabited by

```lean
LCHSWiener.WienerTheorem1
```

## Proof structure

1. `DualFunction.lean`: Section 3.1 dual Schur function and boundary values.
2. `HalfLineKernel.lean`, `ShiftedDualTransform.lean`,
   `ShiftedRateBranch.lean`, `OscillatoryIntegral.lean`,
   `KernelTransform.lean`: explicit positive-half-line transform calculation.
3. `ConvolutionExponential.lean`: positive convolution exponential in `L1`.
4. `HalfLineRepresentation.lean`: the shifted dual function as a one-sided
   Fourier--Stieltjes transform.
5. `VectorMeasureFubini.lean`: Fubini interchange for finite complex measures.
6. `WienerDualBound.lean`: Section 3.2 dual lower bound and the two lambda
   branches.
7. `DensityMeasure.lean`: finite complex measures from integrable densities.
8. `CauchyFourier.lean`: Fourier transform of the Cauchy density (via Fourier
   inversion of `e^{-|x|}`).
9. `KernelUpperBound.lean`: Section 3.3 explicit outer kernel.  Its half-line
   Fourier transform is computed without contour integration, from the
   half-line representation of `Phi_{R,-C}(.-is)`, Fubini against the Cauchy
   density and `s -> 0`; plus total-variation bounds and low/high lambda
   witnesses.
10. `Theorem1.lean`: combines sharp lower and upper bounds with `sInf`.

## Source audit

The source tree contains no use of `sorry`, `admit`, or project-local axioms,
and the earlier abstract convolution-exponential existence interface has been
removed.

`Theorem1.lean` ends with

```lean
#print axioms LCHSWiener.wiener_theorem1
#print axioms LCHSWiener.WienerTheorem1
```

so a local build gives an immediate dependency audit.

## Matrix version (in progress)

`LCHSWiener/MatrixTarget.lean` states the matrix-model version of Theorem 1
(eq. (3.3) of the note) as `MatrixTheorem1Statement`, and the realization
lemma of Section 4 as `RealizationLemma`. Both are stated for `d × d` complex
matrices of every dimension `d`, with the operator norm.

- `HalfPlanePoisson.lean`: Poisson formula at `-i` for bounded holomorphic
  functions on the lower half-plane (vector-valued).
- `OperatorLCHS.lean`: `‖e^{-i(zX+Y)}‖ ≤ 1` for `Im z ≤ 0`, analyticity in `z`,
  and operator-valued integrals against complex measures.
- `MatrixLCHS.lean`: the matrix LCHS identities
  `∫ w(k) e^{-i(kX+Y)} dk = e^{-(X+iY)}` for the Cauchy kernel and the outer
  kernel, and the upper-bound witnesses for both branches.
- `MatrixLowerBound.lean`: the dual inequality (3.7) and the sharp lower bound,
  assuming `RealizationLemma`.
- `MatrixTheorem1.lean`: `MatrixTheorem1_of_realization :
  RealizationLemma → MatrixTheorem1Statement`.
- `PolyApprox.lean`: Section 4.1, approximation of `Φ` on `K ∪ {-i}` by
  `P(e^{-ihz})` with `|P| ≤ 1` on the closed unit disc.
- `Realization.lean`: `PolynomialRealization → RealizationLemma`, where
  `PolynomialRealization` is the part of Sections 4.2–4.3 still to be
  formalized (GQSP decomposition and the finite Fourier clock).

The upper bound is proved unconditionally; the lower bound currently depends on
`PolynomialRealization`.

## Verification status

The project compiles with Lean 4.34.0 / Mathlib v4.34.0, and

```
'LCHSWiener.wiener_theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only the standard Lean axioms are used; there is no `sorry`, `admit` or
project-local axiom.

## How to check the proof

These steps work on Windows, macOS and Linux.

1. Install [elan](https://lean-lang.org/install/), the Lean version manager.
   The Lean 4 VS Code extension can also install it for you.
2. Build:

   ```bash
   git clone <repository-url>
   cd lchs-wiener-full
   lake exe cache get   # download prebuilt Mathlib (a few minutes)
   lake build           # check this project (about a minute)
   ```

   `lean-toolchain` pins Lean 4.34.0 and `lake-manifest.json` pins the exact
   Mathlib revision, so do not run `lake update`.
3. The proof is checked if the output ends with `Build completed
   successfully` and the axiom list printed for `wiener_theorem1` (from
   `#print axioms` at the end of `Theorem1.lean`) is exactly
   `[propext, Classical.choice, Quot.sound]`. Any `sorryAx` or project-local
   axiom in that list would mean the proof is incomplete.

After `lake build`, opening the files in VS Code also shows the per-file
checks.

The theorem statement to review is `WienerTheorem1Statement` in
`LCHSWiener/Target.lean`, together with the definitions it uses in
`LCHSWiener/Core.lean` and `LCHSWiener/MeasureFourier.lean`.
`Theorem1.lean` proves `WienerTheorem1 : WienerTheorem1Statement`.

Do not `import Mathlib` in any file. The top-level `Mathlib.olean` is missing
from the v4.34.0 cache, so that import would force a very long local build.
Import specific Mathlib modules instead.

### GitHub Codespaces only

Use a machine type with at least 4 cores and 16 GB of RAM.
On the 2-core / 8 GB machine, Mathlib's compiled files do not fit in memory and
are constantly re-read from disk, so building a single file takes minutes.
On 4 cores / 16 GB, a full build of this project takes about 20 seconds.
To change it, open the Codespace's menu on github.com/codespaces and choose
"Change machine type"; the new type takes effect after the Codespace restarts.

In a Codespace, `/workspaces` is a slow, persistent disk image, while `/tmp`
is fast local disk that is wiped when the Codespace stops.
`scripts/fast-build.sh` builds from a copy under `/tmp/lchs-fast`, with the
sources symlinked back to the workspace. It needs bash, so it does not run
natively on Windows. It is not needed on an ordinary machine.

```bash
scripts/fast-build.sh                               # whole library
scripts/fast-build.sh LCHSWiener.KernelUpperBound   # one module
```
