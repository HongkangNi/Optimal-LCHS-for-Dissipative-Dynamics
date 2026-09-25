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

## Verification status

The project compiles with Lean 4.34.0 / Mathlib v4.34.0 (`lake build`), and

```
'LCHSWiener.wiener_theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only the standard Lean axioms are used; there is no `sorry`, `admit` or
project-local axiom.

The top-level `Mathlib.olean` is missing from the v4.34.0 cache, so no file may
`import Mathlib`; use specific module imports instead.

In this Codespace `/workspaces` is a slow loop device, so build from a copy on
local disk:

```bash
scripts/fast-build.sh            # whole library
scripts/fast-build.sh LCHSWiener.KernelUpperBound   # one module
```
