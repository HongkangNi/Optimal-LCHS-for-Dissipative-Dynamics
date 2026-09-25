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
8. `KernelUpperBound.lean`: Section 3.3 explicit outer kernel, contour identity,
   total-variation bounds, and low/high lambda witnesses.
9. `Theorem1.lean`: combines sharp lower and upper bounds with `sInf`.

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

The current execution environment does not contain Lean/Lake.  Therefore this
archive has **not** been compiled here.  It should be treated as a complete
Lean source proof awaiting compiler/API verification, not as a claim that
`lake build` has already succeeded.

Expected toolchain: Lean 4.34.0 / Mathlib v4.34.0.

Suggested commands:

```bash
lake update
lake build
lake env lean LCHSWiener/Theorem1.lean
```
