[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)

# Formalized Complex Analysis in Lean

A small collection of formalized theorems in **complex analysis** using **Lean 4** and **mathlib**.

This repository currently contains:

- A formalization of the **Poisson integral theorem** for harmonic functions on the unit disc.  
  File: [PoissonIntegral.lean](ComplexAnalysis/PoissonIntegral.lean), reference: [MathWorld: Poisson Integral](https://mathworld.wolfram.com/PoissonIntegral.html)  
- A formalization of the **Herglotz–Riesz representation theorem** for positive harmonic functions on the unit disc.  
  File: [HerglotzRieszRepresentations.lean](ComplexAnalysis/Positive/HerglotzRieszRepresentations.lean), reference: [Wikipedia: Positive_harmonic_function](https://en.wikipedia.org/wiki/Positive_harmonic_function)  
  📄 [PDF: sketch of the proof](Docs/ProofHerglotzRiesz.pdf)
- A formalization of **Harnack's inequality** for positive harmonic functions on the unit disc.  
  File: [HarnackIneq.lean](ComplexAnalysis/Positive/HarnackIneq.lean) and [HarnackIneq2.lean](ComplexAnalysis/Positive/HarnackIneq2.lean), reference: [Wikipedia: Harnack's_inequality](https://en.wikipedia.org/wiki/Harnack%27s_inequality)

## Dependencies

- [Lean 4](https://leanprover.github.io/)
- [mathlib](https://github.com/leanprover-community/mathlib4)

## Usage

Clone the repository and build with `lake`.
