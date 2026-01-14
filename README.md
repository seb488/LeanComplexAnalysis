[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)

# Formalized Complex Analysis in Lean

A small collection of formalized theorems in **complex analysis** using **Lean 4** and **mathlib**.

This repository currently contains:

- A formalization of the **Poisson integral theorem** for harmonic functions on the unit disc.  
  [MathWorld: Poisson Integral](https://mathworld.wolfram.com/PoissonIntegral.html)
- A formalization of the **Herglotz–Riesz representation theorem** for positive harmonic functions on the unit disc.  
  [Wikipedia: Positive_harmonic_function](https://en.wikipedia.org/wiki/Positive_harmonic_function)

## Dependencies

- [Lean 4](https://leanprover.github.io/)
- [mathlib](https://github.com/leanprover-community/mathlib4)

## Usage

Clone the repository and build with `lake`:

```bash
git clone https://github.com/<your-username>/<repo-name>.git
cd <repo-name>
lake update
lake build
