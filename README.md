[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)

# Formalized Complex Analysis in Lean

A small collection of formalized theorems in **complex analysis** using **Lean 4** and **mathlib**.

#### Possible mathlib contributions:

- The **Poisson integral theorem** for harmonic functions on the unit disc.  
  File: [PoissonIntegral.lean](ComplexAnalysis/PoissonIntegral.lean), reference: [MathWorld: Poisson Integral](https://mathworld.wolfram.com/PoissonIntegral.html)  
- The **Herglotz–Riesz representation theorem** for positive harmonic functions on the unit disc.  
  File: [HerglotzRieszRepresentations.lean](ComplexAnalysis/Positive/HerglotzRieszRepresentations.lean), reference: [Wikipedia: Positive_harmonic_function](https://en.wikipedia.org/wiki/Positive_harmonic_function)  
  📄 [PDF: sketch of the proof](Docs/ProofHerglotzRiesz.pdf)

#### Further contributions:

- **Harnack's inequality** for positive harmonic functions on the unit disc.  
  File: [HarnackIneq.lean](ComplexAnalysis/Positive/HarnackIneq.lean) 
  , reference: [Wikipedia: Harnack's_inequality](https://en.wikipedia.org/wiki/Harnack%27s_inequality)

- **Univalent functions** on the unit disc: Under the assumption that [Grönwall's area theorem](https://en.wikipedia.org/wiki/Area_theorem_(conformal_mapping)) is available, Bieberbach's theorem for the second coefficient is shown ($|a_2|\leq 2$).  
  File: [BieberbachSecondCoeff.lean](ComplexAnalysis/UnivalentFunctions/BieberbachSecondCoeff.lean) 
  , reference: [Wikipedia](https://en.wikipedia.org/wiki/De_Branges%27s_theorem)

### Dependencies

- [Lean 4](https://leanprover.github.io/)
- [mathlib](https://github.com/leanprover-community/mathlib4)

### Acknowledgements

This project was developed with the assistance of Harmonic's AI system **[Aristotle](https://aristotle.harmonic.fun/)**.


### Usage

Clone the repository and build with `lake`.
