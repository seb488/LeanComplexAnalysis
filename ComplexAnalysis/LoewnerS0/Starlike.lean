import LoewnerS0.Loewner

/-!
# Starlike maps and the coefficient `a₃,₀`

* `LoewnerS0.classSstar E`: normalized starlike maps of `𝔹`.
* `LoewnerS0.a30 f u = ⟨D³f(0)(u, u, u)/3!, u⟩`; for `ℂ²` and `u = e₁` this is the coefficient
  of `z₁³` in `f₁`.
* Two standard facts of Loewner theory, stated as propositions (they are proved in the
  literature, and are on the roadmap of this project):
  * `StarlikeGeneration E`: every `h ∈ M(𝔹)` is the generator of a starlike map `f`,
    i.e. `Df(z) h(z) = f(z)` (Suffridge 1970; [GK03, Ch. 6]);
  * `TaylorRecursion E`: comparing Taylor coefficients in `Df · h = f` gives the third
    coefficient of `f` in terms of the Taylor expansion of `h` to order 3
    (Corollary 2.2 of `disproof_starlike.tex`).
-/

open Complex Metric Set
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (E) in
/-- Normalized starlike maps of `𝔹`. -/
def classSstar : Set (E → E) :=
  {f | f ∈ classS E ∧ StarConvex ℝ (0 : E) (f '' unitBall E)}

/-- The coefficient `a_{3,0}(f) = ⟨D³f(0)(u, u, u)/3!, u⟩` in the direction of a unit vector `u`.
For `E = ℂ²` and `u = e₁` this is the coefficient of `z₁³` in `f₁`. -/
def a30 (f : E → E) (u : E) : ℂ :=
  ⟪u, (6 : ℂ)⁻¹ • iteratedFDeriv ℂ 3 f 0 (fun _ => u)⟫_ℂ

/-- The standard basis vector `e₁ = (1, 0)` of `ℂ²`. -/
abbrev e₁ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

variable (E) in
/-- Every `h ∈ M(𝔹)` generates a normalized starlike map `f` with `Df(z) h(z) = f(z)` on `𝔹`
(the map produced by the constant Loewner chain `h(·, t) = h`). -/
def StarlikeGeneration : Prop :=
  ∀ h : E → E, IsCaratheodory h →
    ∃ f ∈ classSstar E, ∀ z ∈ unitBall E, fderiv ℂ f z (h z) = f z

variable (E) in
/-- If `Df(z) h(z) = f(z)` for normalized holomorphic `f`, `h`, and
`h(z) = z + B(z, z) + C(z, z, z) + O(‖z‖⁴)`, then
`D³f(0)(u, u, u)/3! = (B(u, B(u, u)) + B(B(u, u), u) - C(u, u, u))/2`. -/
def TaylorRecursion : Prop :=
  ∀ (f h : E → E) (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) E)
    (C : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) E) (K δ : ℝ),
    IsNormalized f → IsNormalized h → (∀ z ∈ unitBall E, fderiv ℂ f z (h z) = f z) → 0 < δ →
    (∀ z : E, ‖z‖ < δ → ‖h z - z - B ![z, z] - C ![z, z, z]‖ ≤ K * ‖z‖ ^ 4) →
    ∀ u : E, (6 : ℂ)⁻¹ • iteratedFDeriv ℂ 3 f 0 (fun _ => u) =
      (2 : ℂ)⁻¹ • (B ![u, B ![u, u]] + B ![B ![u, u], u] - C ![u, u, u])

end LoewnerS0
