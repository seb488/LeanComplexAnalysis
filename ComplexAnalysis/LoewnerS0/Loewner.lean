import LoewnerS0.Basic

/-!
# Herglotz vector fields, the Loewner ODE and the class `S⁰(𝔹)`

A *Herglotz vector field* (generating vector field) is a map `h : ℝ → E → E` with
`h t ∈ M(𝔹)` for `t ≥ 0` and `t ↦ h t z` measurable. Its *Loewner ODE*

  `∂ₜ v(z, t) = - h(v(z, t), t)`,  `v(z, 0) = z`,

is understood in the Carathéodory (integral) sense:
`v t z = z - ∫₀ᵗ h s (v s z) ds` with an integrable integrand.

A map `f` has *parametric representation* if `f(z) = lim_{t → ∞} eᵗ v(z, t)` for some
Herglotz vector field `h` and solution `v`; these maps form the class `S⁰(𝔹)`
[Graham–Hamada–Kohr 2002]. We also record the equivalent description by Loewner chains
(`classS0'`); the equality `classS0 = classS0'` is a theorem of Graham–Hamada–Kohr, stated in
`LoewnerS0.Roadmap`.

## Main definitions

* `LoewnerS0.IsHerglotzVF h`
* `LoewnerS0.IsLoewnerSolution h v`
* `LoewnerS0.IsParametricRep f h v`
* `LoewnerS0.classS0 E` : the class `S⁰(𝔹)`.
* `LoewnerS0.IsLoewnerChain f`, `LoewnerS0.IsLocallyBounded F`, `LoewnerS0.classS0' E`.
-/

open Complex Metric Set Filter MeasureTheory
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A *Herglotz vector field* (generating vector field) on `𝔹 × [0, ∞)`:
`h t ∈ M(𝔹)` for every `t ≥ 0`, and `t ↦ h t z` is measurable on `[0, ∞)` for every `z ∈ 𝔹`. -/
structure IsHerglotzVF (h : ℝ → E → E) : Prop where
  isCaratheodory : ∀ t, 0 ≤ t → IsCaratheodory (h t)
  aestronglyMeasurable : ∀ z ∈ unitBall E,
    AEStronglyMeasurable (fun t => h t z) (volume.restrict (Ici (0 : ℝ)))

/-- `v` solves the *Loewner ODE* `∂ₜ v = - h(v, t)`, `v(z, 0) = z`, on `[0, ∞)` in the integral
(Carathéodory) sense: for `z ∈ 𝔹` and `t ≥ 0`, `v t z ∈ 𝔹`, the map `s ↦ h s (v s z)` is
integrable on `[0, t]` and `v t z = z - ∫₀ᵗ h s (v s z) ds`. -/
def IsLoewnerSolution (h v : ℝ → E → E) : Prop :=
  ∀ z ∈ unitBall E, ∀ t, 0 ≤ t →
    v t z ∈ unitBall E ∧ IntervalIntegrable (fun s => h s (v s z)) volume 0 t ∧
      v t z = z - ∫ s in (0)..t, h s (v s z)

namespace IsLoewnerSolution

variable {h v : ℝ → E → E}

lemma mem_unitBall (hv : IsLoewnerSolution h v) {z : E} (hz : z ∈ unitBall E) {t : ℝ}
    (ht : 0 ≤ t) : v t z ∈ unitBall E :=
  (hv z hz t ht).1

lemma eq_integral (hv : IsLoewnerSolution h v) {z : E} (hz : z ∈ unitBall E) {t : ℝ}
    (ht : 0 ≤ t) : v t z = z - ∫ s in (0)..t, h s (v s z) :=
  (hv z hz t ht).2.2

/-- The initial condition `v(z, 0) = z` is part of the integral equation. -/
lemma apply_zero (hv : IsLoewnerSolution h v) {z : E} (hz : z ∈ unitBall E) :
    v 0 z = z := by
  simpa using hv.eq_integral hz le_rfl

end IsLoewnerSolution

/-- `f` has *parametric representation* with respect to the Herglotz vector field `h`, with `v`
the solution of the associated Loewner ODE: `f(z) = lim_{t → ∞} eᵗ v(z, t)` on `𝔹`. -/
structure IsParametricRep (f : E → E) (h v : ℝ → E → E) : Prop where
  herglotz : IsHerglotzVF h
  solution : IsLoewnerSolution h v
  tendsto : ∀ z ∈ unitBall E,
    Tendsto (fun t : ℝ => (Real.exp t : ℂ) • v t z) atTop (𝓝 (f z))

variable (E) in
/-- The class `S⁰(𝔹)` of normalized maps with *parametric representation*
[Graham–Hamada–Kohr 2002]. We require `E` to be complete so that Bochner integrals are
meaningful. -/
def classS0 [CompleteSpace E] : Set (E → E) :=
  {f | ∃ h v : ℝ → E → E, IsParametricRep f h v}

/-- A (normalized) *Loewner chain* on `𝔹`: each `f t` (`t ≥ 0`) is univalent and holomorphic
on `𝔹` with `f t 0 = 0` and `D(f t)(0) = eᵗ I`, and `f s (𝔹) ⊆ f t (𝔹)` for `0 ≤ s ≤ t`. -/
structure IsLoewnerChain (f : ℝ → E → E) : Prop where
  differentiableOn : ∀ t, 0 ≤ t → DifferentiableOn ℂ (f t) (unitBall E)
  injOn : ∀ t, 0 ≤ t → InjOn (f t) (unitBall E)
  map_zero : ∀ t, 0 ≤ t → f t 0 = 0
  fderiv_zero : ∀ t, 0 ≤ t →
    fderiv ℂ (f t) 0 = (Real.exp t : ℂ) • ContinuousLinearMap.id ℂ E
  image_subset : ∀ s t, 0 ≤ s → s ≤ t → f s '' unitBall E ⊆ f t '' unitBall E

/-- A family `F t` (`t ≥ 0`) of maps is *locally uniformly bounded* on `𝔹`, i.e. uniformly
bounded on every ball `‖z‖ ≤ r < 1`. For holomorphic maps of the finite dimensional ball this is
the same as being a normal family (Montel). -/
def IsLocallyBounded (F : ℝ → E → E) : Prop :=
  ∀ r < 1, ∃ C, ∀ t, 0 ≤ t → ∀ z : E, ‖z‖ ≤ r → ‖F t z‖ ≤ C

variable (E) in
/-- Maps that are the initial element of a Loewner chain `F` with `{e⁻ᵗ F t}` a normal family.
By Graham–Hamada–Kohr this is again `S⁰(𝔹)` (see `LoewnerS0.Roadmap`). -/
def classS0' : Set (E → E) :=
  {f | ∃ F : ℝ → E → E, IsLoewnerChain F ∧ EqOn (F 0) f (unitBall E) ∧
    IsLocallyBounded fun t z => (Real.exp (-t) : ℂ) • F t z}

end LoewnerS0
