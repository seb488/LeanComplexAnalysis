import LoewnerS0.Prelude

/-!
# The unit ball, normalized maps, the class `S(𝔹)` and the Carathéodory class `M(𝔹)`

Throughout, `E` is a complex inner product space (for instance `ℂⁿ = EuclideanSpace ℂ (Fin n)`)
and `𝔹 = unitBall E` is its open unit ball.

## Conventions

* *Holomorphic* means complex Fréchet differentiable: `DifferentiableOn ℂ f (unitBall E)`.
* Maps are total functions `E → E`; only their values on `𝔹` matter in the definitions.
* Mathlib's inner product `⟪x, y⟫_ℂ` is conjugate-linear in the **first** argument.
  The inner product of the geometric function theory literature (Graham–Kohr),
  `⟨w, z⟩ = ∑ⱼ wⱼ z̄ⱼ`, is therefore `⟨w, z⟩ = ⟪z, w⟫_ℂ`. The defining inequality of the
  Carathéodory class, `Re ⟨h(z), z⟩ > 0`, reads `0 < (⟪z, h z⟫_ℂ).re`.

## Main definitions

* `LoewnerS0.unitBall E` : the open unit ball `𝔹` of `E`.
* `LoewnerS0.IsNormalized f` : `f` is holomorphic on `𝔹`, `f 0 = 0` and `Df(0) = I`.
* `LoewnerS0.classS E` : normalized univalent maps of `𝔹` (the class `S(𝔹)`).
* `LoewnerS0.IsCaratheodory h` : `h` is normalized and `Re ⟨h(z), z⟩ > 0` on `𝔹 \ {0}`.
* `LoewnerS0.classM E` : the Carathéodory class `M(𝔹) = {h | IsCaratheodory h}`.

## References

* I. Graham, G. Kohr, *Geometric Function Theory in One and Higher Dimensions*, Dekker 2003.
* I. Graham, H. Hamada, G. Kohr, *Parametric representation of univalent mappings in several
  complex variables*, Canad. J. Math. 54 (2002), 324–351.
-/

open Complex Metric Set
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0

section Ball

variable (E : Type*) [NormedAddCommGroup E]

/-- The open unit ball `𝔹` of `E`. -/
abbrev unitBall : Set E := ball (0 : E) 1

variable {E}

@[simp] lemma mem_unitBall {z : E} : z ∈ unitBall E ↔ ‖z‖ < 1 := mem_ball_zero_iff

lemma isOpen_unitBall : IsOpen (unitBall E) := isOpen_ball

lemma zero_mem_unitBall : (0 : E) ∈ unitBall E := by simp

lemma unitBall_mem_nhds {z : E} (hz : z ∈ unitBall E) : unitBall E ∈ 𝓝 z :=
  isOpen_unitBall.mem_nhds hz

end Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `f` is a *normalized holomorphic map* of `𝔹`: holomorphic on `𝔹`, `f 0 = 0` and
`Df(0) = I`. -/
structure IsNormalized (f : E → E) : Prop where
  differentiableOn : DifferentiableOn ℂ f (unitBall E)
  map_zero : f 0 = 0
  fderiv_zero : fderiv ℂ f 0 = ContinuousLinearMap.id ℂ E

namespace IsNormalized

variable {f : E → E}

lemma differentiableAt (hf : IsNormalized f) {z : E} (hz : z ∈ unitBall E) :
    DifferentiableAt ℂ f z :=
  hf.differentiableOn.differentiableAt (unitBall_mem_nhds hz)

lemma differentiableAt_zero (hf : IsNormalized f) : DifferentiableAt ℂ f 0 :=
  hf.differentiableAt zero_mem_unitBall

lemma hasFDerivAt_zero (hf : IsNormalized f) :
    HasFDerivAt f (ContinuousLinearMap.id ℂ E) 0 :=
  hf.fderiv_zero ▸ hf.differentiableAt_zero.hasFDerivAt

end IsNormalized

/-- The identity map is normalized. -/
lemma isNormalized_id : IsNormalized (id : E → E) where
  differentiableOn := differentiableOn_id
  map_zero := rfl
  fderiv_zero := fderiv_id

/-- `h` satisfies the defining conditions of the Carathéodory class `M(𝔹)`: it is a normalized
holomorphic map of `𝔹` with `Re ⟨h(z), z⟩ > 0` for `z ∈ 𝔹 \ {0}` (written `0 < (⟪z, h z⟫_ℂ).re`,
see the conventions). -/
structure IsCaratheodory (h : E → E) : Prop where
  isNormalized : IsNormalized h
  re_inner_pos : ∀ z ∈ unitBall E, z ≠ 0 → 0 < (⟪z, h z⟫_ℂ).re

lemma IsCaratheodory.map_zero {h : E → E} (hh : IsCaratheodory h) : h 0 = 0 :=
  hh.isNormalized.map_zero

variable (E)

/-- The class `S(𝔹)` of normalized univalent (= biholomorphic onto the image) maps of `𝔹`. -/
def classS : Set (E → E) :=
  {f | IsNormalized f ∧ InjOn f (unitBall E)}

/-- The Carathéodory class `M(𝔹)`. -/
def classM : Set (E → E) :=
  {h | IsCaratheodory h}

variable {E}

@[simp] lemma mem_classS {f : E → E} : f ∈ classS E ↔ IsNormalized f ∧ InjOn f (unitBall E) :=
  Iff.rfl

@[simp] lemma mem_classM {h : E → E} : h ∈ classM E ↔ IsCaratheodory h := Iff.rfl

/-- In the literature's notation: `Re ⟨h(z), z⟩ = Re ⟪h z, z⟫_ℂ`, i.e. the order of the
arguments does not matter for the real part. -/
lemma re_inner_comm (z w : E) : (⟪z, w⟫_ℂ).re = (⟪w, z⟫_ℂ).re := by
  rw [← inner_conj_symm, Complex.conj_re]

end LoewnerS0
