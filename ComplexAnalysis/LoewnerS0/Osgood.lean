import LoewnerS0.SCV
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Osgood's theorem (statement) and holomorphic inverses

**Osgood's theorem** (W. F. Osgood, 1899): if `U ⊆ ℂⁿ` is open and `f : U → ℂⁿ` is holomorphic and
injective, then the complex Jacobian determinant of `f` vanishes nowhere on `U`. In one variable this
is the familiar fact that a univalent function has a nonvanishing derivative; in several variables
it is a genuine theorem of several complex variables (its proofs use the local theory of analytic
sets, see [Nar71], [Chi89], or [EoM, *Holomorphic mapping*]), and it is not in mathlib.

Here it is stated as a proposition, `LoewnerS0.OsgoodTheorem E`; the theorem itself is assumed (as
a single `sorry`) in `LoewnerS0.Roadmap`, and everything that depends on it in this project takes
`hO : OsgoodTheorem E` as a hypothesis.

## Main results

Let `f` be holomorphic and injective on an open set `U` of a finite-dimensional complex normed
space `E`, and assume Osgood's theorem. Then
* `OsgoodTheorem.exists_equiv`: `Df(z)` is a continuous linear equivalence for `z ∈ U`;
* `OsgoodTheorem.isOpen_image`: `f(U)` is open;
* `OsgoodTheorem.hasFDerivAt_invFunOn`: the inverse `g = invFunOn f U` of `f` on `f(U)` has
  derivative `Df(z)⁻¹` at `f(z)`;
* `OsgoodTheorem.differentiableOn_invFunOn`: `g` is holomorphic on `f(U)`.

The last three are consequences of the inverse function theorem, and hold under the weaker
assumption that `det Df(z) ≠ 0` on `U` (`isOpen_image_of_det_ne_zero`,
`hasFDerivAt_invFunOn_of_det_ne_zero`).

## References

* [Nar71] R. Narasimhan, *Several complex variables*, Chicago Lectures in Mathematics, 1971.
* [Chi89] E. M. Chirka, *Complex analytic sets*, Kluwer, 1989.
* [EoM] *Holomorphic mapping*, Encyclopedia of Mathematics,
  <https://encyclopediaofmath.org/wiki/Holomorphic_mapping>.
-/

open Function Set Filter
open scoped Topology

noncomputable section

namespace LoewnerS0

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Osgood's theorem**: an injective holomorphic map of an open subset `U` of `E` into `E` has
a nonvanishing Jacobian determinant `det Df(z)` at every point of `U`. (It is meant for
finite-dimensional `E`, and it is stated as a proposition: it is not in mathlib.) -/
def OsgoodTheorem : Prop :=
  ∀ (f : E → E) (U : Set E), IsOpen U → DifferentiableOn ℂ f U → InjOn f U →
    ∀ z ∈ U, (fderiv ℂ f z).det ≠ 0

variable {E} [FiniteDimensional ℂ E] {f : E → E} {U : Set E}

/-- A holomorphic map of an open set is strictly differentiable. -/
lemma hasStrictFDerivAt_of_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z : E} (hz : z ∈ U) : HasStrictFDerivAt f (fderiv ℂ f z) z :=
  ((hf.contDiffOn_of_isOpen hU 1).contDiffAt (hU.mem_nhds hz)).hasStrictFDerivAt (by simp)

/-- The derivative of `f`, when its determinant is nonzero, as a continuous linear equivalence. -/
def derivEquiv (f : E → E) (z : E) (hdet : (fderiv ℂ f z).det ≠ 0) : E ≃L[ℂ] E :=
  (fderiv ℂ f z).toContinuousLinearEquivOfDetNeZero hdet

@[simp] lemma coe_derivEquiv {z : E} (hdet : (fderiv ℂ f z).det ≠ 0) :
    (derivEquiv f z hdet : E →L[ℂ] E) = fderiv ℂ f z :=
  ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _

lemma derivEquiv_apply {z : E} (hdet : (fderiv ℂ f z).det ≠ 0) (v : E) :
    derivEquiv f z hdet v = fderiv ℂ f z v :=
  rfl

/-- If `Df(z)` is invertible, `f` maps neighbourhoods of `z` onto neighbourhoods of `f(z)`. -/
lemma image_mem_nhds_of_det_ne_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {z : E}
    (hz : z ∈ U) (hdet : (fderiv ℂ f z).det ≠ 0) {s : Set E} (hs : s ∈ 𝓝 z) :
    f '' s ∈ 𝓝 (f z) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have h1 := hasStrictFDerivAt_of_differentiableOn hU hf hz
  rw [← coe_derivEquiv hdet] at h1
  rw [← h1.map_nhds_eq_of_equiv]
  exact image_mem_map hs

/-- A holomorphic map with invertible derivative on an open set `U` maps `U` to an open set. -/
theorem isOpen_image_of_det_ne_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hdet : ∀ z ∈ U, (fderiv ℂ f z).det ≠ 0) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  exact image_mem_nhds_of_det_ne_zero hU hf hz (hdet z hz) (hU.mem_nhds hz)

/-- **Holomorphic inverse.** If `f` is holomorphic and injective on an open set `U` and `Df(z)` is
invertible, then `g = invFunOn f U` has derivative `Df(z)⁻¹` at `f(z)`. -/
theorem hasFDerivAt_invFunOn_of_det_ne_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {z : E} (hz : z ∈ U) (hdet : (fderiv ℂ f z).det ≠ 0) :
    HasFDerivAt (invFunOn f U) ((derivEquiv f z hdet).symm : E →L[ℂ] E) (f z) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have h1 := hasStrictFDerivAt_of_differentiableOn hU hf hz
  rw [← coe_derivEquiv hdet] at h1
  have hg : ∀ᶠ x in 𝓝 z, invFunOn f U (f x) = x :=
    eventually_of_mem (hU.mem_nhds hz) fun x hx => hinj.leftInvOn_invFunOn hx
  exact (h1.to_local_left_inverse hg).hasFDerivAt

namespace OsgoodTheorem

variable (hO : OsgoodTheorem E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
include hO hU hf hinj

/-- Under Osgood's theorem, the derivative of an injective holomorphic map is a continuous linear
equivalence. -/
theorem exists_equiv {z : E} (hz : z ∈ U) : ∃ e : E ≃L[ℂ] E, (e : E →L[ℂ] E) = fderiv ℂ f z :=
  ⟨derivEquiv f z (hO f U hU hf hinj z hz), coe_derivEquiv _⟩

/-- Under Osgood's theorem, an injective holomorphic map is open. -/
theorem isOpen_image : IsOpen (f '' U) :=
  isOpen_image_of_det_ne_zero hU hf (hO f U hU hf hinj)

/-- Under Osgood's theorem, the inverse `g = invFunOn f U` of an injective holomorphic map `f` has
derivative `Df(z)⁻¹` at `f(z)`. -/
theorem hasFDerivAt_invFunOn {z : E} (hz : z ∈ U) :
    ∃ e : E ≃L[ℂ] E, (e : E →L[ℂ] E) = fderiv ℂ f z ∧
      HasFDerivAt (invFunOn f U) (e.symm : E →L[ℂ] E) (f z) :=
  ⟨_, coe_derivEquiv (hO f U hU hf hinj z hz),
    hasFDerivAt_invFunOn_of_det_ne_zero hU hf hinj hz (hO f U hU hf hinj z hz)⟩

/-- Under Osgood's theorem, the inverse of an injective holomorphic map is holomorphic on the
image. -/
theorem differentiableOn_invFunOn : DifferentiableOn ℂ (invFunOn f U) (f '' U) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨e, -, he⟩ := hasFDerivAt_invFunOn hO hU hf hinj hz
  exact he.differentiableAt.differentiableWithinAt

/-- `Df(z) (Dg(f z) v) = v` for the inverse `g` of `f`. -/
theorem fderiv_apply_fderiv_invFunOn {z : E} (hz : z ∈ U) (v : E) :
    fderiv ℂ f z (fderiv ℂ (invFunOn f U) (f z) v) = v := by
  obtain ⟨e, he, hg⟩ := hasFDerivAt_invFunOn hO hU hf hinj hz
  rw [hg.fderiv, ← he]
  exact e.apply_symm_apply v

end OsgoodTheorem

end LoewnerS0
