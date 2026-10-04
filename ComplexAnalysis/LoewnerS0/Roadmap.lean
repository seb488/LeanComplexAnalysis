import LoewnerS0.Unitary
import LoewnerS0.Starlike
import LoewnerS0.StarlikeGen
import LoewnerS0.TaylorRec
import LoewnerS0.Cex.Main
import LoewnerS0.ClassM
import LoewnerS0.LoewnerODE
import LoewnerS0.LoewnerExist
import LoewnerS0.SecondCoeff
import LoewnerS0.S0Univalent
import LoewnerS0.S0Chain
import LoewnerS0.S0Coeff
import LoewnerS0.StarlikeS0
import LoewnerS0.ChainS0
import LoewnerS0.OsgoodProof

/-!
# Roadmap: the main theorems about `S⁰(𝔹)`

This file started as a list of `sorry`s, each a known theorem with a reference; replacing them,
one at a time, was the plan of the project. Nothing in the other files depends on this file.

**All statements are now proved; the file contains no `sorry`.** The last one was Osgood's theorem
(`osgood`: an injective holomorphic map of an open subset of `ℂⁿ` into `ℂⁿ` has nonvanishing
Jacobian determinant), a theorem of several complex variables that is not in mathlib; it is proved
in `LoewnerS0.OsgoodProof`, by induction on the dimension. The two inclusions
`classS0'_subset_classS0` and `classSstar_subset_classS0` are derived from it
(`LoewnerS0.ChainS0`, `LoewnerS0.StarlikeS0`). Every theorem below depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

Status: the estimates for `M(𝔹)` (`LoewnerS0.ClassM`), existence and uniqueness for the Loewner ODE
(`LoewnerS0.LoewnerExist`, `LoewnerS0.LoewnerODE`), the existence of the limit `lim eᵗ v(z, t)`
and the growth theorem (`LoewnerS0.LoewnerODE`), univalence of maps with parametric
representation (`LoewnerS0.S0Univalent`), the inclusion `S⁰(𝔹) ⊆ S⁰'(𝔹)` (`LoewnerS0.S0Chain`)
and the second coefficient bound (`LoewnerS0.S0Coeff`) are proved; their statements below just
point to the proofs. The second coefficient bound in the form originally stated here is false
(`LoewnerS0.SecondCoeff`); it has been replaced by the correct statement of
Graham–Hamada–Kohr–Kohr.

The inclusions `classS0'_subset_classS0` and `classSstar_subset_classS0` go from a univalent map to
a Loewner chain / Herglotz vector field. Both need Osgood's theorem (every map in `S⁰(𝔹)` has
invertible derivative, so each inclusion implies a special case of it); granting it, they are
proved in `LoewnerS0.ChainS0` (transition maps, Lipschitz dependence on time, Rademacher's theorem
and a Vitali-type argument for the time derivative of the chain) and `LoewnerS0.StarlikeS0`
(Suffridge's argument and the minimum principle for `M(𝔹)`).

The two research targets at the end (`a₃,₀ > 3` in `S⁰(𝔹²)`, even for starlike maps) come from the
counterexample of `disproof_starlike.tex`, formalized in `LoewnerS0.Cex`. The starlike version
`exists_classSstar_a30_gt_three` is completely proved (no `sorry`): the two general theorems it
needs, `LoewnerS0.starlikeGeneration` (every `h ∈ M(𝔹)` generates a starlike map) and
`LoewnerS0.taylorRecursion`, are proved in `LoewnerS0.StarlikeGen` and `LoewnerS0.TaylorRec`.
The `S⁰` version `exists_classS0_a30_gt_three` is proved as well (also without `sorry`): the
starlike map of the example is constructed from the flow of `h`, which is a parametric
representation (`LoewnerS0.starlikeMap_mem_classS0`); the general inclusion
`classSstar_subset_classS0` below is not needed for it.

References:
* [GHK02] I. Graham, H. Hamada, G. Kohr, *Parametric representation of univalent mappings in
  several complex variables*, Canad. J. Math. 54 (2002), 324–351.
* [GK03] I. Graham, G. Kohr, *Geometric Function Theory in One and Higher Dimensions*,
  Dekker 2003, Chapters 6 and 8.
* [Suf70] T. J. Suffridge, *The principle of subordination applied to functions of several
  variables*, Pacific J. Math. 33 (1970).
* [GHKK09] I. Graham, H. Hamada, G. Kohr, M. Kohr, *Asymptotically spirallike mappings in several
  complex variables*, J. Math. Anal. Appl. 353 (2009) (coefficient bounds for `S⁰(𝔹)`).
* [Nar71] R. Narasimhan, *Several complex variables*, Chicago Lectures in Mathematics, 1971
  (Osgood's theorem).
-/

open Complex Metric Set Filter MeasureTheory
open scoped InnerProductSpace Topology

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### Osgood's theorem -/

/-- **Osgood's theorem** (W. F. Osgood, 1899; see e.g. [Nar71] or the Encyclopedia of Mathematics,
*Holomorphic mapping*): an injective holomorphic map of an open subset of a finite-dimensional
complex normed space `V` into `V` has nonvanishing Jacobian determinant
(`LoewnerS0.OsgoodTheorem`). Proved in `LoewnerS0.OsgoodProof`, by induction on the dimension:
the one-variable case is a `k`-th root argument (`LoewnerS0.OsgoodOneDim`); if `Df(z) ≠ 0`, a slice
through `z` reduces the dimension (`LoewnerS0.OsgoodSlice`); and `Df(z) = 0` is impossible, because
then `det Df` would vanish on a Lipschitz curve along which `f` is constant
(`LoewnerS0.OsgoodCurve`). -/
theorem osgood {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] :
    OsgoodTheorem V :=
  osgoodTheorem

/-! ### The Carathéodory class -/

/-- Growth estimate for the Carathéodory class (Pfaltzgraff 1974; see [GK03, Ch. 6]
and [GHK02, Theorem 1.2]). Proved in `LoewnerS0.ClassM`. -/
theorem classM_norm_le [FiniteDimensional ℂ E] {h : E → E} (hh : h ∈ classM E) {z : E}
    (hz : z ∈ unitBall E) : ‖h z‖ ≤ 4 * ‖z‖ / (1 - ‖z‖) ^ 2 :=
  IsCaratheodory.norm_le hh hz

/-- Lower bound for `Re ⟨h(z), z⟩` (Pfaltzgraff 1974; see [GK03, Ch. 6]).
Proved in `LoewnerS0.ClassM`. -/
theorem classM_re_inner_ge [FiniteDimensional ℂ E] {h : E → E} (hh : h ∈ classM E) {z : E}
    (hz : z ∈ unitBall E) : ‖z‖ ^ 2 * (1 - ‖z‖) / (1 + ‖z‖) ≤ (⟪z, h z⟫_ℂ).re :=
  IsCaratheodory.re_inner_ge hh hz

/-! ### The Loewner ODE -/

variable [CompleteSpace E]

/-- Existence of solutions of the Loewner ODE [GHK02]. Proved in `LoewnerS0.LoewnerExist`
(Picard iteration for the measurable-in-time field, `LoewnerS0.Picard`). -/
theorem exists_isLoewnerSolution [FiniteDimensional ℂ E] {h : ℝ → E → E}
    (hh : IsHerglotzVF h) : ∃ v, IsLoewnerSolution h v :=
  hh.exists_isLoewnerSolution

/-- Uniqueness of solutions of the Loewner ODE [GHK02]. Proved in `LoewnerS0.LoewnerODE`
(Gronwall's inequality for absolutely continuous functions). -/
theorem IsLoewnerSolution.eqOn [FiniteDimensional ℂ E] {h v w : ℝ → E → E}
    (hh : IsHerglotzVF h) (hv : IsLoewnerSolution h v) (hw : IsLoewnerSolution h w) {t : ℝ}
    (ht : 0 ≤ t) : EqOn (v t) (w t) (unitBall E) :=
  hv.eqOn_of_isHerglotzVF hh hw ht

/-- The limit `lim_{t → ∞} eᵗ v(z, t)` exists for every Herglotz vector field [GHK02],
so every Herglotz vector field generates an element of `S⁰(𝔹)`. Proved in
`LoewnerS0.LoewnerODE`. -/
theorem exists_isParametricRep [FiniteDimensional ℂ E] {h v : ℝ → E → E}
    (hh : IsHerglotzVF h) (hv : IsLoewnerSolution h v) : ∃ f, IsParametricRep f h v :=
  hv.exists_isParametricRep hh

/-! ### The class `S⁰(𝔹)` -/

/-- Maps with parametric representation are univalent [GHK02]. Proved in
`LoewnerS0.S0Univalent` (holomorphy of the solutions in the initial value, `LoewnerS0.LoewnerHolo`,
and a lower Gronwall bound for the distance of two trajectories). -/
theorem classS0_subset_classS [FiniteDimensional ℂ E] : classS0 E ⊆ classS E :=
  fun _ hf => mem_classS_of_mem_classS0 hf

/-- Maps with parametric representation are initial elements of Loewner chains with
`{e⁻ᵗ f(·, t)}` locally bounded [GHK02]. Proved in `LoewnerS0.S0Chain`. -/
theorem classS0_subset_classS0' [FiniteDimensional ℂ E] : classS0 E ⊆ classS0' E :=
  fun _ hf => mem_classS0'_of_mem_classS0 hf

/-- Initial elements of Loewner chains with `{e⁻ᵗ f(·, t)}` locally bounded have parametric
representation [GHK02]. Derived from Osgood's theorem in `LoewnerS0.ChainS0`: the transition maps
`v(z, s, t) = F_t⁻¹(F_s(z))` give `‖z - v(z, s, t)‖ ≤ (t - s) 4‖z‖/(1-‖z‖)²`, so the chain is
locally Lipschitz in time; by Rademacher's theorem on a dense set and a Vitali-type argument it has
a holomorphic time derivative for almost every `t`, and `h = DF_t⁻¹ ∂_t F` is a Herglotz vector
field whose Loewner ODE is solved by `v(z, 0, t)`. -/
theorem classS0'_subset_classS0 [FiniteDimensional ℂ E] : classS0' E ⊆ classS0 E :=
  classS0'_subset_classS0_of_osgood osgood

/-- Characterization of `S⁰(𝔹)` by Loewner chains whose normalization `e⁻ᵗ f(·, t)` is a normal
family [GHK02]. -/
theorem classS0_eq_classS0' [FiniteDimensional ℂ E] : classS0 E = classS0' E :=
  Set.Subset.antisymm classS0_subset_classS0' classS0'_subset_classS0

/-- Growth theorem for `S⁰(𝔹)` [GHK02, Corollary 2.4]. Proved in `LoewnerS0.LoewnerODE`. -/
theorem classS0_growth [FiniteDimensional ℂ E] {f : E → E} (hf : f ∈ classS0 E) {z : E}
    (hz : z ∈ unitBall E) :
    ‖z‖ / (1 + ‖z‖) ^ 2 ≤ ‖f z‖ ∧ ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 :=
  classS0_norm_bounds hf hz

/-- Second coefficient bound `|⟨D²f(0)(w, w)/2, w⟩| ≤ 2 ‖w‖³` for `f ∈ S⁰(𝔹)` [GHKK09].
Proved in `LoewnerS0.S0Coeff`, as an infinitesimal form of the growth theorem.

This statement replaces the original roadmap item `‖D²f(0)(w, w)/2‖ ≤ 2 ‖w‖²`, which is false
in dimension two, even for starlike maps: see `classS0_second_coeff_norm_bound_false` below. -/
theorem classS0_second_coeff [FiniteDimensional ℂ E] {f : E → E} (hf : f ∈ classS0 E) (w : E) :
    ‖⟪w, (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 f 0 (fun _ => w)⟫_ℂ‖ ≤ 2 * ‖w‖ ^ 3 :=
  classS0_norm_inner_second_coeff_le hf w

/-- The norm bound `‖D²f(0)(w, w)/2‖ ≤ 2 ‖w‖²` fails on `S⁰(𝔹²)` (and on `S*(𝔹²)`): the starlike
map generated by `h(z) = z + (5/2) z₁² e₂` has `D²f(0)(e₁, e₁)/2 = -(5/2) e₂`.
Proved in `LoewnerS0.SecondCoeff`. -/
theorem classS0_second_coeff_norm_bound_false :
    ¬ ∀ f ∈ classS0 (EuclideanSpace ℂ (Fin 2)), ∀ w : EuclideanSpace ℂ (Fin 2),
      ‖(2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 f 0 (fun _ => w)‖ ≤ 2 * ‖w‖ ^ 2 :=
  SecondCoeff.not_classS0_second_coeff

/-! ### Starlike maps -/

/-- Starlike maps have parametric representation (via the autonomous chain `eᵗ f`)
[GK03, Ch. 6]. Derived from Osgood's theorem in `LoewnerS0.StarlikeS0`: `f` is biholomorphic onto
`f(𝔹)`, `h = Df⁻¹ f ∈ M(𝔹)` by Suffridge's Schwarz lemma argument and the minimum principle, and
`eᵗ f(φ_t(z)) = f(z)` along the flow `φ_t` of `h`, so `f = lim eᵗ φ_t`. -/
theorem classSstar_subset_classS0 [FiniteDimensional ℂ E] : classSstar E ⊆ classS0 E :=
  classSstar_subset_classS0_of_osgood osgood

/- `starlikeGeneration : StarlikeGeneration E` (every `h ∈ M(𝔹)` generates a starlike map with
`Df(z) h(z) = f(z)`, [Suf70], [GK03, Ch. 6]) and `taylorRecursion : TaylorRecursion E` (Corollary
2.2 of `disproof_starlike.tex`) were on this list; they are now proved, for every
finite-dimensional `E`, in `LoewnerS0.StarlikeGen` and `LoewnerS0.TaylorRec`. -/

/-! ### The third coefficient -/

/-- **Theorem 1.1 of `disproof_starlike.tex`**: there is a starlike map `f` of `𝔹²` with
`a_{3,0}(f) = 2863108143393914687/954177312400000000 = 3.000603877… > 3`.
Proved without `sorry`, in `LoewnerS0.Cex`. -/
theorem exists_classSstar_a30_gt_three :
    ∃ f ∈ classSstar (EuclideanSpace ℂ (Fin 2)), 3 < (a30 f e₁).re :=
  Cex.exists_classSstar_a30_gt_three

/-- There is `f ∈ S⁰(𝔹²)` with `a_{3,0}(f) > 3`. Proved without `sorry`, in `LoewnerS0.Cex`. -/
theorem exists_classS0_a30_gt_three :
    ∃ f ∈ classS0 (EuclideanSpace ℂ (Fin 2)), 3 < (a30 f e₁).re :=
  Cex.exists_classS0_a30_gt_three

end LoewnerS0
