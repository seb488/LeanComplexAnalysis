import LoewnerS0.Osgood
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Osgood's theorem: the slicing step

Let `f` be holomorphic and injective on an open set `U` of a finite-dimensional complex normed
space `V` of dimension `n`, and assume Osgood's theorem in dimension `n - 1` (for the hyperplanes of
`V`). If `Df(z₀) ≠ 0`, then `Df(z₀)` is injective (`LoewnerS0.injective_fderiv_of_ne_zero`).

Proof: choose a functional `ℓ` with `ℓ (Df(z₀) u) = 1`; the map `Φ(z) = (ℓ(f(z)), P(z - z₀))`, with
`P` the projection onto `H = ker (ℓ ∘ Df(z₀))` along `u`, is a local biholomorphism at `z₀` (inverse
function theorem); let `Ψ` be its inverse. In the coordinates `(a, h) ∈ ℂ × H` given by `Φ`, the first
coordinate of `f` is `a`, so for `a₀ = ℓ(f(z₀))` the slice `h ↦ f(Ψ(a₀, h))` maps into the affine
hyperplane `ℓ = a₀`. Identifying `ker ℓ` with `H`, we obtain an injective holomorphic map
`G : H → H` near `0`; by the induction hypothesis `DG(0)` is injective. If `Df(z₀) x = 0`, then
`x ∈ H` and `DG(0) x = 0`, so `x = 0`.
-/

open Function Set Filter Module
open scoped Topology

noncomputable section

namespace LoewnerS0

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Osgood's theorem in the form "the derivative of an injective holomorphic map of an open set is
injective". -/
def OsgoodInj : Prop :=
  ∀ (f : V → V) (U : Set V), IsOpen U → DifferentiableOn ℂ f U → InjOn f U →
    ∀ z ∈ U, Injective (fderiv ℂ f z)

variable {V} [FiniteDimensional ℂ V]

/-- `finrank (ker L) + 1 = finrank V` for a nonzero functional `L`. -/
lemma finrank_ker_add_one {L : V →L[ℂ] ℂ} {u : V} (hu : L u = 1) :
    finrank ℂ (LinearMap.ker (L : V →ₗ[ℂ] ℂ)) + 1 = finrank ℂ V := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (L : V →ₗ[ℂ] ℂ)
  have h2 : LinearMap.range (L : V →ₗ[ℂ] ℂ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • u, by simp [hu]⟩
  rw [h2, finrank_top, Module.finrank_self] at h1
  omega

/-- **The slicing step** of the proof of Osgood's theorem. -/
theorem injective_fderiv_of_ne_zero
    (IH : ∀ H : Submodule ℂ V, finrank ℂ H + 1 = finrank ℂ V → OsgoodInj H)
    {f : V → V} {U : Set V} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    {z₀ : V} (hz₀ : z₀ ∈ U) (hne : fderiv ℂ f z₀ ≠ 0) : Injective (fderiv ℂ f z₀) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set A := fderiv ℂ f z₀ with hA
  -- a vector `u` with `A u ≠ 0` and a functional `ℓ` with `ℓ (A u) = 1`
  obtain ⟨u, hu⟩ : ∃ u, A u ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (ContinuousLinearMap.ext h)
  set u₁ := A u with hu₁
  obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ u₁ (norm_ne_zero_iff.mpr hu)
  have hgu : g u₁ ≠ 0 := by
    rw [hg]; simpa using hu
  set ℓ : StrongDual ℂ V := (g u₁)⁻¹ • g with hℓ
  have hℓu₁ : ℓ u₁ = 1 := by
    rw [hℓ, smul_apply, smul_eq_mul, inv_mul_cancel₀ hgu]
  -- `L = ℓ ∘ A`, the hyperplane `H = ker L` and the projection `P` onto `H` along `u`
  set L : V →L[ℂ] ℂ := ℓ.comp A with hL
  have hLu : L u = 1 := hℓu₁
  set H : Submodule ℂ V := LinearMap.ker (L : V →ₗ[ℂ] ℂ) with hH
  have hHrank : finrank ℂ H + 1 = finrank ℂ V := finrank_ker_add_one hLu
  have hPmem : ∀ x, (ContinuousLinearMap.id ℂ V - L.smulRight u) x ∈ H := by
    intro x
    simp [hH, hLu]
  set P : V →L[ℂ] H := (ContinuousLinearMap.id ℂ V - L.smulRight u).codRestrict H hPmem with hP
  have hPx : ∀ x, (P x : V) = x - L x • u := fun x => by simp [hP]
  -- the hyperplane `K = ker ℓ`, the projection `πK` onto it along `u₁`, and `K ≃ H`
  set K : Submodule ℂ V := LinearMap.ker (ℓ : V →ₗ[ℂ] ℂ) with hK
  have hKrank : finrank ℂ K + 1 = finrank ℂ V := finrank_ker_add_one hℓu₁
  have hπmem : ∀ x, (ContinuousLinearMap.id ℂ V - ℓ.smulRight u₁) x ∈ K := by
    intro x
    simp [hK, hℓu₁]
  set πK : V →L[ℂ] K := (ContinuousLinearMap.id ℂ V - ℓ.smulRight u₁).codRestrict K hπmem
    with hπK
  have hπKx : ∀ x, (πK x : V) = x - ℓ x • u₁ := fun x => by simp [hπK]
  set eK : K ≃L[ℂ] H :=
    (LinearEquiv.ofFinrankEq K H (by omega)).toContinuousLinearEquiv with heK
  -- the derivative of `Φ` at `z₀`, as an equivalence `V ≃ ℂ × H`
  set inv : ℂ × H →L[ℂ] V := (ContinuousLinearMap.fst ℂ ℂ H).smulRight u +
    H.subtypeL.comp (ContinuousLinearMap.snd ℂ ℂ H) with hinv
  have hinv_apply : ∀ y : ℂ × H, inv y = y.1 • u + (y.2 : V) := fun y => by simp [hinv]
  have h1 : LeftInverse inv (L.prod P) := by
    intro x
    rw [hinv_apply]
    simp only [ContinuousLinearMap.prod_apply, hPx]
    abel
  have h2 : RightInverse inv (L.prod P) := by
    intro y
    have hy2 : L (y.2 : V) = 0 := y.2.2
    have hLy : L (inv y) = y.1 := by
      rw [hinv_apply, map_add, map_smul, hLu, hy2, smul_eq_mul, mul_one, add_zero]
    refine Prod.ext ?_ ?_
    · exact hLy
    · apply Subtype.ext
      simp only [ContinuousLinearMap.prod_apply]
      rw [hPx, hLy, hinv_apply]
      abel
  set e : V ≃L[ℂ] ℂ × H := ContinuousLinearEquiv.equivOfInverse (L.prod P) inv h1 h2 with he
  have he_coe : (e : V →L[ℂ] ℂ × H) = L.prod P := rfl
  have he_symm : ∀ y, e.symm y = inv y := fun y => rfl
  -- the map `Φ` and its strict derivative at `z₀`
  set Φ : V → ℂ × H := fun z => (ℓ (f z), P (z - z₀)) with hΦ
  have hfs : HasStrictFDerivAt f A z₀ := hasStrictFDerivAt_of_differentiableOn hU hf hz₀
  have hΦs : HasStrictFDerivAt Φ (e : V →L[ℂ] ℂ × H) z₀ := by
    have h3 := (ℓ.hasStrictFDerivAt.comp z₀ hfs).prodMk
      (P.hasStrictFDerivAt.comp z₀ ((hasStrictFDerivAt_id z₀).sub_const z₀))
    rw [he_coe]
    convert h3 using 1
    · rfl
    · rw [ContinuousLinearMap.comp_id]
  have hΦd : DifferentiableOn ℂ Φ U :=
    (ℓ.differentiable.comp_differentiableOn hf).prodMk
      (P.differentiable.comp_differentiableOn (differentiableOn_id.sub_const z₀))
  -- the local inverse `Ψ`
  set Φh := hΦs.toOpenPartialHomeomorph Φ with hΦh
  have hΦh_coe : (Φh : V → ℂ × H) = Φ := hΦs.toOpenPartialHomeomorph_coe
  set Ψ := Φh.symm with hΨ
  have hz₀S : z₀ ∈ Φh.source := hΦs.mem_toOpenPartialHomeomorph_source
  have hΨ0 : HasFDerivAt Ψ (e.symm : ℂ × H →L[ℂ] V) (Φ z₀) := by
    have := hΦs.to_localInverse
    rw [HasStrictFDerivAt.localInverse_def] at this
    exact this.hasFDerivAt
  -- `Ψ` is holomorphic near `Φ z₀`
  set N : Set V := (U ∩ Φh.source) ∩
    (fun z => fderiv ℂ Φ z) ⁻¹' range ((↑) : (V ≃L[ℂ] ℂ × H) → V →L[ℂ] ℂ × H) with hN
  have hcontΦ : ContinuousOn (fun z => fderiv ℂ Φ z) U :=
    (hΦd.contDiffOn_of_isOpen hU 1).continuousOn_fderiv_of_isOpen hU le_rfl
  have hNo : IsOpen N :=
    (hcontΦ.mono inter_subset_left).isOpen_inter_preimage (hU.inter Φh.open_source)
      ContinuousLinearEquiv.isOpen
  have hz₀N : z₀ ∈ N := ⟨⟨hz₀, hz₀S⟩, ⟨e, hΦs.hasFDerivAt.fderiv.symm⟩⟩
  set T' := Φh.target ∩ Ψ ⁻¹' N with hT'
  have hT'o : IsOpen T' := Φh.isOpen_inter_preimage_symm hNo
  have hΨd : ∀ y ∈ T', DifferentiableAt ℂ Ψ y := by
    intro y hy
    obtain ⟨⟨hyU, -⟩, e', he'⟩ := hy.2
    have hd : HasFDerivAt Φ (e' : V →L[ℂ] ℂ × H) (Ψ y) := by
      rw [he']
      exact (hΦd.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    rw [← hΦh_coe] at hd
    exact (Φh.hasFDerivAt_symm hy.1 hd).differentiableAt
  have hΦΨ : ∀ y ∈ T', Φ (Ψ y) = y := fun y hy => by
    rw [← hΦh_coe]; exact Φh.right_inv hy.1
  have hΨΦ : Ψ (Φ z₀) = z₀ := by rw [← hΦh_coe]; exact Φh.left_inv hz₀S
  -- the slice through `z₀`
  set a₀ := ℓ (f z₀) with ha₀
  have hΦz₀ : Φ z₀ = (a₀, 0) := by simp [hΦ, ha₀]
  set O : Set H := {h | (a₀, h) ∈ T'} with hO
  have hOo : IsOpen O := hT'o.preimage (continuous_const.prodMk continuous_id)
  have h0O : (0 : H) ∈ O := by
    show (a₀, (0 : H)) ∈ T'
    rw [← hΦz₀]
    refine ⟨?_, ?_⟩
    · rw [← hΦh_coe]; exact Φh.map_source hz₀S
    · show Ψ (Φ z₀) ∈ N
      rw [hΨΦ]; exact hz₀N
  set G : H → H := fun h => eK (πK (f (Ψ (a₀, h)))) with hG
  have hGd : DifferentiableOn ℂ G O := by
    intro h hh
    have hU' : Ψ (a₀, h) ∈ U := hh.2.1.1
    have h3 : DifferentiableAt ℂ (fun h : H => Ψ (a₀, h)) h :=
      (hΨd _ hh).comp h ((differentiableAt_const a₀).prodMk differentiableAt_id)
    have h4 := (hf.differentiableAt (hU.mem_nhds hU')).comp h h3
    exact (eK.differentiableAt.comp h (πK.differentiableAt.comp h h4)).differentiableWithinAt
  have hGi : InjOn G O := by
    intro h₁ hh₁ h₂ hh₂ hG12
    have hℓ1 : ℓ (f (Ψ (a₀, h₁))) = a₀ := congrArg Prod.fst (hΦΨ _ hh₁)
    have hℓ2 : ℓ (f (Ψ (a₀, h₂))) = a₀ := congrArg Prod.fst (hΦΨ _ hh₂)
    have h3 : πK (f (Ψ (a₀, h₁))) = πK (f (Ψ (a₀, h₂))) := eK.injective hG12
    have h4 : f (Ψ (a₀, h₁)) = f (Ψ (a₀, h₂)) := by
      have h5 := congrArg (fun x : K => (x : V)) h3
      simp only [hπKx, hℓ1, hℓ2] at h5
      exact sub_left_injective h5
    have h6 := hinj hh₁.2.1.1 hh₂.2.1.1 h4
    have h7 : ((a₀, h₁) : ℂ × H) = (a₀, h₂) := by
      rw [← hΦΨ _ hh₁, ← hΦΨ _ hh₂, h6]
    exact (Prod.ext_iff.mp h7).2
  -- the induction hypothesis
  have hGinj := IH H hHrank G O hOo hGd hGi 0 h0O
  -- the derivative of `G` at `0`
  have hGder : HasFDerivAt G
      ((eK : K →L[ℂ] H).comp (πK.comp (A.comp ((e.symm : ℂ × H →L[ℂ] V).comp
        (ContinuousLinearMap.inr ℂ ℂ H))))) 0 := by
    have hsl : HasFDerivAt (fun h : H => ((a₀, h) : ℂ × H)) (ContinuousLinearMap.inr ℂ ℂ H) 0 :=
      (hasFDerivAt_const a₀ (0 : H)).prodMk (hasFDerivAt_id (0 : H))
    have hΨ1 : HasFDerivAt Ψ (e.symm : ℂ × H →L[ℂ] V) ((a₀, (0 : H)) : ℂ × H) := by
      rw [← hΦz₀]; exact hΨ0
    have hf1 : HasFDerivAt f A (Ψ ((a₀, (0 : H)) : ℂ × H)) := by
      rw [← hΦz₀, hΨΦ]; exact hfs.hasFDerivAt
    exact (eK : K →L[ℂ] H).hasFDerivAt.comp (0 : H) (πK.hasFDerivAt.comp (0 : H)
      (hf1.comp (0 : H) (hΨ1.comp (0 : H) hsl)))
  -- conclusion
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hLx : L x = 0 := by simp [hL, hx]
  have hxH : x ∈ H := hLx
  have hGx : fderiv ℂ G 0 ⟨x, hxH⟩ = 0 := by
    rw [hGder.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [he_symm, hinv_apply]
    simp [hx]
  have := hGinj (hGx.trans (map_zero _).symm)
  exact congrArg Subtype.val this

end LoewnerS0
