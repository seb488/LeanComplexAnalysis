import LoewnerS0.Flow

/-!
# Holomorphy of the flow

For `h ∈ M(𝔹)` and `t ≥ 0`, the time-`t` map `z ↦ φ_t(z)` of the flow of `ż = -h(z)` is
holomorphic on `𝔹`.

Proof: the Euler polygons `(id - (t/N) h)^[N]` are compositions of holomorphic maps, hence
holomorphic, and they converge to `φ_t` uniformly on every ball `ball 0 ρ`, `ρ < 1`
(the classical error estimate `O(1/N)` for Euler's method, with a discrete Gronwall argument that
also keeps the polygons inside a slightly larger ball). Weierstrass' theorem
(`SCV.differentiableOn_of_tendstoUniformlyOn`) concludes.
-/

open Complex Metric Set Filter
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace LoewnerS0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {h : E → E}

/-- One step of Euler's method with step `Δ` for `ż = -h(z)`. -/
def eulerStep (h : E → E) (Δ : ℝ) (w : E) : E := w - (Δ : ℂ) • h w

omit [FiniteDimensional ℂ E] in
lemma eulerStep_sub_le {L : ℝ≥0} {S : Set E} (hL : LipschitzOnWith L h S) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) :
    ‖eulerStep h Δ a - eulerStep h Δ b‖ ≤ (1 + L * Δ) * ‖a - b‖ := by
  have e : eulerStep h Δ a - eulerStep h Δ b = (a - b) - (Δ : ℂ) • (h a - h b) := by
    simp only [eulerStep, smul_sub]; abel
  have h1 : ‖h a - h b‖ ≤ L * ‖a - b‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]; exact hL.dist_le_mul a ha b hb
  rw [e]
  calc ‖(a - b) - (Δ : ℂ) • (h a - h b)‖ ≤ ‖a - b‖ + ‖(Δ : ℂ) • (h a - h b)‖ := norm_sub_le _ _
    _ = ‖a - b‖ + Δ * ‖h a - h b‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
    _ ≤ ‖a - b‖ + Δ * (L * ‖a - b‖) := by gcongr
    _ = (1 + L * Δ) * ‖a - b‖ := by ring

variable (hh : IsCaratheodory h)

/-- The local truncation error of Euler's method. -/
lemma norm_flow_sub_eulerStep_le {ρ' : ℝ} (hρ'1 : ρ' < 1) {L : ℝ≥0} {M : ℝ}
    (hL : LipschitzOnWith L h (closedBall 0 ρ')) (hM : ∀ w ∈ closedBall (0 : E) ρ', ‖h w‖ ≤ M)
    {y : E} (hy : ‖y‖ ≤ ρ') {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ‖flow hh Δ y - eulerStep h Δ y‖ ≤ L * M * Δ ^ 2 := by
  have hyB : y ∈ unitBall E := mem_unitBall.mpr (lt_of_le_of_lt hy hρ'1)
  have hmem : ∀ τ, 0 ≤ τ → flow hh τ y ∈ closedBall (0 : E) ρ' := fun τ hτ =>
    mem_closedBall_zero_iff.mpr ((norm_flow_le hh hyB hτ).trans hy)
  have hcont : ContinuousOn (fun τ => flow hh τ y) (Icc 0 Δ) :=
    (continuousOn_flow hh hyB).mono Icc_subset_Ici_self
  -- `‖φ_τ(y) - y‖ ≤ M τ`
  have hstep1 : ∀ τ ∈ Icc 0 Δ, ‖flow hh τ y - y‖ ≤ M * τ := by
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun τ => flow hh τ y)
      (f' := fun τ => -h (flow hh τ y)) (C := M) hcont
      (fun τ hτ => hasDerivWithinAt_flow hh hyB hτ.1)
      (fun τ hτ => by rw [norm_neg]; exact hM _ (hmem τ hτ.1))
    intro τ hτ
    simpa [flow_zero hh hyB] using this τ hτ
  -- the remainder `g(τ) = φ_τ(y) - y + τ h(y)`
  have hg : ∀ τ ∈ Ico 0 Δ, HasDerivWithinAt (fun τ => flow hh τ y - y + τ • h y)
      (-h (flow hh τ y) + h y) (Ici τ) τ := by
    intro τ hτ
    have h1 := (hasDerivWithinAt_flow hh hyB hτ.1).sub_const y
    have h2 := ((hasDerivAt_id τ).smul_const (h y)).hasDerivWithinAt (s := Ici τ)
    have h3 := h1.fun_add h2
    simpa using h3
  have hgcont : ContinuousOn (fun τ => flow hh τ y - y + τ • h y) (Icc 0 Δ) :=
    (hcont.sub continuousOn_const).add (continuousOn_id.smul continuousOn_const)
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment hgcont hg
    (C := L * M * Δ) (fun τ hτ => by
      have h1 : ‖h (flow hh τ y) - h y‖ ≤ L * ‖flow hh τ y - y‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact hL.dist_le_mul _ (hmem τ hτ.1) _ (mem_closedBall_zero_iff.mpr hy)
      have h2 := hstep1 τ (Ico_subset_Icc_self hτ)
      have hL0 : (0 : ℝ) ≤ L := L.2
      calc ‖-h (flow hh τ y) + h y‖ = ‖h (flow hh τ y) - h y‖ := by
            rw [← norm_neg]; congr 1; abel
        _ ≤ L * ‖flow hh τ y - y‖ := h1
        _ ≤ L * (M * τ) := mul_le_mul_of_nonneg_left h2 hL0
        _ ≤ L * M * Δ := by
            rw [← mul_assoc]
            have hLM : 0 ≤ (L : ℝ) * M := mul_nonneg hL0 ((norm_nonneg _).trans (hM y
              (mem_closedBall_zero_iff.mpr hy)))
            exact mul_le_mul_of_nonneg_left hτ.2.le hLM) Δ (right_mem_Icc.mpr hΔ)
  have e : flow hh Δ y - eulerStep h Δ y =
      (flow hh Δ y - y + Δ • h y) - (flow hh 0 y - y + (0 : ℝ) • h y) := by
    rw [flow_zero hh hyB, eulerStep, zero_smul, Complex.coe_smul]; abel
  rw [e]
  calc _ ≤ L * M * Δ * (Δ - 0) := key
    _ = L * M * Δ ^ 2 := by ring

/-- **Global error estimate for Euler's method** (with a discrete Gronwall argument). -/
lemma norm_euler_sub_flow_le {ρ ρ' : ℝ} (hρρ' : ρ ≤ ρ') (hρ'1 : ρ' < 1) {L : ℝ≥0} {M : ℝ}
    (hL : LipschitzOnWith L h (closedBall 0 ρ')) (hM : ∀ w ∈ closedBall (0 : E) ρ', ‖h w‖ ≤ M)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) {N : ℕ}
    (hsmall : (Real.exp (L * (N * Δ)) - 1) * M * Δ ≤ ρ' - ρ) {z : E} (hz : ‖z‖ ≤ ρ) :
    ∀ k ≤ N, ‖(eulerStep h Δ)^[k] z - flow hh (k * Δ) z‖ ≤ ((1 + L * Δ) ^ k - 1) * M * Δ := by
  have hzB : z ∈ unitBall E := mem_unitBall.mpr (by linarith [hz])
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self (by
    linarith [norm_nonneg z])))
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hpow : ∀ k ≤ N, (1 + L * Δ) ^ k ≤ Real.exp (L * (N * Δ)) := by
    intro k hk
    calc (1 + L * Δ) ^ k ≤ Real.exp (L * Δ) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((L : ℝ) * Δ)]) k
      _ = Real.exp (k * (L * Δ)) := (Real.exp_nat_mul _ k).symm
      _ ≤ Real.exp (L * (N * Δ)) := by
          apply Real.exp_le_exp.mpr
          have : (k : ℝ) ≤ N := by exact_mod_cast hk
          nlinarith [mul_nonneg (sub_nonneg.mpr this) (mul_nonneg hL0 hΔ)]
  intro k
  induction k with
  | zero => intro _; simp [flow_zero hh hzB]
  | succ k ih =>
    intro hk
    have hk' : k ≤ N := Nat.le_of_succ_le hk
    have IH := ih hk'
    set ψ := (eulerStep h Δ)^[k] z with hψ
    set x := flow hh (k * Δ) z with hx
    have hkΔ : 0 ≤ (k : ℝ) * Δ := mul_nonneg k.cast_nonneg hΔ
    have hxn : ‖x‖ ≤ ρ := (norm_flow_le hh hzB hkΔ).trans hz
    have hψn : ‖ψ‖ ≤ ρ' := by
      have h1 : ‖ψ‖ ≤ ‖x‖ + ‖ψ - x‖ := by
        calc ‖ψ‖ = ‖x + (ψ - x)‖ := by rw [add_sub_cancel]
          _ ≤ ‖x‖ + ‖ψ - x‖ := norm_add_le _ _
      have h2 : ((1 + L * Δ) ^ k - 1) * M * Δ ≤ (Real.exp (L * (N * Δ)) - 1) * M * Δ := by
        have := hpow k hk'
        have hMΔ : 0 ≤ M * Δ := mul_nonneg hM0 hΔ
        nlinarith
      linarith
    have hxk : flow hh ((k + 1 : ℕ) * Δ) z = flow hh Δ x := by
      rw [hx, ← flow_add hh hzB hkΔ hΔ]; push_cast; ring_nf
    rw [Function.iterate_succ_apply', hxk]
    have hS := eulerStep_sub_le hL hΔ (mem_closedBall_zero_iff.mpr hψn)
      (mem_closedBall_zero_iff.mpr (hxn.trans hρρ'))
    have hT := norm_flow_sub_eulerStep_le hh hρ'1 hL hM (hxn.trans hρρ') hΔ
    calc ‖eulerStep h Δ ψ - flow hh Δ x‖
        ≤ ‖eulerStep h Δ ψ - eulerStep h Δ x‖ + ‖flow hh Δ x - eulerStep h Δ x‖ := by
          rw [← norm_neg (flow hh Δ x - eulerStep h Δ x)]
          convert norm_add_le (eulerStep h Δ ψ - eulerStep h Δ x)
            (-(flow hh Δ x - eulerStep h Δ x)) using 2
          abel
      _ ≤ (1 + L * Δ) * ‖ψ - x‖ + L * M * Δ ^ 2 := add_le_add hS hT
      _ ≤ (1 + L * Δ) * (((1 + L * Δ) ^ k - 1) * M * Δ) + L * M * Δ ^ 2 := by
          gcongr
      _ = ((1 + L * Δ) ^ (k + 1) - 1) * M * Δ := by ring

omit [FiniteDimensional ℂ E] in
include hh in
/-- The Euler polygons are holomorphic where they stay in `𝔹`. -/
lemma differentiableAt_euler {Δ : ℝ} {z : E} :
    ∀ k : ℕ, (∀ j < k, (eulerStep h Δ)^[j] z ∈ unitBall E) →
      DifferentiableAt ℂ ((eulerStep h Δ)^[k]) z := by
  intro k
  induction k with
  | zero => intro _; exact differentiableAt_id
  | succ k ih =>
    intro hmem
    have h1 := ih (fun j hj => hmem j (Nat.lt_succ_of_lt hj))
    have h2 : DifferentiableAt ℂ (eulerStep h Δ) ((eulerStep h Δ)^[k] z) := by
      have hd := hh.isNormalized.differentiableAt (hmem k (Nat.lt_succ_self k))
      exact differentiableAt_id.sub (hd.const_smul (Δ : ℂ))
    rw [Function.iterate_succ']
    exact h2.comp z h1

/-- **The flow is holomorphic**: `z ↦ φ_t(z)` is holomorphic on `𝔹` for every `t ≥ 0`. -/
theorem differentiableOn_flow {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (fun z => flow hh t z) (unitBall E) := by
  intro z₀ hz₀
  set ρ := (1 + ‖z₀‖) / 2 with hρ_def
  have hz₀1 : ‖z₀‖ < 1 := mem_unitBall.mp hz₀
  have hρ1 : ρ < 1 := by linarith
  have hz₀ρ : ‖z₀‖ < ρ := by linarith
  set ρ' := (1 + ρ) / 2 with hρ'_def
  have hρρ' : ρ < ρ' := by linarith
  have hρ'1 : ρ' < 1 := by linarith
  obtain ⟨L, hL⟩ := hh.exists_lipschitzOnWith hρ'1
  obtain ⟨M, hM0, hM⟩ := hh.exists_norm_le hρ'1
  set A := (Real.exp (L * t) - 1) * M * t with hA_def
  have hA0 : 0 ≤ A := by
    have : 0 ≤ Real.exp (L * t) - 1 := by
      have := Real.add_one_le_exp ((L : ℝ) * t)
      have : 0 ≤ (L : ℝ) * t := mul_nonneg L.2 ht
      linarith
    positivity
  -- the number of steps
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (A / (ρ' - ρ))
  set G : ℕ → E → E := fun n => (eulerStep h (t / (n + N₀ + 1 : ℕ)))^[n + N₀ + 1] with hG_def
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n + N₀ + 1 : ℕ) := fun n => by positivity
  -- the error estimate for `G n`
  have herr : ∀ n : ℕ, ∀ z : E, ‖z‖ ≤ ρ → ∀ k ≤ n + N₀ + 1,
      ‖(eulerStep h (t / (n + N₀ + 1 : ℕ)))^[k] z - flow hh (k * (t / (n + N₀ + 1 : ℕ))) z‖ ≤
        A / (n + N₀ + 1 : ℕ) := by
    intro n z hz k hk
    set N := n + N₀ + 1 with hN
    set Δ := t / (N : ℝ) with hΔ
    have hΔ0 : 0 ≤ Δ := div_nonneg ht (hNpos n).le
    have hN0 : (N : ℝ) ≠ 0 := (hNpos n).ne'
    have hNΔ : (N : ℝ) * Δ = t := by rw [hΔ]; field_simp
    have hsmall : (Real.exp (L * (N * Δ)) - 1) * M * Δ ≤ ρ' - ρ := by
      rw [hNΔ]
      have h1 : (Real.exp (L * t) - 1) * M * Δ = A / N := by rw [hA_def, hΔ]; ring
      rw [h1, div_le_iff₀ (hNpos n)]
      have h2 : A / (ρ' - ρ) < N := by
        rw [hN]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [div_lt_iff₀ (by linarith)] at h2
      linarith
    have key := norm_euler_sub_flow_le hh hρρ'.le hρ'1 hL hM hΔ0 hsmall hz k hk
    calc _ ≤ ((1 + L * Δ) ^ k - 1) * M * Δ := key
      _ ≤ (Real.exp (L * t) - 1) * M * Δ := by
          have hpow : (1 + L * Δ) ^ k ≤ Real.exp (L * t) := by
            calc (1 + L * Δ) ^ k ≤ Real.exp (L * Δ) ^ k :=
                  pow_le_pow_left₀ (by have := mul_nonneg (NNReal.coe_nonneg L) hΔ0; positivity)
                    (by linarith [Real.add_one_le_exp ((L : ℝ) * Δ)]) k
              _ = Real.exp (k * (L * Δ)) := (Real.exp_nat_mul _ k).symm
              _ ≤ Real.exp (L * t) := by
                  apply Real.exp_le_exp.mpr
                  have : (k : ℝ) ≤ N := by exact_mod_cast hk
                  rw [← hNΔ]
                  nlinarith [mul_nonneg (sub_nonneg.mpr this) (mul_nonneg (NNReal.coe_nonneg L) hΔ0)]
          have hMΔ : 0 ≤ M * Δ := mul_nonneg hM0 hΔ0
          nlinarith
      _ = A / N := by rw [hA_def, hΔ]; ring
  -- `G n` stays in `closedBall 0 ρ'` and is holomorphic on `ball 0 ρ`
  have hGd : ∀ n, DifferentiableOn ℂ (G n) (ball 0 ρ) := by
    intro n z hz
    have hzρ : ‖z‖ ≤ ρ := (mem_ball_zero_iff.mp hz).le
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_euler hh
    intro j hj
    have h1 := herr n z hzρ j hj.le
    have h2 : ‖flow hh (j * (t / (n + N₀ + 1 : ℕ))) z‖ ≤ ρ :=
      (norm_flow_le hh (mem_unitBall.mpr (by linarith)) (by positivity)).trans hzρ
    have h3 : A / (n + N₀ + 1 : ℕ) ≤ ρ' - ρ := by
      rw [div_le_iff₀ (hNpos n)]
      have h4 : A / (ρ' - ρ) < (n + N₀ + 1 : ℕ) := by
        push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [div_lt_iff₀ (by linarith)] at h4
      linarith
    apply mem_unitBall.mpr
    calc ‖(eulerStep h (t / (n + N₀ + 1 : ℕ)))^[j] z‖
        ≤ ‖flow hh (j * (t / (n + N₀ + 1 : ℕ))) z‖ +
          ‖(eulerStep h (t / (n + N₀ + 1 : ℕ)))^[j] z - flow hh (j * (t / (n + N₀ + 1 : ℕ))) z‖ := by
          rw [← norm_neg ((eulerStep h (t / (n + N₀ + 1 : ℕ)))^[j] z -
            flow hh (j * (t / (n + N₀ + 1 : ℕ))) z)]
          convert norm_add_le (flow hh (j * (t / (n + N₀ + 1 : ℕ))) z)
            ((eulerStep h (t / (n + N₀ + 1 : ℕ)))^[j] z -
              flow hh (j * (t / (n + N₀ + 1 : ℕ))) z) using 2
          · abel
          · rw [norm_neg]
      _ ≤ ρ + (ρ' - ρ) := add_le_add h2 (h1.trans h3)
      _ < 1 := by linarith
  -- uniform convergence
  have hconv : TendstoUniformlyOn G (fun z => flow hh t z) atTop (ball 0 ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (A / ε)
    refine eventually_atTop.mpr ⟨n₀, fun n hn z hz => ?_⟩
    have hzρ : ‖z‖ ≤ ρ := (mem_ball_zero_iff.mp hz).le
    have h1 := herr n z hzρ (n + N₀ + 1) le_rfl
    have hNt : ((n + N₀ + 1 : ℕ) : ℝ) * (t / (n + N₀ + 1 : ℕ)) = t := by
      field_simp
    rw [hNt] at h1
    rw [dist_comm, dist_eq_norm]
    refine lt_of_le_of_lt h1 ?_
    rw [div_lt_iff₀ (hNpos n)]
    rw [div_lt_iff₀ hε] at hn₀
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) ≤ (n + N₀ + 1 : ℕ) := by push_cast; linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
    nlinarith
  have hd := SCV.differentiableOn_of_tendstoUniformlyOn isOpen_ball hGd hconv
  exact (hd z₀ (mem_ball_zero_iff.mpr hz₀ρ)).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz₀ρ)) |>.differentiableWithinAt

end LoewnerS0
