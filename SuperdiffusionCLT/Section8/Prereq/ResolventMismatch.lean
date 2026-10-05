/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.HeatWitness
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall

/-!
# Maximum principle and the `λ`-mismatch lemma for `λ - sΔ`

Classical (`C²` in the open set, continuous on its closure) solutions on a bounded open set of
`Vec d`.  The local second derivative test gives the weak maximum principle for
`lam w - s Δ w`; it yields the two-sided bound, and the comparison of two resolvent solutions
with different shifts `lam₁, lam₂` and diffusivities `s₁, s₂` and the same boundary values.

* `resMis_max_principle`, `resMis_abs_bound`: the maximum principle;
* `resMis_mismatch`, `resMis_mismatch_additive`: the `λ`-mismatch lemma
  (`‖v₁ - v₂‖ ≲ (|λ₁ - λ₂| + |s₁ - s₂|)`, explicit in `λ₁`, `s₂`, `‖f‖`, the boundary bound).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Filter Homogenization Topology SuperdiffusionCLT.Section8.Brownian

variable {d : ℕ}

/-- one-dim local second derivative test -/
theorem resMis_deriv_deriv_nonpos_of_isLocalMax {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ 0)
    (hmax : IsLocalMax φ 0) : deriv (deriv φ) 0 ≤ 0 := by
  have hd0 : deriv φ 0 = 0 := hmax.deriv_eq_zero
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ 2 φ t := hφ.eventually (by simp)
  have hev1 : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt φ (deriv φ t) t := by
    filter_upwards [hev] with t ht
    exact (ht.differentiableAt (by norm_num)).hasDerivAt
  have hdd : DifferentiableAt ℝ (deriv φ) 0 := by
    have h1 : ContDiffAt ℝ 1 (deriv φ) 0 := by
      have h2 : ContDiffAt ℝ 1 (fderiv ℝ φ) 0 := hφ.fderiv_right (m := 1) (by norm_num)
      have h3 : ContDiffAt ℝ 1 (fun t => fderiv ℝ φ t 1) 0 :=
        h2.clm_apply contDiffAt_const
      have h4 : deriv φ = fun t => fderiv ℝ φ t 1 := funext fun t => by
        rw [← fderiv_apply_one_eq_deriv]
      rw [h4]; exact h3
    exact h1.differentiableAt (by norm_num)
  by_contra hneg
  push Not at hneg
  set a := deriv (deriv φ) 0 with ha
  set ψ : ℝ → ℝ := fun t ↦ φ t - (a / 4) * t ^ 2 with hψ
  have hψ1 : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt ψ (deriv φ t - (a / 4) * (2 * t)) t := by
    filter_upwards [hev1] with t ht
    have := ht.sub (((hasDerivAt_pow 2 t).const_mul (a / 4)))
    have e2 : deriv φ t - a / 4 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = deriv φ t - a / 4 * (2 * t) := by
      norm_num
    rw [e2] at this
    exact this
  have hψ1' : deriv ψ =ᶠ[𝓝 0] fun t ↦ deriv φ t - (a / 4) * (2 * t) := by
    filter_upwards [hψ1] with t ht using ht.deriv
  have hψ2 : HasDerivAt (deriv ψ) (a - (a / 4) * 2) 0 := by
    have := hdd.hasDerivAt.sub (((hasDerivAt_id (0 : ℝ)).const_mul 2).const_mul (a / 4))
    have e2 : a - a / 4 * (2 * 1) = a - a / 4 * 2 := by norm_num
    rw [e2] at this
    refine this.congr_of_eventuallyEq ?_
    exact hψ1'
  have hψ0 : deriv ψ 0 = 0 := by
    rw [hψ1'.eq_of_nhds]; simp [hd0]
  have hmin : IsLocalMin ψ 0 := by
    refine isLocalMin_of_deriv_deriv_pos ?_ hψ0 ?_
    · rw [hψ2.deriv]; linarith only [hneg]
    · exact (hφ.differentiableAt (by norm_num)).continuousAt.sub (by fun_prop)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hmin
  obtain ⟨r', hr', hball'⟩ := Metric.eventually_nhds_iff.mp hmax
  have hm := lt_min hr hr'
  have hh : dist (min r r' / 2) 0 < r ∧ dist (min r r' / 2) 0 < r' := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith only [hm])]
    constructor <;> linarith only [min_le_left r r', min_le_right r r', hm]
  have hr2 := hball hh.1
  have hφle := hball' hh.2
  have : 0 < (a / 4) * (min r r' / 2) ^ 2 := by positivity
  simp only [hψ] at hr2
  linarith only [hr2, hφle, this]

theorem resMis_second_deriv_nonpos {f : Vec d → ℝ} {x : Vec d} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (e : Vec d) : fderiv ℝ (fderiv ℝ f) x e e ≤ 0 := by
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ x + s • e) e t := fun t ↦ by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  have hlc : ContDiffAt ℝ 2 (fun s : ℝ ↦ x + s • e) 0 := by fun_prop
  have h0 : (fun s : ℝ ↦ x + s • e) 0 = x := by simp
  set φ : ℝ → ℝ := fun t ↦ f (x + t • e) with hφ
  have hφc : ContDiffAt ℝ 2 φ 0 := by
    have hf' : ContDiffAt ℝ 2 f ((fun s : ℝ ↦ x + s • e) 0) := by rw [h0]; exact hf
    exact hf'.comp (0:ℝ) hlc
  have hφm : IsLocalMax φ 0 := by
    have hc : Continuous (fun s : ℝ ↦ x + s • e) := by fun_prop
    have : ∀ᶠ t in 𝓝 (0:ℝ), f (x + t • e) ≤ f x := by
      have h1 : ∀ᶠ y in 𝓝 x, f y ≤ f x := hmax
      have h2 : Tendsto (fun s : ℝ ↦ x + s • e) (𝓝 0) (𝓝 x) := by
        simpa using hc.tendsto 0
      exact h2.eventually h1
    filter_upwards [this] with t ht
    simpa [hφ] using ht
  have key := resMis_deriv_deriv_nonpos_of_isLocalMax hφc hφm
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev' : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ f (x + t • e) := by
    have h2 : Tendsto (fun s : ℝ ↦ x + s • e) (𝓝 0) (𝓝 x) := by
      simpa using (show Continuous (fun s : ℝ ↦ x + s • e) by fun_prop).tendsto 0
    filter_upwards [h2.eventually hev] with t ht using ht.differentiableAt (by norm_num)
  have h1' : deriv φ =ᶠ[𝓝 0] fun t ↦ fderiv ℝ f (x + t • e) e := by
    filter_upwards [hev'] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  have hdf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ f (x + t • e) e) (fderiv ℝ (fderiv ℝ f) x e e) 0 := by
    have hh : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) ((fun s : ℝ ↦ x + s • e) 0) := by
      rw [h0]; exact hdf'.hasFDerivAt
    have := hh.comp_hasDerivAt (0 : ℝ) (hline 0)
    have h3 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) this
    exact h3
  have h3 : deriv (deriv φ) 0 = fderiv ℝ (fderiv ℝ f) x e e := by
    rw [h1'.deriv_eq]
    exact h2.deriv
  rw [← h3]; exact key

theorem resMis_vecLaplacian_nonpos {f : Vec d → ℝ} {x : Vec d} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) : vecLaplacian f x ≤ 0 := by
  rw [vecLaplacian_eq_sum_fderiv]
  exact Finset.sum_nonpos fun i _ ↦ resMis_second_deriv_nonpos hf hmax _


theorem resMis_vecLaplacian_sub {f g : Vec d → ℝ} {x : Vec d} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    vecLaplacian (fun y ↦ f y - g y) x = vecLaplacian f x - vecLaplacian g x := by
  unfold vecLaplacian
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (fun y ↦ f y - g y) = f - g from rfl,
    iteratedFDeriv_sub_apply hf hg]
  rfl

/-- Weak maximum principle for `lam w - s Δ w` on a bounded open set. -/
theorem resMis_max_principle {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {w : Vec d → ℝ} (hc : ContinuousOn w (closure U)) (h2 : ∀ x ∈ U, ContDiffAt ℝ 2 w x)
    {lam s e m : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s)
    (hineq : ∀ x ∈ U, lam * w x - s * vecLaplacian w x ≤ e)
    (hfr : ∀ y ∈ frontier U, w y ≤ m) : ∀ x ∈ closure U, w x ≤ max m (e / lam) := by
  intro x hx
  obtain ⟨x₀, hx₀, hmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨x, hx⟩ hc
  have hxle : w x ≤ w x₀ := hmax hx
  by_cases hfx : x₀ ∈ frontier U
  · exact (hxle.trans (hfr x₀ hfx)).trans (le_max_left _ _)
  · have hxU : x₀ ∈ U := by
      by_contra hn
      refine hfx ?_
      rw [frontier, hU.interior_eq]
      exact ⟨hx₀, hn⟩
    have hloc : IsLocalMax w x₀ := by
      filter_upwards [hU.mem_nhds hxU] with y hy using hmax (subset_closure hy)
    have hlap := resMis_vecLaplacian_nonpos (h2 x₀ hxU) hloc
    have h1 := hineq x₀ hxU
    have h3 : lam * w x₀ ≤ e := by
      have := mul_nonneg hs (neg_nonneg.mpr hlap)
      linarith only [h1, this]
    have h4 : w x₀ ≤ e / lam := by rw [le_div_iff₀ hlam]; linarith only [h3]
    exact (hxle.trans h4).trans (le_max_right _ _)


/-- Two-sided bound from the maximum principle. -/
theorem resMis_abs_bound {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {w : Vec d → ℝ} (hc : ContinuousOn w (closure U)) (h2 : ∀ x ∈ U, ContDiffAt ℝ 2 w x)
    {lam s e m : ℝ} (hlam : 0 < lam) (hs : 0 ≤ s)
    (hineq : ∀ x ∈ U, |lam * w x - s * vecLaplacian w x| ≤ e)
    (hfr : ∀ y ∈ frontier U, |w y| ≤ m) : ∀ x ∈ closure U, |w x| ≤ max m (e / lam) := by
  intro x hx
  have hup := resMis_max_principle hU hb hc h2 hlam hs (e := e) (m := m)
    (fun y hy ↦ (le_abs_self _).trans (hineq y hy)) (fun y hy ↦ (le_abs_self _).trans (hfr y hy)) x hx
  have hdn := resMis_max_principle hU hb (w := fun y ↦ -w y) hc.neg (fun y hy ↦ (h2 y hy).neg)
    hlam hs (e := e) (m := m)
    (fun y hy ↦ by
      have := (neg_le_abs _).trans (hineq y hy)
      rw [heatWitness_vecLaplacian_neg]
      linarith only [this])
    (fun y hy ↦ (neg_le_abs _).trans (hfr y hy)) x hx
  rw [abs_le]
  constructor
  · linarith only [hdn]
  · exact hup

/-- **The `λ`-mismatch lemma.**  Two classical solutions on a bounded open set with the same
boundary values, right-hand side `f` bounded by `F`, shifts `lam₁, lam₂` and diffusivities
`s₁, s₂`.  If `|v₂| ≤ G` on the frontier then on the closure
`|v₁ - v₂| ≤ (|lam₂ s₁/s₂ - lam₁| max(G, F/lam₂) + |1 - s₁/s₂| F)/lam₁`. -/
theorem resMis_mismatch {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {v₁ v₂ f : Vec d → ℝ} (hc₁ : ContinuousOn v₁ (closure U)) (hc₂ : ContinuousOn v₂ (closure U))
    (h₁ : ∀ x ∈ U, ContDiffAt ℝ 2 v₁ x) (h₂ : ∀ x ∈ U, ContDiffAt ℝ 2 v₂ x)
    {lam₁ lam₂ s₁ s₂ F G : ℝ} (hF : 0 ≤ F) (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂) (hs₁ : 0 ≤ s₁) (hs₂ : 0 < s₂)
    (hf : ∀ x ∈ U, |f x| ≤ F)
    (e₁ : ∀ x ∈ U, lam₁ * v₁ x - s₁ * vecLaplacian v₁ x = f x)
    (e₂ : ∀ x ∈ U, lam₂ * v₂ x - s₂ * vecLaplacian v₂ x = f x)
    (hfr : ∀ y ∈ frontier U, v₁ y = v₂ y) (hG : ∀ y ∈ frontier U, |v₂ y| ≤ G) :
    ∀ x ∈ closure U, |v₁ x - v₂ x| ≤
      (|lam₂ * s₁ / s₂ - lam₁| * max G (F / lam₂) + |1 - s₁ / s₂| * F) / lam₁ := by
  have hV := resMis_abs_bound hU hb hc₂ h₂ hl₂ hs₂.le (e := F) (m := G)
    (fun y hy ↦ by rw [e₂ y hy]; exact hf y hy) hG
  have hDlap : ∀ x ∈ U, vecLaplacian v₂ x = (lam₂ * v₂ x - f x) / s₂ := by
    intro x hx
    have := e₂ x hx
    field_simp
    linarith only [this]
  have hbd : ∀ x ∈ U, |lam₁ * (v₁ x - v₂ x) - s₁ * vecLaplacian (fun y ↦ v₁ y - v₂ y) x| ≤
      |lam₂ * s₁ / s₂ - lam₁| * max G (F / lam₂) + |1 - s₁ / s₂| * F := by
    intro x hx
    rw [resMis_vecLaplacian_sub (h₁ x hx) (h₂ x hx)]
    have hlap := hDlap x hx
    have e1 := e₁ x hx
    have hid : lam₁ * (v₁ x - v₂ x) - s₁ * (vecLaplacian v₁ x - vecLaplacian v₂ x) =
        (lam₂ * s₁ / s₂ - lam₁) * v₂ x + (1 - s₁ / s₂) * f x := by
      rw [hlap]
      have : lam₁ * (v₁ x - v₂ x) - s₁ * (vecLaplacian v₁ x - (lam₂ * v₂ x - f x) / s₂) =
          (lam₁ * v₁ x - s₁ * vecLaplacian v₁ x) - lam₁ * v₂ x + s₁ * (lam₂ * v₂ x - f x) / s₂ := by
        ring
      rw [this, e1]
      field_simp
      ring
    rw [hid]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hV x (subset_closure hx)) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf x hx) (abs_nonneg _)
  have := resMis_abs_bound hU hb (hc₁.sub hc₂) (fun x hx ↦ (h₁ x hx).sub (h₂ x hx)) hl₁ hs₁
    (e := |lam₂ * s₁ / s₂ - lam₁| * max G (F / lam₂) + |1 - s₁ / s₂| * F) (m := 0) hbd
    (fun y hy ↦ by simp [hfr y hy])
  intro x hx
  have h := this x hx
  rw [max_eq_right (by
    have hn : 0 ≤ |lam₂ * s₁ / s₂ - lam₁| * max G (F / lam₂) + |1 - s₁ / s₂| * F := by
      have hm : 0 ≤ max G (F / lam₂) := (div_nonneg hF hl₂.le).trans (le_max_right _ _)
      exact add_nonneg (mul_nonneg (abs_nonneg _) hm) (mul_nonneg (abs_nonneg _) hF)
    exact div_nonneg hn hl₁.le)] at h
  exact h


theorem resMis_isBounded_euclidBall {r : ℝ} (hr : 0 < r) :
    Bornology.IsBounded (SuperdiffusionCLT.Section6.euclidBall (d := d) r) :=
  Metric.isBounded_ball.subset (SuperdiffusionCLT.Section6.euclidBall_subset_ball hr)

theorem resMis_vecLaplacian_const (c : ℝ) (x : Vec d) : vecLaplacian (fun _ : Vec d ↦ c) x = 0 := by
  rw [vecLaplacian_eq_sum_fderiv]
  simp

/-- The mismatch bound in the additive form `|lam₁ - lam₂| + |s₁ - s₂|`. -/
theorem resMis_mismatch_additive {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {v₁ v₂ f : Vec d → ℝ} (hc₁ : ContinuousOn v₁ (closure U)) (hc₂ : ContinuousOn v₂ (closure U))
    (h₁ : ∀ x ∈ U, ContDiffAt ℝ 2 v₁ x) (h₂ : ∀ x ∈ U, ContDiffAt ℝ 2 v₂ x)
    {lam₁ lam₂ s₁ s₂ F G : ℝ} (hF : 0 ≤ F) (hl₁ : 0 < lam₁) (hl₂ : 0 < lam₂) (hs₁ : 0 ≤ s₁)
    (hs₂ : 0 < s₂) (hf : ∀ x ∈ U, |f x| ≤ F)
    (e₁ : ∀ x ∈ U, lam₁ * v₁ x - s₁ * vecLaplacian v₁ x = f x)
    (e₂ : ∀ x ∈ U, lam₂ * v₂ x - s₂ * vecLaplacian v₂ x = f x)
    (hfr : ∀ y ∈ frontier U, v₁ y = v₂ y) (hG : ∀ y ∈ frontier U, |v₂ y| ≤ G) :
    ∀ x ∈ closure U, |v₁ x - v₂ x| ≤
      (|lam₂ - lam₁| * max G (F / lam₂) +
        |s₁ - s₂| / s₂ * (lam₂ * max G (F / lam₂) + F)) / lam₁ := by
  intro x hx
  refine (resMis_mismatch hU hb hc₁ hc₂ h₁ h₂ hF hl₁ hl₂ hs₁ hs₂ hf e₁ e₂ hfr hG x hx).trans ?_
  refine div_le_div_of_nonneg_right ?_ hl₁.le
  have hm : 0 ≤ max G (F / lam₂) := (div_nonneg hF hl₂.le).trans (le_max_right _ _)
  have h1 : |lam₂ * s₁ / s₂ - lam₁| ≤ |lam₂ - lam₁| + lam₂ * (|s₁ - s₂| / s₂) := by
    have : lam₂ * s₁ / s₂ - lam₁ = (lam₂ - lam₁) + lam₂ * ((s₁ - s₂) / s₂) := by
      field_simp; ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
    rw [abs_mul, abs_div, abs_of_pos hl₂, abs_of_pos hs₂]
  have h2 : |1 - s₁ / s₂| = |s₁ - s₂| / s₂ := by
    have : 1 - s₁ / s₂ = -((s₁ - s₂) / s₂) := by field_simp; ring
    rw [this, abs_neg, abs_div, abs_of_pos hs₂]
  rw [h2]
  have := mul_le_mul_of_nonneg_right h1 hm
  linarith only [this]

/-- Witness: two constant solutions of `1 · v - 0 = 1` on the unit ball. -/
example : ∀ x ∈ closure (SuperdiffusionCLT.Section6.euclidBall (d := 2) 1),
    |(fun _ : Vec 2 ↦ (1:ℝ)) x - (fun _ : Vec 2 ↦ (1:ℝ)) x| ≤
      (|(1:ℝ) - 1| * max 1 (1 / 1) + |(1:ℝ) - 1| / 1 * (1 * max 1 (1 / 1) + 1)) / 1 :=
  resMis_mismatch_additive (SuperdiffusionCLT.Section6.isOpen_euclidBall 1)
    (resMis_isBounded_euclidBall one_pos) continuousOn_const continuousOn_const
    (fun _ _ ↦ contDiffAt_const) (fun _ _ ↦ contDiffAt_const) (F := 1) (G := 1) zero_le_one
    one_pos one_pos zero_le_one one_pos (f := fun _ ↦ 1) (fun _ _ ↦ by simp)
    (fun x _ ↦ by rw [resMis_vecLaplacian_const]; simp)
    (fun x _ ↦ by rw [resMis_vecLaplacian_const]; simp)
    (fun _ _ ↦ rfl) (fun _ _ ↦ by simp)

end SuperdiffusionCLT.Section8
