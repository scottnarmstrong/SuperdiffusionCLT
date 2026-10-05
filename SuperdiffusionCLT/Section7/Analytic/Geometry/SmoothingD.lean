/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.SmoothingC

/-!
# `W^{1,∞}` up to the boundary: local Lipschitz bounds on every piece `U ∩ B(x, r / C)`

* `exists_ball_lipschitz_representative`: on a ball inside `U` (convex `W^{1,∞}`).
* `exists_global_of_local`: Lipschitz representatives on every piece `U ∩ B(x, ρ)` glue to one
  function (two continuous functions that agree a.e. on an open set agree there).
* `exists_localLipschitz_representative` (E1): a uniformly `C^{1,1}` domain.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization Filter Topology

variable {d : ℕ}

theorem exists_ball_lipschitz_representative {U : Set (Vec d)} (g : H1Function U) {G : ℝ}
    (hG0 : 0 ≤ G) (hG : ∀ᵐ w ∂volume.restrict U, ∀ i, |g.grad w i| ≤ G) {x : Vec d} {ρ : ℝ}
    (hsub : Metric.ball x ρ ⊆ U) :
    ∃ ū : Vec d → ℝ, ū =ᵐ[volume.restrict (Metric.ball x ρ)] g.toFun ∧
      ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ, |ū y - ū z| ≤ d * G * ‖y - z‖ := by
  have hR : IsOpenBoundedConvexDomain (Metric.ball x ρ) :=
    ⟨Metric.isOpen_ball, Metric.isBounded_ball.isBoundedDomain, convex_ball _ _⟩
  have := exists_lipschitz_representative_of_convex hR (g.restrict Metric.isOpen_ball hsub) hG0
    (ae_restrict_of_ae_restrict_of_subset hsub hG)
  exact this

/-- Lipschitz representatives on every piece `U ∩ B(x, ρ)` glue to a single function. -/
theorem exists_global_of_local {U : Set (Vec d)} {ρ : ℝ} (hρ : 0 < ρ) {f : Vec d → ℝ}
    {K : NNReal}
    (h : ∀ x : Vec d, ∃ ū : Vec d → ℝ, ū =ᵐ[volume.restrict (U ∩ Metric.ball x ρ)] f ∧
      LipschitzOnWith K ū (U ∩ Metric.ball x ρ)) (hU : IsOpen U) :
    ∃ g' : Vec d → ℝ, g' =ᵐ[volume.restrict U] f ∧
      ∀ x, LipschitzOnWith K g' (U ∩ Metric.ball x ρ) := by
  choose ū hae hlip using h
  have hopen : ∀ x, IsOpen (U ∩ Metric.ball x ρ) := fun x => hU.inter Metric.isOpen_ball
  have hloc : ∀ x, ∀ y ∈ U ∩ Metric.ball x ρ, ū y y = ū x y := by
    intro x y hy
    have hyy : y ∈ U ∩ Metric.ball y ρ := ⟨hy.1, Metric.mem_ball_self hρ⟩
    set O : Set (Vec d) := (U ∩ Metric.ball y ρ) ∩ (U ∩ Metric.ball x ρ) with hO
    have hOo : IsOpen O := (hopen y).inter (hopen x)
    have h1 : ū y =ᵐ[volume.restrict O] f :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hae y)
    have h2 : ū x =ᵐ[volume.restrict O] f :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hae x)
    have h3 : ū y =ᵐ[volume.restrict O] ū x := h1.trans h2.symm
    have hc1 : ContinuousOn (ū y) O := (hlip y).continuousOn.mono Set.inter_subset_left
    have hc2 : ContinuousOn (ū x) O := (hlip x).continuousOn.mono Set.inter_subset_right
    exact Measure.eqOn_open_of_ae_eq h3 hOo hc1 hc2 ⟨hyy, hy⟩
  refine ⟨fun y => ū y y, ?_, fun x => ?_⟩
  · -- almost everywhere on `U`
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : Vec d => U ∩ Metric.ball x ρ) hopen
    have hUsub : U ⊆ ⋃ x ∈ T, U ∩ Metric.ball x ρ := by
      intro y hy
      have : y ∈ ⋃ x : Vec d, U ∩ Metric.ball x ρ :=
        Set.mem_iUnion.2 ⟨y, hy, Metric.mem_ball_self hρ⟩
      rwa [← hT] at this
    have hcov : ∀ x ∈ T, (fun y => ū y y) =ᵐ[volume.restrict (U ∩ Metric.ball x ρ)] f := by
      intro x _
      have hx : ∀ᵐ y ∂volume.restrict (U ∩ Metric.ball x ρ), ū x y = f y := hae x
      filter_upwards [hx, ae_restrict_mem (hopen x).measurableSet] with y hy hyP
      rw [hloc x y hyP, hy]
    have := (ae_restrict_biUnion_iff (fun x : Vec d => U ∩ Metric.ball x ρ) hTc
      (fun y => ū y y = f y)).2 hcov
    exact ae_restrict_of_ae_restrict_of_subset hUsub this
  · have : Set.EqOn (fun y => ū y y) (ū x) (U ∩ Metric.ball x ρ) := fun y hy => hloc x y hy
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have e1 : ū a a = ū x a := this ha
    have e2 : ū b b = ū x b := this hb
    rw [e1, e2]
    exact (hlip x).dist_le_mul a ha b hb


theorem lipschitzOnWith_of_abs_le {s : Set (Vec d)} {f : Vec d → ℝ} {K K' : ℝ} (hK0 : 0 ≤ K)
    (hK : K ≤ K') (h : ∀ y ∈ s, ∀ z ∈ s, |f y - f z| ≤ K * ‖y - z‖) :
    LipschitzOnWith (Real.toNNReal K') f s :=
  LipschitzOnWith.of_dist_le_mul fun y hy z hz => by
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (hK0.trans hK)]
    exact (h y hy z hz).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

/-- A ball not meeting the frontier of an open set lies inside it or misses it. -/
theorem ball_subset_or_disjoint {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} {ρ : ℝ}
    (h : ∀ x' ∈ frontier U, x' ∉ Metric.ball x ρ) :
    Metric.ball x ρ ⊆ U ∨ Disjoint (Metric.ball x ρ) U := by
  have hdis : Disjoint U (closure U)ᶜ := Set.disjoint_compl_right_iff_subset.2 subset_closure
  have hcov : Metric.ball x ρ ⊆ U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hc : y ∈ closure U
    · left
      by_contra hn
      refine h y ?_ hy
      rw [frontier, hU.interior_eq]
      exact ⟨hc, hn⟩
    · right; exact hc
  rcases (convex_ball x ρ).isPreconnected.subset_or_subset hU isClosed_closure.isOpen_compl hdis
    hcov with h1 | h1
  · exact Or.inl h1
  · right
    exact Set.disjoint_left.2 fun y hy hyU => h1 hy (subset_closure hyU)

/-- **E1.** `W^{1,∞}` up to the boundary: for a uniformly `C^{1,1}` domain `U` (slope bound `M₁`)
and `g ∈ H¹(U)` with `‖∇g‖ ∈ L^∞(U)`, there is a representative of `g` that is
`C ‖∇g‖_∞`-Lipschitz on every piece `U ∩ B(x, r / C)`, `C = C(d, M₁)`. -/
theorem exists_localLipschitz_representative (d : ℕ) (M₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Set (Vec d)} {r M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
      ∀ (g : H1Function U), eLpNorm (fun x => ‖g.grad x‖) ⊤ (volume.restrict U) < ⊤ →
      ∃ g' : Vec d → ℝ, g' =ᵐ[volume.restrict U] g.toFun ∧
        ∀ x : Vec d, LipschitzOnWith
          (Real.toNNReal (C * (eLpNorm (fun x => ‖g.grad x‖) ⊤ (volume.restrict U)).toReal))
          g' (U ∩ Metric.ball x (r / C)) := by
  set M : ℝ := max M₁ 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  set L : ℝ := 1 + (1 + d) * M with hL
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith only [hM, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  set A : ℝ := 1 + d * (1 + d) * M with hA
  have hA1 : 1 ≤ A := by
    rw [hA]
    have : (0 : ℝ) ≤ d * (1 + d) * M := by positivity
    linarith only [this]
  set C : ℝ := 2 * (d + 1) * A * L ^ 2 with hC
  have hd1 : (1 : ℝ) ≤ d + 1 := by linarith only [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hCpos : 0 < C := by rw [hC]; positivity
  have hC2 : 2 * L ^ 2 ≤ C := by
    rw [hC]
    have : 0 ≤ L ^ 2 := by positivity
    nlinarith only [hd1, hA1, this, mul_nonneg this (by linarith only [hd1] : (0:ℝ) ≤ d + 1)]
  refine ⟨C, hCpos, fun {U r M₂ D} hUC g hg => ?_⟩
  obtain ⟨hUo, hr, hD, hcharts⟩ := hUC
  set G : ℝ := (eLpNorm (fun x => ‖g.grad x‖) ⊤ (volume.restrict U)).toReal with hGdef
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hGn : ∀ᵐ w ∂volume.restrict U, ‖g.grad w‖ ≤ G := by
    have := enorm_ae_le_eLpNormEssSup (fun x => ‖g.grad x‖) (volume.restrict U)
    have hmeas : AEStronglyMeasurable (fun x => ‖g.grad x‖) (volume.restrict U) :=
      (aemeasurable_pi_iff.2 fun i => (g.gradMemL2 i).aestronglyMeasurable.aemeasurable).norm.aestronglyMeasurable
    rw [← eLpNorm_exponent_top hmeas] at this
    filter_upwards [this] with w hw
    exact (ENNReal.ofReal_le_iff_le_toReal hg.ne).1 (by rw [enorm_norm, ← ofReal_norm] at hw; exact hw)
  have hG : ∀ᵐ w ∂volume.restrict U, ∀ i, |g.grad w i| ≤ G := by
    filter_upwards [hGn] with w hw i
    have h1 : |g.grad w i| ≤ ‖g.grad w‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (g.grad w) i
    exact h1.trans hw
  have hdG : (d : ℝ) * G ≤ C * G := by
    refine mul_le_mul_of_nonneg_right ?_ hG0
    rw [hC]
    have h1 : (d : ℝ) ≤ 2 * (d + 1) := by linarith only [hd1]
    have h2 : (1 : ℝ) ≤ A * L ^ 2 := by nlinarith only [hA1, hL1]
    nlinarith only [h1, h2, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hchartG : (d : ℝ) * (A * G) * L ≤ C * G := by
    rw [hC]
    have h1 : (d : ℝ) ≤ 2 * (d + 1) := by linarith only [hd1]
    have h2 : L ≤ L ^ 2 := by nlinarith only [hL1]
    have h3 : (0 : ℝ) ≤ A * G := by positivity
    calc (d : ℝ) * (A * G) * L = (d * L) * (A * G) := by ring
      _ ≤ (2 * (d + 1) * L ^ 2) * (A * G) := by
          refine mul_le_mul_of_nonneg_right ?_ h3
          nlinarith only [h1, h2, hL1, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      _ = _ := by ring
  have hlocal : ∀ x : Vec d, ∃ ū : Vec d → ℝ,
      ū =ᵐ[volume.restrict (U ∩ Metric.ball x (r / C))] g.toFun ∧
      LipschitzOnWith (Real.toNNReal (C * G)) ū (U ∩ Metric.ball x (r / C)) := by
    intro x
    by_cases hfr : ∃ x' ∈ frontier U, x' ∈ Metric.ball x (r / C)
    · obtain ⟨x', hx'f, hx'b⟩ := hfr
      obtain ⟨e, ψ, he, hψ, hb1, _, hch⟩ := hcharts x' hx'f
      have hb : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M := fun y => (hb1 y).trans (le_max_left _ _)
      obtain ⟨ū, hae, hlip⟩ := exists_chart_lipschitz_representative hr he hψ hb hch g hG0 hG
      have hsub : U ∩ Metric.ball x (r / C) ⊆ U ∩ Metric.ball x' (r / L ^ 2) := by
        intro y hy
        refine ⟨hy.1, ?_⟩
        have hy2 := Metric.mem_ball.1 hy.2
        rw [Metric.mem_ball]
        have h1 := dist_triangle y x x'
        have h2 : dist x x' < r / C := by
          rw [Metric.mem_ball] at hx'b; rwa [dist_comm] at hx'b
        have h3 : r / C + r / C ≤ r / L ^ 2 := by
          have a1 : r / C ≤ r / (2 * L ^ 2) := div_le_div_of_nonneg_left hr.le (by positivity) hC2
          have a2 : r / (2 * L ^ 2) + r / (2 * L ^ 2) = r / L ^ 2 := by
            field_simp
            ring
          linarith only [a1, a2]
        linarith only [h1, hy2, h2, h3]
      refine ⟨ū, ae_restrict_of_ae_restrict_of_subset hsub hae, ?_⟩
      refine lipschitzOnWith_of_abs_le (by positivity) hchartG fun y hy z hz => ?_
      exact hlip y (hsub hy) z (hsub hz)
    · push Not at hfr
      rcases ball_subset_or_disjoint hUo hfr with hb | hb
      · obtain ⟨ū, hae, hlip⟩ := exists_ball_lipschitz_representative g hG0 hG hb
        have hinter : U ∩ Metric.ball x (r / C) = Metric.ball x (r / C) :=
          Set.inter_eq_right.2 hb
        rw [hinter]
        exact ⟨ū, hae, lipschitzOnWith_of_abs_le (by positivity) hdG hlip⟩
      · have hempty : U ∩ Metric.ball x (r / C) = ∅ := by
          rw [Set.inter_comm]; exact Set.disjoint_iff_inter_eq_empty.1 hb
        rw [hempty]
        exact ⟨g.toFun, by simp, by simp [LipschitzOnWith]⟩
  exact exists_global_of_local (by positivity) hlocal hUo

end SuperdiffusionCLT.Section7
