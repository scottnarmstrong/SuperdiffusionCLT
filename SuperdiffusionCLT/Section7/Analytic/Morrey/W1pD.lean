/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Morrey.W1pC

@[expose] public section

open MeasureTheory Homogenization Filter Topology

/-!
# Morrey's inequality for `W^{1,p}` on an axis cube

For `p > d ≥ 1` and `u ∈ W^{1,p}(Q)` on an axis cube `Q` of side `L`, `u` has a continuous
representative, every continuous representative `ū` satisfies
`|ū x - ū y| ≤ C(d,p) ‖x - y‖^{1-d/p} ‖∇u‖_{L^p(Q)}`, and
`|ū x - ⨍_Q u| ≤ C(d,p) L^{1-d/p} ‖∇u‖_{L^p(Q)}`, with `C(d,p) = 4 d / (1 - d/p)`.  The proof
passes to the limit in the uniform Hölder bound for the smooth representatives of the convex
smoothing along a subsequence converging almost everywhere.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Morrey's inequality for `W^{1,p}` on an axis cube**: a continuous representative exists and
satisfies the Hölder bound. -/
theorem w1p_exists_continuous_representative (hd0 : 0 < d) {z : Vec d} {L : ℝ} (hL : 0 < L)
    {p : ℝ} (hp : (d : ℝ) < p) (u : W1pFunction (axisCube z L) (ENNReal.ofReal p)) :
    ∃ ū : Vec d → ℝ, ContinuousOn ū (axisCube z L) ∧
      ū =ᵐ[volume.restrict (axisCube z L)] u.toFun ∧
      ∀ x ∈ axisCube z L, ∀ y ∈ axisCube z L,
        |ū x - ū y| ≤ 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p)
            (volume.restrict (axisCube z L))).toReal := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hp1 : 1 < p := by linarith only [hd1, hp]
  have hp0 : 0 < p := by linarith only [hp1]
  have hdp : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hp
  have hα : 0 < 1 - (d : ℝ) / p := by linarith only [hdp]
  have hU := isOpenBoundedConvexDomain_axisCube z L
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hp1' : 1 ≤ ENNReal.ofReal p := by simpa using (ENNReal.ofReal_le_ofReal hp1.le)
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hball := closedBall_subset_axisCube (z := z) hL
  have hr : (0 : ℝ) < L / 4 := by positivity
  set x0 : Vec d := fun j => z j + L / 2 with hx0
  set ε : ℕ → ℝ := fun n => unitConvexApproxScale (n + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => by
    simp only [hεdef, unitConvexApproxScale]; positivity
  have hε1 : ∀ n, ε n < 1 := fun n => by
    simp only [hεdef, unitConvexApproxScale]
    rw [div_lt_one (by positivity)]
    push_cast
    linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hεt : Tendsto ε atTop (𝓝 0) :=
    tendsto_unitConvexApproxScale_zero.comp (tendsto_add_atTop_nat 1)
  set v : ℕ → Vec d → ℝ := fun n => convexApproxSmoothRepresentative (axisCube z L) unitConvexApproxKernel
    u.toFun x0 (L / 4) (ε n) with hvdef
  have hlp := tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn hU hρ hp1' hpT u.memLp
    hball hr hεt (Eventually.of_forall hε0) (Eventually.of_forall hε1)
  have hlp' : Tendsto (fun n => eLpNorm (v n - u.toFun) (ENNReal.ofReal p) (volume.restrict (axisCube z L)))
      atTop (𝓝 0) := by
    refine hlp.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' hU.isOpen.measurableSet).2 (ae_of_all _ fun x hx => ?_)
    simp only [Pi.sub_apply, hvdef]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU hρ hx hball hr
      (hε0 n) (hε1 n)]
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by simpa using hp0) hlp'
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  set Gr := (eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L))).toReal
    with hGrdef
  have hGr0 : 0 ≤ Gr := ENNReal.toReal_nonneg
  set Hc : ℝ := 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * Gr with hHc
  have hHc0 : 0 ≤ Hc := by
    have : 0 < 1 / (1 - (d : ℝ) / p) := one_div_pos.2 hα
    positivity
  set α : ℝ := 1 - (d : ℝ) / p with hαdef
  set f : ℕ → Vec d → ℝ := fun k => v (ns k) with hfdef
  have hH : ∀ k, ∀ x y, x ∈ (axisCube z L) → y ∈ (axisCube z L) → |f k x - f k y| ≤ Hc * ‖x - y‖ ^ α := by
    intro k x y hx hy
    have := abs_sub_convexApproxSmoothRepresentative_le hL hp1 hp u (hε0 (ns k)) (hε1 (ns k))
      hx hy
    calc _ ≤ _ := this
      _ = _ := by rw [hHc]; ring
  have hg : Continuous fun t : ℝ => Hc * t ^ α :=
    continuous_const.mul (Real.continuous_rpow_const hα.le)
  have hg0 : Hc * (0 : ℝ) ^ α = 0 := by rw [Real.zero_rpow hα.ne', mul_zero]
  have hmod : ∀ η > 0, ∃ δ > 0, ∀ a b : Vec d, ‖a - b‖ < δ → Hc * ‖a - b‖ ^ α < η := by
    intro η hη
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hg.continuousAt η hη
    refine ⟨δ, hδ, fun a b hab => ?_⟩
    have := h (x := ‖a - b‖) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]; exact hab)
    rw [Real.dist_eq, hg0, sub_zero, abs_lt] at this
    exact this.2
  set S : Set (Vec d) := {x | x ∈ (axisCube z L) ∧ Tendsto (fun k => f k x) atTop (𝓝 (u.toFun x))} with hS
  have hSae : ∀ᵐ x ∂volume, x ∈ (axisCube z L) → x ∈ S := by
    have := (ae_restrict_iff' hU.isOpen.measurableSet).1 hae
    filter_upwards [this] with x hx hxU
    exact ⟨hxU, hx hxU⟩
  have hdense : ∀ x, x ∈ (axisCube z L) → ∀ η > 0, ∃ x' ∈ S, Hc * ‖x - x'‖ ^ α < η := by
    intro x hx η hη
    obtain ⟨δ, hδ, hδη⟩ := hmod η hη
    by_contra hcon
    push Not at hcon
    have hsub : (axisCube z L) ∩ Metric.ball x δ ⊆ {y | ¬(y ∈ (axisCube z L) → y ∈ S)} := by
      intro y hy hyS
      have := hcon y (hyS hy.1)
      have hlt : ‖x - y‖ < δ := by
        rw [← dist_eq_norm]; exact Metric.mem_ball'.1 hy.2
      exact absurd (hδη x y hlt) (not_lt.2 this)
    have hpos : 0 < volume ((axisCube z L) ∩ Metric.ball x δ) :=
      (hU.isOpen.inter Metric.isOpen_ball).measure_pos volume ⟨x, hx, Metric.mem_ball_self hδ⟩
    have hnull : volume {y | ¬(y ∈ (axisCube z L) → y ∈ S)} = 0 := ae_iff.1 hSae
    exact hpos.ne' (measure_mono_null hsub hnull)
  have hlim : ∀ x ∈ (axisCube z L), ∃ l, Tendsto (fun k => f k x) atTop (𝓝 l) := fun x hx =>
    exists_tendsto_of_dense (· ∈ (axisCube z L)) S f (fun x y => Hc * ‖x - y‖ ^ α) hH (fun x hx => hx.1)
      hdense (fun x hx => ⟨_, hx.2⟩) hx
  set ū : Vec d → ℝ := fun x => limUnder atTop (fun k => f k x) with hūdef
  have hū : ∀ x ∈ (axisCube z L), Tendsto (fun k => f k x) atTop (𝓝 (ū x)) := fun x hx =>
    tendsto_nhds_limUnder (hlim x hx)
  have hhold : ∀ x ∈ (axisCube z L), ∀ y ∈ (axisCube z L), |ū x - ū y| ≤ Hc * ‖x - y‖ ^ α := fun x hx y hy =>
    le_of_tendsto' ((hū x hx).sub (hū y hy)).abs fun k => hH k x y hx hy
  refine ⟨ū, ?_, ?_, ?_⟩
  · rw [Metric.continuousOn_iff]
    intro b hb η hη
    obtain ⟨δ, hδ, hδη⟩ := hmod η hη
    refine ⟨δ, hδ, fun a ha hab => ?_⟩
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hhold a ha b hb) (hδη a b ?_)
    rw [← dist_eq_norm]; exact hab
  · refine (ae_restrict_iff' hU.isOpen.measurableSet).2 (hSae.mono fun x hx hxU => ?_)
    exact tendsto_nhds_unique (hū x hxU) (hx hxU).2
  · exact fun x hx y hy => (hhold x hx y hy).trans (le_of_eq (by rw [hHc]; ring))

/-- **Morrey's inequality for `W^{1,p}` on an axis cube**: every continuous representative of `u`
satisfies the Hölder bound `|ū x - ū y| ≤ C ‖x - y‖^{1-d/p} ‖∇u‖_{L^p}`. -/
theorem w1p_morrey_holder (hd0 : 0 < d) {z : Vec d} {L : ℝ} (hL : 0 < L) {p : ℝ}
    (hp : (d : ℝ) < p) (u : W1pFunction (axisCube z L) (ENNReal.ofReal p)) {ū : Vec d → ℝ}
    (hc : ContinuousOn ū (axisCube z L)) (hae : ū =ᵐ[volume.restrict (axisCube z L)] u.toFun)
    {x y : Vec d} (hx : x ∈ axisCube z L) (hy : y ∈ axisCube z L) :
    |ū x - ū y| ≤ 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) *
      (eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p)
        (volume.restrict (axisCube z L))).toReal := by
  obtain ⟨ū', hc', hae', h'⟩ := w1p_exists_continuous_representative hd0 hL hp u
  have heq : Set.EqOn ū ū' (axisCube z L) :=
    Measure.eqOn_open_of_ae_eq (hae.trans hae'.symm) (isOpen_axisCube z L) hc hc'
  rw [heq hx, heq hy]
  exact h' x hx y hy

/-- Satisfiability witness: the affine function `x ↦ x 0` on the unit interval (`d = 1`, `p = 2`),
viewed as a `W^{1,2}` function through the smooth constructor, with the Hölder bound at the points
`1/4` and `3/4`. -/
example :
    |(fun x : Vec 1 => x 0) (fun _ => 1 / 4) - (fun x : Vec 1 => x 0) (fun _ => 3 / 4)| ≤
      4 * ((1 : ℕ) : ℝ) * (1 / (1 - ((1 : ℕ) : ℝ) / 2)) *
        ‖(fun _ : Fin 1 => (1 / 4 : ℝ)) - (fun _ => 3 / 4)‖ ^ (1 - ((1 : ℕ) : ℝ) / 2) *
        (eLpNorm (fun w => ‖(W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
            (U := axisCube (0 : Vec 1) 1) (p := ENNReal.ofReal 2)
            (isOpenBoundedConvexDomain_axisCube (0 : Vec 1) 1)
            (f := fun x : Vec 1 => x 0)
            (ContinuousLinearMap.contDiff
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0))).grad w‖)
          (ENNReal.ofReal 2) (volume.restrict (axisCube (0 : Vec 1) 1))).toReal := by
  refine w1p_morrey_holder (d := 1) (by norm_num) (z := (0 : Vec 1)) (L := 1) (by norm_num)
    (p := 2) (by norm_num) (W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_axisCube (0 : Vec 1) 1) (p := ENNReal.ofReal 2)
      (f := fun x : Vec 1 => x 0) (ContinuousLinearMap.contDiff
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)))
    (ū := fun x : Vec 1 => x 0)
    (ContinuousLinearMap.continuous
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).continuousOn
    (Filter.EventuallyEq.refl _ _) ?_ ?_
  · intro i _; norm_num
  · intro i _; norm_num

end SuperdiffusionCLT.Section7
