/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2K
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApi
public import SuperdiffusionCLT.Section8.Prereq.BallBoundaryD
public import SuperdiffusionCLT.Section8.Prereq.ResolventMismatchB
public import SuperdiffusionCLT.Section8.Prereq.InteriorW2pB
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateB

/-!
# The limit profile and the pointwise equation

For the heat field `½ Id` on the unit ball, the continuous zero-trace profile `wb` of
`lam v - ½ Δ v = 1` is `C²` inside, solves the equation pointwise, and `1 - lam wb` decays
exponentially away from the boundary (`resMis_exp_decay`).

* `exitEst_h1_congr`: an `H¹` function may be re-represented on a null set;
* `exitEst_intC2_weak`, `exitEst_intC2_weak_congr`: the scalar-forced weak equation tested on smooth
  compactly supported functions;
* `exitEst_pointwise_local`: the pointwise equation for a weak solution which is `C²` inside;
* `exitEst_limit_profile`: the limit profile.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.DivergenceForm

variable {d : ℕ}

/-- An `H¹` function may be re-represented on a null set. -/
theorem exitEst_h1_congr {U : Set (Vec d)} (u : H1Function U) {w : Vec d → ℝ}
    (hw : w =ᵐ[volume.restrict U] u.toFun) :
    ∃ u' : H1Function U, u'.toFun = w ∧ u'.grad = u.grad := by
  have hweak : HasWeakGradientOn U w u.grad := fun i φ hφ hc hs => by
    have h := u.hasWeakGradient i φ hφ hc hs
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [hw] with x hx
    rw [hx]
  exact ⟨H1Function.mk w u.grad (MemLp.ae_eq hw.symm u.memL2) u.gradMemL2 hweak, rfl, rfl⟩

/-- The scalar-forced weak equation `-∇·(a∇u) = 1 - lam u`, tested on smooth compactly supported
functions. -/
theorem exitEst_intC2_weak {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d} {lam : ℝ}
    (u : H1Function U)
    (hsol : IsScalarForcedWeakSolution a U (fun y => 1 - lam * u.toFun y) u) :
    intC2_Weak a lam (fun _ => 1) U u := by
  intro φ hφ hc hs
  have h := hsol.2 (H10Function.ofContDiff hU hφ hc hs)
  have hφ0 : Continuous φ := hφ.continuous
  have i1 : Integrable φ (volume.restrict U) := (hφ0.integrable_of_hasCompactSupport hc).restrict
  have i2 : Integrable (fun x => u.toFun x * φ x) (volume.restrict U) :=
    intW2p_integrable_mul u.memL2 hφ0 hc
  have e : (∫ x in U, (1 - lam * u.toFun x) * (H10Function.ofContDiff hU hφ hc hs).toH1Function.toFun x) =
      (∫ x in U, 1 * φ x) - lam * ∫ x in U, u.toFun x * φ x := by
    rw [← integral_const_mul, ← integral_sub (by simpa using i1) (i2.const_mul lam)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [H10Function.ofContDiff, H1Function.ofContDiff]
    ring
  rw [e] at h
  have e2 : (∫ x in U, vecDot (matVecMul (a x) (u.grad x))
      ((H10Function.ofContDiff hU hφ hc hs).toH1Function.grad x)) =
      ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (fun i => fderiv ℝ φ x (basisVec i)) := rfl
  rw [e2] at h
  linarith only [h]

/-- The weak equation is insensitive to a null-set change of the representative. -/
theorem exitEst_intC2_weak_congr {U : Set (Vec d)} {a : CoeffField d} {mu : ℝ} {g : Vec d → ℝ}
    {u u' : H1Function U} (h : intC2_Weak a mu g U u) (hg : u'.grad = u.grad)
    (hf : u'.toFun =ᵐ[volume.restrict U] u.toFun) : intC2_Weak a mu g U u' := by
  intro φ hφ hc hs
  have h1 := h φ hφ hc hs
  rw [hg]
  have e : ∫ x in U, u'.toFun x * φ x = ∫ x in U, u.toFun x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]
  rw [e]
  exact h1

/-- **The pointwise equation, local form.**  For a constant isotropic coefficient and a weak
solution which is `C²` at every point of the open set `U`, the equation holds pointwise. -/
theorem exitEst_pointwise_local {U : Set (Vec d)} (hU : IsOpen U) {c mu : ℝ} {g : Vec d → ℝ}
    (hg : Continuous g) (u : H1Function U)
    (hw : intC2_Weak (fun _ => c • (1 : Mat d)) mu g U u)
    (h2 : ∀ x ∈ U, ContDiffAt ℝ 2 u.toFun x) {x : Vec d} (hx : x ∈ U) :
    c * Brownian.vecLaplacian u.toFun x = mu * u.toFun x - g x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hK : IsCompact (Metric.closedBall x (ε / 2)) := isCompact_closedBall x (ε / 2)
  have hKU : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith only [hε])).trans hball
  obtain ⟨χ, hχ, -, hχ1, hχs⟩ := exists_contDiff_one_on_compact_tsupport_subset hK hKU hU
  set ũ : Vec d → ℝ := fun y => χ y * u.toFun y with hũ
  have hũ2 : ContDiff ℝ 2 ũ := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ U
    · exact ((hχ.of_le (by simp)).contDiffAt).mul (h2 z hz)
    · have hz' : z ∉ tsupport χ := fun h => hz (hχs h)
      have h0 : χ =ᶠ[nhds z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with y hy
      simp [hũ, hy]
  set B : Set (Vec d) := Metric.ball x (ε / 2) with hB
  have hBo : IsOpen B := Metric.isOpen_ball
  have hBK : B ⊆ Metric.closedBall x (ε / 2) := Metric.ball_subset_closedBall
  have hBU : B ⊆ U := hBK.trans hKU
  have hxB : x ∈ B := Metric.mem_ball_self (by linarith only [hε])
  have hu₁ := hw.restrict hBo hBU
  obtain ⟨u₂, hu₂f, hu₂g⟩ := exitEst_h1_congr (u.restrict hBo hBU) (w := ũ) (by
    refine (ae_restrict_iff' hBo.measurableSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have : χ y = 1 := by simpa using hχ1 (hBK hy)
    simp [hũ, this, H1Function.restrict])
  have hu₂ := exitEst_intC2_weak_congr hu₁ hu₂g (by
    refine (ae_restrict_iff' hBo.measurableSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have : χ y = 1 := by simpa using hχ1 (hBK hy)
    simp [hu₂f, hũ, this, H1Function.restrict])
  have hb : Bornology.IsBounded B := Metric.isBounded_ball
  have key := intC2_pointwise hBo hb (a := fun _ => c • (1 : Mat d)) (fun i j => contDiff_const)
    hg hu₂ (by rw [hu₂f]; exact hũ2) hxB
  rw [hu₂f, divForm_const_smul_one c ũ hũ2 x] at key
  have hloc : ũ =ᶠ[nhds x] u.toFun := by
    filter_upwards [hBo.mem_nhds hxB] with y hy
    have : χ y = 1 := by simpa using hχ1 (hBK hy)
    simp [hũ, this]
  have hlap : Brownian.vecLaplacian ũ x = Brownian.vecLaplacian u.toFun x := by
    rw [Brownian.vecLaplacian_eq_sum_fderiv, Brownian.vecLaplacian_eq_sum_fderiv,
      hloc.fderiv.fderiv_eq]
  rw [hlap, hloc.eq_of_nhds] at key
  exact key

/-- The Laplacian commutes with constant factors. -/
theorem exitEst_lap_const_mul (c : ℝ) {f : Vec d → ℝ} {x : Vec d} (hf : ContDiffAt ℝ 2 f x) :
    Brownian.vecLaplacian (fun y => c * f y) x = c * Brownian.vecLaplacian f x := by
  unfold Brownian.vecLaplacian
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := iteratedFDeriv_const_smul_apply (a := c) hf
  rw [show (fun y => c * f y) = c • f from rfl, h]
  simp

/-- **The limit profile.**  For the heat field `½ Id` on the unit ball there is a continuous
zero-trace profile `wb`, a weak solution `vb` of `lam v - ½ Δ v = 1` with zero data, agreeing with
`wb` almost everywhere, such that `1 - lam wb` decays exponentially away from the boundary. -/
theorem exitEst_limit_profile [NeZero d] (hd : 2 ≤ d) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (wb : Vec d → ℝ) (vb : H1Function (euclideanBall (0 : Vec d) 1)), Continuous wb ∧
      SuperdiffusionCLT.Section7.IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d))
        (euclideanBall (0 : Vec d) 1) (fun x => 1 - lam * vb.toFun x) 0 vb ∧
      (∀ᵐ y ∂(volume.restrict (euclideanBall (0 : Vec d) 1)), wb y = vb.toFun y) ∧
      ∀ (x : Vec d) (δ : ℝ), 0 < δ →
        (∀ y : Vec d, vecNormSq (y - x) < δ ^ 2 → y ∈ euclideanBall (0 : Vec d) 1) →
        1 - lam * wb x ≤
          2 * d * Real.exp (-(Real.sqrt (lam / (1 / 2)) * (δ / Real.sqrt d))) := by
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) one_pos
  have hUo : IsOpen (euclideanBall (0 : Vec d) 1) := hV.isOpen
  have hb : Bornology.IsBounded (euclideanBall (0 : Vec d) 1) := hV.isBoundedDomain.isBounded
  obtain ⟨wb, u, hw, hoff, hwu, hsol⟩ :=
    ballBdry_data (ballBdry_heatInput (nu := (1 / 2 : ℝ)) hd (by norm_num)) (0 : Vec d) one_pos hlam
  have ha : (ballBdry_heatInput (nu := (1 / 2 : ℝ)) hd (by norm_num) : FieldInputData d _ _).analyticData.a =
      fun _ => (1 / 2 : ℝ) • (1 : Mat d) := by
    funext y
    simp [FieldInputData.analyticData]
  rw [ha] at hsol
  have hweak0 : intC2_Weak (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) lam (fun _ => 1)
      (euclideanBall (0 : Vec d) 1) u.toH1Function :=
    exitEst_intC2_weak hUo u.toH1Function hsol
  obtain ⟨vb', hf', hg'⟩ := exitEst_h1_congr u.toH1Function (w := wb) hwu
  have hweak' : intC2_Weak (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) lam (fun _ => 1)
      (euclideanBall (0 : Vec d) 1) vb' :=
    exitEst_intC2_weak_congr hweak0 hg' (by rw [hf']; exact hwu)
  obtain ⟨M, hM⟩ := intC2_bound_on hb hw
  have hsk : ∀ (y : Vec d) (i j : Fin d), (fun _ : Vec d => (1 / 2 : ℝ) • (1 : Mat d)) y i j +
      (fun _ : Vec d => (1 / 2 : ℝ) • (1 : Mat d)) y j i = if i = j then 2 * (1 / 2) else 0 := by
    intro y i j
    by_cases h : i = j
    · subst h; simp; norm_num
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), h]
  have h2 : ∀ x ∈ euclideanBall (0 : Vec d) 1, ContDiffAt ℝ 2 wb x := fun x hx => by
    have := intC2_contDiffAt hd hUo (a := fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (nu := 1 / 2)
      (by norm_num) hsk (fun i j => contDiff_const) (mu := lam) (g := fun _ => 1) contDiff_const
      (M := M) (u := vb') hweak' (by rw [hf']; exact hw.continuousOn)
      (fun y hy => by rw [hf']; exact hM y hy) hx
    rwa [hf'] at this
  have hpt : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      (1 / 2 : ℝ) * Brownian.vecLaplacian wb x = lam * wb x - 1 := fun x hx => by
    have := exitEst_pointwise_local hUo (c := 1 / 2) (mu := lam) (g := fun _ => 1)
      continuous_const vb' hweak' (fun y hy => by rw [hf']; exact h2 y hy) hx
    rwa [hf'] at this
  refine ⟨wb, u.toH1Function, hw, ⟨fun φ => ?_, ⟨u, ?_⟩⟩, hwu, ?_⟩
  · have := hsol.2 φ
    simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero]
    exact this
  · funext x
    simp
  · intro x δ hδ hball
    refine resMis_exp_decay hUo hb (w := fun y => 1 - lam * wb y) (lam := lam) (s := 1 / 2)
      (by fun_prop) (fun y hy => contDiffAt_const.sub (contDiffAt_const.mul (h2 y hy))) hlam
      (by norm_num) (fun y hy => ?_) (fun y hy => ?_) hδ hball
    · have e1 : Brownian.vecLaplacian (fun y => 1 - lam * wb y) y =
          0 - lam * Brownian.vecLaplacian wb y := by
        rw [resMis_vecLaplacian_sub (f := fun _ => (1 : ℝ)) (g := fun y => lam * wb y)
          contDiffAt_const (contDiffAt_const.mul (h2 y hy)), resMis_vecLaplacian_const,
          exitEst_lap_const_mul lam (h2 y hy)]
      rw [e1]
      have e2 : lam * (1 - lam * wb y) - 1 / 2 * (0 - lam * Brownian.vecLaplacian wb y) =
          lam * (1 - lam * wb y + 1 / 2 * Brownian.vecLaplacian wb y) := by ring
      rw [e2]
      have e3 := hpt y hy
      have : 1 - lam * wb y + 1 / 2 * Brownian.vecLaplacian wb y = 0 := by linarith only [e3]
      rw [this, mul_zero]
    · have hy' : y ∉ euclideanBall (0 : Vec d) 1 := by
        rw [hUo.frontier_eq] at hy
        exact hy.2
      simp [hoff y hy']

end SuperdiffusionCLT.Section8
