/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorW2p

/-!
# Continuous weak derivatives are classical derivatives

If `w` and `G₀, …, G_{d-1}` are continuous, `G_i` is the weak `i`-th partial derivative of `w`
against all smooth compactly supported tests, and `w`, `G_i` have compact support, then `w` is
`C¹` with `∂ᵢ w = Gᵢ`.  Proof: the mollifications `ρₙ ⋆ w` are smooth with partial derivatives
`ρₙ ⋆ Gᵢ` and converge uniformly together with their derivatives.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped Convolution

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_moll_fderiv (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {w : Vec d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    {G : Fin d → Vec d → ℝ}
    (hweak : ∀ i, ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, w x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x)
    (x : Vec d) (i : Fin d) :
    fderiv ℝ (intW2p_moll δ hδ n w) x (basisVec i) = intW2p_moll δ hδ n (G i) x := by
  have h1 : ContDiff ℝ 1 (((intW2p_bump δ hδ n).normed volume)) :=
    ((intW2p_bump (d := d) δ hδ n).contDiff_normed (μ := volume)).of_le (by exact_mod_cast le_top)
  have hli : LocallyIntegrable w volume := hw.locallyIntegrable
  have h := ((intW2p_bump (d := d) δ hδ n).hasCompactSupport_normed (μ := volume)).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) h1 hli x
  have h' : HasFDerivAt (intW2p_moll δ hδ n w) _ x := h
  rw [h'.fderiv]
  unfold intW2p_moll
  rw [convolution_eq_swap]
  rw [convolution_eq_swap]
  set ρ := (intW2p_bump (d := d) δ hδ n).normed volume with hρ
  have hρs : ContDiff ℝ (⊤ : ℕ∞) ρ := (intW2p_bump (d := d) δ hδ n).contDiff_normed (μ := volume)
  have hF : ∀ t, (ContinuousLinearMap.precompL (Vec d) (ContinuousLinearMap.lsmul ℝ ℝ)
      (fderiv ℝ ρ (x - t))) (w t) = w t • fderiv ℝ ρ (x - t) := fun t ↦ by
    ext v
    simp [ContinuousLinearMap.precompL, mul_comm]
  have hFc : Continuous fun t ↦ w t • fderiv ℝ ρ (x - t) :=
    hw.smul ((hρs.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id))
  have hFs : HasCompactSupport fun t ↦ w t • fderiv ℝ ρ (x - t) := hwc.smul_right
  have hint := hFc.integrable_of_hasCompactSupport (μ := volume) hFs
  rw [ContinuousLinearMap.integral_apply (by simpa only [hF] using hint)]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun t ↦ ρ (x - t) :=
    hρs.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport fun t ↦ ρ (x - t) :=
    ((intW2p_bump (d := d) δ hδ n).hasCompactSupport_normed (μ := volume)).comp_homeomorph
      ((Homeomorph.neg (Vec d)).trans (Homeomorph.addLeft x))
  have hw' := hweak i _ hφ hφc
  have hder : ∀ y, fderiv ℝ (fun t ↦ ρ (x - t)) y (basisVec i) = -fderiv ℝ ρ (x - y) (basisVec i) :=
    fun y ↦ by
    have := ((hρs.differentiable (by simp)).differentiableAt (x := x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
    have h2 : HasFDerivAt (fun t ↦ ρ (x - t)) _ y := this
    rw [h2.fderiv]
    simp
  have e1 : ∀ y, (((ContinuousLinearMap.precompL (Vec d) (ContinuousLinearMap.lsmul ℝ ℝ))
      (fderiv ℝ ρ (x - y))) (w y)) (basisVec i) = -(w y * fderiv ℝ (fun t ↦ ρ (x - t)) y (basisVec i)) :=
    fun y ↦ by
    rw [hder y]
    simp [ContinuousLinearMap.precompL, mul_comm]
  simp_rw [e1, integral_neg, hw', neg_neg]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp [mul_comm]

theorem intC2_moll_uniform (δ : ℝ) (hδ : 0 < δ) {ψ : Vec d → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x, |intW2p_moll δ hδ n ψ x - ψ x| ≤ ε := by
  obtain ⟨η, hη, hηψ⟩ := Metric.uniformContinuous_iff.1 (hc.uniformContinuous_of_continuous hψ) ε hε
  have hev : ∀ᶠ n : ℕ in atTop, (intW2p_bump (d := d) δ hδ n).rOut < η :=
    (intW2p_tendsto_rOut δ hδ).eventually (gt_mem_nhds hη)
  filter_upwards [hev] with n hn x
  have h := (intW2p_bump (d := d) δ hδ n).dist_normed_convolution_le (μ := volume) (x₀ := x)
    (g := ψ) (ε := ε) hψ.aestronglyMeasurable (fun y hy ↦ by
      have : dist y x < η := lt_trans (Metric.mem_ball.1 hy) hn
      exact (hηψ this).le)
  rw [Real.dist_eq] at h
  exact h

theorem intC2_opNorm_le (L : Vec d →L[ℝ] ℝ) : ‖L‖ ≤ ∑ i, |L (basisVec i)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) fun v ↦ ?_
  have hv : v = ∑ i, v i • basisVec i := by
    funext j
    simp [basisVec, Pi.single_apply]
  have h1 : L v = ∑ i, v i * L (basisVec i) := by
    conv_lhs => rw [hv]
    simp [map_sum]
  rw [h1, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
    (abs_nonneg _)

/-- The candidate derivative `∑ Gᵢ(x) eᵢ*`. -/
noncomputable def intC2_cand (G : Fin d → Vec d → ℝ) (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, G i x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i

theorem intC2_cand_apply (G : Fin d → Vec d → ℝ) (x : Vec d) (i : Fin d) :
    intC2_cand G x (basisVec i) = G i x := by
  simp [intC2_cand, basisVec, Pi.single_apply]

/-- **A continuous weak gradient is the classical gradient** (compactly supported case). -/
theorem intC2_hasFDerivAt_of_weak {w : Vec d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    {G : Fin d → Vec d → ℝ} (hG : ∀ i, Continuous (G i)) (hGc : ∀ i, HasCompactSupport (G i))
    (hweak : ∀ i, ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, w x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x) (x : Vec d) :
    HasFDerivAt w (intC2_cand G x) x := by
  refine hasFDerivAt_of_tendstoUniformly (l := atTop) (f := fun n ↦ intW2p_moll 1 one_pos n w)
    (f' := fun n y ↦ fderiv ℝ (intW2p_moll 1 one_pos n w) y) (g' := intC2_cand G) ?_ ?_ ?_ x
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hd0 : (0 : ℝ) < d + 1 := by positivity
    have hev : ∀ i, ∀ᶠ n : ℕ in atTop, ∀ y, |intW2p_moll 1 one_pos n (G i) y - G i y| ≤
        ε / 2 / (d + 1) := fun i ↦ intC2_moll_uniform 1 one_pos (hG i) (hGc i) (by positivity)
    have hall := (Filter.eventually_all.2 hev)
    filter_upwards [hall] with n hn y
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (intC2_opNorm_le _) ?_
    have hterm : ∀ i, |(intC2_cand G y - fderiv ℝ (intW2p_moll 1 one_pos n w) y) (basisVec i)| ≤
        ε / 2 / (d + 1) := fun i ↦ by
      rw [sub_apply, intC2_cand_apply, intC2_moll_fderiv 1 one_pos n hw hwc hweak y i,
        abs_sub_comm]
      exact hn i y
    calc _ ≤ ∑ _i : Fin d, ε / 2 / (d + 1) := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = d * (ε / 2 / (d + 1)) := by simp
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hd0]
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith only [this, hε]
  · intro n y
    exact (((intW2p_moll_contDiff 1 one_pos n hw).differentiable (by simp)) y).hasFDerivAt
  · intro y
    exact intW2p_moll_tendsto 1 one_pos hw y

theorem intC2_bump {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} (hx : x ∈ U) :
    ∃ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      ∀ᶠ y in 𝓝 x, η y = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  let b : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith only [hε]⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, ?_⟩
  · rw [b.tsupport_eq]
    refine (Metric.closedBall_subset_ball ?_).trans hball
    show ε / 2 < ε
    linarith only [hε]
  · filter_upwards [Metric.ball_mem_nhds x (show 0 < b.rIn by show 0 < ε / 4; positivity)] with y hy
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)

theorem intC2_continuous_mul {U : Set (Vec d)} (hU : IsOpen U) {η f : Vec d → ℝ}
    (hη : Continuous η) (hs : tsupport η ⊆ U) (hf : ContinuousOn f U) :
    Continuous fun y ↦ η y * f y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ U
  · exact hη.continuousAt.mul (hf.continuousAt (hU.mem_nhds hy))
  · have hy' : y ∉ tsupport η := fun h ↦ hy (hs h)
    have : (fun z ↦ η z * f z) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hy'] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    exact continuousAt_const.congr this.symm

theorem intC2_integral_eq {U : Set (Vec d)} (hU : IsOpen U) {θ f : Vec d → ℝ}
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) (hs : tsupport θ ⊆ U) (hf : ContinuousOn f U) :
    Integrable (fun y ↦ θ y * f y) volume ∧
      ∫ y in U, θ y * f y = ∫ y, θ y * f y := by
  have hc := intC2_continuous_mul hU hθ hs hf
  have hcs : HasCompactSupport fun y ↦ θ y * f y := hθc.mul_right
  have hint := hc.integrable_of_hasCompactSupport (μ := volume) hcs
  refine ⟨hint, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_⟩
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hs h)), zero_mul]

theorem intC2_d1_cont {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin d) :
    Continuous fun y ↦ fderiv ℝ η y (basisVec i) :=
  (hη.continuous_fderiv (by simp)).clm_apply continuous_const

theorem intC2_d1_ts {η : Vec d → ℝ} (i : Fin d) :
    tsupport (fun y ↦ fderiv ℝ η y (basisVec i)) ⊆ tsupport η :=
  tsupport_fderiv_apply_subset ℝ (basisVec i)

/-- **Local version.**  A function continuous on an open set `U` whose weak partials in `U`
are continuous on `U` is classically differentiable on `U`. -/
theorem intC2_hasFDerivAt_of_weak_local {U : Set (Vec d)} (hU : IsOpen U) {w : Vec d → ℝ}
    {G : Fin d → Vec d → ℝ} (hw : ContinuousOn w U) (hG : ∀ i, ContinuousOn (G i) U)
    (hweak : ∀ i, HasWeakPartialDerivOn U i w (G i)) {x : Vec d} (hx : x ∈ U) :
    HasFDerivAt w (intC2_cand G x) x := by
  obtain ⟨η, hη, hηc, hηs, hη1⟩ := intC2_bump hU hx
  have hd1 : ∀ i, Continuous fun y ↦ fderiv ℝ η y (basisVec i) := intC2_d1_cont hη
  have hd1c : ∀ i, HasCompactSupport fun y ↦ fderiv ℝ η y (basisVec i) := fun i ↦
    hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hd1s : ∀ i, tsupport (fun y ↦ fderiv ℝ η y (basisVec i)) ⊆ U := fun i ↦
    (intC2_d1_ts i).trans hηs
  have hWc : Continuous fun y ↦ η y * w y := intC2_continuous_mul hU hη.continuous hηs hw
  have hGc : ∀ i, Continuous fun y ↦ η y * G i y + fderiv ℝ η y (basisVec i) * w y := fun i ↦
    (intC2_continuous_mul hU hη.continuous hηs (hG i)).add
      (intC2_continuous_mul hU (hd1 i) (hd1s i) hw)
  have key := intC2_hasFDerivAt_of_weak (w := fun y ↦ η y * w y) hWc hηc.mul_right
    (G := fun i y ↦ η y * G i y + fderiv ℝ η y (basisVec i) * w y) hGc
    (fun i ↦ (hηc.mul_right).add ((hd1c i).mul_right)) (fun i φ hφ hφc ↦ by
      have hψ : ContDiff ℝ (⊤ : ℕ∞) fun y ↦ η y * φ y := hη.mul hφ
      have hψc : HasCompactSupport fun y ↦ η y * φ y := hφc.mul_left
      have hψs : tsupport (fun y ↦ η y * φ y) ⊆ U := tsupport_mul_subset_left.trans hηs
      have hw1 := hweak i _ hψ hψc hψs
      have hpr : ∀ y, fderiv ℝ (fun y ↦ η y * φ y) y (basisVec i) =
          η y * fderiv ℝ φ y (basisVec i) + φ y * fderiv ℝ η y (basisVec i) := fun y ↦ by
        rw [fderiv_fun_mul (hη.differentiable (by simp) y) (hφ.differentiable (by simp) y)]
        simp
      have hφ0 : Continuous φ := hφ.continuous
      have hdφ := intC2_d1_cont hφ i
      have a1 := intC2_integral_eq hU (θ := fun y ↦ η y * fderiv ℝ φ y (basisVec i))
        (f := w) (hη.continuous.mul hdφ) (hηc.mul_right) (tsupport_mul_subset_left.trans hηs) hw
      have a2 := intC2_integral_eq hU (θ := fun y ↦ φ y * fderiv ℝ η y (basisVec i))
        (f := w) (hφ0.mul (hd1 i)) ((hd1c i).mul_left) (tsupport_mul_subset_right.trans (hd1s i)) hw
      have a3 := intC2_integral_eq hU (θ := fun y ↦ η y * φ y) (f := G i)
        (hη.continuous.mul hφ0) hψc hψs (hG i)
      have hsplit : ∫ y in U, w y * fderiv ℝ (fun y ↦ η y * φ y) y (basisVec i) =
          (∫ y in U, (η y * fderiv ℝ φ y (basisVec i)) * w y) +
            ∫ y in U, (φ y * fderiv ℝ η y (basisVec i)) * w y := by
        rw [← integral_add a1.1.integrableOn a2.1.integrableOn]
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        simp only [hpr y]
        ring
      have hr : ∫ y in U, G i y * (η y * φ y) = ∫ y in U, (η y * φ y) * G i y :=
        integral_congr_ae (Eventually.of_forall fun y ↦ by ring)
      rw [hsplit, hr, a1.2, a2.2, a3.2] at hw1
      have e1 : ∫ y, (η y * w y) * fderiv ℝ φ y (basisVec i) =
          ∫ y, (η y * fderiv ℝ φ y (basisVec i)) * w y :=
        integral_congr_ae (Eventually.of_forall fun y ↦ by ring)
      have e2 : ∫ y, (η y * G i y + fderiv ℝ η y (basisVec i) * w y) * φ y =
          (∫ y, (η y * φ y) * G i y) + ∫ y, (φ y * fderiv ℝ η y (basisVec i)) * w y := by
        rw [← integral_add a3.1 a2.1]
        exact integral_congr_ae (Eventually.of_forall fun y ↦ by ring)
      rw [e1, e2]
      linarith only [hw1])
  have hev : (fun y ↦ η y * w y) =ᶠ[𝓝 x] w := by
    filter_upwards [hη1] with y hy
    rw [hy, one_mul]
  have hd0 : fderiv ℝ η x = 0 := by
    have : η =ᶠ[𝓝 x] fun _ ↦ 1 := hη1
    rw [this.fderiv_eq]
    simp
  have hcand : intC2_cand (fun i y ↦ η y * G i y + fderiv ℝ η y (basisVec i) * w y) x =
      intC2_cand G x := by
    unfold intC2_cand
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show (η x * G i x + fderiv ℝ η x (basisVec i) * w x) • _ = _
    rw [hd0, hη1.self_of_nhds]
    simp
  have key' := key x
  rw [hcand] at key'
  exact key'.congr_of_eventuallyEq hev.symm

end SuperdiffusionCLT.Section8
