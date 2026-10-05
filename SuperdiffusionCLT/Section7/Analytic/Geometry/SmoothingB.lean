/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.H1.Definitions
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Continuity
public import SuperdiffusionCLT.Section7.Analytic.Morrey.W1pD

/-!
# Bounded weak gradient on a convex domain gives a Lipschitz representative

For `u ∈ H¹(R)` on an open bounded convex set `R` whose weak gradient satisfies
`|∂ᵢ u| ≤ G` almost everywhere, the convex-domain smoothings `v_ε` (a mollification of `u` sampled
along segments towards a fixed interior ball) are smooth with `|∂ᵢ v_ε| ≤ G` on all of `R`; hence
they are `d G`-Lipschitz for the sup norm, and so is their a.e. limit.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization Filter Topology

variable {d : ℕ}

theorem smoothingSample_eq_comp (x0 x : Vec d) (r ε : ℝ) :
    (fun z => convexApproxSample x0 z r ε x) =
      (fun y : Vec d => y + ((1 - ε) • x + ε • x0)) ∘ (fun z : Vec d => (-(ε * r)) • z) := by
  funext z
  ext i
  simp only [convexApproxSample_apply, Function.comp_apply, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  ring

theorem smoothingSample_quasiMeasurePreserving (x0 x : Vec d) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) :
    Measure.QuasiMeasurePreserving (fun z => convexApproxSample x0 z r ε x) volume volume := by
  rw [smoothingSample_eq_comp]
  refine Measure.QuasiMeasurePreserving.comp
    (measurePreserving_add_right volume ((1 - ε) • x + ε • x0)).quasiMeasurePreserving ?_
  exact Measure.quasiMeasurePreserving_smul volume (neg_ne_zero.2 (mul_pos hε hr).ne')

/-- The convex smoothing of an a.e. bounded function is bounded by the same bound at every
point of the domain. -/
theorem convexApproxSmoothing_abs_le {R : Set (Vec d)} (hR : IsOpenBoundedConvexDomain R)
    {ρ f : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) {x0 x : Vec d} {r ε : ℝ} (hx : x ∈ R)
    (hball : Metric.closedBall x0 r ⊆ R) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) {G : ℝ}
    (hG : ∀ᵐ w ∂volume.restrict R, |f w| ≤ G) :
    |convexApproxSmoothing ρ f x0 r ε x| ≤ G := by
  have hRm : MeasurableSet R := hR.isOpen.measurableSet
  have hTm : MeasurableSet (tsupport ρ) := (isClosed_tsupport ρ).measurableSet
  have hTc : IsCompact (tsupport ρ) := hρ.compactSupport.isCompact
  have hae0 : ∀ᵐ w ∂volume, w ∈ R → |f w| ≤ G := (ae_restrict_iff' hRm).1 hG
  have hae1 : ∀ᵐ z ∂volume, convexApproxSample x0 z r ε x ∈ R →
      |f (convexApproxSample x0 z r ε x)| ≤ G :=
    (smoothingSample_quasiMeasurePreserving x0 x hr hε0).ae hae0
  have hae2 : ∀ᵐ z ∂volume.restrict (tsupport ρ),
      ‖convexApproxIntegrand ρ f x0 r ε x z‖ ≤ ρ z * G := by
    filter_upwards [ae_restrict_of_ae hae1, ae_restrict_mem hTm] with z hz hzT
    have hz1 : ‖z‖ ≤ 1 := by
      have := hρ.support_subset_closedBall hzT
      simpa using this
    have hmem := convexApproxSample_mem_of_isOpenBoundedConvexDomain hR hx hball hr.le hz1
      hε0.le hε1.le
    rw [convexApproxIntegrand_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg z),
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hz hmem) (hρ.nonneg z)
  have hint : Integrable (fun z => ρ z * G) (volume.restrict (tsupport ρ)) :=
    (hρ.continuous.mul continuous_const).continuousOn.integrableOn_compact hTc
  have := norm_integral_le_of_norm_le hint hae2
  rw [integral_mul_const, hρ.setIntegral_one, one_mul] at this
  rw [convexApproxSmoothing_apply]
  simpa [Real.norm_eq_abs] using this

/-- The partial derivatives of the convex smoothing of `u` are bounded by `G` on all of `R`. -/
theorem abs_fderiv_convexApproxSmoothRepresentative_le {R : Set (Vec d)}
    (hR : IsOpenBoundedConvexDomain R) (u : H1Function R) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ᵐ x ∂volume.restrict R, ∀ i, |u.grad x i| ≤ G) {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) {x0 : Vec d} {r ε : ℝ} (hball : Metric.closedBall x0 r ⊆ R)
    (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) (i : Fin d) {z : Vec d} (hz : z ∈ R) :
    |fderiv ℝ (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) z (basisVec i)| ≤ G := by
  have hRm : MeasurableSet R := hR.isOpen.measurableSet
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hRm hρ one_le_two u.memL2 hr hε0
  have hae := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec hR (i := i) hρ
    one_le_two u.memL2 (u.gradMemL2 i) (u.hasWeakGradient i) hball hr hε0 hε1
  have hG' : ∀ᵐ w ∂volume.restrict R, |u.grad w i| ≤ G := by
    filter_upwards [hG] with w hw using hw i
  have hpt : ∀ x ∈ R, |(1 - ε) * convexApproxSmoothRepresentative R ρ (fun w => u.grad w i)
      x0 r ε x| ≤ G := by
    intro x hx
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hR hρ hx hball hr hε0
      hε1, abs_mul, abs_of_nonneg (by linarith only [hε1])]
    have := convexApproxSmoothing_abs_le hR hρ hx hball hr hε0 hε1 hG'
    calc _ ≤ (1 - ε) * G := mul_le_mul_of_nonneg_left this (by linarith only [hε1])
      _ ≤ G := by nlinarith only [hG0, hε0]
  have hcont : Continuous fun x => fderiv ℝ
      (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) x (basisVec i) :=
    ((hsmooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  by_contra hcon
  push Not at hcon
  set S : Set (Vec d) := {x | x ∈ R ∧ G < |fderiv ℝ
      (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) x (basisVec i)|} with hS
  have hSo : IsOpen S := by
    have : IsOpen {x | G < |fderiv ℝ (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) x
        (basisVec i)|} := isOpen_lt continuous_const hcont.abs
    exact hR.isOpen.inter this
  have hpos : 0 < volume S := hSo.measure_pos volume ⟨z, hz, hcon⟩
  have hnull : ∀ᵐ x ∂volume, x ∈ R → |fderiv ℝ
      (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) x (basisVec i)| ≤ G := by
    rw [← ae_restrict_iff' hRm]
    filter_upwards [hae, ae_restrict_mem hRm] with x hx hxR
    rw [hx]
    exact hpt x hxR
  have h0 : volume S = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hnull)
    exact fun h => absurd (h hx.1) (not_le.2 hx.2)
  exact hpos.ne' h0

/-- The convex smoothing is `d G`-Lipschitz on `R`. -/
theorem abs_convexApproxSmoothRepresentative_sub_le {R : Set (Vec d)}
    (hR : IsOpenBoundedConvexDomain R) (u : H1Function R) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ᵐ x ∂volume.restrict R, ∀ i, |u.grad x i| ≤ G) {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) {x0 : Vec d} {r ε : ℝ} (hball : Metric.closedBall x0 r ⊆ R)
    (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) {x y : Vec d} (hx : x ∈ R) (hy : y ∈ R) :
    |convexApproxSmoothRepresentative R ρ u.toFun x0 r ε x -
      convexApproxSmoothRepresentative R ρ u.toFun x0 r ε y| ≤ d * G * ‖x - y‖ := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hR.isOpen.measurableSet hρ one_le_two u.memL2 hr hε0
  have hb : ∀ z ∈ R, ‖fderiv ℝ (convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) z‖ ≤
      d * G := by
    intro z hz
    refine (norm_le_sum_basisVec _).trans ?_
    calc _ ≤ ∑ _i : Fin d, G :=
          Finset.sum_le_sum fun i _ =>
            abs_fderiv_convexApproxSmoothRepresentative_le hR u hG0 hG hρ hball hr hε0 hε1 i hz
      _ = d * G := by simp
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := convexApproxSmoothRepresentative R ρ u.toFun x0 r ε) (s := R)
    (fun z _ => (hsmooth.differentiable (by simp)) z) hb hR.2.2 hy hx
  simpa [Real.norm_eq_abs] using this


/-- **Convex `W^{1,∞}`.** If the weak gradient of `u ∈ H¹(R)` is a.e. bounded by `G` in each
coordinate on an open bounded convex set `R`, then `u` has a representative that is
`d G`-Lipschitz on `R`. -/
theorem exists_lipschitz_representative_of_convex {R : Set (Vec d)}
    (hR : IsOpenBoundedConvexDomain R) (u : H1Function R) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ᵐ x ∂volume.restrict R, ∀ i, |u.grad x i| ≤ G) :
    ∃ ū : Vec d → ℝ, ū =ᵐ[volume.restrict R] u.toFun ∧
      ∀ x ∈ R, ∀ y ∈ R, |ū x - ū y| ≤ d * G * ‖x - y‖ := by
  have hRm : MeasurableSet R := hR.isOpen.measurableSet
  by_cases hne : R.Nonempty
  swap
  · refine ⟨u.toFun, ae_eq_refl _, fun x hx => absurd ⟨x, hx⟩ hne⟩
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨δ, hδ, hδR⟩ := Metric.isOpen_iff.1 hR.isOpen x0 hx0
  set r : ℝ := δ / 2 with hrdef
  have hr : 0 < r := by positivity
  have hball : Metric.closedBall x0 r ⊆ R :=
    (Metric.closedBall_subset_ball (by rw [hrdef]; linarith only [hδ])).trans hδR
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
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
  set v : ℕ → Vec d → ℝ := fun n => convexApproxSmoothRepresentative R unitConvexApproxKernel
    u.toFun x0 r (ε n) with hvdef
  have hlp := tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn hR hρ one_le_two
    (by simp) u.memL2 hball hr hεt (Eventually.of_forall hε0) (Eventually.of_forall hε1)
  have hlp' : Tendsto (fun n => eLpNorm (v n - u.toFun) 2 (volume.restrict R)) atTop (𝓝 0) := by
    refine hlp.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' hRm).2 (ae_of_all _ fun x hx => ?_)
    simp only [Pi.sub_apply, hvdef]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hR hρ hx hball hr
      (hε0 n) (hε1 n)]
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (by simp) hlp'
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  set Hc : ℝ := d * G with hHc
  have hHc0 : 0 ≤ Hc := by positivity
  set f : ℕ → Vec d → ℝ := fun k => v (ns k) with hfdef
  have hH : ∀ k, ∀ x y, x ∈ R → y ∈ R → |f k x - f k y| ≤ Hc * ‖x - y‖ := by
    intro k x y hx hy
    exact abs_convexApproxSmoothRepresentative_sub_le hR u hG0 hG hρ hball hr (hε0 (ns k))
      (hε1 (ns k)) hx hy
  set S : Set (Vec d) := {x | x ∈ R ∧ Tendsto (fun k => f k x) atTop (𝓝 (u.toFun x))} with hS
  have hSae : ∀ᵐ x ∂volume, x ∈ R → x ∈ S := by
    have := (ae_restrict_iff' hRm).1 hae
    filter_upwards [this] with x hx hxU
    exact ⟨hxU, hx hxU⟩
  have hdense : ∀ x, x ∈ R → ∀ η > 0, ∃ x' ∈ S, Hc * ‖x - x'‖ < η := by
    intro x hx η hη
    set δ' : ℝ := η / (Hc + 1) with hδ'
    have hδ'0 : 0 < δ' := by positivity
    by_contra hcon
    push Not at hcon
    have hsub : R ∩ Metric.ball x δ' ⊆ {y | ¬(y ∈ R → y ∈ S)} := by
      intro y hy hyS
      have := hcon y (hyS hy.1)
      have hlt : ‖x - y‖ < δ' := by
        rw [← dist_eq_norm]; exact Metric.mem_ball'.1 hy.2
      have h1 : Hc * ‖x - y‖ ≤ Hc * δ' := mul_le_mul_of_nonneg_left hlt.le hHc0
      have h2 : Hc * δ' < η := by
        rw [hδ', mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith only [hη, hHc0]
      linarith only [this, h1, h2]
    have hpos : 0 < volume (R ∩ Metric.ball x δ') :=
      (hR.isOpen.inter Metric.isOpen_ball).measure_pos volume ⟨x, hx, Metric.mem_ball_self hδ'0⟩
    have hnull : volume {y | ¬(y ∈ R → y ∈ S)} = 0 := ae_iff.1 hSae
    exact hpos.ne' (measure_mono_null hsub hnull)
  have hlim : ∀ x ∈ R, ∃ l, Tendsto (fun k => f k x) atTop (𝓝 l) := fun x hx =>
    exists_tendsto_of_dense (· ∈ R) S f (fun x y => Hc * ‖x - y‖) hH (fun x hx => hx.1)
      hdense (fun x hx => ⟨_, hx.2⟩) hx
  set ū : Vec d → ℝ := fun x => limUnder atTop (fun k => f k x) with hūdef
  have hū : ∀ x ∈ R, Tendsto (fun k => f k x) atTop (𝓝 (ū x)) := fun x hx =>
    tendsto_nhds_limUnder (hlim x hx)
  refine ⟨ū, ?_, fun x hx y hy => ?_⟩
  · refine (ae_restrict_iff' hRm).2 (hSae.mono fun x hx hxU => ?_)
    exact tendsto_nhds_unique (hū x hxU) (hx hxU).2
  · exact le_of_tendsto' ((hū x hx).sub (hū y hy)).abs fun k => hH k x y hx hy

end SuperdiffusionCLT.Section7
