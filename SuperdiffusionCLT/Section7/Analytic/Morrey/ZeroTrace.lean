/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Homogenization.Sobolev.W1p.GlobalMollifierLp
public import SuperdiffusionCLT.Section7.Prereq.Morrey
public import Homogenization.Sobolev.Foundations.AxisCube

@[expose] public section

open MeasureTheory Homogenization Convolution


/-!
# Morrey's inequality for zero-trace functions

For `U ⊆ axisCube z L` open and `φ ∈ H¹₀(U)`, `‖φ‖_{L^∞(U)} ≤ C(d,p) L^{1-d/p} ‖∇φ‖_{L^p(U)}`
whenever `p > d ≥ 1`.  The proof mollifies the zero extension, bounds the mollified gradient by the
mollified `L^p` majorant, applies the `C¹` Morrey inequality on an enlarged cube, and passes to an
almost-everywhere limit.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem hasFDerivAt_convolution_apply_basisVec {k f : Vec d → ℝ} (hk : ContDiff ℝ 1 k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume) (x v : Vec d) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x v =
      ∫ t, (fderiv ℝ k t v) * f (x - t) ∂volume := by
  have h := hkc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hf x
  rw [h.fderiv, convolution_def]
  have hce : ConvolutionExists (fderiv ℝ k) f
      (ContinuousLinearMap.precompL (Vec d) (ContinuousLinearMap.lsmul ℝ ℝ)) volume :=
    (hkc.fderiv ℝ).convolutionExists_left _ (hk.continuous_fderiv one_ne_zero) hf
  have hint := hce x
  rw [ContinuousLinearMap.integral_apply hint]
  simp

theorem fderiv_reflect_apply {k : Vec d → ℝ} (hk : ContDiff ℝ 1 k) (x s v : Vec d) :
    fderiv ℝ (fun y => k (x - y)) s v = - fderiv ℝ k (x - s) v := by
  have h3 : HasFDerivAt (fun y : Vec d => k (x - y)) ((fderiv ℝ k (x - s)).comp (-(ContinuousLinearMap.id ℝ (Vec d)))) s :=
    ((hk.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp s
      ((hasFDerivAt_id s).const_sub x)
  rw [h3.fderiv]
  simp

theorem fderiv_convolution_basisVec {k f gi : Vec d → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f volume) {i : Fin d}
    (hi : HasWeakPartialDerivOn Set.univ i f gi) (x : Vec d) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x (basisVec i) =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] gi) x := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  rw [hasFDerivAt_convolution_apply_basisVec hk1 hkc hf, convolution_def]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => k (x - y)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun y : Vec d => k (x - y)) :=
    hkc.comp_isClosedEmbedding (Homeomorph.subLeft x).isClosedEmbedding
  have hw := hi _ hφ hφc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at hw
  simp only [fderiv_reflect_apply hk1, mul_neg, integral_neg] at hw
  have e1 : ∫ t, (fderiv ℝ k t) (basisVec i) * f (x - t) ∂volume =
      ∫ s, (fderiv ℝ k (x - s)) (basisVec i) * f s ∂volume := by
    rw [← integral_sub_left_eq_self (fun s => (fderiv ℝ k (x - s)) (basisVec i) * f s) volume x]
    simp
  have e2 : ∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (k t) (gi (x - t)) ∂volume =
      ∫ s, gi s * k (x - s) ∂volume := by
    rw [← integral_sub_left_eq_self (fun s => gi s * k (x - s)) volume x]
    simp [mul_comm]
  rw [e1, e2]
  have : ∫ s, (fderiv ℝ k (x - s)) (basisVec i) * f s ∂volume =
      ∫ s, f s * (fderiv ℝ k (x - s)) (basisVec i) ∂volume := by
    congr 1; ext s; ring
  rw [this]
  linarith only [hw]

theorem norm_fderiv_convolution_le {k f : Vec d → ℝ} {Du : Vec d → Vec d}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k) (hk0 : ∀ y, 0 ≤ k y)
    (hf : LocallyIntegrable f volume) (hDu : HasWeakGradientOn Set.univ f Du)
    (hDuLoc : ∀ i, LocallyIntegrable (fun x => Du x i) volume)
    (hG : LocallyIntegrable (fun x => (d : ℝ) * ‖Du x‖) volume) (x : Vec d) :
    ‖fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖ ≤
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => (d : ℝ) * ‖Du y‖)) x := by
  have hkcont : Continuous k := hk.continuous
  have hGint : Integrable (fun t => k t * ((d : ℝ) * ‖Du (x - t)‖)) volume :=
    (hkc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hkcont hG) x
  have hRHS : (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => (d : ℝ) * ‖Du y‖)) x =
      ∫ t, k t * ((d : ℝ) * ‖Du (x - t)‖) ∂volume := by
    rw [convolution_def]; rfl
  have hnn : 0 ≤ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => (d : ℝ) * ‖Du y‖)) x := by
    rw [hRHS]
    exact integral_nonneg fun t => mul_nonneg (hk0 t) (by positivity)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun v => ?_
  have hdecomp : fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x v =
      ∫ t, k t * (∑ i, v i * Du (x - t) i) ∂volume := by
    have hv : v = ∑ i, v i • basisVec i := by
      ext j; simp [Finset.sum_apply, basisVec_apply]
    have hli : ∀ i, Integrable (fun t => k t * Du (x - t) i) volume := fun i =>
      (hkc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hkcont (hDuLoc i)) x
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [fderiv_convolution_basisVec hk hkc hf (hDu _), convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hli i).const_mul (v i))]
    congr 1; ext t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hpt : ∀ t, ‖k t * (∑ i, v i * Du (x - t) i)‖ ≤
      ‖v‖ * (k t * ((d : ℝ) * ‖Du (x - t)‖)) := by
    intro t
    rw [norm_mul, Real.norm_of_nonneg (hk0 t)]
    have hsum : ‖∑ i, v i * Du (x - t) i‖ ≤ ‖v‖ * ((d : ℝ) * ‖Du (x - t)‖) := by
      calc ‖∑ i, v i * Du (x - t) i‖ ≤ ∑ i, ‖v i * Du (x - t) i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin d, ‖v‖ * ‖Du (x - t)‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm (Du (x - t)) i)
            (norm_nonneg _) (norm_nonneg _)
        _ = ‖v‖ * ((d : ℝ) * ‖Du (x - t)‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc k t * ‖∑ i, v i * Du (x - t) i‖ ≤ k t * (‖v‖ * ((d : ℝ) * ‖Du (x - t)‖)) :=
          mul_le_mul_of_nonneg_left hsum (hk0 t)
      _ = _ := by ring
  rw [hdecomp, hRHS, Real.norm_eq_abs, mul_comm, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hGint.const_mul ‖v‖) (Filter.Eventually.of_forall hpt)

theorem toReal_volume_axisCube (w : Vec d) {M : ℝ} (hM : 0 < M) :
    (volume (axisCube w M)).toReal = M ^ d := by
  rw [axisCube, Real.volume_pi_Ioo]
  simp [ENNReal.toReal_ofReal hM.le]

theorem norm_sub_le_of_mem_axisCube (w : Vec d) {M : ℝ} (hM : 0 ≤ M) {a b : Vec d}
    (ha : a ∈ axisCube w M) (hb : b ∈ axisCube w M) : ‖a - b‖ ≤ M := by
  refine (pi_norm_le_iff_of_nonneg ?_).2 fun j => ?_
  · exact hM
  · have h1 := ha j (Set.mem_univ j)
    have h2 := hb j (Set.mem_univ j)
    simp only [Set.mem_Ioo] at h1 h2
    rw [Real.norm_eq_abs, Pi.sub_apply, abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

theorem abs_le_cube_morrey_of_vanish {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u) {w : Vec d} {M : ℝ}
    (hM : 0 < M) {p : ℝ} (hp1 : 1 < p) (hd : (d : ℝ) < p) {x y : Vec d}
    (hx : x ∈ axisCube w M) (hy : y ∈ axisCube w M) (huy : u y = 0) {H : Vec d → ℝ}
    (hH0 : ∀ z, 0 ≤ H z) (hH : ∀ z, ‖fderiv ℝ u z‖ ≤ H z)
    (hHint : Integrable (fun z => H z ^ p) volume) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∫ z, H z ^ p ∂volume ≤ Λ ^ p) :
    |u x| ≤ 2 * (1 / (1 - (d : ℝ) / p)) * M ^ (1 - (d : ℝ) / p) * Λ := by
  have hp0 : 0 < p := by linarith only [hp1]
  have hvol : volume (axisCube w M) ≠ 0 := by
    intro h
    have := toReal_volume_axisCube w hM
    rw [h, ENNReal.toReal_zero] at this
    exact (pow_pos hM d).ne this
  have hmor := abs_sub_le_morrey (volume : Measure (Vec d)) hu (isOpen_axisCube w M).measurableSet
    (convex_axisCube w M) (Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _) hvol
    (fun a ha b hb => norm_sub_le_of_mem_axisCube w hM.le ha hb) (p := p) hp1
    (by simpa [Module.finrank_fin_fun] using hd) hx hy
  rw [huy, sub_zero] at hmor
  simp only [Module.finrank_fin_fun] at hmor
  rw [toReal_volume_axisCube w hM] at hmor
  have hI : ∫ z in axisCube w M, ‖fderiv ℝ u z‖ ^ p ∂volume ≤ Λ ^ p := by
    refine le_trans ?_ hΛ
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
      hHint.integrableOn (Filter.Eventually.of_forall fun z =>
        Real.rpow_le_rpow (norm_nonneg _) (hH z) hp0.le)) ?_
    exact setIntegral_le_integral hHint (Filter.Eventually.of_forall fun z =>
      Real.rpow_nonneg (hH0 z) _)
  have hI0 : 0 ≤ ∫ z in axisCube w M, ‖fderiv ℝ u z‖ ^ p ∂volume :=
    integral_nonneg fun z => by positivity
  have hMd : (0 : ℝ) < (M ^ d)⁻¹ := inv_pos.2 (pow_pos hM d)
  have hT : ((M ^ d)⁻¹ * ∫ z in axisCube w M, ‖fderiv ℝ u z‖ ^ p ∂volume) ^ (1 / p) ≤
      M ^ (-((d : ℝ) / p)) * Λ := by
    calc _ ≤ ((M ^ d)⁻¹ * Λ ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (mul_nonneg hMd.le hI0) (mul_le_mul_of_nonneg_left hI hMd.le)
            (by positivity)
      _ = M ^ (-((d : ℝ) / p)) * Λ := by
          rw [Real.mul_rpow hMd.le (by positivity), ← Real.rpow_mul hΛ0, mul_one_div_cancel hp0.ne',
            Real.rpow_one, ← Real.rpow_natCast, Real.inv_rpow (by positivity),
            ← Real.rpow_mul hM.le, ← Real.rpow_neg (by positivity)]
          congr 2; ring
  have hMM : M * M ^ (-((d : ℝ) / p)) = M ^ (1 - (d : ℝ) / p) := by
    rw [sub_eq_add_neg, Real.rpow_add hM, Real.rpow_one]
  have hc : 0 ≤ 2 * (1 / (1 - (d : ℝ) / p)) := by
    have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hd
    have : 0 < 1 - (d : ℝ) / p := by linarith only [this]
    positivity
  calc |u x| ≤ _ := hmor
    _ ≤ 2 * (1 / (1 - (d : ℝ) / p)) * M * (M ^ (-((d : ℝ) / p)) * Λ) :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg hc hM.le)
    _ = 2 * (1 / (1 - (d : ℝ) / p)) * M ^ (1 - (d : ℝ) / p) * Λ := by
        rw [← hMM]; ring

theorem scaledKernel_ne_zero_norm_le {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) {a : ℝ}
    (ha : 0 < a) {t : Vec d} (ht : scaledConvexApproxKernel ρ a t ≠ 0) : ‖t‖ ≤ a := by
  have h1 : ρ (a⁻¹ • t) ≠ 0 := fun h => ht (by simp [scaledConvexApproxKernel, h])
  have h2 := hρ.support_subset_closedBall (subset_tsupport ρ h1)
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos ha] at h2
  have := mul_le_mul_of_nonneg_left h2 ha.le
  rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, mul_one] at this

theorem convolution_eq_zero_of_far {k u0 : Vec d → ℝ} {a : ℝ} {y : Vec d}
    (hk : ∀ t, k t ≠ 0 → ‖t‖ ≤ a) (hu : ∀ t, ‖t‖ ≤ a → u0 (y - t) = 0) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u0) y = 0 := by
  rw [convolution_def]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases h : k t = 0
  · simp [h]
  · simp [hu t (hk t h)]

theorem integral_rpow_le_of_eLpNorm_le {H : Vec d → ℝ} {p : ℝ} (hp : 0 < p)
    (hH : MemLp H (ENNReal.ofReal p) volume) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (h : eLpNorm H (ENNReal.ofReal p) volume ≤ ENNReal.ofReal Λ) :
    Integrable (fun z => ‖H z‖ ^ p) volume ∧ ∫ z, ‖H z‖ ^ p ∂volume ≤ Λ ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  refine ⟨?_, ?_⟩
  · simpa [hpr] using hH.integrable_norm_rpow hp0 hpt
  · rw [hH.eLpNorm_eq_integral_rpow_norm hp0 hpt, hpr] at h
    have h2 := (ENNReal.ofReal_le_ofReal_iff hΛ0).1 h
    have h3 := Real.rpow_le_rpow (by positivity) h2 hp.le
    rwa [← Real.rpow_mul (integral_nonneg fun z => by positivity), inv_mul_cancel₀ hp.ne',
      Real.rpow_one] at h3

theorem abs_mollify_le (hd0 : 0 < d) {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) {a : ℝ}
    (ha : 0 < a) {z : Vec d} {L : ℝ} (hL : 0 < L) (haL : a ≤ L / 4)
    {u0 : Vec d → ℝ} {Du : Vec d → Vec d} (hu0 : MemLp u0 2 volume)
    (hDu : ∀ i, MemLp (fun x => Du x i) 2 volume) (hw : HasWeakGradientOn Set.univ u0 Du)
    (hsupp : ∀ x, x ∉ axisCube z L → u0 x = 0) {p : ℝ} (hp : (d : ℝ) < p)
    (hG : MemLp (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume)
    {x : Vec d} (hx : x ∈ axisCube (z - fun _ => L / 2) (2 * L)) :
    |(scaledConvexApproxKernel ρ a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u0) x| ≤
      2 * (1 / (1 - (d : ℝ) / p)) * (2 * L) ^ (1 - (d : ℝ) / p) *
        (eLpNorm (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume).toReal := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hp1 : 1 < p := by linarith only [hd1, hp]
  have hp0 : 0 < p := by linarith only [hp1]
  set k := scaledConvexApproxKernel ρ a with hkdef
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := contDiff_scaledConvexApproxKernel hρ a
  have hkc : HasCompactSupport k := hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
  have hk0 : ∀ y, 0 ≤ k y := scaledConvexApproxKernel_nonneg hρ ha
  have hu0loc : LocallyIntegrable u0 volume := hu0.locallyIntegrable (by norm_num)
  have hDuLoc : ∀ i, LocallyIntegrable (fun x => Du x i) volume := fun i =>
    (hDu i).locallyIntegrable (by norm_num)
  have hp1' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp1.le
  have hGloc : LocallyIntegrable (fun x => (d : ℝ) * ‖Du x‖) volume := hG.locallyIntegrable hp1'
  have hu : ContDiff ℝ 1 (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u0) :=
    (HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hkc hk
      hu0loc).of_le (by exact_mod_cast le_top)
  set H := k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => (d : ℝ) * ‖Du y‖) with hH
  have hHc : Continuous H :=
    (HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hkc hk
      hGloc).continuous
  have hH0 : ∀ z, 0 ≤ H z := fun z' => by
    rw [hH, convolution_def]
    exact integral_nonneg fun t => mul_nonneg (hk0 t) (by positivity)
  have hyoung : eLpNorm H (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume :=
    young_convolution_nonneg_integral_one_of_aemeasurable hp1' ENNReal.ofReal_ne_top hk0
      (integrable_scaledConvexApproxKernel hρ ha) (integral_scaledConvexApproxKernel hρ ha)
      (measurable_scaledConvexApproxKernel hρ.continuous a) hG.aestronglyMeasurable.aemeasurable
  have hHmem : MemLp H (ENNReal.ofReal p) volume :=
    lt_of_le_of_lt hyoung hG
  have hΛ0 : 0 ≤ (eLpNorm (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume).toReal :=
    ENNReal.toReal_nonneg
  obtain ⟨hHint, hHle⟩ := integral_rpow_le_of_eLpNorm_le hp0 hHmem hΛ0
    (by rw [ENNReal.ofReal_toReal hG.ne]; exact hyoung)
  have hHnorm : ∀ z, ‖H z‖ = H z := fun z => Real.norm_of_nonneg (hH0 z)
  simp only [hHnorm] at hHint hHle
  have hy : (z - fun _ => 3 * L / 8) ∈ axisCube (z - fun _ => L / 2) (2 * L) := by
    intro j _
    simp only [Pi.sub_apply, Set.mem_Ioo]
    constructor <;> linarith only [hL]
  have hy0 : (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u0) (z - fun _ => 3 * L / 8) = 0 := by
    refine convolution_eq_zero_of_far (a := a) (fun t ht => scaledKernel_ne_zero_norm_le hρ ha ht)
      fun t ht => hsupp _ fun hmem => ?_
    have h1 := hmem ⟨0, hd0⟩ (Set.mem_univ _)
    have h2 := (abs_le.1 ((norm_le_pi_norm t ⟨0, hd0⟩).trans ht)).1
    simp only [Set.mem_Ioo, Pi.sub_apply] at h1
    linarith only [h1.1, h2, haL, hL]
  exact abs_le_cube_morrey_of_vanish hu (by linarith only [hL]) hp1 hp hx hy hy0 hH0
    (norm_fderiv_convolution_le hk hkc hk0 hu0loc hw hDuLoc hGloc) hHint hΛ0 hHle

end SuperdiffusionCLT.Section7
