/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import Homogenization.Sobolev.W1p.BasicLemmas
public import Homogenization.Sobolev.Foundations.AxisCube

@[expose] public section

open MeasureTheory Homogenization

/-!
# `L^p` bound for the gradient of the convex smoothing

For a `W^{1,p}` function `u` on an axis cube `U` and the smooth representative `v` of its convex
smoothing, `‖∇v‖_{L^p(U)} ≤ d ‖∇u‖_{L^p(U)}`, uniformly in the smoothing parameter.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The operator norm of a linear functional on `ℝ^d` (sup norm) is at most the sum of its values
on the basis vectors. -/
theorem norm_le_sum_basisVec (A : Vec d →L[ℝ] ℝ) : ‖A‖ ≤ ∑ i, |A (basisVec i)| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun w => ?_
  have hw : w = ∑ i, w i • basisVec i := by
    funext j
    simp [Finset.sum_apply, basisVec, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum, Finset.sum_mul]
  refine (Real.norm_eq_abs _ ▸ Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w i)
    (abs_nonneg _)

theorem locallyIntegrableOn_of_memLpOn {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {p : ENNReal} (hp1 : 1 ≤ p) {u : Vec d → ℝ} (hu : MemLpOn U p u) :
    LocallyIntegrableOn u U volume := by
  have := hU.isFiniteMeasure_restrict_volume
  exact IntegrableOn.locallyIntegrableOn (show IntegrableOn u U volume from hu.integrable hp1)

theorem smoothing_constant_le_one {p : ℝ} (hp1 : 1 < p) (hd : (d : ℝ) < p) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ENNReal.ofReal (1 - ε) * ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^ (1 / ENNReal.ofReal p).toReal ≤ 1 := by
  have hp0 : 0 < p := by linarith only [hp1]
  have ht : 0 < 1 - ε := by linarith only [hε1]
  have hexp : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le, one_div]
  rw [hexp, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := 1 - ε with htdef
  have ht1 : t ≤ 1 := by linarith only [hε0]
  have hdp : (d : ℝ) * (1 / p) ≤ 1 := by
    rw [← mul_div_assoc, mul_one]
    exact (div_le_one hp0).2 hd.le
  have hinv1 : 1 ≤ t⁻¹ := one_le_inv_iff₀.2 ⟨ht, ht1⟩
  have h1 : ((t ^ d)⁻¹) ^ (1 / p) ≤ t⁻¹ := by
    rw [← inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    calc (t⁻¹) ^ ((d : ℝ) * (1 / p)) ≤ (t⁻¹) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hinv1 hdp
      _ = t⁻¹ := Real.rpow_one _
  calc t * ((t ^ d)⁻¹) ^ (1 / p) ≤ t * t⁻¹ := mul_le_mul_of_nonneg_left h1 ht.le
    _ = 1 := mul_inv_cancel₀ ht.ne'

/-- The `L^p` norm of the gradient of the smooth representative is controlled by `d` times the
`L^p` norm of the weak gradient. -/
theorem eLpNorm_fderiv_convexApproxSmoothRepresentative_le {z : Vec d} {L : ℝ} {p : ℝ}
    (hp1 : 1 < p) (hd : (d : ℝ) < p)
    (u : W1pFunction (axisCube z L) (ENNReal.ofReal p)) {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ axisCube z L) (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε < 1) :
    eLpNorm (fun w => ‖fderiv ℝ (convexApproxSmoothRepresentative (axisCube z L)
        unitConvexApproxKernel u.toFun x0 r ε) w‖) (ENNReal.ofReal p)
        (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal d * eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p)
        (volume.restrict (axisCube z L)) := by
  have hp0 : 0 < p := by linarith only [hp1]
  have hU := isOpenBoundedConvexDomain_axisCube z L
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp1' : 1 ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp1.le)
  set ρ : Vec d → ℝ := unitConvexApproxKernel with hρdef
  have huLoc := locallyIntegrableOn_of_memLpOn hU hp1' u.memLp
  have hDuLoc : ∀ i : Fin d, LocallyIntegrableOn (fun x => u.grad x i) (axisCube z L) volume :=
    fun i => locallyIntegrableOn_of_memLpOn hU hp1' (u.gradMemLp i)
  have hvS : ContDiff ℝ (⊤ : ℕ∞) (convexApproxSmoothRepresentative (axisCube z L) ρ u.toFun x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hρ hp1' u.memLp hr hε0
  have hv1 : ContDiff ℝ 1 (convexApproxSmoothRepresentative (axisCube z L) ρ u.toFun x0 r ε) :=
    hvS.of_le (by exact_mod_cast le_top)
  have hweak := HasWeakGradientOn.convexApproxSmoothRepresentative hU huLoc hDuLoc
    u.hasWeakGradient hρ hball hr hε0 hε1
  have hclass := HasWeakGradientOn.of_contDiff (U := axisCube z L) hv1
  set v := convexApproxSmoothRepresentative (axisCube z L) ρ u.toFun x0 r ε with hvdef
  set w : Fin d → Vec d → ℝ := fun i =>
    convexApproxSmoothRepresentative (axisCube z L) ρ (fun y => u.grad y i) x0 r ε with hwdef
  have hwS : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i) := fun i =>
    contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hρ hp1' (u.gradMemLp i) hr hε0
  have hae : ∀ i, (fun x => fderiv ℝ v x (basisVec i)) =ᵐ[volume.restrict (axisCube z L)]
      fun x => (1 - ε) * w i x := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU.isOpen ?_ ?_ (hclass i) (hweak i)
    · exact ((hv1.continuous_fderiv one_ne_zero).clm_apply continuous_const).locallyIntegrable.locallyIntegrableOn (axisCube z L)
    · exact (continuous_const.mul (hwS i).continuous).locallyIntegrable.locallyIntegrableOn (axisCube z L)
  have hall : ∀ᵐ x ∂(volume.restrict (axisCube z L)), ∀ i, fderiv ℝ v x (basisVec i) = (1 - ε) * w i x :=
    ae_all_iff.2 hae
  have hpt : (fun x => ‖fderiv ℝ v x‖) ≤ᵐ[volume.restrict (axisCube z L)]
      ∑ i, fun x => ‖(1 - ε) * w i x‖ := by
    filter_upwards [hall] with x hx
    rw [Finset.sum_apply]
    refine (norm_le_sum_basisVec _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => by rw [hx i, Real.norm_eq_abs]
  have ht : 0 < 1 - ε := by linarith only [hε1]
  set G := eLpNorm (fun w => ‖u.grad w‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) with hG
  have hi : ∀ i, eLpNorm (fun x => ‖(1 - ε) * w i x‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) ≤ G := by
    intro i
    have hsm : w i =ᵐ[volume.restrict (axisCube z L)]
        convexApproxSmoothing ρ (fun y => u.grad y i) x0 r ε := by
      refine (ae_restrict_iff' hU.isOpen.measurableSet).2 (ae_of_all _ fun x hx => ?_)
      exact convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := fun y => u.grad y i) hU hρ hx hball hr hε0 hε1
    have hDu : eLpNorm (fun x => u.grad x i) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) ≤ G :=
      eLpNorm_mono_ae (u.gradMemLp i).aestronglyMeasurable (ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (u.grad x) i)
    have hsmooth := eLpNorm_convexApproxSmoothing_le hU hρ hp1' hpT (u.gradMemLp i) hball hr
      hε0 hε1
    calc eLpNorm (fun x => ‖(1 - ε) * w i x‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L))
        = eLpNorm ((1 - ε) • w i) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) :=
          eLpNorm_norm _ (continuous_const.mul (hwS i).continuous).aestronglyMeasurable
      _ = ENNReal.ofReal (1 - ε) * eLpNorm (w i) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal ht.le]
      _ ≤ ENNReal.ofReal (1 - ε) * (ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / ENNReal.ofReal p).toReal * G) := by
          rw [eLpNorm_congr_ae hsm]
          gcongr
          exact hsmooth.trans (by gcongr)
      _ = (ENNReal.ofReal (1 - ε) * ENNReal.ofReal (((1 - ε) ^ d)⁻¹) ^
            (1 / ENNReal.ofReal p).toReal) * G := by rw [mul_assoc]
      _ ≤ 1 * G := by gcongr; exact smoothing_constant_le_one hp1 hd hε0 hε1
      _ = G := one_mul _
  have key : eLpNorm (fun w => ‖fderiv ℝ v w‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) ≤
      ENNReal.ofReal d * G := by
   calc eLpNorm (fun w => ‖fderiv ℝ v w‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L))
      ≤ eLpNorm (∑ i, fun x => ‖(1 - ε) * w i x‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) :=
        eLpNorm_mono_ae (hv1.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
          (hpt.mono fun x hx => by
          have hnn : 0 ≤ (∑ i, fun x => ‖(1 - ε) * w i x‖) x := by
            rw [Finset.sum_apply]
            exact Finset.sum_nonneg fun i _ => norm_nonneg _
          rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hnn]
          exact hx)
    _ ≤ ∑ i, eLpNorm (fun x => ‖(1 - ε) * w i x‖) (ENNReal.ofReal p) (volume.restrict (axisCube z L)) :=
        eLpNorm_sum_le hp1'
    _ ≤ ∑ _i : Fin d, G := Finset.sum_le_sum fun i _ => hi i
    _ = ENNReal.ofReal d * G := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_natCast]
  exact key

end SuperdiffusionCLT.Section7
