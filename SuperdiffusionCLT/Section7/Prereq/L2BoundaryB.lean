/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2Boundary
public import SuperdiffusionCLT.Section7.Prereq.MollifiedFluxC
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-!
# The whole-space extension of `u` and the mollification error

The comparison function mollifies a
whole-space `H¹` function `ũ` that agrees with `u` away from the boundary.  Instead of an `H¹`
extension of the datum we use `ũ = ζ' u`, extended by zero, for the cutoff `ζ'` of margin `r / 4`:
it is an `H¹(ℝᵈ)` function, equal to `u` (value and gradient) where `r / 2 < dist(·, Wᶜ)`, and
the mollifier of radius `h ≤ r / 4` only sees that region from the points at distance `≥ r`.

## Main results

* `Section7.l2c_ext`: the extension `ũ` and its agreement with `u` in the interior.
* `Section7.l2c_sub_conv_ae`: the standard mollification estimate for a.e.-measurable data.
* `Section7.l2c_mollError`: `‖ũ - η_h ∗ ũ‖_{L²(V)} ≤ d h ‖∇u‖_{L²(W)}` for `V` at distance `≥ r`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {W : Set (Vec d)}

/-- **The whole-space extension** `ũ = ζ' u` (zero outside `W`), `ζ'` the cutoff of margin `r / 4`. -/
noncomputable def l2c_ext (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r)
    (u : H1Function W) : H1Function (Set.univ : Set (Vec d)) :=
  (H10Function.extendByZeroToOpenSuperset
    (mulLipH10 hW u (l2a_cutoff_lipschitz W (show 0 < r / 4 by positivity))
      (M := 1) (l2a_cutoff_abs_le W (r / 4)) (l2a_cutoff_compact hWb (show 0 < r / 4 by positivity)).1
      (l2a_cutoff_compact hWb (show 0 < r / 4 by positivity)).2)
    hW.measurableSet isOpen_univ (subset_univ _)).toH1Function

/-- `ũ = u` where `r / 2 ≤ dist(·, Wᶜ)`. -/
theorem l2c_ext_toFun (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r)
    (u : H1Function W) {x : Vec d} (hx : x ∈ W) (hd : r / 2 ≤ Metric.infDist x Wᶜ) :
    (l2c_ext hW hWb hr u).toFun x = u.toFun x := by
  have h1 : l2a_cutoff W (r / 4) x = 1 :=
    l2a_cutoff_eq_one (show 0 < r / 4 by positivity) (by linarith only [hd])
  simp [l2c_ext, H10Function.zeroExtension_apply_of_mem _ hx, h1]

/-- `∇ũ = ∇u` where `r / 2 < dist(·, Wᶜ)`. -/
theorem l2c_ext_grad (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r : ℝ} (hr : 0 < r)
    (u : H1Function W) {x : Vec d} (hx : x ∈ W) (hd : r / 2 < Metric.infDist x Wᶜ) :
    (l2c_ext hW hWb hr u).grad x = u.grad x := by
  have h1 : l2a_cutoff W (r / 4) x = 1 :=
    l2a_cutoff_eq_one (show 0 < r / 4 by positivity) (by linarith only [hd])
  have h2 : lipGradient (l2a_cutoff W (r / 4)) x = 0 :=
    l2a_lipGradient_cutoff_eq_zero W (show 0 < r / 4 by positivity) (Or.inr (by linarith only [hd]))
  simp [l2c_ext, H10Function.zeroExtensionGrad_apply_of_mem _ hx, h1, h2]

/-- **The mollification estimate for an `H¹(ℝᵈ)` function** (`m1_sub_conv_eLpNorm_le` without
the choice of measurable representatives):
`‖ψ - η_h ∗ ψ‖_{L^q(V)} ≤ √d h ‖∇ψ‖_{L^q(Wo)}` when the sup-balls of radius `h` around the points
of `V` lie in the open set `Wo`. -/
theorem l2c_sub_conv_ae {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    {Wo : Set (Vec d)} (hWo : IsOpen Wo) {V : Set (Vec d)} (hV : MeasurableSet V)
    (hVW : ∀ x ∈ V, ∀ y, dist y x ≤ h → y ∈ Wo) (ψ : H1Function (Set.univ : Set (Vec d)))
    {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun x => ψ.toFun x - l2a_moll d h η ψ.toFun x) (ENNReal.ofReal q) (volume.restrict V) ≤
      ENNReal.ofReal (Real.sqrt d * h) *
        eLpNorm (fun y => eucNorm (ψ.grad y)) (ENNReal.ofReal q) (volume.restrict Wo) := by
  have hψ2 : MemLp ψ.toFun 2 volume := by simpa [MemL2On, Measure.restrict_univ] using ψ.memL2
  have hg2 : ∀ i, MemLp (fun x => ψ.grad x i) 2 volume := fun i => by
    simpa [MemL2On, Measure.restrict_univ] using ψ.gradMemL2 i
  have hψl : LocallyIntegrable ψ.toFun volume := hψ2.locallyIntegrable (by norm_num)
  have hgl : ∀ i, LocallyIntegrable (fun x => ψ.grad x i) volume :=
    fun i => (hg2 i).locallyIntegrable (by norm_num)
  set ψm : Vec d → ℝ := hψ2.aestronglyMeasurable.mk ψ.toFun with hψm
  set gm : Fin d → Vec d → ℝ := fun i => (hg2 i).aestronglyMeasurable.mk (fun x => ψ.grad x i)
    with hgm
  have hψe : ψ.toFun =ᵐ[volume] ψm := hψ2.aestronglyMeasurable.ae_eq_mk
  have hge : ∀ i, (fun x => ψ.grad x i) =ᵐ[volume] gm i := fun i =>
    (hg2 i).aestronglyMeasurable.ae_eq_mk
  have hψm_meas : Measurable ψm := hψ2.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgm_meas : ∀ i, Measurable (gm i) := fun i =>
    (hg2 i).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hmoll : ∀ x, l2a_moll d h η ψm x = l2a_moll d h η ψ.toFun x := fun x => by
    unfold l2a_moll
    refine integral_congr_ae ?_
    filter_upwards [hψe] with y hy
    rw [hy]
  have hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Wo → ∫ x, ψm x * fderiv ℝ φ x (basisVec i) = -∫ x, gm i x * φ x := by
    intro i φ hφ hφc hφW
    have := ψ.hasWeakGradient i φ hφ hφc (subset_univ _)
    simp only [Measure.restrict_univ] at this
    have e1 : ∫ x, ψm x * fderiv ℝ φ x (basisVec i) = ∫ x, ψ.toFun x * fderiv ℝ φ x (basisVec i) :=
      integral_congr_ae (by filter_upwards [hψe] with y hy; rw [← hy])
    have e2 : ∫ x, gm i x * φ x = ∫ x, ψ.grad x i * φ x :=
      integral_congr_ae (by filter_upwards [hge i] with y hy; rw [← hy])
    rw [e1, e2]
    exact this
  have key := m1_sub_conv_eLpNorm_le hh hηc hη0 hη1 hηs hWo hV hVW hψm_meas
    (g := fun x i => gm i x) (fun i => hgm_meas i) (hψl.congr hψe)
    (fun i => (hgl i).congr (hge i)) hweak hq
  have hL : (fun x => ψ.toFun x - l2a_moll d h η ψ.toFun x) =ᵐ[volume.restrict V]
      fun x => ψm x - ∫ y, a16_kernel d h η (x - y) * ψm y := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hψe] with y hy
    rw [← hy]
    exact congrArg _ (hmoll y).symm
  have hR : (fun y => eucNorm (ψ.grad y)) =ᵐ[volume.restrict Wo]
      fun y => eucNorm ((fun x i => gm i x) y) := by
    refine ae_restrict_of_ae ?_
    have : ∀ᵐ y ∂volume, ∀ i, ψ.grad y i = gm i y := ae_all_iff.2 hge
    filter_upwards [this] with y hy
    exact congrArg eucNorm (funext hy)
  rw [eLpNorm_congr_ae hL, eLpNorm_congr_ae hR]
  exact key

/-- The Euclidean norm is at most `√d` times the sup norm. -/
theorem l2c_eucNorm_le (v : Vec d) : eucNorm v ≤ Real.sqrt d * ‖v‖ := by
  unfold eucNorm
  have h1 : vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    unfold vecNormSq vecDot
    calc ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := norm_le_pi_norm v i
          rw [Real.norm_eq_abs] at this
          calc v i * v i = |v i| * |v i| := by rw [← abs_mul_abs_self]
            _ ≤ ‖v‖ * ‖v‖ := by gcongr
            _ = ‖v‖ ^ 2 := by ring
      _ = (d : ℝ) * ‖v‖ ^ 2 := by simp
  calc Real.sqrt (vecNormSq v) ≤ Real.sqrt ((d : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt d * ‖v‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg v)]

end SuperdiffusionCLT.Section7
