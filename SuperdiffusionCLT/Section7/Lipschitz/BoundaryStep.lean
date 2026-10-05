/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryApproxC
public import SuperdiffusionCLT.Section7.Lipschitz.PatchDecay
public import SuperdiffusionCLT.Section7.Lipschitz.Localize
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import Mathlib.Order.CompletePartialOrder

/-!
# The boundary one-step inequality: calculus

The Taylor estimate and the vector of partial derivatives of a smooth function, the weak equation
of the difference of the homogenized solution and the mollified datum, the change of
normalization between the cube of side `ℓ` and the normalized norms of a set, and the arithmetic
that closes the one-step inequality.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_bdry_step_clm_apply (L : Vec d →L[ℝ] ℝ) (v : Vec d) :
    L v = vecDot v (fun i => L (basisVec i)) := by
  have hdecomp : v = ∑ i : Fin d, v i • basisVec i := by
    funext j
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  calc L v = L (∑ i : Fin d, v i • basisVec i) := by rw [← hdecomp]
    _ = ∑ i : Fin d, v i * L (basisVec i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    _ = _ := rfl

theorem lip_bdry_step_norm_basisVec_le (i : Fin d) : ‖(basisVec i : Vec d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp [basisVec]
  · simp [basisVec, h]

theorem lip_bdry_step_grad_norm_le (L : Vec d →L[ℝ] ℝ) : ‖(fun i => L (basisVec i))‖ ≤ ‖L‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  calc ‖L (basisVec i)‖ ≤ ‖L‖ * ‖(basisVec i : Vec d)‖ := L.le_opNorm _
    _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left (lip_bdry_step_norm_basisVec_le i) (norm_nonneg _)
    _ = ‖L‖ := mul_one _

/-- Taylor estimate of the first order for a smooth function with bounded second derivative. -/
theorem lip_bdry_step_taylor {gt : Vec d → ℝ} (hgt : ContDiff ℝ 2 gt) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ M) (x₀ y : Vec d) :
    |gt y - gt x₀ - vecDot (fun i => fderiv ℝ gt x₀ (basisVec i)) (y - x₀)| ≤
      M * ‖y - x₀‖ * ‖y - x₀‖ := by
  have hd1 : Differentiable ℝ (fderiv ℝ gt) :=
    (hgt.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hd0 : Differentiable ℝ gt := hgt.differentiable (by norm_num)
  set r : ℝ := ‖y - x₀‖ with hr
  have hlip : ∀ x ∈ Metric.closedBall x₀ r, ‖fderiv ℝ gt x - fderiv ℝ gt x₀‖ ≤ M * r := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ gt) (s := Set.univ)
      (fun z _ => hd1 z) (fun z _ => hM z) convex_univ (Set.mem_univ x₀) (Set.mem_univ x)
    have hxr : ‖x - x₀‖ ≤ r := by simpa [dist_eq_norm] using hx
    calc ‖fderiv ℝ gt x - fderiv ℝ gt x₀‖ ≤ M * ‖x - x₀‖ := this
      _ ≤ M * r := by
        have hM0 : 0 ≤ M := (norm_nonneg (fderiv ℝ (fderiv ℝ gt) x₀)).trans (hM x₀)
        exact mul_le_mul_of_nonneg_left hxr hM0
  set L : Vec d →L[ℝ] ℝ := fderiv ℝ gt x₀ with hL
  have hh : ∀ x ∈ Metric.closedBall x₀ r,
      HasFDerivWithinAt (fun x => gt x - L x) (fderiv ℝ gt x - L) (Metric.closedBall x₀ r) x := by
    intro x _
    exact ((hd0 x).hasFDerivAt.sub L.hasFDerivAt).hasFDerivWithinAt
  have hr0 : 0 ≤ r := norm_nonneg _
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun x => gt x - L x)
    (s := Metric.closedBall x₀ r) (C := M * r) hh (fun x hx => hlip x hx) (convex_closedBall _ _)
    (x := x₀) (y := y) (Metric.mem_closedBall_self hr0) (by simp [hr, dist_eq_norm])
  have e : gt y - L y - (gt x₀ - L x₀) = gt y - gt x₀ - vecDot (fun i => L (basisVec i)) (y - x₀) := by
    have hv := lip_bdry_step_clm_apply L (y - x₀)
    rw [map_sub, vecDot_comm] at hv
    linarith only [hv]
  rw [Real.norm_eq_abs, e] at key
  exact key

theorem lip_bdry_step_integrable_mul {V : Set (Vec d)} (hVt : volume V ≠ ⊤) {h θ : Vec d → ℝ}
    (hh : AEStronglyMeasurable h (volume.restrict V)) {B : ℝ}
    (hB : ∀ᵐ x ∂volume.restrict V, |h x| ≤ B) (hθ : MemLp θ 2 (volume.restrict V)) :
    IntegrableOn (fun x => h x * θ x) V := by
  have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVt.lt_top⟩
  have hθ1 : Integrable θ (volume.restrict V) := hθ.integrable (by norm_num)
  refine Integrable.bdd_mul (c := B) hθ1 hh ?_
  filter_upwards [hB] with x hx
  rwa [Real.norm_eq_abs]

theorem lip_bdry_step_cont_bound {V : Set (Vec d)} (hVb : IsBoundedDomain V) {h : Vec d → ℝ}
    (hh : Continuous h) : ∃ B : ℝ, ∀ x ∈ V, |h x| ≤ B := by
  obtain ⟨R, hR, hV⟩ := hVb
  have hsub : V ⊆ Metric.closedBall (0 : Vec d) R := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg hR.le).2 fun i => by simpa using hV x hx i
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Vec d) R).exists_bound_of_continuousOn hh.continuousOn
  exact ⟨B, fun x hx => by simpa [Real.norm_eq_abs] using hB x (hsub hx)⟩

theorem lip_bdry_step_lap_le {gt : Vec d → ℝ} (hgt : ContDiff ℝ (⊤ : ℕ∞) gt) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ M) (x : Vec d) :
    |∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)| ≤ (d : ℝ) * M := by
  have hd1 : Differentiable ℝ (fderiv ℝ gt) :=
    (hgt.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)
  have hterm : ∀ i : Fin d, |fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)| ≤ M := by
    intro i
    have e : fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x =
        (fderiv ℝ (fderiv ℝ gt) x).flip (basisVec i) := by
      rw [fderiv_clm_apply (hd1 x) (differentiableAt_const _)]
      simp
    rw [e]
    simp only [ContinuousLinearMap.flip_apply]
    have h1 := ((fderiv ℝ (fderiv ℝ gt) x) (basisVec i)).le_opNorm (basisVec i)
    have h2 := (fderiv ℝ (fderiv ℝ gt) x).le_opNorm (basisVec i)
    have hb := lip_bdry_step_norm_basisVec_le (d := d) i
    have hn0 : 0 ≤ ‖fderiv ℝ (fderiv ℝ gt) x‖ := norm_nonneg (fderiv ℝ (fderiv ℝ gt) x)
    rw [← Real.norm_eq_abs]
    calc ‖((fderiv ℝ (fderiv ℝ gt) x) (basisVec i)) (basisVec i)‖
        ≤ ‖(fderiv ℝ (fderiv ℝ gt) x) (basisVec i)‖ * ‖(basisVec i : Vec d)‖ := h1
      _ ≤ (‖fderiv ℝ (fderiv ℝ gt) x‖ * ‖(basisVec i : Vec d)‖) * ‖(basisVec i : Vec d)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ M := by
        have hM' := hM x
        have : ‖(basisVec i : Vec d)‖ * ‖(basisVec i : Vec d)‖ ≤ 1 := by
          calc _ ≤ 1 * 1 := mul_le_mul hb hb (norm_nonneg _) zero_le_one
            _ = 1 := one_mul _
        calc (‖fderiv ℝ (fderiv ℝ gt) x‖ * ‖(basisVec i : Vec d)‖) * ‖(basisVec i : Vec d)‖
            = ‖fderiv ℝ (fderiv ℝ gt) x‖ * (‖(basisVec i : Vec d)‖ * ‖(basisVec i : Vec d)‖) := by ring
          _ ≤ ‖fderiv ℝ (fderiv ℝ gt) x‖ * 1 := mul_le_mul_of_nonneg_left this hn0
          _ ≤ M := by linarith only [hM']
  calc |∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)|
      ≤ ∑ i, |fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * M := by simp

theorem lip_bdry_step_phi [NeZero d] {V : Set (Vec d)} (hVo : IsOpen V) (hVb : IsBoundedDomain V)
    (hVt : volume V ≠ ⊤) {s : ℝ} (hs : 0 < s) {f' : Vec d → ℝ}
    (hfm : AEStronglyMeasurable f' (volume.restrict V)) {F : ℝ}
    (hF : ∀ᵐ x ∂volume.restrict V, |f' x| ≤ F) (ub : H1Function V)
    (hub : IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f' (fun _ => 0))
    {gt : Vec d → ℝ} (hgt : ContDiff ℝ (⊤ : ℕ∞) gt) :
    ∃ φ : H1Function V, (∀ x, φ.toFun x = ub.toFun x - gt x) ∧
      MemScalarL2 V (fun x => s⁻¹ * f' x +
        ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)) ∧
      IsWeakSolutionOn (fun _ => (1 : Mat d)) V φ
        (fun x => s⁻¹ * f' x +
          ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)) (fun _ => 0) := by
  classical
  have hSob : IsSobolevRegularDomain V := ⟨hVo.measurableSet, hVb⟩
  have hgt1 : ContDiff ℝ 1 gt := hgt.of_le (by simp)
  let gV : H1Function V := H1Function.ofContDiffOnIsSobolevRegularDomain hSob hgt1
  let Dfun : Fin d → Vec d → ℝ := fun i y => fderiv ℝ gt y (basisVec i)
  have hD2 : ∀ i, ContDiff ℝ 2 (Dfun i) := fun i =>
    (hgt.fderiv_right (m := 2) (by simp)).clm_apply contDiff_const
  let wD : Fin d → H1Function V := fun i =>
    H1Function.ofContDiffOnIsSobolevRegularDomain hSob ((hD2 i).of_le (by norm_num))
  let lapf : Vec d → ℝ := fun x => ∑ i, fderiv ℝ (Dfun i) x (basisVec i)
  have hlapc : Continuous lapf := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hD2 i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨Bl, hBl⟩ := lip_bdry_step_cont_bound hVb hlapc
  have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVt.lt_top⟩
  have hmeas : AEStronglyMeasurable (fun x => s⁻¹ * f' x + lapf x) (volume.restrict V) :=
    (hfm.const_mul _).add hlapc.aestronglyMeasurable
  have hbd : ∀ᵐ x ∂volume.restrict V, |s⁻¹ * f' x + lapf x| ≤ s⁻¹ * |F| + Bl := by
    filter_upwards [hF, ae_restrict_mem hVo.measurableSet] with x hx hxV
    have h1 : |s⁻¹ * f' x| ≤ s⁻¹ * |F| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hs)]
      exact mul_le_mul_of_nonneg_left (hx.trans (le_abs_self F)) (inv_nonneg.2 hs.le)
    calc |s⁻¹ * f' x + lapf x| ≤ |s⁻¹ * f' x| + |lapf x| := abs_add_le _ _
      _ ≤ s⁻¹ * |F| + Bl := add_le_add h1 (hBl x hxV)
  have hL2 : MemLp (fun x => s⁻¹ * f' x + lapf x) 2 (volume.restrict V) :=
    MemLp.of_bound hmeas (s⁻¹ * |F| + Bl) (hbd.mono fun x hx => by rwa [Real.norm_eq_abs])
  refine ⟨ub - gV, fun x => by simp [gV, H1Function.ofContDiffOnIsSobolevRegularDomain], hL2, ?_⟩
  intro θ
  have hθ2 : MemLp θ.toH1Function.toFun 2 (volume.restrict V) := θ.toH1Function.memL2
  have hθg : ∀ i, MemLp (fun x => θ.toH1Function.grad x i) 2 (volume.restrict V) :=
    fun i => θ.toH1Function.gradMemL2 i
  have hi1 : IntegrableOn (fun x => vecDot (ub.grad x) (θ.toH1Function.grad x)) V :=
    integrableOn_vecDot_of_memVectorL2 ub.grad_memVectorL2 θ.toH1Function.grad_memVectorL2
  have hi2 : IntegrableOn (fun x => vecDot (gV.grad x) (θ.toH1Function.grad x)) V :=
    integrableOn_vecDot_of_memVectorL2 gV.grad_memVectorL2 θ.toH1Function.grad_memVectorL2
  have e1 := hub θ
  simp only [lip_int_harm_of_l2_matVecMul_smul_one, vecDot_smul_left, vecDot_zero_left,
    integral_zero, add_zero, matVecMul_one, integral_const_mul] at e1 ⊢
  -- the gradient of `gt` against the test function
  have hDi : ∀ i, IntegrableOn (fun x => Dfun i x * θ.toH1Function.grad x i) V := fun i => by
    obtain ⟨B, hB⟩ := lip_bdry_step_cont_bound hVb ((hD2 i).continuous)
    exact lip_bdry_step_integrable_mul hVt (hD2 i).continuous.aestronglyMeasurable
      ((ae_restrict_iff' hVo.measurableSet).2 (Filter.Eventually.of_forall hB)) (hθg i)
  have hLi : ∀ i, IntegrableOn (fun x => fderiv ℝ (Dfun i) x (basisVec i) *
      θ.toH1Function.toFun x) V := fun i => by
    have hc : Continuous (fun x => fderiv ℝ (Dfun i) x (basisVec i)) :=
      ((hD2 i).continuous_fderiv (by norm_num)).clm_apply continuous_const
    obtain ⟨B, hB⟩ := lip_bdry_step_cont_bound hVb hc
    exact lip_bdry_step_integrable_mul hVt hc.aestronglyMeasurable
      ((ae_restrict_iff' hVo.measurableSet).2 (Filter.Eventually.of_forall hB)) hθ2
  have e2 : ∫ x in V, vecDot (gV.grad x) (θ.toH1Function.grad x) =
      -∫ x in V, lapf x * θ.toH1Function.toFun x := by
    have h1 : ∀ x, vecDot (gV.grad x) (θ.toH1Function.grad x) =
        ∑ i, Dfun i x * θ.toH1Function.grad x i := fun x => rfl
    have h2 : ∀ x, lapf x * θ.toH1Function.toFun x =
        ∑ i, fderiv ℝ (Dfun i) x (basisVec i) * θ.toH1Function.toFun x := fun x => by
      simp only [lapf, Finset.sum_mul]
    simp_rw [h1, h2]
    rw [integral_finsetSum _ (fun i _ => hDi i), integral_finsetSum _ (fun i _ => hLi i),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := rc_ibp (wD i) θ i
    have e3 : ∀ x, (wD i).grad x i = fderiv ℝ (Dfun i) x (basisVec i) := fun x => rfl
    have e4 : ∀ x, (wD i).toFun x = Dfun i x := fun x => rfl
    simp only [e3, e4] at this
    rw [this, neg_neg]
  have e5 : ∫ x in V, vecDot (ub.grad x - gV.grad x) (θ.toH1Function.grad x) =
      (∫ x in V, vecDot (ub.grad x) (θ.toH1Function.grad x)) -
        ∫ x in V, vecDot (gV.grad x) (θ.toH1Function.grad x) := by
    rw [← integral_sub hi1 hi2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show vecDot (ub.grad x - gV.grad x) (θ.toH1Function.grad x) = _
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  have hfθ : IntegrableOn (fun x => f' x * θ.toH1Function.toFun x) V :=
    lip_bdry_step_integrable_mul hVt hfm hF hθ2
  have hlθ : IntegrableOn (fun x => lapf x * θ.toH1Function.toFun x) V := by
    obtain ⟨B, hB⟩ := lip_bdry_step_cont_bound hVb hlapc
    exact lip_bdry_step_integrable_mul hVt hlapc.aestronglyMeasurable
      ((ae_restrict_iff' hVo.measurableSet).2 (Filter.Eventually.of_forall hB)) hθ2
  have e6 : ∫ x in V, (s⁻¹ * f' x + lapf x) * θ.toH1Function.toFun x =
      s⁻¹ * (∫ x in V, f' x * θ.toH1Function.toFun x) +
        ∫ x in V, lapf x * θ.toH1Function.toFun x := by
    rw [← integral_const_mul, ← integral_add (hfθ.const_mul _) hlθ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hsg : (ub - gV).grad = fun x => ub.grad x - gV.grad x := H1Function.sub_grad _ _
  simp only [hsg]
  change ∫ x in V, vecDot (ub.grad x - gV.grad x) (θ.toH1Function.grad x) =
    ∫ x in V, (s⁻¹ * f' x + lapf x) * θ.toH1Function.toFun x
  rw [e5, e2, e6]
  have : ∫ x in V, vecDot (ub.grad x) (θ.toH1Function.grad x) =
      s⁻¹ * ∫ x in V, f' x * θ.toH1Function.toFun x := by
    field_simp
    linarith only [e1]
  rw [this]
  ring

theorem lip_bdry_step_p12_univ {ℓ : ℝ} (S : Set (Vec d)) :
    p12_nmeas ℓ S Set.univ = ENNReal.ofReal ((ℓ ^ d)⁻¹) * volume S := by
  unfold p12_nmeas
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]

theorem lip_bdry_step_p12_ac (ℓ : ℝ) (S : Set (Vec d)) :
    p12_nmeas ℓ S ≪ volume.restrict S := by
  unfold p12_nmeas
  exact Measure.smul_absolutelyContinuous

/-- The normalization of the cube of side `ℓ` against the normalized norm on a larger set. -/
theorem lip_bdry_step_conv {S S' : Set (Vec d)} (hSS : S ⊆ S') (hS'0 : volume S' ≠ 0)
    (hS' : volume S' ≠ ⊤) {ℓ : ℝ} (hℓ : 0 < ℓ) {h : Vec d → ℝ}
    (hh : MemLp h 2 (volume.restrict S')) :
    (eLpNorm h 2 (p12_nmeas ℓ S)).toReal ≤
      Real.sqrt ((ℓ ^ d)⁻¹ * (volume S').toReal) * lipL2 S' h := by
  have hv0 : 0 < (volume S').toReal := ENNReal.toReal_pos hS'0 hS'
  have hc : 0 ≤ (ℓ ^ d)⁻¹ := by positivity
  have h1 : eLpNorm h 2 (p12_nmeas ℓ S) =
      ENNReal.ofReal ((ℓ ^ d)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm h 2 (volume.restrict S) := by
    unfold p12_nmeas
    exact eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h _
      (hh.aestronglyMeasurable.mono_measure (Measure.restrict_mono hSS le_rfl))
  have h2 : eLpNorm h 2 (volume.restrict S) ≤ eLpNorm h 2 (volume.restrict S') :=
    eLpNorm_mono_measure h (Measure.restrict_mono hSS le_rfl)
  have h3 : lipL2 S' h = ((volume S').toReal⁻¹ ^ (1 / 2 : ℝ)) *
      (eLpNorm h 2 (volume.restrict S')).toReal := by
    unfold lipL2
    rw [lip_int_harm_of_l2_lpBar_eq hS'0 hS' hh, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hX : (eLpNorm h 2 (volume.restrict S)).toReal ≤ (eLpNorm h 2 (volume.restrict S')).toReal :=
    ENNReal.toReal_mono hh.eLpNorm_ne_top h2
  have h4 : (eLpNorm h 2 (p12_nmeas ℓ S)).toReal =
      ((ℓ ^ d)⁻¹) ^ (1 / 2 : ℝ) * (eLpNorm h 2 (volume.restrict S)).toReal := by
    rw [h1, smul_eq_mul, ENNReal.toReal_mul]
    congr 1
    have : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by
      rw [ENNReal.toReal_div]; norm_num
    rw [this, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hc]
  rw [h4, h3]
  have hs1 : ((ℓ ^ d)⁻¹) ^ (1 / 2 : ℝ) = Real.sqrt ((ℓ ^ d)⁻¹) := (Real.sqrt_eq_rpow _).symm
  have hs2 : (volume S').toReal⁻¹ ^ (1 / 2 : ℝ) = Real.sqrt ((volume S').toReal⁻¹) :=
    (Real.sqrt_eq_rpow _).symm
  rw [hs1, hs2]
  have hs3 : Real.sqrt ((ℓ ^ d)⁻¹ * (volume S').toReal) * Real.sqrt ((volume S').toReal⁻¹) =
      Real.sqrt ((ℓ ^ d)⁻¹) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  calc Real.sqrt ((ℓ ^ d)⁻¹) * (eLpNorm h 2 (volume.restrict S)).toReal
      ≤ Real.sqrt ((ℓ ^ d)⁻¹) * (eLpNorm h 2 (volume.restrict S')).toReal :=
        mul_le_mul_of_nonneg_left hX (Real.sqrt_nonneg _)
    _ = Real.sqrt ((ℓ ^ d)⁻¹ * (volume S').toReal) *
        (Real.sqrt ((volume S').toReal⁻¹) * (eLpNorm h 2 (volume.restrict S')).toReal) := by
        rw [← mul_assoc, hs3]

/-- A bounded function in the normalization of the cube of side `ℓ`, exponent `q`. -/
theorem lip_bdry_step_bdd {S : Set (Vec d)} (hS : volume S ≠ ⊤) {ℓ : ℝ} (hℓ : 0 < ℓ) {q : ℝ}
    (hq : 1 ≤ q) {h : Vec d → ℝ} (hm : AEStronglyMeasurable h (volume.restrict S)) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ᵐ x ∂volume.restrict S, |h x| ≤ B) :
    (eLpNorm h (ENNReal.ofReal q) (p12_nmeas ℓ S)).toReal ≤
      B * ((ℓ ^ d)⁻¹ * (volume S).toReal) ^ (1 / q) := by
  have hq0 : 0 < q := by linarith only [hq]
  have hc : 0 ≤ (ℓ ^ d)⁻¹ := by positivity
  have hbμ : ∀ᵐ x ∂p12_nmeas ℓ S, ‖h x‖ ≤ B := by
    have := (lip_bdry_step_p12_ac ℓ S).ae_le hb
    filter_upwards [this] with x hx using by rwa [Real.norm_eq_abs]
  have hmμ : AEStronglyMeasurable h (p12_nmeas ℓ S) := hm.mono_ac (lip_bdry_step_p12_ac ℓ S)
  have h1 := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal q) hmμ hbμ
  have hfin : p12_nmeas ℓ S Set.univ ≠ ⊤ := by
    rw [lip_bdry_step_p12_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  have h2 : (eLpNorm h (ENNReal.ofReal q) (p12_nmeas ℓ S)).toReal ≤
      ((p12_nmeas ℓ S Set.univ) ^ ((ENNReal.ofReal q).toReal)⁻¹ * ENNReal.ofReal B).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg
      (by rw [ENNReal.toReal_ofReal hq0.le]; positivity) hfin) ENNReal.ofReal_ne_top) h1
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal hq0.le, lip_bdry_step_p12_univ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc, mul_comm, one_div]

theorem lip_bdry_step_p12_memLp {S S' : Set (Vec d)} (hSS : S ⊆ S') (ℓ : ℝ) {h : Vec d → ℝ}
    (hh : MemLp h 2 (volume.restrict S')) : MemLp h 2 (p12_nmeas ℓ S) := by
  unfold p12_nmeas
  exact (hh.mono_measure (Measure.restrict_mono hSS le_rfl)).smul_measure ENNReal.ofReal_ne_top

/-- The three pieces of the flatness in the normalization of the cube of side `ℓ`. -/
theorem lip_bdry_step_X1 {S Sv Su : Set (Vec d)} (hSm : MeasurableSet S) (hSv : S ⊆ Sv)
    (hSu : S ⊆ Su) (hSv0 : volume Sv ≠ 0) (hSvt : volume Sv ≠ ⊤) (hSu0 : volume Su ≠ 0)
    (hSut : volume Su ≠ ⊤) (hSt : volume S ≠ ⊤) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H R1 R2 R3 : Vec d → ℝ} (hH : ∀ y ∈ S, H y = R1 y + R2 y + R3 y)
    (hR1 : MemLp R1 2 (volume.restrict Sv)) (hR2 : MemLp R2 2 (volume.restrict Su))
    (hR3m : AEStronglyMeasurable R3 (volume.restrict S)) {B3 : ℝ} (hB3 : 0 ≤ B3)
    (hR3 : ∀ y ∈ S, |R3 y| ≤ B3) :
    (eLpNorm H 2 (p12_nmeas ℓ S)).toReal ≤
      Real.sqrt ((ℓ ^ d)⁻¹ * (volume Sv).toReal) * lipL2 Sv R1 +
        Real.sqrt ((ℓ ^ d)⁻¹ * (volume Su).toReal) * lipL2 Su R2 +
        B3 * Real.sqrt ((ℓ ^ d)⁻¹ * (volume S).toReal) := by
  set μ := p12_nmeas ℓ S with hμ
  have hfin : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSt.lt_top⟩
  have hR3L : MemLp R3 2 (volume.restrict S) :=
    MemLp.of_bound hR3m B3 ((ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact hR3 y hy))
  have m1 := lip_bdry_step_p12_memLp hSv ℓ hR1
  have m2 := lip_bdry_step_p12_memLp hSu ℓ hR2
  have m3 := lip_bdry_step_p12_memLp (subset_refl S) ℓ hR3L
  have hHe : eLpNorm H 2 μ = eLpNorm (fun y => R1 y + R2 y + R3 y) 2 μ := by
    refine eLpNorm_congr_ae ?_
    have := (lip_bdry_step_p12_ac ℓ S).ae_le (ae_restrict_mem hSm)
    filter_upwards [this] with y hy using hH y hy
  have hsum : eLpNorm (fun y => R1 y + R2 y + R3 y) 2 μ ≤
      eLpNorm R1 2 μ + eLpNorm R2 2 μ + eLpNorm R3 2 μ := by
    calc eLpNorm (fun y => R1 y + R2 y + R3 y) 2 μ
        = eLpNorm ((R1 + R2) + R3) 2 μ := rfl
      _ ≤ eLpNorm (R1 + R2) 2 μ + eLpNorm R3 2 μ :=
          eLpNorm_add_le (by norm_num)
      _ ≤ (eLpNorm R1 2 μ + eLpNorm R2 2 μ) + eLpNorm R3 2 μ := by
          gcongr
          exact eLpNorm_add_le (by norm_num)
  have hne : eLpNorm R1 2 μ + eLpNorm R2 2 μ + eLpNorm R3 2 μ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨m1.eLpNorm_ne_top, m2.eLpNorm_ne_top⟩,
      m3.eLpNorm_ne_top⟩
  have h1 := lip_bdry_step_conv hSv hSv0 hSvt hℓ hR1
  have h2 := lip_bdry_step_conv hSu hSu0 hSut hℓ hR2
  have h3 := lip_bdry_step_bdd (q := 2) hSt hℓ (by norm_num) hR3m hB3 
    ((ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall hR3))
  rw [hHe]
  calc (eLpNorm (fun y => R1 y + R2 y + R3 y) 2 μ).toReal
      ≤ (eLpNorm R1 2 μ + eLpNorm R2 2 μ + eLpNorm R3 2 μ).toReal := ENNReal.toReal_mono hne hsum
    _ = (eLpNorm R1 2 μ).toReal + (eLpNorm R2 2 μ).toReal + (eLpNorm R3 2 μ).toReal := by
        rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨m1.eLpNorm_ne_top, m2.eLpNorm_ne_top⟩)
          m3.eLpNorm_ne_top, ENNReal.toReal_add m1.eLpNorm_ne_top m2.eLpNorm_ne_top]
    _ ≤ _ := by
        have e3 : (eLpNorm R3 2 μ).toReal ≤ B3 * Real.sqrt ((ℓ ^ d)⁻¹ * (volume S).toReal) := by
          have := h3
          rw [show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) by simp, ← Real.sqrt_eq_rpow] at this
          simpa using this
        linarith only [h1, h2, e3]

theorem lip_bdry_step_arith {Ca Cdec MU a1 a2 a3 a4 A1 A2 C₁ C₂ r0 r1 δ θ Φ P G1 Fs Gk Tt Q Fm : ℝ}
    (hCa : 0 ≤ Ca) (hCdec : 0 ≤ Cdec) (hMU : 0 ≤ MU) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hr0 : 0 ≤ r0) (hr01 : r0 ≤ r1)
    (hr0' : r0 ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ θ) (hΦ : 0 ≤ Φ) (hP : 0 ≤ P)
    (hG1 : 0 ≤ G1) (hFs : 0 ≤ Fs) (hGk : 0 ≤ Gk)
    (hC₁ : Cdec * (a1 * Ca + a2 + MU) ≤ C₁)
    (hC₂ : Cdec * (a1 * Ca + a3 + a4) + A1 * Ca + A2 ≤ C₂)
    (hTt : Tt ≤ Ca * (δ * (Φ + P) + G1 + Fs + Gk))
    (hQ : Q ≤ a1 * Tt + a2 * Φ + a3 * G1 + MU * θ * P + a4 * Fs)
    (hF : Fm ≤ A1 * Tt + Cdec * r0 * Q + A2 * G1) :
    Fm ≤ (C₁ * r1 + C₂ * δ) * Φ + (C₂ * δ + C₁ * r1 * θ) * P + C₂ * (G1 + Fs + Gk) := by
  have hr1 : 0 ≤ r1 := hr0.trans hr01
  have hQ' : Q ≤ a1 * (Ca * (δ * (Φ + P) + G1 + Fs + Gk)) + a2 * Φ + a3 * G1 + MU * θ * P +
      a4 * Fs := by
    have := mul_le_mul_of_nonneg_left hTt ha1
    linarith only [hQ, this]
  have hCQ : Cdec * r0 * Q ≤ Cdec * r0 * (a1 * (Ca * (δ * (Φ + P) + G1 + Fs + Gk)) + a2 * Φ +
      a3 * G1 + MU * θ * P + a4 * Fs) :=
    mul_le_mul_of_nonneg_left hQ' (mul_nonneg hCdec hr0)
  have hTA : A1 * Tt ≤ A1 * (Ca * (δ * (Φ + P) + G1 + Fs + Gk)) := mul_le_mul_of_nonneg_left hTt hA1
  have hrδ : r0 * δ ≤ r1 := by
    calc r0 * δ ≤ r0 * 1 := mul_le_mul_of_nonneg_left hδ1 hr0
      _ ≤ r1 := by linarith only [hr01]
  have t1 : r0 * δ * Φ ≤ r1 * Φ := mul_le_mul_of_nonneg_right hrδ hΦ
  have t2 : r0 * δ * P ≤ δ * P := by
    have : r0 * δ ≤ δ := by
      calc r0 * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hr0' hδ0
        _ = δ := one_mul _
    exact mul_le_mul_of_nonneg_right this hP
  have t3 : r0 * G1 ≤ G1 := by
    calc r0 * G1 ≤ 1 * G1 := mul_le_mul_of_nonneg_right hr0' hG1
      _ = G1 := one_mul _
  have t4 : r0 * Fs ≤ Fs := by
    calc r0 * Fs ≤ 1 * Fs := mul_le_mul_of_nonneg_right hr0' hFs
      _ = Fs := one_mul _
  have t5 : r0 * Gk ≤ Gk := by
    calc r0 * Gk ≤ 1 * Gk := mul_le_mul_of_nonneg_right hr0' hGk
      _ = Gk := one_mul _
  have t6 : r0 * Φ ≤ r1 * Φ := mul_le_mul_of_nonneg_right hr01 hΦ
  have t7 : r0 * θ * P ≤ r1 * θ * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr01 hθ) hP
  have k1 : Cdec * (a1 * Ca) * (r0 * δ * Φ) ≤ Cdec * (a1 * Ca) * (r1 * Φ) :=
    mul_le_mul_of_nonneg_left t1 (by positivity)
  have k2 : Cdec * (a1 * Ca) * (r0 * δ * P) ≤ Cdec * (a1 * Ca) * (δ * P) :=
    mul_le_mul_of_nonneg_left t2 (by positivity)
  have k3 : (Cdec * (a1 * Ca) + Cdec * a3) * (r0 * G1) ≤ (Cdec * (a1 * Ca) + Cdec * a3) * G1 :=
    mul_le_mul_of_nonneg_left t3 (by positivity)
  have k4 : (Cdec * (a1 * Ca) + Cdec * a4) * (r0 * Fs) ≤ (Cdec * (a1 * Ca) + Cdec * a4) * Fs :=
    mul_le_mul_of_nonneg_left t4 (by positivity)
  have k5 : Cdec * (a1 * Ca) * (r0 * Gk) ≤ Cdec * (a1 * Ca) * Gk :=
    mul_le_mul_of_nonneg_left t5 (by positivity)
  have k6 : Cdec * a2 * (r0 * Φ) ≤ Cdec * a2 * (r1 * Φ) :=
    mul_le_mul_of_nonneg_left t6 (by positivity)
  have k7 : Cdec * MU * (r0 * θ * P) ≤ Cdec * MU * (r1 * θ * P) :=
    mul_le_mul_of_nonneg_left t7 (by positivity)
  have c1 : Cdec * (a1 * Ca + a2 + MU) * (r1 * Φ) ≤ C₁ * (r1 * Φ) :=
    mul_le_mul_of_nonneg_right hC₁ (by positivity)
  have c1' : Cdec * (a1 * Ca + a2 + MU) * (r1 * θ * P) ≤ C₁ * (r1 * θ * P) :=
    mul_le_mul_of_nonneg_right hC₁ (by positivity)
  have hs3 : 0 ≤ Cdec * (a1 * Ca + a3 + a4) := by positivity
  have hs4 : 0 ≤ Cdec * a3 := by positivity
  have hs5 : 0 ≤ Cdec * a4 := by positivity
  have hs6 : 0 ≤ Cdec * (a1 * Ca) := by positivity
  have hs7 : 0 ≤ A1 * Ca := by positivity
  have d1 : A1 * Ca ≤ C₂ := by
    have : 0 ≤ Cdec * (a1 * Ca + a3 + a4) := hs3
    linarith only [hC₂, this, hA2]
  have d2 : Cdec * (a1 * Ca) + A1 * Ca ≤ C₂ := by
    have e : Cdec * (a1 * Ca + a3 + a4) = Cdec * (a1 * Ca) + Cdec * a3 + Cdec * a4 := by ring
    linarith only [hC₂, e, hs4, hs5, hA2]
  have d3 : Cdec * (a1 * Ca) + Cdec * a3 + A1 * Ca + A2 ≤ C₂ := by
    have e : Cdec * (a1 * Ca + a3 + a4) = Cdec * (a1 * Ca) + Cdec * a3 + Cdec * a4 := by ring
    linarith only [hC₂, e, hs5]
  have d4 : Cdec * (a1 * Ca) + Cdec * a4 + A1 * Ca ≤ C₂ := by
    have e : Cdec * (a1 * Ca + a3 + a4) = Cdec * (a1 * Ca) + Cdec * a3 + Cdec * a4 := by ring
    linarith only [hC₂, e, hs4, hA2]
  have e1 : A1 * Ca * (δ * Φ) ≤ C₂ * δ * Φ := by
    have := mul_le_mul_of_nonneg_right d1 (mul_nonneg hδ0 hΦ)
    linarith only [this]
  have e2 : (Cdec * (a1 * Ca) + A1 * Ca) * (δ * P) ≤ C₂ * δ * P := by
    have := mul_le_mul_of_nonneg_right d2 (mul_nonneg hδ0 hP)
    linarith only [this]
  have e3 : (Cdec * (a1 * Ca) + Cdec * a3 + A1 * Ca + A2) * G1 ≤ C₂ * G1 :=
    mul_le_mul_of_nonneg_right d3 hG1
  have e4 : (Cdec * (a1 * Ca) + Cdec * a4 + A1 * Ca) * Fs ≤ C₂ * Fs :=
    mul_le_mul_of_nonneg_right d4 hFs
  have e5 : (Cdec * (a1 * Ca) + A1 * Ca) * Gk ≤ C₂ * Gk :=
    mul_le_mul_of_nonneg_right d2 hGk
  have x1 : 0 ≤ Cdec * MU * (r1 * Φ) := by positivity
  have x2 : 0 ≤ Cdec * (a1 * Ca + a2) * (r1 * θ * P) := by positivity
  linarith only [hF, hTA, hCQ, k1, k2, k3, k4, k5, k6, k7, c1, c1', e1, e2, e3, e4, e5, x1, x2]

end SuperdiffusionCLT.Section7
