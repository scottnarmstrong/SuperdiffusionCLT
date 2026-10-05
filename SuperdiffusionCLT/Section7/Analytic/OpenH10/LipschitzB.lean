/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.Lipschitz
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.Matched
public import Homogenization.Sobolev.H1.Algebra.H1Function

/-!
# Lipschitz multipliers in `H¹` and `H¹₀`

The product of an `H¹(U)` function with a bounded Lipschitz function is `H¹(U)` (`mulLip`), with
gradient `η ∇u + u ∇η` where `∇η` is the a.e. classical gradient (`lipGradient`).  A multiplier
with compact support in `U` gives an `H¹₀(U)` function (`mulLipH10`).  Also the difference of two
`H¹₀(U)` functions (`h10Sub`) and `min(u, t) ∈ H¹₀(U)`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

/-- The a.e. classical gradient of a scalar function, in the coordinate basis. -/
noncomputable def lipGradient (η : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => fderiv ℝ η x (basisVec i)

/-- Products of bounded Lipschitz functions are Lipschitz. -/
theorem lipschitzWith_mul {K K' : ℝ≥0} {M N : ℝ} {η ζ : Vec d → ℝ}
    (h : LipschitzWith K η) (h' : LipschitzWith K' ζ)
    (hM : ∀ x, |η x| ≤ M) (hN : ∀ x, |ζ x| ≤ N) :
    LipschitzWith (Real.toNNReal M * K' + Real.toNNReal N * K) (fun x => η x * ζ x) := by
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hNn : 0 ≤ N := (abs_nonneg _).trans (hN 0)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have e1 := h.dist_le_mul x y
  have e2 := h'.dist_le_mul x y
  simp only [dist_eq_norm, Real.norm_eq_abs] at e1 e2 ⊢
  push_cast [Real.coe_toNNReal _ hMn, Real.coe_toNNReal _ hNn]
  have hn := norm_nonneg (x - y)
  calc |η x * ζ x - η y * ζ y| = |η x * (ζ x - ζ y) + ζ y * (η x - η y)| := by ring_nf
    _ ≤ |η x * (ζ x - ζ y)| + |ζ y * (η x - η y)| := abs_add_le _ _
    _ = |η x| * |ζ x - ζ y| + |ζ y| * |η x - η y| := by rw [abs_mul, abs_mul]
    _ ≤ M * (K' * ‖x - y‖) + N * (K * ‖x - y‖) :=
        add_le_add (mul_le_mul (hM x) e2 (abs_nonneg _) hMn)
          (mul_le_mul (hN y) e1 (abs_nonneg _) hNn)
    _ = (M * K' + N * K) * ‖x - y‖ := by ring

theorem integrableOn_mul_of_memL2On {f g : Vec d → ℝ} (hf : MemL2On U f) (hg : MemL2On U g) :
    IntegrableOn (fun x => f x * g x) U := by
  have hht : ENNReal.HolderTriple 2 2 1 :=
    ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  exact memLp_one_iff_integrable.mp (hf.fun_mul (r := 1) hg)

/-- The product `η φ` of a Lipschitz function with a smooth compactly supported one, together
with the a.e. product rule. -/
theorem integral_mul_partial_product (hU : IsOpen U) (u : H1Function U)
    {K : ℝ≥0} {M : ℝ} {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (i : Fin d) :
    ∫ x in U, (η x * u.toFun x) * fderiv ℝ φ x (basisVec i) =
      -∫ x in U, (η x * u.grad x i + u.toFun x * fderiv ℝ η x (basisVec i)) * φ x := by
  have hηc : Continuous η := hη.continuous
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Kφ, hKφ⟩ := (hφ.of_le (by simp : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).lipschitzWith_of_hasCompactSupport hφc (by simp)
  obtain ⟨Bφ, hBφ⟩ := hφcont.bounded_above_of_compact_support hφc
  have hBφ' : ∀ x, |φ x| ≤ Bφ := fun x => by simpa using hBφ x
  have hψ := lipschitzWith_mul hη hKφ hM hBφ'
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hBnn : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ' 0)
  have hψc : HasCompactSupport (fun x => η x * φ x) := hφc.mul_left
  have hψU : tsupport (fun x => η x * φ x) ⊆ U :=
    (tsupport_mul_subset_right (f := η) (g := φ)).trans hφU
  have hmain := H1Function.integral_mul_partial_lip_eq hU u hψ
    hψc hψU i
  set Dφ : Vec d → ℝ := fun x => fderiv ℝ φ x (basisVec i) with hDφ
  set Dη : Vec d → ℝ := fun x => fderiv ℝ η x (basisVec i) with hDη
  have hDφc : Continuous Dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDφcs : HasCompactSupport Dφ := by
    simpa [hDφ] using hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  -- the a.e. product rule
  have hprod : ∀ᵐ x ∂(volume : Measure (Vec d)),
      fderiv ℝ (fun x => η x * φ x) x (basisVec i) = η x * Dφ x + φ x * Dη x := by
    filter_upwards [hη.ae_differentiableAt] with x hx
    rw [fderiv_fun_mul hx (hφ.differentiable (by simp) x)]
    simp [hDφ, hDη]
  -- integrability
  have hφDη : MemL2On U (fun x => φ x * Dη x) := by
    refine MemLp.restrict U ?_
    refine memLp_two_of_bounded_of_zero_off (C := Bφ * K) hφc.isCompact
      (hφcont.aestronglyMeasurable.mul (aestronglyMeasurable_partialDeriv η i))
      ?_ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    filter_upwards [lipschitzWith_ae_norm_partialDeriv_le hη i] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hBφ' x) (by simpa using hx) (norm_nonneg _) hBnn
  have hηDφ : MemL2On U (fun x => η x * Dφ x) :=
    ((hηc.mul hDφc).memLp_of_hasCompactSupport hDφcs.mul_left).restrict U
  have hηφ : MemL2On U (fun x => η x * φ x) :=
    ((hηc.mul hφcont).memLp_of_hasCompactSupport hφc.mul_left).restrict U
  have hDηφ : MemL2On U (fun x => Dη x * φ x) := by
    refine MemLp.restrict U ?_
    refine memLp_two_of_bounded_of_zero_off (C := K * Bφ) hφc.isCompact
      ((aestronglyMeasurable_partialDeriv η i).mul hφcont.aestronglyMeasurable)
      ?_ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    filter_upwards [lipschitzWith_ae_norm_partialDeriv_le hη i] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (by simpa using hx) (hBφ' x) (norm_nonneg _) K.coe_nonneg
  have I1 : IntegrableOn (fun x => u.toFun x * (η x * Dφ x)) U :=
    integrableOn_mul_of_memL2On u.memL2 hηDφ
  have I2 : IntegrableOn (fun x => u.toFun x * (φ x * Dη x)) U :=
    integrableOn_mul_of_memL2On u.memL2 hφDη
  have I3 : IntegrableOn (fun x => u.grad x i * (η x * φ x)) U :=
    integrableOn_mul_of_memL2On (u.grad_memL2 i) hηφ
  have I4 : IntegrableOn (fun x => u.toFun x * Dη x * φ x) U := by
    simpa [mul_assoc] using integrableOn_mul_of_memL2On u.memL2 hDηφ
  have I5 : IntegrableOn (fun x => η x * u.grad x i * φ x) U := by
    simpa [mul_assoc] using I3.congr_fun (fun x _ => by ring) hU.measurableSet
  -- combine
  have e1 : ∫ x in U, u.toFun x * fderiv ℝ (fun x => η x * φ x) x (basisVec i) =
      ∫ x in U, (u.toFun x * (η x * Dφ x) + u.toFun x * (φ x * Dη x)) := by
    refine setIntegral_congr_ae hU.measurableSet ?_
    filter_upwards [hprod] with x hx _
    rw [hx]; ring
  rw [e1, integral_add I1 I2] at hmain
  have e2 : ∫ x in U, (η x * u.toFun x) * Dφ x = ∫ x in U, u.toFun x * (η x * Dφ x) :=
    setIntegral_congr_fun hU.measurableSet fun x _ => by ring
  have e3 : ∫ x in U, u.grad x i * (η x * φ x) = ∫ x in U, η x * u.grad x i * φ x :=
    setIntegral_congr_fun hU.measurableSet fun x _ => by ring
  have e4 : ∫ x in U, (η x * u.grad x i + u.toFun x * Dη x) * φ x =
      (∫ x in U, η x * u.grad x i * φ x) + ∫ x in U, u.toFun x * (φ x * Dη x) := by
    rw [← integral_add I5 I2]
    exact setIntegral_congr_fun hU.measurableSet fun x _ => by ring
  rw [e2, e4]
  rw [e3] at hmain
  linarith only [hmain]

theorem mulLip_memL2 (u : H1Function U) {K : ℝ≥0} {M : ℝ} {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M) : MemL2On U (fun x => η x * u.toFun x) := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine (u.memL2.const_mul M).mono
    ((hη.continuous).aestronglyMeasurable.mul u.memL2.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hMnn]
  exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)

theorem mulLip_gradMemL2 (u : H1Function U) {K : ℝ≥0} {M : ℝ} {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M) (i : Fin d) :
    MemL2On U (fun x => η x * u.grad x i + u.toFun x * fderiv ℝ η x (basisVec i)) := by
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine MemLp.add ?_ ?_
  · refine ((u.grad_memL2 i).const_mul M).mono
      ((hη.continuous).aestronglyMeasurable.mul (u.grad_memL2 i).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hMnn]
    exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)
  · refine (u.memL2.const_mul (K : ℝ)).mono
      (u.memL2.aestronglyMeasurable.mul
        ((aestronglyMeasurable_partialDeriv η i).mono_measure Measure.restrict_le_self))
      ?_
    have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖fderiv ℝ η x (basisVec i)‖ ≤ K :=
      lipschitzWith_ae_norm_partialDeriv_le hη i
    have hae' : ∀ᵐ x ∂(volumeMeasureOn U), ‖fderiv ℝ η x (basisVec i)‖ ≤ K :=
      ae_restrict_of_ae hae
    filter_upwards [hae'] with x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg K.coe_nonneg] at hx ⊢
    rw [mul_comm (K : ℝ)]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

/-- **Product of an `H¹` function with a bounded Lipschitz function.**  The value is `η u`, the
gradient is `η ∇u + u ∇η` with `∇η` the a.e. classical gradient of `η`. -/
noncomputable def mulLip (hU : IsOpen U) (u : H1Function U) {K : ℝ≥0} {M : ℝ}
    {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M) : H1Function U where
  toFun := fun x => η x * u.toFun x
  grad := fun x => η x • u.grad x + u.toFun x • lipGradient η x
  memL2 := mulLip_memL2 u hη hM
  gradMemL2 := fun i => by
    simpa [lipGradient] using mulLip_gradMemL2 u hη hM i
  hasWeakGradient := fun i φ hφ hφc hφU => by
    simpa [lipGradient] using integral_mul_partial_product hU u hη hM hφ hφc hφU i

@[simp] theorem mulLip_toFun (hU : IsOpen U) (u : H1Function U) {K : ℝ≥0} {M : ℝ}
    {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M) :
    (mulLip hU u hη hM).toFun = fun x => η x * u.toFun x := rfl

@[simp] theorem mulLip_grad (hU : IsOpen U) (u : H1Function U) {K : ℝ≥0} {M : ℝ}
    {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M) :
    (mulLip hU u hη hM).grad =
      fun x => η x • u.grad x + u.toFun x • lipGradient η x := rfl


/-- The difference of two `H¹₀(U)` functions. -/
noncomputable def h10Sub (u v : H10Function U) : H10Function U where
  toH1Function := u.toH1Function - v.toH1Function
  approx := fun n x => u.approx n x - v.approx n x
  approx_smooth := fun n => (u.approx_smooth n).sub (v.approx_smooth n)
  approx_hasCompactSupport := fun n => by
    exact (u.approx_hasCompactSupport n).sub (v.approx_hasCompactSupport n)
  approx_support_subset := fun n => by
    refine (closure_mono (Function.support_sub _ _)).trans ?_
    rw [closure_union]
    exact union_subset (u.approx_support_subset n) (v.approx_support_subset n)
  tendsto_approx := by
    have h1 := u.tendsto_approx
    have h2 := v.tendsto_approx
    have hs := h1.add h2
    rw [add_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => bot_le)
      (fun n => ?_)
    have : (fun x => (u.approx n x - v.approx n x) - (u.toH1Function - v.toH1Function).toFun x) =
        (fun x => u.approx n x - u.toH1Function.toFun x) -
          fun x => v.approx n x - v.toH1Function.toFun x := by
      funext x; simp [H1Function.sub_toFun]; ring
    rw [this]
    exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  tendsto_approx_grad := fun i => by
    have h1 := u.tendsto_approx_grad i
    have h2 := v.tendsto_approx_grad i
    have hs := h1.add h2
    rw [add_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => bot_le)
      (fun n => ?_)
    have : (fun x => (fderiv ℝ (fun x => u.approx n x - v.approx n x) x) (basisVec i) -
        (u.toH1Function - v.toH1Function).grad x i) =
        (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) -
          fun x => (fderiv ℝ (v.approx n) x) (basisVec i) - v.toH1Function.grad x i := by
      funext x
      rw [fderiv_fun_sub ((u.approx_smooth n).differentiable (by simp) x)
        ((v.approx_smooth n).differentiable (by simp) x)]
      simp [H1Function.sub_grad]; ring
    rw [this]
    exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)

@[simp] theorem h10Sub_toH1Function (u v : H10Function U) :
    (h10Sub u v).toH1Function = u.toH1Function - v.toH1Function := rfl


/-- **`H¹₀` multiplier.**  A bounded Lipschitz multiplier with compact support in `U` times an
`H¹(U)` function is in `H¹₀(U)`; the underlying `H¹` function is `mulLip`. -/
noncomputable def mulLipH10 (hU : IsOpen U) (u : H1Function U) {K : ℝ≥0} {M : ℝ}
    {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) : H10Function U :=
  toH10OfCompact hU (mulLip hU u hη hM) hηU hηc
    (fun x _ hx => by simp [image_eq_zero_of_notMem_tsupport hx])

@[simp] theorem mulLipH10_toH1Function (hU : IsOpen U) (u : H1Function U) {K : ℝ≥0} {M : ℝ}
    {η : Vec d → ℝ} (hη : LipschitzWith K η) (hM : ∀ x, |η x| ≤ M)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    (mulLipH10 hU u hη hM hηc hηU).toH1Function = mulLip hU u hη hM :=
  toH10OfCompact_toH1Function hU _ _ _ _

/-- **`min(u, t) ∈ H¹₀`** for `u ∈ H¹₀(U)` on an open set of finite volume and `t ≥ 0`. -/
theorem memH10_min (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H10Function U) {t : ℝ}
    (ht : 0 ≤ t) : MemH10 U (fun x => min (u.toH1Function.toFun x) t) := by
  obtain ⟨v, hv⟩ := memH10_positivePart hU hfin u ht
  refine ⟨h10Sub u v, ?_⟩
  funext x
  rw [h10Sub_toH1Function]
  rw [H1Function.sub_toFun]
  show u.toH1Function.toFun x - v.toH1Function.toFun x = _
  rw [hv]
  change u.toH1Function.toFun x - max (u.toH1Function.toFun x - t) 0 = _
  rcases le_total (u.toH1Function.toFun x) t with h | h
  · rw [max_eq_right (by linarith only [h]), min_eq_left h]; ring
  · rw [max_eq_left (by linarith only [h]), min_eq_right h]; ring

/-- Satisfiability witness: a smooth bump of outer radius `1/2` in the unit ball is compactly
supported, Lipschitz, bounded by `1`, with `tsupport` inside the ball. -/
theorem exists_bump_witness :
    ∃ (K : ℝ≥0) (η : Vec 2 → ℝ), LipschitzWith K η ∧ (∀ x, |η x| ≤ 1) ∧ HasCompactSupport η ∧
      tsupport η ⊆ Metric.ball (0 : Vec 2) 1 := by
  let b : ContDiffBump (0 : Vec 2) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hc : HasCompactSupport (b : Vec 2 → ℝ) := b.hasCompactSupport
  obtain ⟨K, hK⟩ := (b.contDiff (n := 1)).lipschitzWith_of_hasCompactSupport hc (by simp)
  refine ⟨K, b, hK, fun x => ?_, hc, ?_⟩
  · rw [abs_of_nonneg (b.nonneg)]; exact b.le_one
  · rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by norm_num [b])

/-- Witness: the hypotheses of `mulLipH10` are met on the unit ball (bump multiplier, `u = 0`). -/
example : ∃ w : H10Function (Metric.ball (0 : Vec 2) 1), w.toH1Function.toFun = 0 := by
  obtain ⟨K, η, hη, hM, hc, hU⟩ := exists_bump_witness
  refine ⟨mulLipH10 Metric.isOpen_ball (0 : H1Function (Metric.ball (0 : Vec 2) 1)) hη hM hc hU,
    ?_⟩
  rw [mulLipH10_toH1Function]
  funext x
  simp [mulLip]

/-- Witness: the hypotheses of `memH10_min` are met on the unit ball (`u = 0`, `t = 1`). -/
example : MemH10 (Metric.ball (0 : Vec 2) 1)
    (fun x => min ((H10Function.ofContDiff (U := Metric.ball (0 : Vec 2) 1) Metric.isOpen_ball
      (f := fun _ => (0 : ℝ)) contDiff_const HasCompactSupport.zero (by simp)).toH1Function.toFun x)
      1) :=
  memH10_min Metric.isOpen_ball (measure_ball_lt_top (x := (0 : Vec 2)) (r := 1)).ne _
    zero_le_one

/-- Witness: the hypotheses of `H1Function.integral_mul_partial_lip_eq` are met (bump test
function, `u = 0`, on the unit ball). -/
example (i : Fin 2) : True := by
  obtain ⟨K, η, hη, -, hc, hU⟩ := exists_bump_witness
  have := H1Function.integral_mul_partial_lip_eq Metric.isOpen_ball
    (0 : H1Function (Metric.ball (0 : Vec 2) 1)) hη hc hU i
  trivial

end SuperdiffusionCLT.Section7
