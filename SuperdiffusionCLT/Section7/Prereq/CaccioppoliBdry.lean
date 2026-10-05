/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Limit
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryLocalized
public import SuperdiffusionCLT.Section7.Analytic.CZ.Local

/-!
# The boundary Caccioppoli test function

A bounded Lipschitz multiplier of an `H¹₀(V)` function is an `H¹₀(V)` function
(`ca2_h10_mulLip`).  Combined with the localized zero trace of `u - γ` this gives the test
function `Φ (u - γ)` for every `C¹` compactly supported weight `Φ` supported in the window
(`ca2_test_fn`), with its gradient.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_eLpNorm_sub_comm' {μ : Measure (Vec d)} (f g : Vec d → ℝ) :
    eLpNorm (fun x => f x - g x) 2 μ = eLpNorm (fun x => g x - f x) 2 μ :=
  eLpNorm_sub_comm f g 2 μ

/-- An `L²` norm of a product with an almost everywhere bounded factor. -/
theorem ca2_eLpNorm_mul_le {μ : Measure (Vec d)} {g h : Vec d → ℝ} (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, |g x| ≤ C) :
    eLpNorm (fun x => g x * h x) 2 μ ≤ ENNReal.ofReal C * eLpNorm h 2 μ := by
  have h1 : eLpNorm (fun x => g x * h x) 2 μ ≤ eLpNorm (C • h) 2 μ := by
    refine eLpNorm_mono_ae (hg.mul hh) ?_
    filter_upwards [hb] with x hx
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  refine h1.trans ?_
  rw [eLpNorm_const_smul]
  simp [Real.enorm_eq_ofReal hC]

/-- A bounded Lipschitz multiplier of an `H¹₀(V)` function is again `H¹₀(V)`. -/
theorem ca2_h10_mulLip {V : Set (Vec d)} (hV : IsOpen V) (w : H10Function V) {K : ℝ≥0} {M : ℝ}
    {Φ : Vec d → ℝ} (hΦ : LipschitzWith K Φ) (hM : ∀ x, |Φ x| ≤ M) :
    MemH10 V (fun x => Φ x * w.toH1Function.toFun x) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set μ : Measure (Vec d) := volume.restrict V with hμ
  let a : ℕ → H1Function V := fun n =>
    H1Function.ofContDiff hV ((w.approx_smooth n).of_le (by simp)) (w.approx_hasCompactSupport n)
  have hmem : ∀ n, MemH10 V (mulLip hV (a n) hΦ hM).toFun := by
    intro n
    refine ⟨toH10OfCompact hV (mulLip hV (a n) hΦ hM) (K := tsupport (w.approx n))
      (w.approx_support_subset n) (w.approx_hasCompactSupport n).isCompact ?_, ?_⟩
    · intro x _ hx
      show Φ x * w.approx n x = 0
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · rw [toH10OfCompact_toH1Function]
  have key := memH10_of_tendsto_H1 hV (mulLip hV w.toH1Function hΦ hM)
    (fun n => mulLip hV (a n) hΦ hM) hmem ?_ ?_
  · exact key
  · -- function part
    have h0 := w.tendsto_approx
    have h1 : Tendsto (fun n => ENNReal.ofReal M * eLpNorm (fun x => w.approx n x -
        w.toH1Function.toFun x) 2 μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.ofReal_ne_top (r := M)))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun n => bot_le)
      (fun n => ?_)
    have hdf : (fun x => (mulLip hV w.toH1Function hΦ hM).toFun x - (mulLip hV (a n) hΦ hM).toFun x) =
        fun x => Φ x * (w.toH1Function.toFun x - w.approx n x) := by
      funext x
      show Φ x * w.toH1Function.toFun x - Φ x * w.approx n x = _
      ring
    have hpm : AEStronglyMeasurable (fun x => w.toH1Function.toFun x - w.approx n x) μ :=
      w.toH1Function.memL2.aestronglyMeasurable.sub ((w.approx_smooth n).continuous.aestronglyMeasurable)
    rw [hdf]
    refine (ca2_eLpNorm_mul_le (μ := μ) hΦ.continuous.aestronglyMeasurable hpm hM0
      (Filter.Eventually.of_forall hM)).trans (le_of_eq ?_)
    rw [ca2_eLpNorm_sub_comm']
  · intro i
    have hp0 := w.tendsto_approx
    have hq0 := w.tendsto_approx_grad i
    have hp1 : Tendsto (fun n => ENNReal.ofReal (K : ℝ) * eLpNorm (fun x => w.approx n x -
        w.toH1Function.toFun x) 2 μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hp0 (Or.inr (ENNReal.ofReal_ne_top (r := (K : ℝ))))
      simpa using this
    have hq1 : Tendsto (fun n => ENNReal.ofReal M * eLpNorm (fun x => (fderiv ℝ (w.approx n) x)
        (basisVec i) - w.toH1Function.grad x i) 2 μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hq0 (Or.inr (ENNReal.ofReal_ne_top (r := M)))
      simpa using this
    have hs := hq1.add hp1
    rw [add_zero] at hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun n => bot_le)
      (fun n => ?_)
    have hΦc : Continuous Φ := hΦ.continuous
    have hpm : AEStronglyMeasurable (fun x => w.toH1Function.toFun x - w.approx n x) μ :=
      w.toH1Function.memL2.aestronglyMeasurable.sub ((w.approx_smooth n).continuous.aestronglyMeasurable)
    have hqm' : AEStronglyMeasurable (fun x => w.toH1Function.grad x i - (fderiv ℝ (w.approx n) x)
        (basisVec i)) μ := by
      refine AEStronglyMeasurable.sub (w.toH1Function.gradMemL2 i).aestronglyMeasurable ?_
      exact (((w.approx_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable
    have hLm : AEStronglyMeasurable (fun x => fderiv ℝ Φ x (basisVec i)) μ :=
      (aestronglyMeasurable_partialDeriv Φ i).mono_measure Measure.restrict_le_self
    have hae : ∀ᵐ x ∂μ, ‖fderiv ℝ Φ x (basisVec i)‖ ≤ K :=
      ae_restrict_of_ae (lipschitzWith_ae_norm_partialDeriv_le hΦ i)
    have hdiff : (fun x => (mulLip hV w.toH1Function hΦ hM).grad x i - (mulLip hV (a n) hΦ hM).grad x i) =
        (fun x => Φ x * (w.toH1Function.grad x i - (fderiv ℝ (w.approx n) x) (basisVec i))) +
          fun x => fderiv ℝ Φ x (basisVec i) * (w.toH1Function.toFun x - w.approx n x) := by
      funext x
      simp only [mulLip_grad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, lipGradient]
      show Φ x * w.toH1Function.grad x i + w.toH1Function.toFun x * fderiv ℝ Φ x (basisVec i) -
        (Φ x * (fderiv ℝ (w.approx n) x) (basisVec i) + w.approx n x * fderiv ℝ Φ x (basisVec i)) = _
      ring
    rw [hdiff]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    have e1 := ca2_eLpNorm_mul_le (μ := μ) hΦ.continuous.aestronglyMeasurable hqm' hM0
      (Filter.Eventually.of_forall hM)
    have e2 := ca2_eLpNorm_mul_le (μ := μ) hLm hpm K.coe_nonneg
      (hae.mono fun x hx => by simpa using hx)
    refine (add_le_add e1 e2).trans (le_of_eq ?_)
    rw [ca2_eLpNorm_sub_comm' (w.toH1Function.grad · i) (fun x => (fderiv ℝ (w.approx n) x) (basisVec i)),
      ca2_eLpNorm_sub_comm' w.toH1Function.toFun (w.approx n)]

/-- **The test function `Φ (u - γ)` under a localized zero trace of `u - γ`**: for a `C¹` weight
`Φ` with compact support inside the window `T`, it is an `H¹₀(V)` function with the product-rule
gradient. -/
theorem ca2_test_fn {V T : Set (Vec d)} (hV : IsOpen V) (hT : IsOpen T) (u : H1Function V)
    {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn V T (fun x => u.toFun x - γ x)) {Φ : Vec d → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) (hΦT : tsupport Φ ⊆ T) :
    ∃ φ : H10Function V, (∀ x, φ.toH1Function.toFun x = Φ x * (u.toFun x - γ x)) ∧
      ∀ᵐ x ∂(volume.restrict V), φ.toH1Function.grad x =
        Φ x • (u.grad x - p12_grad γ x) + (u.toFun x - γ x) • p12_grad Φ x := by
  obtain ⟨ζ, hζ, hζc, hζT, hζ1⟩ := dgloc_exists_cutoff hΦc hT hΦT
  obtain ⟨wz, hwz⟩ := hZ ζ hζ hζc hζT
  obtain ⟨K, hK⟩ := hΦ.lipschitzWith_of_hasCompactSupport hΦc (by simp)
  obtain ⟨B, hB⟩ := hΦ.continuous.bounded_above_of_compact_support hΦc
  have hB' : ∀ x, |Φ x| ≤ B := fun x => by simpa using hB x
  obtain ⟨φ, hφ⟩ := ca2_h10_mulLip hV wz hK hB'
  have hφf : ∀ x, φ.toH1Function.toFun x = Φ x * (u.toFun x - γ x) := by
    intro x
    rw [congrFun hφ x, hwz]
    show Φ x * (ζ x * (u.toFun x - γ x)) = _
    by_cases hx : x ∈ tsupport Φ
    · rw [(hζ1 x hx).self_of_nhds, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  refine ⟨φ, hφf, ?_⟩
  have hγ1 : ContDiff ℝ 1 (fun y => Φ y * γ y) := hΦ.mul (hγ.of_le (by simp))
  have hγc : HasCompactSupport (fun y => Φ y * γ y) := hΦc.mul_right
  set P1 := mulLip hV u hK hB' with hP1
  set P2 : H1Function V := H1Function.ofContDiff hV hγ1 hγc with hP2
  set P := P1 - P2 with hP
  have hfun : φ.toH1Function.toFun = P.toFun := by
    funext x
    rw [hφf x, hP, H1Function.sub_toFun]
    show _ = Φ x * u.toFun x - Φ x * γ x
    ring
  have hall := fun i => gradCoord_ae_eq_of_toFun_eq hV φ.toH1Function P hfun i
  have h2 := ae_all_iff.2 hall
  filter_upwards [h2] with x hx
  funext i
  rw [hx i, hP, H1Function.sub_grad]
  have g1 : P1.grad x i = Φ x * u.grad x i + u.toFun x * fderiv ℝ Φ x (basisVec i) := rfl
  have g2 : P2.grad x i = fderiv ℝ (fun y => Φ y * γ y) x (basisVec i) := rfl
  have hd1 : HasFDerivAt Φ (fderiv ℝ Φ x) x := ((hΦ.differentiable (by simp)) x).hasFDerivAt
  have hd2 : HasFDerivAt γ (fderiv ℝ γ x) x := ((hγ.differentiable (by simp)) x).hasFDerivAt
  have hd3 := hd1.mul hd2
  rw [show (fun y => Φ y * γ y) = Φ * γ from rfl, hd3.fderiv] at g2
  simp only [Pi.sub_apply, g1, g2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, p12_grad]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

end SuperdiffusionCLT.Section7
