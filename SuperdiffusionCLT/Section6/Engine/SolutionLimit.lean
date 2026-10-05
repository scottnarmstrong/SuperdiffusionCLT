/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers

/-!
# Limits of solutions

An `L²` limit of solutions whose gradients converge in `L²` is a solution (the two weak
identities pass to the limit by Cauchy–Schwarz and the bound on the coefficient field).
-/

@[expose] public section

open scoped ENNReal Topology

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter

variable {d : ℕ}

theorem e0e_memLp_of_tendsto {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {fm : ℕ → α → ℝ} {f : α → ℝ} (h : ∀ m, MemLp (fm m) 2 μ)
    (hc : Tendsto (fun m => eLpNorm (fun x => fm m x - f x) 2 μ) atTop (𝓝 0)) :
    MemLp f 2 μ := by
  obtain ⟨m, hm⟩ := (hc.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))).exists
  have h1 : MemLp (fun x => fm m x - f x) 2 μ := lt_trans hm ENNReal.one_lt_top
  have h2 : MemLp (fm m - fun x => fm m x - f x) 2 μ := (h m).sub h1
  have h3 : (fm m - fun x => fm m x - f x) = f := by funext x; simp
  rwa [h3] at h2


theorem e0e_tendsto_integral_mul {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {fm : ℕ → α → ℝ} {f h : α → ℝ} (hfm : ∀ m, MemLp (fm m) 2 μ) (hf : MemLp f 2 μ)
    (hh : MemLp h 2 μ)
    (hc : Tendsto (fun m => eLpNorm (fun x => fm m x - f x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, fm m x * h x ∂μ) atTop (𝓝 (∫ x, f x * h x ∂μ)) := by
  have hbound : ∀ m, ‖(∫ x, fm m x * h x ∂μ) - ∫ x, f x * h x ∂μ‖ₑ ≤
      eLpNorm (fun x => fm m x - f x) 2 μ * eLpNorm h 2 μ := by
    intro m
    have hd : MemLp (fun x => fm m x - f x) 2 μ := (hfm m).sub hf
    have hi1 : Integrable (fun x => fm m x * h x) μ := (hfm m).integrable_mul hh
    have hi2 : Integrable (fun x => f x * h x) μ := hf.integrable_mul hh
    have hsub : (∫ x, fm m x * h x ∂μ) - ∫ x, f x * h x ∂μ =
        ∫ x, (fm m x - f x) * h x ∂μ := by
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [sub_mul])
    rw [hsub]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hmul : MemLp ((fun x => fm m x - f x) * h) 1 μ := by
      have := hd.smul hh (r := 1)
      exact this
    have h1 : ∫⁻ x, ‖(fm m x - f x) * h x‖ₑ ∂μ =
        eLpNorm ((fun x => fm m x - f x) * h) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm hmul.aestronglyMeasurable]
      rfl
    rw [h1]
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hd.aestronglyMeasurable
      hh.aestronglyMeasurable
  have h2 : Tendsto (fun m => eLpNorm (fun x => fm m x - f x) 2 μ * eLpNorm h 2 μ) atTop
      (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const hc (Or.inr hh.eLpNorm_ne_top)
    simpa using this
  have h3 : Tendsto (fun m => ‖(∫ x, fm m x * h x ∂μ) - ∫ x, f x * h x ∂μ‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le) hbound
  exact tendsto_iff_enorm_sub_tendsto_zero.2 h3


theorem e0e_memLp_test {U : Set (Vec d)} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (i : Fin d) :
    MemLp φ 2 (volume.restrict U) ∧
      MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) 2 (volume.restrict U) := by
  refine ⟨hφ.continuous.memLp_of_hasCompactSupport hc, ?_⟩
  have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hcont.memLp_of_hasCompactSupport (hc.fderiv_apply ℝ (basisVec i))

theorem e0e_coeff_aesm {a : CoeffField d} {U : Set (Vec d)} {lam Lam : ℝ}
    (hE : IsEllipticFieldOn lam Lam U a) (i j : Fin d) :
    AEStronglyMeasurable (fun x => a x i j) (volume.restrict U) := by
  have hcm := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hE.1)
  refine hcm.aestronglyMeasurable.congr ?_
  exact (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hE)).2
    (Filter.Eventually.of_forall fun x hx => by simp [Function.comp_def, hx])

theorem e0e_memLp_coeff_mul {a : CoeffField d} {U : Set (Vec d)} {lam Lam : ℝ}
    (hE : IsEllipticFieldOn lam Lam U a) {w : Vec d → ℝ}
    (hw : MemLp w 2 (volume.restrict U)) (i j : Fin d) :
    MemLp (fun x => a x i j * w x) 2 (volume.restrict U) := by
  refine MemLp.of_le_mul (c := Lam) hw ((e0e_coeff_aesm hE i j).mul hw.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hE)).2
    (Filter.Eventually.of_forall fun x hx => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (abs_apply_le_of_isEllipticFieldOn hE hx i j) (norm_nonneg _)

theorem e0e_vecDot_expand (A : Mat d) (G w : Vec d) :
    vecDot (matVecMul A G) w = ∑ i, ∑ j, G j * (A i j * w i) := by
  unfold vecDot matVecMul
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem e0e_flux_integral {a : CoeffField d} {U : Set (Vec d)} {lam Lam : ℝ}
    (hE : IsEllipticFieldOn lam Lam U a) {G w : Vec d → Vec d}
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hw : ∀ i, MemLp (fun x => w x i) 2 (volume.restrict U)) :
    ∫ x in U, vecDot (matVecMul (a x) (G x)) (w x) ∂volume =
      ∑ i, ∑ j, ∫ x in U, G x j * (a x i j * w x i) ∂volume := by
  simp_rw [e0e_vecDot_expand]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    exact fun j _ => (hG j).integrable_mul (e0e_memLp_coeff_mul hE (hw i) i j)
  · intro i _
    exact integrable_finsetSum _ fun j _ => (hG j).integrable_mul (e0e_memLp_coeff_mul hE (hw i) i j)

/-- An `L²` limit of solutions, with `L²`-convergent gradients, is a solution. -/
theorem IsSolOn.of_tendsto {a : CoeffField d} {U : Set (Vec d)} (hU : IsOpen U)
    (hfin : volume U ≠ ⊤) (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam U a)
    {um : ℕ → Vec d → ℝ} {gm : ℕ → Vec d → Vec d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hsol : ∀ m, IsSolOn a U (um m) (gm m))
    (hu : Filter.Tendsto (fun m => eLpNorm (fun x => um m x - u x) 2 (volume.restrict U))
      Filter.atTop (nhds 0))
    (hg : ∀ i : Fin d, Filter.Tendsto
      (fun m => eLpNorm (fun x => gm m x i - g x i) 2 (volume.restrict U))
      Filter.atTop (nhds 0)) :
    IsSolOn a U u g := by
  have _ := hU
  have _ := hfin
  obtain ⟨lam, Lam, hE⟩ := hell
  choose v hv1 hv2 using hsol
  have hum : ∀ m, MemLp (um m) 2 (volume.restrict U) :=
    fun m => ((v m).toH1.memL2).ae_eq (hv1 m)
  have hgm : ∀ m i, MemLp (fun x => gm m x i) 2 (volume.restrict U) := fun m i =>
    (((v m).toH1.gradMemL2 i)).ae_eq ((hv2 m).mono fun x hx => by simp [hx])
  have hu_mem : MemLp u 2 (volume.restrict U) := e0e_memLp_of_tendsto hum hu
  have hg_mem : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U) := fun i =>
    e0e_memLp_of_tendsto (fun m => hgm m i) (hg i)
  have hweak : HasWeakGradientOn U u g := by
    intro i φ hφ hcpt _hsub
    obtain ⟨hφ2, hdφ⟩ := e0e_memLp_test (U := U) hφ hcpt i
    have h1 := e0e_tendsto_integral_mul hum hu_mem hdφ hu
    have h2 := (e0e_tendsto_integral_mul (fun m => hgm m i) (hg_mem i) hφ2 (hg i)).neg
    refine tendsto_nhds_unique h1 (h2.congr fun m => ?_)
    have hw := (v m).toH1.hasWeakGradient i φ hφ hcpt _hsub
    have e1 : ∫ x in U, um m x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        ∫ x in U, (v m).toH1.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume :=
      integral_congr_ae ((hv1 m).mono fun x hx => by simp [hx])
    have e2 : ∫ x in U, gm m x i * φ x ∂volume =
        ∫ x in U, (v m).toH1.grad x i * φ x ∂volume :=
      integral_congr_ae ((hv2 m).mono fun x hx => by simp [hx])
    rw [e1, e2, hw]
  have hsolen : IsSolenoidalOn U (fun x => matVecMul (a x) (g x)) := by
    intro ψ
    have hw : ∀ i, MemLp (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict U) :=
      fun i => ψ.toH1Function.gradMemL2 i
    have hlim : Tendsto (fun m => ∫ x in U, vecDot (matVecMul (a x) (gm m x))
        (ψ.toH1Function.grad x) ∂volume) atTop
        (𝓝 (∫ x in U, vecDot (matVecMul (a x) (g x)) (ψ.toH1Function.grad x) ∂volume)) := by
      simp_rw [e0e_flux_integral hE (fun j => hgm _ j) hw]
      rw [e0e_flux_integral hE hg_mem hw]
      refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
      exact e0e_tendsto_integral_mul (fun m => hgm m j) (hg_mem j)
        (e0e_memLp_coeff_mul hE (hw i) i j) (hg j)
    have hzero : ∀ m, ∫ x in U, vecDot (matVecMul (a x) (gm m x)) (ψ.toH1Function.grad x) ∂volume
        = 0 := by
      intro m
      rw [← ((v m).isHarmonic.2 ψ)]
      exact integral_congr_ae ((hv2 m).mono fun x hx => by simp only [hx])
    simp_rw [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  let H : H1Function U := ⟨u, g, hu_mem, hg_mem, hweak⟩
  exact ⟨⟨H, ⟨H, rfl⟩, hsolen⟩, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩

theorem e0e_isElliptic_one {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn 1 1 U (fun _ => (1 : Mat d)) := by
  classical
  have hmv : ∀ ξ : Vec d, matVecMul (1 : Mat d) ξ = ξ := fun ξ => by
    funext i
    simp [matVecMul, Matrix.one_apply]
  refine ⟨?_, fun x _ => ⟨one_pos, le_rfl, fun ξ => ?_, fun ξ => ?_⟩⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact Measurable.ite hU measurable_const measurable_const
  · simp [hmv, vecNormSq]
  · simp [hmv, vecNormSq]

/-- Witness: the constant zero sequence of solutions of the Laplace equation on the unit ball. -/
example : IsSolOn (fun _ => (1 : Mat d)) (Metric.ball (0 : Vec d) 1)
    (fun _ => 0) (fun _ => 0) := by
  refine IsSolOn.of_tendsto (um := fun _ _ => 0) (gm := fun _ _ => 0) Metric.isOpen_ball
    measure_ball_lt_top.ne ⟨1, 1, e0e_isElliptic_one Metric.isOpen_ball.measurableSet⟩
    (fun _ => ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩)
    ?_ (fun i => ?_)
  · simp
  · simp

end SuperdiffusionCLT.Section6
