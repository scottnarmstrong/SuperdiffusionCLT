/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorW2pC
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Limit
public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalE
public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2pF

/-!
# The cutoff of a weak solution of the Poisson equation

If `z ∈ H¹(U)` solves `-Δ z = h` weakly against `H¹₀(U)` and `χ` is smooth with compact support in
`U`, then `χ z` solves `-Δ (χ z) = χ h - 2 ∇z·∇χ - z Δχ` weakly against `H¹₀(U)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- The cutoff datum `χ h - 2 ∇z·∇χ - z Δχ`. -/
noncomputable def intW2p_cutData {U : Set (Vec d)} (z : H1Function U) (h χ : Vec d → ℝ)
    (x : Vec d) : ℝ :=
  χ x * h x - 2 * vecDot (z.grad x) (fun i ↦ fderiv ℝ χ x (basisVec i)) -
    z.toFun x * ∑ i, intW2p_dd χ i i x

theorem intW2p_memLp_mul_bdd_gen {μ : Measure (Vec d)} {p : ENNReal} {b f : Vec d → ℝ}
    (hb : AEStronglyMeasurable b μ) {M : ℝ} (hM : ∀ x, |b x| ≤ M) (hf : MemLp f p μ) :
    MemLp (fun x ↦ b x * f x) p μ := by
  refine hf.of_le_mul (c := M) (hb.mul hf.aestronglyMeasurable) (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

theorem intW2p_cutData_memLp {μ : Measure (Vec d)} {p : ENNReal} {U : Set (Vec d)}
    {z : H1Function U} {h χ : Vec d → ℝ} (hh : MemLp h p μ)
    (hgz : ∀ i, MemLp (fun x ↦ z.grad x i) p μ) (hzz : MemLp z.toFun p μ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemLp (intW2p_cutData z h χ) p μ := by
  have hd1 : ∀ i, Continuous fun x ↦ fderiv ℝ χ x (basisVec i) := fun i ↦
    (intW2p_d1_smooth hχ i).continuous
  obtain ⟨M1, hM1⟩ := hc.exists_bound_of_continuous hχ.continuous
  have hbd : ∀ i, ∃ M, ∀ x, |fderiv ℝ χ x (basisVec i)| ≤ M := fun i ↦ by
    obtain ⟨M, hM⟩ := (intW2p_d1_cs hc i).exists_bound_of_continuous (hd1 i)
    exact ⟨M, fun x ↦ by simpa only [Real.norm_eq_abs] using hM x⟩
  have hLb : ∃ M, ∀ x, |∑ i, intW2p_dd χ i i x| ≤ M := by
    obtain ⟨M, hM⟩ := (intW2p_cs_sum Finset.univ fun i _ ↦
      intW2p_dd_cs hc i i).exists_bound_of_continuous
      (continuous_finsetSum _ fun i _ ↦ (intW2p_dd_smooth hχ i i).continuous)
    exact ⟨M, fun x ↦ by simpa only [Real.norm_eq_abs] using hM x⟩
  obtain ⟨ML, hML⟩ := hLb
  have t1 : MemLp (fun x ↦ χ x * h x) p μ :=
    intW2p_memLp_mul_bdd_gen (b := χ) hχ.continuous.aestronglyMeasurable
      (M := M1) (fun x ↦ by simpa only [Real.norm_eq_abs] using hM1 x) hh
  have t2 : MemLp (fun x ↦ 2 * vecDot (z.grad x) (fun i ↦ fderiv ℝ χ x (basisVec i))) p μ := by
    have : MemLp (fun x ↦ vecDot (z.grad x) (fun i ↦ fderiv ℝ χ x (basisVec i))) p μ := by
      unfold vecDot
      refine memLp_finsetSum _ fun i _ ↦ ?_
      obtain ⟨M, hM⟩ := hbd i
      have := intW2p_memLp_mul_bdd_gen (b := fun x ↦ fderiv ℝ χ x (basisVec i))
        (hd1 i).aestronglyMeasurable hM (hgz i)
      refine this.ae_eq (Eventually.of_forall fun x ↦ ?_)
      simp only
      ring
    exact MeasureTheory.MemLp.const_mul this 2
  have t3 : MemLp (fun x ↦ z.toFun x * ∑ i, intW2p_dd χ i i x) p μ := by
    have := intW2p_memLp_mul_bdd_gen (b := fun x ↦ ∑ i, intW2p_dd χ i i x)
      (continuous_finsetSum _ fun i _ ↦ (intW2p_dd_smooth hχ i i).continuous).aestronglyMeasurable
      hML hzz
    refine this.ae_eq (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  exact (t1.sub t2).sub t3

/-- **The cutoff equation.** -/
theorem intW2p_cutoff_eq {U : Set (Vec d)} (hU : IsOpen U) {z : H1Function U} {h : Vec d → ℝ}
    (hh : MemLp h 2 (volume.restrict U))
    (hz : SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun _ ↦ (1 : Mat d)) U z h
      (fun _ ↦ 0)) {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    :
    SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun _ ↦ (1 : Mat d)) U
      (z.mulContDiffHasCompactSupport hχ hc) (intW2p_cutData z h χ) (fun _ ↦ 0) := by
  intro ψ
  set P := z.mulContDiffHasCompactSupport hχ hc with hP
  have hFL := intW2p_cutData_memLp (z := z) hh z.grad_memL2 z.memL2 hχ hc
  have hPg : ∀ x, P.grad x = fun i ↦ χ x * z.grad x i + z.toFun x * fderiv ℝ χ x (basisVec i) :=
    fun x ↦ by simp [hP]
  have key : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, vecDot (P.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i))) +
        ∫ x in U, (-(intW2p_cutData z h χ x)) * φ x = 0 := by
    intro φ hφ hφc hφs
    have hχφ : ContDiff ℝ (⊤ : ℕ∞) fun x ↦ χ x * φ x := hχ.mul hφ
    have hχφc : HasCompactSupport fun x ↦ χ x * φ x := hφc.mul_left
    have hχφs : tsupport (fun x ↦ χ x * φ x) ⊆ U := tsupport_mul_subset_right.trans hφs
    have e := hz (H10Function.ofContDiff hU hχφ hχφc hχφs)
    have hd1χ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun x ↦ fderiv ℝ χ x (basisVec i) := intW2p_d1_smooth hχ
    have hd1φ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun x ↦ fderiv ℝ φ x (basisVec i) := intW2p_d1_smooth hφ
    have hLχ : Continuous fun x ↦ ∑ i, intW2p_dd χ i i x :=
      continuous_finsetSum _ fun i _ ↦ (intW2p_dd_smooth hχ i i).continuous
    have hLχc : HasCompactSupport fun x ↦ ∑ i, intW2p_dd χ i i x :=
      intW2p_cs_sum Finset.univ fun i _ ↦ intW2p_dd_cs hc i i
    have hgz : ∀ i, MemLp (fun x ↦ z.grad x i) 2 (volume.restrict U) := z.grad_memL2
    -- integrability of the three sums
    have hI1 : ∀ i ∈ Finset.univ, Integrable (fun x ↦ z.grad x i *
        (χ x * fderiv ℝ φ x (basisVec i))) (volume.restrict U) := fun i _ ↦ by
      have := intW2p_integrable_mul (hgz i) (hχ.continuous.mul (hd1φ i).continuous)
        ((intW2p_d1_cs hφc i).mul_left)
      exact this
    have hI2 : ∀ i ∈ Finset.univ, Integrable (fun x ↦ z.grad x i *
        (φ x * fderiv ℝ χ x (basisVec i))) (volume.restrict U) := fun i _ ↦ by
      have := intW2p_integrable_mul (hgz i) (hφ.continuous.mul (hd1χ i).continuous)
        (hφc.mul_right)
      exact this
    have hI3 : ∀ i ∈ Finset.univ, Integrable (fun x ↦ z.toFun x *
        (fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i))) (volume.restrict U) :=
      fun i _ ↦ by
      have := intW2p_integrable_mul z.memL2 ((hd1χ i).continuous.mul (hd1φ i).continuous)
        ((intW2p_d1_cs hφc i).mul_left)
      exact this
    -- the three identities
    have e1 : ∫ x in U, vecDot (z.grad x) (fun i ↦ fderiv ℝ (fun y ↦ χ y * φ y) x (basisVec i)) =
        ∫ x in U, h x * (χ x * φ x) := by
      have := e
      simp only [intW2p_matVecMul_one] at this
      have h0 : ∀ x, vecDot ((0 : Vec d)) ((H10Function.ofContDiff hU hχφ hχφc hχφs).toH1Function.grad x) = 0 :=
        fun x ↦ by simp [vecDot]
      simp only [h0, integral_zero, add_zero] at this
      exact this
    have e2 : ∀ x, vecDot (z.grad x) (fun i ↦ fderiv ℝ (fun y ↦ χ y * φ y) x (basisVec i)) =
        (∑ i, z.grad x i * (χ x * fderiv ℝ φ x (basisVec i))) +
          ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)) := fun x ↦ by
      rw [← Finset.sum_add_distrib]
      unfold vecDot
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hd := (hχ.differentiable (by simp)) x
      have hd' := (hφ.differentiable (by simp)) x
      simp only [fderiv_fun_mul hd hd', add_apply, smul_apply, smul_eq_mul]
      ring
    have e3 : ∀ i, ∫ x in U, z.grad x i * (fderiv ℝ χ x (basisVec i) * φ x) =
        -∫ x in U, z.toFun x * (intW2p_dd χ i i x * φ x +
          fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i)) := fun i ↦ by
      rw [intW2p_ibp_h1 hU z i ((hd1χ i).of_le (by simp) |>.mul (hφ.of_le (by simp)))
        ((intW2p_d1_cs hc i).mul_right) ((tsupport_mul_subset_right).trans hφs)]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      have hd := ((hd1χ i).differentiable (by simp)) x
      have hd' := (hφ.differentiable (by simp)) x
      simp only [fderiv_fun_mul hd hd', add_apply, smul_apply, smul_eq_mul]
      rw [intW2p_dd_eq_fderiv]
      ring
    have hs1 : ∫ x in U, ∑ i, z.grad x i * (χ x * fderiv ℝ φ x (basisVec i)) =
        ∑ i, ∫ x in U, z.grad x i * (χ x * fderiv ℝ φ x (basisVec i)) :=
      integral_finsetSum _ hI1
    have hs2 : ∫ x in U, ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)) =
        ∑ i, ∫ x in U, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)) :=
      integral_finsetSum _ hI2
    have hs3 : ∫ x in U, ∑ i, z.toFun x * (fderiv ℝ χ x (basisVec i) *
        fderiv ℝ φ x (basisVec i)) = ∑ i, ∫ x in U, z.toFun x * (fderiv ℝ χ x (basisVec i) *
        fderiv ℝ φ x (basisVec i)) := integral_finsetSum _ hI3
    have hS1 : Integrable (fun x ↦ ∑ i, z.grad x i * (χ x * fderiv ℝ φ x (basisVec i)))
        (volume.restrict U) := integrable_finsetSum _ hI1
    have hS2 : Integrable (fun x ↦ ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)))
        (volume.restrict U) := integrable_finsetSum _ hI2
    have hS3 : Integrable (fun x ↦ ∑ i, z.toFun x * (fderiv ℝ χ x (basisVec i) *
        fderiv ℝ φ x (basisVec i))) (volume.restrict U) := integrable_finsetSum _ hI3
    -- (a)
    have ea : ∫ x in U, vecDot (P.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i)) =
        (∫ x in U, ∑ i, z.grad x i * (χ x * fderiv ℝ φ x (basisVec i))) +
        ∫ x in U, ∑ i, z.toFun x * (fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i)) := by
      rw [← integral_add hS1 hS3]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [hPg, vecDot, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    -- (b)
    have hJ1 : Integrable (fun x ↦ h x * (χ x * φ x)) (volume.restrict U) :=
      intW2p_integrable_mul hh (hχ.continuous.mul hφ.continuous) hχφc
    have eb : (∫ x in U, ∑ i, z.grad x i * (χ x * fderiv ℝ φ x (basisVec i))) +
        (∫ x in U, ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i))) =
        ∫ x in U, h x * (χ x * φ x) := by
      rw [← integral_add hS1 hS2, ← e1]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ (e2 x).symm)
    -- (c)
    have hL3 : Integrable (fun x ↦ z.toFun x * ((∑ i, intW2p_dd χ i i x) * φ x))
        (volume.restrict U) :=
      intW2p_integrable_mul z.memL2 (hLχ.mul hφ.continuous) hLχc.mul_right
    have hI4 : ∀ i ∈ Finset.univ, Integrable (fun x ↦ z.toFun x * (intW2p_dd χ i i x * φ x +
          fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i))) (volume.restrict U) :=
      fun i _ ↦ by
      have := intW2p_integrable_mul z.memL2
        (((intW2p_dd_smooth hχ i i).continuous.mul hφ.continuous).add
          ((hd1χ i).continuous.mul (hd1φ i).continuous))
        (((intW2p_dd_cs hc i i).mul_right).add ((intW2p_d1_cs hφc i).mul_left))
      exact this
    have ec : (∫ x in U, ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i))) =
        -(∫ x in U, z.toFun x * ((∑ i, intW2p_dd χ i i x) * φ x)) -
          ∫ x in U, ∑ i, z.toFun x * (fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i)) := by
      rw [hs2, hs3]
      have h1 : ∀ i, ∫ x in U, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)) =
          -∫ x in U, z.toFun x * (intW2p_dd χ i i x * φ x +
            fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i)) := fun i ↦ by
        rw [← e3 i]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
      simp only [h1, Finset.sum_neg_distrib]
      have h2 : ∫ x in U, z.toFun x * ((∑ i, intW2p_dd χ i i x) * φ x) =
          ∑ i, ∫ x in U, z.toFun x * (intW2p_dd χ i i x * φ x) := by
        rw [← integral_finsetSum _ fun i _ ↦ by
          have := intW2p_integrable_mul z.memL2
            ((intW2p_dd_smooth hχ i i).continuous.mul hφ.continuous)
            ((intW2p_dd_cs hc i i).mul_right)
          exact this]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by
          simp only [Finset.sum_mul, Finset.mul_sum])
      have h3 : ∀ i, ∫ x in U, z.toFun x * (intW2p_dd χ i i x * φ x +
          fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i)) =
          (∫ x in U, z.toFun x * (intW2p_dd χ i i x * φ x)) +
          ∫ x in U, z.toFun x * (fderiv ℝ χ x (basisVec i) * fderiv ℝ φ x (basisVec i)) :=
        fun i ↦ by
          rw [← integral_add (by
            have := intW2p_integrable_mul z.memL2
              ((intW2p_dd_smooth hχ i i).continuous.mul hφ.continuous)
              ((intW2p_dd_cs hc i i).mul_right)
            exact this) (hI3 i (Finset.mem_univ i))]
          exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
      simp only [h3, Finset.sum_add_distrib, h2]
      ring
    -- (d)
    have hDφ : Integrable (fun x ↦ ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)))
        (volume.restrict U) := hS2
    have ed : ∫ x in U, (-(intW2p_cutData z h χ x)) * φ x =
        -(∫ x in U, h x * (χ x * φ x)) +
          2 * (∫ x in U, ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i))) +
          ∫ x in U, z.toFun x * ((∑ i, intW2p_dd χ i i x) * φ x) := by
      have : ∀ x, (-(intW2p_cutData z h χ x)) * φ x =
          (-(h x * (χ x * φ x)) +
            2 * (∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)))) +
          z.toFun x * ((∑ i, intW2p_dd χ i i x) * φ x) := fun x ↦ by
        have hD : ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)) =
            vecDot (z.grad x) (fun i ↦ fderiv ℝ χ x (basisVec i)) * φ x := by
          unfold vecDot
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
        rw [hD]
        unfold intW2p_cutData
        ring
      simp_rw [this]
      have i1 : Integrable (fun x ↦ -(h x * (χ x * φ x)) +
          2 * ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i))) (volume.restrict U) :=
        hJ1.neg.add (hDφ.const_mul 2)
      have i2 : Integrable (fun x ↦ -(h x * (χ x * φ x))) (volume.restrict U) := hJ1.neg
      have i3 : Integrable (fun x ↦ 2 * ∑ i, z.grad x i * (φ x * fderiv ℝ χ x (basisVec i)))
          (volume.restrict U) := hDφ.const_mul 2
      rw [integral_add i1 hL3, integral_add i2 i3, integral_neg, integral_const_mul]
    rw [ea, ed]
    linarith only [eb, ec]
  have hmain := intW2p_h10_of_smooth (W := P.grad) (s := fun x ↦ -(intW2p_cutData z h χ x))
    P.grad_memL2 hFL.neg key ψ
  simp only [intW2p_matVecMul_one]
  have h0 : ∀ x, vecDot ((0 : Vec d)) (ψ.toH1Function.grad x) = 0 := fun x ↦ by simp [vecDot]
  simp only [h0, integral_zero, add_zero]
  have : ∫ x in U, (-(intW2p_cutData z h χ x)) * ψ.toH1Function.toFun x =
      -∫ x in U, intW2p_cutData z h χ x * ψ.toH1Function.toFun x := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  rw [this] at hmain
  linarith only [hmain]

instance intW2p_finite_open (Q : TriadicCube d) : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isBounded_openCubeSet Q).measure_lt_top⟩

/-- **The cutoff solution has `L^P` Hessian.**  On the origin cube of scale `3^m`, a weak
solution `z` of `-Δz = h` with `h`, `∇z`, `z` in `L^P`, `P > d`, has a cutoff `χ z` (with
`χ = 1` on the concentric box of half-side `3^m/4`) in `H¹₀` with a weak Hessian in `L^P`. -/
theorem intW2p_core [NeZero d] (hd : 2 ≤ d) (m : ℤ) {P : ℝ} (hP : (d : ℝ) < P)
    {z : H1Function (openCubeSet (originCube d m))} {h : Vec d → ℝ}
    (hz : SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun _ ↦ (1 : Mat d))
      (openCubeSet (originCube d m)) z h (fun _ ↦ 0))
    (hh : MemLp h (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d m)))
    (hgz : ∀ i, MemLp (fun x ↦ z.grad x i) (ENNReal.ofReal P)
      (normalizedCubeMeasure (originCube d m)))
    (hzz : MemLp z.toFun (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d m))) :
    ∃ (χ : Vec d → ℝ) (w : H10Function (openCubeSet (originCube d m)))
      (H : HasWeakHessianOn (openCubeSet (originCube d m)) w.toH1Function),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ openCubeSet (originCube d m) ∧
      (∀ x, (∀ i, |x i| ≤ (3 : ℝ) ^ m / 4) → χ x = 1) ∧
      (∀ x, w.toH1Function.toFun x = χ x * z.toFun x) ∧
      (∀ x, w.toH1Function.grad x =
        fun i ↦ χ x * z.grad x i + z.toFun x * fderiv ℝ χ x (basisVec i)) ∧
      MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) (ENNReal.ofReal P)
        (normalizedCubeMeasure (originCube d m)) := by
  have hU : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _
  have hℓ : 0 < cubeScaleFactor (originCube d m) := SuperdiffusionCLT.Section7.cubeScaleFactor_pos' (originCube d m)
  have hℓ' : cubeScaleFactor (originCube d m) = (3 : ℝ) ^ m := rfl
  set χ : Vec d → ℝ := SuperdiffusionCLT.Section7.p12_cut (0 : Vec d) (cubeScaleFactor (originCube d m)) 0 0
    with hχdef
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := SuperdiffusionCLT.Section7.p12_cut_contDiff _ _ _ _
  have hc : HasCompactSupport χ :=
    SuperdiffusionCLT.Section7.p12_cut_hasCompactSupport _ hℓ _ _
  have hsub : tsupport χ ⊆ (openCubeSet (originCube d m)) := by
    intro x hx
    have h1 := SuperdiffusionCLT.Section7.p12_cut_zero_subset (0 : Vec d) hℓ 0 hx
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have := abs_lt.mp (by simpa only [Pi.zero_apply, sub_zero] using h1 i)
    rw [hℓ'] at this
    constructor <;> linarith only [this.1, this.2]
  have hone : ∀ x, (∀ i, |x i| ≤ (3 : ℝ) ^ m / 4) → χ x = 1 := fun x hx ↦
    SuperdiffusionCLT.Section7.p12_cut_last (0 : Vec d) hℓ 0 (fun i ↦ by
      simpa only [Pi.zero_apply, sub_zero, hℓ'] using hx i)
  have hP2 : (2 : ℝ) < P := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this, hP]
  have hh2 : MemLp h 2 (volume.restrict (openCubeSet (originCube d m))) :=
    (SuperdiffusionCLT.Section7.memLp_restrict_of_normalized (originCube d m) hh).mono_exponent (by
      rw [← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal hP2.le)
  have hweak := intW2p_cutoff_eq hU hh2 hz hχ hc
  obtain ⟨w, hw⟩ := SuperdiffusionCLT.Section7.exists_h10_of_compact hU (z.mulContDiffHasCompactSupport hχ hc) hsub
    hc.isCompact (fun x _ hxK ↦ by
      simp [image_eq_zero_of_notMem_tsupport hxK])
  have hFp : MemLp (intW2p_cutData z h χ) (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d m)) :=
    intW2p_cutData_memLp hh hgz hzz hχ hc
  have hp2 : (2 : ℝ≥0∞) < ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_ofNat]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hP2])).2 hP2
  obtain ⟨ε, C, hε, hC, hmain⟩ := SuperdiffusionCLT.Section7.flatW2p_scalar hd hp2
    ENNReal.ofReal_lt_top
  obtain ⟨H, hHp, -⟩ := hmain m (fun _ ↦ (1 : Mat d)) 0 (fun i j ↦ contDiff_const)
    (fun x _ i j ↦ by simp [hε.le]) (fun x _ i j k ↦ by simp)
    (by simpa only [zero_mul] using hε.le) (intW2p_cutData z h χ) hFp w (by
      intro φ
      have := hweak φ
      rw [← hw] at this
      exact this)
  refine ⟨χ, w, H, hχ, hc, hsub, hone, ?_, ?_, hHp⟩
  · intro x
    rw [hw]
    simp
  · intro x
    rw [hw]
    simp

end SuperdiffusionCLT.Section8
