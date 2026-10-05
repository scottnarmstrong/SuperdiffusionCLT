/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2C
public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalE

/-!
# Stage 1: `∇u ∈ L^P` and `u ∈ C¹` for a bounded solution on a cube

A bounded continuous `H¹` solution of `-∇·(a∇u) + μu = g` on the origin cube of scale `3^m`, with
`a = νId + skew` of class `C²`, has `∇u ∈ L^P` on the cube of scale `3^(m-1)` for every `P < ∞`
(the flux form `-Δu = f/ν - ∇·((u/ν) c)` with a bounded flux), and then `u` is `C¹` on the box
`|xᵢ| < 3^(m-1)/4` with a continuous gradient having `L^P` weak derivatives.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_memLp_cube_mono {Q Q' : TriadicCube d} {B : Set (Vec d)} {f : Vec d → ℝ}
    {p : ENNReal} (hB : MeasurableSet B) (hsub : openCubeSet Q' ⊆ B)
    (hQ : openCubeSet Q' ⊆ openCubeSet Q)
    (h : MemLp f p ((normalizedCubeMeasure Q).restrict B)) :
    MemLp f p (normalizedCubeMeasure Q') := by
  refine SuperdiffusionCLT.Section7.memLp_normalized_of_restrict Q' ?_
  rw [SuperdiffusionCLT.Section7.cubeScalar_normalizedCubeMeasure_eq_smul,
    Measure.restrict_smul] at h
  have hc0 : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos Q))).ne'
  refine MemLp.of_measure_le_smul (c := (ENNReal.ofReal (cubeVolume Q)⁻¹)⁻¹)
    (ENNReal.inv_ne_top.2 hc0) ?_ h
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul,
    Measure.restrict_restrict hB]
  exact Measure.restrict_mono (Set.subset_inter hsub hQ) le_rfl

theorem intC2_memLp_cubeBdd {Q : TriadicCube d} {f : Vec d → ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (openCubeSet Q))) {M : ℝ}
    (hM : ∀ x ∈ openCubeSet Q, |f x| ≤ M) (p : ENNReal) : MemLp f p (normalizedCubeMeasure Q) :=
  SuperdiffusionCLT.Section7.memLp_normalized_of_restrict Q
    (intC2_memLp_bdd (isBounded_openCubeSet Q) (isOpen_openCubeSet Q).measurableSet hmeas hM p)

theorem intC2_memLp_cubeBdd_vec {Q : TriadicCube d} {F : Vec d → Vec d}
    (hmeas : AEStronglyMeasurable F (volume.restrict (openCubeSet Q))) {M : ℝ}
    (hM : ∀ x ∈ openCubeSet Q, ‖F x‖ ≤ M) (p : ENNReal) : MemLp F p (normalizedCubeMeasure Q) := by
  have hprob := SuperdiffusionCLT.Section7.p12_isProb Q
  rw [SuperdiffusionCLT.Section7.cubeScalar_normalizedCubeMeasure_eq_smul] at hprob ⊢
  refine MemLp.of_bound (hmeas.smul_measure _) M ?_
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx using hM x hx

theorem intC2_drift_norm_bound {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j)
    {U : Set (Vec d)} (hb : Bornology.IsBounded U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ U, ‖intW2p_drift a x‖ ≤ M := by
  obtain ⟨M, hM⟩ := intW2p_drift_bound ha hb
  refine ⟨max M 0, le_max_right _ _, fun x hx ↦ ?_⟩
  exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i ↦ by
    simpa only [Real.norm_eq_abs] using (hM x hx i).trans (le_max_left _ _)

theorem intC2_box_quarter_sub (m : ℤ) : openCubeSet (originCube d (m - 1)) ⊆
    intC2_box d ((3 : ℝ) ^ m / 4) := by
  intro x hx i
  rw [mem_openCubeSet_originCube_iff] at hx
  have h := hx i
  have e : (3 : ℝ) ^ (m - 1) = 3 ^ m / 3 := by rw [zpow_sub_one₀ (by norm_num)]; ring
  have hp : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [abs_lt]
  rw [e] at h
  constructor <;> linarith only [h.1, h.2, hp]

/-- **The gradient is `L^P` on the cube of scale `3^(m-1)`.** -/
theorem intC2_gradLp [NeZero d] (hd : 2 ≤ d) (m : ℤ) {P : ℝ} (hP : 2 ≤ P) {a : CoeffField d}
    {nu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {mu : ℝ} {g : Vec d → ℝ} (hg : Continuous g)
    {M : ℝ} {u : H1Function (openCubeSet (originCube d m))}
    (hu : intC2_Weak a mu g (openCubeSet (originCube d m)) u)
    (hcont : ContinuousOn u.toFun (openCubeSet (originCube d m)))
    (hbd : ∀ x ∈ openCubeSet (originCube d m), |u.toFun x| ≤ M) (i : Fin d) :
    MemLp (fun x ↦ u.grad x i) (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d (m - 1))) := by
  have hU : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _
  have hb : Bornology.IsBounded (openCubeSet (originCube d m)) := isBounded_openCubeSet _
  have hsf := intC2_scalarForced hU hb ha hg hu
  have flux := intW2p_laplace_flux hU hb hnu hsk ha hsf
  obtain ⟨ε, C, hε, hC, H⟩ := SuperdiffusionCLT.Section7.localW1p_interior_domain hd hP
  obtain ⟨Mg, hMg⟩ := intC2_bound_on hb hg
  obtain ⟨Mc, hMc0, hMc⟩ := intC2_drift_norm_bound ha hb
  have hum : AEStronglyMeasurable u.toFun (volume.restrict (openCubeSet (originCube d m))) :=
    hcont.aestronglyMeasurable hU.measurableSet
  have hfm0 : AEStronglyMeasurable (fun x ↦ g x - mu * u.toFun x)
      (volume.restrict (openCubeSet (originCube d m))) :=
    hg.aestronglyMeasurable.sub (hum.const_mul mu)
  have hum2 : AEStronglyMeasurable (fun x ↦ u.toFun x / nu)
      (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [div_eq_mul_inv] using hum.mul_const nu⁻¹
  have hfm : AEStronglyMeasurable (fun x ↦ (g x - mu * u.toFun x) / nu)
      (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [div_eq_mul_inv] using hfm0.mul_const nu⁻¹
  have hfb : ∀ x ∈ openCubeSet (originCube d m), |(g x - mu * u.toFun x) / nu| ≤
      (Mg + |mu| * M) / nu := fun x hx ↦ by
    rw [abs_div, abs_of_pos hnu]
    refine div_le_div_of_nonneg_right ?_ hnu.le
    calc |g x - mu * u.toFun x| ≤ |g x| + |mu * u.toFun x| := abs_sub _ _
      _ ≤ Mg + |mu| * M := by
        rw [abs_mul]
        exact add_le_add (hMg x hx) (mul_le_mul_of_nonneg_left (hbd x hx) (abs_nonneg _))
  have hGm : AEStronglyMeasurable (fun x ↦ (u.toFun x / nu) • intW2p_drift a x)
      (volume.restrict (openCubeSet (originCube d m))) :=
    hum2.smul (continuous_pi fun i ↦
      (intW2p_drift_contDiff ha i).continuous).aestronglyMeasurable
  have hGb : ∀ x ∈ openCubeSet (originCube d m), ‖(u.toFun x / nu) • intW2p_drift a x‖ ≤
      (|M| / nu) * Mc := fun x hx ↦ by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hnu]
    exact mul_le_mul (div_le_div_of_nonneg_right ((hbd x hx).trans (le_abs_self M)) hnu.le)
      (hMc x hx) (norm_nonneg _) (by positivity)
  have hmain := H (openCubeSet (originCube d m)) (originCube d m) (fun _ ↦ (1 : Mat d)) hU
    subset_rfl (fun i j ↦ aestronglyMeasurable_const) (fun x _ i j ↦ by simp [hε.le])
    (fun x ↦ (g x - mu * u.toFun x) / nu) (fun x ↦ (u.toFun x / nu) • intW2p_drift a x) u flux
    (intC2_memLp_cubeBdd hfm hfb 2) (intC2_memLp_cubeBdd hfm hfb _)
    (intC2_memLp_cubeBdd_vec hGm hGb _)
  have hv := hmain.1
  have hcomp : MemLp (fun x ↦ u.grad x i) (ENNReal.ofReal P)
      ((normalizedCubeMeasure (originCube d m)).restrict
        (SuperdiffusionCLT.Section7.p12_box
          (fun i ↦ ((originCube d m).index i : ℝ) * cubeScaleFactor (originCube d m))
          (cubeScaleFactor (originCube d m) / 4))) :=
    hv.of_le ((continuous_apply i).comp_aestronglyMeasurable hv.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ norm_le_pi_norm (u.grad x) i)
  refine intC2_memLp_cube_mono
    (SuperdiffusionCLT.Section7.p12_box_measurable _ _) ?_ ?_ hcomp
  · intro x hx j
    have := intC2_box_quarter_sub m hx j
    show |x j - ((originCube d m).index j : ℝ) * cubeScaleFactor (originCube d m)| ≤
      cubeScaleFactor (originCube d m) / 4
    have h0 : ((originCube d m).index j : ℝ) = 0 := by simp [originCube]
    rw [h0, zero_mul, sub_zero]
    exact this.le
  · intro x hx
    exact intC2_box_subset_cube m (intC2_box_quarter_sub m hx)

theorem intC2_memLp_mul_bdd_cube {Q : TriadicCube d} {b f : Vec d → ℝ} {p : ENNReal}
    (hb : AEStronglyMeasurable b (normalizedCubeMeasure Q)) {M : ℝ}
    (hM : ∀ x ∈ openCubeSet Q, |b x| ≤ M) (hf : MemLp f p (normalizedCubeMeasure Q)) :
    MemLp (fun x ↦ b x * f x) p (normalizedCubeMeasure Q) := by
  refine hf.of_le_mul (c := M) (hb.mul hf.aestronglyMeasurable) ?_
  rw [SuperdiffusionCLT.Section7.cubeScalar_normalizedCubeMeasure_eq_smul]
  refine Measure.ae_smul_measure ?_ _
  filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)

theorem intC2_cube_sub (m : ℤ) : openCubeSet (originCube d (m - 1)) ⊆
    openCubeSet (originCube d m) := fun _ hx ↦
  intC2_box_subset_cube m (intC2_box_quarter_sub m hx)

/-- **Stage 1.**  `u` is `C¹` on the box `|xᵢ| < 3^(m-1)/4` with a continuous gradient `G` whose
weak derivatives `Hs` lie in `L^P`. -/
theorem intC2_stage1 [NeZero d] (hd : 2 ≤ d) (m : ℤ) {P : ℝ} (hP : (d : ℝ) < P)
    {a : CoeffField d} {nu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {mu : ℝ} {g : Vec d → ℝ} (hg : Continuous g)
    {M : ℝ} {u : H1Function (openCubeSet (originCube d m))}
    (hu : intC2_Weak a mu g (openCubeSet (originCube d m)) u)
    (hcont : ContinuousOn u.toFun (openCubeSet (originCube d m)))
    (hbd : ∀ x ∈ openCubeSet (originCube d m), |u.toFun x| ≤ M) :
    ∃ (G : Fin d → Vec d → ℝ) (Hs : Fin d → Fin d → Vec d → ℝ),
      (∀ i, ContinuousOn (G i) (intC2_box d ((3 : ℝ) ^ (m - 1) / 4))) ∧
      (∀ x ∈ intC2_box d ((3 : ℝ) ^ (m - 1) / 4), HasFDerivAt u.toFun (intC2_cand G x) x) ∧
      (∀ i, (G i) =ᵐ[volume.restrict (intC2_box d ((3 : ℝ) ^ (m - 1) / 4))]
        fun x ↦ u.grad x i) ∧
      (∀ i j, HasWeakPartialDerivOn (intC2_box d ((3 : ℝ) ^ (m - 1) / 4)) j (G i) (Hs i j)) ∧
      (∀ i j, MemLp (Hs i j) (ENNReal.ofReal P)
        (volume.restrict (intC2_box d ((3 : ℝ) ^ (m - 1) / 4)))) := by
  have hP2 : (2 : ℝ) ≤ P := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this, hP]
  have hsub := intC2_cube_sub (d := d) m
  have hU1 : IsOpen (openCubeSet (originCube d (m - 1))) := isOpen_openCubeSet _
  have hb1 : Bornology.IsBounded (openCubeSet (originCube d (m - 1))) := isBounded_openCubeSet _
  set u1 := u.restrict hU1 hsub with hu1
  have hw1 : intC2_Weak a mu g _ u1 := hu.restrict hU1 hsub
  have hsf := intC2_scalarForced hU1 hb1 ha hg hw1
  have hz := intW2p_laplace_scalar hU1 hb1 hnu hsk ha hsf
  obtain ⟨Mg, hMg⟩ := intC2_bound_on hb1 hg
  obtain ⟨Mc, hMc0, hMc⟩ := intC2_drift_norm_bound ha hb1
  have hum : AEStronglyMeasurable u.toFun (volume.restrict (openCubeSet (originCube d (m - 1)))) :=
    (hcont.mono hsub).aestronglyMeasurable hU1.measurableSet
  have hgrad : ∀ i, MemLp (fun x ↦ u1.grad x i) (ENNReal.ofReal P)
      (normalizedCubeMeasure (originCube d (m - 1))) := fun i ↦
    intC2_gradLp hd m hP2 hnu hsk ha hg hu hcont hbd i
  have hzz : MemLp u1.toFun (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d (m - 1))) :=
    intC2_memLp_cubeBdd hum (fun x hx ↦ hbd x (hsub hx)) _
  have hh : MemLp (fun x ↦ ((g x - mu * u1.toFun x) - vecDot (intW2p_drift a x) (u1.grad x)) / nu)
      (ENNReal.ofReal P) (normalizedCubeMeasure (originCube d (m - 1))) := by
    have h1 : MemLp (fun x ↦ g x - mu * u1.toFun x) (ENNReal.ofReal P)
        (normalizedCubeMeasure (originCube d (m - 1))) :=
      intC2_memLp_cubeBdd (hg.aestronglyMeasurable.sub (hum.const_mul mu))
        (M := Mg + |mu| * M) (fun x hx ↦ by
          calc |g x - mu * u1.toFun x| ≤ |g x| + |mu * u1.toFun x| := abs_sub _ _
            _ ≤ Mg + |mu| * M := by
              rw [abs_mul]
              exact add_le_add (hMg x hx) (mul_le_mul_of_nonneg_left (hbd x (hsub hx))
                (abs_nonneg _))) _
    have h2 : MemLp (fun x ↦ vecDot (intW2p_drift a x) (u1.grad x)) (ENNReal.ofReal P)
        (normalizedCubeMeasure (originCube d (m - 1))) := by
      unfold vecDot
      refine memLp_finsetSum _ fun i _ ↦ ?_
      exact intC2_memLp_mul_bdd_cube (b := fun x ↦ intW2p_drift a x i)
        (intW2p_drift_contDiff ha i).continuous.aestronglyMeasurable
        (M := Mc) (fun x hx ↦ by
          simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (intW2p_drift a x) i).trans
            (hMc x hx)) (hgrad i)
    have := (h1.sub h2).const_mul (1 / nu)
    refine this.ae_eq (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply]
    ring
  exact intC2_core_c1 hd (m - 1) hP hz hh hgrad hzz (hcont.mono hsub)

end SuperdiffusionCLT.Section8
