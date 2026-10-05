/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.AverageNorms
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputsB
public import Homogenization.Sobolev.Foundations.PoincareW1p.Dilation
public import Homogenization.Sobolev.Foundations.PoincareW1p.Translation
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1
public import Homogenization.Sobolev.W1p.H1GradientUpgrade

/-!
# The `L⁴` Poincaré inequality on a triadic cube

The scale-correct finite-`p` Poincaré estimate on the open cube `openCubeSet Q`, obtained from the
unit centred cube by dilation and translation (as for the `H¹` estimate
`scaledTranslatedCubeMeanZeroH1CoerciveEstimate`), and its sub-average form for `W^{1,4}`
functions.  This is the Poincaré inequality on the subcubes `z + cu_n` used in `e.crude.Fz.bound`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal Pointwise

noncomputable section

variable {d : ℕ}

/-- Transport a `W^{1,p}` witness along an equality of domains. -/
private def castW1p {U V : Set (Vec d)} {p : ENNReal} (h : U = V) (u : W1pFunction U p) :
    W1pFunction V p := by
  subst h
  exact u

private theorem subAverage_castW1p {U V : Set (Vec d)} {p : ENNReal} (h : U = V)
    (u : W1pFunction U p) :
    (castW1p h u).subAverageLpSeminorm = u.subAverageLpSeminorm := by
  subst h
  rfl

private theorem gradSum_castW1p {U V : Set (Vec d)} {p : ENNReal} (h : U = V)
    (u : W1pFunction U p) :
    (castW1p h u).gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum := by
  subst h
  rfl

/-- **The sub-average Poincaré inequality on every triadic cube**, with the scale factor
`3^{scale}` and one constant for the whole family of cubes. -/
theorem cube_subAverage_poincare [NeZero d] {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (u : W1pFunction (openCubeSet Q) (ENNReal.ofReal q)),
        u.subAverageLpSeminorm ≤ (C * cubeScaleFactor Q) * u.gradientCoordLpSeminormSum := by
  obtain ⟨C, hC0, hC⟩ :=
    W1pFunction.exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain
      (U := openCubeSet (originCube d 0))
      (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)) hq
  refine ⟨C, hC0, fun Q u => ?_⟩
  set a : ℝ := cubeScaleFactor Q with ha_def
  have ha : 0 < a := by
    simp only [ha_def, cubeScaleFactor]
    positivity
  have hp_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  set z : Vec d := triadicCubeShift Q with hz
  have hset : openCubeSet Q = translateSet z (a • openCubeSet (originCube d 0)) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
      openCubeSet_originCube_eq_smul_unit d Q.scale]
    rfl
  have hset2 : translateSet (-z) (translateSet z (a • openCubeSet (originCube d 0))) =
      a • openCubeSet (originCube d 0) := by
    rw [translateSet_translateSet]
    simp
  let u1 := castW1p hset u
  let u2 := u1.translate (-z)
  let u3 := castW1p hset2 u2
  let u0 := u3.unscale ha
  have hsub : u3.subAverageLpSeminorm = u.subAverageLpSeminorm := by
    rw [subAverage_castW1p, W1pFunction.subAverageLpSeminorm_translate_eq, subAverage_castW1p]
  have hgr : u3.gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum := by
    rw [gradSum_castW1p, W1pFunction.gradientCoordLpSeminormSum_translate_eq, gradSum_castW1p]
  have hbase := hC u0
  have hv : u0.subAverageLpSeminorm =
      W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ * u3.subAverageLpSeminorm :=
    W1pFunction.subAverageLpSeminorm_unscale_eq ha hp_top u3
  have hg : u0.gradientCoordLpSeminormSum =
      a * W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
        u3.gradientCoordLpSeminormSum :=
    W1pFunction.gradientCoordLpSeminormSum_unscale_eq ha hp_top u3
  have hfac : 0 < W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ :=
    W1pFunction.dilationLpFactor_pos d (ENNReal.ofReal q) (inv_pos.mpr ha)
  rw [hv, hg, hsub, hgr] at hbase
  have h2 : W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ * u.subAverageLpSeminorm ≤
      W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
        ((C * a) * u.gradientCoordLpSeminormSum) := by
    calc _ ≤ _ := hbase
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hfac).mp h2

/-- The scalar sub-average Poincaré inequality for `W^{1,4}`, in the normalized `L̲⁴` norms. -/
theorem eLpNorm_sub_integralAverage_le [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (v : W1pFunction (openCubeSet Q) (ENNReal.ofReal 4)),
        eLpNorm (fun x => v.toFun x - integralAverage (openCubeSet Q) v.toFun) 4
            (normalizedCubeMeasure Q) ≤
          ENNReal.ofReal (C * cubeScaleFactor Q) *
            ∑ j : Fin d, eLpNorm (fun x => v.grad x j) 4 (normalizedCubeMeasure Q) := by
  obtain ⟨C, hC0, hC⟩ := cube_subAverage_poincare (d := d) (q := 4) (by norm_num)
  refine ⟨C, hC0, fun Q v => ?_⟩
  have h4 : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by simp
  have hs : 0 ≤ C * cubeScaleFactor Q := mul_nonneg hC0 (by simp only [cubeScaleFactor]; positivity)
  have hmeasG : AEStronglyMeasurable (fun x => v.toFun x - integralAverage (openCubeSet Q) v.toFun)
      (volume.restrict (openCubeSet Q)) :=
    v.memLp.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hG4 : eLpNorm (fun x => v.toFun x - integralAverage (openCubeSet Q) v.toFun) (ENNReal.ofReal 4)
      (volume.restrict (openCubeSet Q)) ≠ ∞ :=
    (v.memLp.sub (memLp_const _)).eLpNorm_ne_top
  have hgrad4 : ∀ j : Fin d, eLpNorm (fun x => v.grad x j) (ENNReal.ofReal 4)
      (volume.restrict (openCubeSet Q)) ≠ ∞ := fun j => (v.gradMemLp j).eLpNorm_ne_top
  have hP := hC Q v
  unfold W1pFunction.subAverageLpSeminorm W1pFunction.gradientCoordLpSeminormSum
    W1pFunction.gradCoordLpSeminorm at hP
  have hP' : eLpNorm (fun x => v.toFun x - integralAverage (openCubeSet Q) v.toFun)
        (ENNReal.ofReal 4) (volume.restrict (openCubeSet Q)) ≤
      ENNReal.ofReal (C * cubeScaleFactor Q) *
        ∑ j : Fin d, eLpNorm (fun x => v.grad x j) (ENNReal.ofReal 4)
          (volume.restrict (openCubeSet Q)) := by
    have h1 := ENNReal.ofReal_le_ofReal hP
    rw [ENNReal.ofReal_toReal hG4, ENNReal.ofReal_mul hs, ENNReal.ofReal_sum_of_nonneg
      (fun j _ => ENNReal.toReal_nonneg)] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_toReal (hgrad4 j)
  rw [← h4, normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet,
    eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top _ _ hmeasG]
  simp only [eLpNorm_smul_measure_of_ne_top (ENNReal.ofReal_ne_top (r := 4)) _ _
    (v.gradMemLp _).aestronglyMeasurable, smul_eq_mul]
  rw [← Finset.mul_sum, mul_left_comm]
  exact mul_le_mul_right hP' _

theorem aestronglyMeasurable_normalized {S : TriadicCube d} {E : Type*} [TopologicalSpace E]
    {f : Vec d → E}
    (h : AEStronglyMeasurable f (volume.restrict (openCubeSet S))) :
    AEStronglyMeasurable f (normalizedCubeMeasure S) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact h.smul_measure _

theorem aestronglyMeasurable_hilbertifyVecField_of_coord {μ : Measure (Vec d)}
    {F : Vec d → Vec d} (h : ∀ i, AEStronglyMeasurable (fun x => F x i) μ) :
    AEStronglyMeasurable (hilbertifyVecField F) μ :=
  ((HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable
    (aemeasurable_pi_iff.2 fun i => (h i).aemeasurable).aestronglyMeasurable)

theorem aestronglyMeasurable_hilbertMat_of_entries {μ : Measure (Vec d)}
    {A : Vec d → Mat d} (h : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ) :
    AEStronglyMeasurable (fun x => HilbertMat.ofMat (A x)) μ := by
  have hM : AEStronglyMeasurable A μ :=
    (aemeasurable_pi_iff.2 fun i => aemeasurable_pi_iff.2 fun j => (h i j).aemeasurable).aestronglyMeasurable
  exact (HilbertMat.continuousLinearEquivMat d).symm.continuous.comp_aestronglyMeasurable hM

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
theorem vecNorm_le_sum_abs (v : Vec d) : Homogenization.Book.Ch02.vecNorm v ≤ ∑ i, |v i| := by
  refine (sq_le_sq₀ (Homogenization.Book.Ch02.vecNorm_nonneg v)
    (Finset.sum_nonneg fun i _ => abs_nonneg _)).1 ?_
  rw [Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]
  calc vecNormSq v = ∑ i, |v i| ^ 2 := by
        unfold vecNormSq vecDot
        exact Finset.sum_congr rfl fun i _ => by rw [sq_abs, sq]
    _ ≤ (∑ i, |v i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

/-- Each entry of a matrix is at most its Frobenius norm. -/
theorem abs_apply_le_norm_hilbertMat (A : Mat d) (i j : Fin d) :
    |A i j| ≤ ‖HilbertMat.ofMat A‖ := by
  refine (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sq_hilbertMat_ofMat, sq_abs, sq]
  calc A i j * A i j ≤ ∑ j', A i j' * A i j' :=
        Finset.single_le_sum (f := fun j' => A i j' * A i j') (fun j' _ => mul_self_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' * A i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' * A i' j')
          (fun i' _ => Finset.sum_nonneg fun j' _ => mul_self_nonneg _) (Finset.mem_univ i)

/-- **The `L̲⁴` Poincaré inequality for a vector field with `W^{1,4}` coordinates**:
`‖F − (F)_S‖_{L̲⁴(S)} ≤ C 3^{scale S} ‖∇F‖_{L̲⁴(S)}`. -/
theorem vecCubeLpENorm_sub_volumeAverageVec_le_jacobian [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : TriadicCube d) (u : Fin d → W1pFunction (openCubeSet S) (ENNReal.ofReal 4)),
        vecCubeLpENorm S 4 (fun x => (fun i => (u i).toFun x) -
            volumeAverageVec (openCubeSet S) (fun x i => (u i).toFun x)) ≤
          ENNReal.ofReal (C * cubeScaleFactor S) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm S 4
              (fun x => HilbertMat.ofMat (fun i j => (u i).grad x j)) := by
  obtain ⟨C₀, hC₀, hP⟩ := eLpNorm_sub_integralAverage_le (d := d)
  refine ⟨C₀ * ((d : ℝ) * d) + 1, by positivity, fun S u => ?_⟩
  have hs : 0 ≤ cubeScaleFactor S := by simp only [cubeScaleFactor]; positivity
  set M := SuperdiffusionCLT.Section2.Norms.cubeLpENorm S 4
    (fun x => HilbertMat.ofMat (fun i j => (u i).grad x j)) with hM
  set G : Fin d → Vec d → ℝ := fun i x =>
    (u i).toFun x - integralAverage (openCubeSet S) (u i).toFun with hG
  have hGm : ∀ i, AEStronglyMeasurable (G i) (normalizedCubeMeasure S) := fun i =>
    aestronglyMeasurable_normalized
      ((u i).memLp.aestronglyMeasurable.sub aestronglyMeasurable_const)
  have h1 : vecCubeLpENorm S 4 (fun x => (fun i => (u i).toFun x) -
        volumeAverageVec (openCubeSet S) (fun x i => (u i).toFun x)) ≤
      ∑ i, eLpNorm (G i) 4 (normalizedCubeMeasure S) := by
    have hGh : AEStronglyMeasurable (hilbertifyVecField (fun x => (fun i => (u i).toFun x) -
        volumeAverageVec (openCubeSet S) (fun x i => (u i).toFun x))) (normalizedCubeMeasure S) :=
      aestronglyMeasurable_hilbertifyVecField_of_coord fun i => hGm i
    have hpt : ∀ x, ‖hilbertifyVecField (fun x => (fun i => (u i).toFun x) -
        volumeAverageVec (openCubeSet S) (fun x i => (u i).toFun x)) x‖ₑ ≤
        ‖(∑ i, fun x => |G i x|) x‖ₑ := by
      intro x
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_hilbertifyVecField_apply, Finset.sum_apply, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
      refine (vecNorm_le_sum_abs _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i _ => rfl
    calc _ ≤ eLpNorm (∑ i, fun x => |G i x|) 4 (normalizedCubeMeasure S) :=
          MeasureTheory.eLpNorm_mono_enorm hGh hpt
      _ ≤ ∑ i, eLpNorm (fun x => |G i x|) 4 (normalizedCubeMeasure S) :=
          eLpNorm_sum_le (by norm_num)
      _ = ∑ i, eLpNorm (G i) 4 (normalizedCubeMeasure S) :=
          Finset.sum_congr rfl fun i _ => by
            simpa [Real.norm_eq_abs] using MeasureTheory.eLpNorm_norm (G i) (hGm i) (p := 4)
  have h2 : ∀ i, eLpNorm (G i) 4 (normalizedCubeMeasure S) ≤
      ENNReal.ofReal (C₀ * cubeScaleFactor S) * ((d : ℝ≥0∞) * M) := by
    intro i
    refine (hP S (u i)).trans (mul_le_mul_right ?_ _)
    calc ∑ j : Fin d, eLpNorm (fun x => (u i).grad x j) 4 (normalizedCubeMeasure S)
        ≤ ∑ _j : Fin d, M := by
          refine Finset.sum_le_sum fun j _ => MeasureTheory.eLpNorm_mono_enorm
            (aestronglyMeasurable_normalized ((u i).gradMemLp j).aestronglyMeasurable) fun x => ?_
          rw [← ofReal_norm, ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.norm_eq_abs]
          exact abs_apply_le_norm_hilbertMat (fun i j => (u i).grad x j) i j
      _ = (d : ℝ≥0∞) * M := by simp
  have hfin : ENNReal.ofReal (C₀ * ((d : ℝ) * d) * cubeScaleFactor S) ≤
      ENNReal.ofReal ((C₀ * ((d : ℝ) * d) + 1) * cubeScaleFactor S) :=
    ENNReal.ofReal_le_ofReal (by
      have : (C₀ * ((d : ℝ) * d) + 1) * cubeScaleFactor S =
          C₀ * ((d : ℝ) * d) * cubeScaleFactor S + cubeScaleFactor S := by ring
      linarith only [this, hs])
  calc _ ≤ ∑ i, eLpNorm (G i) 4 (normalizedCubeMeasure S) := h1
    _ ≤ ∑ _i : Fin d, ENNReal.ofReal (C₀ * cubeScaleFactor S) * ((d : ℝ≥0∞) * M) :=
        Finset.sum_le_sum fun i _ => h2 i
    _ = ENNReal.ofReal (C₀ * ((d : ℝ) * d) * cubeScaleFactor S) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul hC₀, ENNReal.ofReal_mul (Nat.cast_nonneg d),
          ENNReal.ofReal_natCast]
        ring
    _ ≤ _ := by gcongr

/-- Finiteness of an `L^p` norm for the normalized cube measure gives the same for the restricted
Lebesgue measure on the open cube. -/
theorem eLpNorm_restrict_ne_top_of_normalized {S : TriadicCube d} {f : Vec d → ℝ}
    {p : ℝ≥0∞} (hp : p ≠ ∞)
    (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet S)))
    (h : eLpNorm f p (normalizedCubeMeasure S) ≠ ∞) :
    eLpNorm f p (volume.restrict (openCubeSet S)) ≠ ∞ := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet,
    eLpNorm_smul_measure_of_ne_top hp _ _ hf] at h
  intro htop
  rw [htop] at h
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (cubeVolume S)⁻¹ ^ (1 / p).toReal := by
    refine ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos S))) ?_
    exact ENNReal.ofReal_ne_top
  simp only [smul_eq_mul] at h
  exact h (ENNReal.mul_top hpos.ne')

/-- **The `L̲⁴` Poincaré inequality for a vector field with `H¹` coordinates**, with the
Jacobian measured in `L̲⁴` (the right-hand side is `∞` when the Jacobian is not in `L⁴`). -/
theorem vecCubeLpENorm_sub_volumeAverageVec_le_h1 [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : TriadicCube d) (u : Fin d → H1Function (openCubeSet S)),
        vecCubeLpENorm S 4 (fun x => (fun i => (u i).toFun x) -
            volumeAverageVec (openCubeSet S) (fun x i => (u i).toFun x)) ≤
          ENNReal.ofReal (C * cubeScaleFactor S) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm S 4
              (fun x => HilbertMat.ofMat (fun i j => (u i).grad x j)) := by
  obtain ⟨C, hC, hP⟩ := vecCubeLpENorm_sub_volumeAverageVec_le_jacobian (d := d)
  refine ⟨C, hC, fun S u => ?_⟩
  have hs : 0 < C * cubeScaleFactor S := mul_pos hC (by simp only [cubeScaleFactor]; positivity)
  by_cases hM : SuperdiffusionCLT.Section2.Norms.cubeLpENorm S 4
      (fun x => HilbertMat.ofMat (fun i j => (u i).grad x j)) = ∞
  · rw [hM, ENNReal.mul_top (ENNReal.ofReal_pos.2 hs).ne']
    exact le_top
  · have hgrad : ∀ i, GradMemLpOn (openCubeSet S) (ENNReal.ofReal 4) (u i).grad := by
      intro i j
      have hmeas : AEStronglyMeasurable (fun x => (u i).grad x j) (volume.restrict (openCubeSet S)) :=
        ((u i).gradMemL2 j).aestronglyMeasurable
      have hn : eLpNorm (fun x => (u i).grad x j) 4 (normalizedCubeMeasure S) ≠ ∞ := by
        refine ne_top_of_le_ne_top hM (MeasureTheory.eLpNorm_mono_enorm
          (aestronglyMeasurable_normalized hmeas) fun x => ?_)
        rw [← ofReal_norm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_eq_abs]
        exact abs_apply_le_norm_hilbertMat (fun i j => (u i).grad x j) i j
      have h4 : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by simp
      show eLpNorm _ (ENNReal.ofReal 4) _ < ∞
      rw [h4]
      exact lt_top_iff_ne_top.2 (eLpNorm_restrict_ne_top_of_normalized (by norm_num) hmeas hn)
    let q : FiniteLpExponent := ⟨ENNReal.ofReal 4, by simp, ENNReal.ofReal_lt_top⟩
    exact hP S fun i => (u i).toW1pOfGradMemLp (isOpenBoundedConvexDomain_openCubeSet S) q
      (hgrad i)

/-- **The `L̲⁴` Poincaré inequality for a `C¹` vector field.** -/
theorem vecCubeLpENorm_sub_volumeAverageVec_le_contDiff [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : TriadicCube d) (f : Fin d → Vec d → ℝ) (_hf : ∀ i, ContDiff ℝ 1 (f i)),
        vecCubeLpENorm S 4 (fun x => (fun i => f i x) -
            volumeAverageVec (openCubeSet S) (fun x i => f i x)) ≤
          ENNReal.ofReal (C * cubeScaleFactor S) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm S 4
              (fun x => HilbertMat.ofMat (fun i j => fderiv ℝ (f i) x (basisVec j))) := by
  obtain ⟨C, hC, hP⟩ := vecCubeLpENorm_sub_volumeAverageVec_le_jacobian (d := d)
  refine ⟨C, hC, fun S f hf => ?_⟩
  exact hP S fun i => W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet S) (hf i)

end

end SuperdiffusionCLT.Section5
