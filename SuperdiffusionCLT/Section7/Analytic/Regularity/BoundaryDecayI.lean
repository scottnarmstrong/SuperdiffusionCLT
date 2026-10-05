/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayH

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Normalized norms over the sub-cube

Squared `L²` norms over the cube of scale `m - 1` of translates of `u` and `∇u` are bounded by
the corresponding integrals over the sub-cube touching the face, and the `L^q` norm of the data
is controlled with a factor `3^d`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3d_eLpNorm_sq_eq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {F : α → E} (hF : MemLp F 2 μ) :
    ((eLpNorm F 2 μ).toReal) ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  have h := hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at h
  have hnn : 0 ≤ ∫ x, ‖F x‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun x => by positivity
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  have e1 : ∀ x, ‖F x‖ ^ (2 : ℝ) = ‖F x‖ ^ 2 := fun x => by norm_cast
  simp_rw [e1]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem r3d_eLpNorm_sq_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {F : α → E} {G : α → ℝ} (hG : Integrable G μ) (hFG : ∀ᵐ x ∂μ, ‖F x‖ ^ 2 ≤ G x) :
    ((eLpNorm F 2 μ).toReal) ^ 2 ≤ ∫ x, G x ∂μ := by
  by_cases htop : eLpNorm F 2 μ = ⊤
  · rw [htop]
    simp only [ENNReal.toReal_top]
    refine le_trans (by norm_num) (integral_nonneg_of_ae (hFG.mono fun x hx => (sq_nonneg _).trans hx))
  · have hF : MemLp F 2 μ := lt_top_iff_ne_top.2 htop
    rw [r3d_eLpNorm_sq_eq hF]
    exact integral_mono_ae hF.norm.integrable_sq hG hFG

theorem r3d_sup_sq_le (v : Vec d) : ‖v‖ ^ 2 ≤ vecNormSq v := by
  rw [← eucNorm_sq]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  exact (pi_norm_le_iff_of_nonneg (eucNorm_nonneg v)).2 fun i => by
    rw [Real.norm_eq_abs]; exact abs_apply_le_eucNorm v i

theorem r3d_translate_mp (e : Fin d) (m : ℤ) :
    MeasurePreserving (fun x : Vec d => x - r3d_zT e m)
      (volume.restrict (openCubeSet (originCube d (m - 1)))) (volume.restrict (r3d_subV e m)) := by
  have := measurePreserving_subRight_restrict_translateSet (d := d) (r3d_zT e m) (r3d_subV e m)
  rw [r3d_translate_subV] at this
  exact this

theorem r3d_normalized_sub_eq (m : ℤ) :
    normalizedCubeMeasure (originCube d (m - 1)) =
      ENNReal.ofReal (((3 : ℝ) ^ m / 3) ^ d)⁻¹ • volume.restrict (openCubeSet (originCube d (m - 1))) := by
  rw [normalizedCubeMeasure_eq_smul, r3c_cubeVolume_originCube, r3d_pow_pred]

/-- The `L²` norm over the cube of scale `m - 1` of a translated function. -/
theorem r3d_sub_sq_le {E' : Type*} [NormedAddCommGroup E'] (e : Fin d) (m : ℤ) {F : Vec d → E'} {G : Vec d → ℝ}
    (hG : Integrable G (volume.restrict (r3d_subV e m)))
    (hFG : ∀ x, ‖F x‖ ^ 2 ≤ G x) :
    ((eLpNorm (fun y => F (y - r3d_zT e m)) 2 (normalizedCubeMeasure (originCube d (m - 1)))).toReal) ^ 2 ≤
      (((3 : ℝ) ^ m / 3) ^ d)⁻¹ * ∫ x in r3d_subV e m, G x := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m / 3 := by positivity
  have hmp := r3d_translate_mp e m
  have hme : MeasurableEmbedding (fun x : Vec d => x - r3d_zT e m) :=
    (Homeomorph.subRight (r3d_zT e m)).measurableEmbedding
  rw [r3d_normalized_sub_eq]
  have hGi : Integrable (fun y => G (y - r3d_zT e m)) (volume.restrict (openCubeSet (originCube d (m - 1)))) :=
    (hmp.integrable_comp_emb hme).2 hG
  have hGi' : Integrable (fun y => G (y - r3d_zT e m))
      (ENNReal.ofReal (((3 : ℝ) ^ m / 3) ^ d)⁻¹ • volume.restrict (openCubeSet (originCube d (m - 1)))) :=
    hGi.smul_measure ENNReal.ofReal_ne_top
  have h1 := r3d_eLpNorm_sq_le hGi' (Filter.Eventually.of_forall fun y => hFG (y - r3d_zT e m))
  refine h1.trans (le_of_eq ?_)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  exact hmp.integral_comp hme G

theorem r3d_sub_norms (e : Fin d) (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) :
    ((eLpNorm (fun y => u.grad (y - r3d_zT e m)) 2
        (normalizedCubeMeasure (originCube d (m - 1)))).toReal) ^ 2 ≤
      (((3 : ℝ) ^ m / 3) ^ d)⁻¹ *
        ∫ x in r3d_Ebox e m ((3 : ℝ) ^ m / 3), vecNormSq (u.grad x) ∧
    ((eLpNorm (fun y => u.toFun (y - r3d_zT e m)) 2
        (normalizedCubeMeasure (originCube d (m - 1)))).toReal) ^ 2 ≤
      (((3 : ℝ) ^ m / 3) ^ d)⁻¹ * ∫ x in openCubeSet (originCube d m), u.toFun x ^ 2 := by
  have hℓ3 : (0 : ℝ) < (((3 : ℝ) ^ m / 3) ^ d)⁻¹ := by
    have : (0 : ℝ) < (3 : ℝ) ^ m / 3 := by positivity
    positivity
  have hVU := r3d_subV_subset e m
  have hi2 : Integrable (fun x => vecNormSq (u.grad x)) (volume.restrict (openCubeSet (originCube d m))) := by
    have : (fun x => vecNormSq (u.grad x)) = fun x => ∑ i, (u.grad x i) ^ 2 := by
      funext x; simp [vecNormSq, vecDot, pow_two]
    rw [this]
    exact integrable_finsetSum _ fun i _ => (u.grad_memL2 i).integrable_sq
  have hi2o : IntegrableOn (fun x => vecNormSq (u.grad x)) (openCubeSet (originCube d m)) volume := hi2
  have hi1 : Integrable (fun x => u.toFun x ^ 2) (volume.restrict (openCubeSet (originCube d m))) :=
    u.memL2.integrable_sq
  have hi1o : IntegrableOn (fun x => u.toFun x ^ 2) (openCubeSet (originCube d m)) volume := hi1
  constructor
  · have h := r3d_sub_sq_le e m (F := u.grad) (G := fun x => vecNormSq (u.grad x))
      (hi2o.mono_set hVU) (fun x => r3d_sup_sq_le _)
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hℓ3.le
    exact setIntegral_mono_set (hi2o.mono_set (Set.inter_subset_right.trans (le_refl _))) 
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => r3d_subV_subset_Ebox e m hx)
  · have h := r3d_sub_sq_le e m (F := u.toFun) (G := fun x => u.toFun x ^ 2)
      (hi1o.mono_set hVU) (fun x => by rw [Real.norm_eq_abs, sq_abs])
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hℓ3.le
    exact setIntegral_mono_set hi1o (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hVU hx)

theorem r3d_cube_translate_norm (e : Fin d) (m : ℤ) {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hqt : q ≠ ⊤)
    {F : Vec d → ℝ} (hF : MemLp F q (normalizedCubeMeasure (originCube d m))) :
    MemLp (fun y => F (y - r3d_zT e m)) q (normalizedCubeMeasure (originCube d (m - 1))) ∧
      (eLpNorm (fun y => F (y - r3d_zT e m)) q (normalizedCubeMeasure (originCube d (m - 1)))).toReal ≤
        (3 : ℝ) ^ d * (eLpNorm F q (normalizedCubeMeasure (originCube d m))).toReal := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq1).ne'
  have hVD := r3d_subV_subset e m
  have hmp := r3d_translate_mp e m
  have hFD : MemLp F q (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_restrict_of_normalized _ hF
  have hFV : MemLp F q (volume.restrict (r3d_subV e m)) := hFD.mono_measure (Measure.restrict_mono hVD le_rfl)
  have hcomp : MemLp (fun x => F (x - r3d_zT e m)) q (volume.restrict (openCubeSet (originCube d (m - 1)))) :=
    hFV.comp_measurePreserving hmp
  have hV' : (0 : ℝ) < cubeVolume (originCube d (m - 1)) := cubeVolume_pos _
  have hV0 : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  refine ⟨?_, ?_⟩
  · rw [r3d_normalized_sub_eq]
    exact hcomp.smul_measure ENNReal.ofReal_ne_top
  · have hsub : ENNReal.ofReal (((3 : ℝ) ^ m / 3) ^ d)⁻¹ =
        ENNReal.ofReal (cubeVolume (originCube d (m - 1)))⁻¹ := by
      rw [r3c_cubeVolume_originCube, r3d_pow_pred]
    have e1 : eLpNorm (fun x => F (x - r3d_zT e m)) q (normalizedCubeMeasure (originCube d (m - 1))) =
        (ENNReal.ofReal (cubeVolume (originCube d (m - 1)))⁻¹) ^ (1 / q).toReal •
          eLpNorm F q (volume.restrict (r3d_subV e m)) := by
      rw [r3d_normalized_sub_eq, hsub, eLpNorm_smul_measure_of_ne_zero_of_ne_top hq0 hqt]
      congr 1
      exact eLpNorm_comp_measurePreserving hFV.aestronglyMeasurable hmp
    have e2 : eLpNorm F q (volume.restrict (openCubeSet (originCube d m))) =
        (ENNReal.ofReal (cubeVolume (originCube d m))) ^ (1 / q).toReal •
          eLpNorm F q (normalizedCubeMeasure (originCube d m)) := by
      have : volume.restrict (openCubeSet (originCube d m)) =
          (ENNReal.ofReal (cubeVolume (originCube d m))⁻¹)⁻¹ • normalizedCubeMeasure (originCube d m) := by
        rw [normalizedCubeMeasure_eq_smul, smul_smul, ENNReal.inv_mul_cancel
          (by simpa using hV0) ENNReal.ofReal_ne_top, one_smul]
      rw [this, eLpNorm_smul_measure_of_ne_zero_of_ne_top hq0 hqt,
        ENNReal.ofReal_inv_of_pos hV0, inv_inv]
    have e3 : eLpNorm F q (volume.restrict (r3d_subV e m)) ≤
        eLpNorm F q (volume.restrict (openCubeSet (originCube d m))) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hVD le_rfl)
    have hfin : eLpNorm F q (normalizedCubeMeasure (originCube d m)) ≠ ⊤ := hF.eLpNorm_ne_top
    have e4 : eLpNorm (fun x => F (x - r3d_zT e m)) q (normalizedCubeMeasure (originCube d (m - 1))) ≤
        ENNReal.ofReal ((3 : ℝ) ^ d) * eLpNorm F q (normalizedCubeMeasure (originCube d m)) := by
      rw [e1, smul_eq_mul]
      refine (mul_le_mul_right e3 _).trans ?_
      rw [e2, smul_eq_mul, ← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      refine mul_le_mul_left ?_ _
      have hr : ENNReal.ofReal (cubeVolume (originCube d (m - 1)))⁻¹ *
          ENNReal.ofReal (cubeVolume (originCube d m)) = ENNReal.ofReal ((3 : ℝ) ^ d) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hV'.le), r3c_cubeVolume_originCube,
          r3c_cubeVolume_originCube, zpow_sub_one₀ (by norm_num)]
        congr 1
        have : ((3 : ℝ) ^ m) ≠ 0 := by positivity
        field_simp
        rw [div_pow]
        field_simp
      rw [hr]
      have h3 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((3 : ℝ) ^ d) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num))
      have h4 : (1 / q).toReal ≤ 1 := by
        have : 1 / q ≤ 1 := by rw [one_div]; exact ENNReal.inv_le_one.2 hq1
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
      calc ENNReal.ofReal ((3 : ℝ) ^ d) ^ (1 / q).toReal ≤ ENNReal.ofReal ((3 : ℝ) ^ d) ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le h3 h4
        _ = _ := by simp
    have hne : ENNReal.ofReal ((3 : ℝ) ^ d) * eLpNorm F q (normalizedCubeMeasure (originCube d m)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have := ENNReal.toReal_mono hne e4
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this

end SuperdiffusionCLT.Section7
