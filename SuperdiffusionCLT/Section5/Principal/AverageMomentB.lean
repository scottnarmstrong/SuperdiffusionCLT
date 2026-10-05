/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AverageMoment
public import SuperdiffusionCLT.Section5.Localization.CrudeSzC
public import SuperdiffusionCLT.Section2.Estimates.Stream.CenteredShellFluxBounds
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneB
public import SuperdiffusionCLT.Section2.Norms.CubeCarrierIdents
public import SuperdiffusionCLT.Section3.Setup.DirichletResponse

/-!
# Jensen and partition inequalities for the `L̲⁸` averages of the principal term

Deterministic and measure-free tools for `e.principal.uz`:

* `pm_subcubeAvg_lintegral_le`: the subcube average of expectations is at most the expectation of the
  subcube average.
* `subcubeAvg_ofReal_vecNorm_volumeAverageVec_pow_eight_le`: the average over the subcubes of
  `|(G)_{z+cu_n}|⁸` is at most `‖G‖⁸_{L̲⁸(cu_K)}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

theorem pm_sum_lintegral_le_lintegral_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ ω, f i ω ∂μ ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine le_trans ?_ (le_lintegral_add _ _)
    exact add_le_add le_rfl ih

theorem card_descendantsAtScale_ne_zero {Kc n : ℕ} (hn : n ≤ Kc) :
    (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card ≠ 0 := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  rw [descendantsAtScale_eq_descendantsAtDepth _ hk, descendantsAtDepth_card]
  positivity

/-- The subcube average of expectations is at most the expectation of the subcube average. -/
theorem pm_subcubeAvg_lintegral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {Kc n : ℕ}
    (hn : n ≤ Kc) (F : TriadicCube d → Ω → ℝ≥0∞) :
    subcubeAvg Kc n (fun Q => ∫⁻ ω, F Q ω ∂μ) ≤
      ∫⁻ ω, subcubeAvg Kc n (fun Q => F Q ω) ∂μ := by
  unfold subcubeAvg
  have hc : ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (by exact_mod_cast card_descendantsAtScale_ne_zero hn)
  rw [lintegral_const_mul' _ _ hc]
  exact mul_le_mul' le_rfl (pm_sum_lintegral_le_lintegral_sum _ _)

theorem vecCubeLpENorm_pow_eight_eq {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    vecCubeLpENorm Q 8 g ^ (8 : ℕ) =
      ∫⁻ x, ‖hilbertifyVecField g x‖ₑ ^ (8 : ℕ) ∂normalizedCubeMeasure Q := by
  have hm := SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
    hg
  have h1 := avgRootENorm_eq_cubeLpENorm Q (p := 8) (by norm_num) hm
  have h2 := avgPowENorm_eq_rootENorm_rpow Q (p := 8) (by norm_num) (hilbertifyVecField g)
  have h4 : ENNReal.ofReal 8 = 8 := by norm_num
  rw [h4] at h1
  rw [vecCubeLpENorm, ← h1]
  have h3 : avgRootENorm Q 8 (hilbertifyVecField g) ^ (8 : ℕ) =
      avgRootENorm Q 8 (hilbertifyVecField g) ^ (8 : ℝ) := by
    rw [← ENNReal.rpow_natCast]; norm_num
  rw [h3, ← h2]
  unfold avgPowENorm
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_natCast]; norm_num

/-- **Jensen and partition**: the average over the subcubes `z + cu_n` of `|(G)_{z+cu_n}|⁸` is at
most `‖G‖⁸_{L̲⁸(cu_K)}`. -/
theorem subcubeAvg_ofReal_vecNorm_volumeAverageVec_pow_eight_le {Kc n : ℕ} (hn : n ≤ Kc)
    {G : Vec d → Vec d} (hG : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) G) :
    subcubeAvg Kc n (fun Q =>
        ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) G)) ^ (8 : ℕ)) ≤
      vecCubeLpENorm (originCube d (Kc : ℤ)) 8 G ^ (8 : ℕ) := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hstep : subcubeAvg Kc n (fun Q =>
        ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) G)) ^ (8 : ℕ)) ≤
      subcubeAvg Kc n (fun Q => ∫⁻ x, ‖hilbertifyVecField G x‖ₑ ^ (8 : ℕ)
        ∂normalizedCubeMeasure Q) := by
    unfold subcubeAvg
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun Q hQ => ?_)
    have hGQ := SuperdiffusionCLT.Section3.Terms.memVectorL2_mono
      (openCubeSet_subset_of_mem_descendantsAtScale hk hQ) hG
    rw [← vecCubeLpENorm_pow_eight_eq hGQ, volumeAverageVec_cubeSet_eq_openCubeSet]
    exact pow_le_pow_left' (SuperdiffusionCLT.Section2.Estimates.Stream.ofReal_vecNorm_volumeAverageVec_le
      (by norm_num) hGQ) 8
  refine hstep.trans ?_
  rw [subcubeAvg_lintegral_normalizedCubeMeasure hn, ← vecCubeLpENorm_pow_eight_eq hG]

/-! ## Matrix fields -/

section MatNorm

open scoped Matrix.Norms.L2Operator

theorem pm_continuous_matVecMul_field {f : Vec d → Mat d} (hf : Continuous f) (v : Vec d) :
    Continuous (fun x => matVecMul (f x) v) :=
  continuous_pi fun i => by
    simp only [matVecMul]
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp ((continuous_apply i).comp hf)).mul continuous_const

theorem pm_vecCubeLpENorm_matVecMul_le {Q : TriadicCube d} (q : ℝ≥0∞) {f : Vec d → Mat d}
    (hf : Continuous f) {v : Vec d} (hv : vecNorm v ≤ 1) :
    vecCubeLpENorm Q q (fun x => matVecMul (f x) v) ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q q f := by
  have hmeas : AEStronglyMeasurable
      (hilbertifyVecField (fun x => matVecMul (f x) v)) (normalizedCubeMeasure Q) :=
    (SuperdiffusionCLT.Section2.Estimates.Stream.continuous_hilbertifyVecField
      (pm_continuous_matVecMul_field hf v)).aestronglyMeasurable
  refine SuperdiffusionCLT.Section2.Norms.cubeLpENorm_mono_enorm hmeas (fun x => ?_)
  rw [norm_hilbertifyVecField_apply, SuperdiffusionCLT.Section2.Norms.norm_eq_matrixOperatorNorm]
  exact (vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ v).trans
    (mul_le_of_le_one_right (matrixOperatorNorm_nonneg _) hv)

/-- **Jensen for matrix fields**: `|(f)_Q|_{op} ≤ d² ‖f‖_{L̲⁸(Q)}`, the factor `d²` from the
entrywise comparison of the operator and `ℓ¹` norms. -/
theorem ofReal_matrixOperatorNorm_volumeAverageMat_le {Kc n : ℕ} (hn : n ≤ Kc)
    {Q : TriadicCube d} (hQ : Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ))
    {f : Vec d → Mat d} (hf : Continuous f) :
    ENNReal.ofReal (matrixOperatorNorm (volumeAverageMat (cubeSet Q) f)) ≤
      ((d : ℝ≥0∞) * d) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  set A := volumeAverageMat (cubeSet Q) f with hA
  have h1 : matrixOperatorNorm A ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j| :=
    (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans (matrixFrobeniusNorm_le_sum_abs_entries A)
  have hent : ∀ i j : Fin d, ENNReal.ofReal |A i j| ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f := by
    intro i j
    set ej : Vec d := Pi.single j 1 with hej
    have hej1 : vecNorm ej ≤ 1 := by
      rw [← abs_of_nonneg (vecNorm_nonneg ej)]
      refine abs_le_of_sq_le_sq ?_ zero_le_one
      rw [vecNorm_sq_eq_vecNormSq]
      simp [hej, vecNormSq, vecDot, Pi.single_apply]
    have havg : volumeAverageVec (cubeSet Q) (fun x => matVecMul (f x) ej) =
        matVecMul A ej := SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverageVec_matVecMul
      Q hf ej
    have hcomp : (matVecMul A ej) i = A i j := by
      simp [matVecMul, hej, Pi.single_apply]
    have hG : MemVectorL2 (openCubeSet Q) (fun x => matVecMul (f x) ej) :=
      SuperdiffusionCLT.Section3.Terms.memVectorL2_mono
        (openCubeSet_subset_of_mem_descendantsAtScale hk hQ)
        (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous _
          (pm_continuous_matVecMul_field hf ej))
    have hJ := SuperdiffusionCLT.Section2.Estimates.Stream.ofReal_vecNorm_volumeAverageVec_le
      (q := 8) (by norm_num) hG
    rw [← volumeAverageVec_cubeSet_eq_openCubeSet, havg] at hJ
    refine le_trans ?_ (hJ.trans (pm_vecCubeLpENorm_matVecMul_le 8 hf hej1))
    rw [← hcomp]
    exact ENNReal.ofReal_le_ofReal (abs_apply_le_vecNorm _ _)
  calc ENNReal.ofReal (matrixOperatorNorm A)
      ≤ ENNReal.ofReal (∑ i : Fin d, ∑ j : Fin d, |A i j|) := ENNReal.ofReal_le_ofReal h1
    _ = ∑ i : Fin d, ∑ j : Fin d, ENNReal.ofReal |A i j| := by
        rw [ENNReal.ofReal_sum_of_nonneg
          (f := fun i : Fin d => ∑ j : Fin d, |A i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact ENNReal.ofReal_sum_of_nonneg (f := fun j : Fin d => |A i j|)
          (fun j _ => abs_nonneg _)
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = ((d : ℝ≥0∞) * d) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f := by
        simp [Finset.sum_const, Finset.card_univ, mul_assoc]

end MatNorm

end SuperdiffusionCLT.Section5
