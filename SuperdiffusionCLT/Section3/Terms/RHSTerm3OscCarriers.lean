/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputsB

/-!
# The exponent-3 tiling identity for the estimate `e.RHS.term3.B`

Step 1 of the estimate of `e.additivity.defect.splitting` rests on four printed
estimates:

* the per-cube Cauchy-Schwarz / duality display
  `⨍_{z+cu_n} (∇w − (∇w)_{z+cu_n}) · a_{L'}(∇u_m − ∇u_{n,z})
    ≤ [∇w − (∇w)_{z+cu_n}]_{H̲¹(z+cu_n)} ‖a_{L'}(∇u_m − ∇u_{n,z})‖_{Ĥ̲⁻¹(z+cu_n)}`;
* the per-cube Poincaré step
  `avsum_{z ∈ 3^nℤ^d ∩ cu_m} E[[∇w − (∇w)_{z+cu_n}]³_{H̲¹(z+cu_n)}]
    ≤ C avsum_{z} E[‖∇²w‖³_{L̲³(z+cu_n)}] ≤ Cν^{-3/2} 3^{-3ℓ'}`;
* the multiscale-Poincaré / Hölder chain bounding
  `E[‖a_{L'}(∇u_m − ∇u_{n,z})‖^{3/2}_{Ĥ̲⁻¹(z+cu_n)}]` by
  `C 3^{3n/2}(L'ν⁻¹)^{3/4} E[‖s^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}]^{3/4}`;
* `e.additivity.error.superdiff`:
  `avsum_{z} E[‖s^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}] ≤ C(δ + η_L)`.

The step concludes by combining these displays with Hölder's inequality.

The only deterministic ingredient proved in this module is the exponent-3 tiling
identity used for the per-cube Poincaré average.

## Main results

* `cubeLpENorm_three_pow_eq_inv_card_mul_sum`: the exponent-3 tiling identity
  `‖f‖³_{L̲³(cu_m)} = (card)⁻¹ ∑_z ‖f‖³_{L̲³(z+cu_n)}` over the sub-cube family,
  the exponent-3 companion of `cubeLpENorm_two_sq_eq_inv_card_mul_sum`
  (`Section3/Terms/RHSTerm2.lean`) and of `cubeLpENorm_four_pow_eq_inv_card_mul_sum`
  (`Section3/Terms/RHSTerm3SourceGaps.lean`).

The identity carries no geometric input: `d := 1`, `j := 0`, `f := 0` is a
witness for its hypotheses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The exponent-3 tiling identity -/

/-- The third power of an `L³` norm is the lower integral of the third power of
the norm. -/
private theorem eLpNorm_three_pow {α : Type*} {E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (mu : Measure α) (f : α → E)
    (hf : AEStronglyMeasurable f mu) :
    eLpNorm f 3 mu ^ (3 : ℕ) = ∫⁻ a, ‖f a‖ₑ ^ (3 : ℕ) ∂mu := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_natCast _ 3, ← ENNReal.rpow_mul]
  norm_num

/-- **The third power of the normalized cube norm is the plain average of the
third powers over the sub-cubes at depth `j`**, the exponent-3 companion of
`cubeLpENorm_two_sq_eq_inv_card_mul_sum` (`Section3/Terms/RHSTerm2.lean`) and of
`cubeLpENorm_four_pow_eq_inv_card_mul_sum` (`Section3/Terms/RHSTerm3SourceGaps.lean`).
It is the tiling identity behind the per-cube Poincaré average of
`e.RHS.term3.B`. -/
theorem cubeLpENorm_three_pow_eq_inv_card_mul_sum {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} (j : ℕ) (f : Vec d → E) :
    (Section2.Norms.cubeLpENorm Q 3 f) ^ (3 : ℕ) =
      ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ) := by
  classical
  have hcardpos : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty Q j)
  have hdisj : Set.PairwiseDisjoint
      (descendantsAtDepth Q j : Set (TriadicCube d))
      (fun z : TriadicCube d => cubeSet z) := pairwiseDisjoint_descendantsAtDepth Q j
  have hmeas : ∀ R ∈ descendantsAtDepth Q j, MeasurableSet (cubeSet R) :=
    fun R _ => measurableSet_cubeSet R
  have hcv : ∀ R ∈ descendantsAtDepth Q j,
      ((descendantsAtDepth Q j).card : ℝ) * cubeVolume R = cubeVolume Q := by
    intro R hR
    rw [cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth hR]
  have hprod : ∀ R ∈ descendantsAtDepth Q j,
      (cubeVolume Q)⁻¹ * cubeVolume R = ((descendantsAtDepth Q j).card : ℝ)⁻¹ := by
    intro R hR
    have h1 := hcv R hR
    have h2 : ((descendantsAtDepth Q j).card : ℝ)⁻¹ * cubeVolume Q = cubeVolume R := by
      rw [← h1, inv_mul_cancel_left₀ (ne_of_gt hcardpos)]
    have h3 : cubeVolume Q ≠ 0 := by
      rw [← h1]
      exact mul_ne_zero (ne_of_gt hcardpos) (ne_of_gt (cubeVolume_pos R))
    calc (cubeVolume Q)⁻¹ * cubeVolume R
        = (cubeVolume Q)⁻¹ *
            (((descendantsAtDepth Q j).card : ℝ)⁻¹ * cubeVolume Q) := by rw [h2]
      _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ((cubeVolume Q)⁻¹ * cubeVolume Q) := by
          ring
      _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ := by rw [inv_mul_cancel₀ h3, mul_one]
  have hofreal : ∀ R ∈ descendantsAtDepth Q j, ENNReal.ofReal ((cubeVolume Q)⁻¹) *
      ENNReal.ofReal (cubeVolume R) =
        ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) := by
    intro R hR
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 (cubeVolume_pos Q))), hprod R hR]
  have hset : cubeSet Q = ⋃ R ∈ descendantsAtDepth Q j, cubeSet R :=
    cubeSet_eq_iUnion_descendantsAtDepth Q j
  by_cases hfQ : AEStronglyMeasurable f (normalizedCubeMeasure Q)
  swap
  · have hex : ∃ R ∈ descendantsAtDepth Q j,
        ¬ AEStronglyMeasurable f (normalizedCubeMeasure R) := by
      by_contra hcon
      push Not at hcon
      apply hfQ
      rw [aestronglyMeasurable_normalizedCubeMeasure_iff, hset]
      have hU : AEStronglyMeasurable f (volume.restrict
          (⋃ R : {R // R ∈ descendantsAtDepth Q j}, cubeSet R.1)) :=
        aestronglyMeasurable_iUnion_iff.mpr fun R =>
          (aestronglyMeasurable_normalizedCubeMeasure_iff R.1 f).1 (hcon R.1 R.2)
      have hEq : (⋃ R : {R // R ∈ descendantsAtDepth Q j}, cubeSet R.1) =
          ⋃ R ∈ descendantsAtDepth Q j, cubeSet R := by
        ext x
        simp
      rwa [hEq] at hU
    obtain ⟨R, hR, hRm⟩ := hex
    have hRtop : (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ) = ⊤ := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_of_not_aestronglyMeasurable hRm]
      simp
    have hQtop : (Section2.Norms.cubeLpENorm Q 3 f) ^ (3 : ℕ) = ⊤ := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_of_not_aestronglyMeasurable hfQ]
      simp
    have hsumtop : ∑ R ∈ descendantsAtDepth Q j,
        (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ) = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨R, hR, hRtop⟩
    rw [hQtop, hsumtop]
    have hne : ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (inv_pos.2 hcardpos)).ne'
    simp [hne]
  have hfR : ∀ R ∈ descendantsAtDepth Q j,
      AEStronglyMeasurable f (normalizedCubeMeasure R) := by
    intro R hR
    rw [aestronglyMeasurable_normalizedCubeMeasure_iff]
    have hQ := (aestronglyMeasurable_normalizedCubeMeasure_iff Q f).1 hfQ
    refine hQ.mono_set ?_
    rw [hset]
    exact Set.subset_biUnion_of_mem (u := fun R => cubeSet R) hR
  have hpercube : ∀ R ∈ descendantsAtDepth Q j,
      ∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂(volume.restrict (cubeSet R)) =
        ENNReal.ofReal (cubeVolume R) * (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ) := by
    intro R hR
    have hpos : 0 < cubeVolume R := cubeVolume_pos R
    have h2 : ENNReal.ofReal (cubeVolume R) * ENNReal.ofReal ((cubeVolume R)⁻¹) = 1 := by
      rw [mul_comm, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hpos)),
        inv_mul_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one]
    have h1 : (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ) =
        ENNReal.ofReal ((cubeVolume R)⁻¹) *
          ∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂(volume.restrict (cubeSet R)) := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_three_pow _ _ (hfR R hR),
        normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
        smul_eq_mul, Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet R)]
    rw [h1, ← mul_assoc, h2, one_mul]
  rw [Section2.Norms.cubeLpENorm, eLpNorm_three_pow _ _ hfQ,
    normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
    smul_eq_mul, ← Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q),
    hset, lintegral_biUnion_finset hdisj hmeas]
  have hstep : ENNReal.ofReal ((cubeVolume Q)⁻¹) *
      ∑ R ∈ descendantsAtDepth Q j,
        ∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂(volume.restrict (cubeSet R)) =
      ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ) := by
    have hsum1 : ∑ R ∈ descendantsAtDepth Q j,
        ∫⁻ x, ‖f x‖ₑ ^ (3 : ℕ) ∂(volume.restrict (cubeSet R)) =
      ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal (cubeVolume R) *
        (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ) :=
      Finset.sum_congr rfl fun R hR => hpercube R hR
    rw [hsum1,
      Finset.mul_sum (f := fun R : TriadicCube d => ENNReal.ofReal (cubeVolume R) *
        (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ)),
      Finset.mul_sum (f := fun R : TriadicCube d =>
        (Section2.Norms.cubeLpENorm R 3 f) ^ (3 : ℕ))]
    exact Finset.sum_congr rfl fun R hR => by
      rw [← mul_assoc, hofreal R hR]
  exact hstep

/-! ## The per-cube Poincaré average at the carrier -/

/-! ## The per-cube Poincaré step `hPoincare` of the assembly -/

/-! ## The sample-side side conditions at the carriers -/

end

end SuperdiffusionCLT.Section3.Terms
