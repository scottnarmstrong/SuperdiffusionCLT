/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Measurable
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscFluxSeminorm
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgFinalD
public import SuperdiffusionCLT.Section3.Setup.RootBlupPrinted

/-!
# Integrability inputs for the printed flux estimate

The energy has a deterministic integrable envelope. Its three-quarter power
therefore belongs to L^{4/3}. The block tail supplies L⁴ membership, and
Hölder supplies product integrability. No quantitative flux estimate is assumed
in these integrability statements.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open scoped BigOperators

/-- The local energy is integrable without shell-law assumptions. -/
theorem rhsTerm3Integrable_integrable_energy {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hnm : S.n ≤ S.m)
    (e : Homogenization.Vec d) {R : Homogenization.TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m) :
    MeasureTheory.Integrable (fun ω => oscEnergy nu hnu S P e ω R) P.toMeasure := by
  simpa only [oscEnergy, energyL2Carrier_eq_volumeAverage_openCubeSet,
    gluedMaximizerGrad, gluedSubcubeGrad] using
    integrable_hEnergyIntDiff_discharged d hnu P S hnm e R hR

/-- The energy membership required by the flux Hölder step. -/
theorem rhsTerm3Integrable_memLp_energy {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hnm : S.n ≤ S.m)
    (e : Homogenization.Vec d) {R : Homogenization.TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m) :
    MeasureTheory.MemLp (fun ω => oscEnergy nu hnu S P e ω R ^ ((3 : ℝ) / 4))
      (ENNReal.ofReal ((4 : ℝ) / 3)) P.toMeasure := by
  have h := (MeasureTheory.memLp_one_iff_integrable.mpr
    (rhsTerm3Integrable_integrable_energy hnu P S hnm e hR)).norm_rpow_div
    (ENNReal.ofReal ((3 : ℝ) / 4))
  have hp : (1 : ENNReal) / ENNReal.ofReal ((3 : ℝ) / 4) =
      ENNReal.ofReal ((4 : ℝ) / 3) := by
    rw [one_div, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
    norm_num
  simpa only [hp, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 4),
    Real.norm_eq_abs, abs_of_nonneg (oscEnergy_nonneg hnu S P e _ R)] using h

/-- A measurable Gamma-one block envelope has the fourth moment needed by Hölder. -/
theorem rhsTerm3Integrable_memLp_block {α : Type*} [MeasurableSpace α]
    (P : MeasureTheory.ProbabilityMeasure α) {B : α → ℝ} {K : ℝ} (hK : 0 < K)
    (hB : AEMeasurable B P.toMeasure)
    (hTail : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) B K) :
    MeasureTheory.MemLp B (ENNReal.ofReal (4 : ℝ)) P.toMeasure := by
  have hm := Homogenization.IndependentSums.hasGammaMomentGrowthWith_of_isBigO_gammaSigma
    (by norm_num : (0 : ℝ) < 1) hK hB hTail
  have hi := (hm (by norm_num : (1 : ℝ) ≤ 4)).1
  apply (MeasureTheory.integrable_norm_rpow_iff hB.aestronglyMeasurable
    (by norm_num : ENNReal.ofReal (4 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mp
  simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)] using hi

end SuperdiffusionCLT.Section3.Terms
