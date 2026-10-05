/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Holder

/-!
# General lattice-shift covariance, the Hoelder step, and the carrier swap

The printed Hoelder display in the proof of `l.RHS.term3` passes from
`E[avsum_{z'} |(nabla w)_{z'+cu_k}|^2 avsum_{z in z' + 3^n Z^d cap cu_k} F(z)]`
to `E[|avsum_{z in 3^n Z^d cap cu_k} F(z)|^2]^{1/2}
E[||nabla w||^4_{L4bar(cu_m)}]^{1/2}`.  The paper does this silently: the inner average
over `z in z' + 3^n Z^d cap cu_k` is replaced by an average over
`z in 3^n Z^d cap cu_k` in the three moment factors, and the weight
`|(nabla w)_{z'+cu_k}|^2` is decoupled from the coarse blocks without stating an
independence or a Cauchy-Schwarz in the pair `(z,z')`.  This module supplies
the two missing ingredients and the resulting estimate.

* **General lattice-shift covariance.**  `Section3/Terms/TranslatedBlocks.lean`
  proves the shift-to-origin case only.  `sum_descendants_translate` shifts one
  scale-`k` cube onto another, carrying the whole family of scale-`n`
  descendants with it; with the invariance of the shell law
  (`ShellField.map_translateSequence_eq`) it gives
  `integral_sq_descendantAverage_eq`, i.e. the second moment of the inner
  average does not depend on which scale-`k` cube it is read on.
* **The fourth-power sub-cube Jensen inequality.**
  `cubeLpENorm_four_pow_eq_inv_card_mul_sum` and
  `integral_subcube_fourth_average_le` are the fourth-power analogues of
  `ofReal_vecNormSq_volumeAverageVec_le` and
  `cubeLpENorm_two_sq_eq_inv_card_mul_sum`:
  `avsum_{z'} |(nabla w)_{z'+cu_k}|^4 <= ||nabla w||^4_{L4bar(cu_m)}`.

`weightedBlockAverage_integral_le` is the printed Hoelder step itself, at the
carrier `weightedBlockAverage`: Cauchy-Schwarz in `omega` on each `z'`,
then Cauchy-Schwarz in `z'` (the step the print does not state), then the
fourth-power Jensen inequality.  Its two `L^2(P)` side conditions are genuine:
there is no measurability datum on `w` at this surface.

The last section is the algebra of the carrier swap in the proof of `l.RHS.term3`, whose
replacement error is `translatedStreamQuadFormGap`.

## Main results

* `sum_descendants_translate`, `memLp_two_descendantAverage_translate`,
  `integral_sq_descendantAverage_eq`.
* `cubeLpENorm_four_pow_eq_inv_card_mul_sum`,
  `integral_subcube_fourth_average_le`.
* `integral_mul_le_sqrt_mul_sqrt`, `inv_card_sum_sqrt_le_sqrt`,
  `weightedBlockAverage_integral_le`.
* `translatedStreamQuadFormGap_eq_abs_sub`,
  `translatedStreamQuadFormLower_le_nuInv_mul`,
  `measurable_translatedStreamQuadFormGap`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## General lattice-shift covariance -/

/-- Translating a shell sequence by `z + w` is translating it by `w` and then
by `z`. -/
theorem translateSequence_add (z w : Vec d) (omega : ShellSeq d) :
    ShellField.translateSequence (z + w) omega =
      ShellField.translateSequence z (ShellField.translateSequence w omega) := by
  funext nn
  refine ShellField.ext fun x => ?_
  rw [ShellField.translateSequence_apply, ShellField.translateSequence_apply,
    ShellField.translateSequence_apply, ShellField.translate_apply,
    ShellField.translate_apply, ShellField.translate_apply, add_assoc]

/-- Two triadic cubes of the same scale differ by an integer index shift. -/
theorem eq_translateCube_of_scale_eq {Q Q' : TriadicCube d} (h : Q.scale = Q'.scale) :
    Q' = translateCube (fun i => Q'.index i - Q.index i) Q := by
  cases Q with
  | mk s idx =>
    cases Q' with
    | mk s' idx' =>
      simp only at h
      subst h
      refine congrArg (fun f : Fin d → ℤ => TriadicCube.mk s f) ?_
      funext i
      show idx' i = idx i + (idx' i - idx i)
      ring

/-- Shifting the index of a triadic cube shifts its translation vector by the
corresponding physical vector. -/
theorem triadicCubeShift_translateCube (t : Fin d → ℤ) (R : TriadicCube d) :
    triadicCubeShift (translateCube t R) =
      fun i => triadicCubeShift R i + (t i : ℝ) * (3 : ℝ) ^ R.scale := by
  funext i
  show (((R.index i + t i : ℤ)) : ℝ) * cubeScaleFactor (translateCube t R) =
    ((R.index i : ℝ) * cubeScaleFactor R + (t i : ℝ) * (3 : ℝ) ^ R.scale)
  show (((R.index i + t i : ℤ)) : ℝ) * (3 : ℝ) ^ R.scale =
    ((R.index i : ℝ) * (3 : ℝ) ^ R.scale + (t i : ℝ) * (3 : ℝ) ^ R.scale)
  push_cast
  ring

/-- **The lattice vector carrying `Q` onto `Q'`**, for two triadic cubes of the
same scale.  It is the single vector by which the whole family of descendants of
`Q` is translated onto the family of descendants of `Q'`. -/
def cubeShiftVector (Q Q' : TriadicCube d) : Vec d :=
  fun i => ((Q'.index i - Q.index i : ℤ) : ℝ) * (3 : ℝ) ^ Q.scale

/-- Every depth-`j` descendant of `Q` is translated onto the corresponding
descendant of `Q'` by the *same* vector `cubeShiftVector Q Q'`. -/
theorem triadicCubeShift_descendant_translate {Q Q' : TriadicCube d}
    {j : ℕ} {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    triadicCubeShift
        (translateCube (descendantTranslationShift j
          (fun i => Q'.index i - Q.index i)) R) =
      fun i => triadicCubeShift R i + cubeShiftVector Q Q' i := by
  have hRs : R.scale = Q.scale - (j : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hR
  rw [triadicCubeShift_translateCube]
  funext i
  have hpow : (3 : ℝ) ^ j * (3 : ℝ) ^ R.scale = (3 : ℝ) ^ Q.scale := by
    rw [hRs, ← zpow_natCast (3 : ℝ) j, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  show triadicCubeShift R i +
      (((3 : ℤ) ^ j * (Q'.index i - Q.index i) : ℤ) : ℝ) * (3 : ℝ) ^ R.scale =
    triadicCubeShift R i + ((Q'.index i - Q.index i : ℤ) : ℝ) * (3 : ℝ) ^ Q.scale
  rw [← hpow]
  push_cast
  ring

/-- **General lattice-shift covariance of a descendant sum**,
in the form the Hoelder display in the proof of `l.RHS.term3` needs.

`hcov` is the shift-to-origin covariance of `Section3/Terms/TranslatedBlocks.lean`
(`translatedBlockNorm_eq_originCube`, `sigmaStarInvCoarse_cubeSet_translate`,
`volumeAverageMat_cubeSet_finiteShellIncrement_translate`).  The conclusion is
its consequence for two cubes of the same scale: the sum of `F` over the
depth-`j` descendants of `Q'` is the sum over the depth-`j` descendants of `Q`
for the single translated shell sequence. -/
theorem sum_descendants_translate {F : ShellSeq d → TriadicCube d → ℝ}
    (hcov : ∀ (omega : ShellSeq d) (Q : TriadicCube d), F omega Q =
      F (ShellField.translateSequence (triadicCubeShift Q) omega) (originCube d Q.scale))
    {Q Q' : TriadicCube d} (hscale : Q.scale = Q'.scale) (j : ℕ) (omega : ShellSeq d) :
    ∑ z ∈ descendantsAtDepth Q' j, F omega z =
      ∑ z ∈ descendantsAtDepth Q j,
        F (ShellField.translateSequence (cubeShiftVector Q Q') omega) z := by
  classical
  set s : Fin d → ℤ := fun i => Q'.index i - Q.index i with hs
  have hQ' : Q' = translateCube s Q := eq_translateCube_of_scale_eq hscale
  have hset : descendantsAtDepth Q' j =
      (descendantsAtDepth Q j).image (translateCube (descendantTranslationShift j s)) := by
    conv_lhs => rw [hQ']
    rw [descendantsAtDepth_translateCube]
  rw [hset, Finset.sum_image
    (fun R _ R' _ h =>
      Book.Ch02.translateCube_injective (descendantTranslationShift j s) h)]
  refine Finset.sum_congr rfl fun R hR => ?_
  have hshift := triadicCubeShift_descendant_translate (Q := Q) (Q' := Q') (j := j) hR
  have h1 := hcov omega (translateCube (descendantTranslationShift j s) R)
  have h2 := hcov (ShellField.translateSequence (cubeShiftVector Q Q') omega) R
  rw [h1, h2]
  have hsc : (translateCube (descendantTranslationShift j s) R).scale = R.scale := rfl
  rw [hsc]
  refine congrArg (fun t : ShellSeq d => F t (originCube d R.scale)) ?_
  rw [hshift]
  have hfun : (fun i => triadicCubeShift R i + cubeShiftVector Q Q' i) =
      triadicCubeShift R + cubeShiftVector Q Q' := rfl
  rw [hfun, translateSequence_add]

section Stationarity

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- The inner average of the Hoelder display in the proof of `l.RHS.term3` read on
`Q'` is the inner average read on `Q` for the translated shell sequence. -/
theorem descendantAverage_translate {F : ShellSeq d → TriadicCube d → ℝ}
    (hcov : ∀ (omega : ShellSeq d) (Q : TriadicCube d), F omega Q =
      F (ShellField.translateSequence (triadicCubeShift Q) omega) (originCube d Q.scale))
    {Q Q' : TriadicCube d} (hscale : Q.scale = Q'.scale) (j : ℕ) :
    (fun omega : ShellSeq d => (((descendantsAtDepth Q' j).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth Q' j, F omega z) =
      (fun omega : ShellSeq d => (((descendantsAtDepth Q j).card : ℝ))⁻¹ *
          ∑ z ∈ descendantsAtDepth Q j, F omega z) ∘
        ShellField.translateSequence (cubeShiftVector Q Q') := by
  funext omega
  have hcard : (descendantsAtDepth Q' j).card = (descendantsAtDepth Q j).card := by
    rw [descendantsAtDepth_card, descendantsAtDepth_card]
  rw [hcard]
  exact congrArg (fun t : ℝ => (((descendantsAtDepth Q j).card : ℝ))⁻¹ * t)
    (sum_descendants_translate hcov hscale j omega)

/-- **The inner average is square integrable on every scale-`k` cube as soon as
it is on one of them.** -/
theorem memLp_two_descendantAverage_translate (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {F : ShellSeq d → TriadicCube d → ℝ}
    (hcov : ∀ (omega : ShellSeq d) (Q : TriadicCube d), F omega Q =
      F (ShellField.translateSequence (triadicCubeShift Q) omega) (originCube d Q.scale))
    {Q Q' : TriadicCube d} (hscale : Q.scale = Q'.scale) (j : ℕ)
    (hmem : MemLp (fun omega : ShellSeq d => (((descendantsAtDepth Q j).card : ℝ))⁻¹ *
      ∑ z ∈ descendantsAtDepth Q j, F omega z) 2 P.toMeasure) :
    MemLp (fun omega : ShellSeq d => (((descendantsAtDepth Q' j).card : ℝ))⁻¹ *
      ∑ z ∈ descendantsAtDepth Q' j, F omega z) 2 P.toMeasure := by
  rw [descendantAverage_translate hcov hscale j]
  exact hmem.comp_measurePreserving
    (measurePreserving_translateSequence hPrefix hJ2 (cubeShiftVector Q Q'))

/-- **The second moment of the inner average does not depend on which scale-`k`
cube it is read on**.  This
is the silent replacement made in the Hoelder display of `l.RHS.term3`. -/
theorem integral_sq_descendantAverage_eq (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) {F : ShellSeq d → TriadicCube d → ℝ}
    (hcov : ∀ (omega : ShellSeq d) (Q : TriadicCube d), F omega Q =
      F (ShellField.translateSequence (triadicCubeShift Q) omega) (originCube d Q.scale))
    {Q Q' : TriadicCube d} (hscale : Q.scale = Q'.scale) (j : ℕ)
    (hmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => (((descendantsAtDepth Q j).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth Q j, F omega z) P.toMeasure) :
    ∫ omega : ShellSeq d, ((((descendantsAtDepth Q' j).card : ℝ))⁻¹ *
          ∑ z ∈ descendantsAtDepth Q' j, F omega z) ^ (2 : ℕ) ∂P.toMeasure =
      ∫ omega : ShellSeq d, ((((descendantsAtDepth Q j).card : ℝ))⁻¹ *
          ∑ z ∈ descendantsAtDepth Q j, F omega z) ^ (2 : ℕ) ∂P.toMeasure := by
  have hmap : Measure.map
      (ShellField.translateSequence (cubeShiftVector Q Q')) P.toMeasure = P.toMeasure :=
    ShellField.map_translateSequence_eq hPrefix hJ2 (cubeShiftVector Q Q')
  have heq : (fun omega : ShellSeq d => ((((descendantsAtDepth Q' j).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth Q' j, F omega z) ^ (2 : ℕ)) =
      (fun omega : ShellSeq d => ((((descendantsAtDepth Q j).card : ℝ))⁻¹ *
          ∑ z ∈ descendantsAtDepth Q j, F omega z) ^ (2 : ℕ)) ∘
        ShellField.translateSequence (cubeShiftVector Q Q') := by
    have h := descendantAverage_translate (F := F) hcov hscale j
    funext omega
    exact congrArg (fun t : ℝ => t ^ (2 : ℕ)) (congrFun h omega)
  have hsq : AEStronglyMeasurable
      (fun omega : ShellSeq d => ((((descendantsAtDepth Q j).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth Q j, F omega z) ^ (2 : ℕ))
      (Measure.map (ShellField.translateSequence (cubeShiftVector Q Q')) P.toMeasure) := by
    rw [hmap]
    exact hmeas.pow 2
  rw [heq]
  calc ∫ omega : ShellSeq d, ((fun omega : ShellSeq d =>
          ((((descendantsAtDepth Q j).card : ℝ))⁻¹ *
            ∑ z ∈ descendantsAtDepth Q j, F omega z) ^ (2 : ℕ)) ∘
          ShellField.translateSequence (cubeShiftVector Q Q')) omega ∂P.toMeasure
      = ∫ omega : ShellSeq d, ((((descendantsAtDepth Q j).card : ℝ))⁻¹ *
            ∑ z ∈ descendantsAtDepth Q j, F omega z) ^ (2 : ℕ)
          ∂(Measure.map (ShellField.translateSequence (cubeShiftVector Q Q'))
            P.toMeasure) :=
        (integral_map
          (ShellField.measurable_translateSequence (cubeShiftVector Q Q')).aemeasurable
          hsq).symm
    _ = ∫ omega : ShellSeq d, ((((descendantsAtDepth Q j).card : ℝ))⁻¹ *
            ∑ z ∈ descendantsAtDepth Q j, F omega z) ^ (2 : ℕ) ∂P.toMeasure := by
        rw [hmap]

end Stationarity

/-! ## The fourth-power sub-cube Jensen inequality -/

/-- The fourth power of an `L^4` norm is the lower integral of the fourth power
of the norm; the exponent-4 companion of `eLpNorm_two_sq`
(`Section3/ResponseFields/StationaryComparison.lean`). -/
theorem eLpNorm_four_pow {alpha : Type*} {E : Type*} [MeasurableSpace alpha]
    [NormedAddCommGroup E] (nu : Measure alpha) (f : alpha → E)
    (hf : AEStronglyMeasurable f nu) :
    eLpNorm f 4 nu ^ (4 : ℕ) = ∫⁻ a, ‖f a‖ₑ ^ (4 : ℕ) ∂nu := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ← ENNReal.rpow_natCast _ 4, ← ENNReal.rpow_mul]
  norm_num

/-- **The fourth power of the normalized cube norm is the plain average of the
fourth powers over the sub-cubes at depth `j`**, the exponent-4 companion of
`cubeLpENorm_two_sq_eq_inv_card_mul_sum` (`Section3/Terms/RHSTerm2.lean`).  It is
the tiling identity behind the factor `E[||nabla w||^4_{L4bar(cu_m)}]^{1/2}` of
the Hoelder display in the proof of `l.RHS.term3`. -/
theorem cubeLpENorm_four_pow_eq_inv_card_mul_sum {E : Type*} [NormedAddCommGroup E]
    {Q : TriadicCube d} (j : ℕ) (f : Vec d → E) :
    (Section2.Norms.cubeLpENorm Q 4 f) ^ (4 : ℕ) =
      ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ) := by
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
    have hRtop : (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ) = ⊤ := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_of_not_aestronglyMeasurable hRm]
      simp
    have hQtop : (Section2.Norms.cubeLpENorm Q 4 f) ^ (4 : ℕ) = ⊤ := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_of_not_aestronglyMeasurable hfQ]
      simp
    have hsumtop : ∑ R ∈ descendantsAtDepth Q j,
        (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ) = ⊤ :=
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
      ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (cubeSet R)) =
        ENNReal.ofReal (cubeVolume R) * (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ) := by
    intro R hR
    have hpos : 0 < cubeVolume R := cubeVolume_pos R
    have h2 : ENNReal.ofReal (cubeVolume R) * ENNReal.ofReal ((cubeVolume R)⁻¹) = 1 := by
      rw [mul_comm, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hpos)),
        inv_mul_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one]
    have h1 : (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ) =
        ENNReal.ofReal ((cubeVolume R)⁻¹) *
          ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (cubeSet R)) := by
      rw [Section2.Norms.cubeLpENorm, eLpNorm_four_pow _ _ (hfR R hR),
        normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
        smul_eq_mul, Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet R)]
    rw [h1, ← mul_assoc, h2, one_mul]
  rw [Section2.Norms.cubeLpENorm, eLpNorm_four_pow _ _ hfQ,
    normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
    smul_eq_mul, ← Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q),
    hset, lintegral_biUnion_finset hdisj hmeas]
  have hsum1 : ∑ R ∈ descendantsAtDepth Q j,
      ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (cubeSet R)) =
    ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal (cubeVolume R) *
      (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ) :=
    Finset.sum_congr rfl fun R hR => hpercube R hR
  rw [hsum1,
    Finset.mul_sum (f := fun R : TriadicCube d => ENNReal.ofReal (cubeVolume R) *
      (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ)),
    Finset.mul_sum (f := fun R : TriadicCube d =>
      (Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ))]
  exact Finset.sum_congr rfl fun R hR => by rw [← mul_assoc, hofreal R hR]

/-- **Jensen on a cube at the fourth power**: the fourth power of the magnitude
of the cube average of a vector field is at most its fourth normalized
`L4bar` norm.  The second-power version is
`ofReal_vecNormSq_volumeAverageVec_le` (`Section3/Terms/RHSTerm2Displays.lean`);
the passage from `L2bar` to `L4bar` is the exponent monotonicity of the
normalized cube norm. -/
theorem ofReal_vecNormSq_volumeAverageVec_sq_le {Q : TriadicCube d} {G : Vec d → Vec d}
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ENNReal.ofReal (vecNormSq (volumeAverageVec (openCubeSet Q) G) ^ (2 : ℕ)) ≤
      vecCubeLpENorm Q 4 G ^ (4 : ℕ) := by
  have h2 := ofReal_vecNormSq_volumeAverageVec_le hG
  have hmono : vecCubeLpENorm Q 2 G ≤ vecCubeLpENorm Q 4 G :=
    vecCubeLpENorm_mono_exponent Q (by norm_num)
      (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2 hG)
  rw [ENNReal.ofReal_pow (vecNormSq_nonneg _) 2]
  calc (ENNReal.ofReal (vecNormSq (volumeAverageVec (openCubeSet Q) G))) ^ (2 : ℕ)
      ≤ ((vecCubeLpENorm Q 2 G) ^ (2 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left' h2 2
    _ = (vecCubeLpENorm Q 2 G) ^ (4 : ℕ) := by rw [← pow_mul]
    _ ≤ (vecCubeLpENorm Q 4 G) ^ (4 : ℕ) := pow_le_pow_left' hmono 4

/-- **`avsum_{z'} |(nabla w)_{z'+cu_k}|^4 <= ||nabla w||^4_{L4bar(cu_m)}`**, the
fourth-power form of the sub-cube Jensen step the paper performs silently in the
Hoelder display of `l.RHS.term3`. -/
theorem ofReal_subcube_fourth_average_le {k m : ℕ} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) g) :
    ENNReal.ofReal (((largeCubeSubcubes d k m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d k m,
          vecNormSq (volumeAverageVec (openCubeSet z') g) ^ (2 : ℕ)) ≤
      vecCubeLpENorm (originCube d (m : ℤ)) 4 g ^ (4 : ℕ) := by
  classical
  have hnn : ∀ z' ∈ largeCubeSubcubes d k m,
      (0 : ℝ) ≤ vecNormSq (volumeAverageVec (openCubeSet z') g) ^ (2 : ℕ) :=
    fun _ _ => pow_nonneg (vecNormSq_nonneg _) 2
  have hcard : (0 : ℝ) ≤ ((largeCubeSubcubes d k m).card : ℝ)⁻¹ := by positivity
  rw [ENNReal.ofReal_mul hcard, ENNReal.ofReal_sum_of_nonneg hnn]
  have hstep : ∀ z' ∈ largeCubeSubcubes d k m,
      ENNReal.ofReal (vecNormSq (volumeAverageVec (openCubeSet z') g) ^ (2 : ℕ)) ≤
        vecCubeLpENorm z' 4 g ^ (4 : ℕ) :=
    fun _ hz' => ofReal_vecNormSq_volumeAverageVec_sq_le (memVectorL2_subcube hz' hg)
  refine le_trans (mul_le_mul_right (Finset.sum_le_sum hstep) _) ?_
  rw [show vecCubeLpENorm (originCube d (m : ℤ)) 4 g ^ (4 : ℕ) =
      (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 4 (hilbertifyVecField g)) ^ (4 : ℕ)
      from rfl,
    cubeLpENorm_four_pow_eq_inv_card_mul_sum (m - k) (hilbertifyVecField g)]
  exact le_rfl

/-- The expectation form of `ofReal_subcube_fourth_average_le`.  `hfin` is the
finiteness of the fourth moment on the right, which the Bochner integral on the
left needs in order to be compared with a `toReal`; it is supplied by the first
conjunct of `l.w.basic.regbounds`. -/
theorem integral_subcube_fourth_average_le {k m : ℕ} (P : ProbabilityMeasure (ShellSeq d))
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ))))
    (hfin : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
        ∂P.toMeasure) ≠ ⊤) :
    ∫ omega : ShellSeq d, (((largeCubeSubcubes d k m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d k m,
          vecNormSq (volumeAverageVec (openCubeSet z')
            ((w omega).toH1Function.grad)) ^ (2 : ℕ)) ∂P.toMeasure ≤
      gradResponseMoment (m := m) 4 4 P w := by
  classical
  set F : ShellSeq d → ℝ := fun omega => ((largeCubeSubcubes d k m).card : ℝ)⁻¹ *
    ∑ z' ∈ largeCubeSubcubes d k m,
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ) with hFdef
  have hnn : ∀ omega : ShellSeq d, (0 : ℝ) ≤ F omega := by
    intro omega
    rw [hFdef]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => ?_)
    exact pow_nonneg (vecNormSq_nonneg _) 2
  by_cases hint : Integrable F P.toMeasure
  · have heq := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (f := F) (μ := P.toMeasure) (Filter.Eventually.of_forall hnn)
      hint.aestronglyMeasurable
    have hmono : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (F omega) ∂P.toMeasure) ≤
        ∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm (originCube d (m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
          ∂P.toMeasure :=
      lintegral_mono fun omega =>
        ofReal_subcube_fourth_average_le (w omega).toH1Function.grad_memVectorL2
    rw [heq]
    exact ENNReal.toReal_mono hfin hmono
  · rw [MeasureTheory.integral_undef hint]
    exact gradResponseMoment_nonneg 4 4 P w

/-! ## The Hoelder step -/

/-- Cauchy-Schwarz for the expectation of a product of two square-integrable
random variables. -/
theorem integral_mul_le_sqrt_mul_sqrt {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f g : Omega → ℝ} (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    ∫ a, f a * g a ∂mu ≤
      Real.sqrt (∫ a, f a ^ (2 : ℕ) ∂mu) * Real.sqrt (∫ a, g a ^ (2 : ℕ) ∂mu) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num
  have hf2 : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by rwa [htwo]
  have hg2 : MemLp g (ENNReal.ofReal (2 : ℝ)) mu := by rwa [htwo]
  have hmain := integral_mul_norm_le_Lp_mul_Lq hpq hf2 hg2
  have hstep1 : ∫ a, f a * g a ∂mu ≤ ∫ a, ‖f a‖ * ‖g a‖ ∂mu := by
    refine integral_mono (hf.integrable_mul hg) (hf.norm.integrable_mul hg.norm)
      (fun a => ?_)
    exact le_trans (le_abs_self _) (by rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs])
  have hconv : ∀ h : Omega → ℝ, ∫ a, ‖h a‖ ^ (2 : ℝ) ∂mu = ∫ a, h a ^ (2 : ℕ) ∂mu := by
    intro h
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show ‖h a‖ ^ (2 : ℝ) = h a ^ (2 : ℕ)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
      sq_abs]
  rw [hconv f, hconv g] at hmain
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact le_trans hstep1 hmain

/-- Cauchy-Schwarz for a finite average: the average of the square roots is at
most the square root of the average.  This is the second Cauchy-Schwarz of the
Hoelder display, the one in the outer lattice variable `z'` that the paper does
not state. -/
theorem inv_card_sum_sqrt_le_sqrt {iota : Type*} (s : Finset iota) (b : iota → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) :
    (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.sqrt (b i) ≤
      Real.sqrt ((s.card : ℝ)⁻¹ * ∑ i ∈ s, b i) := by
  classical
  rcases Finset.eq_empty_or_nonempty s with hs | hs
  · subst hs
    simp
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hsum0 : (0 : ℝ) ≤ ∑ i ∈ s, b i := Finset.sum_nonneg hb
  have hlhs0 : (0 : ℝ) ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.sqrt (b i) :=
    mul_nonneg (le_of_lt (inv_pos.2 hcard)) (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  have hrhs0 : (0 : ℝ) ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, b i :=
    mul_nonneg (le_of_lt (inv_pos.2 hcard)) hsum0
  rw [Real.le_sqrt hlhs0 hrhs0]
  have hcheb : (∑ i ∈ s, Real.sqrt (b i)) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, Real.sqrt (b i) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hsq : ∑ i ∈ s, Real.sqrt (b i) ^ 2 = ∑ i ∈ s, b i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (hb i hi)
  rw [hsq] at hcheb
  have hkey : ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.sqrt (b i)) ^ 2 =
      ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, Real.sqrt (b i)) ^ 2 := by ring
  rw [hkey]
  have hmul := mul_le_mul_of_nonneg_left hcheb (le_of_lt (pow_pos (inv_pos.2 hcard) 2))
  refine le_trans hmul (le_of_eq ?_)
  field_simp

/-- **The Hoelder step in the proof of `l.RHS.term3`**,
at the carrier `weightedBlockAverage` (`Section3/Terms/RHSTerm3StepsC.lean`):

`E[avsum_{z'} |(nabla w)_{z'+cu_k}|^2 avsum_{z in z'+3^n Z^d cap cu_k} F(z)]
  <= M E[||nabla w||^4_{L4bar(cu_m)}]^{1/2}`

whenever `M` dominates the `L^2(P)` norm of each inner average.  The proof is
the one the print compresses: Cauchy-Schwarz in `omega` on each outer cube `z'`
(`integral_mul_le_sqrt_mul_sqrt`), then Cauchy-Schwarz in `z'`
(`inv_card_sum_sqrt_le_sqrt`, a step the paper does not state), then the
fourth-power sub-cube Jensen inequality
(`integral_subcube_fourth_average_le`).

`hsq` and `hAvg` are square-integrability side conditions: there is no
measurability datum on `w` at this surface, so neither is derivable here. -/
theorem weightedBlockAverage_integral_le {n k m : ℕ} (P : ProbabilityMeasure (ShellSeq d))
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ))))
    (F : ShellSeq d → TriadicCube d → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hfin : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
        ∂P.toMeasure) ≠ ⊤)
    (hsq : ∀ z' ∈ largeCubeSubcubes d k m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) 2 P.toMeasure)
    (hAvg : ∀ z' ∈ largeCubeSubcubes d k m,
      MemLp (fun omega : ShellSeq d =>
        (((descendantsAtDepth z' (k - n)).card : ℝ))⁻¹ *
          ∑ z ∈ descendantsAtDepth z' (k - n), F omega z) 2 P.toMeasure)
    (hMbd : ∀ z' ∈ largeCubeSubcubes d k m,
      ∫ omega : ShellSeq d, ((((descendantsAtDepth z' (k - n)).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth z' (k - n), F omega z) ^ (2 : ℕ) ∂P.toMeasure ≤
      M ^ (2 : ℕ)) :
    ∫ omega : ShellSeq d,
        weightedBlockAverage d n k m ((w omega).toH1Function.grad) (F omega)
        ∂P.toMeasure ≤
      M * gradResponseMoment (m := m) 4 4 P w ^ ((1 : ℝ) / 2) := by
  classical
  set s : Finset (TriadicCube d) := largeCubeSubcubes d k m with hsdef
  set G : TriadicCube d → ShellSeq d → ℝ := fun z' omega =>
    vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) with hGdef
  set A : TriadicCube d → ShellSeq d → ℝ := fun z' omega =>
    (((descendantsAtDepth z' (k - n)).card : ℝ))⁻¹ *
      ∑ z ∈ descendantsAtDepth z' (k - n), F omega z with hAdef
  have hInt : ∀ z' ∈ s, Integrable (fun omega : ShellSeq d => G z' omega * A z' omega)
      P.toMeasure := fun z' hz' => (hsq z' hz').integrable_mul (hAvg z' hz')
  have hsplit : ∫ omega : ShellSeq d,
        weightedBlockAverage d n k m ((w omega).toH1Function.grad) (F omega) ∂P.toMeasure =
      ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, ∫ omega : ShellSeq d, G z' omega * A z' omega
        ∂P.toMeasure := by
    have hpt : ∀ omega : ShellSeq d,
        weightedBlockAverage d n k m ((w omega).toH1Function.grad) (F omega) =
          ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, G z' omega * A z' omega := fun _ => rfl
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum s hInt]
  set b : TriadicCube d → ℝ := fun z' =>
    ∫ omega : ShellSeq d, G z' omega ^ (2 : ℕ) ∂P.toMeasure with hbdef
  have hb0 : ∀ z' ∈ s, 0 ≤ b z' := by
    intro z' _
    exact MeasureTheory.integral_nonneg fun _ => pow_nonneg (vecNormSq_nonneg _) 2
  have hCS : ∀ z' ∈ s, ∫ omega : ShellSeq d, G z' omega * A z' omega ∂P.toMeasure ≤
      Real.sqrt (b z') * M := by
    intro z' hz'
    have h := integral_mul_le_sqrt_mul_sqrt (hsq z' hz') (hAvg z' hz')
    have hA2 : Real.sqrt (∫ omega : ShellSeq d, A z' omega ^ (2 : ℕ) ∂P.toMeasure) ≤ M := by
      have hMs : M = Real.sqrt (M ^ (2 : ℕ)) := (Real.sqrt_sq hM).symm
      rw [hMs]
      exact Real.sqrt_le_sqrt (hMbd z' hz')
    exact le_trans h (mul_le_mul_of_nonneg_left hA2 (Real.sqrt_nonneg _))
  have hcard0 : (0 : ℝ) ≤ ((s.card : ℝ))⁻¹ := by positivity
  have hstep1 : ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, ∫ omega : ShellSeq d,
        G z' omega * A z' omega ∂P.toMeasure ≤
      M * (((s.card : ℝ))⁻¹ * ∑ z' ∈ s, Real.sqrt (b z')) := by
    have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hCS) hcard0
    calc ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, ∫ omega : ShellSeq d,
          G z' omega * A z' omega ∂P.toMeasure
        ≤ ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, Real.sqrt (b z') * M := hsum
      _ = M * (((s.card : ℝ))⁻¹ * ∑ z' ∈ s, Real.sqrt (b z')) := by
          rw [← Finset.sum_mul]
          ring
  have hfour : ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, b z' ≤
      gradResponseMoment (m := m) 4 4 P w := by
    have hIsq : ∀ z' ∈ s, Integrable (fun omega : ShellSeq d => G z' omega ^ (2 : ℕ))
        P.toMeasure := fun z' hz' => (hsq z' hz').integrable_sq
    have hid : ∫ omega : ShellSeq d, (((s.card : ℝ))⁻¹ *
        ∑ z' ∈ s, G z' omega ^ (2 : ℕ)) ∂P.toMeasure =
        ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, b z' := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum s hIsq]
    rw [← hid]
    exact integral_subcube_fourth_average_le P w hfin
  have hstep2 : ((s.card : ℝ))⁻¹ * ∑ z' ∈ s, Real.sqrt (b z') ≤
      Real.sqrt (gradResponseMoment (m := m) 4 4 P w) :=
    le_trans (inv_card_sum_sqrt_le_sqrt s b hb0) (Real.sqrt_le_sqrt hfour)
  have hrw : gradResponseMoment (m := m) 4 4 P w ^ ((1 : ℝ) / 2) =
      Real.sqrt (gradResponseMoment (m := m) 4 4 P w) := (Real.sqrt_eq_rpow _).symm
  rw [hsplit, hrw]
  exact le_trans hstep1 (mul_le_mul_of_nonneg_left hstep2 hM)

/-! ## Translation covariance of the quadratic tail carrier -/

/-- **`(k_l - k_L)_{z+cu_n}^t s_{L,*}^{-1}(z+cu_n)(k_l - k_L)_{z+cu_n}` is
translation covariant**:
it is built from the two covariant objects
`volumeAverageMat (cubeSet z) (k_l - k_L)` and
`sigmaStarInvCoarse (cubeSet z) a_L` of `Section3/Terms/TranslatedBlocks.lean`. -/
theorem translatedStreamQuadForm_eq_originCube (nu : ℝ) (l L : ℕ) (e : Vec d)
    (omega : ShellSeq d) (Q : TriadicCube d) :
    translatedStreamQuadForm nu l L e omega Q =
      translatedStreamQuadForm nu l L e
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) := by
  have hinc : streamIncrementCubeVec l L e omega Q =
      streamIncrementCubeVec l L e
        (ShellField.translateSequence (triadicCubeShift Q) omega)
        (originCube d Q.scale) := by
    rw [streamIncrementCubeVec, streamIncrementCubeVec,
      volumeAverageMat_cubeSet_finiteShellIncrement_translate omega l L Q]
  rw [translatedStreamQuadForm, translatedStreamQuadForm, hinc,
    sigmaStarInvCoarse_cubeSet_translate nu L omega Q]

/-! ## The carrier swap -/

/-- The replacement error of the carrier swap is the difference of the two tested
quadratic forms. -/
theorem translatedStreamQuadFormGap_eq_abs_sub (nu : ℝ) (l L : ℕ) (e : Vec d)
    (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamQuadFormGap nu l L e omega z =
      |translatedStreamQuadFormLower nu l L e omega z -
        translatedStreamQuadForm nu l L e omega z| := by
  rw [translatedStreamQuadFormGap, translatedStreamQuadFormLower,
    translatedStreamQuadForm]
  refine congrArg abs ?_
  rw [sub_matVecMul, sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]

/-- **`q_{s_{l,*}^{-1}}(v) <= nu^{-1}|v|^2`**, the crude quenched ellipticity
bound `e.CG.bounds.1` on a translated cube. -/
theorem translatedStreamQuadFormLower_le_nuInv_mul [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (e : Vec d) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamQuadFormLower nu l L e omega z ≤
      nu⁻¹ * translatedStreamNormSq l L e omega z := by
  have hL := matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega l z
    (streamIncrementCubeVec l L e omega z)
  have hrw : Homogenization.sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega l).toFun =
      Homogenization.sigmaStarInvCoarse (cubeSet z)
        (coefficientCutoff nu omega l).toCoeffField := by
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    rfl
  rw [hrw] at hL
  have hsm : vecDot (streamIncrementCubeVec l L e omega z)
      (matVecMul (nu⁻¹ • (1 : Mat d)) (streamIncrementCubeVec l L e omega z)) =
      nu⁻¹ * translatedStreamNormSq l L e omega z := by
    rw [smul_matVecMul, vecDot_smul_right]
    refine congrArg (fun t : ℝ => nu⁻¹ * t) ?_
    show vecDot (streamIncrementCubeVec l L e omega z)
        (matVecMul (1 : Mat d) (streamIncrementCubeVec l L e omega z)) =
      vecDot (streamIncrementCubeVec l L e omega z)
        (streamIncrementCubeVec l L e omega z)
    refine congrArg (fun u : Vec d =>
      vecDot (streamIncrementCubeVec l L e omega z) u) ?_
    funext i
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  rw [hsm] at hL
  show vecDot (streamIncrementCubeVec l L e omega z)
      (matVecMul (Homogenization.sigmaStarInvCoarse (cubeSet z)
        (coefficientCutoff nu omega l).toCoeffField)
        (streamIncrementCubeVec l L e omega z)) ≤
    nu⁻¹ * translatedStreamNormSq l L e omega z
  linarith only [hL]

/-- `0 <= q_{s_{l,*}^{-1}}(v)`. -/
theorem translatedStreamQuadFormLower_nonneg [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (e : Vec d) (omega : ShellSeq d) (z : TriadicCube d) :
    0 ≤ translatedStreamQuadFormLower nu l L e omega z := by
  have h := (posSemidef_sigmaStarInvCoarse_cutoffCube hnu l omega z).dotProduct_mulVec_nonneg
    (streamIncrementCubeVec l L e omega z)
  simpa only [translatedStreamQuadFormLower, dotProduct, Matrix.mulVec, vecDot, matVecMul,
    RCLike.star_def, conj_trivial, star_trivial] using h

private theorem measurable_vecDotMatVec {Omega : Type*} [MeasurableSpace Omega]
    {M : Omega → Mat d} {v : Omega → Vec d}
    (hM : ∀ i j, Measurable fun omega => M omega i j)
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot (v omega) (matVecMul (M omega) (v omega)) := by
  simp only [vecDot, matVecMul]
  exact Finset.measurable_sum _ fun i _ =>
    (hv i).mul (Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j))

theorem measurable_translatedStreamQuadFormLower [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (e : Vec d) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d =>
      translatedStreamQuadFormLower nu l L e omega z := by
  refine measurable_vecDotMatVec (fun i j => ?_)
    (measurable_streamIncrementCubeVec_apply l L e z)
  have h : (fun omega : ShellSeq d =>
      Homogenization.sigmaStarInvCoarse (cubeSet z)
        (coefficientCutoff nu omega l).toCoeffField i j) =
      fun omega : ShellSeq d =>
        Homogenization.sigmaStarInvCoarse (openCubeSet z)
          (coefficientCutoff nu omega l).toFun i j := by
    funext omega
    rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet]
    rfl
  rw [h]
  exact measurable_sigmaStarInvCoarse_apply (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) z i j

theorem measurable_translatedStreamQuadFormGap [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (e : Vec d) (z : TriadicCube d) :
    Measurable fun omega : ShellSeq d =>
      translatedStreamQuadFormGap nu l L e omega z := by
  have heq : (fun omega : ShellSeq d => translatedStreamQuadFormGap nu l L e omega z) =
      fun omega : ShellSeq d => |translatedStreamQuadFormLower nu l L e omega z -
        translatedStreamQuadForm nu l L e omega z| :=
    funext fun omega => translatedStreamQuadFormGap_eq_abs_sub nu l L e omega z
  rw [heq]
  exact continuous_abs.measurable.comp
    ((measurable_translatedStreamQuadFormLower hnu l L e z).sub
      (measurable_translatedStreamQuadForm hnu l L e z))

/-- The fourth moment of a `Γ₁` variable. -/
theorem integral_fourth_le_of_isBigO_gammaSigma_one
    {P : ProbabilityMeasure (ShellSeq d)} {Y : ShellSeq d → ℝ} {K : ℝ}
    (hK : 0 < K) (hYm : Measurable Y) (hY : IsBigO P.toMeasure (gammaSigma 1) Y K) :
    Integrable (fun omega : ShellSeq d => Y omega ^ (4 : ℕ)) P.toMeasure ∧
      ∫ omega : ShellSeq d, Y omega ^ (4 : ℕ) ∂P.toMeasure ≤
        (4 * gammaMomentConst 1 * K) ^ (4 : ℕ) := by
  have hgrow := hasGammaMomentGrowthWith_of_isBigO_gammaSigma (μ := P.toMeasure)
    (show (0 : ℝ) < 1 by norm_num) hK hYm.aemeasurable hY
  obtain ⟨hint, hbd⟩ := hgrow (show (1 : ℝ) ≤ 4 by norm_num)
  have hpt : ∀ omega : ShellSeq d, |Y omega| ^ (4 : ℝ) = Y omega ^ (4 : ℕ) := by
    intro omega
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow]
    exact abs_of_nonneg (by positivity)
  refine ⟨hint.congr (Filter.Eventually.of_forall hpt), ?_⟩
  have heq : ∫ omega : ShellSeq d, |Y omega| ^ (4 : ℝ) ∂P.toMeasure =
      ∫ omega : ShellSeq d, Y omega ^ (4 : ℕ) ∂P.toMeasure :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hpow : ((4 : ℝ) ^ ((1 : ℝ)⁻¹)) = 4 := by
    rw [inv_one, Real.rpow_one]
  rw [heq, hpow] at hbd
  have hrw : (gammaMomentConst 1 * K * 4) ^ (4 : ℝ) =
      (4 * gammaMomentConst 1 * K) ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hrw] at hbd
  exact hbd

end

end SuperdiffusionCLT.Section3.Terms
