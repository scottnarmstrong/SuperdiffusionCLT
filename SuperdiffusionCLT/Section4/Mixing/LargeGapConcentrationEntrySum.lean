/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationCore
public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationLocality

/-!
# The colour-partitioned `Γ₁` concentration of one entry, and the entrywise sum

`p.mixing.P.three.prime#large-gap-case`: applies
`mixGap_blockConcentrationGamma1` (`LargeGapConcentrationCore.lean`) to the
entrywise deviation `bfA_L(z+cu_n)_{αβ} - bfAhom_L(cu_n)_{αβ}`, with the
colour partition of `Section3.Terms.RHSTerm3InputsC` (`blockSublattice`,
`biUnion_blockSublattice`, `disjoint_blockSublattice`, `card_univ_blockClass`,
`areShellSeparated_of_subset_cubeSet`) at range `ell = L`, exactly mirroring
`Section3.Terms.blockDeviation_concentration`'s instantiation of
`block_concentration`. Then combines the `(2d)² = 4d²` many entries via the
`Γ1` triangle inequality
(`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`) into
a single random variable `mixGap_entrySumEnvelope` dominating the absolute
value of every entry of the averaged deviation matrix simultaneously. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Terms

noncomputable section

variable {d : ℕ}

/-- **The `Γ1` concentration of one entry, colour-partitioned exactly as
`Section3.Terms.blockDeviation_concentration`** (range `ell = L`, so no
gauge/localization decomposition is needed: this is the direct comparison
`bfA_L(z+cu_n) - bfAhom_L(cu_n)`, matching the large-gap case's printed
proposition `p.concentration` applied "with `σ=1`"). -/
theorem mixGap_entryDeviation_concentration [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nn L kk : ℕ} (hnl : nn ≤ L) (hlk : L ≤ kk)
    (alpha beta : BlockCoord d) {z' : TriadicCube d} (hz' : z'.scale = (kk : ℤ)) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d => ((descendantsAtDepth z' (kk - nn)).card : ℝ)⁻¹ *
        ∑ z ∈ descendantsAtDepth z' (kk - nn),
          (blockMatEntry (coarseBlockMatrix (cubeSet z)
              (coefficientCutoff nu omega L).toCoeffField) alpha beta -
            blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ))))
              alpha beta))
      (2 * gammaTriangleConst 1 * gammaOneExpRegimeConst *
          Real.sqrt (((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d) *
          (mixGap_entryEnvelope d nu L +
            IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L) *
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - L : ℕ) : ℝ)) / 2)) := by
  classical
  set D : Finset (TriadicCube d) := descendantsAtDepth z' (kk - nn) with hD
  have hscale : ∀ z ∈ D, z.scale = (nn : ℤ) := by
    intro z hz
    have h := scale_eq_sub_of_mem_descendantsAtDepth (hD ▸ hz)
    rw [hz'] at h
    rw [h, Nat.cast_sub (le_trans hnl hlk)]
    ring
  set nbhd : TriadicCube d → Set (Vec d) := fun z =>
    if z.scale = (nn : ℤ) then cubeSet (coarseAncestor nn L z) else Set.univ
    with hnbhddef
  have hnbhd : ∀ z : TriadicCube d, MeasurableSet (nbhd z) := by
    intro z
    rw [hnbhddef]
    by_cases h : z.scale = (nn : ℤ)
    · simp only [h, ↓reduceIte]
      exact measurableSet_cubeSet _
    · simp only [h, ↓reduceIte]
      exact MeasurableSet.univ
  have hsubn : ∀ z : TriadicCube d, cubeSet z ⊆ nbhd z := by
    intro z
    rw [hnbhddef]
    by_cases h : z.scale = (nn : ℤ)
    · simp only [h, ↓reduceIte]
      exact cubeSet_subset_coarseAncestor hnl h
    · simp only [h, ↓reduceIte]
      exact Set.subset_univ _
  have hnbhd_eq : ∀ z : TriadicCube d, z.scale = (nn : ℤ) →
      nbhd z = cubeSet (coarseAncestor nn L z) := by
    intro z h
    rw [hnbhddef]
    simp only [h, ↓reduceIte]
  have hsep : ∀ c ∈ (Finset.univ :
        Finset ((Fin d → Fin (3 ^ (L - nn))) × ShellField.ShellCubeColor d)),
      ∀ z ∈ blockSublattice nn L D c, ∀ z2 ∈ blockSublattice nn L D c, z ≠ z2 →
        ShellField.AreShellSeparated L (nbhd z) (nbhd z2) := by
    intro c _ z hz z2 hz2 hne
    have hzs : z.scale = (nn : ℤ) := hscale z (blockSublattice_subset nn L D c hz)
    have hz2s : z2.scale = (nn : ℤ) := hscale z2 (blockSublattice_subset nn L D c hz2)
    have hcls : blockClassIndex nn L z = blockClassIndex nn L z2 :=
      (blockClassIndex_of_mem_blockSublattice hz).trans
        (blockClassIndex_of_mem_blockSublattice hz2).symm
    rw [hnbhd_eq z hzs, hnbhd_eq z2 hz2s]
    refine areShellSeparated_of_subset_cubeSet (kk := L) le_rfl
      (coarseAncestor_scale nn L z) (coarseAncestor_scale nn L z2)
      (congrArg Prod.snd hcls) ?_ subset_rfl subset_rfl
    intro hcon
    exact hne (eq_of_coarseAncestor_eq_of_blockClassIndex_eq hzs hz2s hcls hcon)
  have hKpos : (0 : ℝ) < mixGap_entryEnvelope d nu L +
      IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L := by
    have h1 := mixGap_entryEnvelope_pos hnu d L
    have h2 : (0:ℝ) ≤ IndependentSums.gammaMomentConst 1 * mixGap_entryEnvelope d nu L := by
      have := IndependentSums.gammaMomentConst_pos (σ := (1:ℝ)) one_pos
      positivity
    linarith only [h1, h2]
  have hCJ : (0 : ℝ) ≤ ((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d := by positivity
  have hDcard : (D.card : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((kk - nn : ℕ) : ℝ)) := by
    rw [hD, descendantsAtDepth_card,
      show ((d:ℝ) * ((kk-nn:ℕ):ℝ)) = (((d*(kk-nn) : ℕ)):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    rw [pow_mul]
  have hJcard : (((Finset.univ :
        Finset ((Fin d → Fin (3 ^ (L - nn))) ×
          ShellField.ShellCubeColor d)).card : ℕ) : ℝ) ≤
      ((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d *
        (3 : ℝ) ^ ((d : ℝ) * ((L - nn : ℕ) : ℝ)) := by
    rw [card_univ_blockClass,
      show ((d:ℝ) * ((L-nn:ℕ):ℝ)) = (((d*(L-nn) : ℕ)):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    rw [show ((3:ℝ)^(L-nn))^d = ((3:ℝ)^d)^(L-nn) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    exact le_of_eq (by ring)
  exact mixGap_blockConcentrationGamma1 P D Finset.univ (blockSublattice nn L D)
    (fun omega z => blockMatEntry
      (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta -
      blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta)
    hKpos hCJ (hD ▸ descendantsAtDepth_nonempty z' (kk - nn))
    (biUnion_blockSublattice nn L D)
    (fun c _ c' _ hcc => disjoint_blockSublattice nn L D hcc)
    (fun z => (measurable_blockMatEntry_coarseBlockMatrix hnu L z alpha beta).sub
      measurable_const)
    (fun z hz => by
      have h1 : ∫ omega : ShellSeq d, blockMatEntry
          (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta
          ∂P.toMeasure =
          blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta := by
        cases alpha with
        | inl i => cases beta with
          | inl j =>
              exact mixMain_integral_coarseBlockMatrix_upperLeft_eq hnu hPrefix hJ2 hJ3 hJ4 L nn
                (hscale z hz) i j
          | inr j =>
              exact mixMain_integral_coarseBlockMatrix_upperRight_eq hnu hPrefix hJ2 hJ3 hJ4 L nn
                (hscale z hz) i j
        | inr i => cases beta with
          | inl j =>
              exact mixMain_integral_coarseBlockMatrix_lowerLeft_eq hnu hPrefix hJ2 hJ3 hJ4 L nn
                (hscale z hz) i j
          | inr j =>
              exact mixMain_integral_coarseBlockMatrix_lowerRight_eq hnu hPrefix hJ2 hJ3 hJ4 L nn
                (hscale z hz) i j
      have hInt : Integrable (fun omega : ShellSeq d => blockMatEntry
          (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta)
          P.toMeasure := by
        cases alpha with
        | inl i => cases beta with
          | inl j => exact integrable_coarseBlockMatrix_upperLeft_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
          | inr j => exact integrable_coarseBlockMatrix_upperRight_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
        | inr i => cases beta with
          | inl j => exact integrable_coarseBlockMatrix_lowerLeft_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
          | inr j => exact integrable_coarseBlockMatrix_lowerRight_apply hnu L z hPrefix hJ2 hJ3 hJ4 i j
      rw [integral_sub hInt (integrable_const _), h1, integral_const]
      simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul, sub_self])
    (fun z hz => mixGap_isBigO_gammaOne_entryDeviation hnu hPrefix hJ2 hJ3 hJ4 L nn z alpha beta)
    (mixGap_iIndepFun_entryDeviation hnu hJ1 hJ2 le_rfl nn alpha beta Finset.univ
      (blockSublattice nn L D) hnbhd hsubn hsep)
    hnl hlk hDcard hJcard

end

end SuperdiffusionCLT.Section4.Mixing
