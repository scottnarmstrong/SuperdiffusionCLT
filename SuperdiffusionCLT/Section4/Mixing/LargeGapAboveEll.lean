/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationEntrySum

/-!
# Colouring at a general reference scale `ell`, for the `n > L` route

`p.mixing.P.three.prime#large-gap-case`'s `n > L` regime needs the
colour-partition concentration built at reference scale `ell := nn` instead
of `ell := L`, since `L` is too fine a colouring scale once the lattice
itself sits at scale `nn > L`. This is the generalization of
`Section4.Mixing.mixGap_entryDeviation_concentration`
(`LargeGapConcentrationEntrySum.lean`) to an arbitrary colouring scale
`ell` with `nn ≤ ell`, `L ≤ ell`, `ell ≤ kk`, stated under this file's own
mixGapAbove_ prefix. -/

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

/-- **Colouring at a general scale `ell ≥ max nn L`.** -/
theorem mixGapAbove_entryDeviation_concentration_ell [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {nn L ell kk : ℕ} (hnl : nn ≤ ell) (hLl : L ≤ ell) (hlk : ell ≤ kk)
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
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2)) := by
  classical
  set D : Finset (TriadicCube d) := descendantsAtDepth z' (kk - nn) with hD
  have hscale : ∀ z ∈ D, z.scale = (nn : ℤ) := by
    intro z hz
    have h := scale_eq_sub_of_mem_descendantsAtDepth (hD ▸ hz)
    rw [hz'] at h
    rw [h, Nat.cast_sub (le_trans hnl hlk)]
    ring
  set nbhd : TriadicCube d → Set (Vec d) := fun z =>
    if z.scale = (nn : ℤ) then cubeSet (coarseAncestor nn ell z) else Set.univ
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
      nbhd z = cubeSet (coarseAncestor nn ell z) := by
    intro z h
    rw [hnbhddef]
    simp only [h, ↓reduceIte]
  have hsep : ∀ c ∈ (Finset.univ :
        Finset ((Fin d → Fin (3 ^ (ell - nn))) × ShellField.ShellCubeColor d)),
      ∀ z ∈ blockSublattice nn ell D c, ∀ z2 ∈ blockSublattice nn ell D c, z ≠ z2 →
        ShellField.AreShellSeparated ell (nbhd z) (nbhd z2) := by
    intro c _ z hz z2 hz2 hne
    have hzs : z.scale = (nn : ℤ) := hscale z (blockSublattice_subset nn ell D c hz)
    have hz2s : z2.scale = (nn : ℤ) := hscale z2 (blockSublattice_subset nn ell D c hz2)
    have hcls : blockClassIndex nn ell z = blockClassIndex nn ell z2 :=
      (blockClassIndex_of_mem_blockSublattice hz).trans
        (blockClassIndex_of_mem_blockSublattice hz2).symm
    rw [hnbhd_eq z hzs, hnbhd_eq z2 hz2s]
    refine areShellSeparated_of_subset_cubeSet (kk := ell) le_rfl
      (coarseAncestor_scale nn ell z) (coarseAncestor_scale nn ell z2)
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
        Finset ((Fin d → Fin (3 ^ (ell - nn))) ×
          ShellField.ShellCubeColor d)).card : ℕ) : ℝ) ≤
      ((ShellField.shellColorPeriod d : ℕ) : ℝ) ^ d *
        (3 : ℝ) ^ ((d : ℝ) * ((ell - nn : ℕ) : ℝ)) := by
    rw [card_univ_blockClass,
      show ((d:ℝ) * ((ell-nn:ℕ):ℝ)) = (((d*(ell-nn) : ℕ)):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    push_cast
    rw [show ((3:ℝ)^(ell-nn))^d = ((3:ℝ)^d)^(ell-nn) by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    exact le_of_eq (by ring)
  exact mixGap_blockConcentrationGamma1 P D Finset.univ (blockSublattice nn ell D)
    (fun omega z => blockMatEntry
      (coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField) alpha beta -
      blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) alpha beta)
    hKpos hCJ (hD ▸ descendantsAtDepth_nonempty z' (kk - nn))
    (biUnion_blockSublattice nn ell D)
    (fun c _ c' _ hcc => disjoint_blockSublattice nn ell D hcc)
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
    (mixGap_iIndepFun_entryDeviation hnu hJ1 hJ2 hLl nn alpha beta Finset.univ
      (blockSublattice nn ell D) hnbhd hsubn hsep)
    hnl hlk hDcard hJcard

end

end SuperdiffusionCLT.Section4.Mixing
