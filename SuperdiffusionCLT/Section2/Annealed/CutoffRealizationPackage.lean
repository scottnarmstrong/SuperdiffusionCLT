/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import SuperdiffusionCLT.Section2.Cutoff.CoefficientCutoffAPI
public import Homogenization.CoarseGraining.MagicIdentities.StarredSubadditivity
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.DeterministicCoarseData
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Existence
public import Homogenization.Geometry.TriadicPartition

/-!
# Realization of the CoarseGraining subadditivity hypotheses for the cutoff field

The CoarseGraining subadditivity lemma
`Homogenization.sigmaStarInvCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse`
consumes, for a raw coefficient field `a`, a block of Chapter 2 coarse-data
hypotheses on the origin cube and on each depth-`j` descendant: the ellipticity
of the field, the `IsSigmaStarCoarse`/`IsKappaCoarse`/`IsSigmaCoarse`
characterizations of its coarse matrices, invertibility of `s_*(Q; a)`, and the
deterministic coarse block matrix data on every descendant.

This module realizes that hypothesis block for the infrared cutoff
`a_L = nu Id + k_L` of the marginal coefficient field.  The pieces are:

* `exists_isEllipticFieldOn_coefficientCutoff_openCubeSet`: the cutoff field is
  quantitatively elliptic on every triadic open cube, from the symmetric-part
  identity `symmPart(a_L) = nu Id` and the compactness entry bound.
* `cutoffOriginCubeDeterministicData`: the deterministic Chapter 2 coarse data
  of the cutoff field is available on the origin cube `cu_n` and on every
  descendant, packaged by the origin-cube elliptic recovery existence of
  `CoarseGraining`.
* `cutoffSubadditivityHypotheses_originCube`: the exact hypothesis bundle of the
  CoarseGraining subadditivity lemma.
* `sigmaStarInvCoarse_subadditive_cubeSet_originCube_coefficientCutoff`: the
  subadditivity conclusion itself for the cutoff field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining

noncomputable section

variable {d : ℕ}

/-! ## Public Orlicz hoists -/

/-- A deterministic constant has every `Γ_σ` amplitude that dominates it. -/
theorem isBigO_gammaSigma_const_apply {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {c sigma : ℝ} (hc : 0 ≤ c) :
    IsBigO mu (gammaSigma sigma) (fun _ : Omega => c) c := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have hempty : absTailEvent (fun _ : Omega => c) (c * t) = (∅ : Set Omega) := by
    ext omega
    simp only [absTailEvent, upperTailEvent, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_lt]
    calc |c| ≤ c := (abs_of_nonneg hc).le
      _ = c * 1 := (mul_one c).symm
      _ ≤ c * t := mul_le_mul_of_nonneg_left ht hc
  rw [hempty, measureReal_empty]
  exact (Real.exp_pos _).le

/-- Subtracting a bounded quantity from a variable with a `Γ_σ` envelope
enlarges the amplitude by that bound. -/
theorem isBigO_gammaSigma_of_abs_le_add_const {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsFiniteMeasure mu]
    {X Y : Omega → ℝ} {A c sigma : ℝ} (hc : 0 ≤ c)
    (hle : ∀ omega, |Y omega| ≤ |X omega| + c)
    (hX : IsBigO mu (gammaSigma sigma) X A) :
    IsBigO mu (gammaSigma sigma) Y (A + c) := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  refine (measureReal_mono ?_).trans ((isBigO_gammaSigma_iff.1 hX) ht)
  intro omega homega
  have hY : (A + c) * t < |Y omega| := homega
  have hct : c ≤ c * t := le_mul_of_one_le_right hc ht
  have hle' := hle omega
  show A * t < |X omega|
  have hexp : (A + c) * t = A * t + c * t := by ring
  linarith only [hY, hct, hle', hexp]

/-! ## Ellipticity of the cutoff field on a triadic open cube -/

/-- The cutoff coefficient field `a_L = nu Id + k_L` is quantitatively elliptic
on every triadic open cube: the lower constant is the molecular diffusivity
`nu` (the symmetric part of `a_L` is the constant matrix `nu Id`), and the
upper one is the compactness entry bound converted by
`isEllipticMatrix_of_symmPart_eq_smul_one`. -/
theorem exists_isEllipticFieldOn_coefficientCutoff_openCubeSet {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (Q : TriadicCube d) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (openCubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField := by
  obtain ⟨C, hC⟩ := exists_entryBound_coefficientCutoff nu omega L Q
  refine ⟨nu, ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, ⟨?_, fun x hx => ?_⟩⟩
  · exact measurable_matrix_of_entries fun i j =>
      Measurable.ite (isOpen_openCubeSet Q).measurableSet
        ((coefficientCutoff nu omega L).entry_measurable i j) measurable_const
  · exact isEllipticMatrix_of_symmPart_eq_smul_one hnu
      (symmPart_coefficientCutoff nu omega L x)
      (hC x (openCubeSet_subset_cubeSet Q hx))

/-! ## Deterministic coarse data on the origin cube and its descendants -/

/-- The cutoff field on the origin cube `cu_n` is quantitatively elliptic, and
its deterministic Chapter 2 coarse data — the deterministic coarse block
matrix, the coarse matrix characterizations and invertibility of `s_*(R; a_L)`
— is available on `cu_n` itself and on every descendant at every depth. -/
theorem cutoffOriginCubeDeterministicData [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (n : ℤ) :
    ∃ lam Lam : ℝ,
      IsEllipticFieldOn lam Lam (openCubeSet (originCube d n))
        (coefficientCutoff nu omega L).toCoeffField ∧
      OpenCubeDescendantDeterministicCoarseData (originCube d n)
        (coefficientCutoff nu omega L).toCoeffField := by
  obtain ⟨lam, Lam, hEll⟩ :=
    exists_isEllipticFieldOn_coefficientCutoff_openCubeSet hnu omega L (originCube d n)
  refine ⟨lam, Lam, hEll, ?_⟩
  exact openCubeDescendantDeterministicCoarseData_of_recoveryFamily
    (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
      (originCube d n) (coefficientCutoff nu omega L).toCoeffField hEll
      openCubeOriginEllipticRecoveryExistence)

/-! ## The hypothesis bundle of the CoarseGraining subadditivity lemma -/

/-- The exact hypothesis bundle of the CoarseGraining subadditivity lemma
`Homogenization.sigmaStarInvCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse`
for the cutoff field `a_L = nu Id + k_L` on the origin cube `cu_n`: the
ellipticity of `a_L` on the open origin cube, the coarse-matrix
characterizations at the origin cube, invertibility of `s_*(cu_n; a_L)`, and
the deterministic coarse block matrix data on every depth-`j` descendant. -/
theorem cutoffSubadditivityHypotheses_originCube [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (n : ℤ) (j : ℕ) :
    ∃ lam Lam : ℝ, ∃ sigmaQ sigmaStarQ kappaQ : Mat d,
      IsEllipticFieldOn lam Lam (openCubeSet (originCube d n))
        (coefficientCutoff nu omega L).toCoeffField ∧
      IsSigmaStarCoarse (openCubeSet (originCube d n))
        (coefficientCutoff nu omega L).toCoeffField sigmaStarQ ∧
      IsKappaCoarse (openCubeSet (originCube d n))
        (coefficientCutoff nu omega L).toCoeffField sigmaStarQ kappaQ ∧
      IsSigmaCoarse (openCubeSet (originCube d n))
        (coefficientCutoff nu omega L).toCoeffField sigmaQ sigmaStarQ kappaQ ∧
      IsUnit sigmaStarQ.det ∧
      (∀ R ∈ descendantsAtDepth (originCube d n) j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R)
            (coefficientCutoff nu omega L).toCoeffField
            (deterministicCoarseBlockMatrix (openCubeSet R)
              (coefficientCutoff nu omega L).toCoeffField) ∧
          IsSigmaStarCoarse (openCubeSet R)
            (coefficientCutoff nu omega L).toCoeffField sigmaStarR ∧
          IsKappaCoarse (openCubeSet R)
            (coefficientCutoff nu omega L).toCoeffField sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R)
            (coefficientCutoff nu omega L).toCoeffField sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det) := by
  obtain ⟨lam, Lam, hEll, hData⟩ := cutoffOriginCubeDeterministicData hnu omega L n
  have hSelf : OpenCubeDeterministicCoarseData (originCube d n)
      (coefficientCutoff nu omega L).toCoeffField := hData.self
  have hconv : descendantsAtDepth (originCube d n) j
      = descendantsAtScale (originCube d n) ((n : ℤ) - (j : ℤ)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d n)
      (show (n : ℤ) - (j : ℤ) ≤ (n : ℤ) by omega)]
    have hscale : (originCube d n).scale = (n : ℤ) := rfl
    simp only [hscale]
    congr 1
    omega
  have hscale : (originCube d n).scale = (n : ℤ) := rfl
  rcases hSelf with ⟨sigmaQ, sigmaStarQ, kappaQ, hA, hSQ, hKQ, hSigmaQ, hdetQ⟩
  refine ⟨lam, Lam, sigmaQ, sigmaStarQ, kappaQ, hEll, hSQ, hKQ, hSigmaQ, hdetQ,
    fun R hR => ?_⟩
  exact hData ((n : ℤ) - (j : ℤ)) (by rw [hscale]; omega) R (by rw [← hconv]; exact hR)

/-! ## The subadditivity conclusion for the cutoff field -/

/-- The CoarseGraining subadditivity lemma realized for the cutoff field: the inverse
starred coarse matrix of `a_L` on `cu_n` is Loewner-below the depth-`j`
average of its values on the descendant cubes. -/
theorem sigmaStarInvCoarse_subadditive_cubeSet_originCube_coefficientCutoff
    [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (n : ℤ) (j : ℕ) :
    MatLoewnerLE (sigmaStarInvCoarse (cubeSet (originCube d n))
        (coefficientCutoff nu omega L).toCoeffField)
      (descendantsAverageMat (originCube d n) j
        (fun R => sigmaStarInvCoarse (cubeSet R)
          (coefficientCutoff nu omega L).toCoeffField)) := by
  obtain ⟨lam, Lam, sigmaQ, sigmaStarQ, kappaQ, hEll, hSQ, hKQ, hSigmaQ, hdetQ,
    hDesc⟩ := cutoffSubadditivityHypotheses_originCube hnu omega L n j
  exact sigmaStarInvCoarse_subadditive_cubeSet_originCube_descendantsAtDepth_in_loewner_order_of_isSigmaCoarse
    j n (coefficientCutoff nu omega L).toCoeffField hEll hSQ hKQ hSigmaQ hdetQ hDesc

end

end SuperdiffusionCLT.Section2.Annealed