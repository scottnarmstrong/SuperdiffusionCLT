/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.FiniteToInfinite
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayC
public import SuperdiffusionCLT.Section3.HighContrast.BEllAssembly
public import SuperdiffusionCLT.Probability.ConditionalGammaTailShell
public import Mathlib.Order.CompletePartialOrder

/-!
# Averaging over the old field exactly (`e.principal.conditional`)

`bfA_{m-h}(z+cu_n)` is `F_old`-measurable (`F_old = σ(j_r : r ≤ m-h)`), while `D_z` and `P̂_z` are
`F_new`-measurable (`F_new = σ(j_r : m-h < r ≤ m)`); by `a.j.indy` (`ShellLawJ2`) the two are
independent, so each coordinate term `w_{αβ} A_{αβ}` of the quadratic form has expectation
`E[w_{αβ}] E[A_{αβ}]`, and `E[A_{αβ}] = bfAhom_{m-h}(z+cu_n)_{αβ}` by the definition of the annealed
matrix. The weight `w_{αβ} = (1 + D_z) P̂_α P̂_β`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient shellSigma_mono
  indep_shellSigma_of_shellLawJ2)

variable {d : ℕ}

/-- The old shells `r ≤ l` and the fresh shells `l < r ≤ m` are disjoint. -/
theorem disjoint_Ioc_lowerShells (l m : ℕ) :
    Disjoint (Set.Ioc l m) (localizationLowerShells l) := by
  rw [Set.disjoint_left]
  intro r hr hr'
  have hle : r ≤ l := hr'
  exact absurd hle (not_le.mpr (Set.mem_Ioc.mp hr).1)

/-- Every entry of the doubled cutoff-`l` coarse block matrix is measurable for the old-shell
σ-algebra `F_old`. -/
theorem measurable_coarseEntry_oldShells {nu : ℝ} (hnu : 0 < nu) (l : ℕ) (R : TriadicCube d)
    (α β : BlockCoord d) :
    Measurable[shellSigma (d := d) (localizationLowerShells l)]
      (fun ω : ShellSeq d => toFullBlockMat (localizationCoarseAt nu l R ω) α β) := by
  let : MeasurableSpace (ShellSeq d) := shellSigma (d := d) (localizationLowerShells l)
  have hA : Measurable (fun ω : ShellSeq d => coefficientCutoff nu ω l) :=
    measurable_SS_coefficientCutoff_full (S := localizationLowerShells l)
      (fun n hn => by
        simp only [localizationLowerShells, Set.mem_ofPred_eq]
        exact hn) nu
  have hE := fun ω : ShellSeq d => aeLocallyUniformlyEllipticField_coefficientCutoff hnu ω l
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simp only [toFullBlockMat]
          exact measurable_coarseBlockMatrix_upperLeft_apply (A := fun ω : ShellSeq d => coefficientCutoff nu ω l) hA hE R i j
      | inr j =>
          simp only [toFullBlockMat]
          exact measurable_coarseBlockMatrix_upperRight_apply (A := fun ω : ShellSeq d => coefficientCutoff nu ω l) hA hE R i j
  | inr i =>
      cases β with
      | inl j =>
          simp only [toFullBlockMat]
          exact measurable_coarseBlockMatrix_lowerLeft_apply (A := fun ω : ShellSeq d => coefficientCutoff nu ω l) hA hE R i j
      | inr j =>
          simp only [toFullBlockMat]
          exact measurable_coarseBlockMatrix_lowerRight_apply (A := fun ω : ShellSeq d => coefficientCutoff nu ω l) hA hE R i j

/-- Independence of an `F_new`-measurable and an `F_old`-measurable real function (`a.j.indy`). -/
theorem indepFun_newShells_oldShells {P : ProbabilityMeasure (ShellSeq d)} (hJ2 : ShellLawJ2 d P)
    (m h : ℕ) {f g : ShellSeq d → ℝ}
    (hf : Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] f)
    (hg : Measurable[shellSigma (d := d) (localizationLowerShells (m - h))] g) :
    ProbabilityTheory.IndepFun f g P.toMeasure :=
  ProbabilityTheory.indep_of_indep_of_le_right
    (ProbabilityTheory.indep_of_indep_of_le_left
      (indep_shellSigma_of_shellLawJ2 (disjoint_Ioc_lowerShells (m - h) m) hJ2) hf.comap_le)
    hg.comap_le

/-- **`e.principal.conditional`**. Let `D` and the coordinates of `P̂` be
measurable with respect to the fresh shells `σ(j_r : m-h < r ≤ m)` and let the weights
`(1 + D) P̂_α P̂_β` be integrable. Then
`E[(1+D) P̂·bfA_{m-h}(R) P̂] = E[(1+D) P̂·bfAhom_{m-h}(R) P̂]`, `bfAhom_{m-h}(R) = E[bfA_{m-h}(R)]`.
The law hypotheses are the shell prefix, J2 (the independence `a.j.indy`), J3 and J4 (integrability
of the entries of `bfA_{m-h}(R)`). -/
theorem principal_conditional [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m h : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (R : TriadicCube d)
    {D : ShellSeq d → ℝ} {Phat : ShellSeq d → BlockVec d}
    (hD : Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] D)
    (hPhat : ∀ α : BlockCoord d,
      Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] (fun ω => toFullBlockVec (Phat ω) α))
    (hint : ∀ α β : BlockCoord d, Integrable
      (fun ω => (1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β))
      P.toMeasure) :
    ∫ ω, (1 + D ω) * blockVecDot (Phat ω)
        (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Phat ω)) ∂P.toMeasure =
      ∫ ω, (1 + D ω) * blockVecDot (Phat ω)
        (blockMatVecMul (annealedBlockMatrix nu (m - h) P (cubeSet R)) (Phat ω)) ∂P.toMeasure := by
  set w : BlockCoord d → BlockCoord d → ShellSeq d → ℝ := fun α β ω =>
    (1 + D ω) * (toFullBlockVec (Phat ω) α * toFullBlockVec (Phat ω) β) with hw
  set E : BlockCoord d → BlockCoord d → ShellSeq d → ℝ := fun α β ω =>
    blockMatEntry (localizationCoarseAt nu (m - h) R ω) α β with hE
  have hEint : ∀ α β, Integrable (E α β) P.toMeasure := fun α β =>
    integrable_blockMatEntry_coarseBlockMatrix hnu (m - h) R hPrefix hJ2 hJ3 hJ4 α β
  have hEmeas : ∀ α β, Measurable[shellSigma (d := d) (localizationLowerShells (m - h))]
      (E α β) := by
    intro α β
    have := measurable_coarseEntry_oldShells hnu (m - h) R α β
    cases α <;> cases β <;> exact this
  have hwmeas : ∀ α β, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] (w α β) := by
    intro α β
    exact (measurable_const.add hD).mul ((hPhat α).mul (hPhat β))
  have hamb : ∀ α β, AEStronglyMeasurable (w α β) P.toMeasure := fun α β =>
    ((hwmeas α β).mono (shellSigma_le_ambient _) le_rfl).aestronglyMeasurable
  have hEamb : ∀ α β, AEStronglyMeasurable (E α β) P.toMeasure := fun α β =>
    (hEint α β).aestronglyMeasurable
  have hindep : ∀ α β, ProbabilityTheory.IndepFun (w α β) (E α β) P.toMeasure := fun α β =>
    indepFun_newShells_oldShells hJ2 m h (hwmeas α β) (hEmeas α β)
  have hmean : ∀ α β, blockMatEntry (annealedBlockMatrix nu (m - h) P (cubeSet R)) α β =
      ∫ ω, E α β ω ∂P.toMeasure := by
    intro α β
    cases α <;> cases β <;> rfl
  have hLeft : ∀ ω, (1 + D ω) * blockVecDot (Phat ω)
      (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Phat ω)) =
        ∑ α : BlockCoord d, ∑ β : BlockCoord d, w α β ω * E α β ω := by
    intro ω
    rw [SuperdiffusionCLT.Section3.HighContrast.blockVecDot_blockMatVecMul_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hw, hE]
    ring
  have hRight : ∀ ω, (1 + D ω) * blockVecDot (Phat ω)
      (blockMatVecMul (annealedBlockMatrix nu (m - h) P (cubeSet R)) (Phat ω)) =
        ∑ α : BlockCoord d, ∑ β : BlockCoord d, w α β ω *
          blockMatEntry (annealedBlockMatrix nu (m - h) P (cubeSet R)) α β := by
    intro ω
    rw [SuperdiffusionCLT.Section3.HighContrast.blockVecDot_blockMatVecMul_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hw]
    ring
  simp only [hLeft, hRight]
  have hI : ∀ α β, Integrable (fun ω => w α β ω * E α β ω) P.toMeasure := fun α β =>
    (hindep α β).integrable_mul (hint α β) (hEint α β)
  have hJ : ∀ α β, Integrable (fun ω => w α β ω *
      blockMatEntry (annealedBlockMatrix nu (m - h) P (cubeSet R)) α β) P.toMeasure :=
    fun α β => (hint α β).mul_const _
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ fun β _ => hI α β),
    integral_finsetSum _ (fun α _ => integrable_finsetSum _ fun β _ => hJ α β)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finsetSum _ (fun β _ => hI α β), integral_finsetSum _ (fun β _ => hJ α β)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [(hindep α β).integral_fun_mul_eq_mul_integral (hamb α β) (hEamb α β), integral_mul_const,
    hmean α β]

/-! ## Satisfiability -/

/-- The hypotheses of `principal_conditional` are met by the Dirac law at the zero shell sequence
(prefix, J2, J3, J4), `d = 2`, `ν = 1`, `m = 2`, `h = 1`, `D = 0` and a constant block vector. -/
example (X0 : BlockVec 2) :
    ∫ ω, (1 + (0 : ℝ)) * blockVecDot X0
        (blockMatVecMul (localizationCoarseAt (1 : ℝ) (2 - 1) (originCube 2 (0 : ℤ)) ω) X0)
        ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2).toMeasure =
      ∫ _ω, (1 + (0 : ℝ)) * blockVecDot X0
        (blockMatVecMul (annealedBlockMatrix (1 : ℝ) (2 - 1)
          (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2)
          (cubeSet (originCube 2 (0 : ℤ)))) X0)
        ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2).toMeasure := by
  have := principal_conditional (d := 2) (nu := 1) one_pos 2 1
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw le_rfl)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw (originCube 2 (0 : ℤ))
    (D := fun _ => 0) (Phat := fun _ => X0) measurable_const (fun _ => measurable_const)
    (fun _ _ => integrable_const _)
  exact this

end SuperdiffusionCLT.Section5
