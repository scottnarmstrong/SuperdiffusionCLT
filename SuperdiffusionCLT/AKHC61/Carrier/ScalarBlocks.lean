/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.AKHC61.Carrier.Integrability
public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff

/-!
# Package A2: J3-free monotonicity and positivity of the annealed scalars

This file proves the package A2 targets of the AK.HC Theorem 6.1 port
(package A2)
that concern the two scalar sequences `sigmaBarSeq`, `sigmaBarStarInvSeq` and
the cutoff ratio `thetaCutoff`: antitonicity, positivity, and
`thetaCutoff ... n ≥ 1`.

`SuperdiffusionCLT.Section2.Annealed.InfiniteVolume` already proves all of
these facts, but every one of its proofs runs through
`ShellLawJ3`-dependent integrability
(`SuperdiffusionCLT.Section2.Annealed.Integrability.integrable_blockMatEntry_coarseBlockMatrix`).
The main statement `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`
(its (P2') clause is copied verbatim below) carries no `ShellLawJ3` binder. This file re-derives
the same facts using only `0 < nu`, the (P2') clause, and — where the shell
law's stationarity or dihedral symmetry is genuinely needed — `ShellLawPrefix`,
`ShellLawJ2`, `ShellLawJ4`, mining the same proof shapes as `InfiniteVolume.lean`,
but with every `ShellLawJ3`-dependent integrability step replaced by package A1's
`akhc_integrable_blockMatEntry_of_P2`
(`SuperdiffusionCLT.AKHC61.Carrier.Integrability`).

## Hypothesis bookkeeping

Tracing exactly which shell-law binder each fact needs (beyond `0 < nu` and
the (P2') clause) turns up a genuine hypothesis reduction relative to the
`ShellLawJ3`-based originals, because A1's integrability needs no shell-law
binder at all:

* the lower-block monotonicity/antitonicity of `sigmaBarStarInvSeq` needs only
  `ShellLawPrefix`, `ShellLawJ2` (stationarity) — **not** `ShellLawJ4`;
* positivity of both scalars and `1 ≤ thetaCutoff ... n` need only
  `ShellLawJ4` (dihedral symmetry, to identify the diagonal blocks with
  scalars) — **not** `ShellLawPrefix`/`ShellLawJ2`;
* the upper-block monotonicity of `sigmaBarSeq` and the antitonicity of
  `thetaCutoff` need all three (`ShellLawPrefix`, `ShellLawJ2`, `ShellLawJ4`).

## Main results

* `akhc_antitone_sigmaBarStarInvSeq_of_P2`, `akhc_antitone_sigmaBarSeq_of_P2`:
  antitonicity of the two scalar sequences.
* `akhc_sigmaBarStarInvSeq_pos_of_P2`, `akhc_sigmaBarSeq_pos_of_P2`:
  positivity.
* `akhc_one_le_thetaCutoff_of_P2`, `akhc_antitone_thetaCutoff_of_P2`: node 60,
  `Θ_n ≥ 1` and `Θ` antitone.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Carrier

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Part 1: `cutoffLaw`-level integrability, J3-free, from package A1 -/

section P2Integrability

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **J3-free replacement for `integrable_blockMatEntry_cutoffLaw`.** Entries of
`bfA_L(cu_Q)` are integrable for `cutoffLaw`, using package A1's
`akhc_integrable_blockMatEntry_of_P2` (`0 < nu` and the (P2') clause alone) in
place of the `ShellLawJ3`-dependent original. -/
theorem akhc_integrable_blockMatEntry_cutoffLaw_of_P2
    (Q : TriadicCube d) (alpha beta : BlockCoord d) :
    Integrable (fun a : RegCoeffField d ↦
      blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta)
      (cutoffLaw (d := d) nu L P) := by
  rw [cutoffLaw]
  refine (integrable_map_measure
    ((aemeasurable_blockMatEntry_cutoffLaw hnu L P Q alpha
      beta).aestronglyMeasurable)
    (measurable_coefficientCutoff nu L).aemeasurable).2 ?_
  exact akhc_integrable_blockMatEntry_of_P2 d hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 Q alpha beta

/-- **J3-free replacement for `integrable_coarseFullBlockMatrixAtCube_cutoffLaw`.** -/
theorem akhc_integrable_coarseFullBlockMatrixAtCube_cutoffLaw_of_P2
    (Q : TriadicCube d) :
    Integrable (Book.Ch04.coarseFullBlockMatrixAtCube Q)
      (cutoffLaw (d := d) nu L P) := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro alpha
  refine MeasureTheory.Integrable.of_eval ?_
  intro beta
  have h := akhc_integrable_blockMatEntry_cutoffLaw_of_P2 hnu gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 Q alpha beta
  have hfun :
      (fun a : RegCoeffField d ↦
        Book.Ch04.coarseFullBlockMatrixAtCube Q a alpha beta) =
        fun a : RegCoeffField d ↦
          blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta := by
    funext a
    cases alpha <;> cases beta <;> rfl
  rw [hfun]
  exact h

/-- **J3-free replacement for `integrable_coarseBlockMatrix_lowerRight`.** The
lower-right block of `bfA_L(cu_Q)`, as a `Mat d`-valued observable on the
shell-sequence carrier, is `P`-integrable. -/
theorem akhc_integrable_coarseBlockMatrix_lowerRight_of_P2 (Q : TriadicCube d) :
    Integrable (fun omega : ShellSeq d ↦
      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toFun).lowerRight)
      P.toMeasure := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro i
  refine MeasureTheory.Integrable.of_eval ?_
  intro j
  exact akhc_integrable_blockMatEntry_of_P2 d hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 Q (Sum.inr i)
    (Sum.inr j)

end P2Integrability

/-! ## Part 2: monotonicity of the lower block `sigmaBarStarInvSeq`

Needs only stationarity (`ShellLawPrefix`, `ShellLawJ2`), not `ShellLawJ4`: the
lower-right block of a block-Löwner comparison is a matrix comparison
unconditionally (`Homogenization.Book.Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE`). -/

section P2Monotone

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **J3-free replacement for `blockMatLoewnerLE_annealedBlockMatrix_originCube`.** -/
theorem akhc_blockMatLoewnerLE_annealedBlockMatrix_originCube_of_P2
    {j k : ℤ} (hj : 0 ≤ j) (hjk : j ≤ k) :
    BlockMatLoewnerLE (annealedBlockMatrix nu L P (cubeSet (originCube d k)))
      (annealedBlockMatrix nu L P (cubeSet (originCube d j))) := by
  have hmono :=
    (restrictionLawCarrier_cutoffLaw hnu L
        P).blockMatLoewnerLE_annealedBlockMatrixAtScale
      (restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu L) hj hjk
      (fun alpha beta ↦ akhc_integrable_blockMatEntry_cutoffLaw_of_P2 hnu gamma H D m2
        PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
        hP2 (originCube d k) alpha beta)
      (fun R _ alpha beta ↦ akhc_integrable_blockMatEntry_cutoffLaw_of_P2 hnu gamma H D m2
        PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
        hP2 R alpha beta)
  rw [annealedBlockMatrix_eq_ch04 hnu L P (originCube d k),
    annealedBlockMatrix_eq_ch04 hnu L P (originCube d j)]
  simpa only [Book.Ch04.annealedBlockMatrixAtScale] using hmono

/-- **J3-free replacement for `matLoewnerLE_sigmaBarStarInv_originCube`.** -/
theorem akhc_matLoewnerLE_sigmaBarStarInv_originCube_of_P2
    {j k : ℤ} (hj : 0 ≤ j) (hjk : j ≤ k) :
    MatLoewnerLE (sigmaBarStarInv nu L P (cubeSet (originCube d k)))
      (sigmaBarStarInv nu L P (cubeSet (originCube d j))) :=
  Book.Ch04.matLoewnerLE_lowerRight_of_blockMatLoewnerLE
    (akhc_blockMatLoewnerLE_annealedBlockMatrix_originCube_of_P2 hnu hPrefix hJ2 gamma H
      D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2 hj hjk)

/-- **J3-free replacement for `sigmaBarStarInvScalar_le_of_le`.** -/
theorem akhc_sigmaBarStarInvScalar_le_of_le_of_P2
    {j k : ℤ} (hj : 0 ≤ j) (hjk : j ≤ k) :
    sigmaBarStarInvScalar nu L P (cubeSet (originCube d k)) ≤
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) :=
  diag_le_of_matLoewnerLE
    (akhc_matLoewnerLE_sigmaBarStarInv_originCube_of_P2 hnu hPrefix hJ2 gamma H D m2
      PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
      hP2 hj hjk) 0

/-- **Node 60, first half (lower block): `sigmaBarStarInvSeq` is antitone,
J3-free.** Needs only `hnu`, `ShellLawPrefix`, `ShellLawJ2`, and the (P2')
clause. -/
theorem akhc_antitone_sigmaBarStarInvSeq_of_P2 :
    Antitone (sigmaBarStarInvSeq nu L P) := by
  intro a b hab
  exact akhc_sigmaBarStarInvScalar_le_of_le_of_P2 hnu hPrefix hJ2 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    (Int.natCast_nonneg a) (Int.ofNat_le.2 hab)

end P2Monotone

/-! ## Part 3: monotonicity of the upper block `sigmaBarSeq`

Needs `ShellLawJ4` in addition, to identify the upper-left block of
`bfAhom_L(cu_n)` with `sigmaBar` (equivalently, to make `kappaBar` vanish). -/

section P2MonotoneJ4

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
  (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
  hGrowth hP2

/-- **J3-free replacement for `matLoewnerLE_sigmaBar_originCube`.** -/
theorem akhc_matLoewnerLE_sigmaBar_originCube_of_P2
    {j k : ℤ} (hj : 0 ≤ j) (hjk : j ≤ k) :
    MatLoewnerLE (sigmaBar nu L P (cubeSet (originCube d k)))
      (sigmaBar nu L P (cubeSet (originCube d j))) := by
  have h := Book.Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE
    (akhc_blockMatLoewnerLE_annealedBlockMatrix_originCube_of_P2 hnu hPrefix hJ2 gamma H
      D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2 hj hjk)
  rwa [annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu L hJ4 k,
    annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu L hJ4 j] at h

/-- **J3-free replacement for `sigmaBarScalar_le_of_le`.** -/
theorem akhc_sigmaBarScalar_le_of_le_of_P2
    {j k : ℤ} (hj : 0 ≤ j) (hjk : j ≤ k) :
    sigmaBarScalar nu L P (cubeSet (originCube d k)) ≤
      sigmaBarScalar nu L P (cubeSet (originCube d j)) :=
  diag_le_of_matLoewnerLE
    (akhc_matLoewnerLE_sigmaBar_originCube_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS
      KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hj
      hjk) 0

/-- **Node 60, second half (upper block): `sigmaBarSeq` is antitone,
J3-free.** Needs `hnu`, `ShellLawPrefix`, `ShellLawJ2`, `ShellLawJ4`, and the
(P2') clause. -/
theorem akhc_antitone_sigmaBarSeq_of_P2 :
    Antitone (sigmaBarSeq nu L P) := by
  intro a b hab
  exact akhc_sigmaBarScalar_le_of_le_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    (Int.natCast_nonneg a) (Int.ofNat_le.2 hab)

end P2MonotoneJ4

/-! ## Part 4: positivity, J3-free

Needs only `ShellLawJ4` (to reduce the diagonal blocks to scalar matrices),
not `ShellLawPrefix`/`ShellLawJ2`: no stationarity is used anywhere in this
part. -/

section P2Positivity

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **J3-free replacement for `one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar`**,
the annealed contrast inequality. -/
theorem akhc_one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar_of_P2 (j : ℤ) :
    1 ≤ sigmaBarScalar nu L P (cubeSet (originCube d j)) *
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) := by
  have hcontrast :=
    Book.Ch04.RestrictionLawCarrier.Internal.one_le_primitive_contrast_of_integrable_coarseFullBlockMatrixAtCube
      (restrictionLawCarrier_cutoffLaw hnu L P)
      (primitiveScalarizationData hnu L hJ4 j)
      (akhc_integrable_coarseFullBlockMatrixAtCube_cutoffLaw_of_P2 hnu gamma H D m2 PsiS
        KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
        (originCube d j))
  rw [show Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.contrast
        (primitiveScalarizationData hnu L hJ4 j) =
      Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.barB
          (primitiveScalarizationData hnu L hJ4 j) *
        Book.Ch04.Internal.AnnealedPrimitiveScalarizationData.barSigmaStarInv
          (primitiveScalarizationData hnu L hJ4 j) from rfl,
    barB_primitiveScalarizationData hnu L hJ4 j,
    barSigmaStarInv_primitiveScalarizationData hnu L hJ4 j] at hcontrast
  exact hcontrast

/-- **J3-free replacement for `sigmaBarStarInvScalar_pos_cutoff`.** -/
theorem akhc_sigmaBarStarInvScalar_pos_of_P2 (n : ℤ) :
    0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d n)) :=
  sigmaBarStarInvScalar_pos hnu L hJ4 n
    (akhc_integrable_coarseBlockMatrix_lowerRight_of_P2 hnu gamma H D m2 PsiS KPsiS
      pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
      (originCube d n))

/-- **J3-free replacement for `sigmaBarScalar_originCube_pos`.** -/
theorem akhc_sigmaBarScalar_originCube_pos_of_P2 (j : ℤ) :
    0 < sigmaBarScalar nu L P (cubeSet (originCube d j)) := by
  have hstar := akhc_sigmaBarStarInvScalar_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 j
  have hcontrast :=
    akhc_one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar_of_P2 hnu hJ4 gamma H D m2 PsiS
      KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 j
  by_contra hle
  push Not at hle
  have hmul := mul_le_mul_of_nonneg_right hle hstar.le
  rw [zero_mul] at hmul
  linarith only [hcontrast, hmul]

/-- Positivity of `sigmaBarStarInvSeq`, J3-free. -/
theorem akhc_sigmaBarStarInvSeq_pos_of_P2 (n : ℕ) :
    0 < sigmaBarStarInvSeq nu L P n :=
  akhc_sigmaBarStarInvScalar_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (n : ℤ)

/-- Positivity of `sigmaBarSeq`, J3-free. -/
theorem akhc_sigmaBarSeq_pos_of_P2 (n : ℕ) :
    0 < sigmaBarSeq nu L P n :=
  akhc_sigmaBarScalar_originCube_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (n : ℤ)

/-- **Node 60, `Θ_n ≥ 1`, J3-free.** Needs only `hnu`, `ShellLawJ4`, and the
(P2') clause — no `ShellLawPrefix`/`ShellLawJ2`. -/
theorem akhc_one_le_thetaCutoff_of_P2 (n : ℕ) :
    1 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n := by
  have h := akhc_one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar_of_P2 hnu hJ4 gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
    hP2 (n : ℤ)
  rw [SuperdiffusionCLT.Frozen.Section4.thetaCutoff, sigmaBarSeq, sigmaBarStarInvSeq]
  exact h

end P2Positivity

/-! ## Part 5: `thetaCutoff` is antitone, J3-free

Needs all three shell-law binders: stationarity (for the two monotonicity
facts of Parts 2-3) and `ShellLawJ4` (for the positivity used to multiply the
two antitone bounds). -/

section P2ThetaAntitone

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
  (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
  hGrowth hP2

/-- **Node 60, second half: `thetaCutoff nu L P` is antitone, J3-free.** The
product of the two antitone nonnegative scalar sequences of Parts 2-3. Needs
`hnu`, `ShellLawPrefix`, `ShellLawJ2`, `ShellLawJ4`, and the (P2') clause. -/
theorem akhc_antitone_thetaCutoff_of_P2 :
    Antitone (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P) := by
  intro a b hab
  have hA := akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hab
  have hB := akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hab
  have hBpos := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 b
  have hApos := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 a
  rw [SuperdiffusionCLT.Frozen.Section4.thetaCutoff,
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff]
  exact mul_le_mul hA hB hBpos.le hApos.le

end P2ThetaAntitone

end

end SuperdiffusionCLT.AKHC61.Carrier
