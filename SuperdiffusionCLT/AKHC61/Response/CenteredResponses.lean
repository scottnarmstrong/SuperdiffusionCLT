/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.AKHC61.Carrier.Integrability
public import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.LawCarrierFullBlock
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Package B1: the centered-response identity for the cutoff law

`AK.HC`'s Section 6 identity `l.Jminusmeans.to.Theta` / `e.Thetam.byJ.agh`
(`CoarseGraining`'s `Section54/OneStepContraction/CenteredResponses.lean:120`,
`thetaAtScale_sub_one_eq_two_centeredResponse_special`, together with
`Section52/CenteredResponses.lean:59,137`) is RETYPED here for the law of the
infrared cutoff field `cutoffLaw nu L P`. The `CoarseGraining` source is typed
on `Ch04.RestrictionStructuralLaw`, whose `unit_range` field the cutoff law
does not have (route W, `dprime.plan.md` §3). This module reproves it on the
weaker typing `(Ch04.RestrictionLawCarrier, isotropic, adjoint invariant)`
alone -- exactly `Ch04.Theorems.Scalarization.lean:412`
(`Internal.annealedScalarizationTheory_of_isotropic_adjoint`/
`annealedPrimitiveScalarizationData_of_isotropic_adjoint`, no `hStruct`) --
using the already proved local scalar reduction of
`SuperdiffusionCLT.Section2.Annealed.Symmetry` (built on that same
isotropic/adjoint route under `ShellLawJ4`, J3-free), and the (P2')-based
integrability of package A1
(`SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2`),
**not** `QuantitativeCoarseGrainedEllipticity` (P4) and **not** `ShellLawJ3`.

## Route

* Step 0 (pure algebra). For any `A B c > 0` and `e : Vec d`, with the
  geometric-mean special vectors `p := c^{-1/2} • e`, `q := c^{1/2} • e`, the
  bilinear identity
  `(½ A (q·q) − p·q + ½ B (p·p)) − ½ (A•q − p)·(q − B•p) = ½ (A B − 1) |e|²`
  holds regardless of the value of `c`; `c` is fixed to `AK.HC`/`CoarseGraining`'s
  `sigmaHat = sqrt(σ̄_m σ̄*_m)` for source fidelity (`akhc_special_algebra`).
* Step 1 (integrability bridge, no J3). Package A1's shell-carrier integrability
  is pushed forward along `cutoffLaw = Measure.map (coefficientCutoff nu · L)
  P.toMeasure` to give `Integrable (Ch04.coarseFullBlockMatrixAtCube Q)
  (cutoffLaw nu L P)`, entrywise then assembled (`akhc_integrable_*_of_P2`).
  The same integrability, via `Ch04`'s J3-free `Internal.barSigmaStarInv_pos_...`
  and `Internal.barB_pos_...` (`LawCarrierFullBlock.lean`), gives strict
  positivity of both `sigmaBarStarInvSeq` and `sigmaBarSeq` at every scale, with
  no extra hypothesis (`akhc_scalars_pos`).
* Step 2 (block reduction, `ShellLawJ4` only). `Ch04.expectedResponseJCubeSet
  (cutoffLaw nu L P) (originCube d m) p q` is rewritten through
  `Ch04.RestrictionLawCarrier.integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix`
  (law-free beyond `RestrictionLawCarrier` + integrability) into the quadratic
  form in the annealed block matrix, then the lower-left block vanishes and
  the two diagonal blocks scalarize to `sigmaBarSeq`/`sigmaBarStarInvSeq` by
  the already proved, J3-free `Symmetry.lean` lemmas under `ShellLawJ4`
  (`akhc_expectedResponseJCubeSet_originCube_eq`).
* Step 3 (assembly). Steps 0 and 2 combine into the target identity. The J*
  twin is free: `cutoffLaw` is adjoint invariant under `ShellLawJ4`
  (`isAdjointInvariantInLawR_cutoffLaw`), so the adjoint response observable
  has the *same* expectation as the primal one, and the twin identity follows by
  substitution.

## A finding against the literal task wording

The literal target quoted to this package reads
`thetaCutoff nu L P m − 1 = 2 * (expectedResponseJCubeSet (cutoffLaw …)
(originCube d m) p_e q_e − ½ p_e·q_e)`. This is **false** for `CoarseGraining`'s
actual special vectors (and indeed for any single choice of `p_e, q_e`
independent of `Θ_m`): direct computation (matching `CoarseGraining`'s own
`centeredResponseExpectationFormula_special_eq`) gives, for the special
vectors, `expectedResponseJCubeSet(p_e,q_e) = (√Θ_m − 1)|e|²` and the genuine
centering term `scalarizedResponseCenteringTerm(p_e,q_e) = (√Θ_m −
(Θ_m+1)/2)|e|²`, which equals `½|e|² = ½ p_e·q_e` only when `Θ_m = 1`. The
correct identity subtracts the real centering term `akhc_centeringTerm`
(`½ (A•q − p)·(q − B•p)`), not `½ p_e·q_e`; this file proves that corrected,
source-faithful statement, which is exactly `CoarseGraining`'s
`thetaAtScale_sub_one_eq_two_centeredResponse_special` retyped for the cutoff
law.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Response

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Step 0: pure real algebra for the geometric-mean special vectors -/

private theorem akhc_rpow_half_mul_half {c : ℝ} (hc : 0 < c) :
    c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c := by
  rw [← Real.rpow_add hc]
  norm_num

private theorem akhc_rpow_negHalf_mul_negHalf {c : ℝ} (hc : 0 < c) :
    c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c⁻¹ := by
  rw [← Real.rpow_add hc, show (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) = -(1 : ℝ) by norm_num,
    Real.rpow_neg hc.le, Real.rpow_one]

private theorem akhc_rpow_negHalf_mul_half {c : ℝ} (hc : 0 < c) :
    c ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add hc, show (-(1 / 2 : ℝ)) + (1 / 2 : ℝ) = (0 : ℝ) by norm_num,
    Real.rpow_zero]

private theorem akhc_rpow_half_mul_negHalf {c : ℝ} (hc : 0 < c) :
    c ^ (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) = 1 := by
  rw [← Real.rpow_add hc, show (1 / 2 : ℝ) + (-(1 / 2 : ℝ)) = (0 : ℝ) by norm_num,
    Real.rpow_zero]

omit [NeZero d] in
/-- The four inner-product facts for the geometric-mean special vectors
`p = c^{-1/2} • e`, `q = c^{1/2} • e`, `c > 0`. -/
private theorem akhc_specialVec_dots {c : ℝ} (hc : 0 < c) (e : Vec d) :
    vecDot (c ^ (-(1 / 2 : ℝ)) • e) (c ^ (1 / 2 : ℝ) • e) = vecNormSq e ∧
    vecDot (c ^ (1 / 2 : ℝ) • e) (c ^ (-(1 / 2 : ℝ)) • e) = vecNormSq e ∧
    vecDot (c ^ (1 / 2 : ℝ) • e) (c ^ (1 / 2 : ℝ) • e) = c * vecNormSq e ∧
    vecDot (c ^ (-(1 / 2 : ℝ)) • e) (c ^ (-(1 / 2 : ℝ)) • e) = c⁻¹ * vecNormSq e := by
  simp only [vecNormSq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, akhc_rpow_negHalf_mul_half hc, one_mul]
  · rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, akhc_rpow_half_mul_negHalf hc, one_mul]
  · rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, akhc_rpow_half_mul_half hc]
  · rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, akhc_rpow_negHalf_mul_negHalf hc]

omit [NeZero d] in
/-- The generic bilinear expansion of the centering term, for any `p q : Vec d`
and `A B : ℝ`. Pure vector algebra, no positivity needed. -/
private theorem akhc_vecDot_sub_smul_sub_smul (A B : ℝ) (p q : Vec d) :
    vecDot (A • q - p) (q - B • p) =
      A * vecDot q q - A * B * vecDot q p - vecDot p q + B * vecDot p p := by
  have h1 : A • q - p = A • q + (-1 : ℝ) • p := by rw [sub_eq_add_neg, neg_one_smul]
  have h2 : q - B • p = q + (-B) • p := by rw [sub_eq_add_neg, neg_smul]
  rw [h1, h2]
  simp only [vecDot_add_left, vecDot_add_right, vecDot_smul_left, vecDot_smul_right]
  ring

omit [NeZero d] in
/-- **Step 0 assembly.** For `A B c > 0` and `e : Vec d`, with the geometric-mean
special vectors `p = c^{-1/2}•e`, `q = c^{1/2}•e`, the response quadratic form
minus the real centering term is `½(AB−1)|e|²`, regardless of `c`. -/
private theorem akhc_special_algebra {A B c : ℝ} (hc : 0 < c) (e : Vec d) :
    ((1 / 2 : ℝ) * vecDot (c ^ (1 / 2 : ℝ) • e) (A • (c ^ (1 / 2 : ℝ) • e)) -
        vecDot (c ^ (-(1 / 2 : ℝ)) • e) (c ^ (1 / 2 : ℝ) • e) +
        (1 / 2 : ℝ) * vecDot (c ^ (-(1 / 2 : ℝ)) • e) (B • (c ^ (-(1 / 2 : ℝ)) • e))) -
      (1 / 2 : ℝ) * vecDot (A • (c ^ (1 / 2 : ℝ) • e) - c ^ (-(1 / 2 : ℝ)) • e)
        (c ^ (1 / 2 : ℝ) • e - B • (c ^ (-(1 / 2 : ℝ)) • e)) =
      (1 / 2 : ℝ) * (A * B - 1) * vecNormSq e := by
  obtain ⟨hpq, hqp, hqq, hpp⟩ := akhc_specialVec_dots (d := d) hc e
  rw [vecDot_smul_right (c ^ (1 / 2 : ℝ) • e) (c ^ (1 / 2 : ℝ) • e) A,
    vecDot_smul_right (c ^ (-(1 / 2 : ℝ)) • e) (c ^ (-(1 / 2 : ℝ)) • e) B,
    akhc_vecDot_sub_smul_sub_smul A B (c ^ (-(1 / 2 : ℝ)) • e) (c ^ (1 / 2 : ℝ) • e),
    hpq, hqp, hqq, hpp]
  ring

/-! ## The special vectors and the centering term, on the cutoff law -/

/-- `sigmaHat_m = sqrt(σ̄_m σ̄*_m)`, `CoarseGraining`'s `sigmaHatAtScale`
(`Ch05/Definitions.lean:380`) retyped for the cutoff law: `σ̄*_m` is
`(sigmaBarStarInvSeq nu L P m)⁻¹`, so `σ̄_m σ̄*_m = sigmaBarSeq /
sigmaBarStarInvSeq`. -/
noncomputable def akhc_sigmaHatScalar (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (m : ℕ) : ℝ :=
  Real.sqrt (sigmaBarSeq nu L P m / sigmaBarStarInvSeq nu L P m)

/-- `p_e = sigmaHat_m^{-1/2} • e`, `CoarseGraining`'s `specialPAtScale`. -/
noncomputable def akhc_specialP (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m : ℕ)
    (e : Vec d) : Vec d :=
  (akhc_sigmaHatScalar nu L P m) ^ (-(1 / 2 : ℝ)) • e

/-- `q_e = sigmaHat_m^{1/2} • e`, `CoarseGraining`'s `specialQAtScale`. -/
noncomputable def akhc_specialQ (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (m : ℕ)
    (e : Vec d) : Vec d :=
  (akhc_sigmaHatScalar nu L P m) ^ (1 / 2 : ℝ) • e

/-- The real centering term, `CoarseGraining`'s `scalarizedResponseCenteringTerm`
retyped on the two bare scalars `A = σ̄*⁻¹`, `B = σ̄` instead of `hStruct`. -/
noncomputable def akhc_centeringTerm (A B : ℝ) (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) * vecDot (A • q - p) (q - B • p)

/-! ## Step 1: the (P2')-based integrability bridge to the `cutoffLaw` carrier,
without `ShellLawJ3`, and the resulting positivity of the two scalars -/

section Integrability

variable {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- Entrywise integrability of `bfA_L(cu)` for the `cutoffLaw` carrier, pushed
forward from A1's shell-carrier integrability. No `ShellLawJ3`. -/
private theorem akhc_b1_integrable_blockMatEntry_cutoffLaw
    (Q : TriadicCube d) (alpha beta : BlockCoord d) :
    Integrable (fun a : RegCoeffField d ↦
      blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha beta)
      (cutoffLaw (d := d) nu L P) := by
  rw [cutoffLaw]
  refine (integrable_map_measure
    ((aemeasurable_blockMatEntry_cutoffLaw hnu L P Q alpha beta).aestronglyMeasurable)
    (measurable_coefficientCutoff nu L).aemeasurable).2 ?_
  exact akhc_integrable_blockMatEntry_of_P2 d hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 Q alpha beta

/-- The unfolded doubled coarse block matrix is Bochner integrable for the
`cutoffLaw` carrier. No `ShellLawJ3`. -/
private theorem akhc_b1_integrable_coarseFullBlockMatrixAtCube_cutoffLaw
    (Q : TriadicCube d) :
    Integrable (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q)
      (cutoffLaw (d := d) nu L P) := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro alpha
  refine MeasureTheory.Integrable.of_eval ?_
  intro beta
  have h := akhc_b1_integrable_blockMatEntry_cutoffLaw hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 Q alpha beta
  have hfun :
      (fun a : RegCoeffField d ↦ Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a alpha
          beta) =
        fun a : RegCoeffField d ↦ blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) alpha
          beta := by
    funext a
    cases alpha <;> cases beta <;> rfl
  rw [hfun]
  exact h

include hJ4

/-- **Positivity of the two annealed scalars, with no extra hypothesis.**
Package A1's integrability, pushed to `cutoffLaw`, feeds `CoarseGraining`'s
J3-free `Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube`
and `Internal.barB_pos_of_integrable_coarseFullBlockMatrixAtCube`
(`LawCarrierFullBlock.lean`), and the already proved
`barSigmaStarInv_primitiveScalarizationData` / `barB_primitiveScalarizationData`
identify their values with `sigmaBarStarInvSeq` / `sigmaBarSeq`. -/
private theorem akhc_scalars_pos (m : ℕ) :
    0 < sigmaBarStarInvSeq nu L P m ∧ 0 < sigmaBarSeq nu L P m := by
  have hBlock := akhc_b1_integrable_coarseFullBlockMatrixAtCube_cutoffLaw hnu P L gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    (originCube d (m : ℤ))
  have hApos :=
    Homogenization.Book.Ch04.RestrictionLawCarrier.Internal.barSigmaStarInv_pos_of_integrable_coarseFullBlockMatrixAtCube
      (restrictionLawCarrier_cutoffLaw hnu L P) (primitiveScalarizationData hnu L hJ4 (m : ℤ))
      hBlock
  have hBpos :=
    Homogenization.Book.Ch04.RestrictionLawCarrier.Internal.barB_pos_of_integrable_coarseFullBlockMatrixAtCube
      (restrictionLawCarrier_cutoffLaw hnu L P) (primitiveScalarizationData hnu L hJ4 (m : ℤ)) hBlock
  rw [barSigmaStarInv_primitiveScalarizationData hnu L hJ4 (m : ℤ)] at hApos
  rw [barB_primitiveScalarizationData hnu L hJ4 (m : ℤ)] at hBpos
  exact ⟨hApos, hBpos⟩

/-- `sigmaHat_m > 0`. -/
private theorem akhc_sigmaHatScalar_pos (m : ℕ) : 0 < akhc_sigmaHatScalar nu L P m := by
  obtain ⟨hApos, hBpos⟩ := akhc_scalars_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
    hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  unfold akhc_sigmaHatScalar
  exact Real.sqrt_pos.2 (div_pos hBpos hApos)

end Integrability

/-! ## Step 2: the block reduction, `ShellLawJ4` only -/

section Reduction

variable {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (m : ℕ)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4

omit [NeZero d] hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
private theorem akhc_matVecMul_one (x : Vec d) :
    Homogenization.matVecMul (1 : Mat d) x = x := by
  change (1 : Matrix (Fin d) (Fin d) ℝ).mulVec x = x
  exact Matrix.one_mulVec x

omit [NeZero d] hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
private theorem akhc_zero_matVecMul (x : Vec d) : Homogenization.matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [Homogenization.matVecMul]

/-- **Step 2.** `Ch04.expectedResponseJCubeSet` at the origin cube `cu_m` is the
quadratic form with `A = sigmaBarStarInvSeq nu L P m`, `B = sigmaBarSeq nu L P
m`, and no cross term (the annealed lower-left block vanishes under
`ShellLawJ4`). Law-free beyond `RestrictionLawCarrier` + integrability + the
scalar reduction. -/
private theorem akhc_expectedResponseJCubeSet_originCube_eq (p q : Vec d) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (m : ℤ)) p q =
      (1 / 2 : ℝ) * vecDot q ((sigmaBarStarInvSeq nu L P m) • q) - vecDot p q +
        (1 / 2 : ℝ) * vecDot p ((sigmaBarSeq nu L P m) • p) := by
  have hP := restrictionLawCarrier_cutoffLaw hnu L P
  have hBlock := akhc_b1_integrable_coarseFullBlockMatrixAtCube_cutoffLaw hnu P L gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    (originCube d (m : ℤ))
  have hraw := hP.integral_restrictionResponseJObservableCubeSet_eq_quadratic_annealedBlockMatrix
    (originCube d (m : ℤ)) p q hBlock
  have hLL : (Homogenization.Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu L P)
      (cubeSet (originCube d (m : ℤ)))).lowerLeft = 0 := by
    rw [← annealedBlockMatrix_eq_ch04 hnu L P (originCube d (m : ℤ))]
    exact annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu L hJ4 (m : ℤ)
  have hUL : (Homogenization.Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu L P)
      (cubeSet (originCube d (m : ℤ)))).upperLeft =
      (sigmaBarSeq nu L P m) • (1 : Mat d) := by
    rw [← annealedBlockMatrix_eq_ch04 hnu L P (originCube d (m : ℤ))]
    rw [annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu L hJ4 (m : ℤ)]
    exact sigmaBar_originCube_eq_smul_one hnu L hJ4 (m : ℤ)
  have hLR : (Homogenization.Book.Ch04.annealedBlockMatrix (cutoffLaw (d := d) nu L P)
      (cubeSet (originCube d (m : ℤ)))).lowerRight =
      (sigmaBarStarInvSeq nu L P m) • (1 : Mat d) := by
    rw [← annealedBlockMatrix_eq_ch04 hnu L P (originCube d (m : ℤ))]
    exact sigmaBarStarInv_originCube_eq_smul_one hnu L hJ4 (m : ℤ)
  rw [Homogenization.Book.Ch04.expectedResponseJCubeSet]
  rw [hraw, hLL, hUL, hLR, akhc_zero_matVecMul, Homogenization.vecDot_zero_right,
    sub_zero, Homogenization.smul_matVecMul, Homogenization.smul_matVecMul,
    akhc_matVecMul_one, akhc_matVecMul_one]

end Reduction

/-! ## Step 3: assembly, the target identity and its J* twin -/

section Assembly

variable {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (m : ℕ)
  (e : Vec d) (he : vecNormSq e = 1)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 he

/-- **Package B1, main identity.** The centered-response identity of `AK.HC`
Section 6 / `CoarseGraining`'s `thetaAtScale_sub_one_eq_two_centeredResponse_special`,
retyped for the cutoff law: no `hStruct`, no `QuantitativeCoarseGrainedEllipticity`,
no `ShellLawJ3`. -/
theorem akhc_thetaCutoff_sub_one_eq_two_centeredResponse_special :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 =
      2 * (Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
              (Homogenization.originCube d (m : ℤ))
              (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) -
            akhc_centeringTerm (sigmaBarStarInvSeq nu L P m) (sigmaBarSeq nu L P m)
              (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e)) := by
  have hc := akhc_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
    hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  have hJeq := akhc_expectedResponseJCubeSet_originCube_eq hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
    (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e)
  have halg := akhc_special_algebra (A := sigmaBarStarInvSeq nu L P m)
    (B := sigmaBarSeq nu L P m) (c := akhc_sigmaHatScalar nu L P m) hc e
  have hthetaeq : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 =
      2 * ((1 / 2 : ℝ) * (sigmaBarStarInvSeq nu L P m * sigmaBarSeq nu L P m - 1) *
        vecNormSq e) := by
    rw [SuperdiffusionCLT.Frozen.Section4.thetaCutoff, he]
    ring
  rw [hthetaeq, hJeq]
  unfold akhc_centeringTerm akhc_specialP akhc_specialQ
  rw [halg]

end Assembly

end

end SuperdiffusionCLT.AKHC61.Response
