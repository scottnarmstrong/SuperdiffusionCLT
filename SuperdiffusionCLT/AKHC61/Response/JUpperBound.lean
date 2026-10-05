/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.Integrability
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import Homogenization.Book.Ch04.Theorems.Expectations
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.NormalizedCutoff

/-!
# Package B2: the div-curl / J-upper-bound response inequality for the cutoff law

The target is `e.divcurl.conclusion.pre`: instantiate `CoarseGraining`'s

`Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.NormalizedCutoff
  .expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_normalizedCutoff`

at the cutoff law `cutoffLaw nu L P`, `s = t = 1/2`, and discharge its
four hypotheses `hParent`, `hJ`, `hGradSq`, `hFluxSq`.

## What is discharged here

`hParent` and `hJ` are fully discharged, **without `ShellLawJ3`**, from package A1
(`SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2`) alone. The route:

1. `akhc_integrable_blockMatEntry_cutoffLaw` transports A1's entrywise integrability (stated on
   the shell-sequence carrier `P.toMeasure`) to the pushforward `cutoffLaw nu L P`, along the
   same `Measure.map`/`integrable_map_measure` idiom the (`ShellLawJ3`-dependent)
   `SuperdiffusionCLT.Section2.Annealed.integrable_blockMatEntry_cutoffLaw` uses.
2. `akhc_integrable_coarseFullBlockMatrixAtCube_cutoffLaw` assembles the entrywise facts, over
   the finite index `Homogenization.BlockCoord d`, into bundled integrability of
   `Ch04.coarseFullBlockMatrixAtCube Q`, for **any** triadic cube `Q` (not only the parent), via
   `MeasureTheory.Integrable.of_eval`.
3. `akhc_integrable_restrictionResponseJObservableCubeSet_cutoffLaw` feeds that into CG's
   `Ch04.RestrictionLawCarrier.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube`
   to integrate the scalar response observable at any cube. Since it holds at *every* cube, it
   discharges both `hParent` (at the parent `originCube d m`) and `hJ` (at every descendant, with
   the descendant membership hypothesis simply unused).

## What is NOT discharged here, and why

`hGradSq`/`hFluxSq` ask for square-integrability of the *full* (countable-supremum) weak norms
`Ch04.canonicalScalarResponseGradientWeakNormCubeSet`/`...FluxWeakNormCubeSet`. CG's own
deterministic maximizer bound (`WeakNormsMaximizer.weakNormsMaximizerGradient_homogenizationScale`)
dominates these pointwise by `2 * gradientRHSAtScale C m k s s' p q p0 a`, but
that RHS itself is built from `Ch04.LambdaSqCoeffField`/`lambdaSqCoeffField` (an infinite
geometric-weighted sum over triadic scales, `Ch02/MultiscaleEllipticity/...`), not from anything
A1 or A3 controls. Bounding `LambdaSqCoeffField` samplewise by AK.HC's event quantity `M_{n,ρ}`
is the "main inequality" treated in `AKHC61/WeakNorms/`, and its probabilistic second moment
(`AKHC61/Tails/`) is a further, separate step. Threading square-integrability through
`gradientRHSAtScale`'s four summands (`gradientAverageTermAtScale`,
`gradientMismatchTermAtScale`, `gradientLowScaleTailAtScale`, `gradientConstantTailAtScale`)
would in any case still bottom out at `LambdaSqCoeffField`/`lambdaSqCoeffField` integrability.

So `hGradSq`/`hFluxSq` are carried here as **named hypotheses**, stated in exactly CG's own
shape (only `P` specialized to `cutoffLaw nu L P`, `s`/`t` fixed to `1/2`) — precisely the
"if you need something from [MaximizerBridgeB], carry it as a named hypothesis with a precise
statement" instruction. This mirrors CG's own architecture: its second target theorem in the
same file (`..._of_normalizedCutoff_of_P4`) *also* leaves `hGradSq`/`hFluxSq` as explicit
hypotheses even under the strictly stronger `(P4)` typing, discharging only `hParent`/`hJ`.

## Refute-first check

The CG hypotheses `hParent`, `hJ` are non-vacuous and genuinely discharged (Step 1-3 above is a
real proof, not a restatement). `hGradSq`/`hFluxSq` are not refuted — nothing here suggests they
are false for the cutoff law — they are simply not covered by the integrability results above.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Response

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open scoped Matrix.Norms.Elementwise

noncomputable section

/-! ## Step 1: entrywise integrability of `bfA_L(Q)` at the cutoff law, from A1 (J3-free) -/

/-- **Entrywise integrability of the coarse block matrix at the cutoff law**, transported from
A1 (`SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2`) along the
pushforward `cutoffLaw`, for **any** triadic cube `Q`. This is the `ShellLawJ3`-free replacement
for `SuperdiffusionCLT.Section2.Annealed.integrable_blockMatEntry_cutoffLaw`,
which needs `ShellLawJ3` (via `integrable_blockMatEntry_coarseBlockMatrix`); the root's (P2')/
(P3') binders do not carry J3. -/
theorem akhc_integrable_blockMatEntry_cutoffLaw
    (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
                annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    (Q : Homogenization.TriadicCube d) (alpha beta : Homogenization.BlockCoord d) :
    MeasureTheory.Integrable
      (fun a : Homogenization.RegCoeffField d =>
        Homogenization.blockMatEntry
          (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a.toFun) alpha beta)
      (cutoffLaw (d := d) nu L P) := by
  rw [cutoffLaw]
  refine (MeasureTheory.integrable_map_measure
    ((aemeasurable_blockMatEntry_cutoffLaw hnu L P Q alpha
      beta).aestronglyMeasurable)
    (measurable_coefficientCutoff nu L).aemeasurable).2 ?_
  exact SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2
    d hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
    hpPsiS hGrowth hP2 Q alpha beta

/-! ## Step 2: bundled full-block-matrix integrability, at any cube -/

/-- Bundled integrability of the full doubled coarse block matrix at the cutoff law, for **any**
triadic cube, assembled entrywise from `akhc_integrable_blockMatEntry_cutoffLaw` via
`MeasureTheory.Integrable.of_eval` on the finite index `Homogenization.BlockCoord d`. This mirrors
the (`ShellLawJ3`-dependent)
`SuperdiffusionCLT.Section2.Annealed.integrable_coarseFullBlockMatrixAtCube_cutoffLaw`. -/
theorem akhc_integrable_coarseFullBlockMatrixAtCube_cutoffLaw
    (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
                annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    (Q : Homogenization.TriadicCube d) :
    MeasureTheory.Integrable (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q)
      (cutoffLaw (d := d) nu L P) := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro alpha
  refine MeasureTheory.Integrable.of_eval ?_
  intro beta
  have h := akhc_integrable_blockMatEntry_cutoffLaw d hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 Q alpha beta
  have hfun :
      (fun a : Homogenization.RegCoeffField d =>
        Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q a alpha beta) =
        fun a : Homogenization.RegCoeffField d =>
          Homogenization.blockMatEntry
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) a.toFun) alpha beta := by
    funext a
    cases alpha <;> cases beta <;> rfl
  rw [hfun]
  exact h

/-! ## Step 3: integrability of the scalar response `J`-observable, at any cube -/

/-- The scalar response `J`-observable `Ch04.restrictionResponseJObservableCubeSet Q p q` is
`P`-integrable at the cutoff law, for **any** triadic cube `Q` and any loading `p q`. This
discharges both `hParent` (at `Q := originCube d m`) and `hJ` (at every descendant `R`, the
descendant-membership hypothesis being simply unused) of CG's normalized-cutoff `J`-upper-bound
theorem. -/
theorem akhc_integrable_restrictionResponseJObservableCubeSet_cutoffLaw
    (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
                annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    (Q : Homogenization.TriadicCube d) (p q : Homogenization.Vec d) :
    MeasureTheory.Integrable
      (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q p q)
      (cutoffLaw (d := d) nu L P) := by
  have hP : Homogenization.Book.Ch04.RestrictionLawCarrier (cutoffLaw (d := d) nu L P) :=
    restrictionLawCarrier_cutoffLaw hnu L P
  have hBlock :
      MeasureTheory.Integrable (Homogenization.Book.Ch04.coarseFullBlockMatrixAtCube Q)
        (cutoffLaw (d := d) nu L P) :=
    akhc_integrable_coarseFullBlockMatrixAtCube_cutoffLaw d hnu P L gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 Q
  exact hP.integrable_restrictionResponseJObservableCubeSet_of_integrable_coarseFullBlockMatrixAtCube
    Q p q hBlock

/-! ## Package B2's target: the normalized-cutoff `J`-upper bound at the cutoff law -/

/-- **Package B2's target.** CG's normalized-cutoff `J`-upper-bound theorem
(`Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.NormalizedCutoff`),
instantiated at the cutoff law `cutoffLaw nu L P` and `s = t = 1/2`. `hParent` and `hJ`
are fully discharged from A1 (Steps 1-3 above), without `ShellLawJ3`. `hGradSq`/`hFluxSq` are
carried as explicit hypotheses, in exactly CG's own shape: closing them needs
`Ch04.LambdaSqCoeffField`/`lambdaSqCoeffField` integrability, which is not yet available (see the
module docstring). -/
theorem akhc_jUpperBound_of_cutoffLaw
    (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    -- (P2') `a.ellipticity.weaker`, copied verbatim from
    -- `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`.
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
                annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    (p q p0 q0 : Homogenization.Vec d)
    (hGradSq :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (Homogenization.originCube d m) (1 / 2 : ℝ) p q p0 a.toFun) ^ 2)
        (cutoffLaw (d := d) nu L P))
    (hFluxSq :
      MeasureTheory.Integrable
        (fun a : Homogenization.RegCoeffField d =>
          (Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (Homogenization.originCube d m) (1 / 2 : ℝ) p q q0 a.toFun) ^ 2)
        (cutoffLaw (d := d) nu L P)) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d m
    let j : ℕ := Int.toNat (m - k)
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) Q p q -
        (1 / 2 : ℝ) * Homogenization.vecDot p0 q0 ≤
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale
        (cutoffLaw (d := d) nu L P) m k (1 / 2 : ℝ) (1 / 2 : ℝ)
        (1 + Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffBound Q)
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant Q)
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep Q j)
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ))
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q (1 / 2 : ℝ))
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff Q
          (1 / 2 : ℝ) (1 / 2 : ℝ))
        p q p0 q0 := by
  have hP : Homogenization.Book.Ch04.RestrictionLawCarrier (cutoffLaw (d := d) nu L P) :=
    restrictionLawCarrier_cutoffLaw hnu L P
  have hstat : Homogenization.Book.Ch04.RestrictionStationaryLaw (cutoffLaw (d := d) nu L P) :=
    restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu L
  have hParent :
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
          (Homogenization.originCube d m) p q) (cutoffLaw (d := d) nu L P) :=
    akhc_integrable_restrictionResponseJObservableCubeSet_cutoffLaw d hnu P L gamma H D m2 PsiS
      KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
      (Homogenization.originCube d m) p q
  have hJ : ∀ R, R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d m) k →
      MeasureTheory.Integrable
        (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet R p q)
        (cutoffLaw (d := d) nu L P) := by
    intro R _
    exact akhc_integrable_restrictionResponseJObservableCubeSet_cutoffLaw d hnu P L gamma H D m2
      PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 R p q
  exact
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_normalizedCutoff
      (s := (1 / 2 : ℝ)) (t := (1 / 2 : ℝ)) hP hstat hk_nonneg hkm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) p q p0 q0 hParent hJ hGradSq hFluxSq

end

end SuperdiffusionCLT.AKHC61.Response
