/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermsCombined
public import SuperdiffusionCLT.Section4.Mixing.AnnealedFinal
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# mixBase: the pointwise `F1 + F2 + F3` decomposition

`Section4/Mixing/MixWlogWrapperB.lean`'s `mixWlog_smallGapFromBaseB` reduces
`hSmallGapD` to ONE remaining hypothesis `hBase`: a bounded-gap, internal-`K0` small-gap
estimate whose conclusion needs a literal pointwise decomposition `F1 + F2 + F3` of the
coarse-block-minus-`AL` summand (matching `MixingBelowCutoff.lean`'s own
three-way `Γ2`/`Γ1`/`Γ1/3` reading), each piece translation covariant, with
`L ≤ n → F1 ≡ 0 ∧ F2 ≡ 0` — NOT a single combined `(X1+X2+X3)`-amplitude bound
of the kind produced by `TermsCombined.lean`'s
`mixTerms_combineTermsBound` and `AnnealedFinal.lean`'s
`mixFin_annealedComparison`.

This file supplies that pointwise algebraic skeleton, at an internal
auxiliary scale `ell` (an ordinary argument here; `hBase`'s own proof will
choose `ell` as a function of `n, L` and an internal `K0`). It does NOT
treat the analytic (`IsBigO`) half of `hBase`; the closing section below
lists what that half requires.

## Design

`p.mixing.P.three.prime`'s add-and-subtract decomposition
(`DecomposeInstance.lean`,
`TermsCombined.lean`'s `mixTerms_reassembled_eq_add`) splits
`coarseBlockMatrix(R) - Aell` into the localization term plus the gauge term
`mixTerms_gaugeTermMatrix`. The gauge term's own explicit block form
(`mixBase_gaugeTermMatrix_eq`, re-derived here from the two PUBLIC ingredients
`mixTerms_annealedBlockDiag` and `mixTerms_gaugeTermBlockForm` — the existing
private form in `TermGaugeBilinear.lean` is file-scoped) shows it splits
EXACTLY, as a matrix, into a piece linear in the averaged stream increment
`h_R` (the two off-diagonal blocks, `mixBase_F1`) and a piece quadratic in
`h_R` (the upper-left block alone, `mixBase_F2`): `mixBase_F1 + mixBase_F2 =
gaugeTermMatrix`'s bilinear value, exactly (`mixBase_F1_add_F2_eq_gaugeTermMatrix_bilinear`).

But `hBase`'s target sum is relative to `AL` (`annealedBlockMatrix nu L ...`),
not `Aell`: `coarseBlockMatrix(R) - Aell = coarseBlockMatrix(R) - AL + (AL -
Aell)`, so the constant (`R`- and `omega`-independent) correction `-(AL -
Aell)` must be folded into one of the three pieces for the pointwise identity
to hold literally. `mixBase_F3` folds it into the localization piece:
`F3 := localizationTerm - (AL - Aell)`. Since the correction is constant in
`(R, omega)` it is trivially translation covariant, so `F3`'s covariance
reduces to the localization term's own (`coarseBlockMatrix` covariance,
proved as `mixFin_coarseBlockMatrix_hFcov` in `WlogTranslate.lean`,
plus the same `h_R` covariance used for `F1`, `F2`).

`L ≤ n`, combined with `ell ≥ n` (forced by `mixMain_term1BoundBare`'s own
`n ≤ ell` hypothesis, which `hBase`'s eventual proof must respect), gives
`L ≤ ell`, hence `Finset.Ioc ell L = ∅`, hence `finiteShellIncrement omega ell
L ≡ 0` identically (`Section2/Cutoff/Finite.lean`'s definition is a sum over
that literal interval) — so `h_R = 0` for every `R`, and both `mixBase_F1`,
`mixBase_F2` (which are algebraically linear/quadratic in `h_R`) vanish
identically, with NO probabilistic argument needed.

## What `hBase` further requires (not carried out in this file)

* The deterministic per-cube (or per-average) `Γ2`/`Γ1` bilinear bounds
  `2 * avg F1 ≤ X1 * Q_ell`, `2 * avg F2 ≤ X2 * Q_ell` SEPARATELY (not the
  combined `(4tY1+2t²Y2)` bound of `TermGaugeBilinear.lean`/`TermGaugeFinal.lean`)
  — reusing `TermGaugeFinal.lean`'s `Γ2`/`Γ1`
  Orlicz bounds on `mixGaugeFinal_Y1`/`Y2` and `TermGaugeFinalB.lean`'s
  `mixGaugeFinal_X1g_isBigO`/`mixGaugeFinal_X2g_isBigO` (already at the exact
  `tL`-based amplitude of the statement) needs a fresh Cauchy-Schwarz argument splitting the
  cross terms from the diagonal term (the private
  `mixTail_cross_le`/`mixTail_diag_le` machinery of `TermGaugeBilinear.lean`
  is file-scoped and not reusable; the same elementary argument needs
  re-deriving here or in a follow-up file).
* The Aell-normalized bound on `F3` (`X3 := X3loc + [correction amplitude]`),
  where `X3loc` is `MixMainTerm1Bare.lean`'s
  `mixMain_term1BoundBare`, and `[correction amplitude]` is the DETERMINISTIC
  (`omega`-independent) bound `AnnealedFinal.lean`'s `mixFin_annealedComparison`
  already supplies on `2*(AL - Aell bilinear)` (fed `mixMain_term1BoundBare`
  and the gauge witnesses of `TermGaugeFinalB.lean` as its own
  `hLocBound`/`hGaugeBound`) — the REVERSE sign is obtained by evaluating that
  same universally-quantified bound at `(-p, q)` (`InvertB.lean`'s docstring
  already uses this trick; `Q_ell(-p) = Q_ell(p)` since `Q_ell` is quadratic).
  A constant (`omega`-independent) real is `O_Γσ` of itself at any `σ > 0`
  trivially.
* `ConvertNormalization.lean`'s `mixMain_convertNormalization_bilinear`,
  applied separately to `F1`, `F2`, `F3` (it is agnostic to how many pieces
  there are — it converts ONE bilinear form's Aell-sandwich bound to an
  AL-sandwich bound, amplitude scaled by `(1-t)⁻¹`), using `InvertB.lean`'s
  `mixMain_invertB_scalar_bounds`/`mixMain_quadraticForm_dom_of_scalar_bounds`
  fed the SAME `mixFin_annealedComparison` instance above for the `t ≤ 1/2`
  domination (this needs `t ≤ 1/2`, to be checked for the internal-`K0`, `ell`-near-`n` design;
  not carried out here).
* The internal `ell` choice itself (as a function of `n, L, K0`) and the
  final `mb`-vs-`m` bookkeeping matching the exact
  `hBase` binder of the wlog wrapper (this file's lemmas are stated at a free `ell : ℕ`
  parameter, deliberately, so the caller supplies whatever choice its own
  case split needs).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)
open SuperdiffusionCLT.Section3.Terms (translateReg_finiteShellIncrement)

noncomputable section

variable {d : ℕ}

/-! ## Translation covariance of the averaged stream increment, general form -/

/-- **General translation covariance of the averaged stream increment.** The
general (`translateSet z U`, not tied to a specific triadic cube) form of
`Section3/Terms/TranslatedBlocks.lean`'s
`volumeAverageMat_cubeSet_finiteShellIncrement_translate`, proved the same
way (dropping the initial cube-specific rewrite, since `U` is already in
`translateSet` form here). -/
theorem mixBase_volumeAverageMat_translateSet_finiteShellIncrement
    (z : Vec d) (U : Set (Vec d)) (omega : ShellSeq d) (ell L : ℕ) :
    volumeAverageMat (translateSet z U) (fun y => finiteShellIncrement omega ell L y) =
      volumeAverageMat U
        (fun y => finiteShellIncrement (ShellField.translateSequence z omega) ell L y) := by
  funext i j
  rw [volumeAverageMat, volumeAverageMat, Book.Ch01.volumeAverage_translateSet_eq_comp_addRight]
  refine congrArg (volumeAverage U) ?_
  funext x
  exact congrFun (congrFun (congrArg (fun a : RegCoeffField d => a.toFun x)
    (translateReg_finiteShellIncrement z omega ell L)) i) j

/-! ## The explicit block form of the gauge term, re-derived from public ingredients -/

/-- **The explicit block form of `mixTerms_gaugeTermMatrix`.** Re-derives
`TermGaugeBilinear.lean`'s file-scoped `mixTail_gaugeTermMatrix_eq` from the
two PUBLIC ingredients `mixTerms_annealedBlockDiag`
(`Term2ScaleComparison.lean`) and `mixTerms_gaugeTermBlockForm`
(`Term2ScaleComparison.lean`), identically to that file's own proof. -/
theorem mixBase_gaugeTermMatrix_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : ShellLawJ4 d P) (n : ℤ) (R : TriadicCube d) :
    mixTerms_gaugeTermMatrix nu omega ell L P n R =
      { upperLeft :=
          sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) •
            (matTranspose (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) *
              volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y))
        upperRight :=
          -(sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) •
            matTranspose (volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)))
        lowerLeft :=
          -(sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) •
            volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y))
        lowerRight := 0 } := by
  show
    ofFullBlockMat
        (toFullBlockMat
            (blockMatMul (blockMatTranspose (blockG (-(volumeAverageMat (cubeSet R)
                  (fun y ↦ finiteShellIncrement omega ell L y)))))
              (blockMatMul (annealedBlockMatrix nu ell P (cubeSet (originCube d n)))
                (blockG (-(volumeAverageMat (cubeSet R)
                    (fun y ↦ finiteShellIncrement omega ell L y))))))
          - toFullBlockMat (annealedBlockMatrix nu ell P (cubeSet (originCube d n)))) = _
  rw [mixTerms_annealedBlockDiag hnu ell hJ4 n, mixTerms_gaugeTermBlockForm]

/-! ## `F1`, `F2`: the linear/quadratic-in-`h` gauge pieces, and `F3`: the
localization term corrected to the `AL` reference -/

/-- `F2`, the piece of the gauge term quadratic in the averaged stream
increment `h_R` (the upper-left block of `mixBase_gaugeTermMatrix_eq`). -/
noncomputable def mixBase_F2 [NeZero d] (nu : ℝ) (ell L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℤ) (R : TriadicCube d) (omega : ShellSeq d) (p q : BlockVec d) : ℝ :=
  sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n)) *
    vecDot p.1 (matVecMul (matTranspose (volumeAverageMat (cubeSet R)
          (fun y ↦ finiteShellIncrement omega ell L y)) *
        volumeAverageMat (cubeSet R) (fun y ↦ finiteShellIncrement omega ell L y)) q.1)

/-- `F1`, the piece of the gauge term linear in the averaged stream increment
`h_R` (the two off-diagonal blocks of `mixBase_gaugeTermMatrix_eq`). -/
noncomputable def mixBase_F1 [NeZero d] (nu : ℝ) (ell L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℤ) (R : TriadicCube d) (omega : ShellSeq d) (p q : BlockVec d) : ℝ :=
  -(sigmaBarStarInvScalar nu ell P (cubeSet (originCube d n))) *
    (vecDot p.1 (matVecMul (matTranspose (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y))) q.2) +
      vecDot p.2 (matVecMul (volumeAverageMat (cubeSet R)
            (fun y ↦ finiteShellIncrement omega ell L y)) q.1))

/-- `F3`, the localization term corrected by the constant (`R`-, `omega`-
independent) `AL`-vs-`Aell` mismatch, so that `F1 + F2 + F3` lands on the
`AL`-relative summand exactly (see the module docstring). -/
noncomputable def mixBase_F3 [NeZero d] (nu : ℝ) (ell L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℤ) (R : TriadicCube d) (omega : ShellSeq d) (p q : BlockVec d) : ℝ :=
  blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P n R) q) -
    (blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d n))) q) -
      blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P n) q))

/-! ## The pointwise sum identity -/

/-- **`F1 + F2` equals the gauge term's bilinear value.** Pure algebra, from
`mixBase_gaugeTermMatrix_eq`'s explicit block form and the block bilinear
primitives. -/
theorem mixBase_F1_add_F2_eq_gaugeTermMatrix_bilinear [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (ell L : ℕ) {P : ProbabilityMeasure (ShellSeq d)} (hJ4 : ShellLawJ4 d P)
    (n : ℤ) (R : TriadicCube d) (p q : BlockVec d) :
    mixBase_F1 nu ell L P n R omega p q + mixBase_F2 nu ell L P n R omega p q =
      blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P n R) q) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rw [mixBase_gaugeTermMatrix_eq hnu omega ell L hJ4 n R]
  have hzero : matVecMul (0 : Mat d) q2 = 0 := by
    change (0 : Mat d).mulVec q2 = 0
    exact Matrix.zero_mulVec q2
  unfold mixBase_F1 mixBase_F2
  simp only [blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd,
    vecDot_add_right, neg_matVecMul, vecDot_neg_right, smul_matVecMul, vecDot_smul_right,
    hzero, vecDot_zero_right]
  ring

/-- **The full pointwise decomposition.** `F1 + F2 + F3`, at every descendant
cube `R` and gauge point `omega`, equals the `AL`-relative summand of the
decomposition in the statement of `p.mixing.P.three.prime`. -/
theorem mixBase_sum_eq [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (ell L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)} (hJ4 : ShellLawJ4 d P) (n : ℤ) (R : TriadicCube d)
    (p q : BlockVec d) :
    mixBase_F1 nu ell L P n R omega p q + mixBase_F2 nu ell L P n R omega p q +
        mixBase_F3 nu ell L P n R omega p q =
      blockVecDot p
        (blockMatVecMul (ofFullBlockMat
            (toFullBlockMat
                (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
              toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d n))))) q) := by
  have hgauge := mixBase_F1_add_F2_eq_gaugeTermMatrix_bilinear hnu omega ell L hJ4 n R p q
  have hreassembled : blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P n R) q) =
      blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P n R) q) +
        blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P n R) q) :=
    mixTerms_reassembled_eq_add nu omega ell L P n R p q
  have hreassembled_eq : blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P n R) q) =
      blockVecDot p
          (blockMatVecMul (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q) -
        blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P n) q) :=
    mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear _ _ p q
  have hcoarse_AL_eq : blockVecDot p
      (blockMatVecMul (ofFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
            toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d n))))) q) =
      blockVecDot p
          (blockMatVecMul (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) q) -
        blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d n))) q) :=
    mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear _ _ p q
  unfold mixBase_F3
  rw [hcoarse_AL_eq]
  linarith only [hgauge, hreassembled, hreassembled_eq]

/-! ## `L ≤ ell → F1 ≡ 0 ∧ F2 ≡ 0` -/

/-! ## Translation covariance of `F1`, `F2`, `F3` -/

/-- **`F1` is translation covariant**, in exactly the shape `hFcov`
(`WlogTranslate.lean`'s `mixFin_wlogTranslate`) needs. -/
theorem mixBase_F1_hFcov [NeZero d] (nu : ℝ) (ell L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℤ) :
    ∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d) (p q : BlockVec d),
      cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
        mixBase_F1 nu ell L P n (translateCube w Q) omega p q =
          mixBase_F1 nu ell L P n Q (ShellField.translateSequence zreal omega) p q := by
  intro zreal w Q omega p q hset
  unfold mixBase_F1
  rw [hset, mixBase_volumeAverageMat_translateSet_finiteShellIncrement]

/-- **`F2` is translation covariant**, in exactly the shape `hFcov` needs. -/
theorem mixBase_F2_hFcov [NeZero d] (nu : ℝ) (ell L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (n : ℤ) :
    ∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d) (p q : BlockVec d),
      cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
        mixBase_F2 nu ell L P n (translateCube w Q) omega p q =
          mixBase_F2 nu ell L P n Q (ShellField.translateSequence zreal omega) p q := by
  intro zreal w Q omega p q hset
  unfold mixBase_F2
  rw [hset, mixBase_volumeAverageMat_translateSet_finiteShellIncrement]

/-- **The localization-term matrix is translation covariant.** Combines
`WlogTranslate.lean`'s `coarseBlockMatrix`/`coefficientCutoff` mechanism
(the exact route `mixFin_coarseBlockMatrix_hFcov` uses there) with
`mixBase_volumeAverageMat_translateSet_finiteShellIncrement` for the
gauge-conjugation's averaged stream increment. -/
theorem mixBase_localizationTermMatrix_translate [NeZero d] (nu : ℝ) (ell L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (n : ℤ) (zreal : Vec d) (w : Fin d → ℤ)
    (Q : TriadicCube d) (omega : ShellSeq d)
    (hset : cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q)) :
    mixTerms_localizationTermMatrix nu omega ell L P n (translateCube w Q) =
      mixTerms_localizationTermMatrix nu (ShellField.translateSequence zreal omega) ell L P n Q := by
  unfold mixTerms_localizationTermMatrix
  rw [hset, coarseBlockMatrix_translateSet_eq_translateCoeffField,
    ← translateReg_coefficientCutoff nu zreal omega L,
    mixBase_volumeAverageMat_translateSet_finiteShellIncrement]
  rfl

end

end SuperdiffusionCLT.Section4.Mixing
