/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2LocDisplays
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Assembly
public import SuperdiffusionCLT.Frozen.Section3.WBasicRegbounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Analytic
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2FinalB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2KmnBounds

/-!
# The display `e.RHS.term2.R.bounds` at the printed constant `C(d)`

## Summary

**This module relaxes the binder `hDispDR` of the named-witness reduction of `l.RHS.term2`
to the constant `C₁`.**  The paper writes in `l.RHS.term2` "There exists~$C(d)<\infty$
such that, for the scales selected in~\eqref{e.scale.selection}", and the display
`e.RHS.term2.R.bounds` closes at `\leq C L' |p|` with that same unspecified `C`.
The numeral `1` occurs nowhere in the statement or the display, while the binder `hDispDR` of
the named-witness reduction reads the display at the constant `1`, which the paper never
supplies.  The discharge of `hDispDR` at a dimension-only constant is in `RHSTerm2DispCanonical`.

## What this module proves

* `hRres_of_exists_canonical_at` — the single-witness form of the residue `hRres` at an
  arbitrary display constant `C₁`.
* `term2_finalC_named_dispConst` — the `l.RHS.term2` conclusion with the display `hDispDR` at an
  arbitrary constant `C₁ ≥ 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

/-! ## The `∀ DR` binder of `hRres` at a general display constant -/

/-- **`hRres` from a single existential witness, at the display constant
`C₁`.**

`RHSTerm2LocDisplays.hRres_of_exists_canonical` reads the display
`e.RHS.term2.R.bounds` at `C₁ = 1`.  This is the same statement at an arbitrary
display constant `C₁`: the three clauses are carried through
`cubeLpENorm_ofMat_congr_of_weakGradient`, which is *constant-blind*, so the
proof is the collapse argument of `hRres_collapse` verbatim and nothing in it
depends on the value of `C₁`.  In particular the printed constant `C(d)` may be
substituted for the literal `1` at no cost — which is the only reason the
relaxation in this module is possible at all.

The hypotheses are exactly the two data clauses (`hg`, `hL`) and the three
clauses (`hc`) at the witness `DR₀`, with the display clause at `C₁`. -/
theorem hRres_of_exists_canonical_at (d : ℕ) [NeZero d] {C₁ : ℝ} (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))) :
    (∃ DR₀ : ShellSeq d → Fin d → Vec d → Vec d,
      (∀ (omega : ShellSeq d) (i : Fin d),
        HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                (coefficientCutoff nu omega S.ell).toCoeffField x)
              ((w omega).toH1Function.grad x)) i) (DR₀ omega i)) ∧
      (∀ omega : ShellSeq d,
        MemLp (fun x => HilbertMat.ofMat (fun i j => DR₀ omega i x j)) 2
          (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) ∧
      ((∫⁻ omega : ShellSeq d,
          cubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => HilbertMat.ofMat (fun i j => DR₀ omega i x j)) ^ (2 : ℕ)
          ∂P.toMeasure) ≠ ⊤) ∧
      (AEMeasurable (fun omega : ShellSeq d =>
          cubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => HilbertMat.ofMat (fun i j => DR₀ omega i x j))) P.toMeasure) ∧
      ((∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                  (coefficientCutoff nu omega S.ell).toCoeffField y)
                ((w omega).toH1Function.grad y)) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
        (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
          (∫⁻ omega : ShellSeq d,
              cubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => HilbertMat.ofMat (fun i j => DR₀ omega i x j)) ^
                (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
        C₁ * ((S.LPrime : ℕ) : ℝ) *
          Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)))) →
    ∀ (DR : ShellSeq d → Fin d → Vec d → Vec d),
      (∀ (omega : ShellSeq d) (i : Fin d),
        HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                (coefficientCutoff nu omega S.ell).toCoeffField x)
              ((w omega).toH1Function.grad x)) i) (DR omega i)) →
      (∀ omega : ShellSeq d,
        MemLp (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) 2
          (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) →
      ((∫⁻ omega : ShellSeq d,
          cubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^ (2 : ℕ)
          ∂P.toMeasure) ≠ ⊤) ∧
      (AEMeasurable (fun omega : ShellSeq d =>
          cubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => HilbertMat.ofMat (fun i j => DR omega i x j))) P.toMeasure) ∧
      ((∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                  (coefficientCutoff nu omega S.ell).toCoeffField y)
                ((w omega).toH1Function.grad y)) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
        (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
          (∫⁻ omega : ShellSeq d,
              cubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^
                (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
        C₁ * ((S.LPrime : ℕ) : ℝ) *
          Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e))) := by
  rintro ⟨DR₀, hg, hL, hc⟩ DR hgrad hL2
  have hnorm : ∀ omega : ShellSeq d,
      cubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) =
        cubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => HilbertMat.ofMat (fun i j => DR₀ omega i x j)) :=
    fun omega => cubeLpENorm_ofMat_congr_of_weakGradient 2 (hgrad omega) (hg omega)
      (hL2 omega) (hL omega)
  have hint : (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^ (2 : ℕ)
        ∂P.toMeasure) =
      (∫⁻ omega : ShellSeq d,
        cubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => HilbertMat.ofMat (fun i j => DR₀ omega i x j)) ^ (2 : ℕ)
        ∂P.toMeasure) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
    exact congrArg (fun t : ℝ≥0∞ => t ^ (2 : ℕ)) (hnorm omega)
  exact ⟨by rw [hint]; exact hc.1,
    hc.2.1.congr (Filter.Eventually.of_forall fun omega => (hnorm omega).symm),
    by rw [hint]; exact hc.2.2⟩

/-! ## The named-witness reduction with the display at the printed constant `C₁` -/

/-- **The `l.RHS.term2` conclusion with the display `hDispDR` at an
arbitrary constant `C₁ ≥ 1`.**

This is the named-witness reduction of the term-2 conclusion with its `hDispDR` binder relaxed
from the literal `1 * L' |p|` to `C₁ * L' |p|`, for an arbitrary `C₁ ≥ 1`.  The
hypothesis `hC₁ : 1 ≤ C₁` is exactly the paper's requirement that the constant
of `There exists~$C(d)<\infty$` be at least one, so at `C₁ = C(d)` this is the
printed statement; at `C₁ = 1` it is the literal binder.

**How the relaxed constant is absorbed, explicitly.**  The relaxed display is
fed to the parameterized chain `RHSTerm2Assembly.term2_of_residue` at the
same `C₁` (`term2_of_residue d hd C₁ hC₁ Cloc' hCloc'`).  That chain is the
composition of `l_RHS_term2_of_anchors_proxyMeasurable` (`RHSTerm2MeasurabilityB`)
with `l_RHS_term2_of_anchors_constFirst` and `l_RHS_term2_of_anchors_glued`; it
returns a *terminal* constant `C` with `1 ≤ C` and

`|∫ …| ≤ C * nu^{-3} * (L')^2 * 3^{-(ℓ-n)/2}`,

and `C` is a function of `C₁`, `Cloc` and `d` alone, so the relaxed constant is
absorbed into the term-2 chain's own constant `C` with no side condition beyond
`1 ≤ C₁` and `1 ≤ Cloc'`.  The one constant supplied here that was not in
the earlier reduction is `Cloc' := max 1 (√(max 0 Cloc * shellDerivLargeCubeMomentConst d))`,
whose `≥ 1` half is `le_max_left 1 _`.

Every other binder is verbatim from the named-witness reduction; the proof replaces the
named-clause package `hRcanon` by the relaxed collapse
`hRres_of_exists_canonical_at` at `C₁` and the cube comparison by
`hcube_of_stationarity`, exactly as that reduction does. -/
theorem term2_finalC_named_dispConst (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁) (Cloc : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection) (hSorder : ScalesOrdering S),
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)) →
        (hLocMin : ∀ U : Book.Ch02.Domain d,
            (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
            ∀ (omega' : ShellSeq d) (p q : Vec d)
              (u : AHarmonicFunction
                (fun x : Vec d =>
                  (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                    volumeAverageMat (U : Set (Vec d))
                      (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                (U : Set (Vec d)))
              (v : AHarmonicFunction
                (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
              (∀ w : AHarmonicFunction
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                  (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q u)) →
              (∀ w : AHarmonicFunction
                  (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
                volumeAverage (U : Set (Vec d))
                    (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
                  Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                      anchorDerivSup S.ell S.LPrime S.n omega' *
                    (ResponseJ (U : Set (Vec d)) p q
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                      ResponseJ (U : Set (Vec d)) p q
                        (coefficientCutoff nu omega' S.ell).toCoeffField +
                      2 * vecDot p q)) →
        (hfinR : (∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                    (coefficientCutoff nu omega S.ell).toCoeffField y)
                  ((w omega).toH1Function.grad y)) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) →
        (hFinDR : (∫⁻ omega : ShellSeq d,
            cubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => HilbertMat.ofMat (fun i j =>
                canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
                  w hw omega i x j)) ^ (2 : ℕ)
            ∂P.toMeasure) ≠ ⊤) →
        (hMeasDR : AEMeasurable (fun omega : ShellSeq d =>
            cubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => HilbertMat.ofMat (fun i j =>
                canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
                  w hw omega i x j))) P.toMeasure) →
        -- `hDispDR`: the display `e.RHS.term2.R.bounds` at the printed constant `C₁`
        (hDispDR :
          (∫⁻ omega : ShellSeq d,
                vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                  (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                    ((w omega).toH1Function.grad y)) ^
                  (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
            (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
              (∫⁻ omega : ShellSeq d,
                  cubeLpENorm (originCube d (S.m : ℤ)) 2
                    (fun x => HilbertMat.ofMat (fun i j =>
                      canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
                        w hw omega i x j)) ^
                    (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
            C₁ * ((S.LPrime : ℕ) : ℝ) *
              Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e))) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        testVector nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
  obtain ⟨C, hC₁', hmain⟩ := term2_of_residue d hd C₁ hC₁
    (max 1 (Real.sqrt (max 0 Cloc * shellDerivLargeCubeMomentConst d)))
    (le_max_left 1 _)
  refine ⟨C, hC₁', ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder e he w hw
    hLocMin hfinR hFinDR hMeasDR hDispDR
  have hCloc0 : (0 : ℝ) ≤ max 0 Cloc := le_max_left 0 Cloc
  have hLocMin' : ∀ U : Book.Ch02.Domain d,
      (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
      ∀ (omega' : ShellSeq d) (p q : Vec d)
        (u : AHarmonicFunction
          (fun x : Vec d =>
            (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
              volumeAverageMat (U : Set (Vec d))
                (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
          (U : Set (Vec d)))
        (v : AHarmonicFunction
          (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
        (∀ w : AHarmonicFunction
            (fun x : Vec d =>
              (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                volumeAverageMat (U : Set (Vec d))
                  (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
            (U : Set (Vec d)),
            volumeAverage (U : Set (Vec d))
                (scalarResponseIntegrand (U : Set (Vec d))
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                  p q w) ≤
              volumeAverage (U : Set (Vec d))
                (scalarResponseIntegrand (U : Set (Vec d))
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                  p q u)) →
        (∀ w : AHarmonicFunction
            (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
            volumeAverage (U : Set (Vec d))
                (scalarResponseIntegrand (U : Set (Vec d))
                  (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
              volumeAverage (U : Set (Vec d))
                (scalarResponseIntegrand (U : Set (Vec d))
                  (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
          volumeAverage (U : Set (Vec d))
              (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
            (max 0 Cloc) * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                anchorDerivSup S.ell S.LPrime S.n omega' *
              (ResponseJ (U : Set (Vec d)) p q
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                ResponseJ (U : Set (Vec d)) p q
                  (coefficientCutoff nu omega' S.ell).toCoeffField +
                2 * vecDot p q) := by
    intro U hU omega' p q u v hu hv
    refine le_trans (hLocMin U hU omega' p q u v hu hv) ?_
    exact locMinConstant_mono (nu := nu) S omega' _
      hnu.le (locMinResponseFactor_nonneg nu hnu S U omega' p q) (le_max_right 0 Cloc)
  exact hmain nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder e he w hw
    (hLocM_at_const d hnu hPrefix hJ2 hJ3 hJ4 S hSorder e he hCloc0 hLocMin')
    (hLocN_at_const d hnu hPrefix hJ2 hJ3 hJ4 S hSorder e he hCloc0 hLocMin')
    hfinR
    (hRres_of_exists_canonical_at (C₁ := C₁) d nu P S e w
      ⟨canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e) w hw,
        (canonicalRJacobian_hasWeakGradientOn d hd nu S hSorder
          (testVector nu S.LPrime P S.n e) w hw).1,
        (canonicalRJacobian_hasWeakGradientOn d hd nu S hSorder
          (testVector nu S.LPrime P S.n e) w hw).2,
        hFinDR, hMeasDR, hDispDR⟩)
    (hPtilde_of_cubeEnergy (d := d) nu hnu P S hSorder e hPrefix hJ2 hJ3 hJ4
      (hcube_of_stationarity hnu hPrefix hJ2 hSorder (fluxSlot nu S.LPrime P S.n e)))

end

end SuperdiffusionCLT.Section3.Terms
