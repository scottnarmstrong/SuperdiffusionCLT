/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.ResponseHessianExistence
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1MeasurableInputsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1MeasurableInputsC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1PigeonJensen

/-!
# The `l.RHS.term1` statement with the weak-Hessian binder discharged

`term1_of_residueB` states
`SuperdiffusionCLT.Frozen.Section3.rhs_term1` with eight residue binders:
the five obligations `_hMeasH1`, `_hMeasHminus`, `_hLocMin`, `_hJensen`,
`_hConcDepth` and the three section constants `Cloc`, `hCloc`, `Cc`.  The original
statement also carried the weak-Hessian witness `HD` for the Dirichlet response `w` of
`e.def.w`.  It is not an open question: it is *produced*, for every Dirichlet response, by the
divergence-form Calderón-Zygmund endpoint.

## What this file discharges, and by what

* `HD` — by `Section3.ResponseFields.exists_hasWeakHessianOn_dirichletResponse_family`,
  which consumes the
  `_hw` binder verbatim (`IsDirichletResponse omega S.LPrime S.ellPrime
  S.m (testVector nu S.LPrime P S.n e) (w omega)`) and returns the family in
  `Nonempty` form.  `canonicalResponseHessian` below extracts it with
  `Classical.choice`, so the witness is a definite function of the section data.

Because `HD` is no longer a binder, the obligation `_hMeasH1` — the
`ω`-measurability of the `H̲¹(cu_m)` carrier of the response — is *restated
against that canonical witness*.  This is not a weakening: two weak Hessians of the same
response have the same cube `L²` carrier, so the `H̲¹` carrier is *selection
free*, and the restated obligation is the original one, unchanged, for the particular
witness the section now carries.

## The residue that remains

`_hMeasH1` at the canonical witness, `_hMeasHminus`, `_hLocMin`, `_hJensen`,
`_hConcDepth`, and the three section constants `Cloc`, `hCloc`, `Cc`.  Each of
them remains a hypothesis of `term1_of_residueB`:

* `_hMeasH1` — `Section3.Setup.aemeasurable_vecCubeH1ENorm_grad_of_hessian`
  reduces it to the `ω`-measurability of `ω ↦ ‖D²w_ω‖_{L²(cu_m)}`; the
  measurability of the (unbounded) weak-Hessian operator is not addressed here.
* `_hMeasHminus` — the `ω`-measurability of
  `ω ↦ ‖a_ℓ ∇ũ_n − q̃‖_{Ĥ̲^{-1}(cu_m)}`; that carrier is an uncountable
  supremum over test fields.
* `_hLocMin` — the minimizer clause of `Frozen.Section2.cutoff_localization`.
  Decomposing it into the inputs of its conjunct 3 replaces one binder by eight,
  so it is not a net discharge.
* `_hJensen` — at the pinned proxy `q̃`, a Jensen bound on the difference
  `q̃ − q`; the available duality results are stated at the complementary pin.
* `_hConcDepth` — the sublattice concentration of `a_ℓ ∇ũ_n − q̃` at `Cc`.
* `Cloc`, `hCloc`, `Cc` — section constants; upgrading `Cloc` needs the
  response-factor sign of the localization clause.

## Main results

* `canonicalResponseHessian`: the weak-Hessian family of the response,
  extracted from the existence theorem.
* `term1_of_residueB`: the statement of `rhs_term1` with the
  eight residue binders at the section constants `Cloc`, `Cc`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (vecHatNegENormOrderOne)

noncomputable section

/-! ## The `H̲¹` carrier is independent of the Hessian witness -/

/-! ## The canonical weak Hessian of the response -/

/-- **The weak-Hessian family of the Dirichlet response `w` of `e.def.w`**, as a
definite function of the section data.

`Section3.ResponseFields.exists_hasWeakHessianOn_dirichletResponse_family`
produces a weak Hessian on `openCubeSet (originCube d (S.m : ℤ))` for every
sample from the response equation `_hw` alone; `Classical.choice`
extracts one family from the `Nonempty` witness, so that the downstream
obligations can refer to a single witness instead of carrying the existence as a
hypothesis.  No measurable selection is claimed: the chosen family is an opaque
term, and `_hMeasH1`, the `ω`-measurability of its `H̲¹` carrier, remains the
open obligation. -/
def canonicalResponseHessian (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (S : ScaleSelection) (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
        (w omega).toH1Function :=
  Classical.choice
    (SuperdiffusionCLT.Section3.ResponseFields.exists_hasWeakHessianOn_dirichletResponse_family
      (d := d) hd S (testVector nu S.LPrime P S.n e) w hw)

/-! ## The statement with the weak-Hessian binder discharged -/

/-- **The `l.RHS.term1` statement with only its residue binders.**

The binders and the conclusion are those of the statement with the weak-Hessian binder `HD`,
which is removed: it is
supplied inside the proof by `canonicalResponseHessian d _hd S nu P e w _hw`.
Consequently `_hMeasH1` is stated against that canonical witness rather than
against a free one, which is the same obligation because the `H̲¹` carrier is selection
free.  `qTilde` is pinned at the printed proxy
`q̃ = qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`, and the
section constants `Cloc` and `Cc` are carried as parameters with the gate
`1 ≤ Cc` discharged by `hConcDepth_gate_upgrade`. -/
theorem term1_of_residueB (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
    (Cloc : ℝ) (hCloc : 1 ≤ Cloc) (Cc : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega))
        (_hMeasH1 : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeH1ENorm (originCube d (S.m : ℤ)) (w omega).toH1Function.grad
            (fun x => fun i j =>
              (canonicalResponseHessian d _hd S nu P e w _hw omega).hess i j x))
          P.toMeasure)
        (_hMeasHminus : AEMeasurable (fun omega : ShellSeq d =>
          vecHatNegENormOrderOne (originCube d (S.m : ℤ))
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) -
                qVector hnu P S.ell S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e))) P.toMeasure)
        (_hLocMin : ∀ U : Book.Ch02.Domain d,
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
                      2 * vecDot p q))
        (_hJensen : ENNReal.ofReal (Real.sqrt (vecNormSq
              (qVector hnu P S.ell S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) -
                qVector hnu P S.LPrime S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e)))) ≤
          (∫⁻ omega : ShellSeq d,
              (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x -
                    gluedGradientField hnu S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x))) ^ (2 : ℕ)
            ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
        (_hConcDepth : ∀ j : ℕ,
          (∫⁻ omega : ShellSeq d,
              ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                    qVector hnu P S.ell S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e)))
            ∂P.toMeasure : ℝ≥0∞) ≤
            ENNReal.ofReal (Cc *
                (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
              (∫⁻ omega : ShellSeq d,
                  ENNReal.ofReal (vecSqAvg (originCube d (S.m : ℤ))
                    (fun x => matVecMul
                      ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (gluedGradientField hnu S.ell S.n S.m
                        (fluxSlot nu S.LPrime P S.n e) omega x) -
                        qVector hnu P S.ell S.ell S.n S.m
                          (fluxSlot nu S.LPrime P S.n e)))
              ∂P.toMeasure : ℝ≥0∞))
        (_hPigeon : 2 * S.h ≤ S.m),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                  qVector hnu P S.LPrime S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
            ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) := by
  obtain ⟨C, hC1, hmain⟩ :=
    term1_of_obligations d _hd Cloc hCloc (max 1 Cc) (le_max_left 1 Cc)
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hMeasH1 hMeasHminus hLocMin hJensen hConcDepth hPigeon
  refine hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    (canonicalResponseHessian d _hd S nu P e w hw)
    (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (SuperdiffusionCLT.Section3.Setup.aemeasurable_vecCubeLpENorm_grad hw)
    (aemeasurable_vecCubeLpENorm_fluxDifference_glued hnu P S e)
    hMeasH1 hMeasHminus
    (fun j => aemeasurable_ofReal_vecDepthSqMoment_pairingField hnu P S e
      (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) j)
    (aemeasurable_vecCubeLpENorm_pairingField_glued hnu P S e
      (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)))
    (aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_gluedField (hnu := hnu)
      (LPrime := S.LPrime) (ellPrime := S.ellPrime) (k := S.n) (m := S.m)
      (L := S.ell) (F := fluxSlot nu S.LPrime P S.n e)
      (qTilde := qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))
      (p := testVector nu S.LPrime P S.n e) (mu := P.toMeasure) (w := w) hw)
    hLocMin
    (measurable_coeffCubeLinftyENorm nu S.ell S.ell)
    (measurable_shellDerivCubeLinftyENorm S.ell S.LPrime S.n)
    hJensen
    (hQTilde_of_qTilde_proxy hnu P S e)
    (fun j => le_trans (hConcDepth j)
      (hConcDepth_gate_upgrade (le_max_right 1 Cc)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) _))
    hPigeon

end

end SuperdiffusionCLT.Section3.Terms
