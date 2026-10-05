/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.HatNegNormMeasurable
public import SuperdiffusionCLT.Section3.Terms.SublatticeConcentrationDepth
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays

/-!
# Residues of `term1_final`: the difference-Jensen input and the constant gates

`SuperdiffusionCLT.Section3.Terms.term1_final` states
the `l.RHS.term1` conclusion from seven binders: the section constants
`Cloc`, `Cc`, and the five obligations `_hMeasH1`, `_hMeasHminus`, `_hLocMin`,
`_hJensen`, `_hConcDepth`.  This module advances two of them and wires the one
that can be discharged.

## The difference-Jensen input `_hJensen`

At the printed proxy `q̃ = qVector hnu P S.ell S.ell S.n S.m F` (the coefficient
scale is the *second* argument of `qVector`) the obligation `_hJensen` of
`term1_final` compares the annealed `cu_ℓ`-average of `a_ℓ ∇ũ_ℓ` against the
annealed `L²` energy of `a_ℓ (∇ũ_{L'} − ∇ũ_ℓ)`.  The two are the **difference**
of the two annealed averages `q̃` and `q = qVector hnu P S.LPrime S.ell S.n S.m F`
and the cube `L²` energy of the very same field, up to the sign of the
difference (which the cube `L²` carrier does not see).  So `_hJensen` is a
*difference*-Jensen bound, not a Jensen bound on one average.

`ofReal_vecNormSq_integral_sub_le` states the difference form: for a probability
measure and two `Vec d`-valued maps with componentwise integrable averages, the
squared magnitude of the difference of the two Bochner integrals is at most the
annealed squared magnitude of the pointwise difference.  The proof is
`ofReal_vecNormSq_integral_le` at the pointwise difference, composed with
the integral identity `∫ V − ∫ W = ∫ (V − W)` — which needs **both** averages
integrable; under the total-integral convention the mixed case (one average
integrable, the other not) is not covered, exactly as
`RHSTerm1MeasurableInputsC` records for the complementary `_hQTilde` pin.
`hJensen_printedProxy_of_integrable` is the resulting reduction of the exact
`_hJensen` binder of `term1_final` to those two integrability hypotheses,
composed with the cube Jensen inequality `ofReal_vecNormSq_volumeAverageVec_le`.

## The concentration moment `_hConcDepth`

The per-sublattice rule of `SublatticeConcentrationDepth` is an `O_{Γ₂}` tail for a nonempty
finset average of centered, lane-measurable, deterministically bounded block observables.  The
printed concentration clause of `l.RHS.term1` is a **moment** bound, so the tail rule alone does
not reach it.  The conversion is the printed Γ₂ moment bound
`abs_moment_le_of_isBigO_gammaSigma_two` at `k = 2`, which bounds the annealed second moment of
the finset average by `A² (1 + Γ 2)`.  The remaining structural identity (that each depth-`j`
descendant mean is such a finset average) is the residue recorded in the
`SublatticeConcentrationDepth` docstring.

## The constant gates `Cloc`, `Cc`

Both constants enter `term1_final` ungated, and the gates `1 ≤ Cloc`,
`1 ≤ Cc` are free (`RHSTerm1Final.locMinConstant_mono`,
`RHSTerm1PigeonJensen.hConcDepth_gate_upgrade`).  The shape that works elsewhere
is the term-3 gate `localizationConst d ≤ CL` of
`RHSTerm3LocAnchor.term3_locAnchor_of_conjunct1`.  `LocMinClause` and
`ConcDepthClause` below name the exact binders of `term1_final` as predicates of
their constants; each clause is monotone in its constant.  Unlike the term-3 constant,
neither `Cloc` nor `Cc` can be *pinned* from the available supply, because both appear as
**hypotheses** in `term1_final`
rather than as conclusions produced at a packaging constant — the localization
clause is not supplied (its conjunct-3 route is refuted) and
the concentration clause is not supplied.  That is the exact standing of the two
constant residues.

## Main results

* `ofReal_vecNormSq_integral_sub_le` — the difference-Jensen inequality
  (unconditional in the two integrability hypotheses, which are its premises).
* `hJensen_printedProxy_of_integrable` — the exact `_hJensen` binder of
  `term1_final` at the printed proxy, from the two integrability hypotheses.
* `term1_final_hMinusFree` — `term1_final` with `_hMeasHminus` discharged by
  `HatNegNormMeasurable.aemeasurable_vecHatNegENormOrderOne_term1Hminus`.
* `LocMinClause`, `ConcDepthClause` — the exact binder shapes of the two clauses
  as predicates of their constants.
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

noncomputable section

variable {d : ℕ}

/-! ## The difference-Jensen inequality -/

/-- **Jensen for the difference of two vector-valued means.**  For a probability
measure `mu` and two `Vec d`-valued maps whose component averages are
integrable, the squared magnitude of the difference of the two Bochner
integrals is at most the annealed mean of the squared magnitude of the pointwise
difference.  This is the *difference* form: it is not a Jensen bound on one
average, and it needs both averages integrable so that the integral of the
difference is the difference of the integrals. -/
theorem ofReal_vecNormSq_integral_sub_le {α : Type*} [MeasurableSpace α] {mu : Measure α}
    [IsProbabilityMeasure mu] {V W : α → Vec d}
    (hV : ∀ i : Fin d, Integrable (fun a => V a i) mu)
    (hW : ∀ i : Fin d, Integrable (fun a => W a i) mu) :
    ENNReal.ofReal (vecNormSq ((∫ a, V a ∂mu) - (∫ a, W a ∂mu))) ≤
      ∫⁻ a, ENNReal.ofReal (vecNormSq (V a - W a)) ∂mu := by
  have hsub : (∫ a, V a ∂mu) - (∫ a, W a ∂mu) = ∫ a, (V a - W a) ∂mu :=
    (integral_sub (integrable_pi_iff.2 hV) (integrable_pi_iff.2 hW)).symm
  rw [hsub]
  refine ofReal_vecNormSq_integral_le (V := fun a => V a - W a) fun i => ?_
  exact MeasureTheory.Integrable.sub' (hV i) (hW i)

/-- **The obligation `_hJensen` of `term1_final` at the printed proxy `q̃`.**  The
conclusion is the exact `_hJensen` binder of `term1_final` at
`q̃ = qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`, from the
two componentwise integrability hypotheses of the annealed `cu_ℓ`-averages of
`a_ℓ ∇ũ_ℓ` and `a_ℓ ∇ũ_{L'}` — the content the difference-Jensen inequality
needs and the only content the available supply cannot provide.  The proof is
`ofReal_vecNormSq_integral_sub_le` followed by the cube Jensen
`ofReal_vecNormSq_volumeAverageVec_le` on the pointwise difference
`a_ℓ (∇ũ_{L'} − ∇ũ_ℓ)`. -/
theorem hJensen_printedProxy_of_integrable [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hInt1 : ∀ i : Fin d, Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (S.ell : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x)) i) P.toMeasure)
    (hInt2 : ∀ i : Fin d, Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (S.ell : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x)) i) P.toMeasure) :
    ENNReal.ofReal (Real.sqrt (vecNormSq
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
        ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2) := by
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hF
  set Q : TriadicCube d := originCube d (S.ell : ℤ) with hQ
  set G₁ : ShellSeq d → Vec d → Vec d := fun omega x =>
    matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.ell S.n S.m F omega x) with hG₁
  set G₂ : ShellSeq d → Vec d → Vec d := fun omega x =>
    matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.LPrime S.n S.m F omega x) with hG₂
  set G : ShellSeq d → Vec d → Vec d := fun omega x =>
    matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
      (gluedGradientField hnu S.LPrime S.n S.m F omega x -
        gluedGradientField hnu S.ell S.n S.m F omega x) with hG
  -- the two annealed averages are the Bochner integrals defining the two proxies
  have hq₁ : qVector hnu P S.ell S.ell S.n S.m F =
      ∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (G₁ omega) ∂P.toMeasure := by
    rw [hF, hQ, hG₁]
    exact qVector_eq hnu P S.ell S.ell S.n S.m _
  have hq₂ : qVector hnu P S.LPrime S.ell S.n S.m F =
      ∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q) (G₂ omega) ∂P.toMeasure := by
    rw [hF, hQ, hG₂]
    exact qVector_eq hnu P S.LPrime S.ell S.n S.m _
  -- the difference-Jensen step at the two averages
  have hdiff : ENNReal.ofReal (vecNormSq
        (qVector hnu P S.ell S.ell S.n S.m F -
          qVector hnu P S.LPrime S.ell S.n S.m F)) ≤
      ∫⁻ omega : ShellSeq d, ENNReal.ofReal (vecNormSq
        (volumeAverageVec (openCubeSet Q) (G₁ omega) -
          volumeAverageVec (openCubeSet Q) (G₂ omega))) ∂P.toMeasure := by
    rw [hq₁, hq₂]
    exact ofReal_vecNormSq_integral_sub_le (V := fun omega => volumeAverageVec (openCubeSet Q) (G₁ omega))
      (W := fun omega => volumeAverageVec (openCubeSet Q) (G₂ omega)) hInt1 hInt2
  -- the pointwise difference of the averages is the average of the difference
  have hsub : ∀ omega : ShellSeq d,
      volumeAverageVec (openCubeSet Q) (G₁ omega) -
        volumeAverageVec (openCubeSet Q) (G₂ omega) =
      volumeAverageVec (openCubeSet Q) (fun x => G₁ omega x - G₂ omega x) := by
    intro omega
    refine (volumeAverageVec_sub (fun i => ?_) (fun i => ?_)).symm
    · exact ((memL2On_component_of_memVectorL2
        (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q
          (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q)) i).integrable
        (by norm_num))
    · exact ((memL2On_component_of_memVectorL2
        (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q
          (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q)) i).integrable
        (by norm_num))
  -- the pointwise difference of the two cut-off fields is minus the cut-off of
  -- the difference of the two gradients (the difference-Jensen sign)
  have hsubmul : ∀ (M : Mat d) (v w : Vec d),
      matVecMul M (v - w) = matVecMul M v - matVecMul M w := by
    intro M v w
    rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]
  have hpt : ∀ (omega : ShellSeq d) (x : Vec d),
      G₁ omega x - G₂ omega x = -(G omega x) := by
    intro omega x
    have h1 : G₂ omega x - G₁ omega x = G omega x := by
      simp only [hG₁, hG₂, hG]
      exact (hsubmul _ _ _).symm
    rw [← neg_sub, h1]
  have hsub' : ∀ omega : ShellSeq d,
      volumeAverageVec (openCubeSet Q) (G₁ omega) -
          volumeAverageVec (openCubeSet Q) (G₂ omega) =
        volumeAverageVec (openCubeSet Q) (fun x => -(G omega x)) := by
    intro omega
    rw [hsub omega, funext (hpt omega)]
  -- the cube Jensen step on the pointwise difference, with the sign absorbed by
  -- `vecCubeLpENorm_neg`
  have hstep : (∫⁻ omega : ShellSeq d, ENNReal.ofReal (vecNormSq
        (volumeAverageVec (openCubeSet Q) (G₁ omega) -
          volumeAverageVec (openCubeSet Q) (G₂ omega))) ∂P.toMeasure) ≤
      ∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm Q 2 (G omega)) ^ (2 : ℕ) ∂P.toMeasure := by
    refine lintegral_mono fun omega => ?_
    rw [hsub' omega]
    have hmem : MemVectorL2 (openCubeSet Q) (fun x => -(G omega x)) :=
      (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q
        ((memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q).sub
          (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q))).neg
    have hJ := ofReal_vecNormSq_volumeAverageVec_le (Q := Q)
      (G := fun x => -(G omega x)) hmem
    rw [vecCubeLpENorm_neg] at hJ
    exact hJ
  -- raise to the power `1/2`
  calc ENNReal.ofReal (Real.sqrt (vecNormSq
        (qVector hnu P S.ell S.ell S.n S.m F -
          qVector hnu P S.LPrime S.ell S.n S.m F)))
      = (ENNReal.ofReal (vecNormSq
          (qVector hnu P S.ell S.ell S.n S.m F -
            qVector hnu P S.LPrime S.ell S.n S.m F))) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg (vecNormSq_nonneg _)
            (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (∫⁻ omega : ShellSeq d, ENNReal.ofReal (vecNormSq
          (volumeAverageVec (openCubeSet Q) (G₁ omega) -
            volumeAverageVec (openCubeSet Q) (G₂ omega))) ∂P.toMeasure) ^
              ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hdiff (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ ≤ (∫⁻ omega : ShellSeq d,
          (vecCubeLpENorm Q 2 (G omega)) ^ (2 : ℕ) ∂P.toMeasure) ^
            ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hstep (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-! ## Wiring the discharged measurability obligation

`HatNegNormMeasurable.aemeasurable_vecHatNegENormOrderOne_term1Hminus` supplies the
`_hMeasHminus` binder of `term1_final` verbatim.  The wrapper below restates
`term1_final` with that binder removed and feeds that theorem in its place,
so the obligation count drops from five to four. -/

/-- **`term1_final` with `_hMeasHminus` discharged.**  The binders and
conclusion are those of `term1_final` with the `_hMeasHminus` obligation
removed; the proof supplies it by
`HatNegNormMeasurable.aemeasurable_vecHatNegENormOrderOne_term1Hminus`, which is the
exact shape of that obligation. -/
theorem term1_final_hMinusFree (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (Cloc : ℝ) (Cc : ℝ) :
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
  obtain ⟨C, hC1, hmain⟩ := term1_final d _hd Cloc Cc
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hMeasH1 hLocMin hJensen hConcDepth hPigeon
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hMeasH1 (aemeasurable_vecHatNegENormOrderOne_term1Hminus hnu S P e)
    hLocMin hJensen hConcDepth hPigeon

/-! ## The two constant gates at the clause level

`term1_final` takes both section constants as free reals and never assumes
`1 ≤ Cloc` or `1 ≤ Cc`.  The gates are nevertheless
free: `RHSTerm1PigeonJensen.hConcDepth_gate_upgrade` is the scalar core of the
concentration gate.  The two clauses below name the exact binder shapes of `term1_final`,
and each is upward-closed in its constant:

* `LocMinClause nu S Cloc → Cloc ≤ Cloc' → LocMinClause nu S Cloc'`;
* `ConcDepthClause nu hnu S P e Cc → Cc ≤ Cc' → ConcDepthClause nu hnu S P e Cc'`.

So each clause is upward-closed in its constant — the same gated shape as
`RHSTerm3LocAnchor.term3_locAnchor_of_conjunct1`, where the constant is compared
against the canonical `localizationConst d`.  The difference to term 3 is that
no *pin* is available here: term 3's gate is `localizationConst d ≤ CL` because
the clause is *proved* at the canonical constant, whereas the term-1
localization clause is not supplied at any constant (its conjunct-3 route is
refuted) and the concentration clause
is not supplied at any constant, so `Cloc` and `Cc` are monotone thresholds with
no canonical witness. -/

/-- The localization clause `_hLocMin` of `term1_final`, as a predicate of the
section constant `Cloc`: the clause shape is verbatim that binder, with the
quantified data exposed as arguments. -/
def LocMinClause (d : ℕ) (nu : ℝ) (S : ScaleSelection) (Cloc : ℝ) : Prop :=
  ∀ U : Book.Ch02.Domain d,
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
              2 * vecDot p q)

/-- The concentration clause `_hConcDepth` of `term1_final`, as a predicate of
the section constant `Cc`: the clause shape is verbatim that binder. -/
def ConcDepthClause (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu) (S : ScaleSelection)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) (Cc : ℝ) : Prop :=
  ∀ j : ℕ,
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
        ∂P.toMeasure : ℝ≥0∞)

end

end SuperdiffusionCLT.Section3.Terms
