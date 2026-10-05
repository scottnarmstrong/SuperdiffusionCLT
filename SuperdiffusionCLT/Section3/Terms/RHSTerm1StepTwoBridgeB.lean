/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1StepTwoBridge

/-!
# `l.RHS.term1` from the anchors, with no continuity hypothesis

The statement is `e.RHS.term1` of `l.RHS.term1`.

The earlier assembly of `l.RHS.term1` from the anchors discharges both
step displays, but it still carries one binder that the glued
field does not satisfy: `_hCont`, the continuity of the centred glued flux
`a_ℓ∇ũ_n − q̃`.  That is not a missing lemma, it is false --
`GluedField.gluedGradientField` is a sum of indicators of disjoint triadic
sub-cubes -- so that statement could not be instantiated at the field it is about.

`RHSTerm1StepTwoBridge.hminus_second_moment_memLp` removes it at the third
display of Step 2, by reading the multiscale line of the paper in the
`L̲²` form `RHSTerm1StepTwoOrderOneC.lintegral_vecHatNegENormOrderOne_sq_le_memLp`.  This
file carries that through to the full statement:
`l_RHS_term1_of_anchors_constFirst_memLp` is that assembly
with `_hCont` gone, every other binder in place and the conclusion byte-identical.
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

/-! ## The closing coarsening of Step 3, at the honest Step-2 rate -/

/-- The scale relations behind the closing coarsening: `ℓ ≥ 1`, `h ≥ 1`,
`m ≤ 4ℓ`, `m − ℓ ≤ 2h` and `h ≤ 2ℓ`.  The last three use the pigeonhole
comparability `2h ≤ m`. -/
private theorem scaleFactsMB (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (hPigeon : 2 * S.h ≤ S.m) :
    1 ≤ S.ell ∧ 1 ≤ S.h ∧ S.m ≤ 4 * S.ell ∧ S.m - S.ell ≤ 2 * S.h ∧
      S.h ≤ 2 * S.ell := by
  have h1 := hSorder.m_lt
  have h2 := hSorder.n_lt_ell
  have h3 := hSorder.ell_lt_ellPrime
  have h4 := hSorder.ellPrime_lt_m
  have e1 := S.ellPrime_add_h
  have e2 := S.ell_add_a
  have e3 := S.n_add_a
  have hp := hPigeon
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The closing coarsening of Step 3** at the honest Step-2 rate and with the
window factor: `√(1+2h) ≤ 2h`, `(ℓm(m−ℓ)²)^{1/2} ≤ 4ℓh` and `h ≤ 2ℓ` give
`8ℓh² ≤ 16ℓ²h`, so the window factor costs nothing in `e.RHS.term1`. -/
private theorem coarsenSumMB {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (hPigeon : 2 * S.h ≤ S.m)
    {C1 C2 A3 B3 : ℝ} (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hA30 : 0 ≤ A3)
    (hB30 : 0 ≤ B3) :
    C1 * nu ^ (-((3 : ℝ) / 2)) * ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) * A3 +
        C2 * Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
          Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
            ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) * B3 ≤
      max C1 (16 * C2) * nu ^ (-(3 : ℝ)) *
        ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) * (A3 + B3) := by
  obtain ⟨hl1, hh1, hm4, hmsub, hh2l⟩ := scaleFactsMB S hSorder hPigeon
  have hlR : (1 : ℝ) ≤ (S.ell : ℝ) := Nat.one_le_cast.2 hl1
  have hhR : (1 : ℝ) ≤ (S.h : ℝ) := Nat.one_le_cast.2 hh1
  have hmR : ((S.m : ℕ) : ℝ) ≤ 4 * ((S.ell : ℕ) : ℝ) := by exact_mod_cast hm4
  have hDR : (((S.m - S.ell : ℕ) : ℝ)) ≤ 2 * ((S.h : ℕ) : ℝ) := by exact_mod_cast hmsub
  have hh2lR : ((S.h : ℕ) : ℝ) ≤ 2 * ((S.ell : ℕ) : ℝ) := by exact_mod_cast hh2l
  have hD0 : (0 : ℝ) ≤ ((S.m - S.ell : ℕ) : ℝ) := Nat.cast_nonneg _
  have hanti := Real.antitone_rpow_of_base_le_one hnu hnu1
  have hnu3 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have hC10 : (0 : ℝ) ≤ C1 := le_trans zero_le_one hC1
  have hC20 : (0 : ℝ) ≤ C2 := le_trans zero_le_one hC2
  set Y : ℝ := nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) with hY
  have hY0 : (0 : ℝ) ≤ Y := by rw [hY]; positivity
  -- the first rate
  have hrate1 : nu ^ (-((3 : ℝ) / 2)) * ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) ≤ Y := by
    have hlsq : (S.ell : ℝ) ≤ (S.ell : ℝ) ^ (2 : ℕ) := by nlinarith only [hlR]
    have hsqrth : (S.h : ℝ) ^ ((1 : ℝ) / 2) ≤ (S.h : ℝ) := by
      calc (S.h : ℝ) ^ ((1 : ℝ) / 2) ≤ (S.h : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hhR (by norm_num)
        _ = (S.h : ℝ) := Real.rpow_one _
    rw [hY]
    exact mul_le_mul_of_nonneg (hanti (by norm_num))
      (mul_le_mul_of_nonneg hlsq hsqrth (by linarith only [hlR])
        (by linarith only [hhR])) (Real.rpow_nonneg (le_of_lt hnu) _) (by positivity)
  -- the second rate
  have hwin : Real.sqrt (1 + 2 * (S.h : ℝ)) ≤ 2 * (S.h : ℝ) := by
    have hsq : 1 + 2 * (S.h : ℝ) ≤ (2 * (S.h : ℝ)) ^ (2 : ℕ) := by
      nlinarith only [hhR]
    calc Real.sqrt (1 + 2 * (S.h : ℝ)) ≤ Real.sqrt ((2 * (S.h : ℝ)) ^ (2 : ℕ)) :=
          Real.sqrt_le_sqrt hsq
      _ = 2 * (S.h : ℝ) := Real.sqrt_sq (by linarith only [hhR])
  have hsize : Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
      ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 4 * (S.ell : ℝ) * (S.h : ℝ) := by
    have h1 : (S.ell : ℝ) * (S.m : ℝ) ≤ (S.ell : ℝ) * (4 * (S.ell : ℝ)) :=
      mul_le_mul_of_nonneg_left hmR (by linarith only [hlR])
    have h2 : ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ) ≤ (2 * (S.h : ℝ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hD0 hDR 2
    have h3 : (S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ) ≤
        ((S.ell : ℝ) * (4 * (S.ell : ℝ))) * ((2 * (S.h : ℝ)) ^ (2 : ℕ)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : ((S.ell : ℝ) * (4 * (S.ell : ℝ))) * ((2 * (S.h : ℝ)) ^ (2 : ℕ)) =
        (4 * (S.ell : ℝ) * (S.h : ℝ)) ^ (2 : ℕ) := by ring
    calc Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ Real.sqrt ((4 * (S.ell : ℝ) * (S.h : ℝ)) ^ (2 : ℕ)) := by
          rw [← h4]; exact Real.sqrt_le_sqrt h3
      _ = 4 * (S.ell : ℝ) * (S.h : ℝ) := Real.sqrt_sq (by positivity)
  have hrate2 : Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
      Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
        ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 16 * Y := by
    have hprod : Real.sqrt (1 + 2 * (S.h : ℝ)) *
        Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
          ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) ≤
        16 * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) := by
      have hstep : Real.sqrt (1 + 2 * (S.h : ℝ)) *
          Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
            ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) ≤
          (2 * (S.h : ℝ)) * (4 * (S.ell : ℝ) * (S.h : ℝ)) :=
        mul_le_mul hwin hsize (Real.sqrt_nonneg _) (by positivity)
      have hfin : (2 * (S.h : ℝ)) * (4 * (S.ell : ℝ) * (S.h : ℝ)) ≤
          16 * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) := by
        have hnn : (0 : ℝ) ≤ 8 * (S.ell : ℝ) * (S.h : ℝ) := by positivity
        have hdiff : (0 : ℝ) ≤ 2 * (S.ell : ℝ) - (S.h : ℝ) := by
          linarith only [hh2lR]
        have hmul := mul_nonneg hnn hdiff
        nlinarith only [hmul]
      linarith only [hstep, hfin]
    have hnu13 : nu ^ (-(1 : ℝ)) ≤ nu ^ (-(3 : ℝ)) := hanti (by norm_num)
    have hnu10 : (0 : ℝ) ≤ nu ^ (-(1 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
    have hsz0 : (0 : ℝ) ≤ Real.sqrt (1 + 2 * (S.h : ℝ)) *
        Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
          ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) := by positivity
    calc Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
          Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ))
        = nu ^ (-(1 : ℝ)) * (Real.sqrt (1 + 2 * (S.h : ℝ)) *
            Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
              ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ))) := by ring
      _ ≤ nu ^ (-(3 : ℝ)) * (16 * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ))) :=
          mul_le_mul hnu13 hprod hsz0 hnu3
      _ = 16 * Y := by rw [hY]; ring
  -- assembling
  have hK1 : C1 ≤ max C1 (16 * C2) := le_max_left _ _
  have hK2 : 16 * C2 ≤ max C1 (16 * C2) := le_max_right _ _
  have hfirst : C1 * nu ^ (-((3 : ℝ) / 2)) *
      ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) * A3 ≤
      max C1 (16 * C2) * Y * A3 := by
    have h1 : C1 * (nu ^ (-((3 : ℝ) / 2)) *
        ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ≤ C1 * Y :=
      mul_le_mul_of_nonneg_left hrate1 hC10
    have h2 : C1 * Y ≤ max C1 (16 * C2) * Y := mul_le_mul_of_nonneg_right hK1 hY0
    have h3 := mul_le_mul_of_nonneg_right (le_trans h1 h2) hA30
    calc C1 * nu ^ (-((3 : ℝ) / 2)) * ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) * A3
        = C1 * (nu ^ (-((3 : ℝ) / 2)) *
            ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) * A3 := by ring
      _ ≤ max C1 (16 * C2) * Y * A3 := h3
  have hsecond : C2 * Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
      Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
        ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) * B3 ≤
      max C1 (16 * C2) * Y * B3 := by
    have h1 : C2 * (Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
        Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
          ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ))) ≤ C2 * (16 * Y) :=
      mul_le_mul_of_nonneg_left hrate2 hC20
    have h2 : C2 * (16 * Y) ≤ max C1 (16 * C2) * Y := by
      have := mul_le_mul_of_nonneg_right hK2 hY0
      calc C2 * (16 * Y) = 16 * C2 * Y := by ring
        _ ≤ max C1 (16 * C2) * Y := this
    have h3 := mul_le_mul_of_nonneg_right (le_trans h1 h2) hB30
    calc C2 * Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
          Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
            ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) * B3
        = C2 * (Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
            Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) *
              ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ))) * B3 := by ring
      _ ≤ max C1 (16 * C2) * Y * B3 := h3
  have hexpand : max C1 (16 * C2) * Y * (A3 + B3) =
      max C1 (16 * C2) * Y * A3 + max C1 (16 * C2) * Y * B3 := by ring
  have hgoal : max C1 (16 * C2) * nu ^ (-(3 : ℝ)) *
      ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) * (A3 + B3) =
      max C1 (16 * C2) * Y * (A3 + B3) := by rw [hY]; ring
  rw [hgoal]
  linarith only [hfirst, hsecond, hexpand]

/-! ## `e.RHS.term1` from the anchors, with no continuity hypothesis -/

/-- **`l.RHS.term1` from the anchors, with the constant quantified first and no
continuity hypothesis**:
`|E[⨍_{cu_m} ∇w·(a_ℓ∇u_n − q)]| ≤ C ν^{-3} ℓ² h (3^{-(ℓ-n)/2} + 3^{-(ℓ'-ℓ)})`.

This is the earlier assembly of `l.RHS.term1` from the anchors with its
binder `_hCont` **gone**: the third display of Step 2 is taken from
`hminus_second_moment_memLp`, which reads the multiscale line of the paper in
its `L̲²` form.  That matters because the centred glued flux is
genuinely discontinuous, so the version with `_hCont` could not be instantiated
at the glued field and this one can.  Every other binder is byte-identical, in
the same order, and **the conclusion is byte-identical**.

Discharged here: both step displays (the second at the corrected rate),
`e.nablaw.Lt` (from `l_w_basic_regbounds_window`), the localization
line (from `localization_bridge`), the energy line, the `L̲²` membership of the
centred glued flux, the duality display, and the multiscale line for an `L̲²`
field.  Carried: the clause `_hLocMin` of
`Frozen.Section2.cutoff_localization` in its stated shape, the two annealed
essential-supremum measurability binders, `_hJensen`, `_hQTilde`,
`_hConcDepth`, and the annealed measurability side conditions. -/
theorem l_RHS_term1_of_anchors_constFirst_memLp (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (Cloc : ℝ) (hCloc : 1 ≤ Cloc) (Cc : ℝ) (hCc : 1 ≤ Cc) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hPigeon : 2 * S.h ≤ S.m)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega))
        (HD : ∀ omega : ShellSeq d,
          HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
            (w omega).toH1Function)
        (_hMeasHess : ∀ omega : ShellSeq d,
          AEStronglyMeasurable (fun x : Vec d =>
              HilbertMat.ofMat (fun i j => (HD omega).hess i j x))
            (normalizedCubeMeasure (originCube d (S.m : ℤ))))
        (uNGlued uTildeGlued : ShellSeq d → Vec d → Vec d) (q qTilde : Vec d)
        (_hMeasGradW : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad)
          P.toMeasure)
        (_hMeasFlux : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued omega x - uTildeGlued omega x))) P.toMeasure)
        (_hMeasH1 : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeH1ENorm (originCube d (S.m : ℤ)) (w omega).toH1Function.grad
            (fun x => fun i j => (HD omega).hess i j x)) P.toMeasure)
        (_hMeasHminus : AEMeasurable (fun omega : ShellSeq d =>
          vecHatNegENormOrderOne (originCube d (S.m : ℤ))
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x) - qTilde)) P.toMeasure)
        (_hMeasDepth : ∀ j : ℕ, AEMeasurable (fun omega : ShellSeq d =>
          ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x) - qTilde))) P.toMeasure)
        (_hMeasL2 : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x) - qTilde)) P.toMeasure)
        (_hMeasStep2 : AEMeasurable (fun omega : ShellSeq d =>
          ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x) - qTilde))|) P.toMeasure)
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
        (_hMeasCoeff : Measurable fun omega : ShellSeq d =>
          coeffCubeLinftyENorm nu S.ell S.ell omega)
        (_hMeasDeriv : Measurable fun omega : ShellSeq d =>
          shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega)
        (_hJensen : ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q))) ≤
          (∫⁻ omega : ShellSeq d,
              (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uNGlued omega x - uTildeGlued omega x))) ^ (2 : ℕ)
            ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
        (_hQTilde : ENNReal.ofReal (Real.sqrt (vecNormSq qTilde)) ≤
          (∫⁻ omega : ShellSeq d,
              (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x))) ^ (2 : ℕ)
            ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
        (_hConcDepth : ∀ j : ℕ,
          (∫⁻ omega : ShellSeq d,
              ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x) - qTilde)) ∂P.toMeasure : ℝ≥0∞) ≤
            ENNReal.ofReal (Cc *
                (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
              (∫⁻ omega : ShellSeq d,
                  ENNReal.ofReal (vecSqAvg (originCube d (S.m : ℤ))
                    (fun x => matVecMul
                      ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (uTildeGlued omega x) - qTilde)) ∂P.toMeasure : ℝ≥0∞))
        (_huN : uNGlued = gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e))
        (_huT : uTildeGlued = gluedGradientField hnu S.ell S.n S.m
          (fluxSlot nu S.LPrime P S.n e)),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                    (uNGlued omega x) -
                  q)) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
            ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) := by
  obtain ⟨Creg, hCreg, hreg⟩ := l_w_basic_regbounds_window d hd
  refine ⟨termOneAnchorsConst d Cloc Cc Creg, le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hPigeon e he p hp w hw
    HD hMeasHess uNGlued uTildeGlued q qTilde hMeasGradW hMeasFlux hMeasH1
    hMeasHminus hMeasDepth hMeasL2 hMeasStep2 hLocMin hMeasCoeff hMeasDeriv
    hJensen hQTilde hConcDepth huN huT
  have hregA := hreg nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
  have hGradWL2 := gradW_l2_second_moment_explicit hnu hPrefix hJ2 hJ3 hJ4 S
    hSorder e he p hp w Creg hCreg hregA.1
  have hH1Sq := h1_second_moment_explicit hnu hPrefix hJ2 hJ3 hJ4 S e he p hp w HD
    hMeasHess hMeasGradW (gradWL2ConstFirst Creg) (one_le_gradWL2ConstFirst Creg)
    hGradWL2 Creg hCreg (hregA.2.1 HD)
  subst huN
  subst huT
  set uNGlued : ShellSeq d → Vec d → Vec d :=
    gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) with huNs
  set uTildeGlued : ShellSeq d → Vec d → Vec d :=
    gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) with huTs
  set C4 : ℝ := h1SecondMomentConstFirst (gradWL2ConstFirst Creg) Creg with hC4def
  set C5 : ℝ := hminusSecondMomentConstFirst d Cc with hC5def
  have hC4 : (1 : ℝ) ≤ C4 := one_le_h1SecondMomentConstFirst _ _
  have hC5 : (1 : ℝ) ≤ C5 := one_le_hminusSecondMomentConstFirst d Cc
  have hMemLp : ∀ omega : ShellSeq d,
      MemLp (hilbertifyVecField (fun x =>
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde)) 2
        (normalizedCubeMeasure (originCube d (S.m : ℤ))) := fun omega =>
    Section2.Norms.memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_sub_const qTilde
        (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
          (originCube d (S.m : ℤ))
          (memVectorL2_gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))))
  have hHminusSq := hminus_second_moment_memLp hd hnu hnu1 hPrefix hJ2 hJ3 hJ4 S
    hSorder e _ qTilde hMemLp huTs hQTilde hMeasDepth hMeasL2 Cc hCc
    hConcDepth
  have hStep2 : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x) - qTilde))| ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.sqrt (C4 * C5) * Real.sqrt (1 + 2 * (S.h : ℝ)) *
        nu ^ (-(1 : ℝ)) *
        Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) *
        (3 : ℝ) ^ (-((S.ellPrime : ℝ) - (S.ell : ℝ)))) := by
    have hC40 : (0 : ℝ) ≤ C4 := le_trans zero_le_one hC4
    have hC50 : (0 : ℝ) ≤ C5 := le_trans zero_le_one hC5
    have hpn0 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg _
    have hps : vecNormSq p * vecNormSq (fluxSlot nu S.LPrime P S.n e) = 1 := by
      have hpos := sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
      rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he,
        vecNormSq_fluxSlot hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
      exact mul_inv_cancel₀ hpos.ne'
    have hmm : (S.m : ℝ) = (S.ellPrime : ℝ) + (S.h : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) S.ellPrime_add_h.symm
    set N : ShellSeq d → ℝ≥0∞ := fun omega =>
      vecHatNegENormOrderOne (originCube d (S.m : ℤ))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (uTildeGlued omega x) - qTilde) with hN
    set G : ShellSeq d → ℝ≥0∞ := fun omega =>
      ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) *
        vecCubeH1ENorm (originCube d (S.m : ℤ)) (w omega).toH1Function.grad
          (fun x => fun i j => (HD omega).hess i j x) with hG
    have hDuality := duality_bridge (d := d) nu S w HD uTildeGlued qTilde _ rfl hMemLp
    have hG2 : (∫⁻ omega : ShellSeq d, G omega ^ (2 : ℕ) ∂P.toMeasure) ^
        ((1 : ℝ) / 2) ≤
        ENNReal.ofReal (Real.sqrt (C4 * (1 + 2 * (S.h : ℝ)) *
          (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p)) := by
      refine rpowHalfOfRealCF ?_ hH1Sq
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (S.h : ℝ)) := Real.rpow_nonneg (by norm_num) _
      have hh0 : (0 : ℝ) ≤ (S.h : ℝ) := Nat.cast_nonneg _
      positivity
    have hN2 : (∫⁻ omega : ShellSeq d, N omega ^ (2 : ℕ) ∂P.toMeasure) ^
        ((1 : ℝ) / 2) ≤
        ENNReal.ofReal (Real.sqrt (C5 * nu ^ (-(2 : ℝ)) *
          ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) *
          (3 : ℝ) ^ (2 * (S.ell : ℝ) - 2 * (S.m : ℝ)) *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))) := by
      refine rpowHalfOfRealCF ?_ hHminusSq
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (S.ell : ℝ) - 2 * (S.m : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hnu2 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
      have hsig0 : (0 : ℝ) ≤ vecNormSq (fluxSlot nu S.LPrime P S.n e) :=
        vecNormSq_nonneg _
      positivity
    have harith := step2ArithCF hnu C4 C5 (1 + 2 * (S.h : ℝ))
      ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) (S.h : ℝ)
      (S.ell : ℝ) (S.ellPrime : ℝ) (S.m : ℝ) (vecNormSq p)
      (vecNormSq (fluxSlot nu S.LPrime P S.n e)) hC40 hC50
      (by have : (0 : ℝ) ≤ (S.h : ℝ) := Nat.cast_nonneg _; linarith only [this])
      (by positivity) hpn0 hps hmm
    calc (∫⁻ omega : ShellSeq d,
          ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x) - qTilde))| ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d, G omega * N omega ∂P.toMeasure :=
          lintegral_mono hDuality
      _ ≤ (∫⁻ omega : ShellSeq d, G omega ^ (2 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
            (∫⁻ omega : ShellSeq d, N omega ^ (2 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2) :=
          lintegral_mul_le_rpow_half_mul_rpow_half P G N
            (hMeasH1.const_mul (ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))))) hMeasHminus
      _ ≤ ENNReal.ofReal (Real.sqrt (C4 * (1 + 2 * (S.h : ℝ)) *
              (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p)) *
            ENNReal.ofReal (Real.sqrt (C5 * nu ^ (-(2 : ℝ)) *
              ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) *
              (3 : ℝ) ^ (2 * (S.ell : ℝ) - 2 * (S.m : ℝ)) *
              vecNormSq (fluxSlot nu S.LPrime P S.n e))) := mul_le_mul' hG2 hN2
      _ = ENNReal.ofReal (Real.sqrt (C4 * (1 + 2 * (S.h : ℝ)) *
              (3 : ℝ) ^ (2 * (S.h : ℝ)) * vecNormSq p) *
            Real.sqrt (C5 * nu ^ (-(2 : ℝ)) *
              ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) *
              (3 : ℝ) ^ (2 * (S.ell : ℝ) - 2 * (S.m : ℝ)) *
              vecNormSq (fluxSlot nu S.LPrime P S.n e))) :=
          (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
      _ = ENNReal.ofReal (Real.sqrt (C4 * C5) * Real.sqrt (1 + 2 * (S.h : ℝ)) *
            nu ^ (-(1 : ℝ)) *
            Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((S.ellPrime : ℝ) - (S.ell : ℝ)))) :=
          congrArg ENNReal.ofReal harith
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  have hlm : S.ell ≤ S.m :=
    le_of_lt (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m)
  have hloc := localization_bridge d hnu hPrefix hJ2 S hSorder e
    (le_trans zero_le_one hCloc) hLocMin hMeasCoeff hMeasDeriv
  have hfluxM := flux_l2_second_moment_explicit hnu hnu1 hPrefix hJ2 hJ3 hJ4 S
    hSorder e _ _ S.m Cloc hCloc (hloc S.m (le_trans hnl hlm) (le_refl S.m))
  have hfluxL := flux_l2_second_moment_explicit hnu hnu1 hPrefix hJ2 hJ3 hJ4 S
    hSorder e _ _ S.ell Cloc hCloc (hloc S.ell hnl hlm)
  have hStep1 := decompose_flux_first_explicit hnu hPrefix hJ2 hJ3 hJ4 S e he p hp
    w _ _ q qTilde hMeasGradW hMeasFlux (fluxL2ConstFirst d Cloc)
    (one_le_fluxL2ConstFirst d Cloc) hfluxM
    (qDiff_sq_explicit hnu S e _ _ q qTilde (fluxL2ConstFirst d Cloc)
      (le_trans zero_le_one (one_le_fluxL2ConstFirst d Cloc)) hJensen hfluxL)
    (gradWL2ConstFirst Creg) (one_le_gradWL2ConstFirst Creg) hGradWL2
  have hFluxN : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x)) := fun omega =>
    memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
      (originCube d (S.m : ℤ))
      (memVectorL2_gluedGradientField hnu S.LPrime S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))
  have hFluxTilde : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x)) := fun omega =>
    memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
      (originCube d (S.m : ℤ))
      (memVectorL2_gluedGradientField hnu S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))
  set C1 : ℝ := Real.sqrt (8 * (gradWL2ConstFirst Creg * fluxL2ConstFirst d Cloc))
    with hC1def
  set C2 : ℝ := Real.sqrt (C4 * C5) with hC2def
  have hC1 : (1 : ℝ) ≤ C1 := one_le_stepOneConstFirst d Cloc Creg
  have hC2 : (1 : ℝ) ≤ C2 := one_le_stepTwoConstFirst d Cc Creg
  have hC : max C1 (16 * C2) ≤ termOneAnchorsConst d Cloc Cc Creg := le_max_right _ _
  have hcast : -((S.ellPrime : ℝ) - (S.ell : ℝ)) =
      -((S.ellPrime - S.ell : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hSorder.ell_lt_ellPrime)]
  rw [hcast] at hStep2
  have hC10 : (0 : ℝ) ≤ C1 := le_trans zero_le_one hC1
  have hC20 : (0 : ℝ) ≤ C2 := le_trans zero_le_one hC2
  have hA30 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) :=
    Real.rpow_nonneg (by norm_num) _
  have hB30 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  set a1 : ℝ := C1 * nu ^ (-((3 : ℝ) / 2)) *
    ((S.ell : ℝ) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) *
    (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) with ha1
  set a2 : ℝ := C2 * Real.sqrt (1 + 2 * (S.h : ℝ)) * nu ^ (-(1 : ℝ)) *
    Real.sqrt ((S.ell : ℝ) * (S.m : ℝ) * ((S.m - S.ell : ℕ) : ℝ) ^ (2 : ℕ)) *
    (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ)) with ha2
  have hnu32 : (0 : ℝ) ≤ nu ^ (-((3 : ℝ) / 2)) := Real.rpow_nonneg (le_of_lt hnu) _
  have hnu1' : (0 : ℝ) ≤ nu ^ (-(1 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have hhalf : (0 : ℝ) ≤ (S.h : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ha10 : (0 : ℝ) ≤ a1 := by rw [ha1]; positivity
  have ha20 : (0 : ℝ) ≤ a2 := by rw [ha2]; positivity
  have hptr : ∀ omega : ShellSeq d,
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued omega x) - q))| ≤
        ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uTildeGlued omega x) - qTilde))| +
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (w omega).toH1Function.grad *
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uNGlued omega x - uTildeGlued omega x)) +
              ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q)))) := fun omega =>
    ofReal_abs_volumeAverage_flux_le (originCube d (S.m : ℤ))
      ((coefficientCutoff nu omega S.ell).toCoeffField)
      ((w omega).toH1Function.grad) (uNGlued omega) (uTildeGlued omega) q qTilde
      (w omega).toH1Function.grad_memVectorL2 (hFluxN omega) (hFluxTilde omega)
  have hbig : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x) - q))| ∂P.toMeasure) ≤
      ENNReal.ofReal (a1 + a2) := by
    calc (∫⁻ omega : ShellSeq d,
        ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued omega x) - q))| ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d,
            (ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
                (fun x => vecDot ((w omega).toH1Function.grad x)
                  (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                    (uTildeGlued omega x) - qTilde))| +
              vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                  (w omega).toH1Function.grad *
                (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                    (fun x => matVecMul
                      ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (uNGlued omega x - uTildeGlued omega x)) +
                  ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q)))))
            ∂P.toMeasure := lintegral_mono hptr
      _ = (∫⁻ omega : ShellSeq d,
            ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uTildeGlued omega x) - qTilde))| ∂P.toMeasure) +
          ∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (w omega).toH1Function.grad *
              (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                  (fun x => matVecMul
                    ((coefficientCutoff nu omega S.ell).toCoeffField x)
                    (uNGlued omega x - uTildeGlued omega x)) +
                ENNReal.ofReal (Real.sqrt (vecNormSq (qTilde - q))))
            ∂P.toMeasure := lintegral_add_left' hMeasStep2 _
      _ ≤ ENNReal.ofReal a2 + ENNReal.ofReal a1 := add_le_add hStep2 hStep1
      _ = ENNReal.ofReal (a1 + a2) := by
          rw [← ENNReal.ofReal_add ha20 ha10, add_comm a2 a1]
  have hnu3 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
  have hlh : (0 : ℝ) ≤ (S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ) := by positivity
  have hAB : (0 : ℝ) ≤ (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
      (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ)) := by
    linarith only [hA30, hB30]
  calc |∫ omega : ShellSeq d,
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued omega x) - q)) ∂P.toMeasure|
      ≤ (∫⁻ omega : ShellSeq d,
          ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uNGlued omega x) - q))| ∂P.toMeasure).toReal :=
        abs_integral_le_toReal_lintegral_abs
    _ ≤ (ENNReal.ofReal (a1 + a2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbig
    _ = a1 + a2 := ENNReal.toReal_ofReal (by linarith only [ha10, ha20])
    _ ≤ max C1 (16 * C2) * nu ^ (-(3 : ℝ)) *
          ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
          ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
            (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) := by
        rw [ha1, ha2]
        exact coarsenSumMB hnu hnu1 S hSorder hPigeon hC1 hC2 hA30 hB30
    _ ≤ termOneAnchorsConst d Cloc Cc Creg * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
          ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
            (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC hnu3) hlh) hAB

end

end SuperdiffusionCLT.Section3.Terms
