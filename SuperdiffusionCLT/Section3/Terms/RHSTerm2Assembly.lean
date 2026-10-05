/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RField
public import SuperdiffusionCLT.Section3.Terms.GluedFieldAnnealedFiniteness
public import SuperdiffusionCLT.Section3.Terms.GluedFieldDifferenceMeasurable
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RemainingObligations
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2KmnBounds

/-!
# `l.RHS.term2` reduced to its residue

The display `SuperdiffusionCLT.Frozen.Section3.rhs_term2` follows from seven
ingredients: the regularity, finiteness, measurability and bounds of the response flux
`R = (k_{L'} − k_ℓ)ᵗ ∇w`; the proxy-error display; the proxy-energy display; the finiteness and
the measurability of the annealed squared norms of the proxy fields; the integrability of the
three pairing integrals; and the measurability of the cube mean of `R`.  This module
discharges every ingredient whose proof produces its display at a constant that is independent
of the data, and states the result as `term2_of_residue`, whose binders after those of the
statement are exactly the residue.

## Why the two displays are restated here

The proofs of the proxy-error and proxy-energy displays produce them in the shape
`∃ C, 1 ≤ C ∧ …`, with the witness a function of the data (for the proxy-error
display, of the localization constant and the annealed measures).  The chain
`l_RHS_term2_of_anchors_proxyMeasurable` consumes the two displays at
*fixed* constants `C₂ C₃`, because its own constant is a function of them
(`RHSTerm2Glued.termTwoConst`); a per-instance existential over `C₂ C₃` would
not produce one shared `C` for the display.  An existential witness is
opaque, so it cannot be pinned to a literal.  `term2_ob2_at` and
`term2_ob3_at` below are therefore the two displays at the literal constants
`2 * Cloc` and `3` — the constants their own proofs produce — with
those proofs reproduced verbatim.

## The residue

After the statement's own binders and the two localization clauses
`hLocM` and `hLocN` of the proxy-error display, the residue carried by `term2_of_residue` is:
the finiteness of the annealed squared norm of `R = (k_{L'} − k_ℓ)∇w`; for a weak gradient `DR`
of `R`, the finiteness and the measurability of the annealed squared norm of `DR`; the display
`e.RHS.term2.R.bounds` at `C₁`; and the proxy-mean control `hPtilde` of
`e.RHS.term2.proxy.energy`.  These are the only ingredients not discharged here;
the localization clauses are the third conjunct of the localization statement in
`Section2/Localization/CutoffMinimizerClause.lean`, whose form there is
conditional.  The display `e.RHS.term2.R.bounds` has the shape
`∃ C, 1 ≤ C ∧ …`, whose witness is again opaque and hence cannot be pinned to
the fixed `C₁` that the chain consumes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Norms
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

/-! ## The proxy-error display at a fixed constant -/

/-- **The proxy-error display in the reduction of `l.RHS.term2`, at the fixed constant
`2 * Cloc`**: the display `e.RHS.term2.proxy.error` at the cutoff-`ℓ`
proxy field, its annealed mean and the cutoff-`L'` field `∇u_n`.

This is the content of the proxy-error display — whose proof produces
the witness `2 * Cloc` — displayed non-existentially at that witness, in the
shape in which the chain consumes it.  The mean-defect identity `hAvg`, the
`L̲²` typing `hL2n` and the componentwise integrability `hIntN` of
the display `e.RHS.term2.proxy.error` are discharged as in its proof; the
finiteness `hfinN` of the same display is obtained from the finiteness of the annealed
proxy norms (`term2_ob4_finite`, the finiteness at the large cube `cu_m`) transported to
the cube `cu_n` by the sub-cube domination
`RHSTerm2AnchorsConstFirst.vecCubeLpENorm_subcube_sq_le`, instead of from a
uniform-domination route. -/
theorem term2_ob2_at (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d)
    (Cloc : ℝ)
    (hLocM : (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x -
                gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
        Cloc * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
          (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹)
    (hLocN : (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.n : ℤ)) 2
              (fun x => gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
        Cloc * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
          (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) :
    (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x -
                gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
        Real.sqrt (vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) - testVector nu S.LPrime P S.n e)) ≤
      (2 * Cloc) * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
        (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ := by
  classical
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hF
  set Q : TriadicCube d := originCube d (S.n : ℤ) with hQ
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  obtain ⟨hfinDiff, -⟩ := term2_ob4_finite (d := d) hnu P S hSorder e
  -- the finiteness clause `hfinN` of the display, at the cube `cu_n`, from the finiteness at `cu_m`
  have hfinSwap : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := by
    have heq : (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
              gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)) =
        (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
              gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)) := by
      funext omega
      rw [show (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
            gluedGradientField hnu S.LPrime S.n S.m F omega x) =
          fun x => -(gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x) from by
        funext x
        rw [neg_sub],
        vecCubeLpENorm_neg]
    intro h
    exact hfinDiff (by rw [← heq]; exact h)
  have hfinN : (∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2
      (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
        gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := by
    have hz : Q ∈ largeCubeSubcubes d S.n S.m := by
      rw [hQ]
      exact originCube_mem_largeCubeSubcubes hnm
    have hpt : ∀ omega : ShellSeq d, vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ) ≤
        ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)) *
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
              gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ) :=
      fun omega => vecCubeLpENorm_subcube_sq_le hz _
    have hcm : (∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)) *
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
                gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
          ∂P.toMeasure) =
        ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)) *
          (∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
                gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
            ∂P.toMeasure) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hlt : (∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
          ∂P.toMeasure) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono hpt) ?_
      rw [hcm]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfinSwap)
    exact ne_top_of_lt hlt
  -- the `L̲²` typing `hL2n`
  have hL2n : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q)
      (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
        gluedGradientField hnu S.LPrime S.n S.m F omega x) :=
    fun omega => (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q).sub
      (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q)
  -- the componentwise integrability `hIntN` of the cube averages
  have hIntN : ∀ i : Fin d, MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) i) P.toMeasure := by
    have hT : MeasureTheory.Integrable (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet Q)
          (gluedGradientField hnu S.ell S.n S.m F omega)) P.toMeasure :=
      integrable_annealedGluedAverage hnu S.ell S.n S.m hnm F hPrefix hJ2 hJ3 hJ4
    have hN : MeasureTheory.Integrable (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet Q)
          (gluedGradientField hnu S.LPrime S.n S.m F omega)) P.toMeasure :=
      integrable_annealedGluedAverage hnu S.LPrime S.n S.m hnm F hPrefix hJ2 hJ3 hJ4
    have hsub : MeasureTheory.Integrable (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet Q)
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
            gluedGradientField hnu S.LPrime S.n S.m F omega x)) P.toMeasure :=
      (hT.sub hN).congr (Filter.Eventually.of_forall fun omega => by
        have hxT : ∀ i : Fin d, MeasureTheory.Integrable
            (fun x : Vec d => gluedGradientField hnu S.ell S.n S.m F omega x i)
            (MeasureTheory.volume.restrict (openCubeSet Q)) :=
          fun i => integrable_component_gluedGradientField hnu S.ell S.n S.m F omega Q i
        have hxN : ∀ i : Fin d, MeasureTheory.Integrable
            (fun x : Vec d => gluedGradientField hnu S.LPrime S.n S.m F omega x i)
            (MeasureTheory.volume.restrict (openCubeSet Q)) :=
          fun i => integrable_component_gluedGradientField hnu S.LPrime S.n S.m F omega Q i
        show volumeAverageVec (openCubeSet Q)
              (gluedGradientField hnu S.ell S.n S.m F omega) -
            volumeAverageVec (openCubeSet Q)
              (gluedGradientField hnu S.LPrime S.n S.m F omega) =
          volumeAverageVec (openCubeSet Q)
            (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
              gluedGradientField hnu S.LPrime S.n S.m F omega x)
        exact (volumeAverageVec_sub hxT hxN).symm)
    intro i
    exact hsub.eval i
  -- the mean-defect identity `hAvg` of the display
  have hAvg : annealedGluedAverage hnu P S.ell S.n S.m F - testVector nu S.LPrime P S.n e =
      ∫ omega : ShellSeq d, volumeAverageVec (openCubeSet Q)
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) ∂P.toMeasure :=
    annealedGluedAverage_sub_testVector_eq d nu hnu hPrefix hJ2 hJ3 hJ4 S e
  -- the body of `e.RHS.term2.proxy.error` at the fixed witness `2 * Cloc`
  have hJen : ENNReal.ofReal (vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m F -
        testVector nu S.LPrime P S.n e)) ≤
      ∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure := by
    rw [hAvg]
    refine le_trans (ofReal_vecNormSq_integral_le hIntN) ?_
    exact lintegral_mono fun omega => ofReal_vecNormSq_volumeAverageVec_le (hL2n omega)
  have hreal : vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m F -
        testVector nu S.LPrime P S.n e) ≤
      (∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinN).1 hJen
  have hPpt : Real.sqrt (vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m F -
        testVector nu S.LPrime P S.n e)) ≤
      (∫⁻ omega : ShellSeq d, vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
          gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hreal
  have hfinal : (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
          ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) +
      Real.sqrt (vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m F -
        testVector nu S.LPrime P S.n e)) ≤
      2 * (Cloc * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
        (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) := by
    linarith only [hLocM, hPpt.trans hLocN]
  refine hfinal.trans (le_of_eq ?_)
  ring

/-! ## Small inequalities used by the proxy-energy display -/

/-- `ℝ≥0∞.ofReal` of a doubled real. -/
private theorem ofReal_two_mul_local (r : ℝ) :
    ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The split of `ℝ≥0∞.ofReal (2a + 2b)` used by the constant-translation bound. -/
private theorem ofReal_two_add_two_local {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (2 * a + 2 * b) =
      2 * ENNReal.ofReal a + ENNReal.ofReal (2 * b) := by
  rw [ENNReal.ofReal_add (mul_nonneg zero_le_two ha) (mul_nonneg zero_le_two hb),
    ofReal_two_mul_local]

/-- A nonnegative square root bound. -/
private theorem real_sqrt_le_of_sq_local {K T : ℝ} (hT : 0 ≤ T) (hle : K ≤ T * T) :
    Real.sqrt K ≤ T := by
  have hsq : K ≤ T ^ 2 := by
    rw [sq]
    exact hle
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq hT)

/-- The squared `L̲²` norm of a field translated by a constant vector is
controlled by the two squared norms.  The pointwise split is the public
`Homogenization.vecNormSq_sub_le`. -/
private theorem vecCubeLpENorm_two_sub_const_sq_local {d : ℕ} (Q : TriadicCube d)
    (F : Vec d → Vec d) (c : Vec d)
    (hF : AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q)) :
    vecCubeLpENorm Q 2 (fun x => F x - c) ^ (2 : ℕ) ≤
      2 * (vecCubeLpENorm Q 2 F) ^ (2 : ℕ) + ENNReal.ofReal (2 * vecNormSq c) := by
  have hsub2 : ∀ x : Vec d,
      vecNormSq (F x - c) ≤ 2 * vecNormSq (F x) + 2 * vecNormSq c := fun x =>
    (vecNormSq_sub_le (F x) c).trans (le_of_eq (mul_add 2 _ _))
  -- Pointwise bound on the squared Euclidean magnitude.
  have hpoint : ∀ x : Vec d,
      ENNReal.ofReal (vecNormSq (F x - c)) ≤
        2 * ENNReal.ofReal (vecNormSq (F x)) + ENNReal.ofReal (2 * vecNormSq c) := by
    intro x
    calc ENNReal.ofReal (vecNormSq (F x - c))
        ≤ ENNReal.ofReal (2 * vecNormSq (F x) + 2 * vecNormSq c) :=
          ENNReal.ofReal_le_ofReal (hsub2 x)
      _ = 2 * ENNReal.ofReal (vecNormSq (F x)) + ENNReal.ofReal (2 * vecNormSq c) :=
          ofReal_two_add_two_local (vecNormSq_nonneg (F x)) (vecNormSq_nonneg c)
  -- Measurability of the scaled squared magnitude of the field.
  have h0 : AEMeasurable (fun x : Vec d => ENNReal.ofReal (vecNormSq (F x)))
      (normalizedCubeMeasure Q) := by
    have h1 : AEMeasurable (fun x : Vec d => ‖hilbertifyVecField F x‖ₑ ^ (2 : ℕ))
        (normalizedCubeMeasure Q) := hF.enorm.pow_const 2
    refine h1.congr ?_
    exact Filter.Eventually.of_forall fun x => by
      show ‖hilbertifyVecField F x‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (vecNormSq (F x))
      show ‖HilbertVec.ofVec (F x)‖ₑ ^ (2 : ℕ) = _
      exact enorm_ofVec_sq (F x)
  have hg2 : AEMeasurable (fun x : Vec d => 2 * ENNReal.ofReal (vecNormSq (F x)))
      (normalizedCubeMeasure Q) := h0.const_mul (2 : ℝ≥0∞)
  -- The normalized cube integral splits.
  have hint : ∫⁻ x : Vec d, ENNReal.ofReal (vecNormSq (F x - c))
        ∂(normalizedCubeMeasure Q) ≤
      2 * ∫⁻ x : Vec d, ENNReal.ofReal (vecNormSq (F x))
          ∂(normalizedCubeMeasure Q) + ENNReal.ofReal (2 * vecNormSq c) := by
    calc ∫⁻ x : Vec d, ENNReal.ofReal (vecNormSq (F x - c)) ∂(normalizedCubeMeasure Q) ≤
        ∫⁻ x : Vec d, (2 * ENNReal.ofReal (vecNormSq (F x)) +
            ENNReal.ofReal (2 * vecNormSq c)) ∂(normalizedCubeMeasure Q) :=
          lintegral_mono (f := fun x : Vec d => ENNReal.ofReal (vecNormSq (F x - c)))
            (g := fun x : Vec d => 2 * ENNReal.ofReal (vecNormSq (F x)) +
              ENNReal.ofReal (2 * vecNormSq c)) (fun x => hpoint x)
      _ = ∫⁻ x : Vec d, 2 * ENNReal.ofReal (vecNormSq (F x)) ∂(normalizedCubeMeasure Q) +
            ∫⁻ x : Vec d, ENNReal.ofReal (2 * vecNormSq c) ∂(normalizedCubeMeasure Q) :=
          lintegral_add_left' hg2 _
      _ = 2 * ∫⁻ x : Vec d, ENNReal.ofReal (vecNormSq (F x)) ∂(normalizedCubeMeasure Q) +
            ENNReal.ofReal (2 * vecNormSq c) := by
          rw [lintegral_const_mul'' (2 : ℝ≥0∞) h0, lintegral_const,
            normalizedCubeMeasure_apply_univ Q, mul_one]
  -- Assemble.
  have hX : (vecCubeLpENorm Q 2 F) ^ (2 : ℕ) =
      ∫⁻ x : Vec d, ENNReal.ofReal (vecNormSq (F x)) ∂(normalizedCubeMeasure Q) := by
    rw [vecCubeLpENorm_two_sq Q F hF]
    exact lintegral_congr fun x => enorm_ofVec_sq (F x)
  calc vecCubeLpENorm Q 2 (fun x => F x - c) ^ (2 : ℕ)
      = ∫⁻ x : Vec d, ENNReal.ofReal (vecNormSq (F x - c))
          ∂(normalizedCubeMeasure Q) := by
        have hrw : hilbertifyVecField (fun x => F x - c) =
            hilbertifyVecField F - hilbertifyVecField (fun _ : Vec d => c) := by
          funext x
          exact map_sub (HilbertVec.linearEquivVec d).symm _ _
        have hFc : AEStronglyMeasurable (hilbertifyVecField (fun x => F x - c))
            (normalizedCubeMeasure Q) := by
          rw [hrw]
          exact hF.sub aestronglyMeasurable_const
        rw [vecCubeLpENorm_two_sq Q _ hFc]
        exact lintegral_congr fun x => enorm_ofVec_sq _
    _ ≤ 2 * ∫⁻ x : Vec d, ENNReal.ofReal (vecNormSq (F x))
          ∂(normalizedCubeMeasure Q) + ENNReal.ofReal (2 * vecNormSq c) := hint
    _ = 2 * (vecCubeLpENorm Q 2 F) ^ (2 : ℕ) + ENNReal.ofReal (2 * vecNormSq c) := by
        rw [hX]

/-! ## The proxy-energy display at a fixed constant -/

/-- **The proxy-energy display in the reduction of `l.RHS.term2`, at the fixed constant `3`**:
the display `e.RHS.term2.proxy.energy` at the cutoff-`ℓ` proxy field
`∇ũ_n = gluedGradientField hnu S.ell S.n S.m F` and its annealed mean
`p̃ = annealedGluedAverage hnu P S.ell S.n S.m F`, with
`F = fluxSlot nu S.LPrime P S.n e`.

This is the content of the proxy-energy display, whose proof
returns the witness `3`;
it is displayed here non-existentially at that witness, in the shape in which
the chain consumes it.  The per-field energy bound is discharged from
`RHSTerm1InputsG.vecCubeLpENorm_two_sq_gluedGradientField_le` at the cube scale
`r = S.m`; the proxy-mean control `hPtilde` is carried. -/
theorem term2_ob3_at (d : ℕ) [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1)
    (hPtilde : vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m
          (fluxSlot nu S.LPrime P S.n e)) ≤
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal) :
    (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x -
                annealedGluedAverage hnu P S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e)) ^
        (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
      3 * nu ^ (-(1 : ℝ)) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ := by
  classical
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hF
  set T : Vec d := annealedGluedAverage hnu P S.ell S.n S.m F with hTvec
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  -- the flux slot has the printed squared amplitude
  have hflux : vecNormSq F = (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ ^ (2 : ℝ) := by
    rw [hF, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, inv_pow,
      sq_sigmaBarStarInvSqrt hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n,
      ← vecNormSq_fluxSlot hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
  have hrpow : nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hnu),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, pow_two, mul_inv]
  have hsinv0 : 0 ≤ (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ :=
    inv_nonneg.2 (Real.sqrt_nonneg _)
  set c : ℝ := 2 * nu ^ (-(2 : ℝ)) *
    ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ ^ (2 : ℝ)) with hcd
  have hc0 : 0 ≤ c := by
    rw [hcd]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hnu.le (-(2 : ℝ))))
      (Real.rpow_nonneg hsinv0 (2 : ℝ))
  -- the measurability and energy clauses of `hEnergy`, at the cutoff-`ℓ` field
  have hmT : ∀ omega : ShellSeq d, AEStronglyMeasurable
      (hilbertifyVecField (fun x => gluedGradientField hnu S.ell S.n S.m F omega x))
      (normalizedCubeMeasure (originCube d (S.m : ℤ))) := fun omega =>
    (memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega
        (originCube d (S.m : ℤ)))).aestronglyMeasurable
  have htildeLe : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ) ≤
        ENNReal.ofReal c := by
    intro omega
    refine (vecCubeLpENorm_two_sq_gluedGradientField_le (k := S.n) (r := S.m) (m := S.m)
      hnu hnm (le_refl S.m) S.ell F omega).trans (ENNReal.ofReal_le_ofReal ?_)
    calc nu⁻¹ * nu⁻¹ * vecNormSq F
        = nu ^ (-(2 : ℝ)) * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ ^ (2 : ℝ)) := by
          rw [hrpow, hflux]
      _ ≤ 2 * (nu ^ (-(2 : ℝ)) *
            ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ ^ (2 : ℝ))) :=
          le_mul_of_one_le_left
            (mul_nonneg (Real.rpow_nonneg hnu.le _) (Real.rpow_nonneg hsinv0 _))
            (by norm_num)
      _ = c := by
          rw [hcd]
          ring
  -- Step 1: the proxy mean is bounded by the same amplitude.
  have hconst : ∀ k : ℝ, ∫⁻ omega : ShellSeq d, ENNReal.ofReal k ∂P.toMeasure =
      ENNReal.ofReal k := fun _ => by
    rw [lintegral_const, measure_univ, mul_one]
  have hint1 : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    rw [← hconst c]
    exact lintegral_mono (μ := P.toMeasure)
      (f := fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ))
      (g := fun _ : ShellSeq d => ENNReal.ofReal c) (fun omega => htildeLe omega)
  have hint1ne : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_lt (lt_of_le_of_lt hint1 ENNReal.ofReal_lt_top)
  have hint1conv : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ≤ c :=
    (ENNReal.le_ofReal_iff_toReal_le hint1ne hc0).1 hint1
  have hpt : vecNormSq T ≤ c := hPtilde.trans hint1conv
  -- Step 2: the pointwise cube-level bound.
  have hpw : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - T) ^ (2 : ℕ) ≤
        ENNReal.ofReal (4 * c) := by
    intro omega
    have h1 : vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - T) ^ (2 : ℕ) ≤
      2 * (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ)
        + ENNReal.ofReal (2 * vecNormSq T) :=
      vecCubeLpENorm_two_sub_const_sq_local (originCube d (S.m : ℤ))
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) T (hmT omega)
    have h2 : 2 * (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ)
        + ENNReal.ofReal (2 * vecNormSq T) ≤ ENNReal.ofReal (4 * c) := by
      refine le_trans (add_le_add (mul_le_mul_of_nonneg_left (htildeLe omega) (by positivity))
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpt zero_le_two))) ?_
      rw [← ofReal_two_add_two_local hc0 hc0]
      exact ENNReal.ofReal_le_ofReal
        (le_of_eq (show (2 : ℝ) * c + 2 * c = 4 * c by ring))
    exact h1.trans h2
  -- Step 3: integrate over the probability measure and take the square root.
  set A : ℝ≥0∞ := ∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - T) ^ (2 : ℕ)
        ∂P.toMeasure with hAdef
  have hAle : A ≤ ENNReal.ofReal (4 * c) := by
    rw [hAdef, ← hconst (4 * c)]
    refine lintegral_mono (μ := P.toMeasure)
      (f := fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => gluedGradientField hnu S.ell S.n S.m F omega x - T) ^ (2 : ℕ))
      (g := fun _ : ShellSeq d => ENNReal.ofReal (4 * c)) ?_
    intro omega
    exact hpw omega
  have hAne : A ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt hAle ENNReal.ofReal_lt_top)
  have hAconv : A.toReal ≤ 4 * c :=
    (ENNReal.le_ofReal_iff_toReal_le hAne (mul_nonneg (by norm_num) hc0)).1 hAle
  have hνsq : nu ^ (-(2 : ℝ)) = (nu⁻¹) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hnu.le,
      Real.rpow_natCast, ← inv_pow]
  have hs2 : ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) ^ ((2 : ℝ))
      = ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) ^ 2 := Real.rpow_natCast _ 2
  have hpos : 0 ≤ (nu⁻¹) ^ 2 * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hinv1 : nu ^ (-(1 : ℝ)) = nu⁻¹ := Real.rpow_neg_one nu
  have hTpos : 0 ≤ 3 * nu⁻¹ * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hnu.le)) hsinv0
  have hsq : 4 * c ≤ (3 * nu⁻¹ * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹)) *
      (3 * nu⁻¹ * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹)) := by
    have hL : 4 * c
        = ((nu⁻¹) ^ 2 * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) ^ 2) * 8 := by
      rw [hcd, hνsq, hs2]
      ring
    have hR : (3 * nu⁻¹ * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹)) *
        (3 * nu⁻¹ * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹))
        = ((nu⁻¹) ^ 2 * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) ^ 2) * 9 := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_left (by norm_num : (8 : ℝ) ≤ 9) hpos
  calc A.toReal ^ ((1 : ℝ) / 2)
      = Real.sqrt A.toReal := by rw [Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (4 * c) := Real.sqrt_le_sqrt hAconv
    _ ≤ 3 * nu⁻¹ * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) :=
        real_sqrt_le_of_sq_local hTpos hsq
    _ = 3 * nu ^ (-(1 : ℝ)) * ((sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) := by
        rw [hinv1]

/-! ## `l.RHS.term2` reduced to its residue -/

/-- **`l.RHS.term2` modulo its residue.**  At every pair of
parameters `C₁ ≥ 1`, `Cloc ≥ 1`, the statement
`SuperdiffusionCLT.Frozen.Section3.rhs_term2` holds modulo the five
residue binders carried after the statement's own, all of them at the
data of the statement:

* `hLocM` — the localization estimate for minimizers on the large cube `cu_m`;
* `hLocN` — the same on `cu_n`, carrying the two annealed means;
* `hfinR` — the finiteness of the annealed squared `L̲²(cu_m)`
  norm of the response flux `R = (k_{L'} − k_ℓ) ∇w`;
* `hRres` — for every weak gradient `DR` of `R`: the finiteness
  of the annealed squared `L̲²(cu_m)` norm of `DR`, the
  measurability of `omega ↦ ‖DR(omega)‖_{L̲²(cu_m)}` and the
  display `e.RHS.term2.R.bounds` at `C₁`;
* `hPtilde` — the proxy-mean control of `e.RHS.term2.proxy.energy`.

Everything else is discharged by the following results: the weak gradient of `R` and the
square-integrability of its Jacobian by `RHSTerm2RField.exists_rfieldWeakJacobian`, the
measurability of `‖R‖` by
`Section3.Setup.aemeasurable_vecCubeLpENorm_matVecMul_coefficientCutoff_sub_grad`,
the proxy-error display by `term2_ob2_at` (at the fixed constant `2 * Cloc`), the proxy-energy
display by `term2_ob3_at` (at `3`), the finiteness of the proxy norms by
`GluedFieldAnnealedFiniteness.term2_ob4_finite`, their measurability by
`GluedFieldDifferenceMeasurable.term2_ob5_measurable`, the integrability of the pairings by
`RHSTerm2RemainingObligations.term2_ob6_int`, and the measurability of the cube mean of `R`
with respect to the high-shell σ-algebra by
`measurable_volumeAverageVec_matVecMul_coefficientCutoff_sub_grad_highShellSigma` of
`Section3.Setup.ResponseMeasurabilityD`. -/
theorem term2_of_residue (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁) (Cloc : ℝ) (hCloc : 1 ≤ Cloc) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)) →
        -- `hLocM`: the localization display at `cu_m`
        ((∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x -
                  gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          Cloc * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
            (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
        -- `hLocN`: the localization display at `cu_n`
        ((∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.n : ℤ)) 2
                (fun x => gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x -
                  gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          Cloc * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
            (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
        -- `hfinR`: finite annealed norm of `R`
        ((∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                    (coefficientCutoff nu omega S.ell).toCoeffField y)
                  ((w omega).toH1Function.grad y)) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) →
        -- `hRres`: finiteness and measurability for `DR` and the bounds at `C₁`, for every `DR`
        (∀ (DR : ShellSeq d → Fin d → Vec d → Vec d),
          (∀ (omega : ShellSeq d) (i : Fin d),
            HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                    (coefficientCutoff nu omega S.ell).toCoeffField x)
                  ((w omega).toH1Function.grad x)) i) (DR omega i)) →
          (∀ omega : ShellSeq d,
            MemLp (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) 2
              (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) →
          ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) ∧
          (AEMeasurable (fun omega : ShellSeq d =>
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => HilbertMat.ofMat (fun i j => DR omega i x j))) P.toMeasure) ∧
          ((∫⁻ omega : ShellSeq d,
                vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                  (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                    ((w omega).toH1Function.grad y)) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
            (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
              (∫⁻ omega : ShellSeq d,
                  SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                      (originCube d (S.m : ℤ)) 2
                      (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^
                (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
            C₁ * ((S.LPrime : ℕ) : ℝ) *
              Real.sqrt (vecNormSq (testVector nu S.LPrime P S.n e)))) →
        -- `hPtilde`: the proxy-mean control of `e.RHS.term2.proxy.energy`
        (vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e)) ≤
          (∫⁻ omega : ShellSeq d,
              vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                (fun x => gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
            ∂P.toMeasure : ℝ≥0∞).toReal) →
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
  obtain ⟨C, hC1, hC⟩ := l_RHS_term2_of_anchors_proxyMeasurable d hd C₁ (2 * Cloc) 3
    hC₁ (by linarith only [hCloc]) (by norm_num)
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hLocM hLocN hfinR hRres hPtilde
  -- the `L²` membership of `R = (k_{L'} − k_ℓ) ∇w` on `cu_m` is available
  have hRL2 : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
            (coefficientCutoff nu omega S.ell).toCoeffField y)
          ((w omega).toH1Function.grad y)) := by
    intro omega
    have hGL2 : MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => (w omega).toH1Function.grad x) :=
      (w omega).toH1Function.grad_memVectorL2
    have hA := memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime
      (originCube d (S.m : ℤ)) hGL2
    have hB := memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell
      (originCube d (S.m : ℤ)) hGL2
    have hsplit : (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
        (coefficientCutoff nu omega S.ell).toCoeffField y)
      ((w omega).toH1Function.grad y)) =
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          ((w omega).toH1Function.grad y) -
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y)) := by
      funext y
      exact sub_matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        ((coefficientCutoff nu omega S.ell).toCoeffField y)
        ((w omega).toH1Function.grad y)
    rw [hsplit]
    exact hA.sub hB
  -- weak gradient of `R` and its `L²` Jacobian; response-field clauses carried in `hRres`
  obtain ⟨DR, hDR, hDRL2⟩ := exists_rfieldWeakJacobian d hd nu S hSorder
    (testVector nu S.LPrime P S.n e) w hw
  obtain ⟨hfinDR, hmDR, hRb⟩ := hRres DR hDR hDRL2
  -- finiteness, measurability and integrability of the proxy fields
  obtain ⟨hfinDiff, hfinProx⟩ := term2_ob4_finite hnu P S hSorder e
  obtain ⟨hmDiff, hmProx⟩ := term2_ob5_measurable hnu P S hSorder e
  obtain ⟨hIntDiff, hIntProxy, hIntMean⟩ := term2_ob6_int hnu P S hSorder e w hw hfinR
  exact hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he
    (testVector nu S.LPrime P S.n e) rfl w hw
    (fun omega x => gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega x)
    DR hDR hRb
    (term2_ob2_at d nu hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e Cloc hLocM hLocN)
    (term2_ob3_at d nu hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e he hPtilde)
    (fun omega y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
        (coefficientCutoff nu omega S.ell).toCoeffField y)
      ((w omega).toH1Function.grad y))
    (fun omega y => rfl)
    (fun omega x => HilbertMat.ofMat (fun i j => DR omega i x j))
    (fun omega x => rfl)
    hRL2
    (fun omega => memVectorL2_gluedGradientField hnu S.LPrime S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))
    (fun omega => memVectorL2_gluedGradientField hnu S.ell S.n S.m
      (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))
    hDRL2 hfinR hfinDR hfinDiff hfinProx
    (aemeasurable_vecCubeLpENorm_matVecMul_coefficientCutoff_sub_grad (d := d) hnu S.LPrime S.ell
      (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m)
      (p := testVector nu S.LPrime P S.n e) (mu := P.toMeasure) (w := w) hw)
    hmDR hmDiff hmProx hIntDiff hIntProxy hIntMean
    (fun z hz =>
      SuperdiffusionCLT.Section3.Setup.measurable_volumeAverageVec_matVecMul_coefficientCutoff_sub_grad_highShellSigma
        nu (le_of_lt hSorder.ell_lt_ellPrime) (ellPrime_le_LPrime_of_scalesOrdering hSorder)
        (p := testVector nu S.LPrime P S.n e) hw hz)

end

end SuperdiffusionCLT.Section3.Terms
