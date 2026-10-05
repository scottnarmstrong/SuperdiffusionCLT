/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2LocDisplaysB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2LocDisplays
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Final

/-!
# The `l.RHS.term2` statement with the localization displays at a named constant

The term-2 chain carries five residue hypotheses; `RHSTerm2LocDisplaysB`
proves the first two of them (`hLocM`, `hLocN`) from the single clause
`hLocMin`, and `RHSTerm2LocDisplays` reduces the last three (`hRres` to a single
weak-gradient witness, `hPtilde` to the comparison of the two annealed energies).

## Why the two display reductions cannot be used directly

`RHSTerm2LocDisplaysB.hLocM_of_locMin` and `hLocN_of_locMin` produce their
displays at the **existential** constant `∃ C, 1 ≤ C ∧ ...` of the chain
`sqrt(Cloc * shellDerivLargeCubeMomentConst d)`, where `Cloc` is the clause's own
constant.  The term-2 chain, however, consumes the displays at a **fixed**
constant: `RHSTerm2Assembly.term2_of_residue` takes `Cloc` as a parameter and
the proxy-error display compares the two displays at one and the same
constant.  The witness of an existential produced by a `theorem` is opaque: it
cannot be named, let alone pinned to `sqrt(Cloc * shellDerivLargeCubeMomentConst d)`
or bounded above by it.  A direct test (`obtain ⟨C, _, _⟩ := hLocM_of_locMin ...;
have : C = ... := rfl`) fails at elaboration, so the displays of
`RHSTerm2LocDisplaysB` cannot feed the chain.

The fix below is to re-derive the printed chain
(`subcube_energy_sq_le` + sub-cube decomposition + stationarity + Cauchy-Schwarz +
the annealed derivative moment) at the **named** constant
`max 1 (sqrt(Cloc * shellDerivLargeCubeMomentConst d))`, reproducing
`RHSTerm2LocDisplaysB.hLoc_display_of_locMin` with the existential replaced by
that explicit constant.  `hLoc_display_at_const` is that re-derivation;
`hLocM_at_const` and `hLocN_at_const` are its two instances at `r = S.m` and
`r = S.n`.

## Main results

* `hLoc_display_at_const`: the printed localization chain at the named constant.
* `hLocM_at_const`, `hLocN_at_const`: its instances `hLocM` and `hLocN` of the term-2 chain at
  `r = S.m` and `r = S.n`.
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
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

/-! ## The uniform localization estimate at a named constant -/

variable {nu : ℝ}

/-- **The localization display of `e.RHS.term2.proxy.error` at every
intermediate scale `r`, with the constant named.**
This is `RHSTerm2LocDisplaysB.hLoc_display_of_locMin` with the existential
constant `∃ C, 1 ≤ C ∧ ...` replaced by the explicit constant the printed chain
produces, `max 1 (sqrt(Cloc * shellDerivLargeCubeMomentConst d))`.  The proof is
the same chain: the clause `hLocMin` quenched at each scale-`n` sub-cube
(`RHSTerm2LocDisplaysB.subcube_energy_sq_le`), the exact sub-cube decomposition,
stationarity of the shell law (`ShellLawJ2`), Cauchy-Schwarz in `ω`, and the
annealed derivative moment
`RHSTerm1InputsE.sqrt_second_moment_shellDerivCubeLinftyENorm_high_le`. -/
theorem hLoc_display_at_const (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) (he : vecNormSq e = 1)
    {Cloc : ℝ} (hCloc0 : 0 ≤ Cloc)
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
                  2 * vecDot p q)) :
    ∀ r : ℕ, S.n ≤ r → r ≤ S.m →
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (r : ℤ)) 2
              (fun x => gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x -
                gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
        (max 1 (Real.sqrt (Cloc * shellDerivLargeCubeMomentConst d))) *
          nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
          (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ := by
  classical
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hFdef
  set Cc : ℝ := Real.sqrt (Cloc * shellDerivLargeCubeMomentConst d) with hCcdef
  set K : ℝ := Cloc * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ ((S.n : ℝ)) * vecNormSq F with hKdef
  set M : ℝ := shellDerivLargeCubeMomentConst d * ((3 : ℝ) ^ S.ell)⁻¹ with hMdef
  set Sm : ℝ := (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ with hSmdef
  set t : ℝ := (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) with htdef
  set Y : ShellSeq d → ℝ≥0∞ :=
    fun om => shellDerivCubeLinftyENorm S.ell S.LPrime S.n om with hYdef
  set G : ShellSeq d → ℝ≥0∞ :=
    fun om => ENNReal.ofReal K * Y om with hGdef
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  have hLL : S.ell ≤ S.LPrime := by
    have h1 := hSorder.ell_lt_ellPrime
    have h2 := hSorder.ellPrime_lt_m
    have h3 := hSorder.m_lt_LPrime
    omega
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  have hxcast : ((S.ell - S.n : ℕ) : ℝ) = (S.ell : ℝ) - S.n := by
    rw [Nat.cast_sub hnl]
  have hCdpos : 0 < shellDerivLargeCubeMomentConst d :=
    shellDerivLargeCubeMomentConst_pos hPrefix
  have hClocCd0 : (0 : ℝ) ≤ Cloc * shellDerivLargeCubeMomentConst d :=
    mul_nonneg hCloc0 (le_of_lt hCdpos)
  have hCc2 : Cc ^ 2 = Cloc * shellDerivLargeCubeMomentConst d := by
    rw [hCcdef]
    exact Real.sq_sqrt hClocCd0
  have hYmeas : Measurable Y := by
    rw [hYdef]
    exact measurable_shellDerivCubeLinftyENorm S.ell S.LPrime S.n
  have hGmeas : Measurable G := by
    rw [hGdef]
    exact measurable_const.mul hYmeas
  have hFslot : vecNormSq F =
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ := by
    rw [hFdef]
    exact vecNormSq_fluxSlot hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hsqrtF : (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ = Real.sqrt (vecNormSq F) := by
    show (Real.sqrt
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu S.LPrime P S.n))⁻¹ =
        Real.sqrt (vecNormSq F)
    rw [← Real.sqrt_inv, ← hFslot]
  have hSm2 : Sm ^ 2 = vecNormSq F := by
    rw [hSmdef, hsqrtF, Real.sq_sqrt (vecNormSq_nonneg F)]
  have hnu32sq : (nu ^ (-((3 : ℝ) / 2))) ^ (2 : ℕ) = nu ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnu.le]
    congr 1
    norm_num
  have ht2 : t ^ 2 = (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) := by
    rw [htdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hexp : (3 : ℝ) ^ ((S.n : ℝ)) * ((3 : ℝ) ^ S.ell)⁻¹ =
      (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) := by
    rw [hxcast, ← Real.rpow_natCast (3 : ℝ) S.ell,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    have h1 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg hnu.le _
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((S.n : ℝ)) := Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg (mul_nonneg (mul_nonneg hCloc0 h1) h2) (vecNormSq_nonneg F)
  have hM0 : (0 : ℝ) ≤ M := by
    rw [hMdef]
    exact mul_nonneg (le_of_lt hCdpos) (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
  have hsq : (Cc * nu ^ (-((3 : ℝ) / 2)) * t * Sm) ^ 2 = K * M := by
    have hL : (Cc * nu ^ (-((3 : ℝ) / 2)) * t * Sm) ^ 2 =
        Cc ^ 2 * (nu ^ (-((3 : ℝ) / 2))) ^ 2 * t ^ 2 * Sm ^ 2 := by ring
    rw [hL, hCc2, hnu32sq, ht2, hSm2, hKdef, hMdef, ← hexp]
    ring
  have hRHS0 : (0 : ℝ) ≤ Cc * nu ^ (-((3 : ℝ) / 2)) * t * Sm := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hnu.le _)) (Real.rpow_nonneg (by norm_num) _)) ?_
    rw [hSmdef]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hSq : Real.sqrt (K * M) = Cc * nu ^ (-((3 : ℝ) / 2)) * t * Sm := by
    rw [← hsq, Real.sqrt_sq hRHS0]
  have hmom : ((∫⁻ omega : ShellSeq d, Y omega ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ^
      ((1 : ℝ) / 2)) ≤ ENNReal.ofReal M := by
    have h := sqrt_second_moment_shellDerivCubeLinftyENorm_high_le (P := P) hPrefix hJ3
      (a := S.ell) (b := S.LPrime) (r := S.n) hLL hnl
    simpa only [hYdef, hMdef] using h
  have hfirst : (∫⁻ omega : ShellSeq d, Y omega ∂P.toMeasure) ≤
      (∫⁻ omega : ShellSeq d, Y omega ^ (2 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2) := by
    have h := lintegral_sq_mul_le_of_measurable P.toMeasure
      (X := fun _ : ShellSeq d => (1 : ℝ≥0∞)) (Y := Y) measurable_const hYmeas
    have hone : (∫⁻ omega : ShellSeq d, (1 : ℝ≥0∞) ^ (2 : ℕ) * Y omega ∂P.toMeasure) =
        ∫⁻ omega : ShellSeq d, Y omega ∂P.toMeasure := by
      refine lintegral_congr fun omega => ?_
      rw [one_pow, one_mul]
    have hfour : (∫⁻ omega : ShellSeq d, (1 : ℝ≥0∞) ^ (4 : ℕ) ∂P.toMeasure) = 1 := by
      rw [one_pow, lintegral_one]
      simp
    rw [hone, hfour] at h
    simpa only [ENNReal.one_rpow, one_mul] using h
  intro r hnr hrm
  have hnmr : S.n ≤ S.m := le_trans hnr hrm
  have hCentre : ∀ omega' : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.n : ℤ)))
          (fun x => vecNormSq
            (cubeMaximizerGradient hnu omega' S.LPrime F (originCube d (S.n : ℤ)) x -
              cubeMaximizerGradient hnu omega' S.ell F (originCube d (S.n : ℤ)) x)) ≤
        Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
          anchorDerivSup S.ell S.LPrime S.n omega' * (nu⁻¹ * vecNormSq F) :=
    fun omega' => localization_minimizers_originCube hnu omega' hCloc0 F hLocMin
  have hptw : ∀ omega : ShellSeq d,
      (vecCubeLpENorm (originCube d (r : ℤ)) 2
        (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
          gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) ≤
      ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n r,
          G (ShellField.translateSequence (triadicCubeShift R) omega) := by
    intro omega
    have hsplit := cubeLpENorm_two_sq_eq_inv_card_mul_sum
      (Q := originCube d (r : ℤ)) (r - S.n)
      (hilbertifyVecField (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
        gluedGradientField hnu S.ell S.n S.m F omega x))
    rw [show descendantsAtDepth (originCube d (r : ℤ)) (r - S.n) =
      largeCubeSubcubes d S.n r from rfl] at hsplit
    rw [show vecCubeLpENorm (originCube d (r : ℤ)) 2
        (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
          gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ) =
      Section2.Norms.cubeLpENorm (originCube d (r : ℤ)) 2
          (hilbertifyVecField (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ) from rfl,
      hsplit]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum ?_)
    intro R hR
    exact subcube_energy_sq_le hnu S F hCloc0 hCentre hnmr omega
      (mem_largeCubeSubcubes_of_mem_largeCubeSubcubes_le hnr hrm hR)
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d S.n r).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (largeCubeSubcubes_nonempty d S.n r)
  have hcancel : ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
      (((largeCubeSubcubes d S.n r).card : ℕ) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hcardpos)),
      inv_mul_cancel₀ (ne_of_gt hcardpos), ENNReal.ofReal_one]
  have hchain : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (r : ℤ)) 2
          (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ)
        ∂P.toMeasure) ≤ ENNReal.ofReal (K * M) := by
    refine le_trans (lintegral_mono hptw) ?_
    calc ∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
            ∑ R ∈ largeCubeSubcubes d S.n r,
              G (ShellField.translateSequence (triadicCubeShift R) omega) ∂P.toMeasure
        = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
            ∫⁻ omega : ShellSeq d, ∑ R ∈ largeCubeSubcubes d S.n r,
              G (ShellField.translateSequence (triadicCubeShift R) omega)
            ∂P.toMeasure := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
            ∑ R ∈ largeCubeSubcubes d S.n r, ∫⁻ omega : ShellSeq d,
              G (ShellField.translateSequence (triadicCubeShift R) omega)
            ∂P.toMeasure := by
          refine congrArg (fun s => ENNReal.ofReal
            (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ * s) ?_
          exact lintegral_finsetSum _ (fun R _ =>
            hGmeas.comp (ShellField.measurable_translateSequence (triadicCubeShift R)))
      _ = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
            ∑ _R ∈ largeCubeSubcubes d S.n r,
              ∫⁻ omega : ShellSeq d, G omega ∂P.toMeasure := by
          refine congrArg (fun s => ENNReal.ofReal
            (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ * s) ?_
          refine Finset.sum_congr rfl fun R _ => ?_
          exact (measurePreserving_translateSequence hPrefix hJ2
            (triadicCubeShift R)).lintegral_comp hGmeas
      _ = ENNReal.ofReal (((largeCubeSubcubes d S.n r).card : ℝ))⁻¹ *
            ((((largeCubeSubcubes d S.n r).card : ℕ) : ℝ≥0∞) *
              ∫⁻ omega : ShellSeq d, G omega ∂P.toMeasure) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∫⁻ omega : ShellSeq d, G omega ∂P.toMeasure := by
          rw [← mul_assoc, hcancel, one_mul]
      _ = ENNReal.ofReal K * ∫⁻ omega : ShellSeq d, Y omega ∂P.toMeasure := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal M :=
          mul_le_mul' le_rfl (hfirst.trans hmom)
      _ = ENNReal.ofReal (K * M) := (ENNReal.ofReal_mul hK0).symm
  have hKM0 : (0 : ℝ) ≤ K * M := mul_nonneg hK0 hM0
  have htoReal : ((∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (r : ℤ)) 2
          (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞)).toReal ≤ K * M :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain).trans_eq
      (ENNReal.toReal_ofReal hKM0)
  have hsqrt : (((∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (r : ℤ)) 2
          (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x)) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞)).toReal ^ ((1 : ℝ) / 2)) ≤ Real.sqrt (K * M) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg htoReal (by norm_num)
  have hL1 : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have hnat : 1 ≤ S.LPrime := by omega
    exact_mod_cast hnat
  have hCle : Cc * nu ^ (-((3 : ℝ) / 2)) ≤
      max 1 Cc * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) := by
    have hC0 : (0 : ℝ) ≤ max 1 Cc := le_trans zero_le_one (le_max_left 1 Cc)
    have hnu32 : (0 : ℝ) ≤ nu ^ (-((3 : ℝ) / 2)) := Real.rpow_nonneg hnu.le _
    calc Cc * nu ^ (-((3 : ℝ) / 2)) ≤ max 1 Cc * nu ^ (-((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 Cc) hnu32
      _ = max 1 Cc * nu ^ (-((3 : ℝ) / 2)) * 1 := (mul_one _).symm
      _ ≤ max 1 Cc * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hL1 (mul_nonneg hC0 hnu32)
  have hfinal : Real.sqrt (K * M) ≤ max 1 Cc * nu ^ (-((3 : ℝ) / 2)) *
      ((S.LPrime : ℕ) : ℝ) * t * Sm := by
    rw [hSq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCle (Real.rpow_nonneg (by norm_num) _))
      (by rw [hSmdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [hSmdef, htdef] at hfinal
  exact hsqrt.trans hfinal

/-! ## The two displays at the named constant -/

/-- **`hLocM` of the term-2 chain, at the named constant.**  `hLoc_display_at_const`
at `r = S.m`. -/
theorem hLocM_at_const (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) (he : vecNormSq e = 1)
    {Cloc : ℝ} (hCloc0 : 0 ≤ Cloc)
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
                  2 * vecDot p q)) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
      (max 1 (Real.sqrt (Cloc * shellDerivLargeCubeMomentConst d))) *
        nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
        (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ := by
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  exact hLoc_display_at_const d hnu hPrefix hJ2 hJ3 hJ4 S hSorder e he hCloc0 hLocMin
    S.m hnm le_rfl

/-- **`hLocN` of the term-2 chain, at the named constant.**  `hLoc_display_at_const`
at `r = S.n` with the gradient difference negated, which the cube carrier does
not see (`Section3.ResponseFields.vecCubeLpENorm_neg`). -/
theorem hLocN_at_const (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) (he : vecNormSq e = 1)
    {Cloc : ℝ} (hCloc0 : 0 ≤ Cloc)
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
                  2 * vecDot p q)) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.n : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
      (max 1 (Real.sqrt (Cloc * shellDerivLargeCubeMomentConst d))) *
        nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
        (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ := by
  set F : Vec d := fluxSlot nu S.LPrime P S.n e with hFdef
  have hkey : (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.n : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
              gluedGradientField hnu S.LPrime S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure) =
      (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.n : ℤ)) 2
            (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
              gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure) := by
    refine lintegral_congr fun omega => ?_
    congr 1
    rw [show (fun x => gluedGradientField hnu S.ell S.n S.m F omega x -
            gluedGradientField hnu S.LPrime S.n S.m F omega x) =
          (fun x => -(gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x)) from by
      funext x
      rw [neg_sub]]
    exact vecCubeLpENorm_neg (originCube d (S.n : ℤ)) 2
      (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
        gluedGradientField hnu S.ell S.n S.m F omega x)
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  rw [hkey, hFdef]
  exact hLoc_display_at_const d hnu hPrefix hJ2 hJ3 hJ4 S hSorder e he hCloc0 hLocMin
    S.n le_rfl hnm

/-! ## The conclusion with the shortest residue -/

end

end SuperdiffusionCLT.Section3.Terms
