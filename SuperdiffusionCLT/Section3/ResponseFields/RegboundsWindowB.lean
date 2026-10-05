/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderZero
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindow
public import SuperdiffusionCLT.Section3.Terms.RHSTerm4Join

/-!
# `e.nablaw.Lt` and `e.RHS.term4` with no input left but the window factor

The paper's displays `e.nablaw.Lt` and `e.RHS.term4`.

`l_w_basic_regbounds_window_constFirst` proves `e.nablaw.Lt` with the
low-shell Jacobian input discharged at its own honest amplitude and the
resulting `√(1 + h)` factor carried on the second clause.  Two inputs of that
statement are conclusions of proved theorems and are discharged here:

* the three shell-increment clauses `e.kmn.Lp` (at `p = 8` and `p = 2`) and
  `e.kmn.Hs.osc` (at `s = 1/2`), from
  `SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates`; and
* `hApriori`, from the a priori response estimate
  `SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero`.

The result, `l_w_basic_regbounds_window`, therefore asks for nothing beyond the
dimension `d` and `2 ≤ d`.  Its third clause — the fractional `H̲^{1/2}`
estimate — is byte for byte the third clause of the printed statement,
and it is the only clause `e.RHS.term4` consumes; feeding it to
`l_RHS_term4_of_gate_ae` gives
`l_RHS_term4_of_window`, again with no hypothesis beyond `d` and `2 ≤ d`.  In
particular the constant of term 4 does **not** pick up the window factor: the
factor sits on the second clause of `e.nablaw.Lt`, which term 4 never reads.

## Main results

* `l_w_basic_regbounds_window`: `e.nablaw.Lt` with no hypothesis beyond `d` and
  `2 ≤ d`, with `√(1 + h)` on the amplitude of the second clause only.
* `l_RHS_term4_of_window`: `e.RHS.term4` with no hypothesis beyond `d` and
  `2 ≤ d`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-! ## `e.nablaw.Lt` with every input discharged -/

/-- **`l.w.basic.regbounds`** with the constant quantified before the scale selection, the shell
law, the test vector and the response, and with **every** input discharged: the
three shell-increment clauses from
`streamIncrement_scale_estimates`, the a priori response estimates from
`responseFields_apriori_orderZero`, and the low-shell Jacobian display on
`cu_m` from the large-cube estimate
`exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube`.

The statement is that of the printed `l.w.basic.regbounds` with the binder
`_hNablaKmnLow` and its constant `Cn` removed, except in the amplitude of the
**second** clause, which is `C |p| √(1 + h) 3^{-ℓ'}` instead of `C |p| 3^{-ℓ'}`:
that is the union-bound loss of the low-shell Jacobian (see
`l_w_basic_regbounds_window_constFirst`), absorbed into the conclusion rather
than recorded as the hypothesis `nablaKmnLowWindowConst d S.h ≤ Cn`.  The first
and third clauses are unchanged. -/
theorem l_w_basic_regbounds_window
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)),
        (∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ∧
          ∀ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 8
                (w omega).toH1Function.grad ≤ ENNReal.ofReal (Z omega)) ∧
        (∀ (HD : ∀ omega : ShellSeq d,
              HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
                (w omega).toH1Function),
          ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) *
                (Real.sqrt (1 + (S.h : ℝ)) *
                  (3 : ℝ) ^ (-(S.ellPrime : ℝ))))) ∧
            ∀ omega : ShellSeq d,
              Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
                  (fun x => HilbertMat.ofMat
                    (fun i j => (HD omega).hess i j x)) ≤
                ENNReal.ofReal (Z omega)) ∧
        (∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) *
                (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)))) ∧
          ∀ᵐ omega ∂P.toMeasure,
            Section2.Norms.cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
                (hilbertifyVecField (w omega).toH1Function.grad) ≤
              ENNReal.ofReal (Z omega)) := by
  obtain ⟨Capriori, hCapriori, hApriori⟩ :=
    SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero d hd
  obtain ⟨CTwo, hgateS⟩ :=
    SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates d
  obtain ⟨CZero, COne, hgateP⟩ := hgateS ((1 : ℝ) / 2) (by norm_num) (by norm_num)
  obtain ⟨Ca, hgateA⟩ := hgateP (8 : ℝ) (by norm_num)
  obtain ⟨Cb, hgateB⟩ := hgateP (2 : ℝ) (by norm_num)
  have hCHpos : (0 : ℝ) < |Cb| + 1 := by positivity
  obtain ⟨C, hC1, hmain⟩ :=
    l_w_basic_regbounds_window_constFirst d hd Capriori hCapriori Ca Cb
      (|Cb| + 1) hCHpos hApriori
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
  have _ := CZero
  have _ := COne
  have _ := CTwo
  have hA := hgateA P hPrefix hJ1V2 hJ2 hJ3 hJ4
  have hB := hgateB P hPrefix hJ1V2 hJ2 hJ3 hJ4
  -- `e.kmn.Lp` at `p = 8` and at `p = 2`, at `(l, m, n) = (m, m - 1, ℓ')`
  have hLp8 := exists_kmnLpClause_of_gate (P := P) (C := Ca) (q := (8 : ℝ))
    (l := S.m) (m := S.m - 1) (n := S.ellPrime)
    (fun hlt => (hA.1 S.m (S.m - 1) S.ellPrime hlt (Nat.sub_le S.m 1)).2.1)
  have hLp2 := exists_kmnLpClause_of_gate (P := P) (C := Cb) (q := (2 : ℝ))
    (l := S.m) (m := S.m - 1) (n := S.ellPrime)
    (fun hlt => (hB.1 S.m (S.m - 1) S.ellPrime hlt (Nat.sub_le S.m 1)).2.1)
  -- `e.kmn.Hs.osc` at `(l, n) = (m, ℓ')`, with the clause constant made positive
  have hHs : ∃ X : ShellSeq d → ℝ, Measurable X ∧
      IsBigO P.toMeasure (gammaSigma 2) X
        ((|Cb| + 1) * (3 : ℝ) ^ (-(((1 : ℝ) / 2) * (S.ellPrime : ℝ)))) ∧
      ∀ᵐ omega ∂P.toMeasure,
        (⨆ M : {M : ℕ // S.ellPrime < M},
          cubeEuclideanGagliardoESeminorm (originCube d (S.m : ℤ))
            ((1 : ℝ) / 2) 2
            (fun x => (finiteShellIncrement omega S.ellPrime M.1 x : Mat d))) ≤
          ENNReal.ofReal (X omega) := by
    obtain ⟨X, hXm, hXO, hXle⟩ := hB.2.1 S.m S.ellPrime
    refine ⟨X, hXm, ?_, hXle⟩
    refine hXO.mono_scale ?_
    have hbase : (0 : ℝ) ≤
        (3 : ℝ) ^ (-(((1 : ℝ) / 2) * (S.ellPrime : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hle : Cb ≤ |Cb| + 1 := by
      have := le_abs_self Cb
      linarith only [this]
    exact mul_le_mul_of_nonneg_right hle hbase
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    hLp8 hLp2 hHs

/-! ## `e.RHS.term4` with every input discharged -/

/-- **`l.RHS.term4`** (`e.RHS.term4`) with **no** hypothesis beyond the dimension: the fractional
`H̲^{1/2}` estimate of `e.nablaw.Lt` that `l_RHS_term4_of_gate_ae`
asks for is the third conclusion of
`l_w_basic_regbounds_window`, and every other input of the term-4 chain — the
`W^{-1/2,2}` estimate `e.kmn.Wminussp`, the fractional duality of the paper,
the shell-increment estimates and the a priori response estimate — is available
already.

The amplitude constant does **not** carry the `√(1 + h)` window factor: term 4
reads only the third clause of `e.nablaw.Lt`, whose amplitude
`C |p| 3^{-ℓ'/2}` is the printed one, and the union-bound loss
sits on the second clause, which term 4 never uses. -/
theorem l_RHS_term4_of_window
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                  streamCutoff omega S.ell y)
                ((w omega).toH1Function.grad y)))
          ∂P.toMeasure| ≤
          C * (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) := by
  obtain ⟨Creg, hCreg1, hreg⟩ := l_w_basic_regbounds_window d hd
  obtain ⟨C, hC1, hmain⟩ := l_RHS_term4_of_gate_ae d hd Creg hCreg1
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw
    (hreg nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder ee he p hp w hw).2.2

end

end SuperdiffusionCLT.Section3.ResponseFields
