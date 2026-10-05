/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn
public import SuperdiffusionCLT.Section2.Carriers.BlockOperatorNorm
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The target statement of `l.new.mixing.parameterized`

Lemma `l.new.mixing.parameterized`. This file supplies the three carriers the
exact statement needs and records the statement text itself in the module docstring below,
so that a consumer can copy it verbatim as a hypothesis. The statement is proved, from the
two hypotheses `hHomog` and `hComp`, as `newMixParam_main_uniform_of_inputs`
(`AssemblyMainParamUniform.lean`).

## Carriers

* `newMixParam_entryBound`, `newMixParam_entryBound_holds`: an explicit,
  hypothesis-free (beyond `0 < nu`) entry bound for the cutoff field `a_L` on
  a bounded Chapter 2 domain, in the shape `coefficientCutoffCoeffOn` needs.
  This is the same combination already used privately by
  `SuperdiffusionCLT.Section2.Localization.CutoffLoewnerClauses.cutoffEntryBound`
  (there `private`), rebuilt here from the public lemmas
  `abs_coefficientCutoff_entry_le` and `abs_streamCutoffEntryBound` so this
  file does not need to import that (unrelated, heavier) localization module.
* `newMixParam_aLplusH0`: the Chapter 2 coefficient object `a_L + h_0` on
  `cu_m`, i.e. `addConstSkewCoeffOn` applied to `coefficientCutoffCoeffOn`
  applied to `coefficientCutoff`, exactly the composition already
  established for "coefficient field plus a constant skew matrix" in
  `SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff`.
* `newMixParam_bfAhomPow`: `Ā_r^s η` for `η : BlockVec d` and a real
  exponent `s` (used at `s = ±1/2`). Read scalar-wise, in the same spirit as
  `Frozen/Section4/HomogenizationBelowCutoff.lean`'s "the scalars, not
  matrices" convention: `Ā_r := blockDiag(σ̄_r, σ̄_r^{-1})` is
  literally block-diagonal with the *single* scalar `σ̄_r = sigmaBarInfinite
  nu r P` (matching `HomogenizationBelowCutoff.lean`'s reading of the
  unsubscripted `σ̄_r`, not the separately-limited, not-yet-provably-
  reciprocal pair `sigmaBarUpperLimit`/`sigmaBarStarInvLimit` of
  `AnnealedBlockInfinite.lean`), so its `s`-power acts on the two `Vec d`
  components of `eta` by the two scalars `σ̄_r^s` and `σ̄_r^{-s}`.

## The statement

The exact statement below is expressed in this file's carriers. It is
recorded here as text; it is proved as `newMixParam_main_uniform_of_inputs`:

```
theorem newMixParam_main (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hHomog : <the full `∃ C, ...` body of
      SuperdiffusionCLT.Frozen.Section4.homogenization_below_cutoff d hd>)
    (hComp : <the full `∃ C, ...` body of
      SuperdiffusionCLT.Frozen.Section4.sigmaBar_cutoff_comparison d hd>) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ alpha M K : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K →
            ∀ L m r : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (L : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (m : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                ∀ (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0),
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    ∀ eta : Homogenization.BlockVec d,
                      SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
                        Homogenization.Book.Ch02.doubledResponseJ
                          (Homogenization.Book.Ch02.cubeDomain
                            (Homogenization.originCube d (m : ℤ)))
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta) ≤
                        C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                            (-(2 : ℝ)) *
                            ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                              max 0 ((L : ℝ) - (m : ℝ)) +
                              K * Real.log (L : ℝ) ^ (2 : ℝ)) +
                          X1 omega +
                          (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                                (-(1 : ℝ)) *
                              (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega
```

`hHomog`/`hComp` are the printed lemma's own implicit "Proposition
`p.homog.below` applies" / "the same comparison as in the proof of Lemma
`l.shomm.vs.shomell`" inputs, carried as hypotheses. `nondeg` is `K` in `ShellLawJ5`'s own third
argument, renamed here (matching `MathcalEBounds.lean`'s `nondeg` convention) to avoid
colliding with the *lemma's own* printed `K` (the `|L-r| ≤ K log L` bound).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

/-- An explicit, hypothesis-free (beyond `0 < nu`) entry bound for the level-`L`
cutoff field `a_L = nu Id + k_L` on a Chapter 2 domain, in the shape consumed
by `coefficientCutoffCoeffOn`. This is the molecular diffusivity plus the sum
of the per-entry stream bounds, matching (but locally rebuilding, to avoid an
unrelated heavy import) `CutoffLoewnerClauses.cutoffEntryBound`. -/
noncomputable def newMixParam_entryBound {d : ℕ} (U : Homogenization.Book.Ch02.Domain d)
    (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L : ℕ) : ℝ :=
  nu + ∑ p : Fin d × Fin d,
    |SuperdiffusionCLT.Section2.Cutoff.streamCutoffEntryBound
        U.isDomain.isBoundedDomain.isBounded omega L p|

/-- The explicit entry bound `newMixParam_entryBound` works. -/
theorem newMixParam_entryBound_holds {d : ℕ} [NeZero d]
    (U : Homogenization.Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L : ℕ)
    (x : Homogenization.Vec d) (hx : x ∈ (U : Set (Homogenization.Vec d)))
    (i j : Fin d) :
    |(SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x i j| ≤
      newMixParam_entryBound U nu omega L := by
  refine SuperdiffusionCLT.Section2.CoarseGraining.abs_coefficientCutoff_entry_le
    hnu.le omega L x ?_ i j
  intro i' j'
  calc |SuperdiffusionCLT.Frozen.Section2.streamCutoff omega L x i' j'|
      ≤ |SuperdiffusionCLT.Section2.Cutoff.streamCutoffEntryBound
          U.isDomain.isBoundedDomain.isBounded omega L (i', j')| :=
        (SuperdiffusionCLT.Section2.Cutoff.abs_streamCutoffEntryBound
          U.isDomain.isBoundedDomain.isBounded omega L (i', j') x hx).trans (le_abs_self _)
    _ ≤ ∑ p : Fin d × Fin d,
          |SuperdiffusionCLT.Section2.Cutoff.streamCutoffEntryBound
              U.isDomain.isBoundedDomain.isBounded omega L p| :=
        Finset.single_le_sum
          (f := fun p => |SuperdiffusionCLT.Section2.Cutoff.streamCutoffEntryBound
              U.isDomain.isBoundedDomain.isBounded omega L p|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ _)

/-- The Chapter 2 coefficient object `a_L + h_0` on `cu_m`: the marginal
cutoff field `a_L`, built as a `CoeffOn` via `newMixParam_entryBound_holds`,
shifted by the constant skew-symmetric matrix `h_0`. -/
noncomputable def newMixParam_aLplusH0 {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m : ℕ)
    (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0) :
    Homogenization.Book.Ch02.CoeffOn
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ))) :=
  SuperdiffusionCLT.Section2.CoarseGraining.addConstSkewCoeffOn
    (SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
      hnu omega L
      (fun x hx i j => newMixParam_entryBound_holds _ nu hnu omega L x hx i j))
    hh0

/-- `Ā_r^s η`, read scalar-wise: the block matrix `Ā_r` is block-diagonal with the
single scalar `σ̄_r = sigmaBarInfinite nu r P` on both diagonal blocks (the
print's own definition `Ā_r := blockDiag(σ̄_r, σ̄_r^{-1})`), so its
`s`-power acts on the two `Vec d` components of `η` by `σ̄_r^s` and
`σ̄_r^{-s}` respectively. -/
noncomputable def newMixParam_bfAhomPow {d : ℕ} [NeZero d] (nu : ℝ) (r : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (s : ℝ) (eta : Homogenization.BlockVec d) : Homogenization.BlockVec d :=
  ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^ s • eta.1,
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^ (-s) • eta.2)

end SuperdiffusionCLT.Section4.NewMixing
