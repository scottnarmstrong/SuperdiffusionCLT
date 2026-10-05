/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.TermsCombined
public import SuperdiffusionCLT.Section4.Mixing.Term1UniformBound
public import SuperdiffusionCLT.Section4.Ellipticity.EllipticityBelowCutoffMain

/-!
# mixMain: the `hLocBound`-shaped witness, B-form

`p.mixing.P.three.prime#term1-bound`. `TermsCombined.lean`'s `mixTerms_combineTermsBound` takes the
localization-term bound `hLocBound` as a *bare* `C * m ^ (-5000)`-amplitude
hypothesis. This file supplies the honest replacement at an *explicit*
amplitude, in the same style as the witnesses of
`TermGaugeFinalB.lean`: `mixTerms_term1UniformBound`
(`Term1UniformBound.lean`, the Euclidean-normalized uniform witness) combined
with `mixTerms_crudeEllipticity` (`e.Enaught.vs.Ahom.L.crude`,
`Term1PolarizedBound.lean`) converts the Euclidean sandwich
bound into the `Aell`-relative one `hLocBound` needs, at the explicit
amplitude `ellipBelow_crudeConst d * nu^{-3} * ell` times
`Term1UniformBound.lean`'s own explicit witness amplitude.

## Main result

* `mixMain_term1BoundB`: the `hLocBound`-shaped witness (`TermsCombined.lean`'s
  exact `Aell`-normalized sandwich shape), at the explicit amplitude above,
  unconditional given the standing shell laws and `1 ≤ ell`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section4.Ellipticity

noncomputable section

variable {d : ℕ}

/-- **The `hLocBound`-shaped witness, B-form.** `TermsCombined.lean`'s
`hLocBound`, at the explicit amplitude
`ellipBelow_crudeConst d * nu^{-3} * ell` times `mixTerms_term1UniformBound`'s
own witness amplitude, in place of the bare `C * m ^ (-5000)` the proof
sketch of `p.mixing.P.three.prime` anticipated. Concrete satisfying instance:
`d := 2`, `nu := 1`, `n := 0`, `ell := L := 1`,
and any `P` already known to satisfy the standing shell laws. -/
theorem mixMain_term1BoundB (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
            ∀ m n ell L : ℕ, n ≤ ell → ell ≤ m → ell ≤ L → 1 ≤ ell →
              ∃ X3loc : ShellSeq d → ℝ,
                Measurable X3loc ∧
                  IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3loc
                    (ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (ell : ℝ) *
                      (gammaTriangleConst ((1 : ℝ) / 3) *
                        ((Fintype.card (BlockCoord d × BlockCoord d) : ℝ) *
                          mixTerms_pairFinalAmp C nu d ell L n m))) ∧
                  ∀ (omega : ShellSeq d) (p q : BlockVec d),
                    2 *
                        (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                            blockVecDot p
                              (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
                      X3loc omega *
                        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  obtain ⟨C, hC⟩ := mixTerms_term1UniformBound d
  refine ⟨C, fun nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL hell1 => ?_⟩
  obtain ⟨X, hXm, hXO, hXbd⟩ := hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL
  set K : ℝ := ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (ell : ℝ) with hKdef
  have hKnn : 0 ≤ K := by
    have hcrude_nn : (0 : ℝ) ≤ ellipBelow_crudeConst d :=
      le_trans zero_le_one (ellipBelow_one_le_crudeConst d)
    have hpow_nn : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg hnu.le _
    have hell_nn : (0 : ℝ) ≤ (ell : ℝ) := by positivity
    rw [hKdef]
    exact mul_nonneg (mul_nonneg hcrude_nn hpow_nn) hell_nn
  refine ⟨fun omega => max (X omega) 0 * K, (hXm.max measurable_const).mul_const K, ?_, ?_⟩
  · have habs : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) (fun omega => max (X omega) 0)
        (gammaTriangleConst ((1 : ℝ) / 3) *
          ((Fintype.card (BlockCoord d × BlockCoord d) : ℝ) * mixTerms_pairFinalAmp C nu d ell L n m)) := by
      refine hXO.of_abs_le fun omega => ?_
      rw [abs_of_nonneg (le_max_right (X omega) 0)]
      exact max_le (le_abs_self (X omega)) (abs_nonneg (X omega))
    have hmul := habs.const_mul hKnn
    have heq : (fun omega => K * max (X omega) 0) = (fun omega => max (X omega) 0 * K) := by
      funext omega; ring
    rw [heq] at hmul
    have hamp_eq :
        K * (gammaTriangleConst ((1 : ℝ) / 3) *
          ((Fintype.card (BlockCoord d × BlockCoord d) : ℝ) * mixTerms_pairFinalAmp C nu d ell L n m)) =
        ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (ell : ℝ) *
          (gammaTriangleConst ((1 : ℝ) / 3) *
            ((Fintype.card (BlockCoord d × BlockCoord d) : ℝ) * mixTerms_pairFinalAmp C nu d ell L n m)) := by
      rw [hKdef]
    rwa [hamp_eq] at hmul
  · intro omega p q
    show 2 * mixTerms_avgTerm nu omega ell L n m P p q ≤
        max (X omega) 0 * K *
          (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
            blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q))
    have hb := hXbd omega p q
    have hXle : X omega * (blockVecDot p p + blockVecDot q q) ≤
        max (X omega) 0 * (blockVecDot p p + blockVecDot q q) := by
      have hpq_nn : (0 : ℝ) ≤ blockVecDot p p + blockVecDot q q :=
        add_nonneg (blockVecDot_nonneg p) (blockVecDot_nonneg q)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpq_nn
    have hcrude_p := mixTerms_crudeEllipticity d hnu hnu1 P hPrefix hJ2 hJ3 hJ4 ell n hell1 p
    have hcrude_q := mixTerms_crudeEllipticity d hnu hnu1 P hPrefix hJ2 hJ3 hJ4 ell n hell1 q
    have hXmax_nn : 0 ≤ max (X omega) 0 := le_max_right _ _
    have hstep :
        max (X omega) 0 * (blockVecDot p p + blockVecDot q q) ≤
          max (X omega) 0 * K *
            (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
              blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
      have hpqle : blockVecDot p p + blockVecDot q q ≤
          K * (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
            blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
        have hAell_eq : (mixTerms_Aell nu ell P (n : ℤ) : BlockMat d) =
            annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ))) := rfl
        rw [hAell_eq, hKdef]
        linarith only [hcrude_p, hcrude_q]
      calc max (X omega) 0 * (blockVecDot p p + blockVecDot q q)
          ≤ max (X omega) 0 *
              (K * (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q))) :=
            mul_le_mul_of_nonneg_left hpqle hXmax_nn
        _ = max (X omega) 0 * K *
              (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by ring
    linarith only [hb, hXle, hstep]

end

end SuperdiffusionCLT.Section4.Mixing
