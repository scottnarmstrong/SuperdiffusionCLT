/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.DecomposeInstance
public import SuperdiffusionCLT.Section4.Mixing.Term1PolarizedBound
public import SuperdiffusionCLT.Section4.Mixing.Term2ScaleComparison
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# `p.mixing.P.three.prime#combine-terms-bound`

In the proof of
Proposition `p.mixing.P.three.prime`: "Combining the previous estimates with
the case `p = 2` of `e.kmn.bounds`, we obtain" the `ℓ`-normalized bound on
`bfA_L(z+cu_n) - bfAhom_ℓ(cu_n)`, `avg`-ed over `z ∈ 3^n ℤ^d ∩ cu_m`, with
three Orlicz terms (`Γ_2`, `Γ_1`, `Γ_{1/3}`), matching the shape of the statement in
`Frozen.Section4.mixing_below_cutoff` but at the auxiliary scale
`ℓ` in place of `L`.

This file supplies the assembly step: the decomposition of
`DecomposeInstance.lean` (fully proved) splits the target quantity into the
localization-term average and the gauge-term average; the printed bound on
each summand is taken as a named hypothesis, copying `p.mixing.P.three.prime
#term1-bound` (the polarized reduction is in `Term1PolarizedBound.lean`; the further
reduction to this `Aell`-relative form uses `e.Enaught.vs.Ahom.L.crude`) and the
Cauchy-Schwarz / Jensen / `e.kmn.bounds` consequence of `p.mixing.P.three.prime
#term2-scale-comparison` (`Term2ScaleComparison.lean`'s block form combined
with `e.kmn.bounds`), exactly as printed. Given those two hypotheses, this file proves the
final assembly: the two `Γ_{1/3}` leftovers combine via the triangle
inequality `isBigO_gammaSigma_add_of_isBigO`
(`SuperdiffusionCLT/Probability/GammaSigmaHelpers.lean`), and the
decomposition turns the sum of the two hypothesis bounds into the wanted
bound on the reassembled quantity. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq finiteShellIncrement)
open SuperdiffusionCLT.Probability (isBigO_gammaSigma_add_of_isBigO)

variable {d : ℕ}

/-- The `ℓ`-cutoff annealed matrix on `cu_n`. -/
noncomputable def mixTerms_Aell (nu : ℝ) (ell : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (n : ℤ) : BlockMat d :=
  annealedBlockMatrix nu ell P (cubeSet (originCube d n))

/-- The gauge term of the decomposition, `G_{-h_R}^t Aell(cu_n) G_{-h_R} -
Aell(cu_n)`, at a descendant cube `R`. -/
noncomputable def mixTerms_gaugeTermMatrix (nu : ℝ) (omega : ShellSeq d) (ell L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (n : ℤ) (R : TriadicCube d) : BlockMat d :=
  ofFullBlockMat
    (toFullBlockMat
        (blockMatMul
          (blockMatTranspose
            (blockG (-(volumeAverageMat (cubeSet R) (fun y => finiteShellIncrement omega ell L y)))))
          (blockMatMul (mixTerms_Aell nu ell P n)
            (blockG (-(volumeAverageMat (cubeSet R) (fun y => finiteShellIncrement omega ell L y)))))) -
      toFullBlockMat (mixTerms_Aell nu ell P n))

/-- The reassembled quantity `bfA_L(z+cu_n) - Aell(cu_n)`, `avg`-ed over the
descendant cubes at depth `m - n`. -/
noncomputable def mixTerms_reassembled (nu : ℝ) (omega : ShellSeq d) (ell L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (n : ℤ) (R : TriadicCube d) : BlockMat d :=
  ofFullBlockMat
    (toFullBlockMat
        (coarseBlockMatrix (cubeSet R)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) -
      toFullBlockMat (mixTerms_Aell nu ell P n))

/-- The reassembled quantity is exactly the localization term plus the gauge
term, pointwise at each descendant cube `R`: the summand-level identity
underlying the decomposition of `DecomposeInstance.lean`. -/
theorem mixTerms_reassembled_eq_add (nu : ℝ) (omega : ShellSeq d) (ell L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (n : ℤ) (R : TriadicCube d)
    (p q : BlockVec d) :
    blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P n R) q) =
      blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P n R) q) +
        blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P n R) q) := by
  unfold mixTerms_reassembled mixTerms_localizationTermMatrix mixTerms_gaugeTermMatrix mixTerms_Aell
  rw [mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear, mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear,
    mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear]
  ring

/-- The averaged form of `mixTerms_reassembled_eq_add`: the `avg`-ed
reassembled quantity is the sum of the `avg`-ed localization term and the
`avg`-ed gauge term. -/
theorem mixTerms_reassembled_avg_eq_add (nu : ℝ) (omega : ShellSeq d) (ell L n m : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (p q : BlockVec d) :
    ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P (n : ℤ) R) q) =
      ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q) +
        ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q) := by
  rw [Finset.sum_congr rfl (fun R _ => mixTerms_reassembled_eq_add nu omega ell L P (n : ℤ) R p q),
    Finset.sum_add_distrib, mul_add]

/-- **`p.mixing.P.three.prime#combine-terms-bound`**.
Assembled from
`mixTerms_reassembled_avg_eq_add` (proved) and two hypotheses, each copying a
printed display exactly:

* `hLocBound`, the exact target of `p.mixing.P.three.prime#term1-bound`
  a single `O_{Γ1/3}(C m^{-5000})` witness bounding twice
  the localization-term average. `Term1PolarizedBound.lean` proves the
  polarized reduction of this step from `l.localization.average`;
  the further reduction to this `Aell`-relative form uses
  `e.Enaught.vs.Ahom.L.crude`.
* `hGaugeBound`, the Cauchy-Schwarz / Jensen / `e.kmn.bounds`(p=2) consequence
  of `p.mixing.P.three.prime#term2-scale-comparison`: three
  witnesses (`Γ2`, `Γ1`, `Γ1/3`) bounding twice the gauge-term average.
  `Term2ScaleComparison.lean` proves the block form and the balanced scale
  comparison this consequence rests on; the Cauchy-Schwarz/Jensen bookkeeping
  converting them into this bilinear bound (routine) is taken here as printed.

Given both, the two `Γ1/3` leftovers combine via
`isBigO_gammaSigma_add_of_isBigO`, and `mixTerms_reassembled_avg_eq_add`
turns the sum of the two hypothesis bounds into the wanted bound on the
reassembled quantity. -/
theorem mixTerms_combineTermsBound [NeZero d] {C : ℝ} (hC : 1 ≤ C) (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (ell L n m : ℕ) (hm : 1 ≤ m)
    (hLocBound :
      ∃ X3loc : ShellSeq d → ℝ,
        Measurable X3loc ∧
          IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3loc (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
          ∀ (omega : ShellSeq d) (p q : BlockVec d),
            2 *
                (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                  ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                    blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
              X3loc omega *
                (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                  blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)))
    (hGaugeBound :
      ∃ X1g X2g X3g : ShellSeq d → ℝ,
        Measurable X1g ∧
          IsBigO P.toMeasure (gammaSigma 2) X1g
            (C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) ∧
        Measurable X2g ∧
          IsBigO P.toMeasure (gammaSigma 1) X2g
            (C * ((L - ell : ℕ) : ℝ) *
              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) ∧
        Measurable X3g ∧
          IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3g (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
          ∀ (omega : ShellSeq d) (p q : BlockVec d),
            2 *
                (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                  ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                    blockVecDot p (blockMatVecMul (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
              (X1g omega + X2g omega + X3g omega) *
                (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                  blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q))) :
    ∃ X1 X2 X3 : ShellSeq d → ℝ,
      Measurable X1 ∧
        IsBigO P.toMeasure (gammaSigma 2) X1
          (C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) ∧
      Measurable X2 ∧
        IsBigO P.toMeasure (gammaSigma 1) X2
          (C * ((L - ell : ℕ) : ℝ) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) ∧
      Measurable X3 ∧
        IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3
          (gammaTriangleConst ((1 : ℝ) / 3) * (2 * (C * (m : ℝ) ^ (-(5000 : ℝ))))) ∧
        ∀ (omega : ShellSeq d) (p q : BlockVec d),
          2 *
              (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                  blockVecDot p (blockMatVecMul (mixTerms_reassembled nu omega ell L P (n : ℤ) R) q)) ≤
            (X1 omega + X2 omega + X3 omega) *
              (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  obtain ⟨X3loc, hX3locM, hX3locO, hX3locBd⟩ := hLocBound
  obtain ⟨X1g, X2g, X3g, hX1gM, hX1gO, hX2gM, hX2gO, hX3gM, hX3gO, hGaugeBd⟩ := hGaugeBound
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hamp : (0 : ℝ) < C * (m : ℝ) ^ (-(5000 : ℝ)) :=
    mul_pos hCpos (Real.rpow_pos_of_pos hmR (-(5000 : ℝ)))
  have hX3O :
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) (fun omega => X3loc omega + X3g omega)
        (gammaTriangleConst ((1 : ℝ) / 3) * (C * (m : ℝ) ^ (-(5000 : ℝ)) + C * (m : ℝ) ^ (-(5000 : ℝ)))) :=
    isBigO_gammaSigma_add_of_isBigO (by norm_num) hamp hamp hX3locO hX3gO hX3locM hX3gM
  refine ⟨X1g, X2g, fun omega => X3loc omega + X3g omega, hX1gM, hX1gO, hX2gM, hX2gO, hX3locM.add hX3gM, ?_,
    fun omega p q => ?_⟩
  · rw [show C * (m : ℝ) ^ (-(5000 : ℝ)) + C * (m : ℝ) ^ (-(5000 : ℝ)) = 2 * (C * (m : ℝ) ^ (-(5000 : ℝ))) by
      ring] at hX3O
    exact hX3O
  · rw [mixTerms_reassembled_avg_eq_add]
    have hloc := hX3locBd omega p q
    have hgauge := hGaugeBd omega p q
    dsimp only
    linarith only [hloc, hgauge]

end SuperdiffusionCLT.Section4.Mixing
