/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.Term1PolarizedBound
public import Homogenization.Probability.IndependentSums.Triangle
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# The uniform-witness reduction for `p.mixing.P.three.prime#term1-bound`

The printed step is "testing with `P = bfAhom_ℓ^{-1/2}(cu_n) Q`, taking the supremum over a
finite net of `|Q| = 1`".

`mixTerms_term1PolarizedBound` gives, for each FIXED test pair `(p, q)`, three
witnesses depending on `(p, q)`. This file removes that dependence: since
`(p, q) ↦ avg(p · H_R · q)` is bilinear, testing the finitely many coordinate
pairs `(blockBasis α, blockBasis β)`, `α, β : BlockCoord d` (a Fintype of
size `2d`), and combining via the finite-family Orlicz triangle inequality
gives a single witness that works for every `(p, q)` simultaneously, at the
cost of a `d`-dependent multiplicative constant. No compactness/net argument
on the continuum sphere is needed. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability (isBigO_gammaSigma_add_of_isBigO)

variable {d : ℕ}

/-- The absolute value of a measurable real-valued function is measurable. -/
private theorem mixTerms_measurable_abs {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ}
    (hf : Measurable f) : Measurable (fun x => |f x|) := by
  have : (fun x => |f x|) = fun x => max (f x) (-f x) := by
    funext x; exact abs_eq_max_neg
  rw [this]
  exact hf.max hf.neg

/-- `toFullBlockMat` and `blockMatEntry` agree pointwise. -/
private theorem mixTerms_toFullBlockMat_eq_blockMatEntry (H : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat H α β = blockMatEntry H α β := by
  cases α <;> cases β <;> rfl

/-- **Bilinear expansion in the coordinate basis.** -/
theorem mixTerms_blockVecDot_eq_sum_basis (H : BlockMat d) (p q : BlockVec d) :
    blockVecDot p (blockMatVecMul H q) =
      ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec p α * toFullBlockVec q β *
          blockVecDot (blockBasis α) (blockMatVecMul H (blockBasis β)) := by
  rw [blockVecDot_blockMatVecMul_eq_toLinearMap₂', Matrix.toLinearMap₂'_apply']
  unfold dotProduct Matrix.mulVec
  simp_rw [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [blockBasis_pairing, mixTerms_toFullBlockMat_eq_blockMatEntry]
  ring

/-- **Coordinate (Parseval) bound.** -/
theorem mixTerms_sq_toFullBlockVec_le (p : BlockVec d) (α : BlockCoord d) :
    (toFullBlockVec p α) ^ 2 ≤ blockVecDot p p := by
  rw [← dotProduct_toFullBlockVec p p]
  have hexpand : dotProduct (toFullBlockVec p) (toFullBlockVec p) =
      ∑ i : BlockCoord d, (toFullBlockVec p i) ^ 2 := by
    unfold dotProduct
    exact Finset.sum_congr rfl fun i _ => (sq (toFullBlockVec p i)).symm
  rw [hexpand]
  exact Finset.single_le_sum (fun i _ => sq_nonneg (toFullBlockVec p i)) (Finset.mem_univ α)

/-- Negating the second test vector negates the averaged bilinear value. -/
private theorem mixTerms_avg_neg_right {ι : Type*} (s : Finset ι) (H : ι → BlockMat d) (p q : BlockVec d) :
    (s.card : ℝ)⁻¹ * ∑ z ∈ s, blockVecDot p (blockMatVecMul (H z) (-q)) =
      -((s.card : ℝ)⁻¹ * ∑ z ∈ s, blockVecDot p (blockMatVecMul (H z) q)) := by
  have hpt : ∀ z ∈ s, blockVecDot p (blockMatVecMul (H z) (-q)) =
      -blockVecDot p (blockMatVecMul (H z) q) := by
    intro z _
    have hneg : blockMatVecMul (H z) (-q) = -(blockMatVecMul (H z) q) := by
      have := blockMatVecMul_smul (H z) (-1 : ℝ) q
      simpa using this
    rw [hneg]
    have := blockVecDot_smul_right p (blockMatVecMul (H z) q) (-1 : ℝ)
    simpa using this
  rw [Finset.sum_congr rfl hpt, Finset.sum_neg_distrib, mul_neg]

/-- The `avsum` cardinality-and-sum expression, abbreviated for readability. -/
noncomputable def mixTerms_avgTerm (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ell L n m : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (p q : BlockVec d) : ℝ :=
  ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      blockVecDot p (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)

/-- The "stuff" factor of `l.localization.average`'s amplitude, abbreviated. -/
noncomputable def mixTerms_stuffFactor (d ell L n m : ℕ) : ℝ :=
  (if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
    max 1 (ell : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ)))

private theorem mixTerms_stuffFactor_pos (d ell L n m : ℕ) : 0 < mixTerms_stuffFactor d ell L n m := by
  unfold mixTerms_stuffFactor
  have h1 : (0 : ℝ) ≤ if ell < L then (L : ℝ) * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0 := by
    split_ifs with h
    · positivity
    · exact le_refl 0
  have h2 : (0 : ℝ) < max 1 (ell : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) := by positivity
  linarith only [h1, h2]

/-- The common per-pair amplitude, after bumping each of the (at most six)
individual `l.localization.average` witnesses feeding a basis pair up to a
single value. -/
noncomputable def mixTerms_pairCommonAmp (C nu : ℝ) (d ell L n m : ℕ) : ℝ :=
  (|C| + 1) * nu ^ (-(3 : ℝ)) * 4 * mixTerms_stuffFactor d ell L n m

/-- The amplitude obtained after combining all six `l.localization.average`
witnesses feeding a single basis pair via two nested applications of the
two-term Orlicz triangle inequality. -/
noncomputable def mixTerms_pairFinalAmp (C nu : ℝ) (d ell L n m : ℕ) : ℝ :=
  gammaTriangleConst ((1 : ℝ) / 3) *
    (gammaTriangleConst ((1 : ℝ) / 3) *
        (gammaTriangleConst ((1 : ℝ) / 3) *
            (mixTerms_pairCommonAmp C nu d ell L n m + mixTerms_pairCommonAmp C nu d ell L n m) +
          mixTerms_pairCommonAmp C nu d ell L n m) +
      gammaTriangleConst ((1 : ℝ) / 3) *
        (gammaTriangleConst ((1 : ℝ) / 3) *
            (mixTerms_pairCommonAmp C nu d ell L n m + mixTerms_pairCommonAmp C nu d ell L n m) +
          mixTerms_pairCommonAmp C nu d ell L n m))

private theorem mixTerms_pairCommonAmp_pos (C nu : ℝ) (hnu : 0 < nu) (d ell L n m : ℕ) :
    0 < mixTerms_pairCommonAmp C nu d ell L n m := by
  unfold mixTerms_pairCommonAmp
  have hSTUFF := mixTerms_stuffFactor_pos d ell L n m
  positivity

/-- The `l.localization.average`-derived amplitude at a doubled block vector
`v`, at any `v` with `blockVecDot v v ≤ 4`, is dominated by
`mixTerms_pairCommonAmp`. -/
private theorem mixTerms_amp_le_commonAmp {C nu : ℝ} (hnu : 0 < nu) (d ell L n m : ℕ)
    {v : BlockVec d} (hv : blockVecDot v v ≤ 4) :
    C * nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m ≤
      mixTerms_pairCommonAmp C nu d ell L n m := by
  have hSTUFF := mixTerms_stuffFactor_pos d ell L n m
  have hpow : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
  have hvnn : 0 ≤ blockVecDot v v := blockVecDot_nonneg v
  have h1 : C ≤ |C| + 1 := le_trans (le_abs_self C) (by linarith only)
  have h2 : C * nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m ≤
      (|C| + 1) * nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m := by
    have hnn : 0 ≤ nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m :=
      by positivity
    calc C * nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m
        = C * (nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m) := by ring
      _ ≤ (|C| + 1) * (nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m) :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ = (|C| + 1) * nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m := by ring
  have h3 : (|C| + 1) * nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m ≤
      (|C| + 1) * nu ^ (-(3 : ℝ)) * 4 * mixTerms_stuffFactor d ell L n m := by
    have hnn : 0 ≤ (|C| + 1) * nu ^ (-(3 : ℝ)) := by positivity
    have hnn2 : 0 ≤ mixTerms_stuffFactor d ell L n m := hSTUFF.le
    calc (|C| + 1) * nu ^ (-(3 : ℝ)) * blockVecDot v v * mixTerms_stuffFactor d ell L n m
        = ((|C| + 1) * nu ^ (-(3 : ℝ)) * blockVecDot v v) * mixTerms_stuffFactor d ell L n m := by
          ring
      _ ≤ ((|C| + 1) * nu ^ (-(3 : ℝ)) * 4) * mixTerms_stuffFactor d ell L n m := by
          have := mul_le_mul_of_nonneg_left hv hnn
          exact mul_le_mul_of_nonneg_right this hnn2
      _ = (|C| + 1) * nu ^ (-(3 : ℝ)) * 4 * mixTerms_stuffFactor d ell L n m := by ring
  unfold mixTerms_pairCommonAmp
  linarith only [h2, h3]

/-! ## Norms of coordinate-basis vectors -/

/-- Every basis vector has unit Euclidean norm. -/
theorem mixTerms_blockVecDot_blockBasis_self (α : BlockCoord d) :
    blockVecDot (blockBasis α) (blockBasis α) = 1 := by
  cases α with
  | inl i =>
    show vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) + vecDot (0 : Vec d) (0 : Vec d) = 1
    rw [vecDot_single_left, vecDot_zero_left]
    simp
  | inr i =>
    show vecDot (0 : Vec d) (0 : Vec d) + vecDot (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) = 1
    rw [vecDot_single_left, vecDot_zero_left]
    simp

/-- The doubled quadratic form of the sum of two basis vectors is at most `4`. -/
theorem mixTerms_blockVecDot_blockBasis_add_le (α β : BlockCoord d) :
    blockVecDot (blockBasis α + blockBasis β) (blockBasis α + blockBasis β) ≤ 4 := by
  have hstep : blockVecDot (blockBasis α - (-(blockBasis β))) (blockBasis α - (-(blockBasis β))) ≤
      2 * (blockVecDot (blockBasis α) (blockBasis α) +
        blockVecDot (-(blockBasis β)) (-(blockBasis β))) :=
    blockVecDot_sub_self_le (blockBasis α) (-(blockBasis β))
  have heq : blockBasis α - (-(blockBasis β)) = blockBasis α + blockBasis β := by
    rw [sub_neg_eq_add]
  have hnegβ : blockVecDot (-(blockBasis β)) (-(blockBasis β)) = blockVecDot (blockBasis β) (blockBasis β) := by
    obtain ⟨b1, b2⟩ := blockBasis β
    show vecDot (-b1) (-b1) + vecDot (-b2) (-b2) = vecDot b1 b1 + vecDot b2 b2
    rw [vecDot_neg_left, vecDot_neg_right, neg_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]
  rw [heq, mixTerms_blockVecDot_blockBasis_self, hnegβ, mixTerms_blockVecDot_blockBasis_self] at hstep
  linarith only [hstep]

/-! ## The per-basis-pair absolute bound -/

/-- **The two-sided (absolute value) form of `mixTerms_term1PolarizedBound`, at
a single common amplitude, for every basis pair simultaneously.** For each
`α, β : BlockCoord d`, two applications of `mixTerms_term1PolarizedBound`
(at `(blockBasis α, blockBasis β)` and `(blockBasis α, -blockBasis β)`),
combined with `mixTerms_avg_neg_right` and bumped up to the common amplitude
`mixTerms_pairCommonAmp C nu d ell L n m` via `IsBigO.mono_scale`. -/
theorem mixTerms_term1PairAbsBound (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
            ∀ m n ell L : ℕ, n ≤ ell → ell ≤ m → ell ≤ L →
              ∀ α β : BlockCoord d,
                ∃ Y : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable Y ∧
                    IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) Y
                      (mixTerms_pairFinalAmp C nu d ell L n m) ∧
                    ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                      |2 * mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| ≤
                        Y omega := by
  obtain ⟨C, hC⟩ := mixTerms_term1PolarizedBound d
  refine ⟨C, fun nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL α β => ?_⟩
  have hPosAmp := mixTerms_pairCommonAmp_pos C nu hnu d ell L n m
  have hTri : (0 : ℝ) < gammaTriangleConst ((1 : ℝ) / 3) := by
    have h2 : (2 : ℝ) ≤ gammaGrowthConst ((1 : ℝ) / 3) := two_le_gammaGrowthConst _
    have hgpos : (0 : ℝ) < gammaGrowthConst ((1 : ℝ) / 3) := lt_of_lt_of_le (by norm_num) h2
    unfold gammaTriangleConst
    positivity
  have hnormαβ : blockVecDot (blockBasis α + blockBasis β) (blockBasis α + blockBasis β) ≤ 4 :=
    mixTerms_blockVecDot_blockBasis_add_le α β
  have hnormα : blockVecDot (blockBasis α : BlockVec d) (blockBasis α) ≤ 4 := by
    rw [mixTerms_blockVecDot_blockBasis_self]; norm_num
  have hnormβ : blockVecDot (blockBasis β : BlockVec d) (blockBasis β) ≤ 4 := by
    rw [mixTerms_blockVecDot_blockBasis_self]; norm_num
  -- First application: at (blockBasis α, blockBasis β).
  obtain ⟨X1, X2, X3, hX1m, hX1O, hX2m, hX2O, hX3m, hX3O, hbd⟩ :=
    hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL (blockBasis α) (blockBasis β)
  have hX1O' : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X1 (mixTerms_pairCommonAmp C nu d ell L n m) :=
    hX1O.mono_scale (mixTerms_amp_le_commonAmp hnu d ell L n m hnormαβ)
  have hX2O' : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X2 (mixTerms_pairCommonAmp C nu d ell L n m) :=
    hX2O.mono_scale (mixTerms_amp_le_commonAmp hnu d ell L n m hnormα)
  have hX3O' : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3 (mixTerms_pairCommonAmp C nu d ell L n m) :=
    hX3O.mono_scale (mixTerms_amp_le_commonAmp hnu d ell L n m hnormβ)
  -- Second application: at (blockBasis α, -blockBasis β).
  have hnormαβ' :
      blockVecDot (blockBasis α + -(blockBasis β)) (blockBasis α + -(blockBasis β)) ≤ 4 := by
    have hstep :
        blockVecDot (blockBasis α - blockBasis β) (blockBasis α - blockBasis β) ≤
          2 * (blockVecDot (blockBasis α) (blockBasis α) + blockVecDot (blockBasis β) (blockBasis β)) :=
      blockVecDot_sub_self_le (blockBasis α) (blockBasis β)
    rw [mixTerms_blockVecDot_blockBasis_self, mixTerms_blockVecDot_blockBasis_self,
      sub_eq_add_neg] at hstep
    linarith only [hstep]
  have hnormnegβ : blockVecDot (-(blockBasis β) : BlockVec d) (-(blockBasis β)) ≤ 4 := by
    have heq : blockVecDot (-(blockBasis β) : BlockVec d) (-(blockBasis β)) =
        blockVecDot (blockBasis β) (blockBasis β) := by
      obtain ⟨b1, b2⟩ := blockBasis β
      show vecDot (-b1) (-b1) + vecDot (-b2) (-b2) = vecDot b1 b1 + vecDot b2 b2
      rw [vecDot_neg_left, vecDot_neg_right, neg_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]
    rw [heq, mixTerms_blockVecDot_blockBasis_self]
    norm_num
  obtain ⟨X1', X2', X3', hX1m', hX1O'', hX2m', hX2O'', hX3m', hX3O'', hbd'⟩ :=
    hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL (blockBasis α) (-(blockBasis β))
  have hX1O''' :
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X1' (mixTerms_pairCommonAmp C nu d ell L n m) :=
    hX1O''.mono_scale (mixTerms_amp_le_commonAmp hnu d ell L n m hnormαβ')
  have hX2O''' :
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X2' (mixTerms_pairCommonAmp C nu d ell L n m) :=
    hX2O''.mono_scale (mixTerms_amp_le_commonAmp hnu d ell L n m hnormα)
  have hX3O''' :
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3' (mixTerms_pairCommonAmp C nu d ell L n m) :=
    hX3O''.mono_scale (mixTerms_amp_le_commonAmp hnu d ell L n m hnormnegβ)
  -- Combine all six into one witness.
  have hsum2pos : (0 : ℝ) < mixTerms_pairCommonAmp C nu d ell L n m + mixTerms_pairCommonAmp C nu d ell L n m := by
    linarith only [hPosAmp]
  have hcombo1 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure)
    (by norm_num : (0 : ℝ) < 1 / 3) hPosAmp hPosAmp hX1O' hX2O' hX1m hX2m
  have hcombo1pos : (0 : ℝ) < gammaTriangleConst ((1 : ℝ) / 3) *
      (mixTerms_pairCommonAmp C nu d ell L n m + mixTerms_pairCommonAmp C nu d ell L n m) :=
    mul_pos hTri hsum2pos
  have hcombo2 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure)
    (by norm_num : (0 : ℝ) < 1 / 3) hcombo1pos hPosAmp hcombo1 hX3O' (hX1m.add hX2m) hX3m
  have hcombo3 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure)
    (by norm_num : (0 : ℝ) < 1 / 3) hPosAmp hPosAmp hX1O''' hX2O''' hX1m' hX2m'
  have hcombo4 := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure)
    (by norm_num : (0 : ℝ) < 1 / 3) hcombo1pos hPosAmp hcombo3 hX3O''' (hX1m'.add hX2m') hX3m'
  have hcombo2pos : (0 : ℝ) < gammaTriangleConst ((1 : ℝ) / 3) *
      (gammaTriangleConst ((1 : ℝ) / 3) *
          (mixTerms_pairCommonAmp C nu d ell L n m + mixTerms_pairCommonAmp C nu d ell L n m) +
        mixTerms_pairCommonAmp C nu d ell L n m) :=
    mul_pos hTri (by linarith only [hcombo1pos, hPosAmp])
  have hcombo2abs :
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
        (fun omega => |X1 omega + X2 omega + X3 omega|)
        (gammaTriangleConst ((1 : ℝ) / 3) *
          (gammaTriangleConst ((1 : ℝ) / 3) *
              (mixTerms_pairCommonAmp C nu d ell L n m + mixTerms_pairCommonAmp C nu d ell L n m) +
            mixTerms_pairCommonAmp C nu d ell L n m)) := by
    simpa only [IndependentSums.IsBigO, abs_abs] using hcombo2
  have hcombo4abs :
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
        (fun omega => |X1' omega + X2' omega + X3' omega|)
        (gammaTriangleConst ((1 : ℝ) / 3) *
          (gammaTriangleConst ((1 : ℝ) / 3) *
              (mixTerms_pairCommonAmp C nu d ell L n m + mixTerms_pairCommonAmp C nu d ell L n m) +
            mixTerms_pairCommonAmp C nu d ell L n m)) := by
    simpa only [IndependentSums.IsBigO, abs_abs] using hcombo4
  have hcomboFinal := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure)
    (by norm_num : (0 : ℝ) < 1 / 3) hcombo2pos hcombo2pos hcombo2abs hcombo4abs
    (mixTerms_measurable_abs ((hX1m.add hX2m).add hX3m))
    (mixTerms_measurable_abs ((hX1m'.add hX2m').add hX3m'))
  have hcomboFinal' :
      IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
        (fun omega => |X1 omega + X2 omega + X3 omega| + |X1' omega + X2' omega + X3' omega|)
        (mixTerms_pairFinalAmp C nu d ell L n m) := hcomboFinal
  refine ⟨fun omega => |X1 omega + X2 omega + X3 omega| + |X1' omega + X2' omega + X3' omega|,
    (mixTerms_measurable_abs ((hX1m.add hX2m).add hX3m)).add
      (mixTerms_measurable_abs ((hX1m'.add hX2m').add hX3m')),
    hcomboFinal', fun omega => ?_⟩
  show |2 * mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| ≤
    |X1 omega + X2 omega + X3 omega| + |X1' omega + X2' omega + X3' omega|
  unfold mixTerms_avgTerm
  have hb1 := hbd omega
  have hb2 := hbd' omega
  rw [mixTerms_avg_neg_right] at hb2
  have hb1' : X1 omega + X2 omega + X3 omega ≤ |X1 omega + X2 omega + X3 omega| := le_abs_self _
  have hb2' : X1' omega + X2' omega + X3' omega ≤ |X1' omega + X2' omega + X3' omega| :=
    le_abs_self _
  have hb1'' : (0 : ℝ) ≤ |X1 omega + X2 omega + X3 omega| := abs_nonneg _
  have hb2'' : (0 : ℝ) ≤ |X1' omega + X2' omega + X3' omega| := abs_nonneg _
  rw [abs_le]
  constructor
  · nlinarith only [hb2, hb2', hb1'']
  · nlinarith only [hb1, hb1', hb2'']

/-! ## The averaged bilinear decomposition, and the final uniform bound -/

/-- The bilinear expansion holds for the `avg`-ed quantity too. -/
theorem mixTerms_avgTerm_eq_sum_basis (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ell L n m : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (p q : BlockVec d) :
    mixTerms_avgTerm nu omega ell L n m P p q =
      ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec p α * toFullBlockVec q β *
          mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β) := by
  unfold mixTerms_avgTerm
  rw [Finset.sum_congr rfl
    (fun R (_ : R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n)) =>
      mixTerms_blockVecDot_eq_sum_basis (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) p q)]
  rw [show
      (∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
          ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec p α * toFullBlockVec q β *
              blockVecDot (blockBasis α)
                (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) (blockBasis β))) =
        ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
            toFullBlockVec p α * toFullBlockVec q β *
              blockVecDot (blockBasis α)
                (blockMatVecMul (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) (blockBasis β)) by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun α _ => Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  ring

/-- **`p.mixing.P.three.prime#term1-bound`, uniform-witness reduction, `|v|²`
form.** One witness, working for every test pair `(p, q)` simultaneously.
Assembled from `mixTerms_term1PairAbsBound` (the `4d²` coordinate-pair
absolute bounds, combined via the finite-family Orlicz triangle inequality)
and `mixTerms_avgTerm_eq_sum_basis` + `mixTerms_sq_toFullBlockVec_le` +
AM-GM (the bilinear coordinate expansion). No compactness argument on the
continuum sphere is used; the coordinate Fintype `BlockCoord d × BlockCoord d`
(size `4d²`) plays the role of the "finite net" of the printed proof. -/
theorem mixTerms_term1UniformBound (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
            ∀ m n ell L : ℕ, n ≤ ell → ell ≤ m → ell ≤ L →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                  IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X
                    (gammaTriangleConst ((1 : ℝ) / 3) *
                      ((Fintype.card (BlockCoord d × BlockCoord d) : ℝ) *
                        mixTerms_pairFinalAmp C nu d ell L n m)) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (p q : BlockVec d),
                    2 * mixTerms_avgTerm nu omega ell L n m P p q ≤
                      X omega * (blockVecDot p p + blockVecDot q q) := by
  obtain ⟨C, hC⟩ := mixTerms_term1PairAbsBound d
  refine ⟨C, fun nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL => ?_⟩
  choose Yfun hYmeas hYO hYbd using hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL
  have hYconst : ∀ αβ : BlockCoord d × BlockCoord d, (0 : ℝ) < mixTerms_pairFinalAmp C nu d ell L n m := by
    intro αβ
    have hSTUFF := mixTerms_stuffFactor_pos d ell L n m
    have hpow : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
    have hCcommon : (0 : ℝ) < mixTerms_pairCommonAmp C nu d ell L n m := by
      unfold mixTerms_pairCommonAmp; positivity
    have hTri : (0 : ℝ) < gammaTriangleConst ((1 : ℝ) / 3) := by
      have h2 : (2 : ℝ) ≤ gammaGrowthConst ((1 : ℝ) / 3) := two_le_gammaGrowthConst _
      have hgpos : (0 : ℝ) < gammaGrowthConst ((1 : ℝ) / 3) := lt_of_lt_of_le (by norm_num) h2
      unfold gammaTriangleConst; positivity
    unfold mixTerms_pairFinalAmp
    have := hCcommon
    positivity
  have hsum := isBigO_finset_sum_of_isBigO_gammaSigma (μ := P.toMeasure)
    (s := (Finset.univ : Finset (BlockCoord d × BlockCoord d)))
    (X := fun αβ => Yfun αβ.1 αβ.2) (a := fun _ => mixTerms_pairFinalAmp C nu d ell L n m)
    (σ := (1 : ℝ) / 3) (by norm_num) Finset.univ_nonempty (fun αβ _ => hYconst αβ)
    (fun αβ _ => hYO αβ.1 αβ.2) (fun αβ _ => hYmeas αβ.1 αβ.2)
  have hsumEq : ∑ αβ : BlockCoord d × BlockCoord d, mixTerms_pairFinalAmp C nu d ell L n m =
      (Fintype.card (BlockCoord d × BlockCoord d) : ℝ) * mixTerms_pairFinalAmp C nu d ell L n m := by
    rw [Finset.sum_const, Finset.card_univ]
    ring
  rw [hsumEq] at hsum
  refine ⟨fun omega => ∑ αβ : BlockCoord d × BlockCoord d, Yfun αβ.1 αβ.2 omega,
    Finset.measurable_sum Finset.univ (fun αβ _ => hYmeas αβ.1 αβ.2), hsum, fun omega p q => ?_⟩
  rw [mixTerms_avgTerm_eq_sum_basis]
  have hYnnAll : ∀ α β : BlockCoord d, (0 : ℝ) ≤ Yfun α β omega := by
    intro α β
    have hbd := hYbd α β omega
    have h0 : (0 : ℝ) ≤ |2 * mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| :=
      abs_nonneg _
    linarith only [hbd, h0]
  have hstep : ∀ α β : BlockCoord d,
      toFullBlockVec p α * toFullBlockVec q β *
          mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β) ≤
        (1 / 4 : ℝ) * (blockVecDot p p + blockVecDot q q) * Yfun α β omega := by
    intro α β
    have hp2 := mixTerms_sq_toFullBlockVec_le p α
    have hq2 := mixTerms_sq_toFullBlockVec_le q β
    have hbd := hYbd α β omega
    have habs : toFullBlockVec p α * toFullBlockVec q β *
        mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β) ≤
        |toFullBlockVec p α| * |toFullBlockVec q β| *
          |mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| := by
      calc toFullBlockVec p α * toFullBlockVec q β *
          mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)
          ≤ |toFullBlockVec p α * toFullBlockVec q β *
              mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| := le_abs_self _
        _ = |toFullBlockVec p α| * |toFullBlockVec q β| *
              |mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| := by
              rw [abs_mul, abs_mul]
    have hY2 : 2 * |mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| ≤
        Yfun α β omega := by
      rw [abs_mul] at hbd
      norm_num at hbd
      exact hbd
    have hpabs : |toFullBlockVec p α| ≤ Real.sqrt (blockVecDot p p) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hp2
    have hqabs : |toFullBlockVec q β| ≤ Real.sqrt (blockVecDot q q) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hq2
    have hpqabs : |toFullBlockVec p α| * |toFullBlockVec q β| ≤
        Real.sqrt (blockVecDot p p) * Real.sqrt (blockVecDot q q) :=
      mul_le_mul hpabs hqabs (abs_nonneg _) (Real.sqrt_nonneg _)
    have hamgm : Real.sqrt (blockVecDot p p) * Real.sqrt (blockVecDot q q) ≤
        (1 / 2 : ℝ) * (blockVecDot p p + blockVecDot q q) := by
      have hsq := sq_nonneg (Real.sqrt (blockVecDot p p) - Real.sqrt (blockVecDot q q))
      have he1 : Real.sqrt (blockVecDot p p) ^ 2 = blockVecDot p p :=
        Real.sq_sqrt (blockVecDot_nonneg p)
      have he2 : Real.sqrt (blockVecDot q q) ^ 2 = blockVecDot q q :=
        Real.sq_sqrt (blockVecDot_nonneg q)
      nlinarith only [hsq, he1, he2]
    have habsY : |mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| ≤
        Yfun α β omega / 2 := by linarith only [hY2]
    calc toFullBlockVec p α * toFullBlockVec q β *
        mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)
        ≤ |toFullBlockVec p α| * |toFullBlockVec q β| *
            |mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)| := habs
      _ ≤ (Real.sqrt (blockVecDot p p) * Real.sqrt (blockVecDot q q)) * (Yfun α β omega / 2) := by
          exact mul_le_mul hpqabs habsY (abs_nonneg _)
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ ≤ ((1 / 2 : ℝ) * (blockVecDot p p + blockVecDot q q)) * (Yfun α β omega / 2) :=
          mul_le_mul_of_nonneg_right hamgm (by linarith only [hYnnAll α β])
      _ = (1 / 4 : ℝ) * (blockVecDot p p + blockVecDot q q) * Yfun α β omega := by ring
  have hfinal :
      ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec p α * toFullBlockVec q β *
            mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β) ≤
        (1 / 4 : ℝ) * (blockVecDot p p + blockVecDot q q) *
          ∑ αβ : BlockCoord d × BlockCoord d, Yfun αβ.1 αβ.2 omega := by
    calc ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec p α * toFullBlockVec q β *
            mixTerms_avgTerm nu omega ell L n m P (blockBasis α) (blockBasis β)
        ≤ ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            (1 / 4 : ℝ) * (blockVecDot p p + blockVecDot q q) * Yfun α β omega := by
          refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hstep α β
      _ = (1 / 4 : ℝ) * (blockVecDot p p + blockVecDot q q) *
            ∑ αβ : BlockCoord d × BlockCoord d, Yfun αβ.1 αβ.2 omega := by
          rw [Finset.mul_sum, ← Finset.sum_product']
          congr 1
  have hXnn : (0 : ℝ) ≤ ∑ αβ : BlockCoord d × BlockCoord d, Yfun αβ.1 αβ.2 omega :=
    Finset.sum_nonneg fun αβ _ => hYnnAll αβ.1 αβ.2
  have hpqnn : (0 : ℝ) ≤ blockVecDot p p + blockVecDot q q :=
    add_nonneg (blockVecDot_nonneg p) (blockVecDot_nonneg q)
  nlinarith only [hfinal, hXnn, hpqnn]

end SuperdiffusionCLT.Section4.Mixing
