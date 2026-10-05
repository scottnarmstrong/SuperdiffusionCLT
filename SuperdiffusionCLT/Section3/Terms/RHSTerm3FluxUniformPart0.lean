/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# The block weight of the flux chain

The printed flux chain of `e.RHS.term3.B` passes through the per-cube weight

`∑_{j=-∞}^{n} 3^{j-n} max_{z' ∈ z + 3^j ℤ^d ∩ cu_n} |b_{L'}(z' + cu_j)|^{3/4}`.

Indexing by the depth `k = n - j` below the scale-`n` cube `R = z + cu_n`, the
sub-cubes `z' + cu_j` are the members of `descendantsAtDepth R k`, and
`|b_{L'}(Q)|` is `translatedBlockNorm nu L' omega Q`.

* `fluxUniformBlockMax` is the depth-`k` block maximum;
* `fluxUniformBlockWeightE` is the printed weighted series, summed in `ℝ≥0∞`
  so that it is defined without a summability premise;
* `fluxUniformBlockWeight` is its real value at the cutoff `L' = S.LPrime`, in
  the argument order of the `blockWeight` binder of `fluxUniform_of_gaps`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ}

/-- `max_{Q ∈ descendantsAtDepth R k} |b_L(Q)|`, the depth-`k` block maximum. -/
def fluxUniformBlockMax (nu : ℝ) (L : ℕ) (omega : ShellSeq d) (R : TriadicCube d)
    (k : ℕ) : ℝ≥0 :=
  (descendantsAtDepth R k).sup fun Q => (translatedBlockNorm nu L omega Q).toNNReal

/-- The printed weighted series `∑_k 3^{-k} (max_{depth k} |b_L|)^{3/4}`, in `ℝ≥0∞`. -/
def fluxUniformBlockWeightE (nu : ℝ) (L : ℕ) (omega : ShellSeq d) (R : TriadicCube d) :
    ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ))) *
    ((fluxUniformBlockMax nu L omega R k : ℝ≥0∞) ^ ((3 : ℝ) / 4))

/-- The block weight of the flux chain at the cutoff `L' = S.LPrime`. -/
def fluxUniformBlockWeight (nu : ℝ) (S : ScaleSelection)
    (_P : ProbabilityMeasure (ShellSeq d)) (_e : Vec d) (omega : ShellSeq d)
    (R : TriadicCube d) : ℝ :=
  (fluxUniformBlockWeightE nu S.LPrime omega R).toReal

/-- The block weight is nonnegative. -/
theorem fluxUniformBlockWeight_nonneg (nu : ℝ) (S : ScaleSelection)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) (omega : ShellSeq d)
    (R : TriadicCube d) : 0 ≤ fluxUniformBlockWeight nu S P e omega R :=
  ENNReal.toReal_nonneg

/-- Each block norm at depth `k` is bounded by the depth-`k` maximum. -/
theorem translatedBlockNorm_le_fluxUniformBlockMax (nu : ℝ) (L : ℕ) (omega : ShellSeq d)
    (R : TriadicCube d) {k : ℕ} {Q : TriadicCube d} (hQ : Q ∈ descendantsAtDepth R k) :
    translatedBlockNorm nu L omega Q ≤ (fluxUniformBlockMax nu L omega R k : ℝ) := by
  have h := Finset.le_sup (f := fun Q => (translatedBlockNorm nu L omega Q).toNNReal) hQ
  have h' : ((translatedBlockNorm nu L omega Q).toNNReal : ℝ) ≤
      (fluxUniformBlockMax nu L omega R k : ℝ) := by exact_mod_cast h
  exact (Real.le_coe_toNNReal _).trans h'

end

end SuperdiffusionCLT.Section3.Terms
