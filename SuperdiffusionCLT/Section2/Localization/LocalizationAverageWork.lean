/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Blocks
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeEllipticity
public import SuperdiffusionCLT.Section2.Cutoff.CoefficientCutoffAPI
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Section2.Cutoff.Finite

/-!
# The averaged gauged comparison `l.localization.average`

The statement `SuperdiffusionCLT.Frozen.Section2.localization_average`
(the paper's `l.localization.average`) is the averaged gauged comparison.  This module states
its conclusion with every input as a named hypothesis, isolates the one
analytic premise the statement actually needs, and discharges the rest.

## The printed statement

> **Lemma (Averaged gauged comparison).** Let `m,n,ℓ,L ∈ ℕ` satisfy
> `n ≤ ℓ ≤ m` and `L ≥ ℓ`.  For each `z ∈ 3^nℤ^d ∩ cu_m`, set
> `h_z := (k_L − k_ℓ)_{z+cu_n}`.  Then, for every `P ∈ ℝ^{2d}`,
> ```
> | ⨍_{z ∈ 3^nℤ^d ∩ cu_m} P·(bfA_L(z+cu_n) − G_{−h_z}^t bfAhom_ℓ(cu_n) G_{−h_z}) P |
>  ≤ O_{Γ_{1/3}}( C ν^{−3} |P|² ( 1_{L>ℓ} L 3^{−(ℓ−n)}
>      + (1∨ℓ)(1∨L)(1∨(m−n)) 3^{−(d/2)(m−ℓ)} ) )`,
> ```
> for a constant `C(d) < ∞`.

The formal statement renders this as `∃ C` outermost, then `∀ nu ∈ (0,1]`,
`∀` law `P` with `ShellLawPrefix`/`J1V2`/`J2`/`J3`/`J4`, `∀ m n l L` with
`n ≤ l ≤ m ≤ L`, `∀ Pvec : BlockVec d`, then a witness
`∃ X : ShellSeq d → ℝ` with `Measurable X ∧ X = O_{Γ_{1/3}}(·) ∧ ∀ omega,
|LHS omega| ≤ X omega`.  Its conclusion is reproduced verbatim in
`localization_average_of_orlicz` below, with the outer `∀`/`→` binders turned
into named hypotheses (the single `∃ C` is likewise named).

## What is discharged here, and what is not

The three conjuncts of the conclusion are `Measurable X`, the weak-Orlicz
tail `IsBigO … X ·`, and the pointwise comparison `|LHS| ≤ X`.  With the
canonical witness `X := fun omega => |LHS omega|` the pointwise conjunct is
`le_refl` and the tail conjunct is the statement's entire analytic content.  The
remaining technical conjunct --- measurability of the averaged comparison --- is
**proved** here as `measurable_averagedGaugeComparison`, so
`localization_average_of_orlicz` carries exactly one hypothesis: the weak-Orlicz
bound `IsBigO P.toMeasure (gammaSigma (1/3)) LHS A` at the printed amplitude `A`.
That bound is the analytic content of the statement; it is the object of the
printed proof and is not proved in this module.

All of `IsBigO` is a tail-measure relation (`Homogenization.IndependentSums.
IsBigO`), so the witness form and the printed `O_{Γ_{1/3}}` form agree once the
comparison is measurable; `localization_average_of_orlicz` is the precise
statement of that agreement at the printed amplitude, so the formal conclusion is neither
stronger nor weaker than the printed estimate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The printed amplitude and the printed averaged comparison -/

/-- The printed amplitude of `e.localization.average.oneshot`, verbatim from the
statement:
`C ν^{−3} |P|² ( 1_{L>ℓ} L 3^{−(ℓ−n)}
  + (1∨ℓ)(1∨L)(1∨(m−n)) 3^{−(d/2)(m−ℓ)} )`. -/
noncomputable def localizationAverageEnvelope (C nu : ℝ) (l L m n : ℕ) (Pvec : BlockVec d) : ℝ :=
  C * nu ^ (-(3 : ℝ)) * blockVecDot Pvec Pvec *
    ((if l < L then
          (L : ℝ) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ))
        else 0) +
      max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))))

/-- The averaged gauged comparison of `e.localization.average.oneshot`, verbatim from the
statement: the normalized lattice average over `3^nℤ^d ∩ cu_m` of
`P·(bfA_L(z+cu_n) − G_{−h_z}^t bfAhom_ℓ(cu_n) G_{−h_z})P`, with the lattice
realized as `descendantsAtDepth (originCube d m) (m−n)`, `h_z` as the volume
average of the finite shell increment on `z + cu_n`, and the printed matrix
difference written through
`ofFullBlockMat (toFullBlockMat · − toFullBlockMat ·)`. -/
noncomputable def averagedGaugeComparison (nu : ℝ) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m n : ℕ) (Pvec : BlockVec d)
    (omega : ShellSeq d) : ℝ :=
  ((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
      blockVecDot Pvec
        (blockMatVecMul
          (ofFullBlockMat
            (toFullBlockMat
                (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) -
              toFullBlockMat
                (blockMatMul
                  (blockMatTranspose
                    (blockG
                      (-volumeAverageMat (cubeSet R)
                        (fun y => finiteShellIncrement omega l L y))))
                  (blockMatMul
                    (annealedBlockMatrix nu l P
                      (cubeSet (originCube d (n : ℤ))))
                    (blockG
                      (-volumeAverageMat (cubeSet R)
                        (fun y => finiteShellIncrement omega l L y)))))))
          Pvec)

/-! ## Measurability of the averaged comparison

The raw carrier `BlockMat d` has no `MeasurableSpace` instance, so measurability
is read off the scalar entries `blockMatEntry`.  The four block operations
composing the comparison are closed under entrywise measurability, and the two
base carriers are measurable by the engines above. -/

/-- Entrywise measurability of a `BlockMat`-valued observable. -/
private def MeasBlockEntries (M : ShellSeq d → BlockMat d) : Prop :=
  ∀ α β : BlockCoord d, Measurable (fun omega => blockMatEntry (M omega) α β)

private theorem measBlockEntries_const (H : BlockMat d) :
    MeasBlockEntries (fun _ : ShellSeq d => H) :=
  fun _ _ => measurable_const

/-- `toFullBlockMat` reads a block matrix off entrywise. -/
private theorem toFullBlockMat_apply (A : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat A α β = blockMatEntry A α β := by
  cases α <;> cases β <;> rfl

private theorem blockMatEntry_blockG_upperLeft (g : Mat d) (i j : Fin d) :
    blockMatEntry (blockG g) (Sum.inl i) (Sum.inl j) = (1 : Mat d) i j := rfl

private theorem blockMatEntry_blockG_upperRight (g : Mat d) (i j : Fin d) :
    blockMatEntry (blockG g) (Sum.inl i) (Sum.inr j) = 0 := rfl

private theorem blockMatEntry_blockG_lowerLeft (g : Mat d) (i j : Fin d) :
    blockMatEntry (blockG g) (Sum.inr i) (Sum.inl j) = g i j := rfl

private theorem blockMatEntry_blockG_lowerRight (g : Mat d) (i j : Fin d) :
    blockMatEntry (blockG g) (Sum.inr i) (Sum.inr j) = (1 : Mat d) i j := rfl

/-- `blockG` preserves entrywise measurability. -/
private theorem measBlockEntries_blockG {g : ShellSeq d → Mat d}
    (hg : ∀ i j, Measurable (fun omega => g omega i j)) :
    MeasBlockEntries (fun omega => blockG (g omega)) := by
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa only [blockMatEntry_blockG_upperLeft] using
            (measurable_const : Measurable (fun _ : ShellSeq d => (1 : Mat d) i j))
      | inr j =>
          simpa only [blockMatEntry_blockG_upperRight] using
            (measurable_const : Measurable (fun _ : ShellSeq d => (0 : ℝ)))
  | inr i =>
      cases β with
      | inl j => simpa only [blockMatEntry_blockG_lowerLeft] using hg i j
      | inr j =>
          simpa only [blockMatEntry_blockG_lowerRight] using
            (measurable_const : Measurable (fun _ : ShellSeq d => (1 : Mat d) i j))

/-- `blockMatTranspose` preserves entrywise measurability. -/
private theorem measBlockEntries_blockMatTranspose {M : ShellSeq d → BlockMat d}
    (hM : MeasBlockEntries M) :
    MeasBlockEntries (fun omega => blockMatTranspose (M omega)) := by
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simpa only [blockMatEntry, blockMatTranspose, matTranspose, Matrix.transpose_apply]
            using hM (Sum.inl j) (Sum.inl i)
      | inr j =>
          simpa only [blockMatEntry, blockMatTranspose, matTranspose, Matrix.transpose_apply]
            using hM (Sum.inr j) (Sum.inl i)
  | inr i =>
      cases β with
      | inl j =>
          simpa only [blockMatEntry, blockMatTranspose, matTranspose, Matrix.transpose_apply]
            using hM (Sum.inl j) (Sum.inr i)
      | inr j =>
          simpa only [blockMatEntry, blockMatTranspose, matTranspose, Matrix.transpose_apply]
            using hM (Sum.inr j) (Sum.inr i)

/-- `blockMatMul` preserves entrywise measurability. -/
private theorem measBlockEntries_blockMatMul {M N : ShellSeq d → BlockMat d}
    (hM : MeasBlockEntries M) (hN : MeasBlockEntries N) :
    MeasBlockEntries (fun omega => blockMatMul (M omega) (N omega)) := by
  intro α β
  cases α with
  | inl i =>
      cases β with
      | inl j =>
          simp only [blockMatEntry, blockMatMul, Matrix.add_apply, Matrix.mul_apply]
          exact (Finset.measurable_sum _ fun k _ => (hM (Sum.inl i) (Sum.inl k)).mul
            (hN (Sum.inl k) (Sum.inl j))).add
            (Finset.measurable_sum _ fun k _ => (hM (Sum.inl i) (Sum.inr k)).mul
              (hN (Sum.inr k) (Sum.inl j)))
      | inr j =>
          simp only [blockMatEntry, blockMatMul, Matrix.add_apply, Matrix.mul_apply]
          exact (Finset.measurable_sum _ fun k _ => (hM (Sum.inl i) (Sum.inl k)).mul
            (hN (Sum.inl k) (Sum.inr j))).add
            (Finset.measurable_sum _ fun k _ => (hM (Sum.inl i) (Sum.inr k)).mul
              (hN (Sum.inr k) (Sum.inr j)))
  | inr i =>
      cases β with
      | inl j =>
          simp only [blockMatEntry, blockMatMul, Matrix.add_apply, Matrix.mul_apply]
          exact (Finset.measurable_sum _ fun k _ => (hM (Sum.inr i) (Sum.inl k)).mul
            (hN (Sum.inl k) (Sum.inl j))).add
            (Finset.measurable_sum _ fun k _ => (hM (Sum.inr i) (Sum.inr k)).mul
              (hN (Sum.inr k) (Sum.inl j)))
      | inr j =>
          simp only [blockMatEntry, blockMatMul, Matrix.add_apply, Matrix.mul_apply]
          exact (Finset.measurable_sum _ fun k _ => (hM (Sum.inr i) (Sum.inl k)).mul
            (hN (Sum.inl k) (Sum.inr j))).add
            (Finset.measurable_sum _ fun k _ => (hM (Sum.inr i) (Sum.inr k)).mul
              (hN (Sum.inr k) (Sum.inr j)))

/-- The printed difference `ofFullBlockMat (toFullBlockMat · − toFullBlockMat ·)`
preserves entrywise measurability. -/
private theorem measBlockEntries_ofFullBlockMat_sub {M N : ShellSeq d → BlockMat d}
    (hM : MeasBlockEntries M) (hN : MeasBlockEntries N) :
    MeasBlockEntries
      (fun omega => ofFullBlockMat (toFullBlockMat (M omega) - toFullBlockMat (N omega))) := by
  intro α β
  have h1 : Measurable (fun omega => blockMatEntry (M omega) α β - blockMatEntry (N omega) α β) :=
    (hM α β).sub (hN α β)
  convert h1 using 1
  funext omega
  simp only [blockMatEntry_ofFullBlockMat, toFullBlockMat_apply, Matrix.sub_apply]

/-- The averaged quadratic form of a `BlockMat`-valued observable: measurability
of `P · M P` from entrywise measurability of `M`. -/
private theorem measurable_blockVecDot_blockMatVecMul {M : ShellSeq d → BlockMat d}
    (hM : MeasBlockEntries M) (Q : BlockVec d) :
    Measurable (fun omega => blockVecDot Q (blockMatVecMul (M omega) Q)) := by
  have hul : ∀ i j, Measurable (fun omega => (M omega).upperLeft i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inl i) (Sum.inl j)
  have hur : ∀ i j, Measurable (fun omega => (M omega).upperRight i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inl i) (Sum.inr j)
  have hll : ∀ i j, Measurable (fun omega => (M omega).lowerLeft i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inr i) (Sum.inl j)
  have hlr : ∀ i j, Measurable (fun omega => (M omega).lowerRight i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inr i) (Sum.inr j)
  simp only [blockVecDot, blockMatVecMul, vecDot]
  refine Measurable.add ?_ ?_
  · refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
    exact (Finset.measurable_sum _ fun j _ => (hul i j).mul measurable_const).add
      (Finset.measurable_sum _ fun j _ => (hur i j).mul measurable_const)
  · refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
    exact (Finset.measurable_sum _ fun j _ => (hll i j).mul measurable_const).add
      (Finset.measurable_sum _ fun j _ => (hlr i j).mul measurable_const)

/-! ## The measurability theorem -/

/-- **The averaged gauged comparison is measurable in the shell sequence.**
Every entry of the two coefficient carriers is measurable — the coarse matrices
through `measurable_coarseBlockMatrix_…_apply`, the gauge arguments through
`measurable_volumeAverageMat_of_isBounded` on `measurable_finiteShellIncrement`,
and the annealed matrix is deterministic — and the finitely many block
operations, the lattice sum and the scalar quadratic form preserve this. -/
theorem measurable_averagedGaugeComparison {nu : ℝ} (hnu : 0 < nu) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m n : ℕ) (Pvec : BlockVec d) :
    Measurable (averagedGaugeComparison nu l L P m n Pvec) := by
  unfold averagedGaugeComparison
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun R _ => ?_
  refine measurable_blockVecDot_blockMatVecMul ?_ Pvec
  have hC : MeasBlockEntries
      (fun omega => coarseBlockMatrix (cubeSet R)
        (coefficientCutoff nu omega L).toCoeffField) := by
    intro α β
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            exact
              (SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperLeft_apply
                (A := fun omega => coefficientCutoff nu omega L)
                (measurable_coefficientCutoff nu L)
                (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) R i j)
        | inr j =>
            exact
              (SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperRight_apply
                (A := fun omega => coefficientCutoff nu omega L)
                (measurable_coefficientCutoff nu L)
                (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) R i j)
    | inr i =>
        cases β with
        | inl j =>
            exact
              (SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_lowerLeft_apply
                (A := fun omega => coefficientCutoff nu omega L)
                (measurable_coefficientCutoff nu L)
                (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) R i j)
        | inr j =>
            exact
              (SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_lowerRight_apply
                (A := fun omega => coefficientCutoff nu omega L)
                (measurable_coefficientCutoff nu L)
                (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) R i j)
  have hg : ∀ i j, Measurable
      (fun omega => (-volumeAverageMat (cubeSet R)
        (fun y => finiteShellIncrement omega l L y)) i j) := by
    intro i j
    have hv : Measurable (fun omega => volumeAverageMat (cubeSet R)
        (fun y => finiteShellIncrement omega l L y)) :=
      measurable_volumeAverageMat_of_isBounded (isBounded_cubeSet R) (measurableSet_cubeSet R)
        (measurable_finiteShellIncrement l L)
    have hvij : Measurable (fun omega => volumeAverageMat (cubeSet R)
        (fun y => finiteShellIncrement omega l L y) i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hv)
    exact hvij.neg
  have hG : MeasBlockEntries
      (fun omega => blockG (-volumeAverageMat (cubeSet R)
        (fun y => finiteShellIncrement omega l L y))) :=
    measBlockEntries_blockG hg
  have hH : MeasBlockEntries
      (fun _ : ShellSeq d => annealedBlockMatrix nu l P
        (cubeSet (originCube d (n : ℤ)))) :=
    measBlockEntries_const _
  exact measBlockEntries_ofFullBlockMat_sub hC
    (measBlockEntries_blockMatMul (measBlockEntries_blockMatTranspose hG)
      (measBlockEntries_blockMatMul hH hG))

/-! ## Non-vacuity of the conclusion

At `Pvec = 0` the averaged comparison and its printed amplitude both vanish, and
the conclusion holds with the witness `X = 0` for every constant `C` and every
law --- so the statement is satisfied, its Orlicz premise is inhabited, and
the reduction above is not vacuous. -/

private theorem blockVecDot_zero_left (Y : BlockVec d) :
    blockVecDot (0 : BlockVec d) Y = 0 := by
  have h : (0 : BlockVec d) = (0 : ℝ) • Y := (zero_smul ℝ Y).symm
  rw [h, blockVecDot_smul_left, zero_mul]

/-- The averaged comparison vanishes at `Pvec = 0`. -/
theorem averagedGaugeComparison_zero (nu : ℝ) (l L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (m n : ℕ) :
    averagedGaugeComparison nu l L P m n (0 : BlockVec d) = 0 := by
  funext omega
  unfold averagedGaugeComparison
  simp only [blockVecDot_zero_left, Finset.sum_const_zero, mul_zero, Pi.zero_apply]

/-! ## The conclusion with named hypotheses -/

/-- **The conclusion of `localization_average`, verbatim,
with every input a named hypothesis.**  The outer `∃ C` and the `∀`/`→`
binders of `SuperdiffusionCLT.Frozen.Section2.localization_average` are
turned into the named binders below, in the same order; the witness form
`∃ X, Measurable X ∧ X = O_{Γ_{1/3}}(·) ∧ ∀ omega, |LHS omega| ≤ X omega` is
unchanged, with `LHS` the `averagedGaugeComparison` and the amplitude the
`localizationAverageEnvelope`.

The single non-structural hypothesis is `hOrlicz`: the printed estimate
`LHS = O_{Γ_{1/3}}(A)`, i.e. the analytic content of the printed proof.  With
the witness `X := fun omega => |LHS omega|` the measurability conjunct is
`measurable_averagedGaugeComparison` and the pointwise conjunct is `le_refl`. -/
theorem localization_average_of_orlicz {C nu : ℝ} (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P) (_hJ2 : ShellLawJ2 d P)
    (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
    (m n l L : ℕ) (_hnl : n ≤ l) (_hlm : l ≤ m) (_hlL : l ≤ L)
    (Pvec : BlockVec d)
    (hOrlicz : IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma ((1 : ℝ) / 3))
      (averagedGaugeComparison nu l L P m n Pvec)
      (localizationAverageEnvelope C nu l L m n Pvec)) :
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 3)) X
        (localizationAverageEnvelope C nu l L m n Pvec) ∧
      ∀ omega : ShellSeq d,
        |averagedGaugeComparison nu l L P m n Pvec omega| ≤ X omega :=
  ⟨fun omega => |averagedGaugeComparison nu l L P m n Pvec omega|,
    (Continuous.measurable continuous_abs).comp
      (measurable_averagedGaugeComparison hnu l L P m n Pvec),
    by simpa only [IndependentSums.IsBigO, abs_abs] using hOrlicz,
    fun _ => le_refl _⟩

end SuperdiffusionCLT.Section2.Localization
