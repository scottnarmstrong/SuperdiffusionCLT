/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsD
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlock
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB

/-!
# The `Γ₁` envelope of the averaged stream tail on the centred cube

The statements concern `l.mixing.minscale` and `e.powerofGammasigma` in the paper.

The last free hypothesis of `averaged_quadratic_tail_translated`
(`Section3/Terms/RHSTerm3Inputs.lean`) is `hStreamTailCentred`, the envelope

> `|(k_ℓ − k_{L'})_{cu_n} e|² = O_{Γ₁}(C (L' − ℓ))`.

This module proves it.

## Where the printed proof performs this step

It is *not* the balanced conjunct `e.refined.localization.twoo` of
`l.mixing.minscale`.  In the sandwich reading, that conjunct is

`|s_{L,*}^{-1/2}(cu_n) (k_L − k_ℓ)_{cu_n} s_{L,*}^{-1/2}(cu_n)| ≤ X₁ + X₂`,

equivalently the relative bilinear bound

`2 p·(k_L − k_ℓ)_{cu_n} q ≤ (X₁ + X₂)(p·s_{L,*}(cu_n)p + q·s_{L,*}(cu_n)q)`.

Writing `T` for the sandwiched matrix and `s` for `s_{L,*}(cu_n)`, one has
`s^{-1/2}(k_L − k_ℓ)_{cu_n} e = T s^{1/2} e`, so the conjunct bounds only the
metric quantity

`(k_L − k_ℓ)e · s^{-1} (k_L − k_ℓ)e ≤ (X₁ + X₂)² (e·s e)`,

and says nothing about the Euclidean `|(k_L − k_ℓ)_{cu_n} e|²` without an
upper bound on `e·s_{L,*}(cu_n)e`.  No such bound is available at this
surface: the symmetric part of the cutoff coefficient is exactly `νId`
(`symmPart_restrictedCoefficientCutoff`), so the whole size of `s_{L,*}` sits
in the antisymmetric stream matrix, and the one-sided conjunct bounds
`s_{L,*}^{-1}` from above, hence `s_{L,*}` from *below* only.

The printed proof takes the Euclidean route instead: inside the proof of
`l.mixing.minscale` itself,

> `|(k_L − k_ℓ)_{cu_n}| = |∑_{i=ℓ+1}^L (j_i)_{cu_n}| ≤ O_{Γ₂}(C (L−ℓ)^{1/2})`,

"by `e.jk.spatialavg` and `a.j.iso`, ... and thus, by Proposition
`p.concentration` with `σ = 2`"; and later the same estimate is squared
by `e.powerofGammasigma` into `|h_z|² ≤ O_{Γ₁}(C(L−ℓ))`, which is exactly
`hStreamTailCentred`.  Both inputs are proved here: the unit `Γ₂` amplitude of
one shell average over a cube coarser than the shell is
`isBigO_gammaSigma_shellSpatialAverage_entry_of_le_scale`, the centring comes
from `integral_eq_zero_of_odd_under_negateSequence`, the independence across
shells is a hypothesis on the shell law, and the square-root gain is the
centred independent-sum concentration of the CoarseGraining library.

## Main results

* `volumeAverageMat_finiteShellIncrement_eq_sum`,
  `volumeAverageMat_originCube_finiteShellIncrement_eq_sum`: the coarse average
  of `k_L − k_ℓ` on `cu_n` is the finite sum of the shell spatial averages over
  the scales `(ℓ, L]`.
* `isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage`: the printed
  display `|(k_L − k_ℓ)_{cu_n}| ≤ O_{Γ₂}(C (L−ℓ)^{1/2})`.
* `isBigO_gammaSigma_translatedStreamNormSq_originCube`: `hStreamTailCentred`
  at the explicit constant `streamTailConst d`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The coarse average of a finite stream increment is a sum of shell
averages -/

/-- The normalized average of `k_L − k_ℓ = ∑_{k ∈ (ℓ, L]} j_k` over a bounded
set is the sum of the normalized averages of its shells: each entry of a
regular coefficient field is integrable on a bounded set, so the finite sum
exchanges with the integral. -/
theorem volumeAverageMat_finiteShellIncrement_eq_sum {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (omega : ShellSeq d) (l L : ℕ) :
    volumeAverageMat U (fun y => finiteShellIncrement omega l L y) =
      ∑ k ∈ Finset.Ioc l L, volumeAverageMat U fun y => shellReg omega k y := by
  ext i j
  have hint : ∀ k ∈ Finset.Ioc l L,
      IntegrableOn (fun y : Vec d => shellReg omega k y i j) U volume :=
    fun k _ => integrableOn_entry_of_isBounded (shellReg omega k) hUb i j
  have hsum : ∀ y : Vec d, finiteShellIncrement omega l L y i j =
      ∑ k ∈ Finset.Ioc l L, shellReg omega k y i j := by
    intro y
    rw [finiteShellIncrement_apply]
    simp only [Matrix.sum_apply]
  simp only [Matrix.sum_apply, volumeAverageMat, volumeAverage, hsum]
  rw [MeasureTheory.integral_finsetSum _ hint, Finset.mul_sum]

/-- **`(k_L − k_ℓ)_{cu_n} = ∑_{k=ℓ+1}^L (j_k)_{cu_n}`**, the identity the
printed proof writes in the proof of `l.mixing.minscale`: the half-open cube
average of the finite stream increment is the finite sum of the shell spatial
averages at the cube scale, centred at the origin. -/
theorem volumeAverageMat_originCube_finiteShellIncrement_eq_sum
    (omega : ShellSeq d) (nn l L : ℕ) :
    volumeAverageMat (cubeSet (originCube d (nn : ℤ)))
        (fun y => finiteShellIncrement omega l L y) =
      ∑ k ∈ Finset.Ioc l L, ShellField.shellSpatialAverage (nn : ℤ) 0 (omega k) := by
  rw [volumeAverageMat_cubeSet_eq_openCubeSet,
    volumeAverageMat_finiteShellIncrement_eq_sum
      (Section2.Carriers.isBounded_openCubeSet_originCube (nn : ℤ)) omega l L]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ShellField.shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet,
    translateSet_zero]
  rfl

/-! ## The printed display `|(k_L − k_ℓ)_{cu_n}| = O_{Γ₂}(C (L−ℓ)^{1/2})` -/

variable {P : ProbabilityMeasure (ShellSeq d)}

private theorem measurable_shellSpatialAverage_entry_at (h : ℤ) (y : Vec d) (k : ℕ)
    (i j : Fin d) :
    Measurable fun omega : ShellSeq d =>
      ShellField.shellSpatialAverage h y (omega k) i j := by
  have hrow : Measurable fun A : Mat d => A i := measurable_pi_apply i
  have hcol : Measurable fun v : Fin d → ℝ => v j := measurable_pi_apply j
  exact ((hcol.comp hrow).comp
    (ShellField.measurable_shellSpatialAverage h y)).comp
    (ShellField.measurable_shellCoordinate k)

/-- The dimension-only amplitude of the printed display
`|(k_L − k_ℓ)_{cu_n}| ≤ O_{Γ₂}(C (L−ℓ)^{1/2})`:
the matrix-entry triangle prefactor for the `d²` entries and the
independent-sum constant of the centred concentration of the CoarseGraining
library, at the unit `Γ₂`
amplitude which one shell spatial average has on a cube coarser than the
shell. -/
def streamIncrementNormConst (d : ℕ) : ℝ :=
  gammaTriangleConst 2 * (d : ℝ) ^ 2 * Book.Ch04.gammaSigmaIndependentSumConst 2

theorem streamIncrementNormConst_pos (hd : 0 < d) :
    0 < streamIncrementNormConst d := by
  have h1 : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
    SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
  have h3 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [streamIncrementNormConst]
  positivity

/-- **The printed display inside the proof of `l.mixing.minscale`**:

`|(k_L − k_ℓ)_{cu_n}| = |∑_{k=ℓ+1}^L (j_k)_{cu_n}| ≤ O_{Γ₂}(C (L−ℓ)^{1/2})`.

The shells `k ∈ (ℓ, L]` are finer than the cube scale `n`, so each entry of
each shell spatial average has the *unit* `Γ₂` amplitude of the display
`e.jk.spatialavg` (`isBigO_gammaSigma_shellSpatialAverage_entry_of_le_scale`);
they are centred (the print's appeal to `a.j.iso`) and independent, so the
centred independent-sum concentration of the CoarseGraining library — the
print's Proposition `p.concentration` at `σ = 2` — gives
the square-root gain, and the `d²` entries are summed by the generalized
triangle inequality. -/
theorem isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {nn l L : ℕ} (hnl : nn ≤ l) (hlL : l < L) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d =>
        Book.Ch02.matrixOperatorNorm
          (volumeAverageMat (cubeSet (originCube d (nn : ℤ)))
            (fun y => finiteShellIncrement omega l L y)))
      (streamIncrementNormConst d * Real.sqrt ((L - l : ℕ) : ℝ)) := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  set Y : Fin d → Fin d → ℕ → ShellSeq d → ℝ := fun i j k omega =>
    ShellField.shellSpatialAverage (nn : ℤ) 0 (omega k) i j with hYdef
  have hYmeas : ∀ i j : Fin d, ∀ k : ℕ, Measurable (Y i j k) := fun i j k =>
    measurable_shellSpatialAverage_entry_at (nn : ℤ) 0 k i j
  have hYbig : ∀ i j : Fin d, ∀ k ∈ Finset.Ioc l L,
      IsBigO P.toMeasure (gammaSigma 2) (Y i j k) 1 := by
    intro i j k hk
    have hk' : (nn : ℤ) ≤ (k : ℤ) := by
      have := (Finset.mem_Ioc.mp hk).1
      exact_mod_cast le_of_lt (lt_of_le_of_lt hnl this)
    exact isBigO_gammaSigma_shellSpatialAverage_entry_of_le_scale hPrefix hJ3 k hk' 0 i j
  have hYmean : ∀ i j : Fin d, ∀ k : ℕ,
      ∫ omega : ShellSeq d, Y i j k omega ∂P.toMeasure = 0 := by
    intro i j k
    refine integral_eq_zero_of_odd_under_negateSequence hJ4 (hYmeas i j k) ?_
    intro omega
    simp only [hYdef, ShellField.negateSequence_apply,
      ShellField.shellSpatialAverage_negate, Matrix.neg_apply]
  have hYindep : ∀ i j : Fin d,
      ProbabilityTheory.iIndepFun (fun (k : ℕ) (omega : ShellSeq d) => Y i j k omega)
        P.toMeasure := by
    intro i j
    have hmeasField : Measurable fun jf : ShellField d =>
        ShellField.shellSpatialAverage (nn : ℤ) 0 jf i j := by
      have hrow : Measurable fun A : Mat d => A i := measurable_pi_apply i
      have hcol : Measurable fun v : Fin d → ℝ => v j := measurable_pi_apply j
      exact (hcol.comp hrow).comp (ShellField.measurable_shellSpatialAverage (nn : ℤ) 0)
    exact hJ2.independent.comp
      (fun _ : ℕ => fun jf : ShellField d =>
        ShellField.shellSpatialAverage (nn : ℤ) 0 jf i j)
      (fun _ => hmeasField)
  have hcard : ((Finset.Ioc l L).card : ℝ) = ((L - l : ℕ) : ℝ) := by
    rw [Nat.card_Ioc]
  have hsqrtpos : (0 : ℝ) < Real.sqrt ((L - l : ℕ) : ℝ) := by
    have hgap : (0 : ℝ) < ((L - l : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hlL
    exact Real.sqrt_pos.2 hgap
  have hAmp : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((L - l : ℕ) : ℝ) * 1 := by
    have h2 : (0 : ℝ) < Book.Ch04.gammaSigmaIndependentSumConst 2 :=
      SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos
    positivity
  have hentry : ∀ q : Fin d × Fin d,
      IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega|)
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((L - l : ℕ) : ℝ) * 1) := by
    intro q
    have h := Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := P.toMeasure) (X := Y q.1 q.2) (s := Finset.Ioc l L) (σ := 2) (K := 1)
      (hYindep q.1 q.2) (hYmeas q.1 q.2) (Finset.nonempty_Ioc.mpr hlL)
      (by norm_num) (by norm_num) (by norm_num)
      (fun k hk => hYbig q.1 q.2 k hk) (fun k _ => hYmean q.1 q.2 k)
    rw [hcard] at h
    show IsBigOWith _ _ _ _
    simpa only [IndependentSums.IsBigO, abs_abs] using h
  have hmeasSum : ∀ q : Fin d × Fin d,
      Measurable fun omega : ShellSeq d =>
        |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega| := by
    intro q
    have hsum : Measurable fun omega : ShellSeq d =>
        ∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega :=
      Finset.measurable_sum (Finset.Ioc l L) fun k _ => hYmeas q.1 q.2 k
    simpa only [Real.norm_eq_abs] using hsum.norm
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty :=
    ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  have htriangle := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := P.toMeasure) (Finset.univ : Finset (Fin d × Fin d))
    (X := fun q (omega : ShellSeq d) => |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega|)
    (a := fun _ : Fin d × Fin d =>
      Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt ((L - l : ℕ) : ℝ) * 1)
    (σ := 2) (by norm_num) hne (fun _ _ => hAmp) (fun q _ => hentry q)
    (fun q _ => hmeasSum q)
  have hamp : gammaTriangleConst 2 *
      ∑ _q : Fin d × Fin d,
        (Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((L - l : ℕ) : ℝ) * 1) =
      streamIncrementNormConst d * Real.sqrt ((L - l : ℕ) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, streamIncrementNormConst]
    push_cast
    ring
  rw [hamp] at htriangle
  refine htriangle.of_abs_le fun omega => ?_
  have hnonneg : (0 : ℝ) ≤ ∑ q : Fin d × Fin d,
      |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega| :=
    Finset.sum_nonneg fun q _ => abs_nonneg _
  rw [abs_of_nonneg (Book.Ch02.matrixOperatorNorm_nonneg _), abs_of_nonneg hnonneg]
  have hentryEq : ∑ i : Fin d, ∑ j : Fin d,
      |volumeAverageMat (cubeSet (originCube d (nn : ℤ)))
        (fun y => finiteShellIncrement omega l L y) i j| =
      ∑ q : Fin d × Fin d, |∑ k ∈ Finset.Ioc l L, Y q.1 q.2 k omega| := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [volumeAverageMat_originCube_finiteShellIncrement_eq_sum]
    simp only [Matrix.sum_apply, hYdef]
  rw [← hentryEq]
  exact (Book.Ch02.matrixOperatorNorm_le_matrixFrobeniusNorm _).trans
    (Book.Ch02.matrixFrobeniusNorm_le_sum_abs_entries _)

/-! ## `hStreamTailCentred` -/

/-- For a unit direction `e`, the squared length of `(k_ℓ − k_{L'})_{z+cu_n} e`
is at most the squared operator norm of `(k_ℓ − k_{L'})_{z+cu_n}`. -/
theorem translatedStreamNormSq_le_sq_matrixOperatorNorm {e : Vec d}
    (he : vecNormSq e = 1) (l L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    translatedStreamNormSq l L e omega z ≤
      Book.Ch02.matrixOperatorNorm
          (volumeAverageMat (cubeSet z)
            (fun y => finiteShellIncrement omega l L y)) ^ 2 := by
  have h := Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
    (volumeAverageMat (cubeSet z) (fun y => finiteShellIncrement omega l L y)) e
  rw [he, mul_one] at h
  exact h

/-- The constant of `hStreamTailCentred`: the square of the amplitude of the
printed display `|(k_L − k_ℓ)_{cu_n}| ≤ O_{Γ₂}(C (L−ℓ)^{1/2})`, as
`e.powerofGammasigma` produces it. -/
def streamTailConst (d : ℕ) : ℝ := streamIncrementNormConst d ^ 2

theorem streamTailConst_pos (hd : 0 < d) : 0 < streamTailConst d := by
  rw [streamTailConst]
  exact pow_pos (streamIncrementNormConst_pos hd) 2

/-- **`hStreamTailCentred`** (the squared display in the proof of
`l.mixing.minscale`, and, in the same shape at the scales of `l.RHS.term3`, the
bound used in its proof): for a unit direction `e` and scales `n ≤ ℓ < L`,

`|(k_ℓ − k_L)_{cu_n} e|² = O_{Γ₁}(C (L − ℓ))`.

This is the printed display above, squared by
`e.powerofGammasigma` (`Probability.isBigO_gammaSigma_rpow_fwd` at `p = 2`,
which turns a `Γ₂` bound at amplitude `A` into a `Γ₁` bound at amplitude
`A²`), together with `|Me| ≤ |M||e|`.  It is the last free hypothesis of
`averaged_quadratic_tail_translated`. -/
theorem isBigO_gammaSigma_translatedStreamNormSq_originCube
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {nn l L : ℕ} (hnl : nn ≤ l) (hlL : l < L)
    {e : Vec d} (he : vecNormSq e = 1) :
    IsBigO P.toMeasure (gammaSigma 1)
      (fun omega : ShellSeq d =>
        translatedStreamNormSq l L e omega (originCube d (nn : ℤ)))
      (streamTailConst d * ((L - l : ℕ) : ℝ)) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  set N : ShellSeq d → ℝ := fun omega =>
    Book.Ch02.matrixOperatorNorm
      (volumeAverageMat (cubeSet (originCube d (nn : ℤ)))
        (fun y => finiteShellIncrement omega l L y)) with hNdef
  set A : ℝ := streamIncrementNormConst d * Real.sqrt ((L - l : ℕ) : ℝ) with hAdef
  have hNnonneg : ∀ omega : ShellSeq d, 0 ≤ N omega := fun omega =>
    Book.Ch02.matrixOperatorNorm_nonneg _
  have hApos : 0 < A := by
    have hsq : (0 : ℝ) < Real.sqrt ((L - l : ℕ) : ℝ) := by
      have hgap : (0 : ℝ) < ((L - l : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hlL
      exact Real.sqrt_pos.2 hgap
    rw [hAdef]
    exact mul_pos (streamIncrementNormConst_pos hd) hsq
  have hN : IsBigO P.toMeasure (gammaSigma 2) N A :=
    isBigO_gammaSigma_matrixOperatorNorm_streamIncrementAverage hPrefix hJ2 hJ3 hJ4 hnl hlL
  have hsq := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_fwd
    (mu := P.toMeasure) (X := N) (K := A) (σ := 2) (p := 2)
    (by norm_num) hApos.le hNnonneg hN
  have hsigma : (2 : ℝ) / 2 = 1 := by norm_num
  rw [hsigma] at hsq
  have hrp : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x
    have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [← hcast, Real.rpow_natCast]
  have hfun : (fun omega : ShellSeq d => N omega ^ (2 : ℝ)) =
      fun omega : ShellSeq d => N omega ^ (2 : ℕ) := by
    funext omega
    exact hrp (N omega)
  have hamp : A ^ (2 : ℝ) = streamTailConst d * ((L - l : ℕ) : ℝ) := by
    have hnn : (0 : ℝ) ≤ ((L - l : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hrp, hAdef, mul_pow, Real.sq_sqrt hnn, streamTailConst]
  rw [hfun, hamp] at hsq
  refine hsq.of_abs_le fun omega => ?_
  have hle := translatedStreamNormSq_le_sq_matrixOperatorNorm he l L omega
    (originCube d (nn : ℤ))
  rw [abs_of_nonneg (translatedStreamNormSq_nonneg l L e omega _),
    abs_of_nonneg (pow_nonneg (hNnonneg omega) 2)]
  exact hle

end

end SuperdiffusionCLT.Section3.Terms
