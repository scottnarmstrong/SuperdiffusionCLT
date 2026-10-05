/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CenteredIncrementQuadratic
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Localization
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause

/-!
# The window route of the third localization conjunct

The conclusion of `Frozen.Section2.cutoff_localization` carries the
shell-derivative window

`W = anchorDerivSup m L n omega`

on the RIGHT of its inequality, multiplying `ResponseJ + ResponseJ + 2 p·q`.  The
printed proof bounds the
relative perturbation amplitude `eta = nu⁻¹ ‖k_L - k_m - (k_L - k_m)_U‖` of the
cutoff pair by `C nu⁻¹ 3^n W` in the proof of `l.localization`, i.e. by an explicit
multiple of **the window**, not of the shell gauge.

The amplitudes one might define through the *gauge*
`upperShellDerivGauge n m L omega = ∑ k ∈ Ioc m L, ‖∇ j_k‖_{L^∞(cu_n)}`, the
sum of the individual sup norms, cannot be bounded by the same number of windows: the
gauge is a sum of sups while the window is the sup of the sum, and they are not
comparable in general.  This module instead states the true domination by the window.

* `matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le_window`: the
  true domination the printed proof uses.  The centered finite shell increment,
  the exact perturbation of the cutoff pair, is within the dimensional
  constant `matrixOperatorNorm_diamConst d · 3^n` times the **window** on any
  Chapter 2 domain inside `cu_n`.  This is the window analogue of
  `matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le`
  (`ShellWindowDomination.lean`), whose gauge constant was only ever an upper
  bound for the window, and it needs NO hypothesis bounding the gauge.
* `cutoffPairThetaWindow`, `cutoffPairEtaWindow`: the amplitudes of the corrected
  route, defined from the window.  These are what the assembly multiplies by the
  window-derived response scale: the amplitude is a *product* with the window, not
  a constant.

## Main results

* `matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le_window`: the
  window domination of the centered cutoff-pair perturbation.
* `cutoffPairThetaWindow`, `cutoffPairEtaWindow`: the window amplitudes, with
  `cutoffPairThetaWindow_nonneg` and `cutoffPairEtaWindow_nonneg`.

## References

* The proof of `l.localization` in the paper, and the statement of
  `e.localization.minimizers`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The window mean-value estimate of the finite shell increment

The window `anchorDerivSup m L n omega` is exactly the supremum of the induced
norm of the summed shell derivative on `cu_n` (`matrixDerivativeNorm_sum_le_anchorDerivSup`
gives the pointwise domination).  The mean-value argument of the printed proof
of `l.localization` only ever needs that pointwise domination along the segment
from the cube centre, so it runs with the window in place of the gauge. -/

private def windowEntryCLM (i l : Fin d) : Mat d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) l).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => Fin d → ℝ) i)

@[simp] private theorem windowEntryCLM_apply (i l : Fin d) (A : Mat d) :
    windowEntryCLM i l A = A i l := rfl

/-- **The entrywise mean-value estimate with the window.**  Along the segment
from the cube centre the entries of `k_L - k_m` move by at most the window times
the Euclidean distance to the centre. -/
private theorem abs_entry_finiteShellIncrement_sub_center_le_window
    (omega : ShellSeq d) (m L n : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) (i l : Fin d) :
    |finiteShellIncrement omega m L x i l - finiteShellIncrement omega m L 0 i l| ≤
      anchorDerivSup m L n omega * vecNorm x := by
  set f : ℝ → ℝ := fun t =>
    windowEntryCLM i l (finiteShellIncrement omega m L (t • x)) with hf
  set f' : ℝ → ℝ := fun t =>
    windowEntryCLM i l
      ((∑ k ∈ Finset.Ioc m L, ShellField.deriv (omega k) (t • x)) x) with hf'
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' t) (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have hpath : HasDerivAt (fun s : ℝ => s • x) x t := by
      have h := (hasDerivAt_id t).smul_const x
      simp only [id, one_smul] at h
      exact h
    have hsum :=
      finiteShellIncrement_hasFDerivAt_sum_shellDeriv omega m L (t • x)
    have hinner : HasDerivAt (fun s : ℝ => finiteShellIncrement omega m L (s • x))
        ((∑ k ∈ Finset.Ioc m L, ShellField.deriv (omega k) (t • x)) x) t :=
      hsum.comp_hasDerivAt t hpath
    exact (((windowEntryCLM i l).hasFDerivAt).comp_hasDerivAt t
      hinner).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖f' t‖ ≤ anchorDerivSup m L n omega * vecNorm x := by
    intro t ht
    have htx : t • x ∈ openCubeSet (originCube d (n : ℤ)) :=
      smul_mem_openCubeSet_originCube ⟨ht.1, ht.2.le⟩ hx
    calc
      ‖f' t‖ =
          |((∑ k ∈ Finset.Ioc m L,
            ShellField.deriv (omega k) (t • x)) x) i l| := rfl
      _ ≤ matrixOperatorNorm
          ((∑ k ∈ Finset.Ioc m L,
            ShellField.deriv (omega k) (t • x)) x) :=
        abs_entry_le_matrixOperatorNorm _ _ _
      _ ≤ ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc m L,
              ShellField.deriv (omega k) (t • x)) * vecNorm x :=
        matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm _ _
      _ ≤ anchorDerivSup m L n omega * vecNorm x :=
        mul_le_mul_of_nonneg_right
          (matrixDerivativeNorm_sum_le_anchorDerivSup m L n omega (t • x) htx)
          (vecNorm_nonneg x)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have hf1 : f 1 = finiteShellIncrement omega m L x i l := by
    simp only [hf, one_smul]
    rfl
  have hf0 : f 0 = finiteShellIncrement omega m L 0 i l := by
    simp only [hf, zero_smul]
    rfl
  rw [hf1, hf0] at hmean
  simpa only [Real.norm_eq_abs, sub_zero, mul_one] using hmean

/-- **The exact Euclidean operator norm of the centered increment, bounded by the
window** on `cu_n`. -/
private theorem matrixOperatorNorm_finiteShellIncrement_sub_center_le_window
    (omega : ShellSeq d) (m L n : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    matrixOperatorNorm
        (finiteShellIncrement omega m L x - finiteShellIncrement omega m L 0) ≤
      (d : ℝ) ^ 2 * (anchorDerivSup m L n omega * vecNorm x) := by
  have hentries :
      ∑ i : Fin d, ∑ l : Fin d,
        |(finiteShellIncrement omega m L x -
            finiteShellIncrement omega m L 0) i l - (0 : Mat d) i l| ≤
        (d : ℝ) ^ 2 * (anchorDerivSup m L n omega * vecNorm x) := by
    calc
      ∑ i : Fin d, ∑ l : Fin d,
          |(finiteShellIncrement omega m L x -
              finiteShellIncrement omega m L 0) i l - (0 : Mat d) i l| ≤
          ∑ _i : Fin d, ∑ _l : Fin d,
            anchorDerivSup m L n omega * vecNorm x :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => by
          simpa only [Matrix.sub_apply, Matrix.zero_apply, sub_zero] using
            abs_entry_finiteShellIncrement_sub_center_le_window omega m L n hx i l
      _ = (d : ℝ) ^ 2 * (anchorDerivSup m L n omega * vecNorm x) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
        ring
  refine (matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
    (finiteShellIncrement omega m L x - finiteShellIncrement omega m L 0)
    (0 : Mat d)).trans ?_
  simpa only [matrixOperatorNorm_zero, zero_add] using hentries

/-! ## The centered increment oscillation with the window -/

private theorem window_matrixOperatorNorm_neg (A : Mat d) :
    matrixOperatorNorm (-A) = matrixOperatorNorm A := by
  simp only [matrixOperatorNorm, map_neg, norm_neg]

private theorem window_matrixOperatorNorm_sub_comm (A B : Mat d) :
    matrixOperatorNorm (A - B) = matrixOperatorNorm (B - A) := by
  rw [show B - A = -(A - B) from (neg_sub A B).symm, window_matrixOperatorNorm_neg]

/-- **The window domination of the centered cutoff-pair perturbation** (the
printed proof of `l.localization`): on a Chapter 2
domain contained in the centred cube `cu_n`, the finite shell increment is within
`C(d) 3^n` times the **window** of its volume average, in the exact operator norm
of the anchor's centering.  This is the true replacement of
`matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le`
(`ShellWindowDomination.lean`), whose constant carried the gauge
`∑_k ‖∇ j_k‖_{L^∞(cu_n)}` instead; no hypothesis on the gauge is needed. -/
theorem matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le_window
    (omega : ShellSeq d) (m L n : ℕ)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) :
    matrixOperatorNorm (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) ≤
      matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        anchorDerivSup m L n omega := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hUtop : volume (U : Set (Vec d)) ≠ ⊤ := volume_ne_top_of_isBounded hUb
  have hUpos : volume (U : Set (Vec d)) ≠ 0 :=
    (U.isOpen.measure_pos volume U.nonempty).ne'
  have hW : 0 ≤ anchorDerivSup m L n omega := anchorDerivSup_nonneg m L n omega
  have hR : (0 : ℝ) ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) := by positivity
  set g : ℝ := (d : ℝ) ^ 2 * (anchorDerivSup m L n omega *
      (Real.sqrt d * ((3 : ℝ) ^ n / 2))) with hgdef
  have hg0 : 0 ≤ g := by
    rw [hgdef]
    exact mul_nonneg (sq_nonneg (d : ℝ)) (mul_nonneg hW hR)
  have hxR : vecNorm x ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) :=
    vecNorm_le_of_mem_openCubeSet_originCube (hU hx)
  have hx0 : matrixOperatorNorm (finiteShellIncrement omega m L x -
      finiteShellIncrement omega m L 0) ≤ g := by
    refine (matrixOperatorNorm_finiteShellIncrement_sub_center_le_window omega m L n
      (hU hx)).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxR hW)
      (sq_nonneg (d : ℝ))
  have hpair : ∀ y ∈ (U : Set (Vec d)),
      matrixOperatorNorm (finiteShellIncrement omega m L y -
        finiteShellIncrement omega m L x) ≤ 2 * g := by
    intro y hy
    have hyR : vecNorm y ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) :=
      vecNorm_le_of_mem_openCubeSet_originCube (hU hy)
    have hy0 : matrixOperatorNorm (finiteShellIncrement omega m L y -
        finiteShellIncrement omega m L 0) ≤ g := by
      refine (matrixOperatorNorm_finiteShellIncrement_sub_center_le_window omega m L n
        (hU hy)).trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyR hW)
        (sq_nonneg (d : ℝ))
    have hcomm : matrixOperatorNorm (finiteShellIncrement omega m L 0 -
        finiteShellIncrement omega m L x) ≤ g := by
      rw [window_matrixOperatorNorm_sub_comm]
      exact hx0
    have htri := matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub
      (finiteShellIncrement omega m L y - finiteShellIncrement omega m L x)
      (finiteShellIncrement omega m L y - finiteShellIncrement omega m L 0)
    rw [sub_sub_sub_cancel_left] at htri
    linarith only [htri, hy0, hcomm]
  have hentry : ∀ i j : Fin d,
      |(finiteShellIncrement omega m L x -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) i j| ≤ 2 * g := by
    intro i j
    have hint : IntegrableOn (fun y => finiteShellIncrement omega m L y i j)
        (U : Set (Vec d)) volume :=
      integrableOn_entry_of_isBounded (finiteShellIncrement omega m L) hUb i j
    have h2 : (volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) i j -
        finiteShellIncrement omega m L x i j =
        volumeAverage (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y i j -
            finiteShellIncrement omega m L x i j) := by
      rw [show (volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) i j =
          volumeAverage (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y i j) from rfl,
        ← volumeAverage_sub_const hUpos hUtop hint
          (finiteShellIncrement omega m L x i j)]
    calc |(finiteShellIncrement omega m L x -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y)) i j| =
        |(volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) i j -
          finiteShellIncrement omega m L x i j| := abs_sub_comm _ _
      _ = |volumeAverage (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y i j -
              finiteShellIncrement omega m L x i j)| := by rw [h2]
      _ ≤ 2 * g := by
          refine abs_volumeAverage_le hUpos hUtop fun y hy => ?_
          exact (abs_entry_le_matrixOperatorNorm
            (finiteShellIncrement omega m L y -
              finiteShellIncrement omega m L x) i j).trans (hpair y hy)
  have h2g0 : 0 ≤ 2 * g := by linarith only [hg0]
  refine (matrixOperatorNorm_le_of_entry_bound _ h2g0 hentry).trans ?_
  have hkey : (d : ℝ) * (2 * g) = matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
      anchorDerivSup m L n omega := by
    rw [hgdef, matrixOperatorNorm_diamConst]
    ring
  rw [hkey]

/-! ## The window amplitudes of the corrected route -/

/-- The relative perturbation amplitude `θ` of the printed proof
of `l.localization`, measured through the **window** rather than through the shell
gauge: the printed `η = nu⁻¹‖k_L - k_m - (k_L - k_m)_U‖_{L^∞(U)}` is at most
this. -/
def cutoffPairThetaWindow (d : ℕ) (nu : ℝ) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  nu⁻¹ * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
    anchorDerivSup m L n omega)

/-- The sandwich amplitude `θ (1 + θ)` of the window-based cutoff pair: the
printed `D` of the proof of `l.localization` read at the window amplitude. -/
def cutoffPairEtaWindow (d : ℕ) (nu : ℝ) (n m L : ℕ) (omega : ShellSeq d) : ℝ :=
  cutoffPairThetaWindow d nu n m L omega *
    (1 + cutoffPairThetaWindow d nu n m L omega)

theorem cutoffPairThetaWindow_nonneg (nu : ℝ) (hnu : 0 < nu) (n m L : ℕ)
    (omega : ShellSeq d) :
    0 ≤ cutoffPairThetaWindow d nu n m L omega :=
  mul_nonneg (inv_nonneg.2 hnu.le)
    (mul_nonneg (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
      (anchorDerivSup_nonneg m L n omega))

theorem cutoffPairEtaWindow_nonneg (nu : ℝ) (hnu : 0 < nu) (n m L : ℕ)
    (omega : ShellSeq d) :
    0 ≤ cutoffPairEtaWindow d nu n m L omega := by
  refine mul_nonneg (cutoffPairThetaWindow_nonneg nu hnu n m L omega) ?_
  linarith only [cutoffPairThetaWindow_nonneg nu hnu n m L omega]

end

end SuperdiffusionCLT.Section2.Localization
