/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Localization

/-!
# The shell window dominates its pointwise values and the volume-average
oscillation of the finite shell increment

The statement `Frozen.Section2.cutoff_localization` (`l.localization`)
involves two deterministic window quantities: the `L^∞(cu_n)` window of the shell
increment, the carrier `Section3.Terms.anchorDerivSup`, and the
volume-average-centered increment
`finiteShellIncrement omega m L - (finiteShellIncrement omega m L)_U`.  This
module proves the two deterministic inputs of the window part of the printed
proof, in the exact shapes the statement uses.

* `matrixDerivativeNorm_sum_le_anchorDerivSup` (first input): the window is a
  supremum over the open cube `cu_n` of the exact induced norm of the summed
  shell derivative, and the zero branch of its defining `Option` range makes the
  range bounded above, so every pointwise value on `cu_n` is at most the
  carrier.  The upper bound of the range is the gauge
  `upperShellDerivGauge n m L` of `e.nabla.kmn.Linfty`, so no compactness
  argument is needed.
* `matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le` (second input):
  the increment-level volume-average oscillation, the deterministic
  half of `e.Tsizebounds` and the `incU`-centering used by
  the third clause of the statement.  The proof centers at the origin: both `x` and
  every `y ∈ U` lie in `cu_n`, so the mean-value estimate
  `matrixOperatorNorm_finiteShellIncrement_sub_center_le` bounds the pairs
  `inc(y) - inc(0)` and `inc(x) - inc(0)` by the gauge times the radius
  `√d 3^n / 2` of `cu_n`; the average is within the same bound of every value
  entrywise (`abs_volumeAverage_le`), and the entrywise-to-operator conversion
  `matrixOperatorNorm_le_of_entry_bound` gives the displayed constant.

## Main definitions

* `matrixOperatorNorm_diamConst`: the dimensional constant `d³ √d` of the
  increment-level volume-average oscillation.

## Main results

* `matrixDerivativeNorm_sum_le_anchorDerivSup`: the window dominates
  every pointwise value of the summed shell derivative on `cu_n`.
* `matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le`: on any
  Chapter 2 domain inside `cu_n`, the finite shell increment is within
  `C(d) 3^n` times the upper-shell gauge of its volume average, in the exact
  operator norm of the anchor's centering.

## References

* The window part of the printed proof of `l.localization`.
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
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The window dominates its pointwise values -/

/-- **The window dominates every pointwise value on `cu_n`** (the
deterministic input the printed proof reads off the `L^∞(cu_n)` window
of the statement): the defining range of
`Section3.Terms.anchorDerivSup` contains the value at every point of the open
cube and is bounded above by the upper-shell gauge
`upperShellDerivGauge n m L` (`e.nabla.kmn.Linfty`), so the carrier dominates
each pointwise value with no continuity argument. -/
theorem matrixDerivativeNorm_sum_le_anchorDerivSup (m L n : ℕ) (omega : ShellSeq d)
    (x : Vec d) (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc m L, ShellField.deriv (omega k) x) ≤
      anchorDerivSup m L n omega := by
  have hval : ∀ o : Option {y : Vec d // y ∈ openCubeSet (originCube d (n : ℤ))},
      (match o with
        | none => 0
        | some y => ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc m L, ShellField.deriv (omega k) y.1)) ≤
        upperShellDerivGauge n m L omega := by
    intro o
    cases o with
    | none => exact upperShellDerivGauge_nonneg n m L omega
    | some y =>
      exact matrixDerivativeNorm_sum_shellDeriv_le_upperShellDerivGauge omega n m L y.2
  have hbdd : BddAbove (Set.range fun o :
      Option {x : Vec d // x ∈ openCubeSet (originCube d (n : ℤ))} =>
    match o with
    | none => 0
    | some x => ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc m L, ShellField.deriv (omega k) x.1)) :=
    ⟨upperShellDerivGauge n m L omega, by
      rintro r ⟨o, rfl⟩
      exact hval o⟩
  rw [anchorDerivSup_eq]
  exact le_csSup hbdd ⟨some ⟨x, hx⟩, rfl⟩

/-! ## The increment-level volume-average oscillation -/

/-- The dimensional constant of the increment-level volume-average oscillation:
each entry of `inc(x) - (inc)_U` is at most `2 d² 3^n/2 ·` the gauge, and the
operator norm is at most `d` times the largest entry
(`matrixOperatorNorm_le_of_entry_bound`), i.e. `d³ √d`. -/
def matrixOperatorNorm_diamConst (d : ℕ) : ℝ := (d : ℝ) ^ 3 * Real.sqrt d

theorem matrixOperatorNorm_diamConst_nonneg (d : ℕ) :
    0 ≤ matrixOperatorNorm_diamConst d := by
  unfold matrixOperatorNorm_diamConst
  positivity

private theorem matrixOperatorNorm_neg (A : Mat d) :
    matrixOperatorNorm (-A) = matrixOperatorNorm A := by
  simp only [matrixOperatorNorm, map_neg, norm_neg]

private theorem matrixOperatorNorm_sub_comm (A B : Mat d) :
    matrixOperatorNorm (A - B) = matrixOperatorNorm (B - A) := by
  rw [show B - A = -(A - B) from (neg_sub A B).symm, matrixOperatorNorm_neg]

/-- **The increment-level volume-average oscillation** (the deterministic half
of `e.Tsizebounds`): on a
Chapter 2 domain contained in the centred cube `cu_n`, the finite shell
increment `inc = k_L - k_m` is within `C(d) 3^n` times the upper-shell gauge
`∑_{k ∈ (m, L]} ‖∇ j_k‖_{L^∞(cu_n)}` of its volume average `(inc)_U`, in the
exact operator norm, at every point of `U`.

Both `x` and every `y ∈ U` lie in `cu_n`, so the mean-value estimate
`matrixOperatorNorm_finiteShellIncrement_sub_center_le` bounds the pairs
`inc(z) - inc(0)` by `d²` gauge `|z| ≤ d² gauge √d 3^n / 2`; the pairs
`inc(y) - inc(x)` are then within twice that, hence so is every entry of
`inc(x) - (inc)_U` (`abs_volumeAverage_le`), and
`matrixOperatorNorm_le_of_entry_bound` converts the entry bound. -/
theorem matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le
    (omega : ShellSeq d) (m L n : ℕ)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) :
    matrixOperatorNorm (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) ≤
      matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        upperShellDerivGauge n m L omega := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hUtop : volume (U : Set (Vec d)) ≠ ⊤ := volume_ne_top_of_isBounded hUb
  have hUpos : volume (U : Set (Vec d)) ≠ 0 :=
    (U.isOpen.measure_pos volume U.nonempty).ne'
  have hgg : 0 ≤ upperShellDerivGauge n m L omega :=
    upperShellDerivGauge_nonneg n m L omega
  have hR : (0 : ℝ) ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) := by positivity
  -- the half-diameter of `cu_n` times the gauge, squared dimension
  set g : ℝ := (d : ℝ) ^ 2 * (upperShellDerivGauge n m L omega *
      (Real.sqrt d * ((3 : ℝ) ^ n / 2))) with hgdef
  have hg0 : 0 ≤ g := by
    rw [hgdef]
    exact mul_nonneg (sq_nonneg (d : ℝ)) (mul_nonneg hgg hR)
  have hxR : vecNorm x ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) :=
    vecNorm_le_of_mem_openCubeSet_originCube (hU hx)
  have hx0 : matrixOperatorNorm (finiteShellIncrement omega m L x -
      finiteShellIncrement omega m L 0) ≤ g := by
    refine (matrixOperatorNorm_finiteShellIncrement_sub_center_le omega n m L
      (hU hx)).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxR hgg)
      (sq_nonneg (d : ℝ))
  have hpair : ∀ y ∈ (U : Set (Vec d)),
      matrixOperatorNorm (finiteShellIncrement omega m L y -
        finiteShellIncrement omega m L x) ≤ 2 * g := by
    intro y hy
    have hyR : vecNorm y ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) :=
      vecNorm_le_of_mem_openCubeSet_originCube (hU hy)
    have hy0 : matrixOperatorNorm (finiteShellIncrement omega m L y -
        finiteShellIncrement omega m L 0) ≤ g := by
      refine (matrixOperatorNorm_finiteShellIncrement_sub_center_le omega n m L
        (hU hy)).trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyR hgg)
        (sq_nonneg (d : ℝ))
    have hcomm : matrixOperatorNorm (finiteShellIncrement omega m L 0 -
        finiteShellIncrement omega m L x) ≤ g := by
      rw [matrixOperatorNorm_sub_comm]
      exact hx0
    have htri := matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub
      (finiteShellIncrement omega m L y - finiteShellIncrement omega m L x)
      (finiteShellIncrement omega m L y - finiteShellIncrement omega m L 0)
    rw [sub_sub_sub_cancel_left] at htri
    linarith only [htri, hy0, hcomm]
  -- the entrywise bound of the volume-average-centered increment
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
  -- the operator-norm conversion and the constant
  have h2g0 : 0 ≤ 2 * g := by linarith only [hg0]
  refine (matrixOperatorNorm_le_of_entry_bound _ h2g0 hentry).trans ?_
  have hkey : (d : ℝ) * (2 * g) = matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
      upperShellDerivGauge n m L omega := by
    rw [hgdef, matrixOperatorNorm_diamConst]
    ring
  rw [hkey]

end

end SuperdiffusionCLT.Section2.Localization