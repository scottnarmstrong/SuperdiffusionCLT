/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.ShellDerivLinftyNorm
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# The limiting centered stream matrix `k^U`

The proof of `l.cutoff.approximation` defines, on a bounded domain `U`,

`k^U := k - (k)_U := ∑_{k=0}^∞ (j_k - (j_k)_U)`,   `a^U := ν Id + k^U`,

the series being the one of `e.good.k` recentered so that it
converges. This module supplies the carrier `centeredStreamField` for `k^U`,
its skew-symmetry, the convergence of the series under the manuscript's own
summability hypothesis, and the identity relating it to the centered
infrared cutoff `centeredStreamCutoff` of `Section2/Cutoff/Centered.lean`.

## Convergence and the junk branch

`tsum` returns `0` off the summability event, so the carrier is total. The
junk branch is unreachable at the points of `U` under the hypothesis of
`l.cutoff.approximation`:
`summable_centeredShellTerm` proves that
`∑_k ‖∇ j_k‖_{L∞(U)} < ∞` forces absolute convergence at every `x ∈ U`. The
proof is the mean-value inequality along the segment `[x, y] ⊆ U` followed by
the averaging bound `norm_sub_volumeAverageMat_le`, so it needs `U` to be
**convex**; the manuscript prints a bounded Lipschitz domain, and the passage
from convex to Lipschitz is the `W^{1,∞}(U)` extension step of the printed
proof of `l.cutoff.approximation`, which is not formalized here. The consumers of
this carrier quantify over `Homogenization.Book.Ch02.Domain d`, which is bounded,
open and convex.

## Main definitions

* `centeredShellTerm`: the summand `j_k - (j_k)_U`.
* `centeredStreamField`: `k^U`.

## Main results

* `centeredStreamField_skew`, `centeredStreamField_skew_entry`: `k^U` is
  anti-symmetric at every point, with no hypothesis at all.
* `norm_sub_volumeAverageMat_le`: the averaging bound.
* `norm_centeredShellTerm_le`: `‖j_k(x) - (j_k)_U‖ ≤ C(U) ‖∇ j_k‖_{L∞(U)}` on a
  bounded convex `U`.
* `summable_centeredShellTerm`: convergence of the defining series on `U`.
* `centeredStreamField_sub_centeredStreamCutoff`: the difference between `k^U`
  and the level-`L` centered cutoff is the tail `∑_{k > L}`.
* `centeredStreamField_zero`: the value at the zero shell sequence.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Carriers

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The carrier -/

/-- The `k`-th centered shell term `j_k - (j_k)_U` of the proof of
`l.cutoff.approximation`. -/
def centeredShellTerm (omega : ShellSeq d) (U : Set (Vec d)) (k : ℕ)
    (x : Vec d) : Mat d :=
  shellReg omega k x - volumeAverageMat U fun y => shellReg omega k y

/-- **The limiting centered stream matrix `k^U = k - (k)_U`** of
the proof of `l.cutoff.approximation`. -/
def centeredStreamField (omega : ShellSeq d) (U : Set (Vec d)) (x : Vec d) :
    Mat d :=
  ∑' k : ℕ,
    (shellReg omega k x - volumeAverageMat U fun y => shellReg omega k y)

/-- The carrier is the sum of the centered shell terms. -/
theorem centeredStreamField_eq_tsum (omega : ShellSeq d) (U : Set (Vec d))
    (x : Vec d) :
    centeredStreamField omega U x = ∑' k : ℕ, centeredShellTerm omega U k x :=
  rfl

/-! ## Entries of a convergent matrix series -/

/-- Evaluation of a matrix at one entry, as a continuous linear map. -/
private def matEntryCLM (d : ℕ) (i k : Fin d) : Mat d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun A => A i k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun A => by
      rw [one_mul]
      exact Matrix.norm_entry_le_entrywise_sup_norm A (i := i) (j := k))

/-- Entries of a convergent series of matrices are the series of the
entries. -/
theorem tsum_matrix_apply {f : ℕ → Mat d} (hf : Summable f) (i k : Fin d) :
    (∑' n : ℕ, f n) i k = ∑' n : ℕ, f n i k :=
  ((hf.hasSum.map (matEntryCLM d i k).toAddMonoidHom
    (matEntryCLM d i k).continuous).tsum_eq).symm

/-! ## Anti-symmetry -/

/-- The volume average of one shell is anti-symmetric. -/
theorem matTranspose_volumeAverageMat_shellReg (omega : ShellSeq d)
    (U : Set (Vec d)) (k : ℕ) :
    matTranspose (volumeAverageMat U fun y => shellReg omega k y) =
      -volumeAverageMat U fun y => shellReg omega k y :=
  matTranspose_volumeAverageMat U (fun y => shellReg omega k y)
    fun y i l => ShellField.skew_entry (omega k) y i l

/-- Every centered shell term is anti-symmetric. -/
theorem centeredShellTerm_skew_entry (omega : ShellSeq d) (U : Set (Vec d))
    (k : ℕ) (x : Vec d) (i l : Fin d) :
    centeredShellTerm omega U k x i l =
      -centeredShellTerm omega U k x l i := by
  have havg :=
    congrFun (congrFun (matTranspose_volumeAverageMat_shellReg omega U k) i) l
  simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at havg
  have hskew : shellReg omega k x l i = -shellReg omega k x i l := by
    simp only [shellReg, ShellField.forgetShell_apply]
    exact ShellField.skew_entry (omega k) x l i
  simp only [centeredShellTerm, Matrix.sub_apply]
  rw [havg, hskew]
  ring

/-- **`k^U` is anti-symmetric at every point**, with no hypothesis: off the
summability event the carrier is the zero matrix, which is anti-symmetric. -/
theorem centeredStreamField_skew_entry (omega : ShellSeq d) (U : Set (Vec d))
    (x : Vec d) (i l : Fin d) :
    centeredStreamField omega U x i l =
      -centeredStreamField omega U x l i := by
  by_cases hsum : Summable fun k : ℕ => centeredShellTerm omega U k x
  · rw [centeredStreamField_eq_tsum, tsum_matrix_apply hsum,
      tsum_matrix_apply hsum]
    rw [← tsum_neg]
    exact tsum_congr fun k => centeredShellTerm_skew_entry omega U k x i l
  · rw [centeredStreamField_eq_tsum, tsum_eq_zero_of_not_summable hsum]
    simp only [Matrix.zero_apply, neg_zero]

/-- **`k^U` is an anti-symmetric matrix field.** -/
theorem centeredStreamField_skew (omega : ShellSeq d) (U : Set (Vec d))
    (x : Vec d) :
    matTranspose (centeredStreamField omega U x) =
      -centeredStreamField omega U x := by
  ext i l
  exact centeredStreamField_skew_entry omega U x l i

/-! ## From the induced derivative norm to the ambient norms -/

private theorem norm_mat_le_matrixOperatorNorm (A : Mat d) :
    ‖A‖ ≤ matrixOperatorNorm A := by
  rw [Matrix.norm_le_iff (matrixOperatorNorm_nonneg A)]
  intro i l
  simpa only [Real.norm_eq_abs] using abs_entry_le_matrixOperatorNorm A i l

private theorem vecNorm_le_sqrt_dim_mul_norm (v : Vec d) :
    vecNorm v ≤ Real.sqrt d * ‖v‖ := by
  have hsq : vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    have hterm : ∀ i : Fin d, v i * v i ≤ ‖v‖ ^ 2 := by
      intro i
      have hvi : |v i| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      have := mul_self_le_mul_self (abs_nonneg (v i)) hvi
      rw [abs_mul_abs_self] at this
      simpa only [pow_two] using this
    calc
      vecNormSq v = ∑ i : Fin d, v i * v i := rfl
      _ ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * ‖v‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  calc
    vecNorm v = Real.sqrt (vecNormSq v) := by
      rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg v)]
    _ ≤ Real.sqrt ((d : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt d * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg v)]

private theorem vecNorm_smul (c : ℝ) (v : Vec d) :
    vecNorm (c • v) = |c| * vecNorm v := by
  simp only [vecNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

private theorem matrixOperatorNorm_smul (c : ℝ) (A : Mat d) :
    matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A := by
  simp only [matrixOperatorNorm, map_smul, norm_smul, Real.norm_eq_abs]

private theorem matrixOperatorNorm_apply_le_mul (D : MatrixDerivative d)
    (v : Vec d) :
    matrixOperatorNorm (D v) ≤ matrixDerivativeNorm D * vecNorm v := by
  rcases eq_or_lt_of_le (vecNorm_nonneg v) with hzero | hpos
  · have hv : v = 0 := by
      have hsq : vecNormSq v = 0 := by
        rw [← vecNorm_sq_eq_vecNormSq, ← hzero]
        ring
      funext i
      have hle : v i ^ 2 ≤ 0 := by
        rw [← hsq]
        exact sq_apply_le_vecNormSq v i
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        (le_antisymm hle (sq_nonneg (v i)))
    rw [← hzero, mul_zero, hv, map_zero]
    exact le_of_eq (matrixOperatorNorm_zero (d := d))
  · set t : ℝ := vecNorm v with ht
    have htne : t ≠ 0 := ne_of_gt hpos
    have hw : vecNorm (t⁻¹ • v) ≤ 1 := by
      rw [vecNorm_smul, ← ht, abs_of_nonneg (inv_nonneg.2 hpos.le),
        inv_mul_cancel₀ htne]
    have hle := matrixOperatorNorm_apply_le_matrixDerivativeNorm D (t⁻¹ • v) hw
    rw [map_smul, matrixOperatorNorm_smul,
      abs_of_nonneg (inv_nonneg.2 hpos.le)] at hle
    have hmul := mul_le_mul_of_nonneg_left hle hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ htne, one_mul, mul_comm] at hmul

/-- **The ambient operator norm of the stored shell derivative is controlled by
the carrier on a bounded set**, at the cost of the dimensional factor `√d`
relating the sup norm of `Vec d` to `vecNorm`. -/
theorem norm_deriv_le_shellDerivLinftyNorm {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (j : ShellField d) {z : Vec d} (hz : z ∈ U) :
    ‖ShellField.deriv j z‖ ≤ Real.sqrt d * shellDerivLinftyNorm U j := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (shellDerivLinftyNorm_nonneg U j)) ?_
  intro v
  have hpoint : matrixDerivativeNorm (ShellField.deriv j z) ≤
      shellDerivLinftyNorm U j := le_shellDerivLinftyNorm hU j hz
  calc
    ‖ShellField.deriv j z v‖ ≤ matrixOperatorNorm (ShellField.deriv j z v) :=
      norm_mat_le_matrixOperatorNorm _
    _ ≤ matrixDerivativeNorm (ShellField.deriv j z) * vecNorm v :=
      matrixOperatorNorm_apply_le_mul _ _
    _ ≤ shellDerivLinftyNorm U j * (Real.sqrt d * ‖v‖) := by
        refine mul_le_mul hpoint (vecNorm_le_sqrt_dim_mul_norm v)
          (vecNorm_nonneg v) (shellDerivLinftyNorm_nonneg U j)
    _ = Real.sqrt d * shellDerivLinftyNorm U j * ‖v‖ := by ring

/-- **The mean-value bound on a bounded convex set**: one shell is Lipschitz on
`U` with constant `√d ‖∇ j‖_{L∞(U)}`. -/
theorem norm_shell_sub_le {U : Set (Vec d)} (hU : Bornology.IsBounded U)
    (hconv : Convex ℝ U) (j : ShellField d) {x y : Vec d} (hx : x ∈ U)
    (hy : y ∈ U) :
    ‖j y - j x‖ ≤ Real.sqrt d * shellDerivLinftyNorm U j * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => ShellField.deriv j z)
    (fun z _ => (ShellField.hasFDerivAt j z).hasFDerivWithinAt)
    (fun _ hz => norm_deriv_le_shellDerivLinftyNorm hU j hz) hconv hx hy

/-! ## The averaging bound -/

/-- **A uniform bound on `f(x) - f(y)` over `y ∈ U` bounds `f(x) - (f)_U`.** -/
theorem norm_sub_volumeAverageMat_le {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUpos : volume U ≠ 0) {f : Vec d → Mat d}
    (hint : ∀ i l : Fin d, IntegrableOn (fun y => f y i l) U volume)
    {x : Vec d} {M : ℝ} (hM : ∀ y ∈ U, ‖f x - f y‖ ≤ M) :
    ‖f x - volumeAverageMat U f‖ ≤ M := by
  have hfin : volume U ≠ ⊤ := volume_ne_top_of_isBounded hUb
  have hUne : U.Nonempty := by
    rcases Set.eq_empty_or_nonempty U with h | h
    · exact absurd (by rw [h]; exact measure_empty) hUpos
    · exact h
  obtain ⟨y0, hy0⟩ := hUne
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM y0 hy0)
  have hVpos : 0 < (volume U).toReal := by
    refine ENNReal.toReal_pos hUpos hfin
  rw [Matrix.norm_le_iff hM0]
  intro i l
  have hconst : ∫ _y in U, f x i l ∂volume = (volume U).toReal * f x i l := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, smul_eq_mul]
  have hdiff : ∫ y in U, (f x i l - f y i l) ∂volume =
      (volume U).toReal * f x i l - ∫ y in U, f y i l ∂volume := by
    rw [MeasureTheory.integral_sub (integrableOn_const (C := f x i l) hfin)
      (hint i l), hconst]
  have hentry : (f x - volumeAverageMat U f) i l =
      (volume U).toReal⁻¹ * ∫ y in U, (f x i l - f y i l) ∂volume := by
    rw [Matrix.sub_apply, hdiff]
    simp only [volumeAverageMat, volumeAverage]
    field_simp
  have hbound : ‖∫ y in U, (f x i l - f y i l) ∂volume‖ ≤
      M * (volume U).toReal := by
    have h := norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_ne le_top hfin) (f := fun y => f x i l - f y i l) (C := M)
      (fun y hy => ?_)
    · simpa only [MeasureTheory.Measure.real] using h
    · calc
        ‖f x i l - f y i l‖ = ‖(f x - f y) i l‖ := by
          rw [Matrix.sub_apply]
        _ ≤ ‖f x - f y‖ := Matrix.norm_entry_le_entrywise_sup_norm _
        _ ≤ M := hM y hy
  rw [hentry, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hVpos.le)]
  have hstep : (volume U).toReal⁻¹ *
      |∫ y in U, (f x i l - f y i l) ∂volume| ≤
        (volume U).toReal⁻¹ * (M * (volume U).toReal) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hVpos.le)
    simpa only [Real.norm_eq_abs] using hbound
  calc
    (volume U).toReal⁻¹ * |∫ y in U, (f x i l - f y i l) ∂volume| ≤
        (volume U).toReal⁻¹ * (M * (volume U).toReal) := hstep
    _ = M := by field_simp

/-! ## Convergence of the defining series -/

/-- **Each centered shell term is bounded by `C(U) ‖∇ j_k‖_{L∞(U)}`** on a
bounded convex set of nonzero volume. -/
theorem norm_centeredShellTerm_le {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUconv : Convex ℝ U)
    (hUpos : volume U ≠ 0) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ U → ∀ ⦃b : Vec d⦄, b ∈ U → dist a b ≤ R)
    (omega : ShellSeq d) (k : ℕ) {x : Vec d} (hx : x ∈ U) :
    ‖centeredShellTerm omega U k x‖ ≤
      Real.sqrt d * R * shellDerivLinftyNorm U (omega k) := by
  have hLnonneg : 0 ≤ shellDerivLinftyNorm U (omega k) :=
    shellDerivLinftyNorm_nonneg U (omega k)
  have hR0 : 0 ≤ R := le_trans dist_nonneg (hR hx hx)
  refine norm_sub_volumeAverageMat_le hUb hUpos
    (fun i l => integrableOn_entry_of_isBounded (shellReg omega k) hUb i l) ?_
  intro y hy
  have hmv : ‖(omega k) x - (omega k) y‖ ≤
      Real.sqrt d * shellDerivLinftyNorm U (omega k) * ‖x - y‖ :=
    norm_shell_sub_le hUb hUconv (omega k) hy hx
  have hdist : ‖x - y‖ ≤ R := by
    rw [← dist_eq_norm]
    exact hR hx hy
  have hcoef : 0 ≤ Real.sqrt d * shellDerivLinftyNorm U (omega k) :=
    mul_nonneg (Real.sqrt_nonneg _) hLnonneg
  calc
    ‖shellReg omega k x - shellReg omega k y‖ =
        ‖(omega k) x - (omega k) y‖ := by
      simp only [shellReg, ShellField.forgetShell_apply]
    _ ≤ Real.sqrt d * shellDerivLinftyNorm U (omega k) * ‖x - y‖ := hmv
    _ ≤ Real.sqrt d * shellDerivLinftyNorm U (omega k) * R :=
      mul_le_mul_of_nonneg_left hdist hcoef
    _ = Real.sqrt d * R * shellDerivLinftyNorm U (omega k) := by ring

/-- **The defining series converges at every point of `U`** under the
summability hypothesis of `l.cutoff.approximation`. -/
theorem summable_centeredShellTerm {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUconv : Convex ℝ U)
    (hUpos : volume U ≠ 0) (omega : ShellSeq d)
    (hsum : Summable fun k : ℕ => shellDerivLinftyNorm U (omega k))
    {x : Vec d} (hx : x ∈ U) :
    Summable fun k : ℕ => centeredShellTerm omega U k x := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hUb
  refine Summable.of_norm_bounded
    (g := fun k : ℕ =>
      Real.sqrt d * R * shellDerivLinftyNorm U (omega k))
    (hsum.mul_left _) ?_
  intro k
  exact norm_centeredShellTerm_le hUb hUconv hUpos hR omega k hx

/-! ## The relation to the centered cutoff -/

/-- The volume average of the infrared cutoff is the sum of the shell
averages. -/
theorem volumeAverageMat_streamCutoff_eq_sum {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (omega : ShellSeq d) (L : ℕ) :
    volumeAverageMat U (streamCutoff omega L) =
      ∑ k ∈ Finset.range (L + 1),
        volumeAverageMat U fun y => shellReg omega k y := by
  ext i l
  have hint : ∀ k ∈ Finset.range (L + 1),
      IntegrableOn (fun y : Vec d => shellReg omega k y i l) U volume :=
    fun k _ => integrableOn_entry_of_isBounded (shellReg omega k) hUb i l
  have hsum : ∀ y : Vec d, streamCutoff omega L y i l =
      ∑ k ∈ Finset.range (L + 1), shellReg omega k y i l := by
    intro y
    simp only [streamCutoff_apply_entry, shellReg, ShellField.forgetShell_apply]
  simp only [Matrix.sum_apply, volumeAverageMat, volumeAverage, hsum]
  rw [MeasureTheory.integral_finsetSum _ hint, Finset.mul_sum]

/-- The finite part of the series is the centered cutoff. -/
theorem sum_centeredShellTerm_eq_centeredStreamCutoff {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    ∑ k ∈ Finset.range (L + 1), centeredShellTerm omega U k x =
      centeredStreamCutoff omega L U x := by
  rw [centeredStreamCutoff_apply,
    volumeAverageMat_streamCutoff_eq_sum hUb omega L]
  simp only [centeredShellTerm]
  rw [Finset.sum_sub_distrib]
  congr 1
  ext i l
  simp only [streamCutoff_apply_entry, Matrix.sum_apply, shellReg,
    ShellField.forgetShell_apply]

/-- **`k^U` minus the level-`L` centered cutoff is the tail of the series.**
This is the identity used by the printed proof of `l.cutoff.approximation`. -/
theorem centeredStreamField_sub_centeredStreamCutoff {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (omega : ShellSeq d) {x : Vec d}
    (hsum : Summable fun k : ℕ => centeredShellTerm omega U k x) (L : ℕ) :
    centeredStreamField omega U x - centeredStreamCutoff omega L U x =
      ∑' k : ℕ, centeredShellTerm omega U (L + 1 + k) x := by
  have hsplit := hsum.sum_add_tsum_nat_add (L + 1)
  have hshift : (fun k : ℕ => centeredShellTerm omega U (k + (L + 1)) x) =
      fun k : ℕ => centeredShellTerm omega U (L + 1 + k) x := by
    funext k
    congr 1
    omega
  rw [hshift] at hsplit
  rw [centeredStreamField_eq_tsum, ← hsplit,
    sum_centeredShellTerm_eq_centeredStreamCutoff hUb omega L x]
  abel

/-! ## The zero shell sequence -/

/-- Every centered shell term of the zero shell sequence vanishes. -/
@[simp]
theorem centeredShellTerm_zeroShellSeq (U : Set (Vec d)) (k : ℕ) (x : Vec d) :
    centeredShellTerm (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d)
      U k x = 0 := by
  have hzero : ∀ y : Vec d,
      shellReg (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) k y
        = 0 := by
    intro y
    simp only [shellReg, ShellField.forgetShell_apply,
      SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq_apply,
      ShellField.zero_apply]
  simp only [centeredShellTerm, hzero, sub_eq_zero]
  ext i l
  simp only [volumeAverageMat, volumeAverage, Matrix.zero_apply,
    MeasureTheory.integral_zero, mul_zero]

/-- **`k^U` vanishes at the zero shell sequence.** -/
@[simp]
theorem centeredStreamField_zero (U : Set (Vec d)) (x : Vec d) :
    centeredStreamField
      (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) U x = 0 := by
  rw [centeredStreamField_eq_tsum]
  simp only [centeredShellTerm_zeroShellSeq, tsum_zero]

/-- The `L∞(U)` derivative norm of the zero shell vanishes on every set. -/
@[simp]
theorem shellDerivLinftyNorm_zero (U : Set (Vec d)) :
    shellDerivLinftyNorm U (ShellField.zero d) = 0 := by
  refine le_antisymm (shellDerivLinftyNorm_le le_rfl ?_)
    (shellDerivLinftyNorm_nonneg U _)
  intro x _
  simp only [ShellField.deriv_zero, matrixDerivativeNorm_zero, le_refl]

end

end SuperdiffusionCLT.Section2.Carriers
