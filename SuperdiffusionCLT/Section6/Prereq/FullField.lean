/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummabilityAllScales
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockD

/-!
# The infinite-volume stream matrix `k = ∑_n j_n`

The paper takes `k` as the *formal sum* `k(x) = ∑_{n=0}^∞ j_n(x)`. Only the gradient of `k`
is stationary, and `|(k_m - k_n)(0)| = O_{Γ₂}(C (m-n)^{1/2})`: the values at a point
form a random walk with `Θ(1)` increments, so for a generic admissible law the
raw series `∑ j_n(x)` does not converge. What the paper uses is the
recentered field `k(x) - k(0)` (the estimate `e.a.ellipticity.pointwise`, and its
application to `ã = a - k(0)`), and `∇ k`.

This file defines both the raw `fullStream` (junk `0` off the summability
event) and the recentered `fullStreamRecentered x = ∑' n, (j_n(x) - j_n(0))`,
shows that the latter converges almost surely, locally uniformly, and that it
is the locally uniform limit of `k_L(x) - k_L(0)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The raw stream matrix `k = ∑_n j_n`, with the `tsum` junk value `0` where
the series is not summable. -/
def fullStream (omega : ShellSeq d) (x : Vec d) : Mat d :=
  ∑' n : ℕ, shellReg omega n x

/-- The raw coefficient field `a = ν Id + k`. -/
def fullCoefficient (nu : ℝ) (omega : ShellSeq d) (x : Vec d) : Mat d :=
  nu • (1 : Mat d) + fullStream omega x

/-- The recentered stream matrix `k - k(0) = ∑_n (j_n - j_n(0))`. -/
def fullStreamRecentered (omega : ShellSeq d) (x : Vec d) : Mat d :=
  ∑' n : ℕ, (shellReg omega n x - shellReg omega n 0)

/-- The recentered coefficient field `ã = ν Id + (k - k(0)) = a - k(0)`. -/
def fullCoefficientRecentered (nu : ℝ) (omega : ShellSeq d) (x : Vec d) :
    Mat d :=
  nu • (1 : Mat d) + fullStreamRecentered omega x

/-- The recentered shell term. -/
def shellRecentered (omega : ShellSeq d) (n : ℕ) (x : Vec d) : Mat d :=
  shellReg omega n x - shellReg omega n 0

theorem fullStreamRecentered_eq (omega : ShellSeq d) (x : Vec d) :
    fullStreamRecentered omega x = ∑' n : ℕ, shellRecentered omega n x :=
  rfl

/-- The origin lies in every natural open cube. -/
theorem zero_mem_openCubeSet_originCube (i : ℕ) :
    (0 : Vec d) ∈ openCubeSet (originCube d (i : ℤ)) := by
  rw [mem_openCubeSet_originCube_iff]
  intro j
  have h : (0 : ℝ) < (3 : ℝ) ^ (i : ℤ) := by positivity
  simp only [Pi.zero_apply]
  constructor <;> linarith only [h]

/-- Each recentered shell term is bounded on `cu_i` by `√d 3^i ‖∇ j_n‖_{L∞(cu_i)}`. -/
theorem norm_shellRecentered_le (omega : ShellSeq d) (n i : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    ‖shellRecentered omega n x‖ ≤ Real.sqrt d * (3 : ℝ) ^ i *
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega n) := by
  have hmv := norm_shell_sub_le (isBounded_openCubeSet_originCube (d := d) (i : ℤ))
    (convex_openCubeSet (originCube d (i : ℤ))) (omega n) (zero_mem_openCubeSet_originCube i) hx
  have hdist : ‖x - 0‖ ≤ (3 : ℝ) ^ i := by
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ i := by positivity
    refine (pi_norm_le_iff_of_nonneg h3).2 fun j => ?_
    rw [mem_openCubeSet_originCube_iff] at hx
    obtain ⟨h1, h2⟩ := hx j
    rw [zpow_natCast] at h1 h2
    have hcoord : (x - 0) j = x j := by simp
    rw [hcoord, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith only [h1, h2, pow_pos (by norm_num : (0 : ℝ) < 3) i]
  have hc : 0 ≤ Real.sqrt d *
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega n) :=
    mul_nonneg (Real.sqrt_nonneg _) (shellDerivLinftyNorm_nonneg _ _)
  calc ‖shellRecentered omega n x‖
      = ‖(omega n) x - (omega n) 0‖ := by
        simp only [shellRecentered, shellReg, ShellField.forgetShell_apply]
    _ ≤ Real.sqrt d *
          shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega n) * ‖x - 0‖ := hmv
    _ ≤ Real.sqrt d *
          shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega n) * (3 : ℝ) ^ i :=
        mul_le_mul_of_nonneg_left hdist hc
    _ = _ := by ring

/-- The series of recentered shells converges uniformly on `cu_i` once the
derivative series is summable there. -/
theorem tendstoUniformlyOn_partialSums_recentered {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    TendstoUniformlyOn
      (fun (t : Finset ℕ) (x : Vec d) => ∑ n ∈ t, shellRecentered omega n x)
      (fullStreamRecentered omega) atTop
      (openCubeSet (originCube d (i : ℤ))) :=
  tendstoUniformlyOn_tsum (hsum.mul_left (Real.sqrt d * (3 : ℝ) ^ i))
    fun n _ hx => norm_shellRecentered_le omega n i hx

/-- The recentered series is summable pointwise on `cu_i`. -/
theorem summable_shellRecentered {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d (i : ℤ))) :
    Summable fun n : ℕ => shellRecentered omega n x :=
  Summable.of_norm_bounded (hsum.mul_left (Real.sqrt d * (3 : ℝ) ^ i))
    fun n => norm_shellRecentered_le omega n i hx

/-- The cutoff, recentered at the origin, is the partial sum of the recentered
shells. -/
theorem streamCutoff_sub_origin (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    streamCutoff omega L x - streamCutoff omega L 0 =
      ∑ n ∈ Finset.range (L + 1), shellRecentered omega n x := by
  simp only [streamCutoff_apply, shellRecentered, shellReg, ShellField.forgetShell_apply,
    Finset.sum_sub_distrib]

/-- **Locally uniform convergence of the cutoffs on `cu_i`.** -/
theorem tendstoUniformlyOn_streamCutoff_recentered {omega : ShellSeq d} {i : ℕ}
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    TendstoUniformlyOn
      (fun (L : ℕ) (x : Vec d) => streamCutoff omega L x - streamCutoff omega L 0)
      (fullStreamRecentered omega) atTop
      (openCubeSet (originCube d (i : ℤ))) := by
  have h := (tendstoUniformlyOn_partialSums_recentered hsum).seq_tendstoUniformlyOn
    (fun L : ℕ => Finset.range (L + 1))
    (tendsto_finset_range.comp (tendsto_add_atTop_nat 1))
  refine h.congr (Eventually.of_forall fun L x _ => ?_)
  exact (streamCutoff_sub_origin omega L x).symm

/-- Every bounded set lies in some natural open cube. -/
theorem exists_openCubeSet_superset {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ i : ℕ, S ⊆ openCubeSet (originCube d (i : ℤ)) := by
  obtain ⟨R, hR⟩ := hS.exists_pos_norm_le
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  refine ⟨i, fun x hx => ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro j
  have hxj : |x j| ≤ R := by
    have := (norm_le_pi_norm x j).trans (hR.2 x hx)
    rwa [Real.norm_eq_abs] at this
  rw [zpow_natCast]
  rw [abs_le] at hxj
  constructor <;> linarith only [hxj.1, hxj.2, hi]

/-- **Almost-sure locally uniform convergence of the recentered stream.**
Almost surely, for every bounded set `S`, the recentered cutoffs
`k_L - k_L(0)` converge uniformly on `S` to `fullStreamRecentered`. -/
theorem ae_tendstoUniformlyOn_streamCutoff_recentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ S : Set (Vec d), Bornology.IsBounded S →
      TendstoUniformlyOn
        (fun (L : ℕ) (x : Vec d) => streamCutoff omega L x - streamCutoff omega L 0)
        (fullStreamRecentered omega) atTop S := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω S hS
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset hS
  exact (tendstoUniformlyOn_streamCutoff_recentered (hω i)).mono hi

/-- Almost surely, the series of recentered shells is summable at every point. -/
theorem ae_summable_shellRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
      Summable fun n : ℕ => shellRecentered omega n x := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω x
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset (Bornology.isBounded_singleton (x := x))
  exact summable_shellRecentered (hω i) (hi rfl)

/-- Almost surely, the recentered stream is continuous on all of `ℝ^d`. -/
theorem ae_continuous_fullStreamRecentered {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, Continuous (fullStreamRecentered omega) := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3] with omega hω
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨i, hi⟩ := exists_openCubeSet_superset (Bornology.isBounded_singleton (x := x))
  have hcont : ContinuousOn (fullStreamRecentered omega)
      (openCubeSet (originCube d (i : ℤ))) := by
    refine (tendstoUniformlyOn_streamCutoff_recentered (hω i)).continuousOn
      (Frequently.of_forall fun L => ?_)
    have hc : Continuous fun x : Vec d => streamCutoff omega L x - streamCutoff omega L 0 := by
      refine Continuous.sub ?_ continuous_const
      have h : (fun x : Vec d => streamCutoff omega L x) =
          fun x => ∑ n ∈ Finset.range (L + 1), omega n x :=
        funext fun x => streamCutoff_apply omega L x
      rw [show (streamCutoff omega L).toFun = fun x : Vec d => streamCutoff omega L x from rfl, h]
      exact continuous_finsetSum _ fun n _ => (omega n).1.1.continuous
    exact hc.continuousOn
  exact hcont.continuousAt
    ((isOpen_openCubeSet (originCube d (i : ℤ))).mem_nhds (hi rfl))

end

end SuperdiffusionCLT.Section6
