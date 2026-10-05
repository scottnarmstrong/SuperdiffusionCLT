/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummability
public import SuperdiffusionCLT.Probability.GammaSigmaTsum
public import SuperdiffusionCLT.Section2.Localization.ShellWindowDomination

/-!
# The tail gauge: `e.nabla.kmn.Linfty` uniformly in the upper cutoff

In the proof of `p.new.mixing.attempt`: `sup_{L ≥ m+h} ‖∇(k_L - k_{m+h})‖_{L∞(cu_n)}` is
`O_{Γ₂}(C 3^{-(m+h)})`. The paper bounds the supremum by the full series of shell derivative norms
(the generalized triangle inequality). Here the series is `srootN3_tailGauge`, a single measurable
random variable that does not depend on `L`; it is `Γ₂`-bounded at amplitude `16384 · 3^{-mm}`
(the infinite triangle inequality) and almost surely dominates `upperShellDerivGauge n mm L` for
every `L` (almost-sure summability of the shell derivative norms).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields

noncomputable section

/-- The series of shell derivative norms on `cu_n` over the shells `mm+1, mm+2, ...`, as a
nonnegative real random variable (the sum is taken in `ℝ≥0`, where it is unconditionally the real
`tsum` of the coercions). -/
def srootN3_tailGauge (d n mm : ℕ) (omega : ShellSeq d) : ℝ :=
  ((∑' j : ℕ, Real.toNNReal (ShellField.shellCubeDerivNorm n (omega (mm + 1 + j))) : NNReal) : ℝ)

theorem srootN3_tailGauge_eq {d : ℕ} (n mm : ℕ) (omega : ShellSeq d) :
    srootN3_tailGauge d n mm omega =
      ∑' j : ℕ, ShellField.shellCubeDerivNorm n (omega (mm + 1 + j)) := by
  unfold srootN3_tailGauge
  rw [NNReal.coe_tsum]
  exact tsum_congr fun j => Real.coe_toNNReal _ (ShellField.shellCubeDerivNorm_nonneg n _)

theorem srootN3_tailGauge_nonneg {d : ℕ} (n mm : ℕ) (omega : ShellSeq d) :
    0 ≤ srootN3_tailGauge d n mm omega :=
  NNReal.coe_nonneg _

theorem srootN3_measurable_tailGauge {d : ℕ} (n mm : ℕ) :
    Measurable (srootN3_tailGauge d n mm : ShellSeq d → ℝ) := by
  unfold srootN3_tailGauge
  have h : Measurable fun omega : ShellSeq d =>
      ∑' j : ℕ, Real.toNNReal (ShellField.shellCubeDerivNorm n (omega (mm + 1 + j))) :=
    Measurable.tsum fun j =>
      (measurable_shellCubeDerivNorm_coordinate n (mm + 1 + j)).real_toNNReal
  exact h.coe_nnreal_real

/-- On the event where the shell derivative norms are summable, the tail gauge dominates every
finite upper-shell gauge. -/
theorem srootN3_upperShellDerivGauge_le_tailGauge {d : ℕ} (n mm L : ℕ) (omega : ShellSeq d)
    (hs : Summable fun k : ℕ => ShellField.shellCubeDerivNorm n (omega k)) :
    upperShellDerivGauge n mm L omega ≤ srootN3_tailGauge d n mm omega := by
  rw [srootN3_tailGauge_eq]
  unfold upperShellDerivGauge
  have hI : Finset.Ioc mm L = Finset.Ico (mm + 1) (L + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have hsum : Summable fun j : ℕ => ShellField.shellCubeDerivNorm n (omega (mm + 1 + j)) :=
    ((summable_nat_add_iff (f := fun k : ℕ => ShellField.shellCubeDerivNorm n (omega k))
      (mm + 1)).2 hs).congr fun j => by rw [add_comm]
  exact hsum.sum_le_tsum _ (fun j _ => ShellField.shellCubeDerivNorm_nonneg n _)

theorem srootN3_ae_summable_shellCubeDerivNorm {d : ℕ}
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (n : ℕ) :
    ∀ᵐ omega ∂P.toMeasure,
      Summable fun k : ℕ => ShellField.shellCubeDerivNorm n (omega k) := by
  have h := eventually_summable_shellDerivLinftyNorm hJ3
    (U := openCubeSet (originCube d (n : ℤ))) (m := n) subset_rfl
  filter_upwards [h] with omega homega
  exact homega.congr fun k => SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm_openCubeSet n (omega k)

/-- **`e.nabla.kmn.Linfty`, uniform in the upper cutoff**: the tail gauge is `Γ₂`-bounded at
amplitude `16384 · 3^{-mm}`. -/
theorem srootN3_isBigO_tailGauge {d : ℕ}
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) {n mm : ℕ}
    (hnm : n ≤ mm + 1) :
    IsBigO P.toMeasure (gammaSigma 2) (srootN3_tailGauge d n mm)
      (16384 * ((3 : ℝ) ^ mm)⁻¹) := by
  have hApos : ∀ j : ℕ, 0 ≤ (((3 : ℝ) ^ (mm + 1 + j))⁻¹) := fun j => by positivity
  have hAsum : Summable fun j : ℕ => ((3 : ℝ) ^ (mm + 1 + j))⁻¹ := by
    have hg : Summable fun j : ℕ => ((3 : ℝ)⁻¹) ^ j :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (hg.mul_left (((3 : ℝ) ^ (mm + 1))⁻¹)).congr fun j => ?_
    rw [pow_add (3 : ℝ) (mm + 1) j, mul_inv, inv_pow]
  have hbig : ∀ j : ℕ, IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d => ShellField.shellCubeDerivNorm n (omega (mm + 1 + j)))
      (((3 : ℝ) ^ (mm + 1 + j))⁻¹) := by
    intro j
    have hnk : n ≤ mm + 1 + j := le_trans hnm (Nat.le_add_right _ _)
    have hsmall := (isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate hJ3 (mm + 1 + j)).of_le
      (fun omega => ShellField.shellCubeDerivNorm_mono hnk (omega (mm + 1 + j)))
    exact (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := gammaSigma 2)
      (X := fun omega : ShellSeq d => ShellField.shellCubeDerivNorm n (omega (mm + 1 + j)))
      (A := ((3 : ℝ) ^ (mm + 1 + j))⁻¹)
      (fun omega => ShellField.shellCubeDerivNorm_nonneg n _)).1 hsmall
  have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_tsum_of_one_le
    (mu := P.toMeasure) (sigma := 2) (by norm_num) hAsum hApos
    (fun j => (measurable_shellCubeDerivNorm_coordinate n (mm + 1 + j))) hbig
  have hfun : (fun omega : ShellSeq d =>
      ∑' j : ℕ, ShellField.shellCubeDerivNorm n (omega (mm + 1 + j))) =
      srootN3_tailGauge d n mm := funext fun omega => (srootN3_tailGauge_eq n mm omega).symm
  rw [hfun] at hsum
  refine hsum.mono_scale ?_
  have htsum : ∑' j : ℕ, ((3 : ℝ) ^ (mm + 1 + j))⁻¹ = ((3 : ℝ) ^ mm)⁻¹ * (1 / 2) := by
    have h1 : ∀ j : ℕ, ((3 : ℝ) ^ (mm + 1 + j))⁻¹ =
        (((3 : ℝ) ^ (mm + 1))⁻¹) * ((3 : ℝ)⁻¹) ^ j := fun j => by
      rw [pow_add (3 : ℝ) (mm + 1) j, mul_inv, inv_pow]
    rw [tsum_congr h1, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num),
      pow_succ]
    ring
  rw [htsum]
  have hp : 0 ≤ ((3 : ℝ) ^ mm)⁻¹ := by positivity
  nlinarith only [hp]

end

end SuperdiffusionCLT.Section4.MinimalScales
