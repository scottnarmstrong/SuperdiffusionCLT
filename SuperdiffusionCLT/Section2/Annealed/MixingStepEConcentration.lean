/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingLoewnerStepsB
public import SuperdiffusionCLT.Section2.Annealed.MixingStepEnvelope
public import Homogenization.Book.Ch04.Theorems.PartitionAverages

/-!
# Step E: the entry-level concentration of the descendant average

The Step-E Loewner reduction (in `MixingLoewnerSteps`) turns `hStepE` into the operator-norm
`Gamma_2` concentration of the fluctuation of the descendant average, and
`isBigO_gammaSigma_operatorNorm_of_entrywise` (in `MixingLoewnerStepsB`) further turns it into
entry-level concentration with an abstract amplitude schedule.  This module supplies the two
remaining pieces in explicit form.

## What `MixingStepEnvelope` gives at entry level

`MixingStepEnvelope` gives three entry-level facts about
the centred observable `Y_L,R^{ij} := s^-1_{L,*}(R)_{ij} - shom^-1_{L,*}(cu_h)_{ij}`
(shortcut for `sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu . L)` minus
`sigmaBarStarInv nu L P (cubeSet (originCube d h))`):

* `measurable_isBigO_gammaSigma_entry_sub_sigmaBarStarInv`: for *one cube* `Q`,
  the centred entry is measurable and `O_{Gamma_2}(nu^-1 + nu^-1)`;
* `integral_entry_sub_sigmaBarStarInv_descendant`: for a descendant `R` of `cu_n`,
  the expectation of the centred entry is `0` (stationarity centring);
* `isBigO_gammaSigma_finsetAverage_entry_sub_sigmaBarStarInv`: for a
  *pairwise `ell`-shell-separated* finset `s` of descendants, with `L <= ell`,
  the finset average `s.card^-1 * sum_{R in s} Y_L,R^{ij}` is `O_{Gamma_2}` at the
  sublattice amplitude
  `gammaSigmaIndependentSumConst 2 * (sqrt s.card / s.card) * (nu^-1 + nu^-1)`.

**The obstruction.** The target is the *full* descendant average
`descendantsAverageMat` over `descendantsAtDepth (originCube d n) (n - h)`, and the
envelope theorem applies only to a shell-separated sub-finset. The
descendants at scale `h` are *not* pairwise separated at the cutoff level `L = m`
(their own scale is `h < m`), so the envelope theorem cannot be applied to the
full descendant finset. Its proof also needs the lane measurability level
`ell >= L = m`, whereas the descendants are only separated at their own scale `h`.

## What this module supplies

* `isBigO_gammaSigma_operatorNorm_of_entrywise_uniform`: the entry-to-operator-norm
  union bound with the *explicit* dimensional constant `(d : R) * (d : R)`
  (the `d^2` matrix dimension), for a uniform entry amplitude;
* `isBigO_gammaSigma_descendantAverage_entry_of_colorPartition`: the *entry-level
  concentration of the full descendant average* from a colour partition of the
  descendants into `m`-shell-separated classes; the per-class input is
  *discharged* from the envelope theorem, so the only residual is the
  existence of the partition, made explicit as a hypothesis.

The exact amplitudes are reported in the docstrings; the residual partition and
bookkeeping hypotheses are stated verbatim in the theorem binders.

## Exact amplitudes and the comparison with the printed one

The entry-level amplitude actually proved (Theorem C) is

`gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 * (sqrt(#colors) * (sqrt N / N)) *
(nu^-1 + nu^-1)`,

where `N = 3^(d (n - h))` is the descendant count and `#colors` the number of
colour classes.  The printed target is `CFluc * nu^-2 * 3^-((n - h)/4)`.  The two
agree in shape only through the partition's class count: with `Q` classes the
amplitude carries `sqrt(Q/N)`, so it decays exactly when the partition is coarse.
A residue-class construction on the descendant grid gives `Q = 3^(d (m - h + Delta))`
and each class of size `3^(d (n - m - Delta))` (`Delta >= 1` the separation slack
needed for `AreShellSeparated m`, since two cubes of scale `h` at lattice offset
`3^h K` are `3^h (K - 1)` apart as sets), whence `sqrt(Q/N) = 3^(-d (n - m - Delta)/2)`,
which at the midpoint `m = (n + h + 1)/2` is dominated by the printed
`3^-((n - h)/4)` for `d >= 2`.  That comparison is *not* reproved here: the
cardinality bound on the partition is part of the explicit bookkeeping hypothesis
`hAmpl` of the Step-E bookkeeping.  With singleton classes (`Q = N`) the same
theorem yields only the trivial amplitude `gammaTriangleConst 2 *
gammaSigmaIndependentSumConst 2 * (nu^-1 + nu^-1)`, with no decay in `n - h`; the
partition's coarseness is therefore a genuine residual, not a formality.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The entry-to-operator-norm union bound with the explicit `d^2` factor -/

/-- **Entry-to-operator-norm union bound with the explicit dimensional
constant.**  If every entry `(i,j)` of a matrix observable `M` is measurable and
`O_{Gamma_sigma}` at one *common* amplitude `A > 0`, then `||M||_op` is
`O_{Gamma_sigma}` at the amplitude `gammaTriangleConst sigma * (d * d) * A`.  The
factor `(d : R) * (d : R)` is the number of matrix entries: the operator norm is
dominated by the sum of the `d^2` absolute entries
(`matrixOperatorNorm_le_sum_univ_abs_entry`), and the finite-family triangle
inequality costs the universal constant `gammaTriangleConst sigma`. -/
theorem isBigO_gammaSigma_operatorNorm_of_entrywise_uniform [NeZero d]
    {μ : Measure (ShellSeq d)} [IsFiniteMeasure μ] {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A)
    (M : ShellSeq d → Homogenization.Mat d)
    (hmeas : ∀ p : Fin d × Fin d, Measurable (fun ω : ShellSeq d ↦ M ω p.1 p.2))
    (h : ∀ p : Fin d × Fin d,
      IsBigO μ (gammaSigma σ) (fun ω : ShellSeq d ↦ M ω p.1 p.2) A) :
    IsBigO μ (gammaSigma σ)
      (fun ω : ShellSeq d ↦ Homogenization.Book.Ch02.matrixOperatorNorm (M ω))
      (gammaTriangleConst σ * ((d : ℝ) * (d : ℝ)) * A) := by
  have hbase := isBigO_gammaSigma_operatorNorm_of_entrywise (μ := μ) hσ M
    (fun _ : Fin d × Fin d ↦ A) (fun _ ↦ hA) hmeas h
  have hcard : (∑ _p : Fin d × Fin d, (A : ℝ)) = ((d : ℝ) * (d : ℝ)) * A := by
    have hcardnat : (Finset.univ : Finset (Fin d × Fin d)).card = d * d := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    rw [Finset.sum_const, nsmul_eq_mul, hcardnat]
    push_cast
    ring
  simpa only [mul_assoc, hcard] using hbase

/-! ## `hStepE` from uniform entry-level concentration -/

/-! ## The entry-level concentration from a colour partition -/

/-- The independent-sum constant at `sigma = 2` is positive. -/
private theorem gammaSigmaIndependentSumConst_two_pos :
    0 < Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 := by
  have hlt : ¬ ((2 : ℝ) < 1) := by norm_num
  have hne : ¬ ((2 : ℝ) = 1) := by norm_num
  have hExp : 0 < Homogenization.IndependentSums.gammaSigmaExpRegimeConst 2 :=
    lt_of_lt_of_le
      (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
        (Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)))
      (le_max_left _ _)
  dsimp only [Homogenization.Book.Ch04.gammaSigmaIndependentSumConst,
    Homogenization.Book.Ch04.gammaSigmaExpRegimeEndpointConst,
    Homogenization.IndependentSums.gammaSigmaExpRegimeEndpointConst]
  rw [ite_eq_right hlt, ite_eq_right hne]
  exact mul_pos (by norm_num) hExp

/-- **Entry-level concentration of the full descendant average, from a colour
partition of the descendants into `m`-shell-separated classes.**

`colors` indexes the classes `cls c`, which are required to be *disjoint*,
*nonempty*, to *cover* the depth-`(n - h)` descendants of `originCube d n`, and
to be *pairwise `m`-shell-separated*.  Under those hypotheses the `Gamma_2`
amplitude of the centred full descendant average is
`gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
(sqrt(#colors) * (sqrt N / N)) * (nu^-1 + nu^-1)`, with `N` the descendant count
`3^(d (n - h))`.  The per-class input is *discharged*: each class sum is bounded
from the envelope theorem `isBigO_gammaSigma_finsetAverage_entry_sub_sigmaBarStarInv`
(scaled by the class cardinality), and the classes are aggregated by the
`isBigO_finsetAverage_colorClassSums_gammaSigma`, whose square-root hypothesis is
supplied here by Cauchy-Schwarz from the disjoint cover.  The only residual is the
existence of the partition itself, and the amplitude bookkeeping against the
printed `CFluc * nu^-2 * 3^-((n - h)/4)`. -/
theorem isBigO_gammaSigma_descendantAverage_entry_of_colorPartition [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (hJ1 : ShellLawJ1Restriction d P) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n h : ℕ} (hhm : h < m) (hmn : m ≤ n)
    {ι : Type*} [DecidableEq ι] (colors : Finset ι) (cls : ι → Finset (TriadicCube d))
    (hcolors : colors.Nonempty)
    (hdisj : (colors : Set ι).PairwiseDisjoint cls)
    (hcover : colors.biUnion cls = descendantsAtDepth (originCube d (n : ℤ)) (n - h))
    (hnonempty : ∀ c ∈ colors, (cls c).Nonempty)
    (hsep : ∀ c ∈ colors, ∀ R ∈ cls c, ∀ R' ∈ cls c, R ≠ R' →
      ShellField.AreShellSeparated m (cubeSet R) (cubeSet R'))
    (i j : Fin d) :
    IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d =>
        Homogenization.descendantsAverageMat (originCube d (n : ℤ)) (n - h)
            (fun R ↦ sigmaStarInvCoarse (cubeSet R)
              (coefficientCutoff nu omega m).toCoeffField) i j -
          sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j)
      (gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (Real.sqrt (colors.card : ℝ) *
          (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
            ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) *
        (nu⁻¹ + nu⁻¹)) := by
  classical
  have hhn : h < n := by linarith only [hhm, hmn]
  have hDpos : (0 : ℝ) <
      ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) := by
    rw [SuperdiffusionCLT.Section2.Localization.card_descendantsAtDepth_originCube]
    positivity
  have hDne : ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) ≠ 0 :=
    ne_of_gt hDpos
  have hKpos : (0 : ℝ) < nu⁻¹ + nu⁻¹ := by linarith only [inv_pos.2 hnu]
  have hsub : ∀ c ∈ colors, ∀ R ∈ cls c,
      R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h) := by
    intro c hc R hR
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨c, hc, hR⟩
  have hclass : ∀ c ∈ colors, IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d ↦ ((cls c).card : ℝ)⁻¹ * ∑ R ∈ cls c,
        (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
          sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j))
      (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ)) * (nu⁻¹ + nu⁻¹)) := by
    intro c hc
    exact isBigO_gammaSigma_finsetAverage_entry_sub_sigmaBarStarInv hnu m P hJ1 hPrefix hJ2 hJ3 hJ4
      m le_rfl (hnonempty c hc) (hsep c hc) hhn (hsub c hc) i j
  have hsumc : ∀ c ∈ colors, IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d ↦ ∑ R ∈ cls c,
        (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
          sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j))
      (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((cls c).card : ℝ) * (nu⁻¹ + nu⁻¹)) := by
    intro c hc
    have hcardpos : (0 : ℝ) < ((cls c).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (hnonempty c hc)
    have hcardne : ((cls c).card : ℝ) ≠ 0 := ne_of_gt hcardpos
    have h1 := IndependentSums.IsBigO.const_mul (μ := P.toMeasure) (Ψ := gammaSigma 2)
      (X := fun omega : ShellSeq d ↦ ((cls c).card : ℝ)⁻¹ * ∑ R ∈ cls c,
        (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
          sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j))
      (A := Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ)) * (nu⁻¹ + nu⁻¹))
      hcardpos.le (hclass c hc)
    have hfun : (fun omega : ShellSeq d ↦ ((cls c).card : ℝ) *
        (((cls c).card : ℝ)⁻¹ * ∑ R ∈ cls c,
          (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
            sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j))) =
        (fun omega : ShellSeq d ↦ ∑ R ∈ cls c,
          (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
            sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j)) := by
      funext omega
      rw [← mul_assoc, mul_inv_cancel₀ hcardne, one_mul]
    have hid : ((cls c).card : ℝ) * (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ)) * (nu⁻¹ + nu⁻¹)) =
        Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          Real.sqrt ((cls c).card : ℝ) * (nu⁻¹ + nu⁻¹) := by
      have hdiv : ((cls c).card : ℝ) *
          (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ)) =
          Real.sqrt ((cls c).card : ℝ) := by
        field_simp
      calc ((cls c).card : ℝ) *
            (Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ)) * (nu⁻¹ + nu⁻¹))
          = Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              (((cls c).card : ℝ) *
                (Real.sqrt ((cls c).card : ℝ) / ((cls c).card : ℝ))) * (nu⁻¹ + nu⁻¹) := by
            ring
        _ = Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              Real.sqrt ((cls c).card : ℝ) * (nu⁻¹ + nu⁻¹) := by rw [hdiv]
    rw [hfun, hid] at h1
    exact h1
  have hcardsum : (∑ c ∈ colors, ((cls c).card : ℝ)) =
      ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) := by
    have hcard := Finset.card_biUnion (s := colors) (t := cls) hdisj
    rw [hcover] at hcard
    exact_mod_cast hcard.symm
  have hsqrt : ∑ c ∈ colors, Real.sqrt ((cls c).card : ℝ) ≤
      Real.sqrt (colors.card : ℝ) *
        Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) := by
    have hsch := Real.sum_sqrt_mul_sqrt_le (s := colors)
      (f := fun _ : ι ↦ (1 : ℝ)) (g := fun c ↦ ((cls c).card : ℝ))
      (hf := by intro c; norm_num) (hg := by intro c; positivity)
    simpa only [ge_iff_le, Real.sqrt_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hcardsum] using hsch
  have hYmeas : ∀ c ∈ colors, Measurable (fun omega : ShellSeq d ↦ ∑ R ∈ cls c,
      (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
        sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j)) := by
    intro c hc
    refine Finset.measurable_sum _ ?_
    intro R hR
    exact (measurable_isBigO_gammaSigma_entry_sub_sigmaBarStarInv hnu m P hPrefix hJ2 hJ3 hJ4
      h R i j).1
  have htool := Homogenization.Book.Ch04.isBigO_finsetAverage_colorClassSums_gammaSigma
    (μ := P.toMeasure) (colors := colors)
    (Y := fun c omega ↦ ∑ R ∈ cls c,
      (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
        sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j))
    (classCount := fun c ↦ ((cls c).card : ℝ))
    (colorCount := (colors.card : ℝ))
    (totalCount := ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))
    (C := Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2)
    (K := nu⁻¹ + nu⁻¹) (σ := 2)
    (by norm_num) hcolors
    (fun c hc ↦ by
      show (0 : ℝ) < ((cls c).card : ℝ)
      exact_mod_cast Finset.card_pos.mpr (hnonempty c hc))
    hDpos gammaSigmaIndependentSumConst_two_pos hKpos hsumc hYmeas hsqrt
  have hfun : (fun omega : ShellSeq d ↦
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
          ∑ c ∈ colors, ∑ R ∈ cls c,
            (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
              sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j)) =
      (fun omega : ShellSeq d ↦
        Homogenization.descendantsAverageMat (originCube d (n : ℤ)) (n - h)
            (fun R ↦ sigmaStarInvCoarse (cubeSet R)
              (coefficientCutoff nu omega m).toCoeffField) i j -
          sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j) := by
    funext omega
    have hsplit : ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h),
        (sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j -
          sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j) =
        (∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h),
          sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j) -
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) *
          sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))) i j := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_biUnion hdisj, hcover, hsplit]
    have havg : ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ)⁻¹ *
        (∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - h),
          sigmaStarInvCoarse (cubeSet R) (coefficientCutoff nu omega m).toCoeffField i j) =
        Homogenization.descendantsAverageMat (originCube d (n : ℤ)) (n - h)
          (fun R ↦ sigmaStarInvCoarse (cubeSet R)
            (coefficientCutoff nu omega m).toCoeffField) i j := by
      simp only [Homogenization.descendantsAverageMat, Homogenization.descendantsAverage]
    rw [← havg, mul_sub, ← mul_assoc, inv_mul_cancel₀ hDne, one_mul]
  simpa only [hfun] using htool

/-! ## `hStepE` from a colour partition -/

end

end SuperdiffusionCLT.Section2.Annealed
