/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Response.CoarseAveragesB

/-!
# Package B4, part 3: expectation-level stationarity identities

Continues `CoarseAveragesB.lean`. Combines the stationarity bridge
(`akhc_integral_fullBlockNormalizedFluctuation_eq_originCube_of_mem_descendantsAtScale`)
with integration of the `β`-weighted finite sum over scales `n ∈ (k, m]`, which is the
expectation-level form of the deterministic core
(`akhc_paired_highScaleAverageTerms_special_le_weighted_fullBlockNormalized_fluctuation`).

Each statement is a separate lemma, so that it gets its own heartbeat budget:

* `akhc_integral_descendantsAverage_fluct_eq_two_mul_integral`: the
  stationarity rewrite at a single scale `n`.
* `akhc_integral_weighted_sum_descendantsAverage_fluct_eq`: the integral of
  the `β`-weighted finite sum, via `integral_finset_sum`/`integral_const_mul`
  plus the previous lemma.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Response

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open scoped Matrix.Norms.Elementwise BigOperators

noncomputable section

/-- **The stationarity rewrite at a single scale.** The descendant average of
`2θ·akhcFullBlockNormalizedFluctuationAtScale` at scale `n` integrates, under
the cutoff law, to `2θ` times the single value at `originCube d n`. -/
theorem akhc_integral_descendantsAverage_fluct_eq_two_mul_integral
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (m n : ℤ) (hn0 : 0 ≤ n) (hnm : n ≤ m) (θ : ℝ)
    (hIntFluctN : ∀ R ∈ descendantsAtDepth (originCube d m) (Int.toNat (m - n)),
      Integrable (fun a => akhcFullBlockNormalizedFluctuationAtScale nu L P m R a)
        (cutoffLaw (d := d) nu L P)) :
    (∫ a, descendantsAverage (originCube d m) (Int.toNat (m - n))
        (fun R => 2 * θ * akhcFullBlockNormalizedFluctuationAtScale nu L P m R a)
        ∂(cutoffLaw (d := d) nu L P)) =
      2 * θ * ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P m (originCube d n) a
        ∂(cutoffLaw (d := d) nu L P) := by
  rw [akhc_integral_descendantsAverage _ _ _
      (fun R hR => (hIntFluctN R hR).const_mul (2 * θ))]
  refine akhc_descendantsAverage_eq_of_forall_eq _ _ fun R hR => ?_
  have heq : (∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P m R a
        ∂(cutoffLaw (d := d) nu L P)) =
      ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P m (originCube d n) a
        ∂(cutoffLaw (d := d) nu L P) := by
    refine akhc_integral_fullBlockNormalizedFluctuation_eq_originCube_of_mem_descendantsAtScale
      hnu L hPrefix hJ2 m hn0 hnm ?_
    rw [descendantsAtScale_eq_descendantsAtDepth _ hnm]
    exact hR
  rw [integral_const_mul, heq]

/-- **The integral of the `β`-weighted finite sum.** Swaps `∫` and the finite
sum via `integral_finset_sum`/`integral_const_mul`, then applies the previous
lemma scale by scale. -/
theorem akhc_integral_weighted_sum_descendantsAverage_fluct_eq
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (k m : ℕ) (θ : ℝ) (wβ : ℤ → ℝ)
    (hIntFluct : ∀ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      ∀ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n)),
        Integrable (fun a => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
          (cutoffLaw (d := d) nu L P)) :
    (∫ a, ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), wβ n *
        descendantsAverage (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n))
          (fun R => 2 * θ * akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
        ∂(cutoffLaw (d := d) nu L P)) =
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ), wβ n * (2 * θ) *
        ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
          ∂(cutoffLaw (d := d) nu L P) := by
  set S := Finset.Icc ((k : ℤ) + 1) (m : ℤ) with hSdef
  have hBounds : ∀ n ∈ S, 0 ≤ n ∧ n ≤ (m : ℤ) := by
    intro n hn
    have h1 := (Finset.mem_Icc.mp hn).1
    have h2 := (Finset.mem_Icc.mp hn).2
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    omega
  have hIntEachN : ∀ n ∈ S, Integrable (fun a : RegCoeffField d =>
      wβ n * descendantsAverage (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n))
        (fun R => 2 * θ * akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a))
      (cutoffLaw (d := d) nu L P) := by
    intro n hn
    refine Integrable.const_mul ?_ (wβ n)
    unfold descendantsAverage
    exact Integrable.const_mul
      (integrable_finsetSum _ fun R hR => (hIntFluct n hn R hR).const_mul (2 * θ)) _
  rw [integral_finsetSum S hIntEachN]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hstep := akhc_integral_descendantsAverage_fluct_eq_two_mul_integral hnu L hPrefix hJ2
    (m : ℤ) n (hBounds n hn).1 (hBounds n hn).2 θ (fun R hR => hIntFluct n hn R hR)
  rw [integral_const_mul, hstep]
  ring

end

end SuperdiffusionCLT.AKHC61.Response
