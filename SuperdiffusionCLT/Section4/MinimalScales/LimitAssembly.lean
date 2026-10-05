/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE
public import SuperdiffusionCLT.Section4.MinimalScales.LimitFatouSeries
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Assembly of `hLimit` (the Fatou passage of `p.new.mixing.attempt`)

`srootE_mathcalE_bounds_of_inputs`
(`SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE`) carries a
hypothesis `hLimit`, the Fatou passage to the limiting coefficient in the proof of
`p.new.mixing.attempt`: almost surely, for
every `B`, if the finite-cutoff homogenization error is eventually `≤ B`, the
limiting-field homogenization error is also `≤ B`.

This module proves exactly that statement (`srootL_hLimit_of_termTendsto_and_summable`
below has the identical conclusion, copied verbatim from `SkeletonMathcalE.lean`),
from two named hypotheses carrying the analytic content of the paper's proof; both are
proved outright in sibling modules (`srootL4_hTermTendsto` in `LimitLocTerm.lean` and
`srootL3_hSummCutoff` in `LimitRespSummable.lean`):

* `hTermTendsto` — **termwise convergence of the multiscale response series**:
  for a.e. `omega`, at every scale `l`, the `l`-th term of the series
  defining `mathcalE_{s,2}` for the finite-cutoff field tends, as `L → ∞`, to
  the same term for the limiting field. The paper justifies this by citing the
  matrix comparison `e.localization.A` (available as
  `SuperdiffusionCLT.Frozen.Section2.coarseBlockMatrix_localization`) and
  "the same energy estimate as in the proof of `e.localization.minimizers`"
  applied to the a.s. field convergence `a_L - (k_L)_{cu_m} → a - (k)_{cu_m}`
  in `W^{1,∞}(cu_{m+1})`. The pointwise convergence of the *field itself* on
  the recentering cube `cu_m` is obtained from the tail of the defining series; its geometric
  input is in this module's sibling
  `SuperdiffusionCLT.Section4.MinimalScales.LimitFieldConvergence`; the further
  step is the propagation of that field convergence through the
  coarse-grained/variational quantities `coarseBlockMatrix`, `BlockJ`,
  `normalizedBlockResponseMax`, and hence `scaleResponseAtScale`
  (`Homogenization.Deterministic.MultiscaleQuantities`), for which the
  CoarseGraining library has no continuity lemma in the field argument;
  this is carried out in `LimitLocTerm.lean`.
* `hSummCutoff` — **summability of the finite-cutoff series eventually**: for
  a.e. `omega`, for all large `L`, the series defining `mathcalE_{s,2}` for
  the finite-cutoff field is `Summable`. This is needed only because a
  non-`Summable` real `tsum` is definitionally `0` in Lean: without it, the
  hypothesis `HomogenizationErrorOnCube(a_L) ≤ B` carries no information
  about the true (extended-real) size of a divergent series, and the Fatou
  step cannot transport an eventual bound. Mathematically this follows
  from uniform ellipticity of `a_L` (the standing `nu`-ellipticity of
  `centeredCoefficientCutoff`,
  `SuperdiffusionCLT.Section2.Cutoff.symmPart_centeredCoefficientCutoff`,
  combined with the geometric decay of `geometricWeight` via the general tool
  `Homogenization.summable_geometricWeight_mul_of_nonneg_of_le` and the
  ellipticity-to-uniform-bound machinery of
  `Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl`),
  by threading a uniform response bound through to `srootE_field`.

Given both, the proof is a direct assembly: pass to `ℝ≥0∞` (where `tsum` never
hits the junk-zero branch), apply the Fatou-for-series lemma
`srootL_tsum_liminf_le_liminf_tsum`
(`SuperdiffusionCLT.Section4.MinimalScales.LimitFatouSeries`) to the
termwise limits supplied by `hTermTendsto`, transport the eventual real bound
`B` into `ℝ≥0∞` using `hSummCutoff` (so that `ENNReal.ofReal` commutes with
`tsum`), and return to `ℝ` via `ENNReal.ofReal_le_ofReal_iff`. The case where
the limiting series is not `Summable` is disposed of directly: the real
`tsum` is `0`, `Real.sqrt 0 = 0`, and `0 ≤ B` because `B` already bounds a
nonnegative quantity (the finite-cutoff error at the threshold `L0` supplied
by the target's own antecedent).

## Main result

* `srootL_hLimit_of_termTendsto_and_summable`: `hLimit`, exactly as stated in
  `SkeletonMathcalE.lean`, from `hTermTendsto` and `hSummCutoff`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Filter Homogenization
open scoped ENNReal

/-- **`hLimit`, proved from the two named analytic hypotheses above.** The
conclusion is copied verbatim from the `hLimit` binder of
`srootE_mathcalE_bounds_of_inputs`
(`SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE`). -/
theorem srootL_hLimit_of_termTendsto_and_summable (d : ℕ) [NeZero d]
    (hTermTendsto : ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ m n : ℕ, n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∀ᵐ omega ∂P.toMeasure, ∀ l : ℕ,
                Filter.Tendsto
                  (fun L : ℕ => srootE_term s (srootE_field nu omega L m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                        (1 : Homogenization.Mat d)) n l)
                  Filter.atTop
                  (nhds (srootE_term s (srootE_limField nu omega m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                        (1 : Homogenization.Mat d)) n l)))
    (hSummCutoff : ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ m n : ℕ, n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∀ᵐ omega ∂P.toMeasure, ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
                Summable (fun l : ℕ => srootE_term s (srootE_field nu omega L m n k)
                    ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                      (1 : Homogenization.Mat d)) n l)) :
    ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ m n : ℕ, n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∀ᵐ omega ∂P.toMeasure, ∀ B : ℝ,
                (∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
                  Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
                    Homogenization.MultiscaleExponent.infinity
                    (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                    (srootE_field nu omega L m n k)
                    ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                      (1 : Homogenization.Mat d)) ≤ B) →
                Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
                  Homogenization.MultiscaleExponent.infinity
                  (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                  (srootE_limField nu omega m n k)
                  ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                    (1 : Homogenization.Mat d)) ≤ B := by
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 m n hn2 k hk
  have hTT := hTermTendsto nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1
    m n hn2 k hk
  have hSC := hSummCutoff nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1
    m n hn2 k hk
  filter_upwards [hTT, hSC] with omega hTTomega hSComega
  intro B hEv
  set σ : ℝ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P with hσdef
  set g : ℕ → ℕ → ℝ :=
    fun L l => srootE_term s (srootE_field nu omega L m n k) (σ • (1 : Homogenization.Mat d)) n l
    with hgdef
  set glim : ℕ → ℝ :=
    fun l => srootE_term s (srootE_limField nu omega m n k) (σ • (1 : Homogenization.Mat d)) n l
    with hglimdef
  have hs0' : 0 ≤ s := hs0.le
  have hgnonneg : ∀ L l : ℕ, 0 ≤ g L l := fun L l => srootE_term_nonneg hs0' _ _ n l
  have hglimnonneg : ∀ l : ℕ, 0 ≤ glim l := fun l => srootE_term_nonneg hs0' _ _ n l
  have heqL : ∀ L : ℕ,
      Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
          Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite (2 : ℝ))
          (srootE_field nu omega L m n k) (σ • (1 : Homogenization.Mat d)) =
        Real.sqrt (∑' l : ℕ, g L l) :=
    fun L => srootE_homErr_eq s _ _ n
  have heqlim :
      Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
          Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite (2 : ℝ))
          (srootE_limField nu omega m n k) (σ • (1 : Homogenization.Mat d)) =
        Real.sqrt (∑' l : ℕ, glim l) :=
    srootE_homErr_eq s _ _ n
  rw [heqlim]
  obtain ⟨L0, hL0⟩ := hEv
  have hB0 : 0 ≤ B := by
    have hL0L0 := hL0 L0 le_rfl
    rw [heqL] at hL0L0
    exact le_trans (Real.sqrt_nonneg _) hL0L0
  by_cases hSummLim : Summable glim
  · have hkey : (∑' l : ℕ, glim l) ≤ B ^ 2 := by
      obtain ⟨L1, hL1⟩ := hSComega
      set F : ℕ → ℕ → ℝ≥0∞ := fun L l => ENNReal.ofReal (g L l) with hFdef
      have hliminf_eq : ∀ l : ℕ,
          Filter.liminf (fun L : ℕ => F L l) Filter.atTop = ENNReal.ofReal (glim l) :=
        fun l => Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal (hTTomega l))
      have hfatou := srootL_tsum_liminf_le_liminf_tsum F
      rw [tsum_congr hliminf_eq] at hfatou
      have hEvB2 : ∀ᶠ L : ℕ in Filter.atTop, (∑' l : ℕ, F L l) ≤ ENNReal.ofReal (B ^ 2) := by
        filter_upwards [Filter.eventually_ge_atTop L0, Filter.eventually_ge_atTop L1]
          with L hLL0 hLL1
        have hbL : Summable (fun l : ℕ => g L l) := hL1 L hLL1
        have hsqle : Real.sqrt (∑' l : ℕ, g L l) ≤ B := by
          have hbound := hL0 L hLL0
          rwa [heqL] at hbound
        have hxnonneg : 0 ≤ ∑' l : ℕ, g L l := tsum_nonneg fun l => hgnonneg L l
        have hxleB2 : (∑' l : ℕ, g L l) ≤ B ^ 2 := by
          have hpow : Real.sqrt (∑' l : ℕ, g L l) ^ 2 ≤ B ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqle 2
          rwa [Real.sq_sqrt hxnonneg] at hpow
        calc (∑' l : ℕ, F L l) = ENNReal.ofReal (∑' l : ℕ, g L l) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun l => hgnonneg L l) hbL).symm
          _ ≤ ENNReal.ofReal (B ^ 2) := ENNReal.ofReal_le_ofReal hxleB2
      have hliminf_le :
          Filter.liminf (fun L : ℕ => ∑' l : ℕ, F L l) Filter.atTop ≤
            ENNReal.ofReal (B ^ 2) := by
        apply Filter.liminf_le_of_le (f := Filter.atTop)
          (u := fun L : ℕ => ∑' l : ℕ, F L l) (a := ENNReal.ofReal (B ^ 2))
        intro a ha
        obtain ⟨L, haL, hL⟩ := (ha.and hEvB2).exists
        exact le_trans haL hL
      have hchain := le_trans hfatou hliminf_le
      rw [← ENNReal.ofReal_tsum_of_nonneg hglimnonneg hSummLim] at hchain
      exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg B)).mp hchain
    calc Real.sqrt (∑' l : ℕ, glim l) ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hkey
      _ = B := Real.sqrt_sq hB0
  · rw [tsum_eq_zero_of_not_summable hSummLim, Real.sqrt_zero]
    exact hB0

end SuperdiffusionCLT.Section4.MinimalScales
