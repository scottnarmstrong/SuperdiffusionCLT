/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocSup
public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespSummable
public import SuperdiffusionCLT.Section4.MinimalScales.LimitAssembly

/-!
# Termwise convergence of the multiscale response series, and `hLimit`

From the convergence of the supremum over test vectors on every sub-cube
(`LimitLocSup.lean`): the finite maximum over descendants converges, hence so does
`scaleResponseAtScale ... .infinity` (a continuous power of it), hence each term
`srootE_term` of the series; this is the `hTermTendsto` input of
`srootL_hLimit_of_termTendsto_and_summable`, which together with
`srootL3_hSummCutoff` gives `hLimit`.

## Main results

* `srootL4_tendsto_scaleResponse`: convergence of the scale response at every
  scale `j ≤ n`.
* `srootL4_hTermTendsto`: the `hTermTendsto` hypothesis, proved outright.
* `srootL4_hLimit`: the `hLimit` input of `srootE_mathcalE_bounds_of_inputs`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory Filter
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- Convergence of the scale response, from the convergence of the supremum over test
vectors on every sub-cube. -/
theorem srootL4_tendsto_scaleResponse {d : ℕ} [NeZero d] (n : ℕ) (j : ℤ) (hj : j ≤ (n : ℤ))
    (f : ℕ → CoeffField d) (g : CoeffField d) (a0 : Mat d)
    (hT : ∀ R : TriadicCube d, cubeSet R ⊆ cubeSet (originCube d (n : ℤ)) →
      Filter.Tendsto (fun L : ℕ => normalizedBlockResponseMax R (f L) a0) Filter.atTop
        (nhds (normalizedBlockResponseMax R g a0))) :
    Filter.Tendsto (fun L : ℕ => scaleResponseAtScale (originCube d (n : ℤ)) j
        MultiscaleExponent.infinity (f L) a0) Filter.atTop
      (nhds (scaleResponseAtScale (originCube d (n : ℤ)) j
        MultiscaleExponent.infinity g a0)) := by
  have hj' : j ≤ (originCube d (n : ℤ)).scale := hj
  have hmax : Filter.Tendsto (fun L : ℕ =>
      maxDescendantNormalizedBlockResponseAtScale (originCube d (n : ℤ)) j (f L) a0)
      Filter.atTop (nhds (maxDescendantNormalizedBlockResponseAtScale (originCube d (n : ℤ)) j
        g a0)) :=
    srootL4_tendsto_finsetSsup (descendantsAtScale (originCube d (n : ℤ)) j)
      (fun L R => normalizedBlockResponseMax R (f L) a0)
      (fun R => normalizedBlockResponseMax R g a0)
      (fun R hR => hT R (cubeSet_subset_of_mem_descendantsAtScale hj' hR))
  have hrpow := ((Real.continuousAt_rpow_const
    (maxDescendantNormalizedBlockResponseAtScale (originCube d (n : ℤ)) j g a0) (1 / 2)
    (Or.inr (by norm_num))).tendsto).comp hmax
  exact hrpow

/-- Convergence of the `l`-th series term. -/
theorem srootL4_tendsto_srootE_term {d : ℕ} [NeZero d] (s : ℝ) (n l : ℕ)
    (f : ℕ → CoeffField d) (g : CoeffField d) (a0 : Mat d)
    (hT : ∀ R : TriadicCube d, cubeSet R ⊆ cubeSet (originCube d (n : ℤ)) →
      Filter.Tendsto (fun L : ℕ => normalizedBlockResponseMax R (f L) a0) Filter.atTop
        (nhds (normalizedBlockResponseMax R g a0))) :
    Filter.Tendsto (fun L : ℕ => srootE_term s (f L) a0 n l) Filter.atTop
      (nhds (srootE_term s g a0 n l)) := by
  have hj : ((n : ℤ) - (l : ℤ)) ≤ (n : ℤ) := by omega
  have hsc := srootL4_tendsto_scaleResponse n _ hj f g a0 hT
  have hrpow := ((Real.continuousAt_rpow_const
    (scaleResponseAtScale (originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ))
      MultiscaleExponent.infinity g a0) 2 (Or.inr (by norm_num))).tendsto).comp hsc
  exact hrpow.const_mul _

/-- **`hTermTendsto`, proved outright**: the statement of the hypothesis of
`srootL_hLimit_of_termTendsto_and_summable`. -/
theorem srootL4_hTermTendsto (d : ℕ) [NeZero d] :
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
              ∀ᵐ omega ∂P.toMeasure, ∀ l : ℕ,
                Filter.Tendsto
                  (fun L : ℕ => srootE_term s (srootE_field nu omega L m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                        (1 : Homogenization.Mat d)) n l)
                  Filter.atTop
                  (nhds (srootE_term s (srootE_limField nu omega m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                        (1 : Homogenization.Mat d)) n l)) := by
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 m n hn2 k hk
  filter_upwards [srootL4_tendsto_normalizedBlockResponseMax nu hnu hJ3 m n k hk
    ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Mat d))]
    with omega hT l
  exact srootL4_tendsto_srootE_term s n l _ _ _ hT

/-- **`hLimit`**, the input of `srootE_mathcalE_bounds_of_inputs`. -/
theorem srootL4_hLimit (d : ℕ) [NeZero d] :
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
                    (1 : Homogenization.Mat d)) ≤ B :=
  srootL_hLimit_of_termTendsto_and_summable d (srootL4_hTermTendsto d) (srootL3_hSummCutoff d)

/-! ### Witnesses for the non-law hypotheses -/

end

end SuperdiffusionCLT.Section4.MinimalScales
