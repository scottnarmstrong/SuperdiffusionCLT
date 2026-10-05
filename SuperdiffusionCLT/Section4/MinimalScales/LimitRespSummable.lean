/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespDescendantBound

/-!
# `hSummCutoff`: summability of the finite-cutoff multiscale series

`srootL_hLimit_of_termTendsto_and_summable`
(`SuperdiffusionCLT.Section4.MinimalScales.LimitAssembly`) carries
`hSummCutoff` as a named hypothesis. This module proves it outright: for
EVERY sample `omega` and EVERY cutoff level `L` (so the existential threshold
`L0` may always be taken to be `0`), the series
`∑' l, srootE_term s (srootE_field nu omega L m n k) a0 n l` is `Summable`.

The route is entirely at the `CoeffField`/`BlockJ` layer (`srootE_field` is
everywhere `(nu, Lam)`-elliptic on `cubeSet (originCube d n)`,
`LimitRespEllipticity.lean`), giving a SINGLE bound `B` on
`maxDescendantNormalizedBlockResponseAtScale (originCube d n) ((n:ℤ)-(l:ℤ))
(srootE_field ...) a0`, uniform over every scale `l`
(`LimitRespDescendantBound.lean`): `IsEllipticFieldOn` is a domain-wide, not
per-scale, predicate, so no union bound over `l` is needed. Unfolding
`scaleResponseAtScale` at `MultiscaleExponent.infinity` and cancelling the
`rpow (1/2)` then `rpow 2` (both applied to a nonnegative base) identifies
`srootE_term s a a0 n l` with `geometricWeight s 2 l * maxDescendant...`
exactly, and `Homogenization.summable_geometricWeight_mul_of_nonneg_of_le`
closes the series.

## Main result

* `srootL3_hSummCutoff`: `hSummCutoff`, exactly as stated in
  `LimitAssembly.lean`, proved outright (with `L0 := 0`, i.e. for every
  cutoff level, not merely eventually).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Filter Homogenization
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

/-- **`hSummCutoff`, proved outright**, with `L0 := 0`. -/
theorem srootL3_hSummCutoff (d : ℕ) [NeZero d] :
    ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ m n : ℕ, n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  cubeSet (originCube d (n : ℤ)) ⊆
                cubeSet (originCube d (m : ℤ)) →
              ∀ᵐ omega ∂P.toMeasure, ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
                Summable (fun l : ℕ => srootE_term s (srootE_field nu omega L m n k)
                    ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                      (1 : Mat d)) n l) := by
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 m n hn2 k hk
  refine Filter.Eventually.of_forall (fun omega => ⟨0, fun L _ => ?_⟩)
  obtain ⟨Lam, hEll⟩ := srootL3_isEllipticFieldOn_srootE_field nu hnu omega L m n k hk
  set a0 : Mat d :=
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Mat d) with ha0
  set H : ℕ → ℝ := fun l => maxDescendantNormalizedBlockResponseAtScale
      (originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ)) (srootE_field nu omega L m n k) a0 with hHdef
  set B : ℝ :=
    (nu / (1 + 2 * Lam ^ 2))⁻¹ * fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0) +
      (nu / (1 + 2 * Lam ^ 2))⁻¹ * blockMatrixOfCoeffNormSqBound nu Lam *
        fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0) with hBdef
  have hscale : ∀ l : ℕ, (n : ℤ) - (l : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    intro l
    show (n : ℤ) - (l : ℤ) ≤ (n : ℤ)
    have : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
    linarith only [this]
  have hbound : ∀ l : ℕ, H l ≤ B := by
    intro l
    exact srootL3_maxDescendant_le (originCube d (n : ℤ)) (hscale l)
      (srootE_field nu omega L m n k) a0 hEll
  have hnonneg : ∀ l : ℕ, 0 ≤ H l := by
    intro l
    rw [hHdef]
    show 0 ≤ maxDescendantNormalizedBlockResponseAtScale (originCube d (n : ℤ))
      ((n : ℤ) - (l : ℤ)) (srootE_field nu omega L m n k) a0
    unfold maxDescendantNormalizedBlockResponseAtScale finsetSsup
    refine Real.sSup_nonneg ?_
    rintro x ⟨R, -, rfl⟩
    exact normalizedBlockResponseMax_nonneg R (srootE_field nu omega L m n k) a0
  have heq : ∀ l : ℕ, srootE_term s (srootE_field nu omega L m n k) a0 n l =
      geometricWeight s 2 l * H l := by
    intro l
    unfold srootE_term scaleResponseAtScale
    show geometricWeight s 2 l * (((H l) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ)) = _
    congr 1
    rw [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.sq_sqrt (hnonneg l)]
  have hsum : Summable (fun l : ℕ => geometricWeight s 2 l * H l) :=
    summable_geometricWeight_mul_of_nonneg_of_le
      (by linarith only [hs0] : (0 : ℝ) < s * 2) hnonneg hbound
  exact hsum.congr (fun l => (heq l).symm)

end

end SuperdiffusionCLT.Section4.MinimalScales
