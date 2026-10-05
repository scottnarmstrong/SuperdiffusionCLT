/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmP3Prime
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmOmegaSeq

/-!
Stage 4 (task `sc2`), second piece: rewrites `ThetaLmP3Prime.lean`'s
per-`(j,n)` amplitude (`homogBelow_P3prime_perPoint`) in terms of the global
closed-form majorant `homogBelow_omegaSeq` (`ThetaLmOmegaSeq.lean`), so the
result can be fed directly into AK.HC's (P3') existence binder, which
quantifies the amplitude over `n` alone via a fixed sequence `omegaSeq : ℕ →
ℝ`. The two amplitudes agree everywhere the per-`(j,n)` theorem is ever
invoked (`n ≥ 1`, forced internally by `beta * j < n` with `beta = 1/2 ≥ 0`
and `j : ℕ`), since `homogBelow_omegaSeq`'s only change from the raw
per-`(j,n)` amplitude is `(max 1 n)^{-3000}` in place of `n^{-3000}`,
identical once `n ≥ 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- `homogBelow_omegaSeq` unfolds to the raw per-`(j,n)` amplitude once
`n ≥ 1`, since `max 1 (n:ℝ) = (n:ℝ)` there. -/
theorem homogBelow_omegaSeq_eq_of_one_le
    {d : ℕ} [NeZero d] (nu : ℝ) (L : ℕ) (Cmix : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    {n : ℕ} (hn1 : 1 ≤ n) :
    homogBelow_omegaSeq nu L Cmix P n =
      Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
        (Cmix * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(1 : ℝ)) +
          (Cmix * ((L - n : ℕ) : ℝ) *
              (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(2 : ℝ)) +
            3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ)))) := by
  unfold homogBelow_omegaSeq
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  rw [max_eq_right hn1R]

/-- **The (P3') existence clause, in terms of `homogBelow_omegaSeq`**: the
per-`(j,n)` verification `homogBelow_P3prime_perPoint`, rewritten so its
amplitude is exactly `homogBelow_omegaSeq nu L Cmix P n`, matching AK.HC's
`omegaSeq` binder in `akhc_weakerP3` literally. -/
theorem homogBelow_p3prime_omegaSeq
    (d : ℕ) [NeZero d]
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (M alpha : ℝ)
    (Cmix : ℝ) (hCmix1 : 1 ≤ Cmix)
    (c : ℝ) (hc : 0 < c)
    (L : ℕ) (hL1 : 1 ≤ L)
    (hLabsorbApplied :
        c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2)
    (hSstarApplied : ∀ h : ℕ, (L : ℝ) ≤ 2 * (h : ℝ) → h ≤ L →
        c * (Cmix * M) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ))
    (hLogLeNApplied : ∀ n : ℕ,
        (L : ℝ) - c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
        Cmix * Real.log (nu⁻¹ * (L : ℝ)) ≤ (n : ℝ))
    (hLogRatioApplied : ∀ n : ℕ,
        (L : ℝ) - c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
        Real.log (nu⁻¹ * (L : ℝ)) ≤ 2 * Real.log (nu⁻¹ * (n : ℝ)))
    (hMixApplied : ∀ m n L' : ℕ, 1 ≤ L' →
        (L' : ℝ) - (n : ℝ) ≤
          Cmix⁻¹ *
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L' P
                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
              (2 : ℝ) →
        m < 2 * n →
        (n : ℤ) ≤ (m : ℤ) - ⌈Cmix * Real.log (nu⁻¹ * (L' : ℝ))⌉ →
        ⌈Cmix * Real.log (nu⁻¹ * (L' : ℝ))⌉ ≤ (n : ℤ) →
        (n : ℤ) ≤ (m : ℤ) - ⌈Cmix * Real.log (nu⁻¹ * (n : ℝ))⌉ →
        ((m : ℝ) ≤ (L' : ℝ) + Cmix * Real.log (nu⁻¹ * (L' : ℝ)) →
          ∃ X1 X2 X3 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable X1 ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
                (Homogenization.IndependentSums.gammaSigma 2) X1
                (Cmix * ((L' - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L' P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                    (-(1 : ℝ))) ∧
            Measurable X2 ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
                (Homogenization.IndependentSums.gammaSigma 1) X2
                (Cmix * ((L' - n : ℕ) : ℝ) *
                  (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L' P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                    (-(2 : ℝ))) ∧
            Measurable X3 ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
                (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X3
                (Cmix * (m : ℝ) ^ (-(3000 : ℝ))) ∧
              ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                (p q : Homogenization.BlockVec d),
                2 *
                    (((Homogenization.descendantsAtDepth
                            (Homogenization.originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                      ∑ R ∈ Homogenization.descendantsAtDepth
                          (Homogenization.originCube d (m : ℤ)) (m - n),
                        Homogenization.blockVecDot p
                          (Homogenization.blockMatVecMul
                            (Homogenization.ofFullBlockMat
                              (Homogenization.toFullBlockMat
                                  (Homogenization.coarseBlockMatrix
                                    (Homogenization.cubeSet R)
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L').toCoeffField) -
                                Homogenization.toFullBlockMat
                                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                    nu L' P
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (n : ℤ))))))
                            q)) ≤
                  (X1 omega + X2 omega + X3 omega) *
                    (Homogenization.blockVecDot p
                        (Homogenization.blockMatVecMul
                          (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L' P
                            (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                          p) +
                      Homogenization.blockVecDot q
                        (Homogenization.blockMatVecMul
                          (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L' P
                            (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                          q))) ∧
        ((L' : ℝ) + Cmix * Real.log (nu⁻¹ * (L' : ℝ)) < (m : ℝ) →
          ∃ X4 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
            Measurable X4 ∧
            Homogenization.IndependentSums.IsBigO P.toMeasure
                (Homogenization.IndependentSums.gammaSigma 1) X4
                (Cmix * (m : ℝ) ^ (-(3000 : ℝ))) ∧
              ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                (p q : Homogenization.BlockVec d),
                2 *
                    (((Homogenization.descendantsAtDepth
                            (Homogenization.originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                      ∑ R ∈ Homogenization.descendantsAtDepth
                          (Homogenization.originCube d (m : ℤ)) (m - n),
                        Homogenization.blockVecDot p
                          (Homogenization.blockMatVecMul
                            (Homogenization.ofFullBlockMat
                              (Homogenization.toFullBlockMat
                                  (Homogenization.coarseBlockMatrix
                                    (Homogenization.cubeSet R)
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L').toCoeffField) -
                                Homogenization.toFullBlockMat
                                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                    nu L' P
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (n : ℤ))))))
                            q)) ≤
                  X4 omega *
                    (Homogenization.blockVecDot p
                        (Homogenization.blockMatVecMul
                          (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L' P
                            (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                          p) +
                      Homogenization.blockVecDot q
                        (Homogenization.blockMatVecMul
                          (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L' P
                            (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                          q)))) :
    ∀ j n : ℕ,
      (L : ℝ) - c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
      (1 / 2 : ℝ) * (j : ℝ) < (n : ℝ) →
      (n : ℝ) < (j : ℝ) - (4 * Cmix) * Real.log (nu⁻¹ * (n : ℝ)) →
      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X
            (homogBelow_omegaSeq nu L Cmix P n) ∧
        ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
          (p q : Homogenization.BlockVec d),
          2 *
              (((Homogenization.descendantsAtDepth
                      (Homogenization.originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
                ∑ R ∈ Homogenization.descendantsAtDepth
                    (Homogenization.originCube d (j : ℤ)) (j - n),
                  Homogenization.blockVecDot p
                    (Homogenization.blockMatVecMul
                      (Homogenization.ofFullBlockMat
                        (Homogenization.toFullBlockMat
                            (Homogenization.coarseBlockMatrix
                              (Homogenization.cubeSet R)
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField) -
                          Homogenization.toFullBlockMat
                            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                              nu L P
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ))))))
                      q)) ≤
            X omega *
              (Homogenization.blockVecDot p
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                    p) +
                Homogenization.blockVecDot q
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                    q)) := by
  intro j n hn_ge hbj hjw
  obtain ⟨X, hXmeas, hXbig, hbil⟩ :=
    homogBelow_P3prime_perPoint d nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 M alpha Cmix hCmix1 c hc
      L hL1 hLabsorbApplied hSstarApplied hLogLeNApplied hLogRatioApplied hMixApplied j n
      hn_ge hbj hjw
  refine ⟨X, hXmeas, ?_, hbil⟩
  have hjnn : (0 : ℝ) ≤ (1 / 2 : ℝ) * (j : ℝ) := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hjnn hbj
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  rw [homogBelow_omegaSeq_eq_of_one_le nu L Cmix P hn1]
  exact hXbig

end SuperdiffusionCLT.Section4.HomogBelow
