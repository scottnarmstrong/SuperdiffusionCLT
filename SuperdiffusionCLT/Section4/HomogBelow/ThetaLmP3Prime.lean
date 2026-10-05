/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmGammaSigmaWeaken
public import Homogenization.Probability.IndependentSums.Triangle

/-!
The per-`(j,n)` verification
of the weaker concentration assumption (P3') of [AK, Theorem 6.1] from `mixing_below_cutoff`
(`p.mixing.P.three.prime`, with the extra gap binder
`n ≤ m - ⌈C log(ν⁻¹n)⌉`), following the proof of `l.we.can.apply.hc`.

All five "external" facts this theorem consumes (the mixing law itself, the
`e.L.vs.Lnaught` mixing-window lower bound, and the two log-comparison
absorption facts) are taken **already specialized** at the caller's chosen
constants `C` (the outer `lNaught` threshold constant), `Cmix`
(`mixing_below_cutoff`'s own witness) and `c` (`lNaught_sstar_lower`'s own
witness) — not as raw existentials — because two of them (`Cmix`, `c`) are
independent universal constants with no a priori relation, and the window
condition H1 needs them combined via *different* multiples of `M`: the
threshold `m₃` and the log-comparison facts use `c·M`, while the
`sigmaBarStarScalar` lower bound is invoked at `Cmix·M`. Concretely:

`(L-n) ≤ (L-m₃) ≤ c·M·L^α·log³L` (from `m₃`'s hypothesis, using `c·M`)
`S² ≥ c·(Cmix·M)·L^α·log³L = c·Cmix·M·L^α·log³L` (`hSstarApplied` at `Cmix·M`)
`Cmix⁻¹·S² ≥ c·M·L^α·log³L ≥ L-n`.

The two multiples cancel *exactly*, with no inequality needed between `c`
and `Cmix`. This is why `hSstarApplied` below is pre-applied at `Cmix · M`
specifically (not a generic `M'`), and why `m₃`'s own hypothesis, and the two
log-comparison facts, are all stated with `c · M` (not `M` alone). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- **The (P3') clause, verified per `(j,n)` pair.** -/
theorem homogBelow_P3prime_perPoint
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
            (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
                (Cmix * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                    (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                        (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                      (-(1 : ℝ)) +
                  (Cmix * ((L - n : ℕ) : ℝ) *
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^
                        (-(2 : ℝ)) +
                    3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ))))) ∧
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
  intro j n hn_ge hj_lt_2n hwindow
  have hLge1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hnu_inv_ge1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  have hnu_inv_L_ge1 : (1 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ nu⁻¹ * (L : ℝ) :=
        mul_le_mul hnu_inv_ge1 hLge1 (by norm_num) (le_trans zero_le_one hnu_inv_ge1)
  have hlogL_nonneg : 0 ≤ Real.log (nu⁻¹ * (L : ℝ)) := Real.log_nonneg hnu_inv_L_ge1
  have hCmix_nonneg : (0 : ℝ) ≤ Cmix := by linarith only [hCmix1]
  have hCmixpos : (0 : ℝ) < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have hjnn : (0 : ℝ) ≤ (1 / 2 : ℝ) * (j : ℝ) := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt hjnn hj_lt_2n
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  have hnge1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnu_inv_n_ge1 : (1 : ℝ) ≤ nu⁻¹ * (n : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ nu⁻¹ * (n : ℝ) :=
        mul_le_mul hnu_inv_ge1 hnge1R (by norm_num) (le_trans zero_le_one hnu_inv_ge1)
  have hlogn_nonneg : 0 ≤ Real.log (nu⁻¹ * (n : ℝ)) := Real.log_nonneg hnu_inv_n_ge1
  -- H2
  have hH2 : j < 2 * n := by
    have h : (j : ℝ) < 2 * (n : ℝ) := by linarith only [hj_lt_2n]
    exact_mod_cast h
  -- H4
  have hH4 : ⌈Cmix * Real.log (nu⁻¹ * (L : ℝ))⌉ ≤ (n : ℤ) :=
    Int.ceil_le.mpr (by exact_mod_cast hLogLeNApplied n hn_ge)
  -- H3
  have hlogRatio := hLogRatioApplied n hn_ge
  have hstepA : Cmix * Real.log (nu⁻¹ * (L : ℝ)) ≤ Cmix * (2 * Real.log (nu⁻¹ * (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hlogRatio hCmix_nonneg
  have hstepB : Cmix * (2 * Real.log (nu⁻¹ * (n : ℝ))) ≤ 4 * Cmix * Real.log (nu⁻¹ * (n : ℝ)) := by
    have heq : Cmix * (2 * Real.log (nu⁻¹ * (n : ℝ))) = 2 * Cmix * Real.log (nu⁻¹ * (n : ℝ)) := by
      ring
    rw [heq]
    have h24 : (2 : ℝ) * Cmix ≤ 4 * Cmix := by linarith only [hCmix_nonneg]
    exact mul_le_mul_of_nonneg_right h24 hlogn_nonneg
  have hlogbound : Cmix * Real.log (nu⁻¹ * (L : ℝ)) ≤ 4 * Cmix * Real.log (nu⁻¹ * (n : ℝ)) :=
    le_trans hstepA hstepB
  have hgap : (n : ℝ) + Cmix * Real.log (nu⁻¹ * (L : ℝ)) < (j : ℝ) := by
    linarith only [hwindow, hlogbound]
  have hceil_lt : (⌈Cmix * Real.log (nu⁻¹ * (L : ℝ))⌉ : ℝ) <
      Cmix * Real.log (nu⁻¹ * (L : ℝ)) + 1 := Int.ceil_lt_add_one _
  have hsum_lt : ((n : ℤ) + ⌈Cmix * Real.log (nu⁻¹ * (L : ℝ))⌉ : ℝ) < ((j : ℤ) + 1 : ℝ) := by
    push_cast
    linarith only [hgap, hceil_lt]
  have hsum_lt' : (n : ℤ) + ⌈Cmix * Real.log (nu⁻¹ * (L : ℝ))⌉ < (j : ℤ) + 1 := by
    exact_mod_cast hsum_lt
  have hH3 : (n : ℤ) ≤ (j : ℤ) - ⌈Cmix * Real.log (nu⁻¹ * (L : ℝ))⌉ := by omega
  -- the gap binder of `mixing_below_cutoff`: (n:ℤ) ≤ (j:ℤ) - ⌈Cmix * log(nu⁻¹ n)⌉,
  -- directly from the window's third condition (j - n > 4·Cmix·log(ν⁻¹n)), exactly like hH3
  -- with L replaced by n
  have h4n : Cmix * Real.log (nu⁻¹ * (n : ℝ)) ≤ 4 * Cmix * Real.log (nu⁻¹ * (n : ℝ)) := by
    have h14 : Cmix ≤ 4 * Cmix := by linarith only [hCmix_nonneg]
    calc Cmix * Real.log (nu⁻¹ * (n : ℝ)) ≤ (4 * Cmix) * Real.log (nu⁻¹ * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right h14 hlogn_nonneg
      _ = 4 * Cmix * Real.log (nu⁻¹ * (n : ℝ)) := by ring
  have hgapn : (n : ℝ) + Cmix * Real.log (nu⁻¹ * (n : ℝ)) < (j : ℝ) := by
    linarith only [hwindow, h4n]
  have hceil_lt_n : (⌈Cmix * Real.log (nu⁻¹ * (n : ℝ))⌉ : ℝ) <
      Cmix * Real.log (nu⁻¹ * (n : ℝ)) + 1 := Int.ceil_lt_add_one _
  have hsum_lt_n : ((n : ℤ) + ⌈Cmix * Real.log (nu⁻¹ * (n : ℝ))⌉ : ℝ) < ((j : ℤ) + 1 : ℝ) := by
    push_cast
    linarith only [hgapn, hceil_lt_n]
  have hsum_lt_n' : (n : ℤ) + ⌈Cmix * Real.log (nu⁻¹ * (n : ℝ))⌉ < (j : ℤ) + 1 := by
    exact_mod_cast hsum_lt_n
  have hH3n : (n : ℤ) ≤ (j : ℤ) - ⌈Cmix * Real.log (nu⁻¹ * (n : ℝ))⌉ := by omega
  -- H1
  have hH1 : (L : ℝ) - (n : ℝ) ≤
      Cmix⁻¹ * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (2 : ℝ) := by
    by_cases hnL : n ≤ L
    · have hL2n : (L : ℝ) ≤ 2 * (n : ℝ) := by linarith only [hn_ge, hLabsorbApplied]
      have hS := hSstarApplied n hL2n hnL
      have hstep : Cmix⁻¹ * (c * (Cmix * M) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
          Cmix⁻¹ * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hS (inv_pos.2 hCmixpos).le
      have heq : Cmix⁻¹ * (c * (Cmix * M) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) =
          c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
        field_simp
      rw [heq] at hstep
      linarith only [hn_ge, hstep]
    · push Not at hnL
      have h1 : (L : ℝ) < (n : ℝ) := by exact_mod_cast hnL
      have h2 : (0 : ℝ) ≤ (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (2 : ℝ) := by
        have heq2 : (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (2 : ℝ) =
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (2 : ℕ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [heq2]
        positivity
      have h3 : (0 : ℝ) ≤ Cmix⁻¹ * (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar
          nu L P (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (2 : ℝ) :=
        mul_nonneg (inv_pos.2 hCmixpos).le h2
      linarith only [h1, h3]
  have hMixResult := hMixApplied j n L hL1 hH1 hH2 hH3 hH4 hH3n
  -- gammaTriangleConst (1/3) ≥ 1
  have hgc2 : (2 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    Homogenization.IndependentSums.two_le_gammaGrowthConst _
  have hgcge1 : (1 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    le_trans (by norm_num) hgc2
  have hpow1 : (1 : ℝ) ≤
      Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) ^ (12 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (12 : ℝ) := (Real.one_rpow 12).symm
      _ ≤ Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) ^ (12 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hgcge1 (by norm_num)
  have hgtc1 : (1 : ℝ) ≤ Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) := by
    unfold Homogenization.IndependentSums.gammaTriangleConst
    linarith only [hpow1]
  -- n vs j
  have hnCmixLogL_nonneg : 0 ≤ Cmix * Real.log (nu⁻¹ * (L : ℝ)) :=
    mul_nonneg hCmix_nonneg hlogL_nonneg
  have hnltj : (n : ℝ) < (j : ℝ) := by linarith only [hgap, hnCmixLogL_nonneg]
  have hnlej : (n : ℝ) ≤ (j : ℝ) := le_of_lt hnltj
  have hjpos : (0 : ℝ) < (j : ℝ) := lt_trans hn0 hnltj
  have hn3000pos : (0 : ℝ) < (n : ℝ) ^ (3000 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hj3000pos : (0 : ℝ) < (j : ℝ) ^ (3000 : ℝ) := Real.rpow_pos_of_pos hjpos _
  have hpow3000 : (n : ℝ) ^ (3000 : ℝ) ≤ (j : ℝ) ^ (3000 : ℝ) :=
    Real.rpow_le_rpow hn0.le hnlej (by norm_num)
  have hjneg3000_le : (j : ℝ) ^ (-(3000 : ℝ)) ≤ (n : ℝ) ^ (-(3000 : ℝ)) := by
    rw [Real.rpow_neg hjpos.le, Real.rpow_neg hn0.le]
    exact (inv_le_inv₀ hj3000pos hn3000pos).2 hpow3000
  set S := SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) with hSdef
  have hSinvpos : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar_pos_cutoff
      hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hSpos : 0 < S := by
    rw [hSdef,
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar_eq_inv hnu L hJ4 (n : ℤ)
        hSinvpos]
    exact inv_pos.2 hSinvpos
  set A1 := Cmix * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * S ^ (-(1 : ℝ)) with hA1def
  set A2 := Cmix * ((L - n : ℕ) : ℝ) * S ^ (-(2 : ℝ)) with hA2def
  set A3 := Cmix * (n : ℝ) ^ (-(3000 : ℝ)) with hA3def
  have hA3nonneg : (0 : ℝ) ≤ A3 := by rw [hA3def]; positivity
  have hA1nonneg : (0 : ℝ) ≤ A1 := by
    rw [hA1def]
    have : (0:ℝ) ≤ S ^ (-(1:ℝ)) := (Real.rpow_pos_of_pos hSpos _).le
    positivity
  have hA2nonneg : (0 : ℝ) ≤ A2 := by
    rw [hA2def]
    have : (0:ℝ) ≤ S ^ (-(2:ℝ)) := (Real.rpow_pos_of_pos hSpos _).le
    positivity
  have hA3pos : (0 : ℝ) < A3 := by rw [hA3def]; positivity
  have hA1A3pos : (0 : ℝ) < A1 + A3 := by linarith only [hA1nonneg, hA3pos]
  have hA2A3pos : (0 : ℝ) < A2 + A3 := by linarith only [hA2nonneg, hA3pos]
  have hX3ampLe : Cmix * (j : ℝ) ^ (-(3000 : ℝ)) ≤ A3 := by
    rw [hA3def]
    exact mul_le_mul_of_nonneg_left hjneg3000_le hCmix_nonneg
  by_cases hcase : (j : ℝ) ≤ (L : ℝ) + Cmix * Real.log (nu⁻¹ * (L : ℝ))
  · obtain ⟨X1, X2, X3, hX1meas, hX1big, hX2meas, hX2big, hX3meas, hX3big, hbil⟩ :=
      hMixResult.1 hcase
    have hX1big13 := SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigO_of_gammaSigma_le
      (sigma1 := 2) (sigma2 := (1 : ℝ) / 3) (by norm_num) hX1big
    have hX2big13 := SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigO_of_gammaSigma_le
      (sigma1 := 1) (sigma2 := (1 : ℝ) / 3) (by norm_num) hX2big
    have hX1pad : Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X1 (A1 + A3) :=
      Homogenization.IndependentSums.IsBigOWith.mono_scale hX1big13
        (by linarith only [hA3nonneg])
    have hX2pad : Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2 (A2 + A3) :=
      Homogenization.IndependentSums.IsBigOWith.mono_scale hX2big13
        (by linarith only [hA3nonneg])
    have hX3pad : Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X3 A3 :=
      Homogenization.IndependentSums.IsBigOWith.mono_scale hX3big hX3ampLe
    have hcombined := Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := P.toMeasure) (Finset.univ : Finset (Fin 3))
      (X := ![X1, X2, X3]) (a := ![A1 + A3, A2 + A3, A3]) (σ := (1 : ℝ) / 3)
      (by norm_num) Finset.univ_nonempty
      (fun i _ => by
        fin_cases i
        · simpa using hA1A3pos
        · simpa using hA2A3pos
        · simpa using hA3pos)
      (fun i _ => by
        fin_cases i
        · simpa using hX1pad
        · simpa using hX2pad
        · simpa using hX3pad)
      (fun i _ => by
        fin_cases i
        · simpa using hX1meas
        · simpa using hX2meas
        · simpa using hX3meas)
    have hamp3eq : (3 : ℝ) * A3 = 3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ)) := by rw [hA3def]; ring
    refine ⟨X1 + X2 + X3, hX1meas.add hX2meas |>.add hX3meas, ?_, ?_⟩
    · have hsum_eq : (fun ω => ∑ i : Fin 3, (![X1, X2, X3] i) ω) = X1 + X2 + X3 := by
        funext ω
        simp [Fin.sum_univ_three]
      have hamp_eq : Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
          ∑ i : Fin 3, (![A1 + A3, A2 + A3, A3] i) =
          Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
            (A1 + (A2 + 3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ)))) := by
        rw [← hamp3eq]
        simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        ring
      rw [hsum_eq, hamp_eq] at hcombined
      exact hcombined
    · intro omega p q
      simpa using hbil omega p q
  · push Not at hcase
    obtain ⟨X4, hX4meas, hX4big, hbil⟩ := hMixResult.2 hcase
    have hX4big13 := SuperdiffusionCLT.Section4.HomogBelow.homogBelow_isBigO_of_gammaSigma_le
      (sigma1 := 1) (sigma2 := (1 : ℝ) / 3) (by norm_num) hX4big
    have hamp3eq' : (3 : ℝ) * A3 = 3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ)) := by rw [hA3def]; ring
    have hfinalAmp : Cmix * (j : ℝ) ^ (-(3000 : ℝ)) ≤
        Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
          (A1 + (A2 + 3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ)))) := by
      rw [← hamp3eq']
      have h1 : Cmix * (j : ℝ) ^ (-(3000 : ℝ)) ≤ A3 := hX3ampLe
      have h2 : A3 ≤ A1 + (A2 + 3 * A3) := by linarith only [hA1nonneg, hA2nonneg, hA3nonneg]
      have h3 : A1 + (A2 + 3 * A3) ≤
          Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
            (A1 + (A2 + 3 * A3)) := by
        have hnn : (0 : ℝ) ≤ A1 + (A2 + 3 * A3) := by
          linarith only [hA1nonneg, hA2nonneg, hA3nonneg]
        calc A1 + (A2 + 3 * A3) = 1 * (A1 + (A2 + 3 * A3)) := (one_mul _).symm
          _ ≤ Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
                (A1 + (A2 + 3 * A3)) := mul_le_mul_of_nonneg_right hgtc1 hnn
      linarith only [h1, h2, h3]
    refine ⟨X4, hX4meas, ?_, ?_⟩
    · exact Homogenization.IndependentSums.IsBigOWith.mono_scale hX4big13 hfinalAmp
    · intro omega p q
      simpa using hbil omega p q

end SuperdiffusionCLT.Section4.HomogBelow
