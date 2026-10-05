/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmAssemblyP3Wrap
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmAssemblyStrictMono
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmGrowthExact
public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff

/-!
**The wiring lemma for the application of [AK, Theorem 6.1].**
Combines the (P2′) verification (`ThetaLmP2Prime.lean`, taken here as an
already-obtained witness `H, D, m2, PsiS, KPsiS, pPsiS` from
`homogBelow_P2prime_verified`, since P2′ does not depend on the scale `m`
being applied and is shared by both of Step 3's applications of [AK, Theorem 6.1]) with the
(P3′) verification (`ThetaLmAssemblyP3Wrap.lean`'s `homogBelow_p3prime_omegaSeq`,
using the global majorant `homogBelow_omegaSeq`) to fully discharge every
premise of `akhc_weakerP3` up to
its own `∀ m m0, max m2 m3 ≤ m → ... → ∀ n, m+4m0≤n → thetaCutoff n - 1 ≤ ...`
tail, at the paper's own choice `γ := 1/2` (`e.checkingp2prime`) and
`β := 1/2, L₁ := 4C_mix, L₂ := ν⁻¹` (the proof of `l.we.can.apply.hc`).

`C61`/`alpha61` are the witnesses of [AK, Theorem 6.1] (the outer
`∃C,...∃c,...∃alpha,...` of `akhc_weakerP3`,
obtained once by the caller and shared across both applications in Step 3);
`hAKHCraw` is `hAKHC`'s inner clause after that destructuring, with `C ↦ C61`
and (of [AK, Theorem 6.1]) `alpha ↦ alpha61` substituted textually — copied verbatim
from the statement of `akhc_weakerP3` (reproduced in the `hAKHC` binder of
`FromThetaLm.lean`) with no proof content added. `H, D, m2,
PsiS, KPsiS, pPsiS` are `homogBelow_P2prime_verified`'s witnesses (also
obtained once by the caller, since (P2′) is scale-independent); `Cmix` is
`mixing_below_cutoff`'s witness and `hMixApplied` its inner clause
specialized at `nu, P` and the shell laws, exactly as `ThetaLmP3Prime.lean`
already takes it. `c, hc` are `lNaught_sstar_lower`'s witness (obtained once
by the caller); `m3` is any natural number already known to clear the real
threshold `hm3ge` (the caller supplies it, typically a `Nat.ceil`).

The conclusion of this lemma is the type inferred by Lean's elaboration of the proof (it
was obtained by leaving the return type as a hole), so it matches the proof exactly. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- **The application of [AK, Theorem 6.1], fully wired**: `hAKHCraw` (the clause of [AK],
at `C61, alpha61`), specialized at `γ := 1/2` with the (P2′) witness
`H, D, m2, PsiS, KPsiS, pPsiS`, and at `β := 1/2, L₁ := 4C_mix, L₂ := ν⁻¹`
with the (P3′) witness `Psi := Γ_{1/3}, KPsi := K_{Γ_{1/3}}, pPsi := d+1,
omegaSeq := homogBelow_omegaSeq`, leaves exactly the `∀ m m0, ...`
tail. -/
theorem homogBelow_akhcApplication
    (d : ℕ) [NeZero d]
    (C61 : ℝ) (_hC61_1 : 1 ≤ C61)
    (alpha61 : ℝ) (_halpha61pos : 0 < alpha61) (_halpha61lt1 : alpha61 < 1)
    (hAKHCraw :
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ L : ℕ,
          -- (P2') [AK] `a.ellipticity.weaker`
          ∀ (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ),
            0 ≤ gamma → gamma ≤ 1 / 2 → 1 ≤ H → 0 ≤ D →
            MonotoneOn PsiS (Set.Ici 0) → (∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t) →
            1 ≤ KPsiS → 3 ≤ pPsiS →
            (∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
              s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t)) →
            (∀ j : ℕ, m2 ≤ j →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
                  (H * (j : ℝ) ^ D) ∧
                ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                  (Q : Homogenization.TriadicCube d),
                  Q.scale ≤ (j : ℤ) →
                  Homogenization.cubeCenter Q ∈
                      Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
                    Homogenization.BlockMatLoewnerLE
                      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                            omega L).toCoeffField)
                      ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                            X omega) •
                        SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (j : ℤ))))) →
          -- (P3') [AK] `a.CFS.weaker`
          ∀ (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ),
            0 ≤ beta → beta ≤ 1 / 2 → 1 ≤ L1 → 1 ≤ L2 →
            (∀ k : ℕ, 0 < omegaSeq k) → Antitone omegaSeq →
            Filter.Tendsto omegaSeq Filter.atTop (nhds 0) →
            StrictMonoOn Psi (Set.Ici 0) → (∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) →
            1 ≤ KPsi → (d : ℝ) + 1 ≤ pPsi →
            (∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
              s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t)) →
            (∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
              (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
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
                            q))) →
          -- the conclusion of [AK]
          ∀ m m0 : ℕ, max m2 m3 ≤ m →
            omegaSeq m ^ 2 ≤
              (C61 * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)))⁻¹ →
            C61 * (L1 + (1 + D) / (1 - gamma)) * (1 + D) / ((1 - beta) * (1 - gamma)) *
                Real.log
                  ((C61 * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
                      C61 / (min 3 pPsiS - 2) *
                        Real.exp (C61 * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                          (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) *
                Real.log (3 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 *
                  (2 + L1 * Real.log
                  ((C61 * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
                      C61 / (min 3 pPsiS - 2) *
                        Real.exp (C61 * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                          (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0))) ≤
              (m0 : ℝ) →
            ∀ n : ℕ, m + 4 * m0 ≤ n →
              SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
                C61 * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) *
                    omegaSeq m ^ 2 +
                  C61 * (3 : ℝ) ^
                    (-(min alpha61 ((1 - gamma) / 2) * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ)))))
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (L : ℕ) (hL1 : 1 ≤ L)
    (H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
    (hH1 : 1 ≤ H) (hD0 : 0 ≤ D)
    (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSge1 : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
    (hKPsiS1 : 1 ≤ KPsiS) (hpPsiS2 : 3 ≤ pPsiS)
    (hgrowthPsiS : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
    (hexistsPsiS : ∀ j : ℕ, m2 ≤ j →
      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
        ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
          (Q : Homogenization.TriadicCube d), Q.scale ≤ (j : ℤ) →
          Homogenization.cubeCenter Q ∈
              Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                    omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-((1 / 2 : ℝ) * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    (Cmix : ℝ) (hCmix1 : 1 ≤ Cmix)
    (M alpha : ℝ)
    (c : ℝ) (hc : 0 < c)
    (m3 : ℕ)
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
    (hm3ge : (L : ℝ) - c * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m3 : ℝ))
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
          ∀ m m0 : ℕ, max m2 m3 ≤ m →
            SuperdiffusionCLT.Section4.HomogBelow.homogBelow_omegaSeq nu L Cmix P m ^ 2 ≤
              (C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)))⁻¹ →
            C61 * ((4 * Cmix) + (1 + D) / (1 - (1/2 : ℝ))) * (1 + D) / ((1 - (1/2 : ℝ)) * (1 - (1/2 : ℝ))) *
                Real.log
                  ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)) +
                      C61 / (min 3 pPsiS - 2) *
                        Real.exp (C61 * (((4 * Cmix) + D / (1 - (1/2 : ℝ))) * Real.log (2 * nu⁻¹) +
                          (D + Real.log (H + KPsiS)) / (1 - (1/2 : ℝ))))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) *
                Real.log (3 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 *
                  (2 + (4 * Cmix) * Real.log
                  ((C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)) +
                      C61 / (min 3 pPsiS - 2) *
                        Real.exp (C61 * (((4 * Cmix) + D / (1 - (1/2 : ℝ))) * Real.log (2 * nu⁻¹) +
                          (D + Real.log (H + KPsiS)) / (1 - (1/2 : ℝ))))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0))) ≤
              (m0 : ℝ) →
            ∀ n : ℕ, m + 4 * m0 ≤ n →
              SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
                C61 * (Homogenization.IndependentSums.gammaGrowthConst (1/3)) ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) ((d : ℝ) + 1) - (d : ℝ)) *
                    SuperdiffusionCLT.Section4.HomogBelow.homogBelow_omegaSeq nu L Cmix P m ^ 2 +
                  C61 * (3 : ℝ) ^
                    (-(min alpha61 ((1 - (1/2 : ℝ)) / 2) * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ))))

    := by
  have hAfterP2 := hAKHCraw nu hnu hnu1 P hPrefix hJ2 hJ4 L (1 / 2 : ℝ) H D m2 PsiS KPsiS pPsiS
    (by norm_num) (by norm_num) hH1 hD0 hPsiSMono hPsiSge1 hKPsiS1 hpPsiS2 hgrowthPsiS hexistsPsiS
  have hCmixpos : (0 : ℝ) < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have homegaPos := homogBelow_omegaSeq_pos nu hnu L Cmix P hPrefix hJ2 hJ3 hJ4 hCmixpos
  have homegaAnti := homogBelow_omegaSeq_antitone nu hnu L Cmix P hPrefix hJ2 hJ3 hJ4 hCmixpos
  have homegaTendsto := homogBelow_omegaSeq_tendsto_zero nu L Cmix P hL1
  have hPsiStrictMono := homogBelow_gammaSigma_strictMonoOn (show (0 : ℝ) < 1 / 3 by norm_num)
  have hPsige1 : ∀ t : ℝ, 0 ≤ t → 1 ≤ Homogenization.IndependentSums.gammaSigma (1 / 3) t :=
    fun t ht => Homogenization.IndependentSums.one_le_gammaSigma ht
  have hKPsi1 : (1 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst (1 / 3) :=
    le_trans one_le_two (Homogenization.IndependentSums.two_le_gammaGrowthConst _)
  have hdltpPsi : (d : ℝ) + 1 ≤ (d : ℝ) + 1 := le_refl _
  have hgrowthPsi : ∀ p : ℝ, 1 < p → p ≤ (d : ℝ) + 1 → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ (Homogenization.IndependentSums.gammaGrowthConst (1 / 3)) ^ (3 * ⌈p⌉₊ ^ 2) *
        (Homogenization.IndependentSums.gammaSigma (1 / 3) (t * s) /
          Homogenization.IndependentSums.gammaSigma (1 / 3) t) :=
    fun p hp _hpub t s ht hs =>
      homogBelow_gammaSigma_growthCondition_exact (show (0 : ℝ) < 1 / 3 by norm_num) p hp t s ht hs
  have hL2ge1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  have hL1_4Cmix : (1 : ℝ) ≤ 4 * Cmix := by linarith only [hCmix1]
  have hexistsPsi3 := homogBelow_p3prime_omegaSeq d nu hnu hnu1 P
    hPrefix hJ2 hJ3 hJ4 M alpha Cmix hCmix1 c hc L hL1 hLabsorbApplied hSstarApplied
    hLogLeNApplied hLogRatioApplied hMixApplied
  have hexistsPsi3' := fun (j n : ℕ) (hm3n : m3 ≤ n) (hbj : (1 / 2 : ℝ) * (j : ℝ) < (n : ℝ))
      (hjw : (n : ℝ) < (j : ℝ) - (4 * Cmix) * Real.log (nu⁻¹ * (n : ℝ))) =>
    hexistsPsi3 j n (by have h2 : (m3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm3n
                        linarith only [hm3ge, h2]) hbj hjw
  have hStep := hAfterP2 (1 / 2 : ℝ) (4 * Cmix) nu⁻¹ m3
    (homogBelow_omegaSeq nu L Cmix P)
    (Homogenization.IndependentSums.gammaSigma (1 / 3))
    (Homogenization.IndependentSums.gammaGrowthConst (1 / 3)) ((d : ℝ) + 1)
    (by norm_num) (by norm_num) hL1_4Cmix hL2ge1 homegaPos homegaAnti homegaTendsto
    hPsiStrictMono hPsige1 hKPsi1 hdltpPsi hgrowthPsi hexistsPsi3'
  exact hStep

end SuperdiffusionCLT.Section4.HomogBelow
