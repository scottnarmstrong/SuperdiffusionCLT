/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Ellipticity.EllipticityBelowCutoff
public import SuperdiffusionCLT.Section4.Ellipticity.EnvelopeSandwich
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain

/-!
# The renormalized ellipticity bound below the cutoff, from the union bound

Proposition `p.ellipticity.Ptwoprime`. The statement is
`SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff`.

## Structure of the argument

The printed proof combines exactly two ingredients: the crude comparison
`e.Enaught.vs.Ahom.L.crude` (proved as `ellipBelow_crude_comparison` in
`EllipticityBelowCutoff.lean`) and "a union bound and `e.Enaught.vs.A.and.Ahom`" over every
scale `k ≤ m` and every sub-cube `Q` of `cu_m` at that scale, each contributing a combinatorial
factor `3^{d(m-k)}` (the count of sub-cubes) to a geometric sum in `k`, to produce a *single*
random amplitude witnessing the printed `sup_k` bound.

`e.Enaught.vs.A.and.Ahom` itself -- the per-cube tail bound
`envelopeRatioOn L (openCubeSet Q) omega = O_{Γ1}(1)` -- is available as
`SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain.
blockMatrixOperatorNorm_envelopeRescale_coarseBlockMatrix_le` together with
`isBigOWith_gammaSigma_envelopeRatioOn`. The union bound *combining* the countably many per-cube
tail bounds (one per `(k, Q)` pair, with `Q` ranging over the `3^{d(m-k)}` sub-cubes of `cu_m`
at scale `k`) into the single weighted witness `X` is stated here as the hypothesis `hUnion`; it
is the analogue, for the *first* assertion of `l.bfAm.ellip`, of the union bound over scales and
sub-cubes behind the *third* assertion, and is needed here instead of the latter because the
printed proof of `p.ellipticity.Ptwoprime` cites `e.Enaught.vs.A.and.Ahom`, not
`e.Smgamma.integ`/`e.bfAm.ellip`. The hypothesis is discharged in `Section4/Ellipticity/Union.lean`
(`ellipBelow_union`), which also assembles the fully discharged `ellipBelow_main`.

Given `hUnion`, `ellipBelow_main_of_union` below derives the *exact* conclusion of the main
statement, with no further hypothesis: the crude comparison rescales the envelope
`bfE_L` bound of `hUnion` into the printed `nu^{-2} L` amplitude against
`bfAhom_L(cu_m)`, and `ellipBelow_sandwich_of_opNorm` performs the sqrt-free
bilinear-sandwich conversion (clause (i) of the sandwich forms) at the doubled block level.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Ellipticity

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

variable {d : ℕ}

/-- `ellipBelow_crudeConst d ≥ 1`: the crude comparison constant already
dominates `1`, since it is `2 cutoffEnvelopeConst d + 4 (cutoffEnvelopeConst
d)²` and `cutoffEnvelopeConst d ≥ 1`. -/
theorem ellipBelow_one_le_crudeConst (d : ℕ) : 1 ≤ ellipBelow_crudeConst d := by
  have h1 := one_le_cutoffEnvelopeConst d
  have hsq : 1 ≤ (cutoffEnvelopeConst d) ^ 2 := one_le_pow₀ h1
  unfold ellipBelow_crudeConst
  linarith only [h1, hsq]

/-- `nu ^ (-(2:ℝ)) = nu⁻¹ ^ 2` for `nu > 0`: the real-power reading of the
amplitude in the main statement matches the natural-power reading of the crude
comparison. -/
theorem ellipBelow_rpow_neg_two {nu : ℝ} (hnu : 0 < nu) :
    nu ^ (-(2 : ℝ)) = nu⁻¹ ^ 2 := by
  rw [Real.rpow_neg hnu.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← inv_pow]

/-- **`p.ellipticity.Ptwoprime` from the union bound.** The exact conclusion
of `SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff`,
from the single hypothesis `hUnion` naming the printed union bound in the proof of
`p.ellipticity.Ptwoprime`. `hUnion` is proved,
hypothesis-free, as `ellipBelow_union` (`Section4/Ellipticity/Union.lean`,
which also assembles the fully discharged `ellipBelow_main`). -/
theorem ellipBelow_main_of_union (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
    (hUnion : ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ (P : ProbabilityMeasure (ShellSeq d)),
        ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
          ∀ m L : ℕ, 1 ≤ L → (L : ℝ) ≤ 4 * (m : ℝ) →
            ∃ X : ShellSeq d → ℝ,
              Measurable X ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
                  (C0 * gamma⁻¹) ∧
                ∀ (omega : ShellSeq d) (k : ℤ), k ≤ (m : ℤ) →
                  ∀ Q : TriadicCube d, Q.scale = k →
                    cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
                      envelopeRatioOn L (openCubeSet Q) omega ≤
                        (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P →
          ShellLawJ1Restriction d P →
          ShellLawJ2 d P →
          ShellLawJ3 d P →
          ShellLawJ4 d P →
          ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
            ∀ m L : ℕ, 1 ≤ L → (L : ℝ) ≤ 4 * (m : ℝ) →
              ∃ X : ShellSeq d → ℝ,
                Measurable X ∧
                IndependentSums.IsBigO P.toMeasure
                    (IndependentSums.gammaSigma 1) X
                    (C * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (L : ℝ)) ∧
                  ∀ (omega : ShellSeq d) (k : ℤ), k ≤ (m : ℤ) →
                    ∀ Q : TriadicCube d, Q.scale = k →
                      cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
                        ∀ p q : BlockVec d,
                          2 * blockVecDot p
                                (blockMatVecMul
                                  (coarseBlockMatrix (cubeSet Q)
                                    (coefficientCutoff nu omega L).toCoeffField)
                                  q) ≤
                            (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega *
                              (blockVecDot p
                                  (blockMatVecMul
                                    (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))))
                                    p) +
                                blockVecDot q
                                  (blockMatVecMul
                                    (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))))
                                    q)) := by
  obtain ⟨C0, hC0, hUnion'⟩ := hUnion
  have hcrude1 := ellipBelow_one_le_crudeConst d
  refine ⟨C0 * ellipBelow_crudeConst d, ?_, ?_⟩
  · calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C0 * ellipBelow_crudeConst d :=
        mul_le_mul hC0 hcrude1 zero_le_one (by linarith only [hC0])
  · intro nu hnu hnu1 P hPrefix _hJ1 hJ2 hJ3 hJ4 gamma hgamma0 hgamma1 m L hL hL4
    obtain ⟨X, hXmeas, hXbig, hXbound⟩ :=
      hUnion' P hPrefix hJ2 hJ3 hJ4 gamma hgamma0 hgamma1 m L hL hL4
    set c : ℝ := ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) with hc
    have hcnn : 0 ≤ c := by
      have : (0 : ℝ) ≤ ellipBelow_crudeConst d := le_trans zero_le_one hcrude1
      positivity
    refine ⟨fun omega => c * X omega, hXmeas.const_mul c, ?_, ?_⟩
    · have hconst := hXbig.const_mul (μ := P.toMeasure) (Ψ := IndependentSums.gammaSigma 1)
        (A := C0 * gamma⁻¹) hcnn
      have hrpow := ellipBelow_rpow_neg_two hnu
      have hampEq : c * (C0 * gamma⁻¹) =
          C0 * ellipBelow_crudeConst d * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (L : ℝ) := by
        rw [hc, hrpow]; ring
      rwa [hampEq] at hconst
    · intro omega k hk Q hQscale hQmem p q
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q
        (coefficientCutoff nu omega L).toCoeffField]
      have hratio := hXbound omega k hk Q hQscale hQmem
      have hopnorm : blockMatrixOperatorNorm (envelopeRescale d nu L
          (coarseBlockMatrix (openCubeSet Q) (coefficientCutoff nu omega L).toCoeffField)) ≤
          envelopeRatioOn L (openCubeSet Q) omega := by
        have h := blockMatrixOperatorNorm_envelopeRescale_coarseBlockMatrix_le
          (cubeDomain Q) hnu omega L
        rwa [cubeDomain_coe] at h
      have hopnorm2 : blockMatrixOperatorNorm (envelopeRescale d nu L
          (coarseBlockMatrix (openCubeSet Q) (coefficientCutoff nu omega L).toCoeffField)) ≤
          (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega := hopnorm.trans hratio
      have htnn : 0 ≤ (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega :=
        le_trans (blockMatrixOperatorNorm_nonneg _) hopnorm2
      have hsandwich := ellipBelow_sandwich_of_opNorm hnu L
        (coarseBlockMatrix (openCubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
        hopnorm2 p q
      have hcrude := ellipBelow_crude_comparison d hnu hnu1 P hPrefix hJ2 hJ3 hJ4 L m hL
      have hpEnv : blockVecDot p (blockMatVecMul (envelopeBlockMat d nu L) p) ≤
          ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) *
            blockVecDot p
              (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) p) := by
        have hp := hcrude p
        rw [blockMatVecMul_blockSMul, blockVecDot_smul_right] at hp
        linarith only [hp]
      have hqEnv : blockVecDot q (blockMatVecMul (envelopeBlockMat d nu L) q) ≤
          ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) *
            blockVecDot q
              (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) q) := by
        have hq := hcrude q
        rw [blockMatVecMul_blockSMul, blockVecDot_smul_right] at hq
        linarith only [hq]
      have hdistrib : ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) *
          (blockVecDot p
              (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) p) +
            blockVecDot q
              (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) q)) =
          ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) *
              blockVecDot p
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) p) +
            ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) *
              blockVecDot q
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) q) := by
        ring
      have hEnvSum : blockVecDot p (blockMatVecMul (envelopeBlockMat d nu L) p) +
          blockVecDot q (blockMatVecMul (envelopeBlockMat d nu L) q) ≤
          ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) *
            (blockVecDot p
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) p) +
              blockVecDot q
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) q)) := by
        linarith only [hpEnv, hqEnv, hdistrib]
      have hstep := mul_le_mul_of_nonneg_left hEnvSum htnn
      have heqRHS : ((3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * X omega) *
          (ellipBelow_crudeConst d * nu⁻¹ ^ 2 * (L : ℝ) *
            (blockVecDot p
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) p) +
              blockVecDot q
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) q))) =
          (3 : ℝ) ^ (-(gamma * ((k : ℝ) - (m : ℝ)))) * (c * X omega) *
            (blockVecDot p
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) p) +
              blockVecDot q
                (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))) q)) := by
        rw [hc]; ring
      linarith only [hsandwich, hstep, heqRHS]

end

end SuperdiffusionCLT.Section4.Ellipticity
