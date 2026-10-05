/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalETail
public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonRootTail
public import SuperdiffusionCLT.Section4.NewMixing.ParamStatement
public import SuperdiffusionCLT.Section2.Cutoff.Centered
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Frozen.Section4.LNaught

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

noncomputable section

/-- The shifted, `cu_m`-centered cutoff field `a_L - (k_L)_{cu_m}` on
`z + cu_n`, `z = 3^{n-3} k`, as it enters `mathcalE_bounds`. -/
def srootE_field {d : ℕ} [NeZero d] (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (L m n : ℕ)
    (k : Fin d → ℤ) : Homogenization.CoeffField d :=
  fun x =>
    (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff nu omega L
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))).toCoeffField
      ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)

/-- The shifted limiting field `ν Id + k - (k)_{cu_m}`. -/
def srootE_limField {d : ℕ} (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (m n : ℕ)
    (k : Fin d → ℤ) : Homogenization.CoeffField d :=
  fun x =>
    nu • (1 : Homogenization.Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)

/-- The `l`-th term `css_{2s} 3^{-2sl} X_{n-l}` of the series whose square
root is `E_{s,2}(cu_n; a, a0)`. -/
def srootE_term {d : ℕ} (s : ℝ) (a : Homogenization.CoeffField d)
    (a0 : Homogenization.Mat d) (n l : ℕ) : ℝ :=
  Homogenization.geometricWeight s 2 l *
    Real.rpow (Homogenization.scaleResponseAtScale (Homogenization.originCube d (n : ℤ))
      ((n : ℤ) - (l : ℤ)) Homogenization.MultiscaleExponent.infinity a a0) 2

theorem srootE_homErr_eq {d : ℕ} (s : ℝ) (a : Homogenization.CoeffField d)
    (a0 : Homogenization.Mat d) (n : ℕ) :
    Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
        Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite (2 : ℝ)) a a0 =
      Real.sqrt (∑' l : ℕ, srootE_term s a a0 n l) := by
  rw [Real.sqrt_eq_rpow]
  rfl

theorem srootE_term_nonneg {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (a : Homogenization.CoeffField d)
    (a0 : Homogenization.Mat d) (n l : ℕ) : 0 ≤ srootE_term s a a0 n l := by
  unfold srootE_term
  refine mul_nonneg ?_ ?_
  · unfold Homogenization.geometricWeight Homogenization.geometricDiscount
    refine mul_nonneg ?_ (Real.rpow_nonneg (by norm_num) _)
    have : Real.rpow (3 : ℝ) (-s * 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hs])
    linarith only [this]
  · have h := Real.rpow_two (Homogenization.scaleResponseAtScale
      (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ))
      Homogenization.MultiscaleExponent.infinity a a0)
    change 0 ≤ (Homogenization.scaleResponseAtScale (Homogenization.originCube d (n : ℤ))
      ((n : ℤ) - (l : ℤ)) Homogenization.MultiscaleExponent.infinity a a0) ^ (2 : ℝ)
    rw [h]
    exact sq_nonneg _

theorem srootE_two_sqrt_le {a C y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) (h4 : 4 * a ≤ C) :
    2 * Real.sqrt (a * C * y ^ 2) ≤ C * y := by
  have hC : 0 ≤ C := le_trans (by linarith only [ha]) h4
  rw [Real.sqrt_mul (mul_nonneg ha hC), Real.sqrt_sq hy]
  have hs : Real.sqrt (a * C) ≤ C / 2 := by
    rw [Real.sqrt_le_left (by linarith only [hC])]
    nlinarith only [h4, hC]
  nlinarith only [hs, hy]

theorem srootE_sqrt_add3_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hc
  have p1 := Real.sqrt_nonneg a
  have p2 := Real.sqrt_nonneg b
  have p3 := Real.sqrt_nonneg c
  nlinarith only [h1, h2, h3, mul_nonneg p1 p2, mul_nonneg p1 p3, mul_nonneg p2 p3]

/-- **Skeleton of `p.new.mixing.attempt`.** Every input is a named hypothesis:

* `hParam` — the conclusion of the mixing-lemma family (`l.new.mixing.parameterized`;
  statement recorded in `Section4/NewMixing/ParamStatement.lean`),
  consumed by `hNear` only;
* `hNear` — near scales `l ∈ [n - h̄, n]`, `h̄ = ⌈C₀ s⁻¹ log m⌉`, for the fully
  centered field `a_L - (k_L)_{cu_m}` uniformly over the cutoff range
  `L ≥ m - C₁ s⁻¹ h`: `e.new.mixing.attempt.near` after the
  recentering step of the proof (it packages `e.new.mixing.attempt.local.base`,
  the tail comparison, `l.maximums.Gamma.s`, and the
  shift term of the recentering; `l.new.mixing.parameterized` enters here);
* `hDeep` — deep scales `l < n - h̄`: `e.new.mixing.attempt.deep`,
  with the same recentering, which fixes `C₀`;
* `hLimit` — the Fatou passage to the limiting coefficient.

The range constant `C₁` of the cutoffs is a free parameter above the
package constant `A`, and the bounds are linear in `C₁` at the square level,
so that the single constant `C` can serve as both (the square root in
the last step of the proof closes the loop: `2 √(A C) ≤ C` once `C ≥ 4A`). The near/deep
split, the square root with `e.powerofGammasigma`, the `Γ_{1/3}` triangle
inequality, the Fatou envelope and the constant bookkeeping are proved here. -/
theorem srootE_mathcalE_bounds_of_inputs (d : ℕ) [NeZero d]
    (hParam :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ alpha M K : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K →
            ∀ L m r : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (L : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (m : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                ∀ (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0),
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    ∀ eta : Homogenization.BlockVec d,
                      SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
                        Homogenization.Book.Ch02.doubledResponseJ
                          (Homogenization.Book.Ch02.cubeDomain
                            (Homogenization.originCube d (m : ℤ)))
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta) ≤
                        C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                            (-(2 : ℝ)) *
                            ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                              max 0 ((L : ℝ) - (m : ℝ)) +
                              K * Real.log (L : ℝ) ^ (2 : ℝ)) +
                          X1 omega +
                          (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                                (-(1 : ℝ)) *
                              (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega)
    (hNear : (
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1),
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ alpha M K : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K →
            ∀ L m r : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (L : ℝ) →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
                (m : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ) →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X1
                    (C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                        (-(2 : ℝ)) *
                      (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X2
                    (C * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                ∀ (h0 : Homogenization.Mat d) (hh0 : Homogenization.matTranspose h0 = -h0),
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    ∀ eta : Homogenization.BlockVec d,
                      SuperdiffusionCLT.Section2.Carriers.blockVecNorm eta = 1 →
                        Homogenization.Book.Ch02.doubledResponseJ
                          (Homogenization.Book.Ch02.cubeDomain
                            (Homogenization.originCube d (m : ℤ)))
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P (-(1 : ℝ) / 2) eta)
                          (SuperdiffusionCLT.Section4.NewMixing.newMixParam_bfAhomPow nu r P ((1 : ℝ) / 2) eta) ≤
                        C * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                            (-(2 : ℝ)) *
                            ((Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2 +
                              max 0 ((L : ℝ) - (m : ℝ)) +
                              K * Real.log (L : ℝ) ^ (2 : ℝ)) +
                          X1 omega +
                          (1 + (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu r P) ^
                                (-(1 : ℝ)) *
                              (Homogenization.Book.Ch02.matrixOperatorNorm h0) ^ 2) * X2 omega) →
      ∀ C0 : ℝ, 1 ≤ C0 → ∃ A : ℝ, 1 ≤ A ∧ ∀ C1 : ℝ, A ≤ C1 →
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
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ K : ℝ, C1 ≤ K → ∀ m n : ℕ,
            SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
            m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n → n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∃ Y1 Y2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable Y1 ∧
                IsBigO P.toMeasure (gammaSigma 1) Y1
                  (A * C1 * (s⁻¹ * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
                    Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ^ 2) ∧
                Measurable Y2 ∧
                IsBigO P.toMeasure (gammaSigma (1 / 3)) Y2 (A * (m : ℝ) ^ (-(2000 : ℝ))) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, (m : ℝ) - C1 * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                  ∑ l ∈ Finset.range (⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ + 1),
                      srootE_term s (srootE_field nu omega L m n k)
                        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) n l ≤
                    A * C1 * (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
                      Real.log (m : ℝ)) ^ 2 + Y1 omega + Y2 omega)
    (hDeep : ∃ C0 : ℝ, 1 ≤ C0 ∧ ∃ A : ℝ, 1 ≤ A ∧ ∀ C1 : ℝ, A ≤ C1 →
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
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ K : ℝ, C1 ≤ K → ∀ m n : ℕ,
            SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
            m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n → n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∃ Y2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable Y2 ∧
                IsBigO P.toMeasure (gammaSigma (1 / 3)) Y2 (A * (m : ℝ) ^ (-(2000 : ℝ))) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L : ℕ, (m : ℝ) - C1 * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                  ∑' l : ℕ, srootE_term s (srootE_field nu omega L m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) n
                      (l + (⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ + 1)) ≤ Y2 omega)
    (hLimit : ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
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
                    (srootE_field nu omega L m n k) ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) ≤ B) →
                Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
                  Homogenization.MultiscaleExponent.infinity
                  (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                  (srootE_limField nu omega m n k) ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧
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
          ∀ s : ℝ, 0 < s → s ≤ 1 →
            ∀ K : ℝ, C ≤ K →
              ∀ m n : ℕ,
                SuperdiffusionCLT.Frozen.Section4.lNaught C (C * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
                m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n →
                n ≤ m →
                ∀ k : Fin d → ℤ,
                                    (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                  ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X1 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma 2) X1
                        (C * s⁻¹ * K ^ ((1 : ℝ) / 2) *
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                              P)⁻¹ *
                          Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ∧
                    Measurable X2 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma (2 / 3)) X2
                        (C * (m : ℝ) ^ (-(1000 : ℝ))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ L : ℕ, (m : ℝ) - C * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                          Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                                    nu omega L
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))).toCoeffField
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) +
                            Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                nu • (1 : Homogenization.Mat d) +
                                  SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                    omega
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))
                                    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) ≤
                            C * s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) *
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu m P)⁻¹ *
                                Real.log (m : ℝ) +
                              X1 omega + X2 omega
    := by
  obtain ⟨C0, hC01, Ad, hAd1, hDeepA⟩ := hDeep
  obtain ⟨An, hAn1, hNearA⟩ := hNear hParam C0 hC01
  have hA1 : 1 ≤ max An Ad := le_trans hAn1 (le_max_left _ _)
  refine ⟨16 * max An Ad, by linarith only [hA1], ?_⟩
  intro nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m n hLm hn1 hn2
    k hk
  have hAnC : An ≤ 16 * max An Ad := by
    have := le_max_left An Ad; linarith only [this, hA1]
  have hAdC : Ad ≤ 16 * max An Ad := by
    have := le_max_right An Ad; linarith only [this, hA1]
  obtain ⟨Y1, Y2n, hY1m, hY1O, hY2nm, hY2nO, hNae⟩ := hNearA (16 * max An Ad) hAnC nu cStar
    nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m n hLm hn1 hn2 k hk
  obtain ⟨Y2d, hY2dm, hY2dO, hDae⟩ := hDeepA (16 * max An Ad) hAdC nu cStar
    nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m n hLm hn1 hn2 k hk
  have hLae := hLimit nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 m n hn2
    k hk
  have hσ : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4
  have hKpos : 0 ≤ K := le_trans (by linarith only [hA1]) hK
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hy : 0 ≤ s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ * Real.log (m : ℝ) := by
    have := Real.rpow_nonneg hs0.le (-((1 : ℝ) / 2))
    have := Real.rpow_nonneg hKpos ((1 : ℝ) / 2)
    have := inv_nonneg.2 hσ.le
    positivity
  have hy1 : 0 ≤ s⁻¹ * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ * Real.log (m : ℝ) ^ ((1 : ℝ) / 2) := by
    have := Real.rpow_nonneg hKpos ((1 : ℝ) / 2)
    have := Real.rpow_nonneg hlogm ((1 : ℝ) / 2)
    have := inv_nonneg.2 hσ.le
    have := inv_nonneg.2 hs0.le
    positivity
  have hy2 : 0 ≤ (m : ℝ) ^ (-(1000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hm2000 : (m : ℝ) ^ (-(2000 : ℝ)) = ((m : ℝ) ^ (-(1000 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m)]
    norm_num
  have h4An : 4 * An ≤ 16 * max An Ad := by
    have := le_max_left An Ad; linarith only [this, hAn1]
  set A : ℝ := max An Ad with hAdef
  set C : ℝ := 16 * A with hCdef
  have hAn0 : 0 ≤ An := le_trans zero_le_one hAn1
  have hB1 : 0 ≤ An * C * (s⁻¹ * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
      Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
    have : 0 ≤ C := by linarith only [hA1]
    positivity
  have hB2 : 0 ≤ A * (m : ℝ) ^ (-(2000 : ℝ)) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg m) (-(2000 : ℝ) : ℝ)
    have : 0 ≤ A := by linarith only [hA1]
    positivity
  refine ⟨fun ω => 2 * Real.sqrt |Y1 ω|, fun ω => 2 * Real.sqrt (|Y2n ω| + |Y2d ω|),
    measurable_const.mul (Real.continuous_sqrt.measurable.comp (continuous_abs.measurable.comp hY1m)), ?_,
    measurable_const.mul (Real.continuous_sqrt.measurable.comp
      ((continuous_abs.measurable.comp hY2nm).add (continuous_abs.measurable.comp hY2dm))), ?_,
    ?_⟩
  · have h := srootE_isBigO_sqrt_abs hB1 hY1O
    rw [mul_one] at h
    refine (h.const_mul (c := 2) (by norm_num)).mono_scale ?_
    have := srootE_two_sqrt_le hAn0 hy1 h4An
    calc 2 * Real.sqrt (An * C * (s⁻¹ * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
            Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ^ 2)
        ≤ C * (s⁻¹ * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ * Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) := this
      _ = C * s⁻¹ * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ * Real.log (m : ℝ) ^ ((1 : ℝ) / 2) := by ring
  · have hn' := hY2nO.mono_scale (mul_le_mul_of_nonneg_right (le_max_left An Ad)
      (Real.rpow_nonneg (Nat.cast_nonneg m) _))
    have hd' := hY2dO.mono_scale (mul_le_mul_of_nonneg_right (le_max_right An Ad)
      (Real.rpow_nonneg (Nat.cast_nonneg m) _))
    have h := srootE_isBigO_sqrt_abs_add hB2 hn' hd'
    refine (h.const_mul (c := 2) (by norm_num)).mono_scale ?_
    rw [hm2000, Real.sqrt_mul (by linarith only [hA1]), Real.sqrt_sq hy2]
    have hsA : Real.sqrt A ≤ A := by
      have h1 : 1 ≤ Real.sqrt A := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt hA1
      have h2 := Real.mul_self_sqrt (le_trans zero_le_one hA1)
      nlinarith only [h1, h2]
    have := mul_le_mul_of_nonneg_right hsA hy2
    have hA0 : 0 ≤ A * (m : ℝ) ^ (-(1000 : ℝ)) := mul_nonneg (by linarith only [hA1]) hy2
    rw [hCdef]
    nlinarith only [this, hA0]
  · filter_upwards [hNae, hDae, hLae] with ω hN hD hL
    have env : ∀ L : ℕ,
        (m : ℝ) - C * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
        Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
            Homogenization.MultiscaleExponent.infinity
            (Homogenization.MultiscaleExponent.finite (2 : ℝ))
            (srootE_field nu ω L m n k) ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) ≤
          Real.sqrt (An * C * (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
              Real.log (m : ℝ)) ^ 2) +
            Real.sqrt |Y1 ω| + Real.sqrt (|Y2n ω| + |Y2d ω|) := by
      intro L hLr
      rw [srootE_homErr_eq]
      have hsplit := srootE_tsum_le_split
        (fun l => srootE_term_nonneg hs0.le (srootE_field nu ω L m n k)
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) n l) (⌈C0 * s⁻¹ * Real.log (m : ℝ)⌉₊ + 1)
      have hn := hN L hLr
      have hd := hD L hLr
      have a1 := le_abs_self (Y1 ω)
      have a2 := le_abs_self (Y2n ω)
      have a3 := le_abs_self (Y2d ω)
      have hT : ∑' l : ℕ, srootE_term s (srootE_field nu ω L m n k)
            ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) n l ≤
          An * C * (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
              Real.log (m : ℝ)) ^ 2 + |Y1 ω| + (|Y2n ω| + |Y2d ω|) := by
        linarith only [hsplit, hn, hd, a1, a2, a3]
      refine le_trans (Real.sqrt_le_sqrt hT) (srootE_sqrt_add3_le ?_ (abs_nonneg _)
        (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      have : 0 ≤ C := by linarith only [hA1]
      positivity
    intro L hLr
    have h1 := env L hLr
    have hm0 : (m : ℝ) - C * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
      have : 0 ≤ C * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) := by
        have : 0 ≤ C := by linarith only [hA1]
        have := inv_nonneg.2 hs0.le
        positivity
      linarith only [this]
    have h2 := hL _ ⟨m, fun L' hL' => env L' (le_trans hm0 (by exact_mod_cast hL'))⟩
    have h3 := srootE_two_sqrt_le hAn0 hy h4An
    have key : Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
          Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite (2 : ℝ))
          (srootE_field nu ω L m n k) ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) +
        Homogenization.HomogenizationErrorOnCube (Homogenization.originCube d (n : ℤ)) s
          Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite (2 : ℝ))
          (srootE_limField nu ω m n k) ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d)) ≤
        C * s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ * Real.log (m : ℝ) +
          2 * Real.sqrt |Y1 ω| + 2 * Real.sqrt (|Y2n ω| + |Y2d ω|) := by
      have hCy : C * (s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Real.log (m : ℝ)) =
          C * s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) * (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ * Real.log (m : ℝ) := by ring
      linarith only [h1, h2, h3, hCy]
    exact key

end

end SuperdiffusionCLT.Section4.MinimalScales
