/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Main

/-!
# `l.RHS.term2` at the glued fields, and the constant-first restatement

The paper states `e.RHS.term2` in the form it always uses:

> There exists `C(d) < ∞` such that, for the scales selected in
> `e.scale.selection`, `|E[...]| ≤ C nu^{-3} (L')^2 3^{-(ℓ-n)/2}`.

The constant comes **first**: one `C(d)`, then every admissible choice of
scales, shell law, unit vector and response field.  The per-instance form
of `l.RHS.term2` puts `∃ C, 1 ≤ C ∧ …` inside
all of the section data, where the statement is degenerate: for one fixed
choice of the data the left side is a fixed real and the right coefficient
`nu^{-3}(L')^2 3^{-(ℓ-n)/2}` is a fixed positive real, so a large enough `C`
always exists.  The same remark applies to each of the three displayed inputs.

This module repairs the shape.  `termTwoConst` names the constant that the
assembly of `l.RHS.term2` produces, `C = 2 C₁ C₂ + 2 Cpoin C₁ C₃ + 1`, and
`l_RHS_term2_constFirst` states `e.RHS.term2` with `C` quantified before the
section data, from the three displays carried at the *fixed* constants
`C₁, C₂, C₃` and the per-cube Poincaré constant `Cpoin`.

`l_RHS_term2_constFirst` is **not** a corollary of the per-instance form of `l.RHS.term2`: the
conclusion `∃ C, 1 ≤ C ∧ …` releases the constant it constructed, and no
uniform constant can be recovered from a family of per-instance existentials.
The proof below therefore re-runs the assembly of the proof of `l.RHS.term2` with
`termTwoConst C₁ C₂ C₃ Cpoin` supplied as the witness before the data is
introduced; every step is the one of `RHSTerm2Main`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The constant of `e.RHS.term2` -/

/-- The constant that the assembly of `l.RHS.term2` produces from the constants
of its three displayed inputs and the per-cube Poincaré constant:
`C = 2 C₁ C₂ + 2 Cpoin C₁ C₃ + 1`.  The two `2 C₁ C₂` summands are the
localization-error and mean-defect terms, the summand
`2 Cpoin C₁ C₃` is the decoupled proxy term, and the `+ 1`
makes the constant at least one. -/
def termTwoConst (C₁ C₂ C₃ Cpoin : ℝ) : ℝ :=
  2 * C₁ * C₂ + 2 * Cpoin * C₁ * C₃ + 1

theorem one_le_termTwoConst {C₁ C₂ C₃ Cpoin : ℝ} (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (hC₃ : 1 ≤ C₃) (hCpoin : 0 ≤ Cpoin) : 1 ≤ termTwoConst C₁ C₂ C₃ Cpoin := by
  have hC10 : (0 : ℝ) ≤ C₁ := le_trans zero_le_one hC₁
  have hC20 : (0 : ℝ) ≤ C₂ := le_trans zero_le_one hC₂
  have hC30 : (0 : ℝ) ≤ C₃ := le_trans zero_le_one hC₃
  have h1 : (0 : ℝ) ≤ 2 * C₁ * C₂ := mul_nonneg (mul_nonneg (by norm_num) hC10) hC20
  have h2 : (0 : ℝ) ≤ 2 * Cpoin * C₁ * C₃ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpoin) hC10) hC30
  show (1 : ℝ) ≤ 2 * C₁ * C₂ + 2 * Cpoin * C₁ * C₃ + 1
  linarith only [h1, h2]

/-! ## `e.RHS.term2` with the constant quantified first -/

/-- **`l.RHS.term2` in the paper's own quantifier order**: given the constants
`C₁`, `C₂`, `C₃` of the three displayed inputs `e.RHS.term2.R.bounds`,
`e.RHS.term2.proxy.error`, `e.RHS.term2.proxy.energy` and the constant `Cpoin`
of the per-cube Poincaré inequality, there is one `C` — namely
`termTwoConst C₁ C₂ C₃ Cpoin` — that bounds

`|E[ avsum_{z ∈ 3^n ℤ^d ∩ cu_m} ⨍_{z+cu_n} ∇w · (k_{L'} − k_ℓ)(∇u_{n,z} − p) ]|`

by `C nu^{-3}(L')^2 3^{-(ℓ-n)/2}` **for every** admissible choice of the shell
law, the scales, the unit vector, the response field and the three glued
fields.

The binders after `C` are those of the per-instance form of `l.RHS.term2`, with the three displays
carried at the fixed constants instead of existentially; the conclusion is the
one of that form.  See the module docstring for why this is not a corollary
of it. -/
theorem l_RHS_term2_constFirst (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ C₂ C₃ Cpoin : ℝ) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hC₃ : 1 ≤ C₃)
    (hCpoin : 0 ≤ Cpoin) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (p : Vec d), p = testVector nu S.LPrime P S.n e →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) →
      ∀ (uNGlued uTildeGlued : ShellSeq d → Vec d → Vec d) (pTilde : Vec d)
        (DR : ShellSeq d → Fin d → Vec d → Vec d),
        (∀ omega : ShellSeq d, ∀ i : Fin d,
          HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                  (coefficientCutoff nu omega S.ell).toCoeffField x)
                ((w omega).toH1Function.grad x)) i) (DR omega i)) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                (originCube d (S.m : ℤ)) 2
                (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                  (coefficientCutoff nu omega S.ell).toCoeffField x)
                  ((w omega).toH1Function.grad x)) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
          (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
            (∫⁻ omega : ShellSeq d,
                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                    (originCube d (S.m : ℤ)) 2
                    (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p)) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (S.m : ℤ)) 2
                  (fun x => uNGlued omega x - uTildeGlued omega x) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
          Real.sqrt (vecNormSq (pTilde - p)) ≤
          C₂ * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
            (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (S.m : ℤ)) 2
                  (fun x => uTildeGlued omega x - pTilde) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          C₃ * nu ^ (-(1 : ℝ)) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
      ∀ (Rfield : ShellSeq d → Vec d → Vec d),
        (∀ (omega : ShellSeq d) (y : Vec d), Rfield omega y =
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y)) →
      ∀ (DRmat : ShellSeq d → Vec d → HilbertMat d),
        (∀ (omega : ShellSeq d) (x : Vec d), DRmat omega x =
          HilbertMat.ofMat (fun i j => DR omega i x j)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (Rfield omega)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (uNGlued omega)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (uTildeGlued omega)) →
        (∀ omega : ShellSeq d,
          MemLp (DRmat omega) 2
            (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega) ^ (2 : ℕ)
            ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uNGlued omega x - uTildeGlued omega x) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uTildeGlued omega x - pTilde) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uNGlued omega x - uTildeGlued omega x)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uTildeGlued omega x - pTilde)) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (uNGlued omega y - uTildeGlued omega y))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (uTildeGlued omega y - pTilde))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (pTilde - p))) P.toMeasure) →
        (∀ (omega : ShellSeq d), ∀ z ∈ largeCubeSubcubes d S.n S.m,
          vecCubeLpENorm z 2
              (fun x => Rfield omega x -
                volumeAverageVec (openCubeSet z) (Rfield omega)) ≤
            ENNReal.ofReal (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 (DRmat omega)) →
        (∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot (Rfield omega y)
                (uTildeGlued omega y - pTilde)) ∂P.toMeasure =
          ∫ omega : ShellSeq d,
            (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ largeCubeSubcubes d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot
                    (Rfield omega y - volumeAverageVec (openCubeSet z) (Rfield omega))
                    (uTildeGlued omega y -
                      volumeAverageVec (openCubeSet z) (uTildeGlued omega))))
              ∂P.toMeasure) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (uNGlued omega y - p))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
  refine ⟨termTwoConst C₁ C₂ C₃ Cpoin,
    one_le_termTwoConst hC₁ hC₂ hC₃ hCpoin, ?_⟩
  classical
  have := hd
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
    uNGlued uTildeGlued pTilde DR hDR hRb hPe hPen Rfield hRfield DRmat hDRmat
    hRL2 hUL2 hUtL2 hDRL2 hfinR hfinDR hfinDiff hfinProx hmR hmDR hmDiff hmProx
    hIntDiff hIntProxy hIntMean hPoincare hDecouple
  rw [show termTwoConst C₁ C₂ C₃ Cpoin =
    2 * C₁ * C₂ + 2 * Cpoin * C₁ * C₃ + 1 from rfl]
  have := hJ1V2; have := hw; have := hDR
  have hellLT : S.ell < S.LPrime :=
    lt_trans (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m) hSorder.m_lt_LPrime
  have hRfun : ∀ omega : ShellSeq d,
      (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
          (coefficientCutoff nu omega S.ell).toCoeffField x)
          ((w omega).toH1Function.grad x)) = Rfield omega :=
    fun omega => funext fun y => (hRfield omega y).symm
  have hDRfun : ∀ omega : ShellSeq d,
      (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) = DRmat omega :=
    fun omega => funext fun x => (hDRmat omega x).symm
  simp only [hRfun, hDRfun] at hRb
  have hnegAvg : ∀ (U : Set (Vec d)) (g : Vec d → ℝ),
      volumeAverage U (fun y => -g y) = -volumeAverage U g := by
    intro U g
    simp only [volumeAverage, integral_neg, mul_neg]
  have hpt : ∀ omega : ShellSeq d,
      (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d S.n S.m,
          volumeAverage (openCubeSet z)
            (fun y => vecDot ((w omega).toH1Function.grad y)
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                (coefficientCutoff nu omega S.ell).toCoeffField y)
                (uNGlued omega y - p)))) =
      -(volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (uNGlued omega y - uTildeGlued omega y)) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (uTildeGlued omega y - pTilde)) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (pTilde - p))) := by
    intro omega
    have hinner : ∀ y : Vec d,
        vecDot ((w omega).toH1Function.grad y)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
              (uNGlued omega y - p)) =
          -vecDot (Rfield omega y) (uNGlued omega y - p) := by
      intro y
      rw [vecDot_coefficientCutoff_sub_swap nu omega hellLT y _ _, hRfield omega y]
    have hzsum : ∀ z : TriadicCube d,
        volumeAverage (openCubeSet z)
            (fun y => vecDot ((w omega).toH1Function.grad y)
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                (coefficientCutoff nu omega S.ell).toCoeffField y)
                (uNGlued omega y - p))) =
          -volumeAverage (openCubeSet z)
            (fun y => vecDot (Rfield omega y) (uNGlued omega y - p)) := fun z =>
      (congrArg (volumeAverage (openCubeSet z)) (funext hinner)).trans (hnegAvg _ _)
    rw [Finset.sum_congr rfl (fun z (_ : z ∈ largeCubeSubcubes d S.n S.m) => hzsum z),
      Finset.sum_neg_distrib, mul_neg,
      avsum_split (n := S.n) (pT := pTilde) (pv := p) (hRL2 omega) (hUL2 omega) (hUtL2 omega)]
  have hval : ∫ omega : ShellSeq d,
        (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ z ∈ largeCubeSubcubes d S.n S.m,
            volumeAverage (openCubeSet z)
              (fun y => vecDot ((w omega).toH1Function.grad y)
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                  (coefficientCutoff nu omega S.ell).toCoeffField y)
                  (uNGlued omega y - p)))) ∂P.toMeasure =
      -((∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (uNGlued omega y - uTildeGlued omega y)) ∂P.toMeasure +
          ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (uTildeGlued omega y - pTilde)) ∂P.toMeasure) +
        ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot (Rfield omega y) (pTilde - p)) ∂P.toMeasure) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt), integral_neg,
      MeasureTheory.integral_add
        (f := fun omega : ShellSeq d => volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (uNGlued omega y - uTildeGlued omega y)) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (uTildeGlued omega y - pTilde)))
        (g := fun omega : ShellSeq d => volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (pTilde - p)))
        (hIntDiff.add hIntProxy) hIntMean,
      MeasureTheory.integral_add
        (f := fun omega : ShellSeq d => volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (uNGlued omega y - uTildeGlued omega y)))
        (g := fun omega : ShellSeq d => volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y) (uTildeGlued omega y - pTilde)))
        hIntDiff hIntProxy]
  -- the localization-error term
  have hb1 : |∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => vecDot (Rfield omega y)
          (uNGlued omega y - uTildeGlued omega y)) ∂P.toMeasure| ≤
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega) ^ (2 : ℕ)
            ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) *
        (∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uNGlued omega x - uTildeGlued omega x) ^ (2 : ℕ)
              ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) := by
    refine abs_integral_le_of_bound hmR hmDiff (fun omega => ?_) hfinR hfinDiff le_rfl le_rfl
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    exact ofReal_abs_volumeAverage_vecDot_le (hRL2 omega) ((hUL2 omega).sub (hUtL2 omega))
  -- the mean-defect term
  have hconstInt : (∫⁻ _omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun _ : Vec d => pTilde - p) ^ (2 : ℕ)
        ∂P.toMeasure) = ENNReal.ofReal (vecNormSq (pTilde - p)) := by
    rw [lintegral_const, measure_univ, mul_one,
      vecCubeLpENorm_const_sq (originCube d (S.m : ℤ)) (pTilde - p)]
  have hb3 : |∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => vecDot (Rfield omega y) (pTilde - p)) ∂P.toMeasure| ≤
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega) ^ (2 : ℕ)
            ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) * Real.sqrt (vecNormSq (pTilde - p)) := by
    refine abs_integral_le_of_bound (B := fun _omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (fun _ : Vec d => pTilde - p))
      hmR aemeasurable_const (fun omega => ?_) hfinR ?_ le_rfl ?_
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    · exact ofReal_abs_volumeAverage_vecDot_le (hRL2 omega) (memVectorL2_const (pTilde - p))
    · rw [hconstInt]
      exact ENNReal.ofReal_ne_top
    · rw [hconstInt, ENNReal.toReal_ofReal (vecNormSq_nonneg _), Real.sqrt_eq_rpow]
  -- the decoupled and centred proxy term
  have hKnn : 0 ≤ Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ) :=
    mul_nonneg hCpoin (Real.rpow_nonneg (by norm_num) _)
  have hDRne : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
        (DRmat omega) ≠ ⊤ := fun omega => cubeLpENorm_ne_top_of_memLp (hDRL2 omega)
  have hProxne : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => uTildeGlued omega x - pTilde) ≠ ⊤ := fun omega =>
    vecCubeLpENorm_ne_top (memVectorL2_sub_const pTilde (hUtL2 omega))
  have hAsq : (∫⁻ omega : ShellSeq d,
        (ENNReal.ofReal (2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega)) ^ (2 : ℕ) ∂P.toMeasure) =
      ENNReal.ofReal (2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ))) ^ (2 : ℕ) *
        ∫⁻ omega : ShellSeq d,
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega) ^ (2 : ℕ) ∂P.toMeasure := by
    rw [← lintegral_const_mul'' _ (hmDR.pow_const 2)]
    exact lintegral_congr fun omega => (mul_pow _ _ 2)
  have hb2 : |∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => vecDot (Rfield omega y)
          (uTildeGlued omega y - pTilde)) ∂P.toMeasure| ≤
      (2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) *
        (∫⁻ omega : ShellSeq d,
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega) ^ (2 : ℕ) ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2)) *
      (∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => uTildeGlued omega x - pTilde) ^ (2 : ℕ) ∂P.toMeasure).toReal ^
          ((1 : ℝ) / 2) := by
    rw [hDecouple]
    refine abs_integral_le_of_bound
      (A := fun omega : ShellSeq d =>
        ENNReal.ofReal (2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega))
      (B := fun omega : ShellSeq d => vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => uTildeGlued omega x - pTilde))
      (hmDR.const_mul _) hmProx (fun omega => ?_) ?_ hfinProx ?_ le_rfl ?_
    · have hcb := centred_avsum_bound (n := S.n) (pT := pTilde) hKnn (hRL2 omega)
        (hUtL2 omega) (hDRL2 omega) (hPoincare omega)
      refine le_trans (ENNReal.ofReal_le_ofReal hcb) (le_of_eq ?_)
      show ENNReal.ofReal (2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) *
          (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega)).toReal *
          (vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uTildeGlued omega x - pTilde)).toReal) =
        ENNReal.ofReal (2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ))) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
              (DRmat omega) *
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uTildeGlued omega x - pTilde)
      rw [ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg (by norm_num) hKnn) ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hKnn),
        ENNReal.ofReal_toReal (hDRne omega), ENNReal.ofReal_toReal (hProxne omega)]
    · rw [hAsq]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hfinDR
    · rw [hAsq, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hKnn), ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (mul_nonneg (by norm_num) hKnn)]
    · exact mul_nonneg (mul_nonneg (by norm_num) hKnn)
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  -- the closing arithmetic of the proof
  set IR : ℝ := (∫⁻ omega : ShellSeq d,
    vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega) ^ (2 : ℕ)
      ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) with hIRdef
  set IDR : ℝ := (∫⁻ omega : ShellSeq d,
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
      (DRmat omega) ^ (2 : ℕ) ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) with hIDRdef
  set IDiff : ℝ := (∫⁻ omega : ShellSeq d,
    vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => uNGlued omega x - uTildeGlued omega x) ^ (2 : ℕ)
        ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) with hIDiffdef
  set IProx : ℝ := (∫⁻ omega : ShellSeq d,
    vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => uTildeGlued omega x - pTilde) ^ (2 : ℕ)
        ∂P.toMeasure).toReal ^ ((1 : ℝ) / 2) with hIProxdef
  have hIR0 : 0 ≤ IR := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hIDR0 : 0 ≤ IDR := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hIDiff0 : 0 ≤ IDiff := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hIProx0 : 0 ≤ IProx := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hPpt0 : 0 ≤ Real.sqrt (vecNormSq (pTilde - p)) := Real.sqrt_nonneg _
  have hC10 : (0 : ℝ) ≤ C₁ := le_trans zero_le_one hC₁
  have hC20 : (0 : ℝ) ≤ C₂ := le_trans zero_le_one hC₂
  have hC30 : (0 : ℝ) ≤ C₃ := le_trans zero_le_one hC₃
  have hsgpos : 0 < sigmaBarStarInvSqrt nu S.LPrime P S.n :=
    sigmaBarStarInvSqrt_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hsg0 : (0 : ℝ) ≤ (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ :=
    le_of_lt (inv_pos.2 hsgpos)
  have hnp : Real.sqrt (vecNormSq p) = sigmaBarStarInvSqrt nu S.LPrime P S.n := by
    rw [hp, vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    rfl
  have hdual : Real.sqrt (vecNormSq p) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ = 1 := by
    rw [hnp, mul_inv_cancel₀ hsgpos.ne']
  have hnp0 : 0 ≤ Real.sqrt (vecNormSq p) := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL1 : (1 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := by
    have : 1 ≤ S.LPrime := by
      have := hSorder.m_lt_LPrime
      omega
    exact_mod_cast this
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  have ha0 : (0 : ℝ) ≤ ((S.ell - S.n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3split : (3 : ℝ) ^ ((S.n : ℕ) : ℝ) =
      (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) * (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [Nat.cast_sub hnl]
    ring
  -- the three displayed inputs, split
  have hIRle : IR ≤ C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p) := by
    have h3l : 0 ≤ (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IDR :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hIDR0
    linarith only [hRb, h3l]
  have hIDRle : (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IDR ≤
      C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p) := by
    linarith only [hRb, hIR0]
  have hIDiffle : IDiff ≤ C₂ * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
      (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ := by
    linarith only [hPe, hPpt0]
  have hPptle : Real.sqrt (vecNormSq (pTilde - p)) ≤ C₂ * nu ^ (-((3 : ℝ) / 2)) *
      ((S.LPrime : ℕ) : ℝ) * (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
      (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ := by
    linarith only [hPe, hIDiff0]
  have hB10 : 0 ≤ C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p) :=
    mul_nonneg (mul_nonneg hC10 hL0) hnp0
  have hB20 : 0 ≤ C₂ * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
      (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC20 (Real.rpow_nonneg hnu.le _)) hL0)
      (Real.rpow_nonneg (by norm_num) _)) hsg0
  have hB30 : 0 ≤ C₃ * nu ^ (-(1 : ℝ)) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ :=
    mul_nonneg (mul_nonneg hC30 (Real.rpow_nonneg hnu.le _)) hsg0
  -- the three products
  have hprodA : IR * IDiff ≤ C₁ * C₂ * nu ^ (-((3 : ℝ) / 2)) *
      (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) * (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
    refine le_trans (mul_le_mul hIRle hIDiffle hIDiff0 hB10) (le_of_eq ?_)
    have hre : (C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p)) *
        (C₂ * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
          (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) =
        (C₁ * C₂ * nu ^ (-((3 : ℝ) / 2)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2))) *
          (Real.sqrt (vecNormSq p) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) := by ring
    rw [hre, hdual, mul_one]
  have hprodC : IR * Real.sqrt (vecNormSq (pTilde - p)) ≤ C₁ * C₂ * nu ^ (-((3 : ℝ) / 2)) *
      (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) * (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
    refine le_trans (mul_le_mul hIRle hPptle hPpt0 hB10) (le_of_eq ?_)
    have hre : (C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p)) *
        (C₂ * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
          (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) =
        (C₁ * C₂ * nu ^ (-((3 : ℝ) / 2)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2))) *
          (Real.sqrt (vecNormSq p) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) := by ring
    rw [hre, hdual, mul_one]
  have hmid : 2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) * IDR ≤
      2 * Cpoin * (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) *
        (C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p)) := by
    have hrw : 2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) * IDR =
        (2 * Cpoin * (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
          ((3 : ℝ) ^ ((S.ell : ℕ) : ℝ) * IDR) := by
      rw [h3split]
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hIDRle
      (mul_nonneg (mul_nonneg (by norm_num) hCpoin) (Real.rpow_nonneg (by norm_num) _))
  have hprodB : (2 * (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) * IDR) * IProx ≤
      2 * Cpoin * C₁ * C₃ * nu ^ (-(1 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) := by
    have hmid0 : 0 ≤ 2 * Cpoin * (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) *
        (C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpoin)
        (Real.rpow_nonneg (by norm_num) _)) hB10
    refine le_trans (mul_le_mul hmid hPen hIProx0 hmid0) (le_of_eq ?_)
    have hre : (2 * Cpoin * (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) *
        (C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p))) *
        (C₃ * nu ^ (-(1 : ℝ)) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) =
        (2 * Cpoin * C₁ * C₃ * nu ^ (-(1 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) *
          (Real.sqrt (vecNormSq p) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) := by ring
    rw [hre, hdual, mul_one]
  -- assembling
  rw [hval, abs_neg]
  have hnu30 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) := Real.rpow_nonneg hnu.le _
  have hLsq0 : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := pow_nonneg hL0 2
  have h3half0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) :=
    Real.rpow_nonneg (by norm_num) _
  have h3a0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hX0 : (0 : ℝ) ≤ nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
      (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) :=
    mul_nonneg (mul_nonneg hnu30 hLsq0) h3half0
  have hnu32 : nu ^ (-((3 : ℝ) / 2)) ≤ nu ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hnu1e : nu ^ (-(1 : ℝ)) ≤ nu ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have h3le : (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) ≤
      (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [ha0])
  have hLle : ((S.LPrime : ℕ) : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hL1 hL0
    calc ((S.LPrime : ℕ) : ℝ) = ((S.LPrime : ℕ) : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((S.LPrime : ℕ) : ℝ) * ((S.LPrime : ℕ) : ℝ) := h
      _ = ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) := by ring
  have hC1C20 : (0 : ℝ) ≤ C₁ * C₂ := mul_nonneg hC10 hC20
  have hK0 : (0 : ℝ) ≤ 2 * Cpoin * C₁ * C₃ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCpoin) hC10) hC30
  have hA' : C₁ * C₂ * nu ^ (-((3 : ℝ) / 2)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
      (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) ≤
      C₁ * C₂ * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnu32 hC1C20) hLsq0) h3half0
  have hB' : 2 * Cpoin * C₁ * C₃ * nu ^ (-(1 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
      (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) ≤
      2 * Cpoin * C₁ * C₃ * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
    calc 2 * Cpoin * C₁ * C₃ * nu ^ (-(1 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))
        ≤ 2 * Cpoin * C₁ * C₃ * nu ^ (-(3 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnu1e hK0) hL0) h3a0
      _ ≤ 2 * Cpoin * C₁ * C₃ * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLle (mul_nonneg hK0 hnu30)) h3a0
      _ ≤ 2 * Cpoin * C₁ * C₃ * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) :=
          mul_le_mul_of_nonneg_left h3le (mul_nonneg (mul_nonneg hK0 hnu30) hLsq0)
  have hsum : |(∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot (Rfield omega y)
            (uNGlued omega y - uTildeGlued omega y)) ∂P.toMeasure +
        ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun y => vecDot (Rfield omega y)
            (uTildeGlued omega y - pTilde)) ∂P.toMeasure) +
      ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun y => vecDot (Rfield omega y) (pTilde - p)) ∂P.toMeasure| ≤
      (C₁ * C₂ * nu ^ (-((3 : ℝ) / 2)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
        2 * Cpoin * C₁ * C₃ * nu ^ (-(1 : ℝ)) * ((S.LPrime : ℕ) : ℝ) *
          (3 : ℝ) ^ (-(((S.ell - S.n : ℕ) : ℝ)))) +
      C₁ * C₂ * nu ^ (-((3 : ℝ) / 2)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
        (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by
    refine le_trans (abs_add_le _ _)
      (add_le_add (le_trans (abs_add_le _ _) ?_) (le_trans hb3 hprodC))
    exact add_le_add (le_trans hb1 hprodA) (le_trans hb2 hprodB)
  refine le_trans hsum ?_
  linarith only [hA', hB', hX0]

/-! ## `l.RHS.term2` at the glued fields -/

end

end SuperdiffusionCLT.Section3.Terms
