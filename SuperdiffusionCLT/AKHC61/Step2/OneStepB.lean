/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.OneStep
public import SuperdiffusionCLT.AKHC61.Step2.LaunchB
public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeH

/-!
# Package D3, part 2: constants of the one-step bound (nodes 36-38, 40)

Continues `OneStep.lean` (node 39, the geometric iteration core). The one-step bound
`Θ_{m+N'} ≤ 1 + ¼σΘ_m` is obtained from the already-closed Step 2 weak-norm bound
`akhcPrime_step2_thetaBound` (package C6, `WeakNorms/PrimeH.lean`) by the following
constant bookkeeping, which this file supplies:

* the lower bound `akhcOne_JBconst_ge_four` on C6's dimensional constant `akhcJB_const d`;
* the constant-absorption arithmetic `akhcOne_absorb`, which supplies the source's
  "there exists `δ₀(d) ∈ (0,1)` such that `δ ≤ δ₀` implies ..." **explicitly**,
  as `akhcOneDelta0 d Kw`, with `Kw := akhcPrime_Kst d s' ρ * (cV+5)` (C6's own weak-norm
  constant, made explicit in terms of `K(d,s',ρ)`).

The remaining steps of the one-step bound are monotonicity of `m ↦ Θ_m` (package A2,
`akhc_antitone_thetaCutoff_of_P2`), to pass from `Θ_k` (the pigeon witness scale) down to
`Θ_{m+N'}` since `k ≤ m + N'`, and the variance and smallness hypotheses of C6, which the
version-2 route discharges in `Step2/ElaborateLag.lean`. See `OneStep.lean`'s module docstring for
the iteration count.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

/-! ## A lower bound on the dimensional constant `akhcJB_const d` -/

/-- `akhcJB_const d ≥ 4`, reusing the same `rfl`-unfolding and nonnegativity lemmas as C6's own
`akhcPrime_step2_thetaBound_src` (`WeakNorms/PrimeH.lean`) uses for `akhcJB_const d ≥ 0`, dropping
only the first summand's factor `2^d ≥ 0` down to the trivial `4*(1+2^d) ≥ 4`. -/
theorem akhcOne_JBconst_ge_four (d : ℕ) [NeZero d] : (4 : ℝ) ≤ akhcJB_const d := by
  have hg := quantitativeCubeCutoffGradientConst_nonneg d
  have hlin : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d :=
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
        (Homogenization.cubeBesovScaleWeight_nonneg _ _))
        (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound_nonneg
          (Homogenization.originCube d (0 : ℤ)) (1 / 2 : ℝ)))).trans
    (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
      (Homogenization.originCube d (0 : ℤ)) (r := 1 / 2) (by norm_num) (by norm_num))
  have hprod : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d :=
    (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_nonneg
      (Homogenization.originCube d ((0 : ℕ) : ℤ)) (1 / 2 : ℝ) (1 / 2 : ℝ)).trans
    (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_origin_le_dimensional
      (d := d) 0 (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num))
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
  have h8 : (0 : ℝ) ≤ 8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d := by
    have := mul_nonneg hg h2d
    nlinarith only [this]
  have hK : akhcJB_const d = 4 * (1 + (2 : ℝ) ^ d) +
      8 * quantitativeCubeCutoffGradientConst d * (2 : ℝ) ^ d +
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d +
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d := rfl
  rw [hK]
  nlinarith only [h2d, h8, hlin, hprod]

/-! ## The constant absorption arithmetic (the explicit `δ₀(d)`) -/

/-- **The explicit `δ₀`**, making the statement "there exists `δ₀(d) ∈ (0,1)`" of the paper
concrete in terms of the weak-norm constant `K(d,s',ρ)` (`akhcPrime_Kst`) that C6 already
produces: `δ₀ := (16·C_d·(1+√K_w+K_w))⁻²`, `C_d := akhcJB_const d`. -/
noncomputable def akhcOneDelta0 (d : ℕ) [NeZero d] (Kw : ℝ) : ℝ :=
  ((16 * akhcJB_const d * (1 + Real.sqrt Kw + Kw)) ⁻¹) ^ 2

/-- **The absorption arithmetic.** For `C ≥ 4`, `B ≥ 1`, `0 < σ < 1`, `0 ≤ δ`, `0 ≤ t ≤ δσ²`
and `δ ≤ (16CB)⁻²`, `2CB(σ√δ + t) ≤ ¼σ`. Applied with `C := akhcJB_const d`,
`B := 1+√K_w+K_w`, `t := (3^{2L})⁻¹` (via `hT2small`), this is exactly the constant absorption
`node 40` needs to pass from C6's `Θ_k - 1 ≤ 2C(1+√K_w+K_w)(σ√δ+(3^{ell})⁻¹)Θ_m` to
`Θ_k - 1 ≤ ¼σΘ_m`. -/
theorem akhcOne_absorb {C B sigma delta t : ℝ}
    (hC4 : 4 ≤ C) (hB1 : 1 ≤ B) (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hdelta0 : 0 ≤ delta) (_ht0 : 0 ≤ t) (htsmall : t ≤ delta * sigma ^ 2)
    (hdelta_le : delta ≤ ((16 * C * B) ⁻¹) ^ 2) :
    2 * C * B * (sigma * Real.sqrt delta + t) ≤ 1 / 4 * sigma := by
  have hC0 : (0 : ℝ) ≤ C := by linarith only [hC4]
  have hB0 : (0 : ℝ) ≤ B := by linarith only [hB1]
  have hCB4 : (4 : ℝ) ≤ C * B := by nlinarith only [hC4, hB1, hC0, hB0]
  have hCBpos : (0 : ℝ) < C * B := by linarith only [hCB4]
  have h16CBpos : (0 : ℝ) < 16 * (C * B) := by linarith only [hCBpos]
  set X : ℝ := (16 * (C * B)) ⁻¹ with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hdelta_le' : delta ≤ X ^ 2 := by
    have hrw : (16 * C * B : ℝ) = 16 * (C * B) := by ring
    rw [hXdef, ← hrw]; exact hdelta_le
  have hsdelta : Real.sqrt delta ≤ X := by
    have h1 : Real.sqrt delta ≤ Real.sqrt (X ^ 2) := Real.sqrt_le_sqrt hdelta_le'
    rwa [Real.sqrt_sq hX0] at h1
  have hCBmul : C * B * X = 1 / 16 := by
    rw [hXdef, ← div_eq_mul_inv, div_eq_div_iff h16CBpos.ne' (by norm_num : (16 : ℝ) ≠ 0)]
    ring
  have hbound1 : C * B * Real.sqrt delta ≤ 1 / 16 := by
    calc C * B * Real.sqrt delta ≤ C * B * X := mul_le_mul_of_nonneg_left hsdelta hCBpos.le
      _ = 1 / 16 := hCBmul
  have hX1 : X ≤ 1 := by
    rw [hXdef, inv_eq_one_div, div_le_one h16CBpos]
    linarith only [hCB4]
  have hdXX : delta ≤ X * X := by
    have hsq : X ^ 2 = X * X := sq X
    linarith only [hdelta_le', hsq]
  have hbound2 : C * B * t ≤ 1 / 16 * sigma := by
    have hsig2 : sigma ^ 2 ≤ sigma := by nlinarith only [hsigma0, hsigma1]
    have ht1 : t ≤ delta * sigma := by
      calc t ≤ delta * sigma ^ 2 := htsmall
        _ ≤ delta * sigma := mul_le_mul_of_nonneg_left hsig2 hdelta0
    calc C * B * t ≤ C * B * (delta * sigma) := mul_le_mul_of_nonneg_left ht1 hCBpos.le
      _ = (C * B * delta) * sigma := by ring
      _ ≤ (C * B * (X * X)) * sigma := by
            have hstep : C * B * delta ≤ C * B * (X * X) :=
              mul_le_mul_of_nonneg_left hdXX hCBpos.le
            exact mul_le_mul_of_nonneg_right hstep hsigma0.le
      _ = ((C * B * X) * X) * sigma := by ring
      _ = ((1 / 16) * X) * sigma := by rw [hCBmul]
      _ ≤ ((1 / 16) * 1) * sigma := by
            have hstep2 : (1 / 16 : ℝ) * X ≤ 1 / 16 * 1 :=
              mul_le_mul_of_nonneg_left hX1 (by norm_num)
            exact mul_le_mul_of_nonneg_right hstep2 hsigma0.le
      _ = 1 / 16 * sigma := by ring
  have hscaled : sigma * (C * B * Real.sqrt delta) ≤ sigma * (1 / 16) :=
    mul_le_mul_of_nonneg_left hbound1 hsigma0.le
  nlinarith only [hscaled, hbound2]

/-! ## Node 40: `…step2.one.step.bound.route.elaborate` -/

section RouteElaborate

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hDnn : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowthP2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j → ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
  (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
  (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (homega : ∀ k' : ℕ, 0 < omegaSeq k')
  (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) (hKPsi : 1 ≤ KPsi)
  (hGrowthPsi : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
      (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
      ∃ X : ShellSeq d → ℝ, Measurable X ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
        ∀ (omega : ShellSeq d) (p q : Homogenization.BlockVec d),
          2 *
              (((Homogenization.descendantsAtDepth
                      (Homogenization.originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
                ∑ R ∈ Homogenization.descendantsAtDepth
                    (Homogenization.originCube d (j : ℤ)) (j - n),
                  Homogenization.blockVecDot p
                    (Homogenization.blockMatVecMul
                      (Homogenization.ofFullBlockMat
                        (Homogenization.toFullBlockMat
                            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                              (coefficientCutoff nu omega L).toCoeffField) -
                          Homogenization.toFullBlockMat
                            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ))))))
                      q)) ≤
            X omega *
              (Homogenization.blockVecDot p
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) p) +
                Homogenization.blockVecDot q
                  (Homogenization.blockMatVecMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) q)))

include hnu hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hJ4 hPrefix hJ2
  Psi KPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3

end RouteElaborate

/-! ## Nodes 36-38: the one-step bound for a single `m`
(`x.AK.HC.theorem.6.1#step2.one.step.bound`) -/

section StepBound

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hDnn : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowthP2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j → ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2

end StepBound

/-! ## Node 24: `e.prime.step.one`, the `n`-fold iteration -/

section Iterate

variable {d : ℕ} [NeZero d] {nu : ℝ} (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))

end Iterate

end

end SuperdiffusionCLT.AKHC61.Step2
