/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks

/-!
# Package E1: the scalar algebraic comparison of the homogenized block matrix across scales

This file proves `e.algebraic.add.error.again` of [AK], which is also what
`l.variance` (whose `e.algebraic.add.error` conclusion is reused) needs.

## The source displays

Step 1 of Lemma `l.variance` of [AK] proves, for
`k ≤ n ≤ m` under a smallness hypothesis `e.smallness.ass` (`Θ̃_m - 1 ≤ (80d)⁻¹`),

`|bfAhom^{-1/2}(cus_m) bfAhom(cus_k) bfAhom^{-1/2}(cus_m) - I_{2d}| ≤ 4d(Θ̂_k - Θ̂_m)`
(`e.algebraic.add.error`).

Section 6 (`e.algebraic.add.error.again`) repeats
Step 1 "in our setting" (isotropic, Euclidean cubes, `Θ̂_m := Θ_m`) to get, for every
`k, n ∈ ℕ` with `m₁ + 2m₀ ≤ k ≤ n`,

`|bfAhom^{-1/2}(cu_n) bfAhom(cu_k) bfAhom^{-1/2}(cu_n) - I_{2d}| ≤ 4d(Θ̂_k - Θ̂_n) ≤ 1/40`.

## The scalar reduction and the refutation of the `4d` factor

Under (P4) (isotropy), package A2 (`AKHC61.Carrier.ScalarBlocks`,
`AKHC61.Carrier.ScalarBlocksB`) already gives `bfAhom_L(cu_n) = diag(σ̄_n I_d,
σ̄*⁻¹_n I_d)` and `Θ̂_n = Θ_n = thetaCutoff nu L P n = σ̄_n · σ̄*⁻¹_n`. Substituting the
block-diagonal form into the display above, the conjugated matrix is itself block
diagonal with entries `σ̄_k/σ̄_n` and `σ̄*⁻¹_k/σ̄*⁻¹_n`, so its operator norm minus
`I_{2d}` is exactly `max(σ̄_k/σ̄_n - 1, σ̄*⁻¹_k/σ̄*⁻¹_n - 1)` (both nonnegative, since
`k ≤ n` and both scalar sequences are antitone). The plan's row 49 is right that no
factor `4d` (nor any dimensional constant at all) is needed here: `σ̄_k/σ̄_n - 1 ≤
Θ_k - Θ_n` and the `σ̄*⁻¹` twin hold unconditionally for `k ≤ n`, using only that
`Θ_n ≥ 1` (`akhc_one_le_thetaCutoff_of_P2`, node 60) — **not** the `(80d)⁻¹`
smallness hypothesis `e.smallness.ass`, and **not** the window `m₁ + 2m₀ ≤ k`. This
is a genuine strengthening of both `e.algebraic.add.error` (node 55: it needs no
smallness hypothesis in the isotropic case) and `e.algebraic.add.error.again` (node
49: it needs no window). The trailing `≤ 1/40` of the Section 6 display is a
downstream numeric fact about `Θ_k - Θ_n` at that window (supplied by other steps of
the Step 3 induction, not reproved here); the comparisons below discharge it by transitivity
once that fact is supplied as a hypothesis.

**The plan's parenthetical hint on the real core lemma is imprecise.** It suggests
"positive reals `a ≥ a′`, `b ≥ b′` with `ab ≥ 1`" as the hypothesis. The refutation
`example` below shows `1 ≤ a * b` (the product of the *larger* pair, i.e. `Θ_k ≥ 1`)
is **not** sufficient: `a := 10, a' := 0.5, b := b' := 0.5` satisfies `a' ≤ a`,
`b' ≤ b`, `1 ≤ a * b = 5`, yet `a / a' - 1 = 19 > 4.75 = a * b - a' * b'`. What is
actually needed, and what the application below actually has, is `1 ≤ a' * b'` — the
product of the *smaller* pair (`Θ_n ≥ 1`, the reference/denominator scale) — which
here holds unconditionally at every scale, not just asymptotically.

## Main results

* `akhc_real_ratio_sub_one_le`, `akhc_real_ratio_sub_one_le'`: the purely
  real-number core (no probability, no shell law), reusable elsewhere.
* `akhc_algebraic_comparison_sigmaBar_of_P2`,
  `akhc_algebraic_comparison_sigmaBarStarInv_of_P2`: node 49 (and node 55's plain
  `e.algebraic.add.error`), the two scalar comparisons, `4d`-free and
  smallness-free.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier

noncomputable section

/-! ## Part 1: the real-number core -/

section RealCore

/-- **Purely real-number core, `σ̄` (first-slot) direction.** For positive `a'`
with `a' ≤ a`, `b' ≤ b`, and `1 ≤ a' * b'` (the product at the *reference* index
`a', b'`, not at `a, b`), `a / a' - 1 ≤ a * b - a' * b'`. No sign hypothesis on
`b'` is needed: `1 ≤ a' * b'` together with `0 < a'` already forces `0 < b'`. -/
theorem akhc_real_ratio_sub_one_le {a a' b b' : ℝ} (ha' : 0 < a')
    (haa' : a' ≤ a) (hbb' : b' ≤ b) (hab' : 1 ≤ a' * b') :
    a / a' - 1 ≤ a * b - a' * b' := by
  rw [div_sub_one ha'.ne', div_le_iff₀ ha']
  have hx : (0 : ℝ) ≤ a - a' := by linarith only [haa']
  have hy : (0 : ℝ) ≤ b - b' := by linarith only [hbb']
  have h1 : (a - a') * 1 ≤ (a - a') * (a' * b') := mul_le_mul_of_nonneg_left hab' hx
  nlinarith only [h1, mul_nonneg (mul_nonneg ha'.le ha'.le) hy,
    mul_nonneg (mul_nonneg ha'.le hx) hy]

/-- **Purely real-number core, `σ̄*⁻¹` (second-slot) twin.** Symmetric to
`akhc_real_ratio_sub_one_le`, needing `0 < b'` instead of `0 < a'`. -/
theorem akhc_real_ratio_sub_one_le' {a a' b b' : ℝ} (hb' : 0 < b')
    (haa' : a' ≤ a) (hbb' : b' ≤ b) (hab' : 1 ≤ a' * b') :
    b / b' - 1 ≤ a * b - a' * b' := by
  rw [div_sub_one hb'.ne', div_le_iff₀ hb']
  have hx : (0 : ℝ) ≤ a - a' := by linarith only [haa']
  have hy : (0 : ℝ) ≤ b - b' := by linarith only [hbb']
  have h1 : (b - b') * 1 ≤ (b - b') * (a' * b') := mul_le_mul_of_nonneg_left hab' hy
  nlinarith only [h1, mul_nonneg (mul_nonneg hb'.le hb'.le) hx,
    mul_nonneg (mul_nonneg hb'.le hy) hx]

/-- **Refutation of the plan's parenthetical hint.** `1 ≤ a * b` (the product at
the *larger* pair) does not suffice for `akhc_real_ratio_sub_one_le`'s
conclusion; only `1 ≤ a' * b'` (the product at the reference pair) does. -/
example : ¬ (∀ a a' b b' : ℝ, 0 < a' → 0 < b' → a' ≤ a → b' ≤ b → 1 ≤ a * b →
    a / a' - 1 ≤ a * b - a' * b') := by
  intro h
  have := h 10 0.5 0.5 0.5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this

end RealCore

/-! ## Part 2: the scale-indexed scalar comparisons (`e.algebraic.add.error.again`)

The `(P2')` clause is copied verbatim from
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`. No `(P3')`
clause and no `ShellLawJ3` are used. -/

section ScaleComparison

variable {d : ℕ} [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
  (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
  hGrowth hP2

/-- **Node 49 (`e.algebraic.add.error.again`) and node 55's `e.algebraic.add.error`,
`σ̄` direction, `4d`-free.** No smallness hypothesis and no window `m₁ + 2m₀ ≤ k`:
this holds for every `k ≤ n`. -/
theorem akhc_algebraic_comparison_sigmaBar_of_P2 {k n : ℕ} (hkn : k ≤ n) :
    sigmaBarSeq nu L P k / sigmaBarSeq nu L P n - 1 ≤
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k -
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n := by
  have hSigmaAnti := akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn
  have hStarAnti := akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn
  have hSigmaPosN := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 n
  have hThetaN := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 n
  simp only [SuperdiffusionCLT.Frozen.Section4.thetaCutoff] at hThetaN ⊢
  exact akhc_real_ratio_sub_one_le hSigmaPosN hSigmaAnti hStarAnti hThetaN

/-- **Node 49 and node 55, `σ̄*⁻¹` twin, `4d`-free.** -/
theorem akhc_algebraic_comparison_sigmaBarStarInv_of_P2 {k n : ℕ} (hkn : k ≤ n) :
    sigmaBarStarInvSeq nu L P k / sigmaBarStarInvSeq nu L P n - 1 ≤
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k -
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n := by
  have hSigmaAnti := akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn
  have hStarAnti := akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn
  have hStarPosN := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 n
  have hThetaN := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 n
  simp only [SuperdiffusionCLT.Frozen.Section4.thetaCutoff] at hThetaN ⊢
  exact akhc_real_ratio_sub_one_le' hStarPosN hSigmaAnti hStarAnti hThetaN

end ScaleComparison

/-! ## Part 3: the `... ≤ t` chain (specializes to the source's `≤ 1/40`)

The Section 6 display chains `4d(Θ̂_k - Θ̂_n) ≤ 1/40`; the second inequality is a
numeric fact about the induction's window, established elsewhere (not by this
package). These corollaries discharge it, generically in the bound `t`, by
transitivity with Part 2. -/

section ThetaBounded

variable {d : ℕ} [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
  (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
  hGrowth hP2

end ThetaBounded

end

end SuperdiffusionCLT.AKHC61.Step3
