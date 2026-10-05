/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB
public import SuperdiffusionCLT.AKHC61.Pigeon.Main
public import SuperdiffusionCLT.AKHC61.Params.Constants

/-!
# Package D1: node 28 of `t.weaker.P3`'s Step 1 pigeonhole launch

Source: the proof of Theorem `t.weaker.P3` of [AK], Step 1.

## Main results

* `akhcLaunch_scalar_sandwich`: the pure real "monotone sandwich" arithmetic
  core of node 28 — a product bound on two individually-monotone positive
  reals forces the same bound on each factor.
* `akhcLaunch_pigeonSandwich_block` (**node 28**, `e.first.pigeon.launch.prime`):
  the scalar sandwich lifted, via package A2's block-diagonal iff bridge, to
  the `BlockMatLoewnerLE` shape that the Step 2 `J`-bound consumes as its pigeon hypothesis.

The pigeonhole itself (node 27, `x.AK.HC.theorem.6.1#pigeon.dichotomy`) is `akhcPigeon_main`
(`AKHC61/Pigeon/Main.lean`), applied to the one-dimensional profile
`n ↦ Θ_n = thetaCutoff nu L P n`, bridged via node 28, at `h = 2L`, `δ₁ = σ²δ`, `σ₁ = σ/4`, with
the corrected horizon `N′` (`akhcLaunchNprimeNat`, below — *not* the printed `N`).

## Why the one-dimensional profile suffices (no F018 factor-`d` loss)

Under `ShellLawJ4`, `bfAhom_L(cu_n) = diag(σ̄_n I_d, σ̄*⁻¹_n I_d)`
(`AKHC61/Carrier/ScalarBlocksB.lean`), so `Θ_n := σ̄_n · σ̄*⁻¹_n` is *already*
the full determinant-type potential, a genuine one-dimensional (not
`d`-dimensional) scalar. Applying `akhcPigeon_main` with its own type
parameter instantiated at `1` (not the ambient dimension `d`) to the profile
`n ↦ Θ_n` gives exactly the horizon coefficient `2 δ₁⁻¹ |log σ₁|` (no factor of
`d`), matching the formula `2σ⁻²δ⁻¹|log(σ/4)|` of `akhcLaunchNprimeNat` on the nose (see
`Params/Constants.lean`'s module docstring, "F018/F021"). The "good"
alternative bounds the *product* `Θ_{m-h}/Θ_m ≤ 1+δ₁`; since both `σ̄` and
`σ̄*⁻¹` are individually antitone (package A2), each individual ratio is
already `≥ 1`, so a product bound of `1+δ₁` forces *each* factor's ratio to be
at most `1+δ₁` as well (`akhcLaunch_scalar_sandwich`) — no separate
per-coordinate pigeonhole, and no `d`-dependent loss.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier

noncomputable section

variable {d : ℕ}

/-! ## Node 28, arithmetic core: the pure scalar monotone sandwich -/

/-- **The scalar monotone sandwich.** If `0 < A ≤ A'`, `0 < B ≤ B'`, and the
*product* satisfies `A' * B' ≤ (1+δ) * (A * B)`, then *each* factor
individually satisfies the same `(1+δ)` sandwich: `A' ≤ (1+δ) A` and
`B' ≤ (1+δ) B`. This is where the `F018` "factor-`d`" loss is avoided: no
information is lost passing from the product bound to the per-factor bounds,
because both factors are already known to be `≥ 1` in ratio. -/
theorem akhcLaunch_scalar_sandwich {A A' B B' delta : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hAA' : A ≤ A') (hBB' : B ≤ B')
    (hprod : A' * B' ≤ (1 + delta) * (A * B)) :
    A' ≤ (1 + delta) * A ∧ B' ≤ (1 + delta) * B := by
  have hA' : 0 < A' := hA.trans_le hAA'
  have hB' : 0 < B' := hB.trans_le hBB'
  refine ⟨?_, ?_⟩
  · have h1 : A' * B ≤ A' * B' := mul_le_mul_of_nonneg_left hBB' hA'.le
    have h2 : A' * B ≤ (1 + delta) * A * B := by
      rw [mul_assoc]
      exact h1.trans hprod
    exact le_of_mul_le_mul_right h2 hB
  · have h1 : A * B' ≤ A' * B' := mul_le_mul_of_nonneg_right hAA' hB'.le
    have h2 : A * B' ≤ (1 + delta) * (A * B) := h1.trans hprod
    have h3 : B' * A ≤ (1 + delta) * B * A := by
      rw [mul_comm B' A, mul_assoc, mul_comm B A]
      exact h2
    exact le_of_mul_le_mul_right h3 hA

/-! ## Node 28: the block-Löwner sandwich -/

section Sandwich

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **Node 28** (`e.first.pigeon.launch.prime`). The scalar monotone
sandwich, lifted to the block-Löwner shape that package D2a's `J`-bound
consumes verbatim as its pigeon hypothesis: for `j ≤ ktop` and `Θ_j ≤ (1+δ) Θ_{ktop}`,
`BlockMatLoewnerLE (bfAhom_L(cu_j)) ((1+δ) • bfAhom_L(cu_{ktop}))`. -/
theorem akhcLaunch_pigeonSandwich_block {j ktop : ℕ} (hjktop : j ≤ ktop) {delta : ℝ}
    (hTheta : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P j ≤
      (1 + delta) * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P ktop) :
    BlockMatLoewnerLE (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ))))
      ((1 + delta) • annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))) := by
  have hAmono : sigmaBarSeq nu L P ktop ≤ sigmaBarSeq nu L P j :=
    akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hjktop
  have hBmono : sigmaBarStarInvSeq nu L P ktop ≤ sigmaBarStarInvSeq nu L P j :=
    akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hjktop
  have hApos : 0 < sigmaBarSeq nu L P ktop :=
    akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 ktop
  have hBpos : 0 < sigmaBarStarInvSeq nu L P ktop :=
    akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
      hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 ktop
  obtain ⟨hAle, hBle⟩ := akhcLaunch_scalar_sandwich hApos hBpos hAmono hBmono hTheta
  exact (akhc_blockMatLoewnerLE_annealedBlockMatrix_smul_iff hnu L hJ4 (j : ℤ) (ktop : ℤ)
    (1 + delta)).mpr ⟨hAle, hBle⟩

end Sandwich

/-! ## Node 27: the pigeon dichotomy at the corrected horizon -/

/-- The natural-number reading of the corrected pigeonhole horizon `N′(σ,δ)`
(see `AKHC61/Params/Constants.lean`), for `h = 2L`, `δ₁ = σ²δ`,
`σ₁ = σ/4`: `2L⌈2σ⁻²δ⁻¹|log(σ/4)|⌉`. -/
noncomputable def akhcLaunchNprimeNat (L : ℕ) (delta sigma : ℝ) : ℕ :=
  2 * L * Nat.ceil (2 / (sigma ^ 2 * delta) * |Real.log (sigma / 4)|)

section Dichotomy

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

end Dichotomy

end

end SuperdiffusionCLT.AKHC61.Step2
