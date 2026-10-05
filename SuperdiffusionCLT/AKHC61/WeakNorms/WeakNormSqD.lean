/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.WeakNormSqC
public import SuperdiffusionCLT.AKHC61.Tails.MaximalMomentC
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocks
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import Homogenization.Book.Ch04.Theorems.CanonicalSolutions.Measurability

/-!
# Squared weak norms, part D: `hGradSq` and `hFluxSq` at the cutoff law

The two square-integrability hypotheses that package B2
(`AKHC61/Response/JUpperBound.lean`, `akhc_jUpperBound_of_cutoffLaw`) and the Step 2 skeleton
carry, proved from the root's binders: `0 < ν`, `ShellLawPrefix`, `ShellLawJ2`, `ShellLawJ4` and
V3's (P2′) clause (verbatim), at every scale `m ≥ max(m₂, 1)`, for `s = t = ½` and arbitrary
`p, q, p0, q0`.

## The argument

Normalize by the **deterministic** annealed matrix `E := bfAhom(cu_m)` (positive definite, A2),
take `ρ := γ`, `s' := (γ+1)/4 ∈ [¼, ½)` (so `ρ/2 < s'`) and `k := m - 1`.

1. **Samplewise, law-free** (parts B, C): CG's weak-norm maximizer bound gives
   `weak ≤ 2·RHS` and `RHS ≤ K·(1 + W·M⁺)`, with `K, W` deterministic and
   `M⁺ := M⁺_{m,γ}(E; a_L(ω))` the one-sided event quantity normalized by `E`.
2. **(P2′), through package C1**: `M⁺(ω) ≤ |X(ω)|` with `X = O_{Ψ_S}(H m^D)` measurable
   (`akhcTailEllB_normalizedExcess_moment_le` at `n = h = hprime = m`); in particular the index
   set of `M⁺` is bounded above at every sample.
3. `weak² ≤ 8K²(1 + (W X)²)`, and `(W X)²` is integrable because `p_{Ψ_S} > 2`
   (`akhcMM_integrable_sq_of_isBigO` with the moment order `min 3 p_{Ψ_S} > 2`).

So `E[weak²] < ∞` needs exactly a second moment of the (P2′) variable, which V3 grants. No (P3′)
input is used for integrability; (P3′) enters only the quantitative size of `E[weak²]`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization MeasureTheory
open Homogenization.Book
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

/-- A block-diagonal matrix with two positive scalar blocks is positive definite. -/
theorem akhcWNSq_blockDiag_smul_one_posDef {d : ℕ} {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (toFullBlockMat (Book.Ch02.blockDiag (b • (1 : Mat d)) (c • (1 : Mat d)))).PosDef := by
  have heq : toFullBlockMat (Book.Ch02.blockDiag (b • (1 : Mat d)) (c • (1 : Mat d))) =
      Matrix.diagonal (Sum.elim (fun _ : Fin d => b) (fun _ : Fin d => c)) := by
    ext (i | i) (j | j) <;>
      simp [toFullBlockMat, Book.Ch02.blockDiag, Matrix.diagonal_apply, Matrix.one_apply]
  rw [heq, Matrix.posDef_diagonal_iff]
  rintro (i | i)
  · exact hb
  · exact hc

variable {d : ℕ} [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  -- (P2') `a.ellipticity.weaker`, copied verbatim from
  -- `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`.
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (j : ℤ)) →
          BlockMatLoewnerLE
            (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ)))))

section PosDef

include hnu hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- `bfAhom(cu_m)` is positive definite (J3-free, from A2 and (P2′)). -/
theorem akhcWNSq_annealed_posDef (m : ℤ) :
    (toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d m)))).PosDef := by
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
    hnu L hJ4 m]
  exact akhcWNSq_blockDiag_smul_one_posDef
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarScalar_originCube_pos_of_P2 hnu hJ4
      gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2 m)
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvScalar_pos_of_P2 hnu hJ4
      gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2 m)

end PosDef

section EventBound

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **(P2′) dominates the annealed-normalized event quantity.** For `m ≥ max(m₂, 1)` there is a
measurable `X = O_{Ψ_S}(H m^D)` such that, at every sample, the index set of
`M⁺_{m,γ}(bfAhom(cu_m); a_L(ω))` is bounded above and `M⁺ ≤ |X(ω)|`. -/
theorem akhcWNSq_eventBound {m : ℕ} (hm2 : m2 ≤ m) (hm : 0 < m) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (m : ℝ) ^ D) ∧
      ∀ omega : ShellSeq d,
        BddAbove
          {M : ℝ |
            ∃ Q : TriadicCube d,
              Q.scale ≤ ((m : ℕ) : ℤ) ∧
                cubeCenter Q ∈ cubeSet (originCube d ((m : ℕ) : ℤ)) ∧
                M =
                  Real.rpow (3 : ℝ) (-gamma * ((((m : ℕ) : ℤ) : ℝ) - (Q.scale : ℝ))) *
                    SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess
                      (annealedBlockMatrix nu L P (cubeSet (originCube d ((m : ℕ) : ℤ))))
                      (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toFun)} ∧
        akhcWeakC_eventMoreprotoPlus ((m : ℕ) : ℤ) gamma
            (annealedBlockMatrix nu L P (cubeSet (originCube d ((m : ℕ) : ℤ))))
            (coefficientCutoff nu omega L).toFun ≤ |X omega| := by
  obtain ⟨X, hXm, hXbig, hpt, -⟩ :=
    SuperdiffusionCLT.AKHC61.Tails.akhcTailEllB_normalizedExcess_moment_le hnu hPrefix hJ2
      hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2 (n := m) (h := m) le_rfl hm2 hm (rho := gamma) (hprime := (m : ℝ)) le_rfl
  have hterm : ∀ (omega : ShellSeq d) (Q : TriadicCube d), Q.scale ≤ ((m : ℕ) : ℤ) →
      cubeCenter Q ∈ cubeSet (originCube d ((m : ℕ) : ℤ)) →
      Real.rpow (3 : ℝ) (-gamma * ((((m : ℕ) : ℤ) : ℝ) - (Q.scale : ℝ))) *
          SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess
            (annealedBlockMatrix nu L P (cubeSet (originCube d ((m : ℕ) : ℤ))))
            (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toFun) ≤
        |X omega| := by
    intro omega Q hQs hQc
    have hQr : (Q.scale : ℝ) ≤ (m : ℝ) := by exact_mod_cast hQs
    have h2 := hpt omega Q hQs hQr hQc
    have hsimp : (3 : ℝ) ^ (-(gamma - gamma) * ((m : ℝ) - (m : ℝ))) * |X omega| = |X omega| := by
      simp
    rw [hsimp] at h2
    have hl0 : 0 ≤ (3 : ℝ) ^ (-(gamma * ((m : ℝ) - (Q.scale : ℝ)))) *
        SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess
          (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))))
          (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (SuperdiffusionCLT.AKHC61.Tails.akhcTailEll_excess_nonneg _ _)
    have h3 := (Real.rpow_le_rpow_iff hl0 (abs_nonneg _) (by norm_num : (0 : ℝ) < 2)).1 h2
    rw [SuperdiffusionCLT.AKHC61.Tails.akhcMM_weight_eq]
    exact h3
  refine ⟨X, hXm, hXbig, fun omega => ⟨?_, ?_⟩⟩
  · refine ⟨|X omega|, ?_⟩
    rintro _ ⟨Q, hQs, hQc, rfl⟩
    exact hterm omega Q hQs hQc
  · unfold akhcWeakC_eventMoreprotoPlus
    refine Real.sSup_le ?_ (abs_nonneg _)
    rintro _ ⟨Q, hQs, hQc, rfl⟩
    exact hterm omega Q hQs hQc

end EventBound

end

end SuperdiffusionCLT.AKHC61.WeakNorms
