/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioB
public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioC
public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioD
public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioE
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Final
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# `sbIndep_mainB`: the independence-and-ratio estimate, `hGoodN`'s threshold weakened

The proof instantiates the `hGoodN` hypothesis
only at its own internally-chosen constant `C`,
which is always `≥ 1` but otherwise unconstrained from below by anything the
caller supplies. So a hypothesis `∀ Cthresh : ℝ, 1 ≤ Cthresh → ...` would be stronger
than what is ever consumed: `hGoodN` is stated here as
`∃ C0g : ℝ, 1 ≤ C0g ∧ ∀ Cthresh : ℝ, C0g ≤ Cthresh → ...`, and the proof
folds `C0g` into the internal constant
`C0` (so the final chosen `C` is automatically `≥ C0g` too). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization (localizationUpperShells localizationLowerShells
  localizationUpperShells_disjoint_lowerShells)
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **`sbIndep_mainB`**: the independence-and-ratio estimate, with `hGoodN` quantified as
`∃ C0g, 1 ≤ C0g ∧ ∀ Cthresh, C0g ≤ Cthresh`. -/
theorem sbIndep_mainB (d : ℕ) [NeZero d]
    (hGoodN : ∃ Cnear C2 C0g : ℝ, 1 ≤ Cnear ∧ 1 ≤ C2 ∧ 1 ≤ C0g ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ Cthresh : ℝ, C0g ≤ Cthresh →
            ∀ L ell : ℕ, ell < L →
              SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              ∃ n : ℕ,
                (|sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n -
                      (∫ omega, sbIndep_quadTerm (d := d) nu ell L n omega ∂P.toMeasure) -
                      (∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure)| ≤
                    Cnear * (L : ℝ) ^ (-(99 : ℝ))) ∧
                (∀ k l : Fin d, Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
                  sbIndep_sInvMat (d := d) nu ell n omega k l *
                  sbIndep_hMat (d := d) ell L n omega l 0) P.toMeasure) ∧
                (0 ≤ sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ)))) ∧
                (sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ≤
                  C2 * (sigmaBarInfinite nu ell P)⁻¹) ∧
                ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤ sigmaBarSeq nu ell P n) ∧
                (n ≤ ell) ∧
                ((ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1))
    (hAbsorb : ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              (256 : ℝ) * C ≤ sigmaBarInfinite nu ell P ^ 2 ∧
                C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
                      Real.log (L : ℝ) ^ (3 : ℝ) +
                    C * (L : ℝ) ^ (-(99 : ℝ)) ≤ (1 : ℝ) / 8) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              ∃ n : ℕ,
                (|sigmaBarSeq nu L P n * (sigmaBarSeq nu ell P n)⁻¹ - 1| ≤
                    C * M * (L : ℝ) ^ alpha *
                        (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
                        Real.log (L : ℝ) ^ (3 : ℝ) +
                      C * (L : ℝ) ^ (-(99 : ℝ)) ∧
                  C * M * (L : ℝ) ^ alpha *
                        (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
                        Real.log (L : ℝ) ^ (3 : ℝ) +
                      C * (L : ℝ) ^ (-(99 : ℝ)) ≤ (1 : ℝ) / 8) ∧
                (n ≤ ell) ∧
                ((ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1) := by
  obtain ⟨Cnear, C2, C0g, hCnear1, hC21, hC0g1, hGoodN⟩ := hGoodN
  set C0 : ℝ := max C0g (max 1 (max ((8 / 7 : ℝ) * Cnear) (max C2 (max (sbIndep_Cmom0 d)
      ((8 / 7 : ℝ) * C2 * sbIndep_Cmom0 d))))) with hC0def
  have hC0_C0g : C0g ≤ C0 := le_max_left _ _
  have hC0_1 : (1 : ℝ) ≤ C0 := le_trans (le_max_left _ _) (le_max_right _ _)
  obtain ⟨C0', hC0'1, hAbsorbFn⟩ := hAbsorb
  set C : ℝ := max C0 (max C0' (C0 ^ 2)) with hCdef
  have hCC0 : C0 ≤ C := le_max_left _ _
  have hCC0' : C0' ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCC0sq : C0 ^ 2 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCC0g : C0g ≤ C := le_trans hC0_C0g hCC0
  refine ⟨C, le_trans hC0_1 hCC0, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L ell hell
    hLnaught hscale
  obtain ⟨hSigmaSq, hAbsorbBound⟩ := hAbsorbFn C hCC0' nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2
    hJ4 hJ5 alpha M hα0 hα1 hM L ell hell hLnaught hscale
  rcases eq_or_lt_of_le hell with heq | hlt
  · -- `ell = L`: the ratio is `1`, so the bound holds trivially. `n := ell`
    -- trivially satisfies the two new witness conjuncts (`n ≤ ell` is
    -- `le_refl`, and the gap is `0`).
    refine ⟨ell, ⟨?_, hAbsorbBound⟩, le_refl ell, ?_⟩
    · rw [heq]
      have hLpos := sigmaBarSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 L
      rw [mul_inv_cancel₀ hLpos.ne', sub_self, abs_zero]
      have h1 : (0 : ℝ) ≤ C * M * (L : ℝ) ^ alpha *
          (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
        have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
        have hinv0 : (0 : ℝ) ≤ (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) :=
          Real.rpow_nonneg (sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4).le _
        have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one (le_trans hC0_1 hCC0)
        have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hM0) hL0) hinv0) hlog30
      have h2 : (0 : ℝ) ≤ C * (L : ℝ) ^ (-(99 : ℝ)) :=
        mul_nonneg (le_trans zero_le_one (le_trans hC0_1 hCC0))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      linarith only [h1, h2]
    · have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
      linarith only [hlogLnn]
  · -- `ell < L`: the genuine independence-and-ratio argument.
    obtain ⟨n, hNear, hCI3, hSNN, hHP1, hHP2, hNell, hGap⟩ :=
      hGoodN nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM
        C hCC0g L ell hlt hLnaught hscale
    -- `hCIsInv`, `hCI1`, `hCI2` are not carried in `hGoodN`
    -- (see the independence-ratio estimate): `hCIsInv` is the
    -- single-entry integrability `integrable_coarseBlockMatrix_lowerRight_apply`;
    -- `hCI1`/`hCI2` are the
    -- `IndependenceRatioD.sbIndep_integrable_envelope_mul_envelope_mul_hMat`
    -- domination argument.
    have hCIsInv : ∀ k l : Fin d, Integrable (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l)
        P.toMeasure := fun k l =>
      SuperdiffusionCLT.Section2.Annealed.integrable_coarseBlockMatrix_lowerRight_apply
        hnu ell (originCube d (n : ℤ)) hPrefix hJ2 hJ3 hJ4 k l
    have hCI1 : ∀ k l : Fin d, Integrable (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l *
        sbIndep_hMat (d := d) ell L n omega l 0) P.toMeasure := fun k l =>
      sbIndep_integrable_envelope_mul_envelope_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hlt n l
        (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k 0)
        (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l)
        (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
          hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inl 0))
        (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
          hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
        (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
          hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inl 0))
        (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
          hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
    have hCI2 : ∀ k l : Fin d, Integrable (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
        sbIndep_sInvMat (d := d) nu ell n omega k l *
        sbIndep_kcgMat (d := d) nu ell n omega l 0) P.toMeasure := fun k l => by
      have h := sbIndep_integrable_envelope_mul_envelope_mul_hMat hnu hPrefix hJ2 hJ3 hJ4 hlt n k
        (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l)
        (fun omega => sbIndep_kcgMat (d := d) nu ell n omega l 0)
        (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
          hnu ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
        (SuperdiffusionCLT.Section2.Annealed.measurable_blockMatEntry_coarseBlockMatrix
          hnu ell (originCube d (n : ℤ)) (Sum.inr l) (Sum.inl 0))
        (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
          hnu omega ell (originCube d (n : ℤ)) (Sum.inr k) (Sum.inr l))
        (fun omega => SuperdiffusionCLT.Section2.Annealed.abs_blockMatEntry_coarseBlockMatrix_le
          hnu omega ell (originCube d (n : ℤ)) (Sum.inr l) (Sum.inl 0))
      have heq : (fun omega => sbIndep_hMat (d := d) ell L n omega k 0 *
          sbIndep_sInvMat (d := d) nu ell n omega k l *
          sbIndep_kcgMat (d := d) nu ell n omega l 0) =
        (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l *
          sbIndep_kcgMat (d := d) nu ell n omega l 0 *
          sbIndep_hMat (d := d) ell L n omega k 0) := by
        funext omega; ring
      rw [heq]; exact h
    -- The lower-shell strong measurability of the carriers `kcg_ell(cu_n)`,
    -- `s_{ell,*}(cu_n)` is proved directly (not carried in `hGoodN`), from the
    -- full-field measurability of `coefficientCutoff`
    -- (`measurable_SS_coarseBlockMatrix_lowerLeft` and
    -- `measurable_SS_coarseBlockMatrix_lowerRight`,
    -- `Section2/Localization/LocalizationAverageT2Final.lean`).
    have hCM : ∀ k l : Fin d,
        StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)]
          (fun omega => sbIndep_kcgMat (d := d) nu ell n omega k l) ∧
        StronglyMeasurable[shellSigma (d := d) (localizationLowerShells ell)]
          (fun omega => sbIndep_sInvMat (d := d) nu ell n omega k l) := by
      intro k l
      refine ⟨?_, ?_⟩
      · exact (SuperdiffusionCLT.Section2.Localization.measurable_SS_coarseBlockMatrix_lowerLeft
          hnu (originCube d (n : ℤ)) k l).stronglyMeasurable
      · exact (SuperdiffusionCLT.Section2.Localization.measurable_SS_coarseBlockMatrix_lowerRight
          hnu (originCube d (n : ℤ)) k l).stronglyMeasurable
    refine ⟨n, ⟨?_, hAbsorbBound⟩, hNell, hGap⟩
    have hCross : ∫ omega, sbIndep_crossTerm (d := d) nu ell L n omega ∂P.toMeasure = 0 :=
      sbIndep_integral_crossTerm_eq_zero hPrefix hJ2 hJ3 hJ4 nu hlt n
        (fun k l => (hCM k l)) (fun k l => hCI1 k l) (fun k l => hCI2 k l)
    obtain ⟨hQuadNonneg, hQuadLe⟩ :=
      sbIndep_integral_quadTerm_le hPrefix hnu hJ2 hJ3 hJ4 hlt n
        (fun k l => (hCM k l).2) hCIsInv hCI3 hSNN
    rw [hCross, sub_zero] at hNear
    have hdiff_le : sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n ≤
        sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) * sbIndep_Cmom0 d *
            ((L : ℝ) - (ell : ℝ)) +
          Cnear * (L : ℝ) ^ (-(99 : ℝ)) := by
      have := (abs_le.mp hNear).2
      linarith only [this, hQuadLe]
    have hdiff_ge : -(Cnear * (L : ℝ) ^ (-(99 : ℝ))) ≤
        sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n := by
      have := (abs_le.mp hNear).1
      linarith only [this, hQuadNonneg]
    have hSInv_le : sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
        sbIndep_Cmom0 d ≤ C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d :=
      mul_le_mul_of_nonneg_right hHP1 (sbIndep_Cmom0_nonneg d)
    have hLellM : (L : ℝ) - (ell : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      linarith only [hscale]
    have hLellM0 : (0 : ℝ) ≤ (L : ℝ) - (ell : ℝ) := by
      have : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hell
      linarith only [this]
    have hCmom0nn := sbIndep_Cmom0_nonneg d
    have hC2nn : (0 : ℝ) ≤ C2 := le_trans zero_le_one hC21
    have hEllInfPos := sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4
    have hkey : sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n ≤
        C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
            (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) +
          Cnear * (L : ℝ) ^ (-(99 : ℝ)) := by
      have hstep1 : sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) *
          sbIndep_Cmom0 d * ((L : ℝ) - (ell : ℝ)) ≤
          C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d * ((L : ℝ) - (ell : ℝ)) :=
        mul_le_mul_of_nonneg_right hSInv_le hLellM0
      have hMLnn : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
        have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
        have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
        positivity
      have hstep2 : C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d * ((L : ℝ) - (ell : ℝ)) ≤
          C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
            (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hLellM
          (mul_nonneg (mul_nonneg hC2nn (inv_nonneg.2 hEllInfPos.le)) hCmom0nn)
      linarith only [hdiff_le, hstep1, hstep2]
    have hratio_le : sigmaBarSeq nu L P n * (sigmaBarSeq nu ell P n)⁻¹ - 1 ≤
        C0 * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) +
          C0 * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) := by
      have hEllnPos := sigmaBarSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
      have h78 : (7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤ sigmaBarSeq nu ell P n := hHP2
      have hratio_eq : sigmaBarSeq nu L P n * (sigmaBarSeq nu ell P n)⁻¹ - 1 =
          (sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n) * (sigmaBarSeq nu ell P n)⁻¹ := by
        field_simp
      have hinv_le : (sigmaBarSeq nu ell P n)⁻¹ ≤ (8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹ := by
        have h78pos : (0 : ℝ) < (7 / 8 : ℝ) * sigmaBarInfinite nu ell P := by positivity
        calc (sigmaBarSeq nu ell P n)⁻¹ ≤
            ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P)⁻¹ :=
              inv_anti₀ h78pos h78
          _ = (8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹ := by
              rw [mul_inv, inv_div]
      have hnum_nonneg : (0 : ℝ) ≤ C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
          (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) + Cnear * (L : ℝ) ^ (-(99 : ℝ)) := by
        have h1 : (0 : ℝ) ≤ C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
            (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
          have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
          have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
          have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
          have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
          positivity
        have h2 : (0 : ℝ) ≤ Cnear * (L : ℝ) ^ (-(99 : ℝ)) :=
          mul_nonneg (le_trans zero_le_one hCnear1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        linarith only [h1, h2]
      rw [hratio_eq]
      have hchain : (sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n) *
          (sigmaBarSeq nu ell P n)⁻¹ ≤
          (C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
              (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) +
            Cnear * (L : ℝ) ^ (-(99 : ℝ))) * ((8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹) := by
        calc (sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n) * (sigmaBarSeq nu ell P n)⁻¹ ≤
            (C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
                (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) +
              Cnear * (L : ℝ) ^ (-(99 : ℝ))) * (sigmaBarSeq nu ell P n)⁻¹ :=
              mul_le_mul_of_nonneg_right hkey (inv_nonneg.2 hEllnPos.le)
          _ ≤ (C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
                (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) +
              Cnear * (L : ℝ) ^ (-(99 : ℝ))) * ((8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹) :=
              mul_le_mul_of_nonneg_left hinv_le hnum_nonneg
      have hrw : (C2 * (sigmaBarInfinite nu ell P)⁻¹ * sbIndep_Cmom0 d *
              (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) +
            Cnear * (L : ℝ) ^ (-(99 : ℝ))) * ((8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹) =
          (8 / 7 : ℝ) * C2 * sbIndep_Cmom0 d * M * (L : ℝ) ^ alpha *
              ((sigmaBarInfinite nu ell P)⁻¹ * (sigmaBarInfinite nu ell P)⁻¹) *
              Real.log (L : ℝ) ^ (3 : ℝ) +
            (8 / 7 : ℝ) * Cnear * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) := by
        ring
      rw [hrw] at hchain
      have hinvsq : (sigmaBarInfinite nu ell P)⁻¹ * (sigmaBarInfinite nu ell P)⁻¹ =
          (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hEllInfPos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast, pow_two, mul_inv]
      rw [hinvsq] at hchain
      have hc0ge1 : (8 / 7 : ℝ) * C2 * sbIndep_Cmom0 d ≤ C0 := by
        rw [hC0def]
        exact le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))))
      have hc0geCnear : (8 / 7 : ℝ) * Cnear ≤ C0 := by
        rw [hC0def]
        exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hMLlog0 : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha *
          (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
        have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
        have hinv0 : (0 : ℝ) ≤ (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) :=
          Real.rpow_nonneg hEllInfPos.le _
        have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
        positivity
      have hLm990 : (0 : ℝ) ≤ (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) :=
        mul_nonneg (inv_nonneg.2 hEllInfPos.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hbound1 : (8 / 7 : ℝ) * C2 * sbIndep_Cmom0 d * M * (L : ℝ) ^ alpha *
              (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) ≤
            C0 * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hc0ge1 hMLlog0
        calc (8 / 7 : ℝ) * C2 * sbIndep_Cmom0 d * M * (L : ℝ) ^ alpha *
              (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) =
            (8 / 7 : ℝ) * C2 * sbIndep_Cmom0 d * (M * (L : ℝ) ^ alpha *
              (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
          _ ≤ C0 * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) := this
      have hbound2 : (8 / 7 : ℝ) * Cnear * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) ≤
          C0 * ((sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ))) := by
        have := mul_le_mul_of_nonneg_right hc0geCnear hLm990
        calc (8 / 7 : ℝ) * Cnear * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) =
            (8 / 7 : ℝ) * Cnear * ((sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ))) := by
              ring
          _ ≤ C0 * ((sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ))) := this
      linarith only [hchain, hbound1, hbound2]
    have hc0geCnear' : (8 / 7 : ℝ) * Cnear ≤ C0 := by
      rw [hC0def]
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hratio_ge : -(C0 * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ) +
        C0 * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ))) ≤
        sigmaBarSeq nu L P n * (sigmaBarSeq nu ell P n)⁻¹ - 1 := by
      have hEllnPos := sigmaBarSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n
      have h78 : (7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤ sigmaBarSeq nu ell P n := hHP2
      have h78pos : (0 : ℝ) < (7 / 8 : ℝ) * sigmaBarInfinite nu ell P := by positivity
      have hinv_le : (sigmaBarSeq nu ell P n)⁻¹ ≤ (8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹ := by
        calc (sigmaBarSeq nu ell P n)⁻¹ ≤ ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P)⁻¹ :=
              inv_anti₀ h78pos h78
          _ = (8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹ := by rw [mul_inv, inv_div]
      have hratio_eq : sigmaBarSeq nu L P n * (sigmaBarSeq nu ell P n)⁻¹ - 1 =
          (sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n) * (sigmaBarSeq nu ell P n)⁻¹ := by
        field_simp
      rw [hratio_eq]
      have hCnearL990 : (0 : ℝ) ≤ Cnear * (L : ℝ) ^ (-(99 : ℝ)) :=
        mul_nonneg (le_trans zero_le_one hCnear1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hstep1 : -(Cnear * (L : ℝ) ^ (-(99 : ℝ))) * (sigmaBarSeq nu ell P n)⁻¹ ≤
          (sigmaBarSeq nu L P n - sigmaBarSeq nu ell P n) * (sigmaBarSeq nu ell P n)⁻¹ :=
        mul_le_mul_of_nonneg_right hdiff_ge (inv_nonneg.2 hEllnPos.le)
      have hneg : -(Cnear * (L : ℝ) ^ (-(99 : ℝ))) ≤ 0 := by linarith only [hCnearL990]
      have hstep2 : -(Cnear * (L : ℝ) ^ (-(99 : ℝ))) * ((8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹) ≤
          -(Cnear * (L : ℝ) ^ (-(99 : ℝ))) * (sigmaBarSeq nu ell P n)⁻¹ :=
        mul_le_mul_of_nonpos_left hinv_le hneg
      have hLm990 : (0 : ℝ) ≤ (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) :=
        mul_nonneg (inv_nonneg.2 (sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4).le)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hbound3 : -(Cnear * (L : ℝ) ^ (-(99 : ℝ))) * ((8 / 7 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹) =
          -((8 / 7 : ℝ) * Cnear * ((sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)))) := by
        ring
      have hbound4 : -((8 / 7 : ℝ) * Cnear * ((sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)))) ≥
          -(C0 * ((sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)))) := by
        have := mul_le_mul_of_nonneg_right hc0geCnear' hLm990
        linarith only [this]
      have hMLlog0' : (0 : ℝ) ≤ C0 * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ) := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
        have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
        have hinv0 : (0 : ℝ) ≤ (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) :=
          Real.rpow_nonneg (sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4).le _
        have hC00 : (0 : ℝ) ≤ C0 := le_trans zero_le_one hC0_1
        have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC00 hM0) hL0) hinv0) hlog30
      linarith only [hstep1, hstep2, hbound3, hbound4, hMLlog0']
    -- `hMono`: `C0`'s display `≤` `C`'s display, via `256 * C ≤ shom_ell²` (`hSigmaSq`,
    -- from `hAbsorbFn`) and `C0² ≤ C` (`hCC0sq`): together these give `16 * C0 ≤ shom_ell`,
    -- which absorbs the `shom_ell⁻¹` factor on the second term into the growth from `C0`
    -- to `C` (the role the deleted `hLvsLnaught`'s first conjunct used to play).
    have hEllInfPos' := sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4
    have h256C0sq : (256 : ℝ) * C0 ^ 2 ≤ 256 * C := mul_le_mul_of_nonneg_left hCC0sq (by norm_num)
    have heqsq : ((16 : ℝ) * C0) ^ 2 = 256 * C0 ^ 2 := by ring
    have hSq16C0 : ((16 : ℝ) * C0) ^ 2 ≤ sigmaBarInfinite nu ell P ^ 2 := by
      rw [heqsq]; linarith only [h256C0sq, hSigmaSq]
    have h16C0nn : (0 : ℝ) ≤ 16 * C0 := by linarith only [hC0_1]
    have hShomEll16C0 : 16 * C0 ≤ sigmaBarInfinite nu ell P := by
      have habs := abs_le_of_sq_le_sq hSq16C0 hEllInfPos'.le
      rwa [abs_of_nonneg h16C0nn] at habs
    have hMono : C0 * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ) +
        C0 * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) ≤
        C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) +
          C * (L : ℝ) ^ (-(99 : ℝ)) := by
      have hMLlog0'' : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ) := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
        have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
        have hinv0 : (0 : ℝ) ≤ (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) :=
          Real.rpow_nonneg hEllInfPos'.le _
        have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
        positivity
      have hterm1 : C0 * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) ≤
          C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) := by
        have heq1 : C0 * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ) =
            C0 * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
        have heq2 : C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ) =
            C * (M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
              Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
        rw [heq1, heq2]
        exact mul_le_mul_of_nonneg_right hCC0 hMLlog0''
      have hL990nn : (0 : ℝ) ≤ (L : ℝ) ^ (-(99 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hC0shom : C0 * (sigmaBarInfinite nu ell P)⁻¹ ≤ 1 / 16 := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hEllInfPos' (by norm_num : (0 : ℝ) < 16)]
        linarith only [hShomEll16C0]
      have hterm2 : C0 * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) ≤
          C * (L : ℝ) ^ (-(99 : ℝ)) := by
        calc C0 * (sigmaBarInfinite nu ell P)⁻¹ * (L : ℝ) ^ (-(99 : ℝ)) ≤
              (1 / 16 : ℝ) * (L : ℝ) ^ (-(99 : ℝ)) :=
              mul_le_mul_of_nonneg_right hC0shom hL990nn
          _ ≤ C * (L : ℝ) ^ (-(99 : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith only [hC0_1, hCC0]) hL990nn
      linarith only [hterm1, hterm2]
    refine abs_le.mpr ⟨by linarith only [hratio_ge, hMono], by linarith only [hratio_le, hMono]⟩

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
