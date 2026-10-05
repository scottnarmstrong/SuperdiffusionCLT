/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section4.EllipticityBelowCutoff
public import SuperdiffusionCLT.Section2.Annealed.Envelope
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section4.HomogBelow.GrowthCondition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Verification of the weaker ellipticity assumption (P2') of [AK, Theorem 6.1] for the
choice of `l.we.can.apply.hc` (see `e.checkingp2prime`): `H := C_(ellipticity) γ⁻¹ν⁻²`,
`D := 1`, `Ψ_S := Γ_1`, `K_{Ψ_S}`, `p_{Ψ_S} := 2d`, `m₂ := ⌈L/4⌉` -- from
`SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff`
(`p.ellipticity.Ptwoprime`) and the growth
lemma `homogBelow_gammaSigma_growthCondition_ge_two` (`GrowthCondition.lean`).

`H` is taken as `4 · C_(ellipticity) · γ⁻¹ · ν⁻²` (not the printed
`C_(ellipticity) γ⁻¹ν⁻²`): `ellipticity_below_cutoff`'s own amplitude is
`C·γ⁻¹·ν⁻²·L` at every scale `j ≥ m₂ = ⌈L/4⌉`, constant in `j`, while (P2') of [AK]
wants an amplitude `H·j^D = H·j` that *grows* with `j`; the factor `4`
is exactly what is needed so that `H·j ≥ C·γ⁻¹·ν⁻²·L` already at the
worst case `j = m₂` (using `4·m₂ ≥ L`), after which `IsBigO`'s monotonicity
in the amplitude (`IsBigOWith.mono_scale`) absorbs the rest. This is a
genuine (small) strengthening of the printed choice, not a weakening: replacing
`H` by `4H` only weakens the concentration bound.

The one-sided Loewner form of (P2') (as opposed to `ellipticity_below_cutoff`'s
own two-sided bilinear form) is derived here from first
principles: set `p = q` in the bilinear bound and use positive-semidefiniteness
of `annealedBlockMatrix` (reproduced below from public building blocks, since
`zero_le_blockVecDot_annealedBlockMatrix_cubeSet`,
`Section2/Localization/LocalizationDisplayC.lean`, is `private`). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- **PSD-ness of the annealed block matrix**, quadratic-form form: reproduced
from the public `blockVecDot_annealedBlockMatrix`
(`Section2/Annealed/Envelope.lean`) and
`zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff`
(`Section2/Annealed/Integrability.lean`), since the corresponding fact
for a general cube (`zero_le_blockVecDot_annealedBlockMatrix_cubeSet`,
`Section2/Localization/LocalizationDisplayC.lean`) is declared `private`
and not consumable from here. -/
theorem homogBelow_zero_le_blockVecDot_annealedBlockMatrix
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l : ℕ) (Q : Homogenization.TriadicCube d) (X : Homogenization.BlockVec d) :
    0 ≤ Homogenization.blockVecDot X
      (Homogenization.blockMatVecMul
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu l P
          (Homogenization.cubeSet Q)) X) := by
  rw [SuperdiffusionCLT.Section2.Annealed.blockVecDot_annealedBlockMatrix
    hnu l Q hPrefix hJ2 hJ3 hJ4 X]
  exact MeasureTheory.integral_nonneg fun omega =>
    SuperdiffusionCLT.Section2.Annealed.zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff
      hnu omega l Q X

/-- **The one-sided Loewner conversion**: from the two-sided bilinear bound
`2 p·Hq ≤ t(p·Ap + q·Aq)` (for every `p q`) and positive-semidefiniteness of
`A`, get `H ⪯ (1+t) • A` in `BlockMatLoewnerLE`'s quadratic-form sense
(the quadratic-form sense): set `p = q =: X`, giving `X·HX ≤ t·X·AX`, then add
`(1-t)·... ` -- more precisely `t·X·AX ≤ (1+t)·X·AX` since `X·AX ≥ 0` for every
sign of `t`. -/
theorem homogBelow_blockMatLoewnerLE_of_bilinear
    {d : ℕ} {H A : Homogenization.BlockMat d} {t : ℝ}
    (hA : ∀ X : Homogenization.BlockVec d,
      0 ≤ Homogenization.blockVecDot X (Homogenization.blockMatVecMul A X))
    (hbil : ∀ p q : Homogenization.BlockVec d,
      2 * Homogenization.blockVecDot p (Homogenization.blockMatVecMul H q) ≤
        t * (Homogenization.blockVecDot p (Homogenization.blockMatVecMul A p) +
          Homogenization.blockVecDot q (Homogenization.blockMatVecMul A q))) :
    Homogenization.BlockMatLoewnerLE H ((1 + t) • A) := by
  intro X
  have hXX := hbil X X
  have hXA := hA X
  have heq : Homogenization.blockMatVecMul ((1 + t) • A) X =
      (1 + t) • Homogenization.blockMatVecMul A X :=
    Homogenization.blockMatVecMul_blockSMul (1 + t) A X
  rw [heq, Homogenization.blockVecDot_smul_right]
  set a := Homogenization.blockVecDot X (Homogenization.blockMatVecMul H X) with ha_def
  set b := Homogenization.blockVecDot X (Homogenization.blockMatVecMul A X) with hb_def
  have hstep1 : 2 * a ≤ 2 * (t * b) := by
    have hring : t * (b + b) = 2 * (t * b) := by ring
    linarith only [hXX, hring]
  have hstep2 : a ≤ t * b := by linarith only [hstep1]
  have hstep3 : t * b ≤ (1 + t) * b := by
    have hring2 : (1 + t) * b - t * b = b := by ring
    linarith only [hXA, hring2]
  have hstep4 : a ≤ (1 + t) * b := le_trans hstep2 hstep3
  linarith only [hstep4]

/-- **The deterministic ellipticity constant**: `ellipticity_below_cutoff`'s
own witness, extracted via `Classical.choose` (not `obtain`) so that it is a
single, reusable real number across every file that needs it — in
particular so `homogBelow_P2prime_verified`'s witness `H` can be stated as an
*equation* in terms of it (see the final conjunct below), letting a
downstream caller (`M0ThresholdB.lean`, parametrized by an
explicit `Cellip`) use the very same constant. -/
noncomputable def homogBelow_Cellip (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  (SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff d hd).choose

theorem homogBelow_Cellip_ge1 (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    1 ≤ homogBelow_Cellip d hd :=
  (SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff d hd).choose_spec.1

/-- **The (P2') clause, verified.** For every `γ ∈ (0,1)` and every
infrared cutoff scale `L ≥ 1`, the choice `H := 4 C_(ellipticity) γ⁻¹ ν⁻²`,
`D := 1`, `m₂ := ⌈L/4⌉`, `Ψ_S := Γ_1`, `K_{Ψ_S} := gammaGrowthConst 1`,
`p_{Ψ_S} := 2d` discharges every premise of the (P2') binder in
`akhc_weakerP3`, using only `ellipticity_below_cutoff`. The extra final conjunct `4 * m2 ≤ L +
3` exposes the concrete size of the witness `m2 := (L+3)/4` (needed in
`ThetaLmAssemblyAKHCApp.lean`: since `m2` is
otherwise hidden behind this theorem's own `∃`, a caller who `obtain`s it has
no way to bound it against `L`, which is needed to discharge the
`max m2 m3 ≤ m` premise of [AK, Theorem 6.1]). The further final conjunct `H = 4 *
homogBelow_Cellip d hd * gamma⁻¹ * nu^(-2)` similarly exposes `H`'s exact
formula in terms of the deterministic `homogBelow_Cellip` (needed for
`homogBelowM0_threshold_corrected` of `M0ThresholdB.lean`, whose `H := 8 *
Cellip * nu⁻²` at `gamma = 1/2` must be matched against this same opaque `H`
by equality, not merely by construction). The three further final
conjuncts `D = 1`, `KPsiS = gammaGrowthConst 1`, `pPsiS = 2 * (d : ℝ)`
expose the same witnesses' exact values for the same reason: the
match between `ThetaLmAssemblyAKHCApp.lean`'s generic (`D, H,
KPsiS, pPsiS`-parametrized) "big-log ≤ m0" hypothesis and
`M0ThresholdB.lean`'s `homogBelowM0_threshold_corrected` (hardwired at
`D=1, KPsiS=2, pPsiS=2d`) needs these as rewritable equalities, not merely
definitional facts erased by `obtain`. -/
theorem homogBelow_P2prime_verified
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (L : ℕ) (hL : 1 ≤ L)
    (gamma : ℝ) (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1) :
    ∃ (H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ),
      1 ≤ H ∧ 0 ≤ D ∧
      MonotoneOn PsiS (Set.Ici 0) ∧ (∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t) ∧
      1 ≤ KPsiS ∧ 3 ≤ pPsiS ∧
      (∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
        s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t)) ∧
      (∀ j : ℕ, m2 ≤ j →
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
                ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                  SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                    (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ))))) ∧
      4 * m2 ≤ L + 3 ∧
      H = 4 * homogBelow_Cellip d hd * gamma⁻¹ * nu ^ (-(2 : ℝ)) ∧
      D = 1 ∧ KPsiS = Homogenization.IndependentSums.gammaGrowthConst 1 ∧
      pPsiS = 2 * (d : ℝ) := by
  set C : ℝ := homogBelow_Cellip d hd with hCdef
  have hC1 : (1 : ℝ) ≤ C := homogBelow_Cellip_ge1 d hd
  have hEllRaw := (SuperdiffusionCLT.Frozen.Section4.ellipticity_below_cutoff d hd).choose_spec.2
  have hgammaInv : (1 : ℝ) ≤ gamma⁻¹ := (one_le_inv₀ hgamma0).mpr hgamma1.le
  have hnu2le1 : nu ^ (2 : ℝ) ≤ 1 := by
    calc nu ^ (2 : ℝ) ≤ (1 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow 2
  have hnu2pos : (0 : ℝ) < nu ^ (2 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hnuRpow : (1 : ℝ) ≤ nu ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hnu.le]
    exact (one_le_inv₀ hnu2pos).mpr hnu2le1
  refine ⟨4 * C * gamma⁻¹ * nu ^ (-(2 : ℝ)), 1, (L + 3) / 4,
    Homogenization.IndependentSums.gammaSigma 1,
    Homogenization.IndependentSums.gammaGrowthConst 1, 2 * (d : ℝ),
    ?_, zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1 ≤ H
    have hCnonneg : (0 : ℝ) ≤ C := by linarith only [hC1]
    have hCle : C ≤ C * gamma⁻¹ := by
      calc C = C * 1 := (mul_one C).symm
        _ ≤ C * gamma⁻¹ := mul_le_mul_of_nonneg_left hgammaInv hCnonneg
    have h1 : (1 : ℝ) ≤ C * gamma⁻¹ := le_trans hC1 hCle
    have h1nonneg : (0 : ℝ) ≤ C * gamma⁻¹ := le_trans zero_le_one h1
    have h2le : C * gamma⁻¹ ≤ C * gamma⁻¹ * nu ^ (-(2 : ℝ)) := by
      calc C * gamma⁻¹ = C * gamma⁻¹ * 1 := (mul_one _).symm
        _ ≤ C * gamma⁻¹ * nu ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hnuRpow h1nonneg
    have h2 : (1 : ℝ) ≤ C * gamma⁻¹ * nu ^ (-(2 : ℝ)) := le_trans h1 h2le
    have h3 : (1 : ℝ) ≤ 4 * (C * gamma⁻¹ * nu ^ (-(2 : ℝ))) := by linarith only [h2]
    calc (1 : ℝ) ≤ 4 * (C * gamma⁻¹ * nu ^ (-(2 : ℝ))) := h3
      _ = 4 * C * gamma⁻¹ * nu ^ (-(2 : ℝ)) := by ring
  · -- MonotoneOn PsiS (Set.Ici 0)
    exact (Homogenization.IndependentSums.admissiblePsi_gammaSigma (by norm_num : (0:ℝ) ≤ 1)).1
  · -- ∀ t, 0 ≤ t → 1 ≤ PsiS t
    exact (Homogenization.IndependentSums.admissiblePsi_gammaSigma (by norm_num : (0:ℝ) ≤ 1)).2
  · -- 1 ≤ KPsiS
    exact le_trans one_le_two (Homogenization.IndependentSums.two_le_gammaGrowthConst 1)
  · -- 3 ≤ pPsiS
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hd2]
  · -- growth condition
    intro p hp2 _hpUB t s ht hs
    exact SuperdiffusionCLT.Section4.HomogBelow.homogBelow_gammaSigma_growthCondition_ge_two
      (by norm_num : (0:ℝ) < 1) p hp2 t s ht hs
  · -- (P2') existence
    intro j hj
    have hLj4 : L ≤ 4 * j := by omega
    have hLj : (L : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast hLj4
    obtain ⟨X, hXmeas, hXbig, hXbil⟩ :=
      hEllRaw nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 gamma hgamma0 hgamma1 j L hL hLj
    refine ⟨X, hXmeas, ?_, ?_⟩
    · have hnn : (0 : ℝ) ≤ C * gamma⁻¹ * nu ^ (-(2 : ℝ)) := by positivity
      have hamp : C * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (L : ℝ) ≤
          (4 * C * gamma⁻¹ * nu ^ (-(2 : ℝ))) * (j : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
        calc C * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (L : ℝ) ≤
              C * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (4 * (j : ℝ)) :=
            mul_le_mul_of_nonneg_left hLj hnn
          _ = 4 * C * gamma⁻¹ * nu ^ (-(2 : ℝ)) * (j : ℝ) := by ring
      exact Homogenization.IndependentSums.IsBigOWith.mono_scale hXbig hamp
    · intro omega Q hQscale hQcenter
      refine homogBelow_blockMatLoewnerLE_of_bilinear
        (homogBelow_zero_le_blockVecDot_annealedBlockMatrix hnu hPrefix hJ2 hJ3 hJ4 L
          (Homogenization.originCube d (j : ℤ)))
        ?_
      intro p q
      exact hXbil omega Q.scale hQscale Q rfl hQcenter p q
  · -- 4 * m2 ≤ L + 3, exposing the witness `m2 := (L+3)/4`'s size to callers
    rw [mul_comm]
    exact Nat.div_mul_le_self (L + 3) 4
  · -- H = 4 * homogBelow_Cellip d hd * gamma⁻¹ * nu ^ (-2), by definition of C
    rfl
  · -- D = 1
    rfl
  · -- KPsiS = gammaGrowthConst 1
    rfl
  · -- pPsiS = 2 * (d : ℝ)
    rfl

end SuperdiffusionCLT.Section4.HomogBelow
