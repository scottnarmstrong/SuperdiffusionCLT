/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.RecursionB
public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeI
public import Homogenization.Book.Ch02.MultiscaleEllipticity

/-!
# Step 3 recursion, version 2: the linear weak-norm term without a square root

The source term of the Step 3 recursion is `linConst · √(Θ_m · stepBound)`. The square root comes
from bounding the centering vectors crudely, by `‖q₀‖² ≤ Θ_m σ̂_m` and `‖p₀‖² ≤ Θ_m σ̂_m⁻¹`. Those
bounds are of order one. The exact values are small. With `u = √Θ_m` and `r = σ̂_m^{1/2}`,

`q₀ = r (1 - u) e`  and  `p₀ = r⁻¹ (u - 1) e`,

so `‖q₀‖² ≤ (Θ_m - 1)² σ̂_m` and `‖p₀‖² ≤ (Θ_m - 1)² σ̂_m⁻¹` (`akhcRV2_centering_sq_le`).
The two linear weak-norm terms of `CoarseGraining`'s route-W `J`-bound are then at most
`linConst · (Θ_m - 1) · √W` (`akhcRV2_weakSum_le`). By AM-GM this is at most
`(linConst/2) (Θ_m - 1)² + (linConst/2) W`. The recursion with this source,
`(linConst/2) (Θ_m - 1)² + (linConst/2 + prodConst) · stepBound`, is linear in `stepBound`,
with no square root, plus a square of `F m = Θ_m - 1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-- `x · √W ≤ x²/2 + W/2` for `0 ≤ W`. -/
theorem akhcRV2_mul_sqrt_le {x W : ℝ} (hW : 0 ≤ W) :
    x * Real.sqrt W ≤ (1 / 2 : ℝ) * x ^ 2 + (1 / 2 : ℝ) * W := by
  have hs := Real.sq_sqrt hW
  have h0 := sq_nonneg (x - Real.sqrt W)
  nlinarith only [hs, h0]

/-- `u - 1 ≤ u² - 1` for `1 ≤ u`. -/
theorem akhcRV2_sub_one_le_sq_sub_one {u : ℝ} (hu : 1 ≤ u) : u - 1 ≤ u ^ 2 - 1 := by
  nlinarith only [hu]

section Sharp

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
  (hJ4 : ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4

/-- **The sharp centering-vector bounds.** `‖q₀‖² ≤ (Θ_m - 1)² σ̂_m` and
`‖p₀‖² ≤ (Θ_m - 1)² σ̂_m⁻¹`, for `p₀ = akhc_step2P0`, `q₀ = akhc_step2Q0`. The cruder bound has
`Θ_m` in place of `(Θ_m - 1)²`. -/
theorem akhcRV2_centering_sq_le (m : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P m e‖ ^ 2 ≤
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) ^ 2 *
          akhc_sigmaHatScalar nu L P m ∧
      ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P m e‖ ^ 2 ≤
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) ^ 2 *
          (akhc_sigmaHatScalar nu L P m)⁻¹ := by
  have hA : 0 < sigmaBarStarInvSeq nu L P m :=
    akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hB : 0 < sigmaBarSeq nu L P m :=
    akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hTheta1 : 1 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m :=
    akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  obtain ⟨hAc, hBc⟩ := SuperdiffusionCLT.AKHC61.Step2.akhcJB_param hA hB
  generalize hudef : Real.sqrt (sigmaBarSeq nu L P m * sigmaBarStarInvSeq nu L P m) = u at hAc hBc
  have hu1 : 1 ≤ u := by
    rw [← hudef, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hTheta1
  have hcpos : 0 < Real.sqrt (sigmaBarSeq nu L P m / sigmaBarStarInvSeq nu L P m) :=
    Real.sqrt_pos.2 (div_pos hB hA)
  have hsigHat : akhc_sigmaHatScalar nu L P m =
      Real.sqrt (sigmaBarSeq nu L P m / sigmaBarStarInvSeq nu L P m) := by
    rw [akhc_sigmaHatScalar]
  generalize hcdef :
      Real.sqrt (sigmaBarSeq nu L P m / sigmaBarStarInvSeq nu L P m) = c at hcpos hAc hBc hsigHat
  have hr : 0 < c ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hcpos _
  have hrr : c ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c :=
    SuperdiffusionCLT.AKHC61.Step2.akhcJB_rpow_half_mul_self hcpos
  have hp : akhc_specialP nu L P m e = (c ^ (1 / 2 : ℝ))⁻¹ • e := by
    rw [akhc_specialP, hsigHat, SuperdiffusionCLT.AKHC61.Step2.akhcJB_rpow_neg_half hcpos]
  have hq : akhc_specialQ nu L P m e = c ^ (1 / 2 : ℝ) • e := by
    rw [akhc_specialQ, hsigHat]
  generalize hrdef : c ^ (1 / 2 : ℝ) = r at hr hrr hp hq
  rw [← hrr] at hAc hBc
  have hrinv : 0 < r⁻¹ := inv_pos.2 hr
  have hrr1 : r * r * (r⁻¹ * r⁻¹) = 1 := by field_simp
  have hAinv : sigmaBarStarInvSeq nu L P m = u * (r⁻¹ * r⁻¹) := by
    rw [← hAc, mul_assoc, hrr1, mul_one]
  have hur : r ≤ u * r := by
    have h := mul_le_mul_of_nonneg_right hu1 hr.le
    rwa [one_mul] at h
  have hurinv : r⁻¹ ≤ u * r⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hu1 hrinv.le
    rwa [one_mul] at h
  have hq0 : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P m e‖ ≤ u * r - r := by
    have hBr1 : sigmaBarSeq nu L P m * r⁻¹ = u * r := by rw [hBc]; field_simp
    rw [SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0, hq, hp, smul_smul, ← sub_smul, hBr1]
    refine (SuperdiffusionCLT.AKHC61.Step2.akhcJB_norm_smul_le he _).trans (abs_le.2 ⟨?_, ?_⟩)
    · linarith only [hur]
    · linarith only [hur]
  have hp0 : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P m e‖ ≤ u * r⁻¹ - r⁻¹ := by
    have hAr1 : sigmaBarStarInvSeq nu L P m * r = u * r⁻¹ := by rw [hAinv]; field_simp
    rw [SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0, hq, hp, smul_smul, ← sub_smul, hAr1]
    refine (SuperdiffusionCLT.AKHC61.Step2.akhcJB_norm_smul_le he _).trans (abs_le.2 ⟨?_, ?_⟩)
    · linarith only [hurinv]
    · linarith only [hurinv]
  have hΘeq : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m =
      sigmaBarSeq nu L P m * sigmaBarStarInvSeq nu L P m := rfl
  have hu_sq : u ^ 2 = SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
    rw [hΘeq, ← hudef]
    exact Real.sq_sqrt (mul_nonneg hB.le hA.le)
  have hc_eq : akhc_sigmaHatScalar nu L P m = r * r := by rw [hsigHat, ← hrr]
  have hu1' : 0 ≤ u - 1 := by linarith only [hu1]
  have huu : u - 1 ≤ u ^ 2 - 1 := akhcRV2_sub_one_le_sq_sub_one hu1
  have hsq : (u - 1) ^ 2 ≤ (u ^ 2 - 1) ^ 2 := pow_le_pow_left₀ hu1' huu 2
  refine ⟨?_, ?_⟩
  · have hq0' : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P m e‖ ≤ r * (u - 1) := by
      linarith only [hq0]
    calc ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P m e‖ ^ 2
        ≤ (r * (u - 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq0' 2
      _ = (u - 1) ^ 2 * (r * r) := by ring
      _ ≤ (u ^ 2 - 1) ^ 2 * (r * r) :=
          mul_le_mul_of_nonneg_right hsq (mul_nonneg hr.le hr.le)
      _ = (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) ^ 2 *
            akhc_sigmaHatScalar nu L P m := by rw [hc_eq, hu_sq]
  · have hp0' : ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P m e‖ ≤
        r⁻¹ * (u - 1) := by
      linarith only [hp0]
    calc ‖SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P m e‖ ^ 2
        ≤ (r⁻¹ * (u - 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp0' 2
      _ = (u - 1) ^ 2 * (r * r)⁻¹ := by rw [mul_inv]; ring
      _ ≤ (u ^ 2 - 1) ^ 2 * (r * r)⁻¹ :=
          mul_le_mul_of_nonneg_right hsq (inv_nonneg.2 (mul_nonneg hr.le hr.le))
      _ = (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) ^ 2 *
            (akhc_sigmaHatScalar nu L P m)⁻¹ := by rw [hc_eq, hu_sq]

end Sharp

section WeakSum

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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

/-- **The weak-norm sum bound with the sharp centering factor.** The right side is
`linConst · (Θ_m - 1) · √W + prodConst · W`,
`W := akhcPrime_srcEnergy nu L P m e`, in place of `linConst · √(Θ_m W) + prodConst · W`. -/
theorem akhcRV2_weakSum_le (m : ℕ) (hm2 : m2 ≤ m) (hm0 : 0 < m) (e : Vec d)
    (he : vecNormSq e = 1) :
    let Q := Homogenization.originCube d (m : ℤ)
    let p := akhc_specialP nu L P m e
    let q := akhc_specialQ nu L P m e
    let p0 := SuperdiffusionCLT.AKHC61.Step2.akhc_step2P0 nu L P m e
    let q0 := SuperdiffusionCLT.AKHC61.Step2.akhc_step2Q0 nu L P m e
    let BφS := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q
      (1 / 2 : ℝ)
    let BφT := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound Q
      (1 / 2 : ℝ)
    let Cprod := Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff
      Q (1 / 2 : ℝ) (1 / 2 : ℝ)
    let gradCoeff := (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * Homogenization.cubeBesovScaleWeight
      (-(1 / 2 : ℝ)) Q * BφS
    let fluxCoeff := (3 : ℝ) ^ ((d : ℝ) + 1 / 2) * Homogenization.cubeBesovScaleWeight
      (-(1 / 2 : ℝ)) Q * BφT
    let gradWeak : RegCoeffField d → ℝ := fun a =>
      Homogenization.Book.Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q (1 / 2 : ℝ) p q p0
        a.toFun
    let fluxWeak : RegCoeffField d → ℝ := fun a =>
      Homogenization.Book.Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q (1 / 2 : ℝ) p q q0
        a.toFun
    ((1 / 2 : ℝ) * ‖q0‖ * (((Fintype.card (Fin d) : ℝ) * gradCoeff) *
          ∫ a, gradWeak a ∂(cutoffLaw (d := d) nu L P)) +
        (1 / 2 : ℝ) * ‖p0‖ * (((Fintype.card (Fin d) : ℝ) * fluxCoeff) *
          ∫ a, fluxWeak a ∂(cutoffLaw (d := d) nu L P))) +
      Cprod * (Real.sqrt (∫ a, (gradWeak a) ^ 2 ∂(cutoffLaw (d := d) nu L P)) *
        Real.sqrt (∫ a, (fluxWeak a) ^ 2 ∂(cutoffLaw (d := d) nu L P))) ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d *
          ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) *
            Real.sqrt (SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e)) +
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d *
          SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
  intro Q p q p0 q0 BφS BφT Cprod gradCoeff fluxCoeff gradWeak fluxWeak
  set Θm := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m with hΘm_def
  set c := akhc_sigmaHatScalar nu L P m with hc_def
  have hc_pos : 0 < c := akhcRec_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  -- the two square-integrability facts (package "WeakNormSqE")
  have hGradSq : Integrable (fun a : RegCoeffField d => (gradWeak a) ^ 2)
      (cutoffLaw (d := d) nu L P) :=
    SuperdiffusionCLT.AKHC61.WeakNorms.akhcWNSq_integrable_gradientWeakNorm_sq hnu hPrefix
      hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 hm2 hm0 p q p0
  have hFluxSq : Integrable (fun a : RegCoeffField d => (fluxWeak a) ^ 2)
      (cutoffLaw (d := d) nu L P) :=
    SuperdiffusionCLT.AKHC61.WeakNorms.akhcWNSq_integrable_fluxWeakNorm_sq hnu hPrefix hJ2
      hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2 hm2 hm0 p q q0
  -- the `akhcPrime_srcEnergy` decomposition, folded via `set` right after being stated
  -- in expanded form
  have hsrcEnergy_unfold :
      SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e =
        c * (∫ a, (gradWeak a) ^ 2 ∂(cutoffLaw (d := d) nu L P)) +
          c⁻¹ * (∫ a, (fluxWeak a) ^ 2 ∂(cutoffLaw (d := d) nu L P)) := rfl
  set G2 := ∫ a, (gradWeak a) ^ 2 ∂(cutoffLaw (d := d) nu L P) with hG2_def
  set F2 := ∫ a, (fluxWeak a) ^ 2 ∂(cutoffLaw (d := d) nu L P) with hF2_def
  have hG2_nonneg : 0 ≤ G2 := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hF2_nonneg : 0 ≤ F2 := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  -- the centering-vector norm bounds
  obtain ⟨hq0sq, hp0sq⟩ := akhcRV2_centering_sq_le hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m e he
  -- the two Cauchy-Schwarz linear bounds
  have hIG : ∫ a, gradWeak a ∂(cutoffLaw (d := d) nu L P) ≤ Real.sqrt G2 :=
    SuperdiffusionCLT.AKHC61.Step2.akhcJB_integral_le_sqrt_integral_sq hGradSq
  have hIF : ∫ a, fluxWeak a ∂(cutoffLaw (d := d) nu L P) ≤ Real.sqrt F2 :=
    SuperdiffusionCLT.AKHC61.Step2.akhcJB_integral_le_sqrt_integral_sq hFluxSq
  -- the dimensional coefficient bounds
  have hcg0 : 0 ≤ (Fintype.card (Fin d) : ℝ) * gradCoeff :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
      (Homogenization.cubeBesovScaleWeight_nonneg _ _))
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound_nonneg _ _))
  have hcg : (Fintype.card (Fin d) : ℝ) * gradCoeff ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
      Q (by norm_num) (by norm_num)
  have hcf0 : 0 ≤ (Fintype.card (Fin d) : ℝ) * fluxCoeff :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by positivity)
      (Homogenization.cubeBesovScaleWeight_nonneg _ _))
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffDualBound_nonneg _ _))
  have hcf : (Fintype.card (Fin d) : ℝ) * fluxCoeff ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53_linearCutoffCoeff_le_dimensional
      Q (by norm_num) (by norm_num)
  have hCprod0 :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_nonneg Q
      (1 / 2 : ℝ) (1 / 2 : ℝ)
  have hCprod :=
    Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_origin_le_dimensional
      (d := d) m (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
  -- the two `Z` bounds
  have hcG2_le : c * G2 ≤ SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
    rw [hsrcEnergy_unfold]
    have : 0 ≤ c⁻¹ * F2 := mul_nonneg (by positivity) hF2_nonneg
    linarith only [this]
  have hcF2_le : c⁻¹ * F2 ≤ SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
    rw [hsrcEnergy_unfold]
    have : 0 ≤ c * G2 := mul_nonneg hc_pos.le hG2_nonneg
    linarith only [this]
  have hΘ1sq : 0 ≤ (Θm - 1) ^ 2 := sq_nonneg _
  have hZg : ‖q0‖ * ‖q0‖ * G2 ≤
      (Θm - 1) ^ 2 * SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
    have h1 : ‖q0‖ * ‖q0‖ ≤ (Θm - 1) ^ 2 * c := by
      have := hq0sq; rw [sq ‖q0‖] at this; exact this
    calc ‖q0‖ * ‖q0‖ * G2 ≤ ((Θm - 1) ^ 2 * c) * G2 := mul_le_mul_of_nonneg_right h1 hG2_nonneg
      _ = (Θm - 1) ^ 2 * (c * G2) := by ring
      _ ≤ (Θm - 1) ^ 2 * SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e :=
          mul_le_mul_of_nonneg_left hcG2_le hΘ1sq
  have hZf : ‖p0‖ * ‖p0‖ * F2 ≤
      (Θm - 1) ^ 2 * SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
    have h1 : ‖p0‖ * ‖p0‖ ≤ (Θm - 1) ^ 2 * c⁻¹ := by
      have := hp0sq; rw [sq ‖p0‖] at this; exact this
    calc ‖p0‖ * ‖p0‖ * F2 ≤ ((Θm - 1) ^ 2 * c⁻¹) * F2 := mul_le_mul_of_nonneg_right h1 hF2_nonneg
      _ = (Θm - 1) ^ 2 * (c⁻¹ * F2) := by ring
      _ ≤ (Θm - 1) ^ 2 * SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e :=
          mul_le_mul_of_nonneg_left hcF2_le hΘ1sq
  -- term 3: the two linear weak-norm terms
  have hT3g := SuperdiffusionCLT.AKHC61.Step2.akhcJB_linear_term_le (norm_nonneg q0) hcg0 hcg
    hIG hZg
  have hT3f := SuperdiffusionCLT.AKHC61.Step2.akhcJB_linear_term_le (norm_nonneg p0) hcf0 hcf
    hIF hZf
  -- term 4: the product term
  have hcc : (1 : ℝ) ≤ c * c⁻¹ := by rw [mul_inv_cancel₀ hc_pos.ne']
  have hT4le : Real.sqrt G2 * Real.sqrt F2 ≤ c * G2 + c⁻¹ * F2 :=
    SuperdiffusionCLT.AKHC61.Step2.akhcJB_sqrt_mul_sqrt_le (inv_pos.2 hc_pos).le hc_pos.le hcc
      hG2_nonneg hF2_nonneg
  have hT4eq : c * G2 + c⁻¹ * F2 =
      SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e :=
    hsrcEnergy_unfold.symm
  have hCprod_nonneg : 0 ≤ Cprod := hCprod0
  have hW_nonneg : 0 ≤ SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
    rw [← hT4eq]
    have h1 : 0 ≤ c * G2 := mul_nonneg hc_pos.le hG2_nonneg
    have h2 : 0 ≤ c⁻¹ * F2 := mul_nonneg (by positivity) hF2_nonneg
    linarith only [h1, h2]
  have hT4 : Cprod * (Real.sqrt G2 * Real.sqrt F2) ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d *
        SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
    have hstep1 : Cprod * (Real.sqrt G2 * Real.sqrt F2) ≤
        Cprod * SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e := by
      rw [← hT4eq]
      exact mul_le_mul_of_nonneg_left hT4le hCprod_nonneg
    have hstep2 : Cprod * SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e ≤
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d *
          SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e :=
      mul_le_mul_of_nonneg_right hCprod hW_nonneg
    exact hstep1.trans hstep2
  -- assembly: the sum of the linear and product terms
  have hΘ1 : 0 ≤ Θm - 1 := by
    have h1 := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
    linarith only [h1]
  have hsqrtZ : Real.sqrt ((Θm - 1) ^ 2 *
        SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e) =
      (Θm - 1) * Real.sqrt (SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_srcEnergy nu L P m e) := by
    rw [Real.sqrt_mul hΘ1sq, Real.sqrt_sq hΘ1]
  rw [hsqrtZ] at hT3g hT3f
  linarith only [hT3g, hT3f, hT4]

end WeakSum

end

end SuperdiffusionCLT.AKHC61.Step3
