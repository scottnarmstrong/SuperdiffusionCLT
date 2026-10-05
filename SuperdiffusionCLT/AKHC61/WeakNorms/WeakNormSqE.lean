/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.WeakNormSqD

/-!
# Squared weak norms, part E: the two integrability theorems

`akhcWNSq_integrable_gradientWeakNorm_sq` and `akhcWNSq_integrable_fluxWeakNorm_sq` are exactly
the hypotheses `hGradSq` and `hFluxSq` of `akhc_jUpperBound_of_cutoffLaw`
(`AKHC61/Response/JUpperBound.lean`) at `m : ℕ` with `m ≥ max(m₂, 1)`, proved from the root's
binders (`0 < ν`, `ShellLawPrefix`, `ShellLawJ2`, `ShellLawJ4`, V3's (P2′) clause). See
`WeakNormSqD.lean` for the argument.
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

/-! ## Elementary facts -/

/-- `(2K(1 + W x))² ≤ 8K²(1 + (W x)²)`. -/
theorem akhcWNSq_sq_bound {K W x : ℝ} :
    (2 * K * (1 + W * x)) ^ 2 ≤ 8 * K ^ 2 * (1 + (W * x) ^ 2) := by
  have h : 0 ≤ (K * (1 - W * x)) ^ 2 := sq_nonneg _
  nlinarith only [h]

omit [NeZero d] in
/-- The weak norm (a supremum of nonnegative partial sums) is nonnegative. -/
theorem akhcWNSq_gradientWeakNorm_nonneg (Q : TriadicCube d) (s : ℝ) (p q p0 : Vec d)
    (a : CoeffField d) : 0 ≤ Ch04.canonicalScalarResponseGradientWeakNormCubeSet Q s p q p0 a := by
  unfold Ch04.canonicalScalarResponseGradientWeakNormCubeSet
  refine Real.iSup_nonneg fun N => ?_
  unfold Ch04.canonicalScalarResponseGradientWeakNormPartialCubeSet
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

omit [NeZero d] in
theorem akhcWNSq_fluxWeakNorm_nonneg (Q : TriadicCube d) (t : ℝ) (p q q0 : Vec d)
    (a : CoeffField d) : 0 ≤ Ch04.canonicalScalarResponseFluxWeakNormCubeSet Q t p q q0 a := by
  unfold Ch04.canonicalScalarResponseFluxWeakNormCubeSet
  refine Real.iSup_nonneg fun N => ?_
  unfold Ch04.canonicalScalarResponseFluxWeakNormPartialCubeSet
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

omit [NeZero d] in
theorem akhcWNSq_gradConst_nonneg {E : BlockMat d} {m k : ℤ} {s s' ρ C : ℝ} (hs : 0 ≤ s)
    (hs's : s' ≤ s) (hC : 0 ≤ C) (p q p0 : Vec d) :
    0 ≤ akhcWNSq_gradConst E m k s s' ρ C p q p0 := by
  unfold akhcWNSq_gradConst
  have h1 : 0 ≤ (s - s')⁻¹ := inv_nonneg.mpr (by linarith only [hs's])
  have h2 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs
  have h3 := Real.sqrt_nonneg (akhcWNSq_Bg E p q p0)
  have h4 := Real.sqrt_nonneg (akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.lowerRight *
    akhcWNSq_Bj E p q)
  have h5 : (0 : ℝ) ≤ ((Finset.Icc (k + 1) m).card : ℝ) := Nat.cast_nonneg _
  have h6 := norm_nonneg p0
  positivity

omit [NeZero d] in
theorem akhcWNSq_fluxConst_nonneg {E : BlockMat d} {m k : ℤ} {s s' ρ C : ℝ} (hs : 0 ≤ s)
    (hs's : s' ≤ s) (hC : 0 ≤ C) (p q q0 : Vec d) :
    0 ≤ akhcWNSq_fluxConst E m k s s' ρ C p q q0 := by
  unfold akhcWNSq_fluxConst
  have h1 : 0 ≤ (s - s')⁻¹ := inv_nonneg.mpr (by linarith only [hs's])
  have h2 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs
  have h3 := Real.sqrt_nonneg (akhcWNSq_Bf E p q q0)
  have h4 := Real.sqrt_nonneg (akhcWeakC2_maximizerConst s' ρ * Ch02.matrixNorm E.upperLeft *
    akhcWNSq_Bj E p q)
  have h5 : (0 : ℝ) ≤ ((Finset.Icc (k + 1) m).card : ℝ) := Nat.cast_nonneg _
  have h6 := norm_nonneg q0
  positivity

/-- The exponent bookkeeping for `s = ½`, `s' = (γ+1)/4`, `ρ = γ`. -/
theorem akhcWNSq_exponents {gamma : ℝ} (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) :
    0 < (gamma + 1) / 4 ∧ (1 / 2 : ℝ) / 2 ≤ (gamma + 1) / 4 ∧ (gamma + 1) / 4 < 1 / 2 ∧
      gamma / 2 < (gamma + 1) / 4 := by
  refine ⟨by linarith only [hgamma0], by linarith only [hgamma0], by linarith only [hgamma1],
    by linarith only [hgamma1]⟩

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **`hGradSq` at the cutoff law.** For `m ≥ max(m₂, 1)` and any `p, q, p0`, the squared
gradient weak norm at `s = ½` is integrable under `cutoffLaw ν L P`. -/
theorem akhcWNSq_integrable_gradientWeakNorm_sq {m : ℕ} (hm2 : m2 ≤ m) (hm : 0 < m)
    (p q p0 : Vec d) :
    Integrable
      (fun a : RegCoeffField d =>
        (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (originCube d (m : ℤ)) (1 / 2 : ℝ) p q p0 a.toFun) ^ 2)
      (cutoffLaw (d := d) nu L P) := by
  obtain ⟨X, hXm, hXbig, hX⟩ := akhcWNSq_eventBound hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hm2 hm
  obtain ⟨hs'0, hs'low, hs'high, hgap⟩ := akhcWNSq_exponents hgamma0 hgamma1
  set E := annealedBlockMatrix nu L P (cubeSet (originCube d ((m : ℕ) : ℤ))) with hEdef
  have hE : (toFullBlockMat E).PosDef :=
    akhcWNSq_annealed_posDef hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 _
  set k : ℤ := (m : ℤ) - 1 with hkdef
  have hkm : k < (m : ℤ) := by omega
  set Cst := Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d with hCstdef
  have hC : 0 ≤ Cst :=
    Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst_nonneg d
  set K := akhcWNSq_gradConst E (m : ℤ) k (1 / 2) ((gamma + 1) / 4) gamma Cst p q p0 with hKdef
  have hK : 0 ≤ K := akhcWNSq_gradConst_nonneg (by norm_num) hs'high.le hC p q p0
  set W := akhcWNSq_W gamma (m : ℤ) k with hWdef
  have hW : 1 ≤ W := akhcWNSq_one_le_W hgamma0 _ _
  have hH0 : 0 < H * (m : ℝ) ^ D :=
    mul_pos (by linarith only [hH]) (Real.rpow_pos_of_pos (by exact_mod_cast hm) D)
  have hXsq : Integrable (fun omega => (W * X omega) ^ 2) P.toMeasure :=
    SuperdiffusionCLT.AKHC61.Tails.akhcMM_integrable_sq_of_isBigO hKPsiS hPsiSOne
      (SuperdiffusionCLT.AKHC61.Tails.akhcMM_growth_ext hpPsiS hGrowth)
      (p := min 3 pPsiS) (lt_min (by norm_num) hpPsiS) (min_le_right _ _) hH0 hXm hXbig W
  have hg : Integrable (fun omega => 8 * K ^ 2 * (1 + (W * X omega) ^ 2)) P.toMeasure :=
    ((integrable_const (1 : ℝ)).add hXsq).const_mul _
  have hP := restrictionLawCarrier_cutoffLaw hnu L P
  have hfm : AEStronglyMeasurable
      (fun a : RegCoeffField d =>
        (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (originCube d (m : ℤ)) (1 / 2 : ℝ) p q p0 a.toFun) ^ 2)
      (Measure.map (fun omega : ShellSeq d => coefficientCutoff nu omega L) P.toMeasure) :=
    ((hP.aemeasurable_canonicalScalarResponseGradientWeakNorm_cubeSet
      (originCube d (m : ℤ)) (1 / 2 : ℝ) p q p0).pow_const 2).aestronglyMeasurable
  have hφ := (measurable_coefficientCutoff (d := d) nu L).aemeasurable (μ := P.toMeasure)
  rw [cutoffLaw, integrable_map_measure hfm hφ]
  refine hg.mono' (hfm.comp_aemeasurable hφ) (Filter.Eventually.of_forall fun omega => ?_)
  set a := coefficientCutoff nu omega L with hadef
  have ha := aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L
  obtain ⟨hBdd, hMX⟩ := hX omega
  have hw := Ch05.Section53.WeakNormsMaximizer.weakNormsMaximizerGradient_homogenizationScale
    a ha hkm (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hs'low hs'high p q p0
  have hr := akhcWNSq_gradientRHSAtScale_le hE ha
    (fun R => isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega L R)
    (fun R Z => zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega L R Z)
    (k := k) hs'0 hs'high hgap hgamma0 hC hBdd p q p0
  have hWM : W * akhcWeakC_eventMoreprotoPlus ((m : ℕ) : ℤ) gamma E a.toFun ≤ W * |X omega| :=
    mul_le_mul_of_nonneg_left hMX (by linarith only [hW])
  have h0 := akhcWNSq_gradientWeakNorm_nonneg (originCube d (m : ℤ)) (1 / 2 : ℝ) p q p0 a.toFun
  have hle : Ch04.canonicalScalarResponseGradientWeakNormCubeSet
      (originCube d (m : ℤ)) (1 / 2 : ℝ) p q p0 a.toFun ≤ 2 * K * (1 + W * |X omega|) := by
    have hKW := mul_le_mul_of_nonneg_left (add_le_add_left hWM 1) hK
    nlinarith only [hw, hr, hKW]
  have hsq := pow_le_pow_left₀ h0 hle 2
  have hfin : (2 * K * (1 + W * |X omega|)) ^ 2 ≤ 8 * K ^ 2 * (1 + (W * X omega) ^ 2) := by
    have := akhcWNSq_sq_bound (K := K) (W := W) (x := |X omega|)
    rwa [mul_pow W |X omega|, sq_abs, ← mul_pow] at this
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq.trans hfin

/-- **`hFluxSq` at the cutoff law.** For `m ≥ max(m₂, 1)` and any `p, q, q0`, the squared flux
weak norm at `t = ½` is integrable under `cutoffLaw ν L P`. -/
theorem akhcWNSq_integrable_fluxWeakNorm_sq {m : ℕ} (hm2 : m2 ≤ m) (hm : 0 < m)
    (p q q0 : Vec d) :
    Integrable
      (fun a : RegCoeffField d =>
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (originCube d (m : ℤ)) (1 / 2 : ℝ) p q q0 a.toFun) ^ 2)
      (cutoffLaw (d := d) nu L P) := by
  obtain ⟨X, hXm, hXbig, hX⟩ := akhcWNSq_eventBound hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hm2 hm
  obtain ⟨hs'0, hs'low, hs'high, hgap⟩ := akhcWNSq_exponents hgamma0 hgamma1
  set E := annealedBlockMatrix nu L P (cubeSet (originCube d ((m : ℕ) : ℤ))) with hEdef
  have hE : (toFullBlockMat E).PosDef :=
    akhcWNSq_annealed_posDef hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 _
  set k : ℤ := (m : ℤ) - 1 with hkdef
  have hkm : k < (m : ℤ) := by omega
  set Cst := Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst d with hCstdef
  have hC : 0 ≤ Cst :=
    Ch05.Section53.WeakNormsMaximizer.section53WeakNormMaximizerConst_nonneg d
  set K := akhcWNSq_fluxConst E (m : ℤ) k (1 / 2) ((gamma + 1) / 4) gamma Cst p q q0 with hKdef
  have hK : 0 ≤ K := akhcWNSq_fluxConst_nonneg (by norm_num) hs'high.le hC p q q0
  set W := akhcWNSq_W gamma (m : ℤ) k with hWdef
  have hW : 1 ≤ W := akhcWNSq_one_le_W hgamma0 _ _
  have hH0 : 0 < H * (m : ℝ) ^ D :=
    mul_pos (by linarith only [hH]) (Real.rpow_pos_of_pos (by exact_mod_cast hm) D)
  have hXsq : Integrable (fun omega => (W * X omega) ^ 2) P.toMeasure :=
    SuperdiffusionCLT.AKHC61.Tails.akhcMM_integrable_sq_of_isBigO hKPsiS hPsiSOne
      (SuperdiffusionCLT.AKHC61.Tails.akhcMM_growth_ext hpPsiS hGrowth)
      (p := min 3 pPsiS) (lt_min (by norm_num) hpPsiS) (min_le_right _ _) hH0 hXm hXbig W
  have hg : Integrable (fun omega => 8 * K ^ 2 * (1 + (W * X omega) ^ 2)) P.toMeasure :=
    ((integrable_const (1 : ℝ)).add hXsq).const_mul _
  have hP := restrictionLawCarrier_cutoffLaw hnu L P
  have hfm : AEStronglyMeasurable
      (fun a : RegCoeffField d =>
        (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (originCube d (m : ℤ)) (1 / 2 : ℝ) p q q0 a.toFun) ^ 2)
      (Measure.map (fun omega : ShellSeq d => coefficientCutoff nu omega L) P.toMeasure) :=
    ((hP.aemeasurable_canonicalScalarResponseFluxWeakNorm_cubeSet
      (originCube d (m : ℤ)) (1 / 2 : ℝ) p q q0).pow_const 2).aestronglyMeasurable
  have hφ := (measurable_coefficientCutoff (d := d) nu L).aemeasurable (μ := P.toMeasure)
  rw [cutoffLaw, integrable_map_measure hfm hφ]
  refine hg.mono' (hfm.comp_aemeasurable hφ) (Filter.Eventually.of_forall fun omega => ?_)
  set a := coefficientCutoff nu omega L with hadef
  have ha := aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L
  obtain ⟨hBdd, hMX⟩ := hX omega
  have hw := Ch05.Section53.WeakNormsMaximizer.weakNormsMaximizerFlux_homogenizationScale
    a ha hkm (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hs'low hs'high p q q0
  have hr := akhcWNSq_fluxRHSAtScale_le hE ha
    (fun R => isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega L R)
    (fun R Z => zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega L R Z)
    (k := k) hs'0 hs'high hgap hgamma0 hC hBdd p q q0
  have hWM : W * akhcWeakC_eventMoreprotoPlus ((m : ℕ) : ℤ) gamma E a.toFun ≤ W * |X omega| :=
    mul_le_mul_of_nonneg_left hMX (by linarith only [hW])
  have h0 := akhcWNSq_fluxWeakNorm_nonneg (originCube d (m : ℤ)) (1 / 2 : ℝ) p q q0 a.toFun
  have hle : Ch04.canonicalScalarResponseFluxWeakNormCubeSet
      (originCube d (m : ℤ)) (1 / 2 : ℝ) p q q0 a.toFun ≤ 2 * K * (1 + W * |X omega|) := by
    have hKW := mul_le_mul_of_nonneg_left (add_le_add_left hWM 1) hK
    nlinarith only [hw, hr, hKW]
  have hsq := pow_le_pow_left₀ h0 hle 2
  have hfin : (2 * K * (1 + W * |X omega|)) ^ 2 ≤ 8 * K ^ 2 * (1 + (W * X omega) ^ 2) := by
    have := akhcWNSq_sq_bound (K := K) (W := W) (x := |X omega|)
    rwa [mul_pow W |X omega|, sq_abs, ← mul_pow] at this
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq.trans hfin

end

end SuperdiffusionCLT.AKHC61.WeakNorms
