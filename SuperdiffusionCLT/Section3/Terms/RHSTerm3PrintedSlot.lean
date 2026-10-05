/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlowupLocal

/-!
# Term three with the printed operator slot

The operator slot is dominated by the sum of its coordinate quadratic forms.
Directional moment estimates are summed before the final constant is chosen;
the response regularity amplitude is unchanged on unit coordinate directions.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open scoped BigOperators ENNReal

/-- The weighted integral of the printed-scale comparison splits into its
constant, quadratic, replacement, centered, and remainder terms. -/
theorem rhsTerm3PrintedSlot_integral_split {d : ℕ} [NeZero d] {nu : ℝ}
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hnk : S.n ≤ coarseBlockScale d S) (hkm : coarseBlockScale d S ≤ S.m)
    (g : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d → Homogenization.Vec d)
    (Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.TriadicCube d → ℝ)
    (hpre : ∀ ω R, R.scale = (S.n : ℤ) → translatedBlockNorm nu S.LPrime ω R ≤
      2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) +
        2 * (translatedStreamBasisSum nu S.ell S.LPrime ω R +
          translatedStreamBasisGapSum nu S.ell S.LPrime ω R) +
        2 * translatedBlockDevSumSigned nu S.ell S.n P ω R + Z ω R)
    (hB : MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (g ω) (translatedBlockNorm nu S.LPrime ω)) P.toMeasure)
    (h1 : MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (g ω) (fun _ => 1)) P.toMeasure)
    (hQ : ∀ i : Fin d, MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (g ω) (translatedStreamQuadForm nu S.ell S.LPrime (Homogenization.basisVec i) ω)) P.toMeasure)
    (hG : ∀ i : Fin d, MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (g ω) (translatedStreamQuadFormGap nu S.ell S.LPrime (Homogenization.basisVec i) ω)) P.toMeasure)
    (hD : MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (g ω) (translatedBlockDevSumSigned nu S.ell S.n P ω)) P.toMeasure)
    (hZ : MeasureTheory.Integrable (fun ω => weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (g ω) (Z ω)) P.toMeasure) :
    (∫ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m
      (g ω) (translatedBlockNorm nu S.LPrime ω) ∂P.toMeasure) ≤
      2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) *
        (∫ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m (g ω) (fun _ => 1) ∂P.toMeasure) +
      2 * (∑ i : Fin d, ∫ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        (g ω) (translatedStreamQuadForm nu S.ell S.LPrime (Homogenization.basisVec i) ω) ∂P.toMeasure) +
      2 * (∑ i : Fin d, ∫ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        (g ω) (translatedStreamQuadFormGap nu S.ell S.LPrime (Homogenization.basisVec i) ω) ∂P.toMeasure) +
      2 * (∫ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        (g ω) (translatedBlockDevSumSigned nu S.ell S.n P ω) ∂P.toMeasure) +
      (∫ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m (g ω) (Z ω) ∂P.toMeasure) := by
  classical
  have h := fun ω => rhsTerm3BlowupLocal_weighted_mono_at_scale hnk hkm (g ω) (hpre ω)
  simp only [weightedBlockAverage_add] at h
  have hc : ∀ ω, weightedBlockAverage d S.n (coarseBlockScale d S) S.m (g ω)
      (fun _ => 2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n)) =
      2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n) *
        weightedBlockAverage d S.n (coarseBlockScale d S) S.m (g ω) (fun _ => 1) := by
    intro ω
    simpa only [mul_one] using weightedBlockAverage_const_mul (n := S.n) (k := coarseBlockScale d S) (m := S.m)
      (g ω) (2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n)) (fun _ => (1 : ℝ))
  simp only [hc, weightedBlockAverage_add, weightedBlockAverage_const_mul, translatedStreamBasisSum,
    translatedStreamBasisGapSum, weightedBlockAverage_univ_sum] at h
  have hQi := MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hQ i)
  have hGi := MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hG i)
  have hi := (((h1.const_mul (2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n))).add ((hQi.add hGi).const_mul 2)).add (hD.const_mul 2)).add hZ
  have hle := MeasureTheory.integral_mono hB hi (fun ω => h ω)
  simp only [Pi.add_apply] at hle
  have h01 := h1.const_mul (2 * ((d : ℝ) * SuperdiffusionCLT.Section2.Annealed.sigmaBarSeq nu S.ell P S.n))
  have h23 := (hQi.add hGi).const_mul 2
  have hdd := hD.const_mul 2
  have heq0 := MeasureTheory.integral_add ((h01.add h23).add hdd) hZ
  have heq1 := MeasureTheory.integral_add (h01.add h23) hdd
  have heq2 := MeasureTheory.integral_add h01 h23
  have heq3 := MeasureTheory.integral_add hQi hGi
  simp only [Pi.add_apply] at heq0 heq1 heq2 heq3
  rw [heq0, heq1, heq2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, heq3,
    MeasureTheory.integral_finsetSum _ (fun i _ => hQ i),
    MeasureTheory.integral_finsetSum _ (fun i _ => hG i)] at hle
  linarith only [hle]

/-- Finiteness of the response second moment from its regularity bound. -/
theorem rhsTerm3PrintedSlot_gradTwo_finite {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)} (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection) (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    {e : Homogenization.Vec d} (he : Homogenization.vecNormSq e = 1)
    {p : Homogenization.Vec d} (hp : p = SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    {C : ℝ} (hC : 1 ≤ C) {Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} (hZmeas : Measurable Z)
    (hZbigO : Homogenization.IndependentSums.IsBigO P.toMeasure (Homogenization.IndependentSums.gammaSigma 2) Z
      (C * (Real.sqrt (Homogenization.vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))))
    (hZbound : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad ≤
        ENNReal.ofReal (Z omega)) :
    (∫⁻ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
        (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤ := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC
  have hh1 : 1 ≤ S.h := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := S.ellPrime_add_h
    omega
  have hhR : (0 : ℝ) < (S.h : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hh1
  have hpn : (0 : ℝ) < Homogenization.vecNormSq p := by
    rw [hp, SuperdiffusionCLT.Section3.Setup.vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he]
    exact SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hhalf : (0 : ℝ) < (S.h : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hhR _
  have hA : (0 : ℝ) < C * (Real.sqrt (Homogenization.vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2)) :=
    mul_pos hC0 (mul_pos (Real.sqrt_pos.2 hpn) hhalf)
  have hptr : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by
    intro omega
    have hdown : SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2
        (w omega).toH1Function.grad ≤
        SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 8 (w omega).toH1Function.grad :=
      vecCubeLpENorm_mono_exponent (Homogenization.originCube d (S.m : ℤ)) (by norm_num)
        (aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
          (w omega).toH1Function.grad_memVectorL2)
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ)
        ≤ (ENNReal.ofReal |Z omega|) ^ (2 : ℕ) :=
          pow_le_pow_left' (le_trans (le_trans hdown (hZbound omega)) habs) 2
      _ = ENNReal.ofReal (|Z omega| ^ (2 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
      _ = ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by
          rw [Real.rpow_natCast]
  have hint : MeasureTheory.Integrable
      (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d => |Z omega| ^ (((2 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hA hZmeas.aemeasurable hZbigO 2
  have hle : (∫⁻ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure) ≤
      ENNReal.ofReal
        (∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, |Z omega| ^ (((2 : ℕ) : ℝ)) ∂P.toMeasure) := by
    calc (∫⁻ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
        (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2
          (w omega).toH1Function.grad) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
            ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) ∂P.toMeasure :=
          MeasureTheory.lintegral_mono hptr
      _ = ENNReal.ofReal
            (∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, |Z omega| ^ (((2 : ℕ) : ℝ)) ∂P.toMeasure) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun omega =>
              Real.rpow_nonneg (abs_nonneg _) _)).symm
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end SuperdiffusionCLT.Section3.Terms
