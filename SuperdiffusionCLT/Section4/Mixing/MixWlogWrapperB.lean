/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.WlogTranslate
public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssemblyF
public import SuperdiffusionCLT.Section3.HighContrast.BEllParameters

/-!
# The single-split wrapper for `hSmallGapD`, with the base case restricted to `n ≤ L`

`mixWlog_smallGapFromBaseB` reduces the small-gap clause to a base case `hBase`, with two features.

* The base case `hBase` is only required for `n ≤ L`. The clause `L < n` of the small-gap
  statement is proved directly from the large-gap estimate above scale `L`
  (`mixWlogB_above`), using the standing hypothesis `n ≤ m - ⌈C log(ν⁻¹n)⌉`. This is needed
  because `hBase`'s window `10 K₀ log(ν⁻¹L) ≤ m - n` carries no information about `log(ν⁻¹n)`
  when `L < n`.
* The returned threshold also dominates the threshold of `mixWlogB_above`.

The argument is a single split: the internal scale
`mtilde = n + ⌈10 K₀ log(ν⁻¹L)⌉` depends only on `K₀, ν, L`, `hBase` is invoked once at
`(n, mtilde)` with the rescaled constant `Cin = C / M`, and the three pieces are reassembled
over the sub-cubes with `mixFin_wlogTranslate` and `mixMain_wlogInductionStep`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)
open SuperdiffusionCLT.Section3.Terms (translateObservable measurable_translateObservable
  isBigO_gammaSigma_translateObservable)

noncomputable section

variable {d : ℕ}

/-- **The single-split wrapper**: from the bounded-gap base case `hBase` (for `n ≤ L`) to the
full small-gap clause `hSmallGapD` of `mixMain_mainB`. -/
theorem mixWlog_smallGapFromBaseB (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hBase :
      ∃ K0 C0base : ℝ, 1 ≤ K0 ∧ 1 ≤ C0base ∧
        ∀ C : ℝ, C0base ≤ C →
          ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
            ∀ (P : ProbabilityMeasure (ShellSeq d)),
              ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
              ShellLawJ4 d P →
                ∀ n L : ℕ, 1 ≤ L → 1 ≤ n → n ≤ L →
                  (L : ℝ) - (n : ℝ) ≤
                    C⁻¹ * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (2 : ℝ) →
                  ∀ mb : ℕ, n ≤ mb →
                    (10 * K0 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((mb - n : ℕ) : ℝ)) →
                    (((mb - n : ℕ) : ℝ) ≤ 20 * K0 * (1 + Real.log (nu⁻¹ * (L : ℝ)))) →
                    ∃ F1 F2 F3 : TriadicCube d → ShellSeq d → BlockVec d → BlockVec d → ℝ,
                      (∀ R omega p q, F1 R omega p q + F2 R omega p q + F3 R omega p q =
                        blockVecDot p (blockMatVecMul (ofFullBlockMat
                          (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                                (coefficientCutoff nu omega L).toCoeffField) -
                            toFullBlockMat
                              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))))) q)) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F1 (translateCube w Q) omega p q =
                              F1 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F2 (translateCube w Q) omega p q =
                              F2 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F3 (translateCube w Q) omega p q =
                              F3 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (L ≤ n → ∀ R omega p q, F1 R omega p q = 0) ∧
                      (L ≤ n → ∀ R omega p q, F2 R omega p q = 0) ∧
                      ∃ X1 X2 X3 : ShellSeq d → ℝ,
                        Measurable X1 ∧
                          IsBigO P.toMeasure (gammaSigma 2) X1
                            (C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                                (-(1 : ℝ))) ∧
                        Measurable X2 ∧
                          IsBigO P.toMeasure (gammaSigma 1) X2
                            (C * ((L - n : ℕ) : ℝ) *
                              (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                                (-(2 : ℝ))) ∧
                        Measurable X3 ∧
                          IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3
                            (C * (mb : ℝ) ^ (-(3000 : ℝ))) ∧
                          ∀ (omega : ShellSeq d) (p q : BlockVec d),
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F1 R' omega p q) ≤
                              X1 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) ∧
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F2 R' omega p q) ≤
                              X2 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) ∧
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F3 R' omega p q) ≤
                              X3 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q))) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ C : ℝ, C0 ≤ C →
        ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
          ∀ (P : ProbabilityMeasure (ShellSeq d)),
            ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
              ∀ m n L : ℕ, 1 ≤ L →
                (L : ℝ) - (n : ℝ) ≤
                  C⁻¹ * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (2 : ℝ) →
                m < 2 * n →
                (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ →
                ⌈C * Real.log (nu⁻¹ * (L : ℝ))⌉ ≤ (n : ℤ) →
                (n : ℤ) ≤ (m : ℤ) - ⌈C * Real.log (nu⁻¹ * (n : ℝ))⌉ →
                ((m : ℝ) ≤ (L : ℝ) + C * Real.log (nu⁻¹ * (L : ℝ)) →
                  ∃ X1 X2 X3 : ShellSeq d → ℝ,
                    Measurable X1 ∧
                    IsBigO P.toMeasure (gammaSigma 2) X1
                        (C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                            (-(1 : ℝ))) ∧
                    Measurable X2 ∧
                    IsBigO P.toMeasure (gammaSigma 1) X2
                        (C * ((L - n : ℕ) : ℝ) *
                          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                            (-(2 : ℝ))) ∧
                    Measurable X3 ∧
                    IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3
                        (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
                      ∀ (omega : ShellSeq d) (p q : BlockVec d),
                        2 *
                            (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                              ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                                blockVecDot p
                                  (blockMatVecMul
                                    (ofFullBlockMat
                                      (toFullBlockMat
                                          (coarseBlockMatrix (cubeSet R)
                                            (coefficientCutoff nu omega L).toCoeffField) -
                                        toFullBlockMat
                                          (annealedBlockMatrix nu L P
                                            (cubeSet (originCube d (n : ℤ))))))
                                    q)) ≤
                          (X1 omega + X2 omega + X3 omega) *
                            (blockVecDot p
                                (blockMatVecMul
                                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                  p) +
                              blockVecDot q
                                (blockMatVecMul
                                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                  q))) := by
  obtain ⟨K0, C0base, hK01, hC0base1, hBase⟩ := hBase
  obtain ⟨CA, hCA1, hAbove⟩ := mixWlogB_above d hd
  have hgt2 : (0:ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hgt1 : (0:ℝ) < gammaTriangleConst 1 := gammaTriangleConst_pos
  have hgt13 : (0:ℝ) < gammaTriangleConst ((1:ℝ)/3) := gammaTriangleConst_pos
  have h2pow_pos : (0:ℝ) < (2:ℝ) ^ (3000:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  set M : ℝ := max 1 (gammaTriangleConst 2 + gammaTriangleConst 1 +
      gammaTriangleConst ((1:ℝ)/3) * (2:ℝ) ^ (3000:ℝ)) with hMdef
  have hM1 : (1:ℝ) ≤ M := le_max_left _ _
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hprod13_pos : (0:ℝ) < gammaTriangleConst ((1:ℝ)/3) * (2:ℝ) ^ (3000:ℝ) :=
    mul_pos hgt13 h2pow_pos
  have hMge2 : gammaTriangleConst 2 ≤ M :=
    le_trans (by linarith only [hgt1, hprod13_pos]) (le_max_right (1:ℝ) _)
  have hMge1 : gammaTriangleConst 1 ≤ M :=
    le_trans (by linarith only [hgt2, hprod13_pos]) (le_max_right (1:ℝ) _)
  have hMge13 : gammaTriangleConst ((1:ℝ)/3) * (2:ℝ) ^ (3000:ℝ) ≤ M :=
    le_trans (by linarith only [hgt2, hgt1]) (le_max_right (1:ℝ) _)
  have hC0_1 : (1:ℝ) ≤ max (max (M * C0base) (10 * K0)) CA := le_trans hCA1 (le_max_right _ _)
  refine ⟨max (max (M * C0base) (10 * K0)) CA, hC0_1, ?_⟩
  intro C hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n L hL1 hLnR hmn2n hgapMn hgapLn hgapNn hcase
  have hCM : M * C0base ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC10K0 : 10 * K0 ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hCA : CA ≤ C := le_trans (le_max_right _ _) hC
  have hC1 : (1:ℝ) ≤ C := le_trans hC0_1 hC
  have hCpos : (0:ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hlogL_nn : (0:ℝ) ≤ Real.log (nu⁻¹ * (L:ℝ)) := by
    have hnuinv1 : (1:ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hLcast : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL1
    refine Real.log_nonneg ?_
    calc (1:ℝ) = 1*1 := by ring
      _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
  -- basic scale facts
  have hmn : n ≤ m := by
    have hceil_nn : (0:ℤ) ≤ ⌈C * Real.log (nu⁻¹ * (L:ℝ))⌉ := by
      have : (0:ℝ) ≤ C * Real.log (nu⁻¹ * (L:ℝ)) := mul_nonneg hCpos.le hlogL_nn
      exact_mod_cast Int.ceil_nonneg this
    omega
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  by_cases hLnlt : L < n
  · exact hAbove C hCA nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n L hL1 hLnlt hgapNn
  have hnL : n ≤ L := not_lt.1 hLnlt
  -- the internal splitting scale mtilde
  set qZ : ℤ := ⌈10 * K0 * Real.log (nu⁻¹ * (L:ℝ))⌉ with hqZdef
  have hqZnn : (0:ℤ) ≤ qZ := by
    have h10K0nn : (0:ℝ) ≤ 10 * K0 := by linarith only [hK01]
    exact Int.ceil_nonneg (mul_nonneg h10K0nn hlogL_nn)
  set q : ℕ := qZ.toNat with hqdef
  have hqcast : (q:ℤ) = qZ := Int.toNat_of_nonneg hqZnn
  set mtilde : ℕ := n + q with hmtildedef
  have hntilde : n ≤ mtilde := Nat.le_add_right _ _
  have hmtsub : mtilde - n = q := by omega
  have hqR_lb : 10 * K0 * Real.log (nu⁻¹ * (L:ℝ)) ≤ (q:ℝ) := by
    have := Int.le_ceil (10 * K0 * Real.log (nu⁻¹ * (L:ℝ)))
    rw [← hqZdef] at this
    have hcast : (qZ:ℝ) = (q:ℝ) := by exact_mod_cast hqcast.symm
    linarith only [this, hcast.le, hcast.ge]
  have hqR_ub : (q:ℝ) ≤ 20 * K0 * (1 + Real.log (nu⁻¹ * (L:ℝ))) := by
    have hlt := Int.ceil_lt_add_one (10 * K0 * Real.log (nu⁻¹ * (L:ℝ)))
    rw [← hqZdef] at hlt
    have hcast : (qZ:ℝ) = (q:ℝ) := by exact_mod_cast hqcast.symm
    nlinarith only [hlt, hcast.le, hcast.ge, hK01]
  have hwindow1 : 10 * K0 * Real.log (nu⁻¹ * (L:ℝ)) ≤ ((mtilde - n : ℕ):ℝ) := by
    rw [hmtsub]; exact hqR_lb
  have hwindow2 : ((mtilde - n : ℕ):ℝ) ≤ 20 * K0 * (1 + Real.log (nu⁻¹ * (L:ℝ))) := by
    rw [hmtsub]; exact hqR_ub
  have hmtildem : mtilde ≤ m := by
    have hCge : 10 * K0 * Real.log (nu⁻¹ * (L:ℝ)) ≤ C * Real.log (nu⁻¹ * (L:ℝ)) :=
      mul_le_mul_of_nonneg_right hC10K0 hlogL_nn
    have hceilmono : qZ ≤ ⌈C * Real.log (nu⁻¹ * (L:ℝ))⌉ := Int.ceil_mono hCge
    have hZ : ⌈C * Real.log (nu⁻¹ * (L:ℝ))⌉ ≤ (m:ℤ) - (n:ℤ) := by linarith only [hgapMn]
    have : qZ ≤ (m:ℤ) - (n:ℤ) := le_trans hceilmono hZ
    have hqle : (q:ℤ) ≤ (m:ℤ) - (n:ℤ) := hqcast ▸ this
    omega
  have hm2mtilde : m < 2 * mtilde := lt_of_lt_of_le hmn2n (by omega)
  -- Cin, the rescaled constant fed to hBase
  set Cin : ℝ := C / M with hCindef
  have hCinpos : (0:ℝ) < Cin := div_pos hCpos hMpos
  have hCinC0base : C0base ≤ Cin := by
    rw [hCindef, le_div_iff₀ hMpos]
    linarith only [hCM]
  have hCinv : Cin⁻¹ = M * C⁻¹ := by rw [hCindef, inv_div, div_eq_mul_inv]
  have hLnRcin : (L:ℝ) - (n:ℝ) ≤
      Cin⁻¹ * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (2:ℝ) := by
    have hsigmapos : (0:ℝ) < sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ))) :=
      SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L hPrefix hJ2 hJ3 hJ4 (n:ℤ)
    have hsq_nn : (0:ℝ) ≤ (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (2:ℝ) :=
      Real.rpow_nonneg hsigmapos.le _
    rw [hCinv]
    nlinarith only [hLnR, hM1, hsq_nn, mul_nonneg (inv_nonneg.2 hCpos.le) hsq_nn]
  -- invoke the base case at the bounded scale mtilde
  obtain ⟨F1, F2, F3, hFsum, hFcov1, hFcov2, hFcov3, hZero1, hZero2,
      X1_0, X2_0, X3_0, hX1_0M, hX1_0O, hX2_0M, hX2_0O, hX3_0M, hX3_0O, hbase_bound⟩ :=
    hBase Cin hCinC0base nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 n L hL1 hn1 hnL hLnRcin
      mtilde hntilde hwindow1 hwindow2
  have hbound1 : ∀ omega p q, 2 * descendantsAverage (originCube d (mtilde:ℤ)) (mtilde - n)
      (fun R' => F1 R' omega p q) ≤
        X1_0 omega * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) q)) :=
    fun omega p q => (hbase_bound omega p q).1
  have hbound2 : ∀ omega p q, 2 * descendantsAverage (originCube d (mtilde:ℤ)) (mtilde - n)
      (fun R' => F2 R' omega p q) ≤
        X2_0 omega * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) q)) :=
    fun omega p q => (hbase_bound omega p q).2.1
  have hbound3 : ∀ omega p q, 2 * descendantsAverage (originCube d (mtilde:ℤ)) (mtilde - n)
      (fun R' => F3 R' omega p q) ≤
        X3_0 omega * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) q)) :=
    fun omega p q => (hbase_bound omega p q).2.2
  set G3 : BlockVec d → BlockVec d → ℝ := fun p q =>
      blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) p) +
        blockVecDot q (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))) q)
    with hG3def
  -- X3: reassemble the localization/gauge-leftover Gamma_{1/3} witness
  have hmtildepos : 1 ≤ mtilde := le_trans hn1 hntilde
  have hmtildeR_pos : (0:ℝ) < (mtilde:ℝ) := by exact_mod_cast hmtildepos
  have ha3pos : (0:ℝ) < Cin * (mtilde:ℝ) ^ (-(3000:ℝ)) :=
    mul_pos hCinpos (Real.rpow_pos_of_pos hmtildeR_pos _)
  obtain ⟨hX3RM, hX3RO, hbound3R⟩ :=
    mixFin_wlogTranslate (d := d) (P := P) hPrefix hJ2 (n := n) (mtilde := mtilde) (m := m)
      hntilde hmtildem (G := G3) (a := Cin * (mtilde:ℝ) ^ (-(3000:ℝ))) (σ := (1:ℝ)/3)
      (F := F3) hFcov3 hX3_0M hX3_0O hbound3
  obtain ⟨X3', hX3'M, hX3'O, hX3'bd⟩ :=
    mixMain_wlogInductionStep (d := d) (Ω := ShellSeq d) (μ := P.toMeasure)
      (n := n) (mtilde := mtilde) (m := m) hntilde hmtildem (G := G3)
      (a := Cin * (mtilde:ℝ) ^ (-(3000:ℝ))) (σ := (1:ℝ)/3) (by norm_num) ha3pos
      (F := F3) (X := fun R => translateObservable X3_0 R) hX3RM hX3RO hbound3R
  have hmtilde_rpow_le : (mtilde:ℝ) ^ (-(3000:ℝ)) ≤ (2:ℝ) ^ (3000:ℝ) * (m:ℝ) ^ (-(3000:ℝ)) :=
    mixMain_wlogAuxScale_rpow_le (m := m) (mtilde := mtilde) (p := 3000) (by norm_num) hm1 hm2mtilde
  have hmR_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hmpow_nn : (0:ℝ) ≤ (m:ℝ) ^ (-(3000:ℝ)) := (Real.rpow_pos_of_pos hmR_pos _).le
  have hX3amp : gammaTriangleConst ((1:ℝ)/3) * (Cin * (mtilde:ℝ) ^ (-(3000:ℝ))) ≤
      C * (m:ℝ) ^ (-(3000:ℝ)) := by
    have hstep1 : Cin * (mtilde:ℝ) ^ (-(3000:ℝ)) ≤ Cin * ((2:ℝ) ^ (3000:ℝ) * (m:ℝ) ^ (-(3000:ℝ))) :=
      mul_le_mul_of_nonneg_left hmtilde_rpow_le hCinpos.le
    have hstep2 : gammaTriangleConst ((1:ℝ)/3) * (Cin * ((2:ℝ) ^ (3000:ℝ) * (m:ℝ) ^ (-(3000:ℝ)))) =
        (gammaTriangleConst ((1:ℝ)/3) * (2:ℝ) ^ (3000:ℝ)) * (Cin * (m:ℝ) ^ (-(3000:ℝ))) := by ring
    have hstep3 : (gammaTriangleConst ((1:ℝ)/3) * (2:ℝ) ^ (3000:ℝ)) * (Cin * (m:ℝ) ^ (-(3000:ℝ))) ≤
        M * (Cin * (m:ℝ) ^ (-(3000:ℝ))) :=
      mul_le_mul_of_nonneg_right hMge13 (mul_nonneg hCinpos.le hmpow_nn)
    have hstep4 : M * (Cin * (m:ℝ) ^ (-(3000:ℝ))) = C * (m:ℝ) ^ (-(3000:ℝ)) := by
      rw [hCindef]; field_simp
    have hmul1 : gammaTriangleConst ((1:ℝ)/3) * (Cin * (mtilde:ℝ) ^ (-(3000:ℝ))) ≤
        gammaTriangleConst ((1:ℝ)/3) * (Cin * ((2:ℝ) ^ (3000:ℝ) * (m:ℝ) ^ (-(3000:ℝ)))) :=
      mul_le_mul_of_nonneg_left hstep1 hgt13.le
    calc gammaTriangleConst ((1:ℝ)/3) * (Cin * (mtilde:ℝ) ^ (-(3000:ℝ)))
        ≤ gammaTriangleConst ((1:ℝ)/3) * (Cin * ((2:ℝ) ^ (3000:ℝ) * (m:ℝ) ^ (-(3000:ℝ)))) := hmul1
      _ = (gammaTriangleConst ((1:ℝ)/3) * (2:ℝ) ^ (3000:ℝ)) * (Cin * (m:ℝ) ^ (-(3000:ℝ))) := hstep2
      _ ≤ M * (Cin * (m:ℝ) ^ (-(3000:ℝ))) := hstep3
      _ = C * (m:ℝ) ^ (-(3000:ℝ)) := hstep4
  have hX3finO : IsBigO P.toMeasure (gammaSigma ((1:ℝ)/3)) X3' (C * (m:ℝ) ^ (-(3000:ℝ))) :=
    hX3'O.mono_scale hX3amp
  have hFinalGoalEq : ∀ omega p q,
      2 * (((descendantsAtDepth (originCube d (m:ℤ)) (m - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (m:ℤ)) (m - n),
              blockVecDot p (blockMatVecMul (ofFullBlockMat
                  (toFullBlockMat (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
                    toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))))) q)) =
      2 * descendantsAverage (originCube d (m:ℤ)) (m - n)
          (fun R' => F1 R' omega p q + F2 R' omega p q + F3 R' omega p q) := by
    intro omega p q
    have hcongr : (fun R => blockVecDot p (blockMatVecMul (ofFullBlockMat
          (toFullBlockMat (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
            toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))))) q)) =
        (fun R => F1 R omega p q + F2 R omega p q + F3 R omega p q) := by
      funext R; exact (hFsum R omega p q).symm
    show 2 * (((descendantsAtDepth (originCube d (m:ℤ)) (m - n)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (m:ℤ)) (m - n),
          (fun R => blockVecDot p (blockMatVecMul (ofFullBlockMat
              (toFullBlockMat (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
                toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d (n:ℤ)))))) q)) R) =
      2 * descendantsAverage (originCube d (m:ℤ)) (m - n)
          (fun R' => F1 R' omega p q + F2 R' omega p q + F3 R' omega p q)
    rw [hcongr]
    rfl
  by_cases hLn : L ≤ n
  · -- degenerate branch: (L-n:ℕ) = 0, so X1, X2 amplitudes vanish and X1 = X2 = 0 suffice.
    have hLnzero : ((L - n : ℕ):ℝ) = 0 := by
      have hz : L - n = 0 := Nat.sub_eq_zero_of_le hLn
      exact_mod_cast hz
    have hamp1zero : C * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
        (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ)) = 0 := by
      rw [hLnzero, Real.zero_rpow (by norm_num)]; ring
    have hamp2zero : C * ((L - n : ℕ):ℝ) *
        (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ)) = 0 := by
      rw [hLnzero]; ring
    have hzeroBigO2 : IsBigO P.toMeasure (gammaSigma 2) (fun _ : ShellSeq d => (0:ℝ)) 0 := by
      intro t ht
      have hempty : upperTailEvent (fun _ : ShellSeq d => |(0:ℝ)|) (0 * t) = (∅ : Set (ShellSeq d)) := by
        ext omega; simp [upperTailEvent]
      show P.toMeasure.real (upperTailEvent (fun _ : ShellSeq d => |(0:ℝ)|) (0 * t)) ≤ (gammaSigma 2 t)⁻¹
      rw [hempty]
      have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one ht
      have hpsi1 : (1:ℝ) ≤ gammaSigma 2 t := IndependentSums.one_le_gammaSigma ht0
      simp only [MeasureTheory.measureReal_empty]
      positivity
    have hzeroBigO1 : IsBigO P.toMeasure (gammaSigma 1) (fun _ : ShellSeq d => (0:ℝ)) 0 := by
      intro t ht
      have hempty : upperTailEvent (fun _ : ShellSeq d => |(0:ℝ)|) (0 * t) = (∅ : Set (ShellSeq d)) := by
        ext omega; simp [upperTailEvent]
      show P.toMeasure.real (upperTailEvent (fun _ : ShellSeq d => |(0:ℝ)|) (0 * t)) ≤ (gammaSigma 1 t)⁻¹
      rw [hempty]
      have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one ht
      have hpsi1 : (1:ℝ) ≤ gammaSigma 1 t := IndependentSums.one_le_gammaSigma ht0
      simp only [MeasureTheory.measureReal_empty]
      positivity
    refine ⟨fun _ => (0:ℝ), fun _ => (0:ℝ), X3', measurable_const, hamp1zero ▸ hzeroBigO2,
      measurable_const, hamp2zero ▸ hzeroBigO1, hX3'M, hX3finO, ?_⟩
    intro omega p q
    rw [hFinalGoalEq omega p q]
    have heqsum : (fun R' => F1 R' omega p q + F2 R' omega p q + F3 R' omega p q) =
        (fun R' => F3 R' omega p q) := by
      funext R'
      rw [hZero1 hLn R' omega p q, hZero2 hLn R' omega p q]
      ring
    rw [heqsum]
    show 2 * descendantsAverage (originCube d (m:ℤ)) (m - n) (fun R' => F3 R' omega p q) ≤
        ((0:ℝ) + 0 + X3' omega) * G3 p q
    have hfin := hX3'bd omega p q
    linarith only [hfin]
  · -- the genuine gauge-term branch: n < L, so (L-n:ℕ) > 0 and the amplitudes are strictly positive.
    replace hLn : n < L := not_le.1 hLn
    have hLnpos : 0 < L - n := by omega
    have hLnR_pos : (0:ℝ) < ((L - n : ℕ):ℝ) := by exact_mod_cast hLnpos
    have hsigmapos : (0:ℝ) < sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ))) :=
      SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L hPrefix hJ2 hJ3 hJ4 (n:ℤ)
    have ha1pos : (0:ℝ) < Cin * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
        (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ)) :=
      mul_pos (mul_pos hCinpos (Real.rpow_pos_of_pos hLnR_pos _)) (Real.rpow_pos_of_pos hsigmapos _)
    have ha2pos : (0:ℝ) < Cin * ((L - n : ℕ):ℝ) *
        (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ)) :=
      mul_pos (mul_pos hCinpos hLnR_pos) (Real.rpow_pos_of_pos hsigmapos _)
    obtain ⟨hX1RM, hX1RO, hbound1R⟩ :=
      mixFin_wlogTranslate (d := d) (P := P) hPrefix hJ2 (n := n) (mtilde := mtilde) (m := m)
        hntilde hmtildem (G := G3)
        (a := Cin * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ))) (σ := (2:ℝ))
        (F := F1) hFcov1 hX1_0M hX1_0O hbound1
    obtain ⟨X1', hX1'M, hX1'O, hX1'bd⟩ :=
      mixMain_wlogInductionStep (d := d) (Ω := ShellSeq d) (μ := P.toMeasure)
        (n := n) (mtilde := mtilde) (m := m) hntilde hmtildem (G := G3)
        (a := Cin * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ))) (σ := (2:ℝ))
        (by norm_num) ha1pos
        (F := F1) (X := fun R => translateObservable X1_0 R) hX1RM hX1RO hbound1R
    obtain ⟨hX2RM, hX2RO, hbound2R⟩ :=
      mixFin_wlogTranslate (d := d) (P := P) hPrefix hJ2 (n := n) (mtilde := mtilde) (m := m)
        hntilde hmtildem (G := G3)
        (a := Cin * ((L - n : ℕ):ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ))) (σ := (1:ℝ))
        (F := F2) hFcov2 hX2_0M hX2_0O hbound2
    obtain ⟨X2', hX2'M, hX2'O, hX2'bd⟩ :=
      mixMain_wlogInductionStep (d := d) (Ω := ShellSeq d) (μ := P.toMeasure)
        (n := n) (mtilde := mtilde) (m := m) hntilde hmtildem (G := G3)
        (a := Cin * ((L - n : ℕ):ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ))) (σ := (1:ℝ))
        (by norm_num) ha2pos
        (F := F2) (X := fun R => translateObservable X2_0 R) hX2RM hX2RO hbound2R
    have hX1amp : gammaTriangleConst 2 * (Cin * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ))) ≤
        C * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ)) := by
      have hrest_nn : (0:ℝ) ≤ ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ)) :=
        mul_nonneg (Real.rpow_nonneg hLnR_pos.le _) (Real.rpow_nonneg hsigmapos.le _)
      have hstep1 : gammaTriangleConst 2 * (Cin * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ))) =
          (gammaTriangleConst 2 * Cin) * (((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ))) := by ring
      have hstep2 : C * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ)) =
          C * (((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ))) := by ring
      rw [hstep1, hstep2]
      have hMCin : M * Cin = C := by rw [hCindef]; field_simp
      have hcoefle : gammaTriangleConst 2 * Cin ≤ C := by
        have hstepc := mul_le_mul_of_nonneg_right hMge2 hCinpos.le
        linarith only [hstepc, hMCin]
      exact mul_le_mul_of_nonneg_right hcoefle hrest_nn
    have hX2amp : gammaTriangleConst 1 * (Cin * ((L - n : ℕ):ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ))) ≤
        C * ((L - n : ℕ):ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ)) := by
      have hrest_nn : (0:ℝ) ≤ ((L - n : ℕ):ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ)) :=
        mul_nonneg hLnR_pos.le (Real.rpow_nonneg hsigmapos.le _)
      have hstep1 : gammaTriangleConst 1 * (Cin * ((L - n : ℕ):ℝ) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ))) =
          (gammaTriangleConst 1 * Cin) * (((L - n : ℕ):ℝ) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ))) := by ring
      have hstep2 : C * ((L - n : ℕ):ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ)) =
          C * (((L - n : ℕ):ℝ) *
            (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ))) := by ring
      rw [hstep1, hstep2]
      have hMCin : M * Cin = C := by rw [hCindef]; field_simp
      have hcoefle : gammaTriangleConst 1 * Cin ≤ C := by
        have hstepc := mul_le_mul_of_nonneg_right hMge1 hCinpos.le
        linarith only [hstepc, hMCin]
      exact mul_le_mul_of_nonneg_right hcoefle hrest_nn
    have hX1finO : IsBigO P.toMeasure (gammaSigma 2) X1'
        (C * ((L - n : ℕ):ℝ) ^ ((1:ℝ)/2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(1:ℝ))) :=
      hX1'O.mono_scale hX1amp
    have hX2finO : IsBigO P.toMeasure (gammaSigma 1) X2'
        (C * ((L - n : ℕ):ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n:ℤ)))) ^ (-(2:ℝ))) :=
      hX2'O.mono_scale hX2amp
    refine ⟨X1', X2', X3', hX1'M, hX1finO, hX2'M, hX2finO, hX3'M, hX3finO, ?_⟩
    intro omega p q
    rw [hFinalGoalEq omega p q]
    have hAvgAdd : descendantsAverage (originCube d (m:ℤ)) (m - n)
        (fun R' => F1 R' omega p q + F2 R' omega p q + F3 R' omega p q) =
        descendantsAverage (originCube d (m:ℤ)) (m - n) (fun R' => F1 R' omega p q) +
          descendantsAverage (originCube d (m:ℤ)) (m - n) (fun R' => F2 R' omega p q) +
          descendantsAverage (originCube d (m:ℤ)) (m - n) (fun R' => F3 R' omega p q) := by
      simp only [descendantsAverage, Finset.sum_add_distrib, mul_add]
    rw [hAvgAdd]
    have h1 := hX1'bd omega p q
    have h2 := hX2'bd omega p q
    have h3 := hX3'bd omega p q
    nlinarith only [h1, h2, h3]

end

end SuperdiffusionCLT.Section4.Mixing
