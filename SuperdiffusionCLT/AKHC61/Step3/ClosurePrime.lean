/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.RecursionWC
public import SuperdiffusionCLT.AKHC61.Step3.IterationD

/-!
# Closing Step 3 on the V4′ range: the bridge to the decay lemma

`akhcF1_core` (`AKHC61/Core.lean`) carries Step 3 as `hStep3`. This file holds the bridge
below, and records an obstruction.

* **The bridge** `akhcCL_recursion_range`. One application of `akhcRV2_weighted_recursion` at
  scale `m` with base `k ≥ K₀`, rewritten in the exact form of the recursion hypothesis of
  `akhcDW_decay` (`Step3/DecayWeightedB.lean`). The form is
  `F = Θ - 1`, `θ = akhcIter_thetaMax d`, `c = linConst/2`, `A = B = B_w`, `w = 3^{-(1/2-s')}`,
  `q(n) = n - ℓ(n)`, sums over `j < m - K₀`. The step reindexes `(k, m] ∋ n ↦ j = m - n`, extends
  the sums from `j < m - k` to `j < m - K₀` (the extra terms are `≥ 0`, since `Θ` is antitone and
  `≥ 1`), and caps `θ_m` by the dimension-only `θmax` (`IterationD`).
* **The `β` obstruction** (a remark; no Lean statement is kept). Every instance of
  `akhcRV2_weighted_recursion` at scale `n` has a base `k` with `βn < k ≤ n` (its `hbeta`,
  `hkm`). Its right side contains the low-scale tail `B_w 3^{-(1-2s')(n-k)}`, and every other
  summand is `≥ 0`. So any sequence below `B_w 3^{-(1-2s')(n-k)}` for all such `k` satisfies every
  instance of the recursion. For each rate `κ > 0` there are `β ∈ [0, 1)` and a nonnegative,
  antitone, `σ`-small such sequence that is not `O(3^{-κ(n-N)})` from any start `N`. Hence no
  argument that only feeds this recursion (with Step 2's `Θ ≤ 1 + σ`, monotonicity, `Θ ≥ 1`) into
  a decay lemma can give `hStep3` with a rate `κ` independent of `β`. V4′'s
  `κ = min{α(d), (1-γ)/2}` is such a rate, and V4′ allows every `β ∈ [0, 1)`. The rate this route
  delivers is at most `(1-2s')(1-β) ≤ (1-β)/2`.
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

/-! ## The bridge: the weighted recursion in the form of `akhcDW_decay` -/

/-- **Reindexing**: `Σ_{n ∈ (k, m]} 3^{-(1/2-s')(m-n)} g_n ≤ Σ_{j < m-K₀} w^j g_{m-j}`,
`w = 3^{-(1/2-s')}`, when `K₀ ≤ k ≤ m` and `g ≥ 0` on `(K₀, k]`. -/
theorem akhcCL_wsum_le_range (s' : ℝ) {k m K0 : ℕ} (hK0k : K0 ≤ k) (hkm : k ≤ m) (g : ℕ → ℝ)
    (hg : ∀ n, K0 < n → n ≤ k → 0 ≤ g n) :
    ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) * g n ≤
      ∑ j ∈ Finset.range (m - K0), ((3 : ℝ) ^ (-(1 / 2 - s'))) ^ j * g (m - j) := by
  have heq : ∑ n ∈ Finset.Icc (k + 1) m,
      (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) * g n =
      ∑ j ∈ Finset.range (m - k), ((3 : ℝ) ^ (-(1 / 2 - s'))) ^ j * g (m - j) := by
    refine Finset.sum_nbij' (fun n => m - n) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      have h := Finset.mem_Icc.1 hn
      exact Finset.mem_range.2 (by omega)
    · intro j hj
      have h := Finset.mem_range.1 hj
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · intro n hn
      have h := Finset.mem_Icc.1 hn
      omega
    · intro j hj
      have h := Finset.mem_range.1 hj
      omega
    · intro n hn
      have h := Finset.mem_Icc.1 hn
      rw [← Real.rpow_mul_natCast (by norm_num), Nat.cast_sub h.2,
        show m - (m - n) = n by omega]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega))
  · intro j hj hjn
    have h1 := Finset.mem_range.1 hj
    have h2 : ¬ j < m - k := fun h => hjn (Finset.mem_range.2 h)
    exact mul_nonneg (by positivity) (hg (m - j) (by omega) (by omega))

theorem akhcCL_Bw_nonneg (d : ℕ) [NeZero d] {s' : ℝ} (rho : ℝ) (hhi : s' < 1 / 2) :
    0 ≤ akhcRW_Bw d s' rho := by
  have hlin : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d := by
    unfold SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst
    have := Homogenization.quantitativeCubeCutoffGradientConst_nonneg d
    positivity
  have hprod : 0 ≤ SuperdiffusionCLT.AKHC61.Step2.akhcJB_prodConst d :=
    (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_nonneg
      (Homogenization.originCube d ((0 : ℕ) : ℤ)) (1 / 2 : ℝ) (1 / 2 : ℝ)).trans
      (Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffProductCoeff_origin_le_dimensional
        (d := d) 0 (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num))
  have hGs := akhcRW_Gs_nonneg hhi
  have hmax : 0 ≤ SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC2_maximizerConst s' rho := by
    unfold SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC2_maximizerConst
    positivity
  unfold akhcRW_Bw akhcRW_Benergy
  positivity

section Bridge

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
  (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
  (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (homega : ∀ k : ℕ, 0 < omegaSeq k)
  (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) (hKPsi : 1 ≤ KPsi)
  (hGrowthPsi : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
    (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
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
                          (Homogenization.coarseBlockMatrix
                            (Homogenization.cubeSet R)
                            (coefficientCutoff nu omega L).toCoeffField) -
                        Homogenization.toFullBlockMat
                          (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                            nu L P
                            (Homogenization.cubeSet
                              (Homogenization.originCube d (n : ℤ))))))
                    q)) ≤
          X omega *
            (Homogenization.blockVecDot p
                (Homogenization.blockMatVecMul
                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                  p) +
              Homogenization.blockVecDot q
                (Homogenization.blockMatVecMul
                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                    (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                  q)))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
  hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3

/-- **The bridge.** `akhcRV2_weighted_recursion` at scale `m` with base `k ≥ K₀`, in the exact
form of the recursion hypothesis of `akhcDW_decay` for `F = Θ - 1`: contraction
`akhcIter_thetaMax d` at lag `Lstep`, quadratic coefficient `linConst/2`, drop and lag sums over
`j < m - K₀` with weight `w = 3^{-(1/2-s')}` and coefficient `B_w`, lag `q(n) = n - ℓ(n)`, and
source `B_w (Υ^{port} ω_{k-ℓ(k)}² + (P2′ tail) + 3^{-(1-2s')(m-k)})`. Its hypotheses are those of
`akhcRV2_weighted_recursion` and `K₀ ≤ k`. -/
theorem akhcCL_recursion_range (hd : 2 ≤ d) (homegaAnti : Antitone omegaSeq)
    {m k Lstep K0 : ℕ} (hK0k : K0 ≤ k) (hm2 : m2 ≤ m) (hkm : k < m) (hLstep : Lstep ≤ m)
    (e : Vec d) (he : vecNormSq e = 1)
    (hScaleSep :
      Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffOscillationConstant
          (Homogenization.originCube d (m : ℤ)) *
        Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.section53CutoffScaleSep
          (Homogenization.originCube d (m : ℤ)) Lstep ≤ (1 / 4 : ℝ))
    {s' rho eta : ℝ} (hlo : 1 / 4 ≤ s') (hhi : s' < 1 / 2) (hgap : rho / 2 < s')
    (hgammarho : gamma ≤ rho) (heta2 : 2 < eta) (hetaPsi : eta ≤ pPsi)
    (hc : 0 < 2 * rho - 2 * (d : ℝ) / eta)
    {k0 : ℕ} (hk0m : k0 ≤ m) (hm3 : m3 ≤ k) (hbeta : beta * (m : ℝ) < (k : ℝ))
    (hwin : (k : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * (k : ℝ)))
    (hkL1 : L1 ≤ (k : ℝ))
    (hwinE2 : ∀ n ∈ Finset.Icc (k + 1) m, 1 < L2 * (n : ℝ) ∧
      beta * (n : ℝ) <
        (n : ℝ) - (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n : ℝ) ∧
      m3 ≤ n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n)
    (hΘ2 : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
      (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ≤ 2) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1 ≤
      akhcIter_thetaMax d *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - Lstep) - 1) +
        SuperdiffusionCLT.AKHC61.Step2.akhcJB_linConst d / 2 *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) ^ 2 +
        akhcRW_Bw d s' rho * ∑ j ∈ Finset.range (m - K0), ((3 : ℝ) ^ (-(1 / 2 - s'))) ^ j *
          ((SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (m - j) - 1) -
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1)) +
        akhcRW_Bw d s' rho * ∑ j ∈ Finset.range (m - K0), ((3 : ℝ) ^ (-(1 / 2 - s'))) ^ j *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
            ((m - j) - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 (m - j)) -
              1) ^ 2 +
        akhcRW_Bw d s' rho *
          (akhcRW_UpsPort d eta rho KPsi *
              omegaSeq (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ^ 2 +
            3 * KPsiS ^ 36 * (H * (m : ℝ) ^ D) ^ (2 : ℝ) *
              (3 : ℝ) ^ (-2 * (rho - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
            (3 : ℝ) ^ (-(1 - 2 * s') * ((m : ℝ) - (k : ℝ)))) := by
  have hW := akhcRV2_weighted_recursion hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 beta L1 L2 m3 omegaSeq
    Psi KPsi pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3 hd homegaAnti hm2 hkm
    hLstep e he hScaleSep hlo hhi hgap hgammarho heta2 hetaPsi hc hk0m hm3 hbeta hwin hkL1
    hwinE2 hΘ2
  have hanti := akhc_antitone_thetaCutoff_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (L := L)
  have hone := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (L := L)
  have hBw := akhcCL_Bw_nonneg d rho hhi
  set Θ := SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P with hΘdef
  set ℓ := SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 with hℓdef
  -- the contraction factor
  have hθ := akhcIter_theta_le_thetaMax d (Homogenization.originCube d (m : ℤ))
  have hθmul := mul_le_mul_of_nonneg_right hθ (show 0 ≤ Θ (m - Lstep) - 1 by
    linarith only [hone (m - Lstep)])
  -- the two weighted sums
  have hS1 := akhcCL_wsum_le_range s' hK0k hkm.le (fun n => (Θ n - 1) - (Θ m - 1)) (by
    intro n _ hn
    have := hanti (show n ≤ m by omega)
    linarith only [this])
  have hS1eq : ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
      (Θ n - Θ m) = ∑ n ∈ Finset.Icc (k + 1) m,
        (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) * ((Θ n - 1) - (Θ m - 1)) :=
    Finset.sum_congr rfl fun n _ => by ring
  have hS2 := akhcCL_wsum_le_range s' hK0k hkm.le (fun n => (Θ (n - ℓ n) - 1) ^ 2)
    (fun n _ _ => sq_nonneg _)
  rw [← hS1eq] at hS1
  have hB1 := mul_le_mul_of_nonneg_left hS1 hBw
  have hB2 := mul_le_mul_of_nonneg_left hS2 hBw
  linear_combination hW + hθmul + hB1 + hB2

end Bridge

end

end SuperdiffusionCLT.AKHC61.Step3
