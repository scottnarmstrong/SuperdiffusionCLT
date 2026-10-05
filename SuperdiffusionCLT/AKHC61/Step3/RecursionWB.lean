/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.RecursionW

/-!
# The weighted Step 3 recursion, part 2: the weighted energy bound at a fixed base scale

* `akhcRW_fl_le`: for `L₁ ≤ k ≤ n ≤ m` inside the per-scale (P3′) window, the expected
  fluctuation of `bfA(cu_n)` at the normalization of scale `m` is at most
  `512 d² (Θ_{n-ℓ(n)} - 1)² + UpsVar · ω_{k-ℓ(k)}²`, given `Θ_{k-ℓ(k)} ≤ 2`. It composes
  `akhcPrime_integral_fl_le_relFrob` (`WeakNorms/PrimeI.lean`) with
  `akhcVA_variance_again_prime` (`Step3/VarianceAgain.lean`) taken at `p_Ψ := η`, and uses the
  monotonicity of `n ↦ n - ℓ(n)` above `L₁` (`akhcRW_sub_lag_mono`) to move `Θ` and `ω` to the
  base index `k - ℓ(k)`.
* `akhcRW_energy_le`: C6's general form `akhcPrime_expected_energy_le` at `h := k`,
  `β := 1/2 - s'`, `ε := 1`, with every weighted sum kept. The drops are bounded per scale by
  `akhcPrime_tau_le` and E1 (`δ_n := Θ_n - Θ_m`), the fluctuations per scale by
  `akhcRW_fl_le`, the `M⁺` dominator by `akhcMM_Mplus_secondMoment_le` at `h = k`, the
  constant tail by `akhcPrime_constTail_le`; the pieces are assembled by `akhcRW_assembly`.
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

private theorem akhcRW_IAb {ι : Type*} (s : Finset ι) (w F Vb : ι → ℝ) {θ X Gs : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2) (hF : ∀ n ∈ s, F n ≤ Vb n)
    (hVb0 : ∀ n ∈ s, 0 ≤ Vb n) (hX : X = ∑ n ∈ s, w n * Vb n) (hSβ : ∑ n ∈ s, w n ≤ Gs)
    (hX0 : 0 ≤ X) :
    (∑ n ∈ s, w n) * ∑ n ∈ s, w n * (2 * θ) * F n ≤ Gs * (4 * X) := by
  have hsum : ∑ n ∈ s, w n * (2 * θ) * F n ≤ 4 * X := by
    rw [hX, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have h1 := mul_le_mul_of_nonneg_left (hF n hn) (mul_nonneg zero_le_two hθ0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith only [hθ2] : 2 * θ ≤ 4) (hVb0 n hn)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 n)
    calc w n * (2 * θ) * F n = w n * ((2 * θ) * F n) := by ring
      _ ≤ _ := h3
      _ = 4 * (w n * Vb n) := by ring
  have hSw0 : 0 ≤ ∑ n ∈ s, w n := Finset.sum_nonneg fun n _ => hw0 n
  have h4 := mul_le_mul_of_nonneg_left hsum hSw0
  have h5 := mul_le_mul_of_nonneg_right hSβ (by linarith only [hX0] : (0 : ℝ) ≤ 4 * X)
  exact h4.trans h5

private theorem akhcRW_IFb {ι : Type*} (s : Finset ι) (w F Vb : ι → ℝ) {Fm X Y Gs : ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hF : ∀ n ∈ s, F n ≤ Vb n) (hFm : Fm ≤ Y)
    (hX : X = ∑ n ∈ s, w n * Vb n) (hSw : ∑ n ∈ s, w n ≤ Gs) (hY0 : 0 ≤ Y) :
    ∑ n ∈ s, w n * (F n + Fm) ≤ X + Gs * Y := by
  have hsum : ∑ n ∈ s, w n * (F n + Fm) ≤ X + (∑ n ∈ s, w n) * Y := by
    rw [hX, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have h1 := mul_le_mul_of_nonneg_left (add_le_add (hF n hn) hFm) (hw0 n)
    linarith only [h1]
  have h2 := mul_le_mul_of_nonneg_right hSw hY0
  linarith only [hsum, h2]

private theorem akhcRW_CT_le {CT θ T s' : ℝ} (m k : ℕ) (hs0 : 0 ≤ s') (hkmR : (k : ℝ) ≤ (m : ℝ))
    (hθ : θ ≤ 2)
    (hCT : CT ≤ 8 * Real.rpow (3 : ℝ) (-((m : ℝ) - (k : ℝ))) * θ)
    (hTdef : T = (3 : ℝ) ^ (-(1 - 2 * s') * ((m : ℝ) - (k : ℝ)))) : CT ≤ 16 * T := by
  have hexp : Real.rpow (3 : ℝ) (-((m : ℝ) - (k : ℝ))) ≤ T := by
    rw [hTdef]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : 0 ≤ s' * ((m : ℝ) - (k : ℝ)) := mul_nonneg hs0 (by linarith only [hkmR])
    linarith only [this]
  have hr0 : 0 ≤ Real.rpow (3 : ℝ) (-((m : ℝ) - (k : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have h1 := mul_le_mul_of_nonneg_left hθ hr0
  have h2 := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 16)
  have e1 : 8 * Real.rpow (3 : ℝ) (-((m : ℝ) - (k : ℝ))) * θ =
      8 * (Real.rpow (3 : ℝ) (-((m : ℝ) - (k : ℝ))) * θ) := by ring
  linarith only [hCT, h1, h2, e1]

private theorem akhcRW_mem (k m : ℕ) (n : ℤ) (hn : n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ)) :
    Int.toNat n ∈ Finset.Icc (k + 1) m ∧ ((Int.toNat n : ℕ) : ℤ) = n := by
  have h := Finset.mem_Icc.1 hn
  exact ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩

private theorem akhcRW_U2 (s' : ℝ) {m k : ℕ} (hkm : k ≤ m) :
    SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_u (1 / 2) s' (m : ℤ) (k : ℤ) ^ 2 =
      ((1 / 2 - s')⁻¹) ^ 2 * (3 : ℝ) ^ (-(1 - 2 * s') * ((m : ℝ) - (k : ℝ))) := by
  have htoNat : ((Int.toNat ((m : ℤ) - (k : ℤ)) : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
    have : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by omega
    rw [this, Nat.cast_sub hkm]
  unfold SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_u
  rw [htoNat, mul_pow, sq (Real.rpow (3 : ℝ) _), Real.rpow_eq_pow,
    ← Real.rpow_add (by norm_num)]
  congr 2
  ring

section PerScale

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

/-- **The per-scale variance at the normalization of `m`, moved to the base index.** For
`L₁ ≤ k ≤ n ≤ m`, the per-scale window `1 < L₂ n`, `β n < n - ℓ(n)`, `m₃ ≤ n - ℓ(n)`, an
exponent `2 < η ≤ p_Ψ` with `d < η`, and `Θ_{k-ℓ(k)} ≤ 2`:
`E[fluct_m(cu_n)] ≤ 512 d² (Θ_{n-ℓ(n)} - 1)² + UpsVar(d, η, K_Ψ) ω_{k-ℓ(k)}²`. -/
theorem akhcRW_fl_le (hd : 2 ≤ d) (homegaAnti : Antitone omegaSeq) {k n m : ℕ}
    (hkL1 : L1 ≤ (k : ℝ)) (hkn : k ≤ n) (hnm : n ≤ m) (hL2n : 1 < L2 * (n : ℝ))
    (hwin1 : beta * (n : ℝ) <
      (n : ℝ) - (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n : ℝ))
    (hm3n : m3 ≤ n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n)
    {eta : ℝ} (heta2 : 2 < eta) (hetaPsi : eta ≤ pPsi) (hetad : (d : ℝ) < eta)
    (hΘ2 : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
      (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ≤ 2) :
    ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d (n : ℤ)) a
        ∂(cutoffLaw (d := d) nu L P) ≤
      512 * (d : ℝ) ^ 2 * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
          (n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n) - 1) ^ 2 +
        akhcRW_UpsVar d eta KPsi *
          omegaSeq (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ^ 2 := by
  have hmono := akhcRW_sub_lag_mono hL1 hL2 hkL1 hkn
  set kk := k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k with hkk
  set nn := n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n with hnn
  have hΘanti := akhc_antitone_thetaCutoff_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
  have hΘn : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P nn ≤ 2 :=
    (hΘanti hmono).trans hΘ2
  have hΘn1 := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 nn
  have hωn : omegaSeq nn ≤ omegaSeq kk := homegaAnti hmono
  have hGrowthEta : ∀ p : ℝ, 1 < p → p ≤ eta → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t) :=
    fun p hp1 hpη => hGrowthPsi p hp1 (hpη.trans hetaPsi)
  have hvar := (akhcVA_variance_again_prime (hnu := hnu) (P := P) (hJ4 := hJ4) (L := L)
    (hPrefix := hPrefix) (hJ2 := hJ2) (hd := hd) (gamma := gamma) (H := H) (D := D)
    (m2 := m2) (PsiS := PsiS) (KPsiS := KPsiS) (pPsiS := pPsiS) (hgamma0 := hgamma0)
    (hgamma1 := hgamma1) (hH := hH) (hD := hD) (hPsiSMono := hPsiSMono)
    (hPsiSOne := hPsiSOne) (hKPsiS := hKPsiS) (hpPsiS := hpPsiS) (hGrowth := hGrowth)
    (hP2 := hP2) (beta := beta) (L1 := L1) (L2 := L2) (m3 := m3) (omegaSeq := omegaSeq)
    (Psi := Psi) (KPsi := KPsi) (pPsi := eta) (hbeta0 := hbeta0) (hL1 := hL1) (hL2 := hL2)
    (homegaPos := homega) (hPsiOne := hPsiOne) (hKPsi := hKPsi) (hpPsi := hetad)
    (hGrowthP3 := hGrowthEta) (hP3 := hP3) (n := n) (m := m) hnm hL2n hwin1 hm3n).2
  have hfl := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_integral_fl_le_relFrob hnu P L
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
    hP2 hJ4 m n
  rw [akhcVA_matDiag_annealed_eq (hnu := hnu) (hJ4 := hJ4)] at hfl
  refine hfl.trans (hvar.trans ?_)
  -- the `Θ² ω²` factor
  set c := (2 * (d : ℝ)) ^ 2 * ((eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2)) with hcdef
  have hc0 : 0 ≤ c := by
    have h1 : 0 ≤ eta / (eta - 2) :=
      div_nonneg (by linarith only [heta2]) (by linarith only [heta2])
    have h2 : 0 ≤ KPsi ^ (3 * ⌈eta⌉₊ ^ 2) := pow_nonneg (by linarith only [hKPsi]) _
    positivity
  have hΘsq : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P nn ^ 2 ≤ 4 := by
    nlinarith only [hΘn, hΘn1]
  have hωsq : omegaSeq nn ^ 2 ≤ omegaSeq kk ^ 2 :=
    pow_le_pow_left₀ (homega nn).le hωn 2
  have h1 : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P nn ^ 2 *
      (c * omegaSeq nn ^ 2) ≤ 4 * (c * omegaSeq kk ^ 2) :=
    mul_le_mul hΘsq (mul_le_mul_of_nonneg_left hωsq hc0)
      (mul_nonneg hc0 (sq_nonneg _)) (by norm_num)
  have hUps : akhcRW_UpsVar d eta KPsi * omegaSeq kk ^ 2 = 32 * (4 * (c * omegaSeq kk ^ 2)) := by
    rw [akhcRW_UpsVar, hcdef]; ring
  rw [hUps]
  linarith only [h1]

/-- **C6's general form at the fixed base scale `k`, with the weighted sums kept.** Node 7
(`akhcPrime_expected_energy_le`) at `h := k`, `β := 1/2 - s'`, `ε := 1`, with the per-scale
drop bounds (`akhcPrime_tau_le` and E1), the per-scale variance (`akhcRW_fl_le`), C3's `M⁺`
second moment at `h = k` and the constant tail:
`E[σ̂ G² + σ̂⁻¹ F²] ≤ 16 Benergy · (Σ_n w_n (Θ_n - Θ_m) + Σ_n w_n (Θ_{n-ℓ(n)} - 1)² +
Υ^{port} ω_{k-ℓ(k)}² + (P2′ tail at k₀) + 3^{-(1-2s')(m-k)})`, `w_n = 3^{-(1/2-s')(m-n)}`,
`n ∈ (k, m]`. -/
theorem akhcRW_energy_le (hd : 2 ≤ d) (homegaAnti : Antitone omegaSeq) {m k k0 : ℕ}
    (hm2 : m2 ≤ m) (hkm : k < m) (hk0m : k0 ≤ m) (hm3 : m3 ≤ k)
    (hbeta : beta * (m : ℝ) < (k : ℝ))
    (hwin : (k : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * (k : ℝ)))
    (hkL1 : L1 ≤ (k : ℝ))
    (hwinE2 : ∀ n ∈ Finset.Icc (k + 1) m, 1 < L2 * (n : ℝ) ∧
      beta * (n : ℝ) <
        (n : ℝ) - (SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n : ℝ) ∧
      m3 ≤ n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n)
    {s' rho eta : ℝ} (hlo : 1 / 4 ≤ s') (hhi : s' < 1 / 2) (hgap : rho / 2 < s')
    (hgammarho : gamma ≤ rho) (heta2 : 2 < eta) (hetaPsi : eta ≤ pPsi)
    (hc : 0 < 2 * rho - 2 * (d : ℝ) / eta)
    (e : Vec d) (he : vecNormSq e = 1)
    (hΘ2 : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
      (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ≤ 2) :
    ∫ a, SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_energy nu L P m e a
        ∂(cutoffLaw (d := d) nu L P) ≤
      16 * akhcRW_Benergy d s' rho *
        (∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n -
              SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) +
          ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
            (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
              (n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n) - 1) ^ 2 +
          akhcRW_UpsPort d eta rho KPsi *
            omegaSeq (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k) ^ 2 +
          3 * KPsiS ^ 36 * (H * (m : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (rho - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
          (3 : ℝ) ^ (-(1 - 2 * s') * ((m : ℝ) - (k : ℝ)))) := by
  -- the target majorant
  set SD := ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n -
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) with hSDdef
  set SQ := ∑ n ∈ Finset.Icc (k + 1) m, (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
        (n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n) - 1) ^ 2 with hSQdef
  set ω0 := omegaSeq (k - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 k)
    with hω0def
  set Tl := 3 * KPsiS ^ 36 * (H * (m : ℝ) ^ D) ^ (2 : ℝ) *
      (3 : ℝ) ^ (-2 * (rho - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2)
    with hTldef
  set T := (3 : ℝ) ^ (-(1 - 2 * s') * ((m : ℝ) - (k : ℝ))) with hTdef
  set S := SD + SQ + akhcRW_UpsPort d eta rho KPsi * ω0 ^ 2 + Tl + T with hSdef
  -- elementary facts
  have hm : 0 < m := by omega
  have hkmZ : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm.le
  have hs0 : 0 ≤ s' := by linarith only [hlo]
  have hrho1 : rho < 1 := by linarith only [hgap, hhi]
  have heta0 : 0 < eta := by linarith only [heta2]
  have hetad : (d : ℝ) < eta := by
    have h1 : 2 * (d : ℝ) / eta < 2 := by linarith only [hc, hrho1]
    have h2 : (d : ℝ) / eta < 1 := by
      have : 2 * (d : ℝ) / eta = 2 * ((d : ℝ) / eta) := by ring
      linarith only [h1, this]
    exact (div_lt_one heta0).1 h2
  have hΘanti := akhc_antitone_thetaCutoff_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
  have hΘk : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k ≤ 2 :=
    (hΘanti (Nat.sub_le k _)).trans hΘ2
  have hΘm2 : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m ≤ 2 :=
    (hΘanti hkm.le).trans hΘk
  have hΘm1 := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  -- nonnegativity of the pieces of `S`
  have hw0 : ∀ n : ℕ, 0 ≤ (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) :=
    fun n => Real.rpow_nonneg (by norm_num) _
  have hSD0 : 0 ≤ SD := by
    refine Finset.sum_nonneg fun n hn => mul_nonneg (hw0 n) ?_
    have := hΘanti (Finset.mem_Icc.1 hn).2
    linarith only [this]
  have hSQ0 : 0 ≤ SQ := Finset.sum_nonneg fun n _ => mul_nonneg (hw0 n) (sq_nonneg _)
  have hUV0 := akhcRW_UpsVar_nonneg d heta2 hKPsi
  have hUM0 := akhcRW_UpsMM_nonneg d heta2 hKPsi hc
  have hpS : 0 < min 3 pPsiS - 2 := by
    have : 2 < min 3 pPsiS := lt_min (by norm_num) hpPsiS
    linarith only [this]
  have hTl0 : 0 ≤ Tl := by
    have h1 : 0 ≤ (H * (m : ℝ) ^ D) ^ (2 : ℝ) :=
      Real.rpow_nonneg (mul_nonneg (by linarith only [hH]) (Real.rpow_nonneg (Nat.cast_nonneg m) _)) _
    have h2 : 0 ≤ KPsiS ^ 36 := pow_nonneg (by linarith only [hKPsiS]) _
    have h3 : 0 ≤ (3 : ℝ) ^ (-2 * (rho - gamma) * ((m : ℝ) - ((k0 : ℝ) - 1))) :=
      Real.rpow_nonneg (by norm_num) _
    rw [hTldef]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) h1) h3) hpS.le
  have hT0 : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hkmR : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hkm.le
  have hT1 : T ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have : 0 ≤ (1 - 2 * s') * ((m : ℝ) - (k : ℝ)) :=
      mul_nonneg (by linarith only [hhi]) (by linarith only [hkmR])
    linarith only [this]
  have hUω : akhcRW_UpsPort d eta rho KPsi * ω0 ^ 2 =
      akhcRW_UpsVar d eta KPsi * ω0 ^ 2 + akhcRW_UpsMM d eta rho KPsi * ω0 ^ 2 := by
    rw [akhcRW_UpsPort]; ring
  have hUV : 0 ≤ akhcRW_UpsVar d eta KPsi * ω0 ^ 2 := mul_nonneg hUV0 (sq_nonneg _)
  have hUM : 0 ≤ akhcRW_UpsMM d eta rho KPsi * ω0 ^ 2 := mul_nonneg hUM0 (sq_nonneg _)
  have hS0 : 0 ≤ S := by rw [hSdef, hUω]; linarith only [hSD0, hSQ0, hUV, hUM, hTl0, hT0]
  have hSDS : SD ≤ S := by rw [hSdef, hUω]; linarith only [hSQ0, hUV, hUM, hTl0, hT0]
  have hSQS : SQ ≤ S := by rw [hSdef, hUω]; linarith only [hSD0, hUV, hUM, hTl0, hT0]
  have hUVS : akhcRW_UpsVar d eta KPsi * ω0 ^ 2 ≤ S := by
    rw [hSdef, hUω]; linarith only [hSD0, hSQ0, hUM, hTl0, hT0]
  have hTS : T ≤ S := by rw [hSdef, hUω]; linarith only [hSD0, hSQ0, hUV, hUM, hTl0]
  have hMS : Tl + akhcRW_UpsMM d eta rho KPsi * ω0 ^ 2 ≤ S := by
    rw [hSdef, hUω]; linarith only [hSD0, hSQ0, hUV, hT0]
  -- the scalars at `m` and `k`
  have hb := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hcm := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hbk := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
    hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hck := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  set b := sigmaBarSeq nu L P m with hbdef
  set c := sigmaBarStarInvSeq nu L P m with hcdef
  have hθ : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m = b * c := rfl
  set u := Real.sqrt (b * c) with hudef
  have huu : b * c = u * u := (Real.mul_self_sqrt (mul_pos hb hcm).le).symm
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ≤ 2 := by nlinarith only [huu, hθ, hΘm2, hu0]
  set σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  have hσ : 0 < σ := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_sigmaHat_pos
    (m := (m : ℤ)) hb hcm
  obtain ⟨hσc, hσb⟩ := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_sigmaHat_mul hb hcm
  have hσdef : σ = Real.sqrt (b * c⁻¹) := rfl
  rw [← hσdef, ← hudef] at hσc hσb
  -- `σ̄_k ≤ 2 σ̄_m`, `σ̄*⁻¹_k ≤ 2 σ̄*⁻¹_m` (E1 with `Θ_k ≤ 2`)
  have hbk2 : sigmaBarSeq nu L P k ≤ 2 * b := by
    have h := akhc_algebraic_comparison_sigmaBar_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS
      KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm.le
    have h' : sigmaBarSeq nu L P k / b ≤ 2 := by linarith only [h, hΘk, hΘm1]
    exact (div_le_iff₀ hb).1 h'
  have hck2 : sigmaBarStarInvSeq nu L P k ≤ 2 * c := by
    have h := akhc_algebraic_comparison_sigmaBarStarInv_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2
      PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm.le
    have h' : sigmaBarStarInvSeq nu L P k / c ≤ 2 := by linarith only [h, hΘk, hΘm1]
    exact (div_le_iff₀ hcm).1 h'
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have k1 : σ * sigmaBarStarInvSeq nu L P k ≤ 4 := by
    have := mul_le_mul_of_nonneg_left hck2 hσ.le
    have e1 : σ * (2 * c) = 2 * (σ * c) := by ring
    linarith only [this, e1, hσc, hu2]
  have k2 : σ⁻¹ * sigmaBarSeq nu L P k ≤ 4 := by
    have := mul_le_mul_of_nonneg_left hbk2 hσi.le
    have e1 : σ⁻¹ * (2 * b) = 2 * (σ⁻¹ * b) := by ring
    linarith only [this, e1, hσb, hu2]
  -- C3's `M⁺` second moment at `h = k`
  obtain ⟨G, hGint, hMG, hBdd, hGle⟩ :=
    SuperdiffusionCLT.AKHC61.Tails.akhcMM_Mplus_secondMoment_le hnu hPrefix hJ2 hJ4 gamma H
      D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
      beta L1 L2 m3 omegaSeq Psi KPsi pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3
      (n := m) (h := k) (k0 := k0) hkm.le hm2 hm hk0m hm3 hbeta hwin hgammarho heta2 hetaPsi hc
  have hIG0 : 0 ≤ ∫ omega, G omega ∂P.toMeasure :=
    integral_nonneg fun omega => (sq_nonneg _).trans (hMG omega)
  have hGMm : ∫ omega, G omega ∂P.toMeasure ≤ Tl + akhcRW_UpsMM d eta rho KPsi * ω0 ^ 2 := by
    have hωk : omegaSeq k ≤ ω0 := homegaAnti (Nat.sub_le k _)
    have hωk2 : omegaSeq k ^ 2 ≤ ω0 ^ 2 := pow_le_pow_left₀ (homega k).le hωk 2
    have hMMe : (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
        KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * omegaSeq k ^ 2 *
        (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ =
        akhcRW_UpsMM d eta rho KPsi * omegaSeq k ^ 2 := by
      rw [akhcRW_UpsMM]; ring
    have hmono := mul_le_mul_of_nonneg_left hωk2 hUM0
    rw [hMMe] at hGle
    rw [hTldef]
    linarith only [hGle, hmono]
  -- the reference and integrability inputs
  have hE := SuperdiffusionCLT.AKHC61.WeakNorms.akhcWNSq_annealed_posDef hnu hJ4 gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    ((k : ℕ) : ℤ)
  have hIntFluct : ∀ R : TriadicCube d,
      Integrable (fun a => akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) R a)
        (cutoffLaw (d := d) nu L P) := fun R =>
    SuperdiffusionCLT.AKHC61.Carrier.akhcSq_integrable_fullBlockNormalizedFluctuationAtScale_of_P2
      hnu P L gamma H D m2 PsiS KPsiS pPsiS hKPsiS hpPsiS hPsiSOne hGrowth hP2 (m : ℤ) R
  set p := akhcSpecialPAtScale nu L P (m : ℤ) e
  set q := akhcSpecialQAtScale nu L P (m : ℤ) e
  have hJint : ∀ Q : TriadicCube d,
      Integrable (Book.Ch04.restrictionResponseJObservableCubeSet Q p q)
        (cutoffLaw (d := d) nu L P) := fun Q =>
    SuperdiffusionCLT.AKHC61.Response.akhc_integrable_restrictionResponseJObservableCubeSet_cutoffLaw
      d hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 Q p q
  have hIntEn : Integrable (SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_energy nu L P m e)
      (cutoffLaw (d := d) nu L P) := by
    unfold SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_energy
    exact ((SuperdiffusionCLT.AKHC61.WeakNorms.akhcWNSq_integrable_gradientWeakNorm_sq hnu
      hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne
      hKPsiS hpPsiS hGrowth hP2 hm2 hm _ _ _).const_mul _).add
      ((SuperdiffusionCLT.AKHC61.WeakNorms.akhcWNSq_integrable_fluxWeakNorm_sq hnu hPrefix
      hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 hm2 hm _ _ _).const_mul _)
  obtain ⟨hIntA, hIA⟩ := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_integral_avgDom L
    hPrefix hJ2 hnu (1 / 2 - s') m k hIntFluct
  obtain ⟨hIntD, hID⟩ := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_integral_defSum L hnu
    hPrefix hJ2 s' m k p q hJint
  obtain ⟨hIntF, hIF⟩ := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_integral_flSum L hnu
    hPrefix hJ2 s' m k hIntFluct
  have hβ : 1 / 2 - s' ≤ 1 / 2 := by linarith only [hs0]
  have hmain := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_expected_energy_le hnu L hJ4
    hkm (β := 1 / 2 - s') (ε := 1) hβ hlo hhi hgap one_pos e he hb hcm hE G hGint hMG hBdd hIntA
    hIntD hIntF hIntEn
  refine hmain.trans ?_
  rw [hIA, hID, hIF]
  -- the geometric sums
  have hSw0 := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_wSum_nonneg (1 / 2) s' (m : ℤ)
    (k : ℤ)
  have hSw : SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ) ≤
      akhcRW_Gs s' :=
    SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_geom_le hkmZ (by linarith only [hhi])
  have hSβ0 : 0 ≤ ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ) (-(1 / 2 - s') * (Int.toNat ((m : ℤ) - n) : ℝ)) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num) _
  have hSβ : ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Real.rpow (3 : ℝ) (-(1 / 2 - s') * (Int.toNat ((m : ℤ) - n) : ℝ)) ≤ akhcRW_Gs s' :=
    SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_geom_le hkmZ (by linarith only [hhi])
  have hGs0 : 0 ≤ akhcRW_Gs s' := akhcRW_Gs_nonneg hhi
  -- membership bookkeeping
  have hmem : ∀ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      Int.toNat n ∈ Finset.Icc (k + 1) m ∧ ((Int.toNat n : ℕ) : ℤ) = n :=
    fun n hn => akhcRW_mem k m n hn
  -- the per-scale variance budget
  have hA0 : (0 : ℝ) ≤ 512 * (d : ℝ) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have hVn : ∀ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
          ∂(cutoffLaw (d := d) nu L P) ≤
        512 * (d : ℝ) ^ 2 * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
            (Int.toNat n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2
              (Int.toNat n)) - 1) ^ 2 + akhcRW_UpsVar d eta KPsi * ω0 ^ 2 := by
    intro n hn
    obtain ⟨hnN, hcast⟩ := hmem n hn
    have hb' := Finset.mem_Icc.1 hnN
    obtain ⟨h1, h2, h3⟩ := hwinE2 (Int.toNat n) hnN
    have h := akhcRW_fl_le hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 beta L1 L2 m3 omegaSeq Psi KPsi
      pPsi hbeta0 hL1 hL2 homega hPsiOne hKPsi hGrowthPsi hP3 hd homegaAnti (k := k)
      (n := Int.toNat n) (m := m) hkL1 (by omega) hb'.2 h1 h2 h3 heta2 hetaPsi hetad hΘ2
    rw [hcast] at h
    exact h
  set X := ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w (1 / 2) s' (m : ℤ) n *
        (512 * (d : ℝ) ^ 2 * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
            (Int.toNat n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2
              (Int.toNat n)) - 1) ^ 2 + akhcRW_UpsVar d eta KPsi * ω0 ^ 2) with hXdef
  set Y := 512 * (d : ℝ) ^ 2 * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
      (m - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 m) - 1) ^ 2 +
      akhcRW_UpsVar d eta KPsi * ω0 ^ 2 with hYdef
  have hXeq : X = 512 * (d : ℝ) ^ 2 * SQ +
      SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_wSum (1 / 2) s' (m : ℤ) (k : ℤ) *
        (akhcRW_UpsVar d eta KPsi * ω0 ^ 2) :=
    akhcRW_wsum_split s' k m (fun nn => (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
      (nn - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 nn) - 1) ^ 2) _ _
  have hX0 : 0 ≤ X := by
    rw [hXeq]
    exact add_nonneg (mul_nonneg hA0 hSQ0) (mul_nonneg hSw0 hUV)
  have hY0 : 0 ≤ Y := add_nonneg (mul_nonneg hA0 (sq_nonneg _)) hUV
  have hX : X ≤ (512 * (d : ℝ) ^ 2 + akhcRW_Gs s') * S := by
    rw [hXeq]
    have h1 := mul_le_mul_of_nonneg_left hSQS hA0
    have h2 := mul_le_mul hSw hUVS hUV hGs0
    linarith only [h1, h2]
  have hY : Y ≤ (512 * (d : ℝ) ^ 2 + 1) * S := by
    have hmN : m ∈ Finset.Icc (k + 1) m := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    have hsingle := Finset.single_le_sum (f := fun n : ℕ =>
        (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (n : ℝ))) *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
            (n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2 n) - 1) ^ 2)
      (fun n _ => mul_nonneg (hw0 n) (sq_nonneg _)) hmN
    have hone : (3 : ℝ) ^ (-(1 / 2 - s') * ((m : ℝ) - (m : ℝ))) = 1 := by
      rw [sub_self, mul_zero, Real.rpow_zero]
    simp only [hone, one_mul] at hsingle
    have h1 := mul_le_mul_of_nonneg_left (hsingle.trans hSQS) hA0
    rw [hYdef]
    linarith only [h1, hUVS]
  have hθ0 : 0 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
    linarith only [hΘm1]
  -- (i) the node-16 piece
  have hIAb : (∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ) (-(1 / 2 - s') * (Int.toNat ((m : ℤ) - n) : ℝ))) *
      ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
        Real.rpow (3 : ℝ) (-(1 / 2 - s') * (Int.toNat ((m : ℤ) - n) : ℝ)) *
          (2 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) *
          ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
            ∂(cutoffLaw (d := d) nu L P) ≤ akhcRW_Gs s' * (4 * X) :=
    akhcRW_IAb (Finset.Icc ((k : ℤ) + 1) (m : ℤ))
      (fun n => Real.rpow (3 : ℝ) (-(1 / 2 - s') * (Int.toNat ((m : ℤ) - n) : ℝ)))
      (fun n => ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
        ∂(cutoffLaw (d := d) nu L P))
      (fun n => 512 * (d : ℝ) ^ 2 * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
            (Int.toNat n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2
              (Int.toNat n)) - 1) ^ 2 + akhcRW_UpsVar d eta KPsi * ω0 ^ 2)
      (fun _ => Real.rpow_nonneg (by norm_num) _) hθ0 hΘm2 hVn
      (fun _ _ => add_nonneg (mul_nonneg hA0 (sq_nonneg _)) hUV) hXdef hSβ hX0
  -- (ii) the drop piece
  have hIDb : ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w (1 / 2) s' (m : ℤ) n *
        Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ) n p q ≤ 2 * SD := by
    have hSDeq := akhcRW_wsum_eq s' k m (fun nn =>
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P nn -
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m)
    rw [hSDdef, ← hSDeq, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hnN, hcast⟩ := hmem n hn
    have hnm : Int.toNat n ≤ m := (Finset.mem_Icc.1 hnN).2
    have hw := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w_nonneg (1 / 2) s' (m : ℤ) n
    have hδ0 : 0 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
      have := hΘanti hnm
      linarith only [this]
    have hbn : sigmaBarSeq nu L P (Int.toNat n) ≤
        (1 + (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
          SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m)) * b := by
      have h := akhc_algebraic_comparison_sigmaBar_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS
        KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hnm
      have h' : sigmaBarSeq nu L P (Int.toNat n) / b ≤
          1 + (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) := by
        linarith only [h]
      exact (div_le_iff₀ hb).1 h'
    have hcn : sigmaBarStarInvSeq nu L P (Int.toNat n) ≤
        (1 + (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
          SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m)) * c := by
      have h := akhc_algebraic_comparison_sigmaBarStarInv_of_P2 hnu hPrefix hJ2 hJ4 gamma H D
        m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
        hnm
      have h' : sigmaBarStarInvSeq nu L P (Int.toNat n) / c ≤
          1 + (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
            SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) := by
        linarith only [h]
      exact (div_le_iff₀ hcm).1 h'
    have ht := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_tau_le hnu P L gamma H D m2
      PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
      (Int.toNat n) e he hbn hcn
    rw [hcast] at ht
    have ht2 : Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ) n p q ≤
        2 * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
          SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) := by
      have := mul_le_mul_of_nonneg_left hu2 hδ0
      have e1 : (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
          SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) * u =
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P (Int.toNat n) -
          SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) * Real.sqrt (b * c) := rfl
      linarith only [ht, this, e1]
    have := mul_le_mul_of_nonneg_left ht2 hw
    linarith only [this]
  -- (iii) the fluctuation piece
  have hIFb : ∑ n ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ),
      SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w (1 / 2) s' (m : ℤ) n *
        ((∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
            ∂(cutoffLaw (d := d) nu L P)) +
          ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ)
            (originCube d (m : ℤ)) a ∂(cutoffLaw (d := d) nu L P)) ≤
      X + akhcRW_Gs s' * Y := by
    have hmZ : (m : ℤ) ∈ Finset.Icc ((k : ℤ) + 1) (m : ℤ) :=
      Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
    have hVm : ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ)
        (originCube d (m : ℤ)) a ∂(cutoffLaw (d := d) nu L P) ≤ Y := by
      have h := hVn (m : ℤ) hmZ
      rw [Int.toNat_natCast] at h
      exact h
    exact akhcRW_IFb (Finset.Icc ((k : ℤ) + 1) (m : ℤ))
      (fun n => SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w (1 / 2) s' (m : ℤ) n)
      (fun n => ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d n) a
        ∂(cutoffLaw (d := d) nu L P))
      (fun n => 512 * (d : ℝ) ^ 2 * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P
            (Int.toNat n - SuperdiffusionCLT.AKHC61.Variance.akhcProtoLag L1 L2
              (Int.toNat n)) - 1) ^ 2 + akhcRW_UpsVar d eta KPsi * ω0 ^ 2)
      (fun n => SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_w_nonneg (1 / 2) s' (m : ℤ) n)
      hVn hVm hXdef hSw hY0
  -- κ and B_J at the reference `E = Ahom(cu_k)`
  set cK := SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC2_maximizerConst s' rho with hcKdef
  have hcK : 0 ≤ cK := by
    rw [hcKdef]; unfold SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC2_maximizerConst
    exact sq_nonneg _
  have hLR := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_matrixNorm_lowerRight hnu L hJ4
    ((k : ℕ) : ℤ) hck.le
  have hUL := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_matrixNorm_upperLeft hnu L hJ4
    ((k : ℕ) : ℤ) hbk.le
  rw [hLR, hUL]
  have hchS : sigmaBarStarInvScalar nu L P (cubeSet (originCube d ((k : ℕ) : ℤ))) =
      sigmaBarStarInvSeq nu L P k := rfl
  have hbhS : sigmaBarScalar nu L P (cubeSet (originCube d ((k : ℕ) : ℤ))) =
      sigmaBarSeq nu L P k := rfl
  rw [hchS, hbhS]
  have hκ : σ * (cK * sigmaBarStarInvSeq nu L P k) + σ⁻¹ * (cK * sigmaBarSeq nu L P k) ≤
      8 * cK := by
    have e1 : σ * (cK * sigmaBarStarInvSeq nu L P k) + σ⁻¹ * (cK * sigmaBarSeq nu L P k) =
        cK * (σ * sigmaBarStarInvSeq nu L P k + σ⁻¹ * sigmaBarSeq nu L P k) := by ring
    have := mul_le_mul_of_nonneg_left (add_le_add k1 k2) hcK
    linarith only [e1, this]
  have hκ0 : 0 ≤ σ * (cK * sigmaBarStarInvSeq nu L P k) + σ⁻¹ * (cK * sigmaBarSeq nu L P k) :=
    add_nonneg (mul_nonneg hσ.le (mul_nonneg hcK hck.le)) (mul_nonneg hσi.le (mul_nonneg hcK hbk.le))
  rw [SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_Bj_eq hnu L hJ4]
  rw [hbhS, hchS]
  obtain ⟨hpp, hqq, hpq⟩ := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_special_norms hσ he
  have hpp' : vecNormSq p = σ⁻¹ := hpp
  have hqq' : vecNormSq q = σ := hqq
  have hpq' : vecDot p q = 1 := hpq
  rw [hpp', hqq', hpq', abs_one]
  have hBj : (1 / 2 : ℝ) * (sigmaBarSeq nu L P k * σ⁻¹ + sigmaBarStarInvSeq nu L P k * σ) + 1 ≤
      5 := by
    have e1 : sigmaBarSeq nu L P k * σ⁻¹ + sigmaBarStarInvSeq nu L P k * σ =
        σ⁻¹ * sigmaBarSeq nu L P k + σ * sigmaBarStarInvSeq nu L P k := by ring
    linarith only [e1, k1, k2]
  have hBj0 : 0 ≤ (1 / 2 : ℝ) * (sigmaBarSeq nu L P k * σ⁻¹ +
      sigmaBarStarInvSeq nu L P k * σ) + 1 :=
    add_nonneg (mul_nonneg one_half_pos.le (add_nonneg (mul_nonneg hbk.le hσi.le)
      (mul_nonneg hck.le hσ.le))) zero_le_one
  -- the low-scale tail factor and the constant tail
  have htoNat : ((Int.toNat ((m : ℤ) - (k : ℤ)) : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := by
    have : Int.toNat ((m : ℤ) - (k : ℤ)) = m - k := by omega
    rw [this, Nat.cast_sub hkm.le]
  have hU2 : SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_u (1 / 2) s' (m : ℤ) (k : ℤ) ^ 2 =
      ((1 / 2 - s')⁻¹) ^ 2 * T := akhcRW_U2 s' hkm.le
  have hCT := SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_constTail_le hnu P L gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4
    m k e he
  rw [htoNat] at hCT
  have hCT' : SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_constTail nu L P m k e ≤
      16 * T := akhcRW_CT_le m k hs0 hkmR hΘm2 hCT hTdef
  have hUc : (0 : ℝ) ≤ ((1 / 2 - s')⁻¹) ^ 2 := sq_nonneg _
  refine (akhcRW_assembly hS0 hA0 hcK hUc hX0 hY0 hX hY hSDS hMS hTS hT0 hT1 hIAb hIDb hIG0 hGMm
    hIFb hθ0 hΘm2 hκ0 hκ hSw0 hSw hBj0 hBj hU2 hCT').trans (le_of_eq ?_)
  rw [akhcRW_Benergy]

end PerScale

end

end SuperdiffusionCLT.AKHC61.Step3
