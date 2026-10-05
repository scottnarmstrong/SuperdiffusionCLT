/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeD
public import SuperdiffusionCLT.AKHC61.Step2.JBoundSkeletonB

/-!
# Package C6, part 5: the deterministic coefficients at the Step 2 scales

At the parent scale `m` with `b = σ̄_m`, `c = σ̄*⁻¹_m`, `σ̂ = (b/c)^{1/2}`, `u = Θ_m^{1/2}`, and the
reference `E = Ahom(cu_h) = diag(σ̄_h, σ̄*⁻¹_h)` with the pigeonhole closeness
`σ̄_h ≤ (1+δ₁) b`, `σ̄*⁻¹_h ≤ (1+δ₁) c`:

* `σ̂ |E_LR| + σ̂⁻¹ |E_UL| ≤ 2(1+δ₁) u` (the mismatch/low-scale prefactor `κ`);
* `B_J(E) ≤ (1+δ₁) u + 1`;
* the constant-tail energy is at most `8·3^{-(m-k)} Θ_m`;
* the geometric weight sums are bounded by `(1 - 3^{-a})⁻¹`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-! ## Geometric weight sums (retyped from `CoarseGraining`'s private
`sum_range_to_Icc_descending`, `sum_Icc_betaWeight_le_geometric_inv`) -/

theorem akhcPrime_sum_range_to_Icc {k m : ℤ} (hkm : k ≤ m) (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (Int.toNat (m - k)), F j) =
      ∑ n ∈ Finset.Icc (k + 1) m, F (Int.toNat (m - n)) := by
  classical
  refine Finset.sum_bij (fun j _hj => m - (j : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hL : ((Int.toNat (m - k) : ℕ) : ℤ) = m - k :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hkm)
    have hj_lt_nat : j < Int.toNat (m - k) := Finset.mem_range.mp hj
    have hj_lt' : (j : ℤ) < ((Int.toNat (m - k) : ℕ) : ℤ) := by exact_mod_cast hj_lt_nat
    rw [hL] at hj_lt'
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro j₁ _ j₂ _ h
    have h' : m - (j₁ : ℤ) = m - (j₂ : ℤ) := h
    have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by omega
    exact_mod_cast hcast
  · intro n hn
    have hn_low : k + 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_high : n ≤ m := (Finset.mem_Icc.mp hn).2
    refine ⟨Int.toNat (m - n), ?_, ?_⟩
    · apply Finset.mem_range.mpr
      omega
    · have hto : ((Int.toNat (m - n) : ℕ) : ℤ) = m - n :=
        Int.toNat_of_nonneg (sub_nonneg.mpr hn_high)
      change m - ((Int.toNat (m - n) : ℕ) : ℤ) = n
      rw [hto]
      ring
  · intro j _
    have harg : Int.toNat (m - (m - (j : ℤ))) = j := by
      have hsub : m - (m - (j : ℤ)) = (j : ℤ) := by ring
      rw [hsub, Int.toNat_natCast]
    rw [harg]

/-- `Σ_{n ∈ (k, m]} 3^{-a (m-n)} ≤ (1 - 3^{-a})⁻¹` for `a > 0`. -/
theorem akhcPrime_geom_le {k m : ℤ} (hkm : k ≤ m) {a : ℝ} (ha : 0 < a) :
    (∑ n ∈ Finset.Icc (k + 1) m, Real.rpow (3 : ℝ) (-a * (Int.toNat (m - n) : ℝ))) ≤
      (1 - Real.rpow (3 : ℝ) (-a))⁻¹ := by
  rw [← akhcPrime_sum_range_to_Icc hkm (fun j => Real.rpow (3 : ℝ) (-a * (j : ℝ)))]
  set r : ℝ := Real.rpow (3 : ℝ) (-a) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ha])
  have hterm : ∀ j : ℕ, Real.rpow (3 : ℝ) (-a * (j : ℝ)) = r ^ j := by
    intro j
    rw [hr]
    exact Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) (-a) j
  simp only [hterm]
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := Int.toNat (m - k)) hr0 hr1
  rw [pow_zero, one_div] at h
  rw [Finset.range_eq_Ico]
  exact h

/-! ## Scalar identities for the geometric mean -/

/-- `σ̂ c = (bc)^{1/2}` and `σ̂⁻¹ b = (bc)^{1/2}` for `σ̂ = (b c⁻¹)^{1/2}`. -/
theorem akhcPrime_sigmaHat_mul {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (b * c⁻¹) * c = Real.sqrt (b * c) ∧
      (Real.sqrt (b * c⁻¹))⁻¹ * b = Real.sqrt (b * c) := by
  have hs : 0 < Real.sqrt (b * c⁻¹) := Real.sqrt_pos.2 (mul_pos hb (inv_pos.2 hc))
  have hsq : Real.sqrt (b * c⁻¹) ^ 2 = b * c⁻¹ := Real.sq_sqrt (mul_pos hb (inv_pos.2 hc)).le
  have h1 : Real.sqrt (b * c⁻¹) * c = Real.sqrt (b * c) := by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (mul_pos hb hc).le (mul_pos hs hc).le]
    have : Real.sqrt (b * c⁻¹) * c * (Real.sqrt (b * c⁻¹) * c) =
        Real.sqrt (b * c⁻¹) ^ 2 * c * c := by ring
    rw [this, hsq]
    field_simp
  refine ⟨h1, ?_⟩
  have hbc : b = Real.sqrt (b * c⁻¹) ^ 2 * c := by rw [hsq]; field_simp
  calc (Real.sqrt (b * c⁻¹))⁻¹ * b = (Real.sqrt (b * c⁻¹))⁻¹ * (Real.sqrt (b * c⁻¹) ^ 2 * c) := by
        rw [← hbc]
    _ = Real.sqrt (b * c⁻¹) * c := by field_simp
    _ = Real.sqrt (b * c) := h1

/-- The special vectors: `|p|² = σ̂⁻¹`, `|q|² = σ̂`, `p·q = 1` for a unit `e`. -/
theorem akhcPrime_special_norms {d : ℕ} {σ : ℝ} (hσ : 0 < σ) {e : Vec d} (he : vecNormSq e = 1) :
    vecNormSq (σ ^ (-(1 / 2) : ℝ) • e) = σ⁻¹ ∧ vecNormSq (σ ^ (1 / 2 : ℝ) • e) = σ ∧
      vecDot (σ ^ (-(1 / 2) : ℝ) • e) (σ ^ (1 / 2 : ℝ) • e) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vecNormSq_smul, he, mul_one, akhcPrime_rpow_neg_half_sq hσ.le]
  · rw [vecNormSq_smul, he, mul_one, akhcPrime_rpow_half_sq hσ.le]
  · rw [vecDot_smul_left, vecDot_smul_right]
    have he' : vecDot e e = 1 := he
    rw [he', mul_one, ← Real.rpow_add hσ]
    norm_num

/-! ## The reference `E = Ahom(cu_h)` -/

section Reference

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hJ4 in
theorem akhcPrime_matrixNorm_lowerRight (h : ℤ)
    (hc : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d h))) :
    Book.Ch02.matrixNorm (annealedBlockMatrix nu L P (cubeSet (originCube d h))).lowerRight =
      sigmaBarStarInvScalar nu L P (cubeSet (originCube d h)) := by
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
    hnu L hJ4 h]
  exact Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg hc

include hnu hJ4 in
theorem akhcPrime_matrixNorm_upperLeft (h : ℤ)
    (hb : 0 ≤ sigmaBarScalar nu L P (cubeSet (originCube d h))) :
    Book.Ch02.matrixNorm (annealedBlockMatrix nu L P (cubeSet (originCube d h))).upperLeft =
      sigmaBarScalar nu L P (cubeSet (originCube d h)) := by
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
    hnu L hJ4 h]
  exact Book.Ch05.Section52.matrixNorm_smul_one_eq_of_nonneg hb

include hnu hJ4 in
theorem akhcPrime_Bj_eq (h : ℤ) (p q : Vec d) :
    akhcWNSq_Bj (annealedBlockMatrix nu L P (cubeSet (originCube d h))) p q =
      (1 / 2 : ℝ) * (sigmaBarScalar nu L P (cubeSet (originCube d h)) * vecNormSq p +
        sigmaBarStarInvScalar nu L P (cubeSet (originCube d h)) * vecNormSq q) +
        |vecDot p q| := by
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
    hnu L hJ4 h]
  unfold akhcWNSq_Bj
  simp only [blockVecDot, blockMatVecMul, Book.Ch02.blockDiag, akhc_matVecMul_smul_one,
    akhc_matVecMul_zero_block, add_zero, zero_add, vecDot_smul_right]
  have hn : vecDot (-p) (-p) = vecNormSq p := by
    simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]
  rw [show (-p : Vec d) = -p from rfl, hn]
  rfl

end Reference

/-! ## The cutoff-law layer: (P2') context -/

section Law

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (L : ℕ)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
        (H * (j : ℝ) ^ D) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                  omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                  X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet
                  (Homogenization.originCube d (j : ℤ)))))
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **The `τ`-defect at the special vectors under the pigeonhole closeness.** If
`σ̄_n ≤ (1+δ) σ̄_m` and `σ̄*⁻¹_n ≤ (1+δ) σ̄*⁻¹_m`, then `τ_{m,n} ≤ δ Θ_m^{1/2}`. -/
theorem akhcPrime_tau_le (m n : ℕ) (e : Vec d) (he : vecNormSq e = 1) {δ : ℝ}
    (hbn : sigmaBarSeq nu L P n ≤ (1 + δ) * sigmaBarSeq nu L P m)
    (hcn : sigmaBarStarInvSeq nu L P n ≤ (1 + δ) * sigmaBarStarInvSeq nu L P m) :
    Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ) (n : ℤ)
        (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) ≤
      δ * Real.sqrt (sigmaBarSeq nu L P m * sigmaBarStarInvSeq nu L P m) := by
  have hb := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hc := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 m
  have hEJ := fun j : ℕ => SuperdiffusionCLT.AKHC61.Step2.akhcJB_expectedJ_originCube_eq hnu
    P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 hJ4 j (akhcSpecialPAtScale nu L P (m : ℤ) e)
      (akhcSpecialQAtScale nu L P (m : ℤ) e)
  have hτ : Book.Ch05.tauAtScale (cutoffLaw (d := d) nu L P) (m : ℤ) (n : ℤ)
      (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) =
      Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) (originCube d (n : ℤ))
          (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) -
        Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P) (originCube d (m : ℤ))
          (akhcSpecialPAtScale nu L P (m : ℤ) e) (akhcSpecialQAtScale nu L P (m : ℤ) e) := rfl
  rw [hτ, hEJ n, hEJ m]
  set σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  have hσ : 0 < σ := akhcPrime_sigmaHat_pos (m := (m : ℤ)) hb hc
  obtain ⟨hpp, hqq, hpq⟩ := akhcPrime_special_norms hσ he
  set p := akhcSpecialPAtScale nu L P (m : ℤ) e
  set q := akhcSpecialQAtScale nu L P (m : ℤ) e
  have hpp' : vecDot p p = σ⁻¹ := hpp
  have hqq' : vecDot q q = σ := hqq
  have hpq' : vecDot p q = 1 := hpq
  simp only [vecDot_smul_right p p, vecDot_smul_right q q, hpp', hqq', hpq']
  obtain ⟨h1, h2⟩ := akhcPrime_sigmaHat_mul hb hc
  have hσdef : σ = Real.sqrt (sigmaBarSeq nu L P m * (sigmaBarStarInvSeq nu L P m)⁻¹) := rfl
  rw [← hσdef] at h1 h2
  have hc' : sigmaBarStarInvSeq nu L P n * σ ≤ (1 + δ) * (sigmaBarStarInvSeq nu L P m * σ) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcn hσ.le
  have hb' : sigmaBarSeq nu L P n * σ⁻¹ ≤ (1 + δ) * (sigmaBarSeq nu L P m * σ⁻¹) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbn (inv_pos.2 hσ).le
  have e1 : sigmaBarStarInvSeq nu L P m * σ = Real.sqrt (sigmaBarSeq nu L P m *
      sigmaBarStarInvSeq nu L P m) := by rw [mul_comm]; exact h1
  have e2 : sigmaBarSeq nu L P m * σ⁻¹ = Real.sqrt (sigmaBarSeq nu L P m *
      sigmaBarStarInvSeq nu L P m) := by rw [mul_comm]; exact h2
  rw [e1] at hc'
  rw [e2] at hb'
  have hm1 : (1 / 2 : ℝ) * (sigmaBarStarInvSeq nu L P m * σ) - 1 +
      (1 / 2 : ℝ) * (sigmaBarSeq nu L P m * σ⁻¹) = Real.sqrt (sigmaBarSeq nu L P m *
        sigmaBarStarInvSeq nu L P m) - 1 := by rw [e1, e2]; ring
  have hA : (1 / 2 : ℝ) * (sigmaBarStarInvSeq nu L P m * σ) - 1 +
      (1 / 2 : ℝ) * (sigmaBarSeq nu L P m * σ⁻¹) =
      (1 / 2 : ℝ) * (σ * sigmaBarStarInvSeq nu L P m) - 1 +
      (1 / 2 : ℝ) * (σ⁻¹ * sigmaBarSeq nu L P m) := by ring
  nlinarith only [hc', hb', hm1, hA]

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **The constant-tail energy.** `σ̂ K_G² + σ̂⁻¹ K_F² ≤ 8·3^{-(m-k)} Θ_m`. -/
theorem akhcPrime_constTail_le (m k : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    akhcPrime_constTail nu L P m k e ≤
      8 * Real.rpow (3 : ℝ) (-(Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) *
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
  have hb := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hc := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 m
  have hθ1 := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma
    H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  set b := sigmaBarSeq nu L P m
  set c := sigmaBarStarInvSeq nu L P m
  have hθ : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m = b * c := rfl
  rw [hθ] at hθ1 ⊢
  set σ := akhcSigmaHatAtScale nu L P (m : ℤ)
  have hσ : 0 < σ := akhcPrime_sigmaHat_pos (m := (m : ℤ)) hb hc
  obtain ⟨h1, h2⟩ := akhcPrime_sigmaHat_mul hb hc
  have hσdef : σ = Real.sqrt (b * c⁻¹) := rfl
  rw [← hσdef] at h1 h2
  set u := Real.sqrt (b * c)
  have hu2 : u * u = b * c := Real.mul_self_sqrt (mul_pos hb hc).le
  have hu1 : 1 ≤ u := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hθ1
  set r := σ ^ (1 / 2 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hσ _
  have hrr : r * r = σ := by rw [← sq]; exact akhcPrime_rpow_half_sq hσ.le
  have hri : σ ^ (-(1 / 2) : ℝ) = r⁻¹ := Real.rpow_neg hσ.le _
  have hp : akhcSpecialPAtScale nu L P (m : ℤ) e = r⁻¹ • e := by
    rw [← hri]; rfl
  have hq : akhcSpecialQAtScale nu L P (m : ℤ) e = r • e := rfl
  have hcS : sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) = c := rfl
  have hbS : sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) = b := rfl
  have hp0 : sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) •
      akhcSpecialQAtScale nu L P (m : ℤ) e - akhcSpecialPAtScale nu L P (m : ℤ) e =
      (c * r - r⁻¹) • e := by rw [hcS, hp, hq, smul_smul, ← sub_smul]
  have hq0 : akhcSpecialQAtScale nu L P (m : ℤ) e -
      sigmaBarScalar nu L P (cubeSet (originCube d (m : ℤ))) •
        akhcSpecialPAtScale nu L P (m : ℤ) e = (r - b * r⁻¹) • e := by
    rw [hbS, hp, hq, smul_smul, ← sub_smul]
  have hnp := SuperdiffusionCLT.AKHC61.Step2.akhcJB_norm_smul_le he (c * r - r⁻¹)
  have hnq := SuperdiffusionCLT.AKHC61.Step2.akhcJB_norm_smul_le he (r - b * r⁻¹)
  unfold akhcPrime_constTail
  rw [hp0, hq0]
  unfold Book.Ch05.Section53.WeakNormsMaximizer.gradientConstantTailAtScale
    Book.Ch05.Section53.WeakNormsMaximizer.fluxConstantTailAtScale
  set t := Real.rpow (3 : ℝ) (-(1 / 2) * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ))
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have htt : t * t = Real.rpow (3 : ℝ) (-(Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) := by
    show (3 : ℝ) ^ (-(1 / 2) * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) *
      (3 : ℝ) ^ (-(1 / 2) * (Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ)) =
        (3 : ℝ) ^ (-(Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ))
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  -- the two weighted squares
  have hA : σ * (c * r - r⁻¹) ^ 2 ≤ b * c := by
    have hid : σ * (c * r - r⁻¹) ^ 2 = (σ * c - 1) ^ 2 := by
      rw [← hrr]; field_simp
    have e1 : σ * c = u := h1
    rw [hid, e1, ← hu2]
    nlinarith only [hu1]
  have hB : σ⁻¹ * (r - b * r⁻¹) ^ 2 ≤ b * c := by
    have hid : σ⁻¹ * (r - b * r⁻¹) ^ 2 = (1 - σ⁻¹ * b) ^ 2 := by
      rw [← hrr]; field_simp
    rw [hid, h2, ← hu2]
    nlinarith only [hu1]
  have hnp2 : ‖(c * r - r⁻¹) • e‖ ^ 2 ≤ (c * r - r⁻¹) ^ 2 := by
    rw [← sq_abs (c * r - r⁻¹)]
    exact pow_le_pow_left₀ (norm_nonneg _) hnp 2
  have hnq2 : ‖(r - b * r⁻¹) • e‖ ^ 2 ≤ (r - b * r⁻¹) ^ 2 := by
    rw [← sq_abs (r - b * r⁻¹)]
    exact pow_le_pow_left₀ (norm_nonneg _) hnq 2
  have hsq1 : ((1 / 2 : ℝ)⁻¹ * t * ‖(c * r - r⁻¹) • e‖) ^ 2 =
      4 * (t * t) * ‖(c * r - r⁻¹) • e‖ ^ 2 := by ring
  have hsq2 : ((1 / 2 : ℝ)⁻¹ * t * ‖(r - b * r⁻¹) • e‖) ^ 2 =
      4 * (t * t) * ‖(r - b * r⁻¹) • e‖ ^ 2 := by ring
  rw [hsq1, hsq2, htt]
  set T := Real.rpow (3 : ℝ) (-(Int.toNat ((m : ℤ) - (k : ℤ)) : ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hσi : 0 ≤ σ⁻¹ := (inv_pos.2 hσ).le
  have k1 := mul_le_mul_of_nonneg_left hnp2 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
    hT) hσ.le)
  have k2 := mul_le_mul_of_nonneg_left hnq2 (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
    hT) hσi)
  have k3 := mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hT)
  have k4 := mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hT)
  nlinarith only [k1, k2, k3, k4]

end Law

end

end SuperdiffusionCLT.AKHC61.WeakNorms
