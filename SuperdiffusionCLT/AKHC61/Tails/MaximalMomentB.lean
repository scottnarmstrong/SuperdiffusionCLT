/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Tails.MaximalMoment
public import SuperdiffusionCLT.AKHC61.Tails.CFSTranslate

/-!
# Package C3 (continued): nodes 12 and 11, the second moment of `M⁺_{n,ρ}`

Source: `e.mathcalM.m.rho.bound` and `e.this.is.so.nice.again` of [AK].

The event quantity is the paper's one-sided `M_{n,ρ}`, normalized by the
**deterministic** annealed matrix `bfAhom(cu_h)`:

`akhcMM_Mplus n h ρ ω := akhcWeakC_eventMoreprotoPlus n ρ (bfAhom(cu_h)) (a_L(ω))`,

the general form of `MaximizerBridgeC.lean`'s one-sided quantity, at the source's normalization.
(`akhcWeakC_eventMoreprotoPlus` with the random reference `bfA(cu_h; a)` would instead
normalize by the *random* `bfA(cu_h; a)`.)

The supremum over `Q` is split at the integer scale `k₀`: the scales `Q.scale < k₀` are controlled
by (P2′) through package C1 (`akhcTailEllB_normalizedExcess_moment_le`, with `hprime := k₀ - 1`),
the scales `k ∈ [k₀, n]` by (P3′) through the translation transport of `CFSTranslate.lean` and
package C2's union bounds (`akhcCfs_scaleSum_secondMoment_le`), combined by the pointwise
layer-cake replacement `akhcMM_sSup_sq_le`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Tails

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

/-! ## Deterministic helpers -/

/-- Every triadic cube is the translate of the origin cube of its own scale by its index. -/
theorem akhcMM_eq_translateCube_originCube {d : ℕ} (Q : TriadicCube d) :
    Q = translateCube Q.index (originCube d Q.scale) := by
  cases Q
  simp only [translateCube, originCube, Pi.zero_apply, zero_add]

/-- The scale of a descendant at scale `k` is `k`. -/
theorem akhcMM_scale_of_mem_descendantsAtScale {d : ℕ} {R Q : TriadicCube d} {k : ℤ}
    (hQ : Q ∈ descendantsAtScale R k) : Q.scale = k := by
  unfold descendantsAtScale at hQ
  split_ifs at hQ with hk
  · have := scale_eq_sub_of_mem_descendantsAtDepth hQ
    rw [this, Int.toNat_of_nonneg (by linarith only [hk])]
    ring
  · simp at hQ

/-- The number of descendants of `cu_n` at scale `k ≤ n` is `(3^d)^(n-k)`. -/
theorem akhcMM_card_descendantsAtScale {d : ℕ} {n k : ℕ} (hkn : k ≤ n) :
    ((descendantsAtScale (originCube d (n : ℤ)) (k : ℤ)).card : ℝ) = ((3 : ℝ) ^ d) ^ (n - k) := by
  have hk : (k : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    show (k : ℤ) ≤ (n : ℤ)
    exact_mod_cast hkn
  unfold descendantsAtScale
  rw [dite_eq_left hk, descendantsAtDepth_card]
  have htn : Int.toNat ((originCube d (n : ℤ)).scale - (k : ℤ)) = n - k := by
    show Int.toNat ((n : ℤ) - (k : ℤ)) = n - k
    omega
  rw [htn]
  push_cast
  ring

/-- The descendants of `cu_n` at scale `k ≤ n` form a nonempty set. -/
theorem akhcMM_descendantsAtScale_nonempty {d : ℕ} (n k : ℕ) :
    (descendantsAtScale (originCube d (n : ℤ)) ((min k n : ℕ) : ℤ)).Nonempty := by
  refine descendantsAtScale_nonempty (originCube d (n : ℤ)) ?_
  show ((min k n : ℕ) : ℤ) ≤ (n : ℤ)
  exact_mod_cast min_le_right k n

/-- The growth domain extension of (P2′)'s growth condition from `2 ≤ p` to `1 < p`. -/
theorem akhcMM_growth_ext {PsiS : ℝ → ℝ} {KPsiS pPsiS : ℝ} (hpPsiS : 2 < pPsiS)
    (hGrowth2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t)) :
    ∀ p : ℝ, 1 < p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t) := by
  intro p hp1 hpPsiS' t s ht hs
  rcases le_or_gt 2 p with hp2 | hp2
  · exact hGrowth2 p hp2 hpPsiS' t s ht hs
  · have hc1 : (1 : ℕ) < ⌈p⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hp1)
    have hc2 : ⌈p⌉₊ ≤ 2 := Nat.ceil_le.2 (by exact_mod_cast hp2.le)
    have hceil : ⌈p⌉₊ = ⌈(2 : ℝ)⌉₊ := by
      rw [show ⌈(2 : ℝ)⌉₊ = 2 by norm_num]
      omega
    have hsp : s ^ p ≤ s ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hs hp2.le
    rw [hceil]
    exact hsp.trans (hGrowth2 2 le_rfl (by linarith only [hpPsiS]) t s ht hs)

/-! ## Section variables: the shell law and (P2′) carried verbatim -/

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

include hnu hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- Scaling `bfAhom(cu_j)` by two coefficients `c1 ≤ c2` keeps the Loewner order (A2's
block-diagonal form and positivity of its two scalars). -/
theorem akhcMM_smul_annealed_le_smul_annealed {j : ℤ} {c1 c2 : ℝ} (hc : c1 ≤ c2) :
    BlockMatLoewnerLE (c1 • annealedBlockMatrix nu L P (cubeSet (originCube d j)))
      (c2 • annealedBlockMatrix nu L P (cubeSet (originCube d j))) := by
  have ha : 0 ≤ sigmaBarScalar nu L P (cubeSet (originCube d j)) :=
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarScalar_originCube_pos_of_P2
      hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 j).le
  have hb : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d j)) :=
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvScalar_pos_of_P2
      hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
      hpPsiS hGrowth hP2 j).le
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
        hnu L hJ4 j,
    blockSMul_blockDiag_smul_one, blockSMul_blockDiag_smul_one]
  exact SuperdiffusionCLT.AKHC61.Carrier.akhc_blockMatLoewnerLE_blockDiag_smul_one_iff.2
    ⟨mul_le_mul_of_nonneg_right hc ha, mul_le_mul_of_nonneg_right hc hb⟩

/-- A Loewner witness `bfA ⪯ (1 + x)•bfAhom(cu_j)` gives the excess bound `excess ≤ |x|`. -/
theorem akhcMM_excess_le_abs {j : ℤ} {E : BlockMat d} {x : ℝ}
    (hE : BlockMatLoewnerLE E ((1 + x) • annealedBlockMatrix nu L P (cubeSet (originCube d j)))) :
    akhcTailEll_excess (annealedBlockMatrix nu L P (cubeSet (originCube d j))) E ≤ |x| := by
  have hmono := akhcMM_smul_annealed_le_smul_annealed hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 (j := j)
    (c1 := 1 + x) (c2 := 1 + |x|) (by linarith only [le_abs_self x])
  exact akhcTailEll_excess_le_of_blockMatLoewnerLE (abs_nonneg x) (hE.trans hmono)

/-! ## The (P3′) range: a translate-indexed family of excess witnesses -/

include hPrefix hJ2 in
/-- **The CFS-range witnesses.** From V3's origin-cube (P3′) clause (copied verbatim as `hP3`),
transported to every translate by `CFSTranslate.lean` (stationarity only) and chained with
subadditivity (`CFS.lean`): for every scale `k ∈ [k₀, n]` and every cube `Q` of scale `k`, there is
a measurable `X_Q = O_Ψ(ω_h)` with `excess(bfAhom(cu_h), bfA(Q; ω)) ≤ X_Q(ω)` at every sample.
The window hypotheses are those of (P3′) at `(j, n) := (k, h)`, uniformly in `k ≥ k₀`. -/
theorem akhcMM_cfs_family
    (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ)
    (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)
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
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField) -
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
    {n h k0 : ℕ} (hm3 : m3 ≤ h) (hbeta : beta * (n : ℝ) < (h : ℝ))
    (hwin : (h : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * (h : ℝ))) :
    ∀ (k : ℕ) (Q : TriadicCube d), ∃ Xq : ShellSeq d → ℝ,
      k0 ≤ k → k ≤ n → Q.scale = (k : ℤ) →
        Measurable Xq ∧ IsBigO P.toMeasure Psi Xq (omegaSeq h) ∧
          ∀ omega : ShellSeq d,
            akhcTailEll_excess (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
              (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) ≤
            Xq omega := by
  intro k Q
  by_cases hcond : k0 ≤ k ∧ k ≤ n ∧ Q.scale = (k : ℤ)
  swap
  · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond⟩
  obtain ⟨hk0k, hkn, hQk⟩ := hcond
  have hkR : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0k
  have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hlog : 0 ≤ L1 * Real.log (L2 * (h : ℝ)) := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hpos
      have h2 : (1 : ℝ) ≤ L2 * (h : ℝ) := by nlinarith only [h1, hL2]
      exact mul_nonneg (by linarith only [hL1]) (Real.log_nonneg h2)
  have hhk : h ≤ k := by
    have : (h : ℝ) ≤ (k : ℝ) := by linarith only [hwin, hlog, hkR]
    exact_mod_cast this
  have hbk : beta * (k : ℝ) < (h : ℝ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hknR hbeta0) hbeta
  have hwk : (h : ℝ) < (k : ℝ) - L1 * Real.log (L2 * (h : ℝ)) := by
    linarith only [hwin, hkR]
  obtain ⟨X, hXm, hXbig, hXbil⟩ := hP3 k h hm3 hbk hwk
  obtain ⟨X', hX'm, hX'big, hX'loew⟩ :=
    akhcCfsT_blockMatLoewnerLE_translateCube_of_P3prime nu L hPrefix hJ2 hhk Q.index hXm hXbig
      hXbil
  refine ⟨fun omega => |X' omega|, fun _ _ _ => ⟨continuous_abs.measurable.comp hX'm, ?_, ?_⟩⟩
  · simpa only [IsBigO, abs_abs] using hX'big
  · intro omega
    have hQ : Q = translateCube Q.index (originCube d (k : ℤ)) := by
      conv_lhs => rw [akhcMM_eq_translateCube_originCube Q]
      rw [hQk]
    have hl := hX'loew omega (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)
    rw [← hQ] at hl
    exact akhcMM_excess_le_abs hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hl

end

end SuperdiffusionCLT.AKHC61.Tails
