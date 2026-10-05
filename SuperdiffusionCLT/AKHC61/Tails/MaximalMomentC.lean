/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Tails.MaximalMomentB

/-!
# Package C3 (continued): the event quantity `M⁺_{n,ρ}` and its second moment

The statements `e.this.is.so.nice.again` and `e.mathcalM.m.rho.bound` of [AK], for the
one-sided event quantity at the paper's deterministic normalization `bfAhom(cu_h)`:

`akhcMM_Mplus n h ρ ω = sup_{Q.scale ≤ n, centre in cu_n} 3^{-ρ(n - Q.scale)} ·
  |(bfAhom(cu_h)^{-1/2} bfA(Q; ω) bfAhom(cu_h)^{-1/2} - I)_+|`

(the positive part read as the Loewner excess `akhcTailEll_excess`).

The main theorem `akhcMM_Mplus_secondMoment_le` gives a measurable, integrable `G` with
`M⁺(ω)² ≤ G(ω)` at **every** sample, the supremum's index set bounded above at every sample, and

`∫ G ≤ 3 K_{Ψ_S}^{36} (H n^D)² 3^{-2(ρ-γ)(n-k₀+1)} / (min{3,p_{Ψ_S}} - 2)
       + η/(η-2) · K_Ψ^{3⌈η⌉²} K_Ψ^{2·3⌈η⌉²/η} ω_h² / (1 - 3^{-(2ρ - 2d/η)})`.

**The layer-cake SOURCE_GAP of node 12.** The source combines the two tail bounds ("combining
the previous two displays") by a tail integral of `P[M > t]`. Here it is replaced by a pointwise
inequality, `(sup)² ≤ Y² + Σ_{k ∈ [k₀, n]} G_k²` (`akhcMM_sSup_sq_le`), where `Y` dominates every
small-scale term (C1: a single random variable, uniformly in `Q`) and `G_k` is the weighted maximum
over the `3^{d(n-k)}` cubes at scale `k` (C2). Integrating is then linearity of the expectation
over finitely many terms; no tail integral is needed.

**What is not claimed.** `∫ M⁺²` itself is not stated: measurability of
`ω ↦ akhcTailEll_excess (bfAhom) (bfA(Q; ω))` is not established here, so the statement is the
domination `M⁺² ≤ G` by an explicit integrable `G`, which is what every consumer uses.
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

/-- **`M⁺_{n,ρ}` at the paper's normalization `bfAhom(cu_h)`** (`e.event.moreproto`),
the one-sided quantity of `MaximizerBridgeC.lean` with the deterministic annealed reference. -/
def akhcMM_Mplus {d : ℕ} (nu : ℝ) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (n h : ℕ)
    (rho : ℝ) (omega : ShellSeq d) : ℝ :=
  SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC_eventMoreprotoPlus ((n : ℕ) : ℤ) rho
    (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
    (coefficientCutoff nu omega L).toCoeffField

/-- The weight of `M⁺`'s defining supremum, in the `rpow` form used by C1 and C2. -/
theorem akhcMM_weight_eq (n : ℕ) (rho s : ℝ) :
    Real.rpow (3 : ℝ) (-rho * ((((n : ℕ) : ℤ) : ℝ) - s)) = (3 : ℝ) ^ (-(rho * ((n : ℝ) - s))) := by
  rw [Real.rpow_eq_pow]
  congr 1
  push_cast
  ring

/-! ## Integrability of the two dominating pieces -/

/-- A weighted `IsBigO` variable with `2 < p ≤ p_Ψ` (growth on `1 < p`) is square-integrable. -/
theorem akhcMM_integrable_sq_of_isBigO {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Psi : ℝ → ℝ} {K pPsi p A : ℝ} (hK : 1 ≤ K)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t)
    (hGrowth : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
    (hp : 2 < p) (hpPsi : p ≤ pPsi) (hA : 0 < A) {X : Ω → ℝ} (hXm : Measurable X)
    (hX : IsBigO μ Psi X A) (w : ℝ) :
    Integrable (fun ω => (w * X ω) ^ 2) μ := by
  have hi := SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_abs_rpow_of_isBigO hK hPsiOne
    hGrowth hA hXm hX (p := p) (q := 2) (by linarith only [hp]) hpPsi (by norm_num) hp
  have heq : (fun ω => (w * X ω) ^ 2) = fun ω => w ^ 2 * |X ω| ^ (2 : ℝ) := by
    funext ω
    rw [Real.rpow_two, sq_abs, mul_pow]
  rw [heq]
  exact hi.const_mul _

/-! ## The main theorem -/

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

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **Nodes 12 and 11: the second moment of `M⁺_{n,ρ}`.** Under `0 < ν`, `Prefix`, `J2`, `J4`,
V3's (P2′) and (P3′) clauses (verbatim), the window `m₃ ≤ h`, `βn < h`,
`h < k₀ - L₁ log(L₂h)`, and the exponent conditions `γ ≤ ρ`, `2 < η ≤ p_Ψ`, `2ρ - 2d/η > 0`:
there is an integrable `G` dominating `M⁺(ω)²` at every sample, the supremum defining `M⁺(ω)` is
over a set bounded above at every sample, and `∫ G` is at most the (P2′) term plus the (P3′) term
of `e.mathcalM.m.rho.bound`, with the exponents C1 and C2 prove. -/
theorem akhcMM_Mplus_secondMoment_le
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
    {n h k0 : ℕ} (hhn : h ≤ n) (hn_m2 : m2 ≤ n) (hn_pos : 0 < n) (hk0n : k0 ≤ n)
    (hm3 : m3 ≤ h) (hbeta : beta * (n : ℝ) < (h : ℝ))
    (hwin : (h : ℝ) < (k0 : ℝ) - L1 * Real.log (L2 * (h : ℝ)))
    {rho eta : ℝ} (hgammarho : gamma ≤ rho) (heta2 : 2 < eta) (hetaPsi : eta ≤ pPsi)
    (hc : 0 < 2 * rho - 2 * (d : ℝ) / eta) :
    ∃ G : ShellSeq d → ℝ, Integrable G P.toMeasure ∧
      (∀ omega : ShellSeq d, akhcMM_Mplus nu L P n h rho omega ^ 2 ≤ G omega) ∧
      (∀ omega : ShellSeq d, BddAbove {M : ℝ | ∃ Q : TriadicCube d, Q.scale ≤ ((n : ℕ) : ℤ) ∧
        cubeCenter Q ∈ cubeSet (originCube d ((n : ℕ) : ℤ)) ∧
        M = Real.rpow (3 : ℝ) (-rho * ((((n : ℕ) : ℤ) : ℝ) - (Q.scale : ℝ))) *
          akhcTailEll_excess (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
            (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)}) ∧
      ∫ omega, G omega ∂P.toMeasure ≤
        3 * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-2 * (rho - gamma) * ((n : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) +
          (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
            KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * omegaSeq h ^ 2 *
            (1 - (3 : ℝ) ^ (-(2 * rho - 2 * (d : ℝ) / eta)))⁻¹ := by
  -- (P2′) range, package C1.
  obtain ⟨X, hXm, hXbig, hptw, hint⟩ :=
    akhcTailEllB_normalizedExcess_moment_le hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hhn hn_m2 hn_pos
      (rho := rho) (hprime := (k0 : ℝ) - 1) hgammarho
  set B : ℝ := (3 : ℝ) ^ (-(rho - gamma) * ((n : ℝ) - ((k0 : ℝ) - 1))) with hBdef
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by norm_num) _
  -- (P3′) range: the translate-indexed family.
  have hfam := akhcMM_cfs_family hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 beta L1 L2 m3 omegaSeq Psi
    hbeta0 hL1 hL2 hP3 (n := n) hm3 hbeta hwin
  choose Xf hXf using hfam
  let S : ℕ → Finset (TriadicCube d) :=
    fun k => descendantsAtScale (originCube d (n : ℤ)) ((min k n : ℕ) : ℤ)
  have hSne : ∀ k, (S k).Nonempty := fun k => akhcMM_descendantsAtScale_nonempty n k
  have hSmem : ∀ k, k ≤ n → ∀ Q, Q ∈ S k ↔ Q ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ) := by
    intro k hkn Q
    simp only [S, min_eq_left hkn]
  let Gk : ℕ → ShellSeq d → ℝ := fun k omega =>
    (3 : ℝ) ^ (-(rho * ((n : ℝ) - (k : ℝ)))) * (S k).sup' (hSne k) (fun Q => Xf k Q omega)
  let Y : ShellSeq d → ℝ := fun omega => B * |X omega|
  let f : ShellSeq d → TriadicCube d → ℝ := fun omega Q =>
    Real.rpow (3 : ℝ) (-rho * ((((n : ℕ) : ℤ) : ℝ) - (Q.scale : ℝ))) *
      akhcTailEll_excess (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
        (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField)
  have hf0 : ∀ omega Q, 0 ≤ f omega Q := fun omega Q =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (akhcTailEll_excess_nonneg _ _)
  have hsmall : ∀ omega (Q : TriadicCube d), Q.scale ≤ (n : ℤ) →
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) → Q.scale < (k0 : ℤ) → f omega Q ≤ Y omega := by
    intro omega Q hQn hQc hQk0
    have hQr : (Q.scale : ℝ) ≤ (k0 : ℝ) - 1 := by
      have h1 : Q.scale ≤ (k0 : ℤ) - 1 := by omega
      have h2 := (Int.cast_le (R := ℝ)).2 h1
      push_cast at h2
      exact h2
    have h2 := hptw omega Q hQn hQr hQc
    have hl0 : 0 ≤ (3 : ℝ) ^ (-(rho * ((n : ℝ) - (Q.scale : ℝ)))) *
        akhcTailEll_excess (annealedBlockMatrix nu L P (cubeSet (originCube d (h : ℤ))))
          (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (akhcTailEll_excess_nonneg _ _)
    have h3 := (Real.rpow_le_rpow_iff hl0 (mul_nonneg hB0 (abs_nonneg _))
      (by norm_num : (0 : ℝ) < 2)).1 h2
    show Real.rpow _ _ * _ ≤ B * |X omega|
    rw [akhcMM_weight_eq]
    exact h3
  have hlarge : ∀ omega (k : ℕ), k0 ≤ k → k ≤ n →
      ∀ Q ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ), f omega Q ≤ Gk k omega := by
    intro omega k hk0k hkn Q hQ
    have hQs := akhcMM_scale_of_mem_descendantsAtScale hQ
    have hQS : Q ∈ S k := (hSmem k hkn Q).2 hQ
    obtain ⟨-, -, hbound⟩ := hXf k Q hk0k hkn hQs
    have hw0 : 0 ≤ (3 : ℝ) ^ (-(rho * ((n : ℝ) - (k : ℝ)))) := Real.rpow_nonneg (by norm_num) _
    show Real.rpow _ _ * _ ≤ _
    rw [akhcMM_weight_eq, hQs, Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left
      ((hbound omega).trans (Finset.le_sup' (fun Q => Xf k Q omega) hQS)) hw0
  have hdom : ∀ omega, akhcMM_Mplus nu L P n h rho omega ^ 2 ≤
      Y omega ^ 2 + ∑ k ∈ Finset.Icc k0 n, Gk k omega ^ 2 := fun omega =>
    akhcMM_sSup_sq_le n k0 (f omega) (hf0 omega) (hsmall omega) (fun k => Gk k omega)
      (hlarge omega)
  -- Integrability of the two pieces.
  have hH0 : 0 < H * (n : ℝ) ^ D :=
    mul_pos (by linarith only [hH]) (Real.rpow_pos_of_pos (by exact_mod_cast hn_pos) D)
  have hYint : Integrable (fun omega => Y omega ^ 2) P.toMeasure :=
    akhcMM_integrable_sq_of_isBigO hKPsiS hPsiSOne (akhcMM_growth_ext hpPsiS hGrowth)
      (p := min 3 pPsiS) (lt_min (by norm_num) hpPsiS) (min_le_right _ _) hH0
      (continuous_abs.measurable.comp hXm) (by simpa only [IsBigO, abs_abs, Function.comp_apply] using hXbig) B
  have hmemAll : ∀ k, k0 ≤ k → k ≤ n → ∀ Q ∈ S k,
      Measurable (Xf k Q) ∧ IsBigO P.toMeasure Psi (Xf k Q) (omegaSeq h) := by
    intro k hk0k hkn Q hQ
    obtain ⟨h1, h2, -⟩ := hXf k Q hk0k hkn
      (akhcMM_scale_of_mem_descendantsAtScale ((hSmem k hkn Q).1 hQ))
    exact ⟨h1, h2⟩
  have hGint : ∀ k ∈ Finset.Icc k0 n, Integrable (fun omega => Gk k omega ^ 2) P.toMeasure := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hsupbig := SuperdiffusionCLT.AKHC61.Carrier.akhc_isBigO_finset_sup_of_isBigO hKPsi
      hPsiOne hGrowthPsi (p := eta) (by linarith only [heta2]) hetaPsi (hSne k) (homega h)
      (fun Q hQ => (hmemAll k hk.1 hk.2 Q hQ).2)
    have hsupm : Measurable (fun omega => (S k).sup' (hSne k) (fun Q => Xf k Q omega)) := by
      have hm := (S k).measurable_sup' (hSne k) (fun Q hQ => (hmemAll k hk.1 hk.2 Q hQ).1)
      have hfun : (fun omega => (S k).sup' (hSne k) (fun Q => Xf k Q omega)) =
          (S k).sup' (hSne k) (Xf k) := by
        funext omega
        rw [Finset.sup'_apply]
      rw [hfun]
      exact hm
    have hA : 0 < KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * ((S k).card : ℝ) ^ (1 / eta) *
        omegaSeq h := by
      have h1 : 0 < KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) :=
        Real.rpow_pos_of_pos (by linarith only [hKPsi]) _
      have h2 : (0 : ℝ) < ((S k).card : ℝ) ^ (1 / eta) :=
        Real.rpow_pos_of_pos (by exact_mod_cast (hSne k).card_pos) _
      exact mul_pos (mul_pos h1 h2) (homega h)
    exact akhcMM_integrable_sq_of_isBigO hKPsi hPsiOne hGrowthPsi heta2 hetaPsi hA hsupm
      hsupbig _
  obtain ⟨hint_all, heq⟩ := akhcMM_integral_dominator n k0 Y Gk hYint hGint
  refine ⟨fun omega => Y omega ^ 2 + ∑ k ∈ Finset.Icc k0 n, Gk k omega ^ 2, hint_all, hdom,
    fun omega => akhcMM_bddAbove n k0 (f omega) (hsmall omega) (fun k => Gk k omega)
      (hlarge omega), ?_⟩
  rw [heq]
  have hC1 : ∫ omega, Y omega ^ 2 ∂P.toMeasure ≤
      3 * KPsiS ^ 36 * (H * (n : ℝ) ^ D) ^ (2 : ℝ) *
        (3 : ℝ) ^ (-2 * (rho - gamma) * ((n : ℝ) - ((k0 : ℝ) - 1))) / (min 3 pPsiS - 2) := by
    have hfun : (fun omega => Y omega ^ 2) = fun omega => (B * |X omega|) ^ (2 : ℝ) := by
      funext omega
      rw [Real.rpow_two]
    rw [hfun]
    exact hint
  have hcard : ∀ k, k0 ≤ k → k ≤ n → ((S k).card : ℝ) = ((3 : ℝ) ^ d) ^ (n - k) := by
    intro k _ hkn
    simp only [S, min_eq_left hkn]
    exact akhcMM_card_descendantsAtScale hkn
  have hC2 := akhcCfs_scaleSum_secondMoment_le hKPsi hPsiOne hGrowthPsi
    (by linarith only [heta2]) heta2 hetaPsi (d := d) hk0n (rho := rho)
    (c := 2 * rho - 2 * (d : ℝ) / eta) rfl hc hSne hcard (homega h)
    (fun k hk0k hkn Q hQ => (hmemAll k hk0k hkn Q hQ).1)
    (fun k hk0k hkn Q hQ => (hmemAll k hk0k hkn Q hQ).2)
  exact add_le_add hC1 hC2

end

end SuperdiffusionCLT.AKHC61.Tails
