/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.ProtoD
public import SuperdiffusionCLT.AKHC61.Variance.CFSApplied
public import SuperdiffusionCLT.AKHC61.Step3.AlgebraicComparison

/-!
# Package E2: `e.variance.again.prime` (node 50), the lag made explicit

`e.variance.again.prime` of [AK] (proof of Theorem `t.weaker.P3`, Step 3).

## What this file assembles

Two already proved pieces:

* `akhcProtoD_variance_quadratic` (`Variance/ProtoD.lean`): for `k ≤ n`,
  `k ≤ m`, `w_m := Sum.elim σ̄_m σ̄*⁻¹_m`,
  `E|A(cu_n) - W_m|²_{w_m} ≤ 512d²(Θ̂_k-1)² + 32 E|avsum(A(z+cu_k)) - Ahom_k|²_{w_m}`,
  carrying `hLinInt` at `w_m`.
* `akhc_CFS_weaker_applied` (`Variance/CFSApplied.lean`): in the strict
  `(P3′)` window `β n < k < n - L₁log(L₂k)`,
  `E|avsum(A(z+cu_k)) - Ahom_k|²_{w_k} ≤ (2d)²(pΨ/(pΨ-2))K_Ψ^{3⌈pΨ⌉₊²}ω_k²`,
  at `w_k := akhcMatDiag(Ahom(cu_k))`, the **inner** scale `k`, not `w_m`.

**The normalizations differ** (`w_m` vs `w_k`): this is the genuine content
package E1 (`Step3.AlgebraicComparison`) is cited for in the paper
("by `a.CFS.weaker` **and** `e.algebraic.add.error.again`"). Converting
`|·|²_{w_k}` into `|·|²_{w_m}` via `akhc_relFrobSq_le_of_le_mul` costs a
factor `Θ̂_k²` (from E1's `σ̄_k/σ̄_m - 1 ≤ Θ̂_k - Θ̂_m ≤ Θ̂_k - 1`, using
`Θ̂_m ≥ 1`). **This factor is not visible in the printed display** (whose
`CK_Ψ^{27}ω_k²` carries no extra `Θ̂_k` dependence) — either the source
absorbs it silently into the numeric exponent `27`, or (more likely, since
`Θ̂_k` is controlled inductively, not by this lemma alone) a uniform bound
`Θ̂_k ≤ B` from elsewhere (e.g. Step 1's `Θ̂_{m₁+2m₀} ≤ 1+σ` plus monotonicity)
is silently used at the point of application. **REFUTE-FIRST FINDING**:
package E2 cannot derive `Θ̂_k ≤ B` on its own — no such hypothesis is in the
allowed list (0<ν≤1, Prefix, J2, J4, (P2′), (P3′), A4 parameters) — so this
file states the bound **honestly with the `Θ̂_k²` factor explicit**
(`akhcVA_variance_again_prime`). The clean form matching exactly what the paper
prints follows **conditionally on an external `Θ̂_k ≤ B` hypothesis**. The stated form makes ℓ's
role fully visible, with no silent `3^{κℓ}`-style drop: `κ` never appears here, only the
explicit lag `akhcProtoLag L1 L2 n` (`Variance/ProtoB.lean`).

## The window: strict, one scale inside (C2's finding)

A non-strict window can contain a point at which `(P3′)`'s own strict hypothesis
fails (a boundary coincidence found by C2). Instantiating `k := n - akhcProtoLag L1 L2 n`,
the derived strict inequality `k < n - L1 log(L2 k)` (`akhcVA_window2_of_window1` below) holds
unconditionally from `β n < n - ℓ(n)` (giving `ℓ(n) < n`) together with the
mild side condition `1 < L2 n` (ensuring `ℓ(n) ≥ 1`, so `k < n` strictly, the
"one scale inside" C2 asked for); without `1 < L2 n` the degenerate
coincidence `L2 n = 1` reproduces exactly C2's boundary failure.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Section4
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.Variance

noncomputable section

variable {d : ℕ}

/-! ## Part 1: `akhcCFSLinEntry = akhcProtoLinearAvg`, the same average -/

/-- **`CFSApplied.lean`'s CFS linear average and `ProtoB.lean`'s proto linear
average are the same function.** Both are `avsum_R (A(R) - Ahom(cu_k))` over
`R` ranging over the depth-`(n-k)` descendants of `cu_n`; this file needs both
names (`ProtoD` consumes the latter, `CFSApplied` produces the former). -/
theorem akhcVA_cfsLinEntry_eq_protoLinearAvg [NeZero d] (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (k n : ℕ) :
    akhcCFSLinEntry nu L P k n = akhcProtoLinearAvg nu P L k n := rfl

/-! ## Part 2: the strict `(P3′)` window at `k := n - ℓ(n)` -/

/-- **`ℓ(n) < n` from `β n < n - ℓ(n)`.** No positivity of `L1, L2` is
needed: only `0 ≤ β`. -/
theorem akhcVA_lag_lt_of_window1 (L1 L2 : ℝ) (n : ℕ) {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hwin1 : beta * (n : ℝ) < (n : ℝ) - (akhcProtoLag L1 L2 n : ℝ)) :
    akhcProtoLag L1 L2 n < n := by
  have hβn : (0 : ℝ) ≤ beta * (n : ℝ) := mul_nonneg hbeta0 (Nat.cast_nonneg n)
  have : (akhcProtoLag L1 L2 n : ℝ) < (n : ℝ) := by linarith only [hβn, hwin1]
  exact_mod_cast this

/-- **The natural-number lag scale `k := n - ℓ(n)` casts additively.** -/
theorem akhcVA_lag_cast (L1 L2 : ℝ) (n : ℕ) (h : akhcProtoLag L1 L2 n < n) :
    ((n - akhcProtoLag L1 L2 n : ℕ) : ℝ) = (n : ℝ) - (akhcProtoLag L1 L2 n : ℝ) :=
  Nat.cast_sub h.le

/-- **`ℓ(n) ≥ 1` from `1 < L₂ n`.** With `L1 ≥ 1`, `L1 log(L2 n) > 0`, so its
ceiling is a positive natural number. -/
theorem akhcVA_one_le_lag (L1 L2 : ℝ) (n : ℕ) (hL1 : 1 ≤ L1)
    (hL2n : 1 < L2 * (n : ℝ)) :
    1 ≤ akhcProtoLag L1 L2 n := by
  have hlog : 0 < Real.log (L2 * (n : ℝ)) := Real.log_pos hL2n
  have hL1pos : (0 : ℝ) < L1 := by linarith only [hL1]
  have hpos : 0 < L1 * Real.log (L2 * (n : ℝ)) := mul_pos hL1pos hlog
  have hceil : (0 : ℝ) < (akhcProtoLag L1 L2 n : ℝ) :=
    lt_of_lt_of_le hpos (Nat.le_ceil (L1 * Real.log (L2 * (n : ℝ))))
  exact_mod_cast hceil

/-- **The strict `(P3′)` window at `k := n - ℓ(n)`, one scale inside
(the boundary failure found by C2, avoided here by `1 < L2 n`).**
Given `0 ≤ β`, `1 ≤ L1`, `1 ≤ L2`, `1 < L2 n`, and `β n < n - ℓ(n)`, the
instantiated scale `k := n - ℓ(n)` satisfies `k < n - L1 log(L2 k)`
strictly. -/
theorem akhcVA_window2_of_window1 (L1 L2 : ℝ) (n : ℕ) {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hL2n : 1 < L2 * (n : ℝ))
    (hwin1 : beta * (n : ℝ) < (n : ℝ) - (akhcProtoLag L1 L2 n : ℝ)) :
    ((n - akhcProtoLag L1 L2 n : ℕ) : ℝ) <
      (n : ℝ) - L1 * Real.log (L2 * ((n - akhcProtoLag L1 L2 n : ℕ) : ℝ)) := by
  set ℓ := akhcProtoLag L1 L2 n with hℓ_def
  have hℓlt : ℓ < n := akhcVA_lag_lt_of_window1 L1 L2 n hbeta0 hwin1
  have hcast : ((n - ℓ : ℕ) : ℝ) = (n : ℝ) - (ℓ : ℝ) := akhcVA_lag_cast L1 L2 n hℓlt
  have hℓ1 : 1 ≤ ℓ := akhcVA_one_le_lag L1 L2 n hL1 hL2n
  have hL1pos : (0 : ℝ) < L1 := by linarith only [hL1]
  have hL2pos : (0 : ℝ) < L2 := by linarith only [hL2]
  have hknlt : ((n - ℓ : ℕ) : ℝ) < (n : ℝ) := by
    rw [hcast]
    have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
    linarith only [this]
  have hkpos : (0 : ℝ) < ((n - ℓ : ℕ) : ℝ) := by
    rw [hcast]
    have hβn : (0 : ℝ) ≤ beta * (n : ℝ) := mul_nonneg hbeta0 (Nat.cast_nonneg n)
    linarith only [hβn, hwin1]
  have hL2klt : L2 * ((n - ℓ : ℕ) : ℝ) < L2 * (n : ℝ) :=
    mul_lt_mul_of_pos_left hknlt hL2pos
  have hL2kpos : (0 : ℝ) < L2 * ((n - ℓ : ℕ) : ℝ) := mul_pos hL2pos hkpos
  have hloglt : Real.log (L2 * ((n - ℓ : ℕ) : ℝ)) < Real.log (L2 * (n : ℝ)) :=
    Real.log_lt_log hL2kpos hL2klt
  have hL1loglt : L1 * Real.log (L2 * ((n - ℓ : ℕ) : ℝ)) < L1 * Real.log (L2 * (n : ℝ)) :=
    mul_lt_mul_of_pos_left hloglt hL1pos
  have hceil : L1 * Real.log (L2 * (n : ℝ)) ≤ (ℓ : ℝ) := Nat.le_ceil _
  linarith only [hcast, hL1loglt, hceil]

/-! ## Part 3: the shared `(P2′)`/`(P3′)` hypothesis block -/

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (hJ4 : ShellLawJ4 d P) (L : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hd : 2 ≤ d)
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
  (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)
  (homegaPos : ∀ k' : ℕ, 0 < omegaSeq k') (homegaAnti : Antitone omegaSeq)
  (homegaTendsto : Filter.Tendsto omegaSeq Filter.atTop (nhds 0))
  (hPsiMono : StrictMonoOn Psi (Set.Ici 0)) (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t)
  (hKPsi : 1 ≤ KPsi) (hpPsi : (d : ℝ) < pPsi)
  (hGrowthP3 : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
    (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
      ∀ (omega : ShellSeq d) (p q : BlockVec d),
        2 *
            (((descendantsAtDepth (originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtDepth (originCube d (j : ℤ)) (j - n),
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
          X omega *
            (blockVecDot p
                (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q
                (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)))

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-! ## Part 4: measurability of the `w`-relative squared linear average -/

/-- **`akhcRelFrobSq w (akhcProtoLinearAvg ...)` is a.e. strongly measurable,
for any (deterministic) positive diagonal `w`.** Same derivation as
`CFSApplied.lean`'s `hFrobMeas`, entrywise from `(P2′)`'s integrability
(package A1); `w` itself carries no randomness, so the argument does not
depend on which normalizer `w` is used. -/
theorem akhcVA_linAvg_relFrobSq_aestronglyMeasurable {k n : ℕ} (w : BlockCoord d → ℝ) :
    AEStronglyMeasurable
      (fun omega => akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega)) P.toMeasure := by
  have hIntA1 := akhc_integrable_blockMatEntry_of_P2 d hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
  have hLinMeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun omega => akhcProtoLinearAvg nu P L k n omega α β)
        P.toMeasure := by
    intro α β
    unfold akhcProtoLinearAvg
    have hSumMeas : AEStronglyMeasurable (fun omega =>
        ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
          (blockMatEntry (coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField) α β -
            blockMatEntry (annealedBlockMatrix nu L P
              (cubeSet (originCube d (k : ℤ)))) α β)) P.toMeasure :=
      Finset.aestronglyMeasurable_fun_sum _ fun R _ =>
        (hIntA1 R α β).aestronglyMeasurable.sub aestronglyMeasurable_const
    exact hSumMeas.const_mul _
  unfold akhcRelFrobSq
  refine Finset.aestronglyMeasurable_fun_sum _ fun α _ => ?_
  refine Finset.aestronglyMeasurable_fun_sum _ fun β _ => ?_
  exact ((continuous_pow 2).div_const _).comp_aestronglyMeasurable (hLinMeas α β)

include hPrefix hJ2 hJ4

/-! ## Part 5: change of normalization `w_k → w_m`, cost `Θ̂_k²` (E1 + A2) -/

/-- **The `w_m`-relative squared Frobenius norm of any `M` is bounded by
`Θ̂_k² ·` its `w_k`-relative squared Frobenius norm, for `k ≤ m`.** From E1's
ratio comparisons `σ̄_k/σ̄_m - 1 ≤ Θ̂_k - Θ̂_m` (and the `σ̄*⁻¹` twin) together
with `Θ̂_m ≥ 1` (node 60), `σ̄_k ≤ Θ̂_k · σ̄_m` (and the twin), so
`akhc_relFrobSq_le_of_le_mul` applies with `c := Θ̂_k`. This is the genuine
content behind the paper's "by `a.CFS.weaker` and `e.algebraic.add.error.again`":
**the `Θ̂_k²` factor is real** and is not present in the printed
`CK_Ψ^{27}ω_k²` bound, so it must be absorbed elsewhere (a uniform bound on
`Θ̂_k`) or carried explicitly, as this file does. -/
theorem akhcVA_relFrobSq_w_le {k m : ℕ} (hkm : k ≤ m)
    (M : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelFrobSq
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m) (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        M ≤
      (thetaCutoff nu L P k) ^ 2 *
        akhcRelFrobSq
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P k) (fun _ : Fin d => sigmaBarStarInvSeq nu L P k))
          M := by
  have hsmPos := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have htmPos := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hskPos := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have htkPos := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hΘm1 := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hratioS := akhc_algebraic_comparison_sigmaBar_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hratioT := akhc_algebraic_comparison_sigmaBarStarInv_of_P2 hnu hPrefix hJ2 hJ4 gamma H
    D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    hkm
  have hsRatio : sigmaBarSeq nu L P k / sigmaBarSeq nu L P m ≤ thetaCutoff nu L P k := by
    linarith only [hratioS, hΘm1]
  have htRatio :
      sigmaBarStarInvSeq nu L P k / sigmaBarStarInvSeq nu L P m ≤ thetaCutoff nu L P k := by
    linarith only [hratioT, hΘm1]
  have hsLe : sigmaBarSeq nu L P k ≤ thetaCutoff nu L P k * sigmaBarSeq nu L P m :=
    (div_le_iff₀ hsmPos).mp hsRatio
  have htLe :
      sigmaBarStarInvSeq nu L P k ≤ thetaCutoff nu L P k * sigmaBarStarInvSeq nu L P m :=
    (div_le_iff₀ htmPos).mp htRatio
  have hw : ∀ α : BlockCoord d, 0 <
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P m) : BlockCoord d → ℝ) α := by
    intro α; cases α with
    | inl i => exact hsmPos
    | inr i => exact htmPos
  have hw' : ∀ α : BlockCoord d, 0 <
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P k)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P k) : BlockCoord d → ℝ) α := by
    intro α; cases α with
    | inl i => exact hskPos
    | inr i => exact htkPos
  have hle : ∀ α : BlockCoord d,
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P k)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P k) : BlockCoord d → ℝ) α ≤
        thetaCutoff nu L P k *
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m) : BlockCoord d → ℝ) α := by
    intro α; cases α with
    | inl i => exact hsLe
    | inr i => exact htLe
  exact akhc_relFrobSq_le_of_le_mul hw hw' hle M

omit hPrefix hJ2 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 in
/-- **`akhcMatDiag` of the annealed block matrix at the origin cube `cu_k` is
the `Sum.elim` diagonal reading `w_k`.** Bridges `CFSApplied.lean`'s own
normalizer to `ProtoD.lean`'s. -/
theorem akhcVA_matDiag_annealed_eq (k : ℕ) :
    akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) =
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P k)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P k) : BlockCoord d → ℝ) := by
  funext α
  unfold akhcMatDiag sigmaBarSeq sigmaBarStarInvSeq
  rw [akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (k : ℤ),
    akhcProtoD_blockMatEntry_blockDiag]
  simp

/-! ## Part 6: node 50, `e.variance.again.prime`, the lag explicit -/

include hd hbeta0 hbeta1 hL1 hL2 homegaPos homegaAnti homegaTendsto hPsiMono hPsiOne hKPsi
  hpPsi hGrowthP3 hP3

omit hbeta1 homegaAnti homegaTendsto hPsiMono in
/-- **Node 50, `e.variance.again.prime`, with the lag `ℓ(n) = ⌈L₁log(L₂n)⌉`
explicit (`akhcProtoLag`) and the normalization-change cost `Θ̂_k²` carried
honestly (see the file docstring: this factor is real and not visible in the
printed display).** For `n ≤ m`, `1 < L₂n` (avoiding C2's boundary
coincidence), the window entry condition `β n < n - ℓ(n)`, and `m₃ ≤ n - ℓ(n)`
(the (P3′) base-scale hypothesis at the instantiated CFS scale), with
`k := n - ℓ(n)`:
`E|Ahom^{-1/2}(cu_m)A(cu_n)Ahom^{-1/2}(cu_m) - I|² ≤ 512d²(Θ̂_k-1)² +
32 Θ̂_k² (2d)²(pΨ/(pΨ-2))K_Ψ^{3⌈pΨ⌉₊²}ω_k²`. -/
theorem akhcVA_variance_again_prime {n m : ℕ} (hnm : n ≤ m)
    (hL2n : 1 < L2 * (n : ℝ))
    (hwin1 : beta * (n : ℝ) < (n : ℝ) - (akhcProtoLag L1 L2 n : ℝ))
    (hm3 : m3 ≤ n - akhcProtoLag L1 L2 n) :
    Integrable (fun omega => akhcRelFrobSq
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField)
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m)))) P.toMeasure ∧
    ∫ omega, akhcRelFrobSq
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField)
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))) ∂P.toMeasure ≤
      512 * (d : ℝ) ^ 2 * (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n) - 1) ^ 2 +
        32 * ((thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2 *
          ((2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) *
            omegaSeq (n - akhcProtoLag L1 L2 n) ^ 2)) := by
  have hℓlt : akhcProtoLag L1 L2 n < n := akhcVA_lag_lt_of_window1 L1 L2 n hbeta0 hwin1
  have hkn : n - akhcProtoLag L1 L2 n ≤ n := Nat.sub_le n (akhcProtoLag L1 L2 n)
  have hkm : n - akhcProtoLag L1 L2 n ≤ m := hkn.trans hnm
  have hcast : ((n - akhcProtoLag L1 L2 n : ℕ) : ℝ) = (n : ℝ) - (akhcProtoLag L1 L2 n : ℝ) :=
    akhcVA_lag_cast L1 L2 n hℓlt
  have hwin1' : beta * (n : ℝ) < ((n - akhcProtoLag L1 L2 n : ℕ) : ℝ) := by
    rw [hcast]; exact hwin1
  have hwin2' : ((n - akhcProtoLag L1 L2 n : ℕ) : ℝ) <
      (n : ℝ) - L1 * Real.log (L2 * ((n - akhcProtoLag L1 L2 n : ℕ) : ℝ)) :=
    akhcVA_window2_of_window1 L1 L2 n hbeta0 hL1 hL2 hL2n hwin1
  have hcfs := akhc_CFS_weaker_applied hnu P hJ4 L hd gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 beta L1 L2 m3 omegaSeq Psi
    KPsi pPsi homegaPos hPsiOne hKPsi hpPsi hGrowthP3 hP3 hm3 hwin1' hwin2'
  rw [akhcVA_matDiag_annealed_eq (hnu := hnu) (hJ4 := hJ4),
    akhcVA_cfsLinEntry_eq_protoLinearAvg] at hcfs
  have hptwise : ∀ omega : ShellSeq d, akhcRelFrobSq
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
      (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega) ≤
      (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2 *
        akhcRelFrobSq (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P (n - akhcProtoLag L1 L2 n))
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P (n - akhcProtoLag L1 L2 n)))
          (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega) :=
    fun omega => akhcVA_relFrobSq_w_le hnu P hJ4 L hPrefix hJ2 gamma H D m2 PsiS KPsiS pPsiS
      hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm _
  have hMeasM := akhcVA_linAvg_relFrobSq_aestronglyMeasurable hnu P L gamma H D m2 PsiS
    KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2
    (k := n - akhcProtoLag L1 L2 n) (n := n)
    (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
      (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
  have hMajInt := hcfs.1.const_mul ((thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2)
  have hsmPos' := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have htmPos' := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hwmpos : ∀ α : BlockCoord d, 0 <
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P m) : BlockCoord d → ℝ) α := by
    intro α
    cases α with
    | inl i => exact hsmPos'
    | inr i => exact htmPos'
  have hLinIntM : Integrable (fun omega => akhcRelFrobSq
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
      (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega)) P.toMeasure := by
    refine hMajInt.mono' hMeasM (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg (akhc_relFrobSq_nonneg hwmpos _)]
    exact hptwise omega
  have hIntBound : ∫ omega, akhcRelFrobSq
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
      (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega) ∂P.toMeasure ≤
      (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2 *
        ((2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) *
          omegaSeq (n - akhcProtoLag L1 L2 n) ^ 2) := by
    calc ∫ omega, akhcRelFrobSq
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
          (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega) ∂P.toMeasure
        ≤ ∫ omega, (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2 *
            akhcRelFrobSq
              (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P (n - akhcProtoLag L1 L2 n))
                (fun _ : Fin d => sigmaBarStarInvSeq nu L P (n - akhcProtoLag L1 L2 n)))
              (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega) ∂P.toMeasure :=
          integral_mono hLinIntM hMajInt hptwise
      _ = (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2 *
            ∫ omega, akhcRelFrobSq
              (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P (n - akhcProtoLag L1 L2 n))
                (fun _ : Fin d => sigmaBarStarInvSeq nu L P (n - akhcProtoLag L1 L2 n)))
              (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega) ∂P.toMeasure :=
          integral_const_mul _ _
      _ ≤ (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2 *
            ((2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) *
              omegaSeq (n - akhcProtoLag L1 L2 n) ^ 2) :=
          mul_le_mul_of_nonneg_left hcfs.2 (sq_nonneg _)
  have hpd := akhcProtoD_variance_quadratic (hnu := hnu) (hPrefix := hPrefix) (hJ2 := hJ2)
    (hJ4 := hJ4) (gamma := gamma) (H := H) (D := D) (m2 := m2) (PsiS := PsiS)
    (KPsiS := KPsiS) (pPsiS := pPsiS) (hgamma0 := hgamma0) (hgamma1 := hgamma1) (hH := hH)
    (hD := hD) (hPsiSMono := hPsiSMono) (hPsiSOne := hPsiSOne) (hKPsiS := hKPsiS)
    (hpPsiS := hpPsiS) (hGrowth := hGrowth) (hP2 := hP2) (hkn := hkn) (hkm := hkm)
    (hLinInt := hLinIntM)
  refine ⟨hpd.1, ?_⟩
  calc ∫ omega, akhcRelFrobSq
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField)
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))) ∂P.toMeasure
      ≤ 512 * (d : ℝ) ^ 2 * (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n) - 1) ^ 2 +
          32 * ∫ omega, akhcRelFrobSq
            (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
              (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
            (akhcProtoLinearAvg nu P L (n - akhcProtoLag L1 L2 n) n omega) ∂P.toMeasure := hpd.2
    _ ≤ 512 * (d : ℝ) ^ 2 * (thetaCutoff nu L P (n - akhcProtoLag L1 L2 n) - 1) ^ 2 +
          32 * ((thetaCutoff nu L P (n - akhcProtoLag L1 L2 n)) ^ 2 *
            ((2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) *
              omegaSeq (n - akhcProtoLag L1 L2 n) ^ 2)) := by linarith only [hIntBound]

end

end SuperdiffusionCLT.AKHC61.Step3
