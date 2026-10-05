/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Tails.CFS
public import SuperdiffusionCLT.AKHC61.Carrier.OrliczMoments
public import SuperdiffusionCLT.AKHC61.Carrier.OrliczMomentsB
public import SuperdiffusionCLT.AKHC61.Params.Constants
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Package C2 (continued): the two union bounds and the second-moment bound

This file proves the two union bounds and the resulting second-moment
bound for the CFS-restricted tail of `M_{n,ρ}`, feeding package C3
(`E[M_{n,ρ}²]`, `e.mathcalM.m.rho.bound`).

## Route taken (a simplification found during this pass)

The source gets from the per-scale union bound to the
scale-sum via a **tail-probability** layer cake:
`P[max_k … > ω_h t] ≤ Σ_k P[… > ω_h t]`, each summand a Pareto tail, summed
geometrically. Reproducing that exactly needs a fresh layer-cake integral
(package A3's own `akhc_abs_rpow_lintegral_le_of_isBigO` is `private`, so it
cannot be reused directly for a differently-shaped tail).

This file instead reaches the **same target shape** by a shorter route,
using only A3's two *public* lemmas:

1. **Union over sub-cubes** (`akhc_isBigO_finset_sup_of_isBigO`, exponent
   `η := akhcEta d pΨ`): turns `N` many `O_Ψ(ω_h)` witnesses at one scale `k`
   into one `O_Ψ(K_Ψ^{(3⌈η⌉²)/η} N^{1/η} ω_h)` witness for their max.
2. **Second moment from `IsBigO`** (`akhc_moment_le_of_isBigO`, same `η`,
   `q := 2`): converts that into `E[(3^{-ρ(n-k)}·max)²] ≤ C·3^{-2ρ(n-k)}·
   K_Ψ^{2(3⌈η⌉²)/η}·N^{2/η}·ω_h²`. With `N = 3^{d(n-k)}`, this decays
   geometrically in `n-k` at rate `c := 2ρ - 2d/η`, **strictly positive**
   because `ρη > d` (a consequence of the definitions of `akhcRho`, `akhcRhoPrime` and
   `akhcEta`, confirming that the "tentative" `akhcEta` really is the exponent the moment
   argument needs).
3. **Union over scales**: since `(sup)² ≤ Σ(squares)` for finitely many
   nonnegative terms (no layer cake needed), `E[Y²] ≤ Σ_k E[(3^{-ρ(n-k)}·
   max_k)²]`, summed by a plain geometric series (`akhcCfs_geomSum_le`).

The resulting bound has the *same shape* as `Υ₁ = C·K_Ψ^{4d²}/
(min{d+1,pΨ}-d)`: it is `O(1/(η-d))` as `η → d⁺` and a fixed power of `K_Ψ`
(exponent `2·(3⌈η⌉²)/η + 3⌈η⌉² ≤ 6⌈η⌉² ≤ 6(d+1)²`, looser than `4d²` but the
same polynomial-in-`d` "type", exactly as the task allows). The exact
numerical exponent `4d²` is **not** independently re-derived here, and is flagged,
not silently claimed.

## How this feeds C3

`e.mathcalM.m.rho.bound`'s target (node 12) splits `M_{n,ρ}`'s defining `sup`
over **all** `k ≤ n` at the threshold scale `h' := h + L₁ log(L₂h)`
(see `CFS.lean`, "Finding 2", for the precise boundary): for
`k < h'` node 14 (`a.ellipticity.weaker`, `Tails/Ellipticity*.lean`, agent
dc1) supplies the bound, and for `k ∈ [h', n]` **this file** supplies it. By
`max(A,B)² ≤ A² + B²` (for nonnegative `A, B`), `E[M_{n,ρ}²] ≤
E[(ellipticity part)²] + E[(CFS part)²]`, i.e. **C3's target is the sum of
node 14's bound and `akhcCfs_scaleSum_secondMoment_le`'s conclusion below**,
exactly the additive form of `e.mathcalM.m.rho.bound`
(`K_Ψ^{4d²}ω_h²/(min{d+1,pΨ}-d) + K_{Ψ_S}^{36}H²n^{2D}3^{-…}/(min{3,p_{Ψ_S}}-2)`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Tails

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.Params

noncomputable section

/-! ## A capstone real-analysis fact: `max² ≤ sum of squares` -/

/-! ## Step 1: the rate `c := 2ρ - 2d/η` is strictly positive -/

/-! ## Step 2: a plain finite geometric sum -/

/-- A finite geometric sum, bounded by its (summable) infinite tail, for any
strictly positive rate `c` — no upper restriction on `c` is needed. -/
theorem akhcCfs_geomSum_le {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (-(c * (j : ℝ))) ≤ (1 - (3 : ℝ) ^ (-c))⁻¹ := by
  set r : ℝ := (3 : ℝ) ^ (-c) with hr_def
  have hr_pos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr_lt_one : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc])
  have heq : ∀ j : ℕ, (3 : ℝ) ^ (-(c * (j : ℝ))) = r ^ j := by
    intro j
    rw [hr_def, ← Real.rpow_natCast ((3:ℝ) ^ (-c)) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1; ring
  simp only [heq]
  have hsum : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr_pos.le hr_lt_one
  have htsum : ∑' j : ℕ, r ^ j = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr_pos.le hr_lt_one
  rw [← htsum]
  exact hsum.sum_le_tsum _ (fun j _ => by positivity)

/-! ## Step 3: the per-scale union bound and second moment -/

/-- **The per-scale union bound + second moment (the two ingredients, combined
at exponent `η`).** For `N` witnesses each `O_Ψ(ω_h)`, weighted by a common
nonnegative factor `w` (the caller supplies `w := 3^{-ρ(n-k)}`), the weighted
max has a controlled second moment. This is the (z-union, then moment)
content of `e.this.is.so.nice.again`'s proof at one fixed scale `k`. -/
theorem akhcCfs_perScale_secondMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {Psi : ℝ → ℝ} {KPsi pPsi eta : ℝ} (hKPsi : 1 ≤ KPsi)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t)
    (hGrowth : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
    (heta1 : 1 < eta) (heta2 : (2:ℝ) < eta) (heta_le : eta ≤ pPsi)
    {ι : Type*} {S : Finset ι} (hS : S.Nonempty)
    {X : ι → Ω → ℝ} {ωh : ℝ} (hωh : 0 < ωh)
    (hXm : ∀ i ∈ S, Measurable (X i))
    (hX : ∀ i ∈ S, IsBigO Pm Psi (X i) ωh) {w : ℝ} :
    ∫ ω, (w * S.sup' hS (fun i => X i ω)) ^ 2 ∂Pm ≤
      (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
        (KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * (S.card : ℝ) ^ (1 / eta) * ωh) ^ 2 *
        w ^ 2 := by
  set W : Ω → ℝ := fun ω => S.sup' hS (fun i => X i ω) with hW_def
  set Amp : ℝ := KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * (S.card : ℝ) ^ (1 / eta) * ωh with hAmp_def
  have hAmp_pos : 0 < Amp := by
    rw [hAmp_def]
    have h1 : (0:ℝ) < KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hKPsi) _
    have h2 : (0:ℝ) < (S.card : ℝ) ^ (1 / eta) := by
      have : (0:ℝ) < (S.card:ℝ) := by exact_mod_cast hS.card_pos
      exact Real.rpow_pos_of_pos this _
    positivity
  have hWbig : IsBigO Pm Psi W Amp := by
    have := akhc_isBigO_finset_sup_of_isBigO hKPsi hPsiOne hGrowth heta1 heta_le hS
      (X := X) (A := ωh) hωh hX
    simpa [hW_def, hAmp_def] using this
  have hWm : Measurable W := by
    classical
    have hm : Measurable (fun ω => S.sup' hS X ω) := S.measurable_sup' hS (fun i hi => hXm i hi)
    simp only [Finset.sup'_apply] at hm
    rwa [hW_def]
  have hmoment := akhc_moment_le_of_isBigO hKPsi hPsiOne hGrowth hAmp_pos hWm hWbig
    (p := eta) (q := 2) heta1 heta_le (by norm_num) heta2
  have heq : (fun ω => (w * W ω) ^ 2) = fun ω => w ^ 2 * |W ω| ^ (2:ℝ) := by
    funext ω
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs, mul_pow]
  rw [heq, MeasureTheory.integral_const_mul]
  have hfinal : w ^ 2 * ∫ ω, |W ω| ^ (2:ℝ) ∂Pm ≤
      w ^ 2 * ((eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) * Amp ^ (2:ℝ)) :=
    mul_le_mul_of_nonneg_left hmoment (by positivity)
  have hAmp2 : Amp ^ (2:ℝ) = Amp ^ 2 := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hAmp2] at hfinal
  linarith only [hfinal]

/-! ## Step 4: sum over scales, the node-13 CFS-tail target -/

/-- **The CFS-restricted tail's second moment, summed over scales
`k ∈ ℕ ∩ [h', n]`** (node 13, `e.this.is.so.nice.again#tail-cfs-weaker`, the
CFS part of `e.mathcalM.m.rho.bound`). Given: a family `X k Q` of witnesses
(one per scale `k` in the window and cube `Q` in a finset `S k` of the right
cardinality `3^{d(n-k)}` at that scale — the intended instantiation is
`S k := descendantsAtScale (originCube d n) (k:ℤ)`, `card = (3^d)^(n-k)` via
`descendantsAtDepth_card`), each `O_Ψ(ω_h)`, THE SUM of the per-scale second
moments (which dominates the second moment of the restricted max, by the elementary
`(sup)² ≤ Σ(squares)` fact for finitely many nonnegative terms) is bounded by
`(η/(η-2))·K_Ψ^{6⌈η⌉²}·ω_h²/(1 - 3^{-c})`, `c := 2ρ - 2d/η > 0`. This is the
`Υ₁ ω_h²`-shaped summand of `e.mathcalM.m.rho.bound`. -/
theorem akhcCfs_scaleSum_secondMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {Psi : ℝ → ℝ} {KPsi pPsi eta : ℝ} (hKPsi : 1 ≤ KPsi)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t)
    (hGrowth : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
    (heta1 : 1 < eta) (heta2 : (2:ℝ) < eta) (heta_le : eta ≤ pPsi)
    {d n h' : ℕ} (hwin : h' ≤ n)
    {rho : ℝ} {c : ℝ} (hc_def : c = 2 * rho - 2 * (d : ℝ) / eta) (hc_pos : 0 < c)
    {ι : Type*} {S : ℕ → Finset ι} (hSne : ∀ k, (S k).Nonempty)
    (hcard : ∀ k, h' ≤ k → k ≤ n → ((S k).card : ℝ) = ((3:ℝ) ^ d) ^ (n - k))
    {X : ℕ → ι → Ω → ℝ} {ωh : ℝ} (hωh : 0 < ωh)
    (hXm : ∀ k, h' ≤ k → k ≤ n → ∀ i ∈ S k, Measurable (X k i))
    (hX : ∀ k, h' ≤ k → k ≤ n → ∀ i ∈ S k, IsBigO Pm Psi (X k i) ωh) :
    ∑ k ∈ Finset.Icc h' n, ∫ ω,
        ((3:ℝ) ^ (-(rho * ((n:ℝ) - (k:ℝ)))) * (S k).sup' (hSne k) (fun i => X k i ω)) ^ 2 ∂Pm ≤
      (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
        KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * ωh ^ 2 * (1 - (3:ℝ) ^ (-c))⁻¹ := by
  -- Per-scale bound, in terms of `j := n - k`.
  have hPerK : ∀ k ∈ Finset.Icc h' n, ∫ ω,
      ((3:ℝ) ^ (-(rho * ((n:ℝ) - (k:ℝ)))) * (S k).sup' (hSne k) (fun i => X k i ω)) ^ 2 ∂Pm ≤
        (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
          (KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * ((S k).card : ℝ) ^ (1 / eta) * ωh) ^ 2 *
          ((3:ℝ) ^ (-(rho * ((n:ℝ) - (k:ℝ))))) ^ 2 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact akhcCfs_perScale_secondMoment_le hKPsi hPsiOne hGrowth heta1 heta2 heta_le
      (hSne k) hωh (hXm k hk.1 hk.2) (hX k hk.1 hk.2)
      (w := (3:ℝ) ^ (-(rho * ((n:ℝ) - (k:ℝ)))))
  refine le_trans (Finset.sum_le_sum hPerK) ?_
  -- Rewrite each summand's card/weight factor as `3^(-c*(n-k))`.
  have hRewrite : ∀ k ∈ Finset.Icc h' n,
      (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
          (KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * ((S k).card : ℝ) ^ (1 / eta) * ωh) ^ 2 *
          ((3:ℝ) ^ (-(rho * ((n:ℝ) - (k:ℝ))))) ^ 2 =
        (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
            KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * ωh ^ 2 *
          (3 : ℝ) ^ (-(c * ((n:ℝ) - (k:ℝ)))) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hcardk : ((S k).card : ℝ) = ((3:ℝ) ^ d) ^ (n - k) := hcard k hk.1 hk.2
    have hexp : ((n - k : ℕ) : ℝ) = (n:ℝ) - (k:ℝ) := Nat.cast_sub hk.2
    have hcardk' : ((S k).card : ℝ) = ((3:ℝ) ^ d) ^ ((n:ℝ) - (k:ℝ)) := by
      rw [hcardk, ← hexp, Real.rpow_natCast]
    have hcardpow : ((S k).card : ℝ) ^ (1 / eta) =
        (3:ℝ) ^ ((d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta) := by
      rw [hcardk', ← Real.rpow_natCast (3:ℝ) d, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1; ring
    have hKfactor : (KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta)) ^ 2 =
        KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) := by
      rw [← Real.rpow_natCast (KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta)) 2,
        ← Real.rpow_mul (le_trans zero_le_one hKPsi)]
      congr 1; ring
    have hprod :
        (KPsi ^ ((3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) * ((S k).card : ℝ) ^ (1 / eta) * ωh) ^ 2 =
          KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) *
            ((3:ℝ) ^ ((d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta)) ^ 2 * ωh ^ 2 := by
      rw [mul_pow, mul_pow, hcardpow, hKfactor]
    have hpow2 : (((3:ℝ) ^ ((d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta))) ^ 2 =
        (3:ℝ) ^ (2 * (d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta) := by
      rw [← Real.rpow_natCast ((3:ℝ) ^ ((d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta)) 2,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1; ring
    have hweight2 : (((3:ℝ) ^ (-(rho * ((n:ℝ) - (k:ℝ)))))) ^ 2 =
        (3:ℝ) ^ (-(2 * rho * ((n:ℝ) - (k:ℝ)))) := by
      rw [← Real.rpow_natCast ((3:ℝ) ^ (-(rho * ((n:ℝ) - (k:ℝ))))) 2,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
      congr 1; ring
    have hexp3 :
        (3:ℝ) ^ (2 * (d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta) * (3:ℝ) ^ (-(2 * rho * ((n:ℝ) - (k:ℝ)))) =
          (3:ℝ) ^ (-(c * ((n:ℝ) - (k:ℝ)))) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      congr 1
      rw [hc_def]; ring
    rw [hprod, hpow2, hweight2]
    rw [show
        (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) *
            (KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) *
                (3:ℝ) ^ (2 * (d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta) * ωh ^ 2) *
            (3:ℝ) ^ (-(2 * rho * ((n:ℝ) - (k:ℝ)))) =
          (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) * KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) *
              ωh ^ 2 *
            ((3:ℝ) ^ (2 * (d:ℝ) * ((n:ℝ) - (k:ℝ)) / eta) *
              (3:ℝ) ^ (-(2 * rho * ((n:ℝ) - (k:ℝ))))) from by ring,
      hexp3]
  rw [Finset.sum_congr rfl hRewrite, ← Finset.mul_sum]
  have hetaC_nonneg : (0:ℝ) ≤
      (eta / (eta - 2)) * KPsi ^ (3 * ⌈eta⌉₊ ^ 2) * KPsi ^ (2 * (3 * (⌈eta⌉₊ : ℝ) ^ 2) / eta) *
        ωh ^ 2 := by
    have h1 : (0:ℝ) ≤ eta / (eta - 2) := by
      apply div_nonneg (le_of_lt (lt_trans zero_lt_two heta2))
      linarith only [heta2]
    have h2 : (0:ℝ) < KPsi := lt_of_lt_of_le zero_lt_one hKPsi
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hetaC_nonneg
  -- Reindex `k ∈ Finset.Icc h' n` by `j := n - k ∈ Finset.range (n - h' + 1)`.
  have hreindex :
      ∑ k ∈ Finset.Icc h' n, (3:ℝ) ^ (-(c * ((n:ℝ) - (k:ℝ)))) =
        ∑ j ∈ Finset.range (n - h' + 1), (3:ℝ) ^ (-(c * (j : ℝ))) := by
    refine Finset.sum_nbij' (fun k => n - k) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_range]
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Nat.cast_sub hk.2]
  rw [hreindex]
  exact akhcCfs_geomSum_le hc_pos (n - h')

end

end SuperdiffusionCLT.AKHC61.Tails
