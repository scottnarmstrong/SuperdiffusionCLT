/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Carrier.OrliczMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# AK.HC union bounds for a general weak-Orlicz tail class

This file proves package A3's item (2):

(2) a finite union / maximum bound: a max over a finset of `N` variables,
each `O_Ψ(A)` under the AK.HC growth condition, is `O_Ψ` with amplitude
`K ^ ((3⌈p⌉₊²) / p) * N ^ (1 / p) * A` (`akhc_isBigO_finset_sup_of_isBigO`).
The mechanism is Boole's inequality plus the same growth-condition argument
as `OrliczMoments.lean`'s `akhc_inv_psi_le_of_growth`: enlarging the
amplitude by a factor `C * N ^ (1/p)` forces `Ψ` at the enlarged scale up by
a factor of `N`, absorbing the `N`-term union bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Carrier

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### A pointwise fact about `Finset.sup'` and absolute value -/

private theorem akhc_abs_sup'_le_sup'_abs {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) :
    |s.sup' hs f| ≤ s.sup' hs (fun i => |f i|) := by
  obtain ⟨i0, hi0⟩ := id hs
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 : |f i0| ≤ s.sup' hs (fun i => |f i|) := Finset.le_sup' (fun i => |f i|) hi0
    have h2 : -|f i0| ≤ f i0 := neg_abs_le (f i0)
    have h3 : f i0 ≤ s.sup' hs f := Finset.le_sup' f hi0
    linarith only [h1, h2, h3]
  · exact Finset.sup'_le hs f
      (fun i hi => (le_abs_self (f i)).trans (Finset.le_sup' (fun j => |f j|) hi))

/-! ### A rpow/npow bridge for the growth-condition exponent -/

/-- `(K ^ ((3⌈p⌉₊²)/p)) ^ p = K ^ (3⌈p⌉₊²)`, bridging the `Real.rpow` scale
factor used for the finite union bound to the `Monoid.npow` exponent of the
AK.HC growth condition. -/
private theorem akhc_rpow_growthExponent_pow
    {K p : ℝ} (hK_pos : 0 < K) (hp_pos : 0 < p) :
    (K ^ ((3 * (⌈p⌉₊ : ℝ) ^ 2) / p)) ^ p = K ^ (3 * ⌈p⌉₊ ^ 2) := by
  rw [← Real.rpow_natCast K (3 * ⌈p⌉₊ ^ 2), ← Real.rpow_mul hK_pos.le]
  congr 1
  push_cast
  field_simp

/-! ### Package A3, item (2): the finite union / maximum bound -/

/-- Package A3, item (2). A max over a finset of `N := s.card` variables,
each `O_Ψ(A)` under the AK.HC growth condition (the `(P3')` shape), is
`O_Ψ` with amplitude `C · N ^ (1/p) · A`, `C := K ^ ((3⌈p⌉₊²)/p)`. This is
the union-bound mechanism used in the proof of `l.weaknorms.prime`: enlarging the amplitude by the
factor `N ^ (1/p)` (up to the growth constant `C`) exactly absorbs the
`N`-term union bound, since the growth condition forces
`Ψ(C N^{1/p} t) ≥ N Ψ(t)`. -/
theorem akhc_isBigO_finset_sup_of_isBigO
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Ψ : ℝ → ℝ} {K pPsi : ℝ} (hK : 1 ≤ K)
    (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Ψ t)
    (hGrowth : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
      s ^ p ≤ K ^ (3 * ⌈p⌉₊ ^ 2) * (Ψ (t * s) / Ψ t))
    {p : ℝ} (hp : 1 < p) (hpPsi : p ≤ pPsi)
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {X : ι → Ω → ℝ} {A : ℝ} (hA : 0 < A)
    (hX : ∀ i ∈ s, IsBigO P Ψ (X i) A) :
    IsBigO P Ψ (fun ω => s.sup' hs (fun i => X i ω))
      (K ^ ((3 * (⌈p⌉₊ : ℝ) ^ 2) / p) * (s.card : ℝ) ^ (1 / p) * A) := by
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  set Cbase : ℝ := K ^ ((3 * (⌈p⌉₊ : ℝ) ^ 2) / p) with hCbase_def
  have hCbase_one_le : 1 ≤ Cbase := by
    rw [hCbase_def]; exact Real.one_le_rpow hK (by positivity)
  have hCbase_pos : 0 < Cbase := lt_of_lt_of_le zero_lt_one hCbase_one_le
  have hN_ge_one : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hNpow_one_le : 1 ≤ (s.card : ℝ) ^ (1 / p) :=
    Real.one_le_rpow hN_ge_one (by positivity)
  have hNpow_pos : 0 < (s.card : ℝ) ^ (1 / p) := lt_of_lt_of_le zero_lt_one hNpow_one_le
  have hCN_ge_one : 1 ≤ Cbase * (s.card : ℝ) ^ (1 / p) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Cbase * (s.card : ℝ) ^ (1 / p) :=
        mul_le_mul hCbase_one_le hNpow_one_le (by norm_num) hCbase_pos.le
  set Amp : ℝ := Cbase * (s.card : ℝ) ^ (1 / p) * A with hAmp_def
  have hAmp_pos : 0 < Amp := by rw [hAmp_def]; positivity
  have hCbase_pow : Cbase ^ p = K ^ (3 * ⌈p⌉₊ ^ 2) :=
    akhc_rpow_growthExponent_pow hK_pos hp_pos
  -- The pointwise bound for the max of absolute values.
  have hMain : IsBigOWith P Ψ (fun ω => s.sup' hs (fun i => |X i ω|)) Amp := by
    intro t ht
    have hEventEq : upperTailEvent (fun ω => s.sup' hs (fun i => |X i ω|)) (Amp * t)
        = ⋃ i ∈ s, upperTailEvent (fun ω => |X i ω|) (Amp * t) := by
      ext ω
      simp only [upperTailEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.lt_sup'_iff,
        exists_prop]
    rw [hEventEq]
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
    have ht' : 1 ≤ Cbase * (s.card : ℝ) ^ (1 / p) * t := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (Cbase * (s.card : ℝ) ^ (1 / p)) * t :=
          mul_le_mul hCN_ge_one ht (by norm_num) (by positivity)
    have hsingle : ∀ i ∈ s, P.real (upperTailEvent (fun ω => |X i ω|) (Amp * t)) ≤
        (Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t))⁻¹ := by
      intro i hi
      have hbig := hX i hi ht'
      have heqarg : A * (Cbase * (s.card : ℝ) ^ (1 / p) * t) = Amp * t := by
        rw [hAmp_def]; ring
      rwa [heqarg] at hbig
    have hΨt_pos : 0 < Ψ t := lt_of_lt_of_le zero_lt_one (hPsiOne t ht0)
    -- The growth condition forces `Ψ (t * s) ≥ N * Ψ t` at `s := Cbase * N^{1/p}`.
    have hgrowth := hGrowth p hp hpPsi t (Cbase * (s.card : ℝ) ^ (1 / p)) ht hCN_ge_one
    have hspow : (Cbase * (s.card : ℝ) ^ (1 / p)) ^ p = K ^ (3 * ⌈p⌉₊ ^ 2) * (s.card : ℝ) := by
      rw [Real.mul_rpow hCbase_pos.le hNpow_pos.le, hCbase_pow]
      congr 1
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (s.card : ℝ)),
        one_div_mul_cancel (ne_of_gt hp_pos), Real.rpow_one]
    rw [hspow] at hgrowth
    have hKpow_pos : (0 : ℝ) < K ^ (3 * ⌈p⌉₊ ^ 2) := by positivity
    have hratio : (s.card : ℝ) ≤
        Ψ (t * (Cbase * (s.card : ℝ) ^ (1 / p))) / Ψ t :=
      le_of_mul_le_mul_left hgrowth hKpow_pos
    have hΨbig : (s.card : ℝ) * Ψ t ≤ Ψ (t * (Cbase * (s.card : ℝ) ^ (1 / p))) := by
      rw [le_div_iff₀ hΨt_pos] at hratio
      linarith only [hratio]
    have hΨbig' : (s.card : ℝ) * Ψ t ≤ Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t) := by
      rwa [mul_comm t (Cbase * (s.card : ℝ) ^ (1 / p))] at hΨbig
    have hΨbig_pos : 0 < Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t) := by
      have hΨt_le : Ψ t ≤ (s.card : ℝ) * Ψ t := by nlinarith only [hΨt_pos, hN_ge_one]
      exact lt_of_lt_of_le hΨt_pos (le_trans hΨt_le hΨbig')
    have hfinal : (s.card : ℝ) * (Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t))⁻¹ ≤ (Ψ t)⁻¹ := by
      rw [← sub_nonneg]
      have hkey : (Ψ t)⁻¹ - (s.card : ℝ) * (Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t))⁻¹ =
          (Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t) - (s.card : ℝ) * Ψ t) *
            ((Ψ t)⁻¹ * (Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t))⁻¹) := by
        field_simp
      rw [hkey]
      exact mul_nonneg (by linarith only [hΨbig']) (by positivity)
    calc P.real (⋃ i ∈ s, upperTailEvent (fun ω => |X i ω|) (Amp * t))
        ≤ ∑ i ∈ s, P.real (upperTailEvent (fun ω => |X i ω|) (Amp * t)) :=
          measureReal_biUnion_finset_le s _
      _ ≤ ∑ _i ∈ s, (Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t))⁻¹ := Finset.sum_le_sum hsingle
      _ = (s.card : ℝ) * (Ψ (Cbase * (s.card : ℝ) ^ (1 / p) * t))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Ψ t)⁻¹ := hfinal
  exact IsBigOWith.of_le hMain
    (fun ω => akhc_abs_sup'_le_sup'_abs s hs (fun i => X i ω))

/-! ### Package A3, item (3): the scale-sum union bound -/

end

end SuperdiffusionCLT.AKHC61.Carrier
