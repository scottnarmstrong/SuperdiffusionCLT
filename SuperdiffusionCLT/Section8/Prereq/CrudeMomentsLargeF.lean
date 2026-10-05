/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeE

/-!
# The fourth moment for times at least one, in polylogarithmic form

The logarithmic scale of the layer cake is at most a dimension-dependent multiple of
`log (K ^ 2 + t)`.  The fourth moment of the process started at the origin is therefore at most
`C t ^ 2 (log (K ^ 2 + t)) ^ (8 n)` with `C` depending only on the dimension, `nu`, the constant
`c0` and exponent `n` of the rough bound and on the freezing amplitude, not on `K`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set Filter
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

/-- The constant of the fourth moment bound for times at least one. -/
def crudeMomL_const (d : ℕ) [NeZero d] (nu c0 amp : ℝ) (n : ℕ) : ℝ :=
  14641 * ((crudeMomL_cut d nu c0 amp n * (1 + 2 * Real.log (1 + 2 * (d : ℝ)))) ^ (8 * n) +
    8 * Real.exp 1 * crudeMomL_budget (crudeMomL_kap d nu c0 n))

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

theorem crudeMomL_const_nonneg (nu c0 amp : ℝ) (n : ℕ) : 0 ≤ crudeMomL_const d nu c0 amp n := by
  have h1 : 1 ≤ crudeMomL_cut d nu c0 amp n := one_le_crudeMomL_cut _ _ _ _
  have h2 : 0 ≤ Real.log (1 + 2 * (d : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith only [this])
  have h3 := crudeMomL_budget_nonneg (crudeMomL_kap d nu c0 n)
  unfold crudeMomL_const
  have : 0 ≤ crudeMomL_cut d nu c0 amp n * (1 + 2 * Real.log (1 + 2 * (d : ℝ))) := by
    apply mul_nonneg (by linarith only [h1]) (by linarith only [h2])
  positivity

/-- **The fourth moment at the origin for times at least one.**  For `t ≥ 1`,
`∫ ‖y‖ ^ 4 d(S t 0) ≤ C t ^ 2 (log (K ^ 2 + t)) ^ (8 n)`. -/
theorem RoughLogBounds.crudeMomL_fourth_moment_polylog (Rb : RoughLogBounds Sp)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) {t : ℝ≥0} (ht1 : 1 ≤ t) :
    ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(R.kernelSemigroup t 0) ≤
      ENNReal.ofReal (crudeMomL_const d A.nu Rb.c0 Rb.amp Rb.n *
        Real.log (Rb.Kc ^ 2 + (t : ℝ)) ^ (8 * Rb.n) * (t : ℝ) ^ 2) := by
  refine (Rb.crudeMomL_fourth_moment R hcons hid ht1).trans (ENNReal.ofReal_le_ofReal ?_)
  have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hθ : (0 : ℝ) ≤ 2 * (d : ℝ) := by linarith only [hd0]
  set L : ℝ := Real.log (Rb.Kc ^ 2 + (t : ℝ)) with hL
  have hL1 : 1 ≤ L := crudeMomL_one_le_log Rb.two_le_Kc (by linarith only [ht1'])
  set cd : ℝ := 1 + 2 * Real.log (1 + 2 * (d : ℝ)) with hcd
  have hlog0 : 0 ≤ Real.log (1 + 2 * (d : ℝ)) := Real.log_nonneg (by linarith only [hd0])
  have hℓ : crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (t : ℝ) ≤ cd * L := by
    unfold crudeMomL_ell
    rw [hcd]
    nlinarith only [hL1, hlog0]
  have hcut1 : 1 ≤ crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n := one_le_crudeMomL_cut _ _ _ _
  have hℓ1 := (crudeMomL_ell_ge Rb.two_le_Kc hθ ht1').1
  set cu : ℝ := crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n with hcu
  set B : ℝ := crudeMomL_budget (crudeMomL_kap d A.nu Rb.c0 Rb.n) with hB
  have hB0 : 0 ≤ B := crudeMomL_budget_nonneg _
  have he : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hpow : ((cu * crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (t : ℝ)) ^ (2 * Rb.n)) ^ 4 ≤
      (cu * cd) ^ (8 * Rb.n) * L ^ (8 * Rb.n) := by
    rw [← pow_mul, show 2 * Rb.n * 4 = 8 * Rb.n by ring, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    calc cu * crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (t : ℝ) ≤ cu * (cd * L) :=
          mul_le_mul_of_nonneg_left hℓ (by linarith only [hcut1])
      _ = _ := by ring
  have hL8 : 1 ≤ L ^ (8 * Rb.n) := one_le_pow₀ hL1
  have ht2 : (0 : ℝ) ≤ (t : ℝ) ^ 2 := by positivity
  unfold crudeMomL_const
  rw [← hcu, ← hB, ← hcd]
  have hsum : ((cu * crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (t : ℝ)) ^ (2 * Rb.n)) ^ 4 +
      8 * Real.exp 1 * B ≤ ((cu * cd) ^ (8 * Rb.n) + 8 * Real.exp 1 * B) * L ^ (8 * Rb.n) := by
    have h1 : 8 * Real.exp 1 * B ≤ 8 * Real.exp 1 * B * L ^ (8 * Rb.n) := by
      calc 8 * Real.exp 1 * B = 8 * Real.exp 1 * B * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hL8 (by positivity)
    nlinarith only [hpow, h1]
  calc 14641 * ((((cu * crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (t : ℝ)) ^ (2 * Rb.n)) ^ 4 +
        8 * Real.exp 1 * B) * (t : ℝ) ^ 2)
      ≤ 14641 * ((((cu * cd) ^ (8 * Rb.n) + 8 * Real.exp 1 * B) * L ^ (8 * Rb.n)) *
        (t : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

end

end SuperdiffusionCLT.Section8
