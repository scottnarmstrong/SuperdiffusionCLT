/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.MoreprotoSqrt
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch04.Theorems.CoarseObservables
public import Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer.AssemblyFinal

/-!
# Package B3, one-sided variant (continued): shared real-analysis machinery

Companion to `MaximizerBridgeC.lean` (task db3b follow-up). This file holds the generic,
BlockMat/Loewner-free real-analysis machinery (the growth-weighted geometric series and the
per-scale-linear-bound-to-square-root packaging) that the earlier bridge file also used, but
whose lemmas there were all `private`. Split into its own file
purely to keep both files under the 800-line cap; nothing here is specific to the one-sided
excess construction.

## Main results

* `akhcWeakC2_maximizerConst`: the constant `C(s',rho)`, in closed form.
* `akhcWeakC2_tsum_sq_le`: the shared assembly step that the two headline bounds call, made
  public so that this file can be imported by the files that prove them.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization
open Homogenization.Book

/-- **Notation normalizer.** See `MaximizerBridgeC.lean`'s own copy of this lemma for why it is
needed; duplicated here (trivial, `rfl`) rather than imported, since `MaximizerBridgeC.lean`'s
copy is `private`. -/
private theorem akhcWeakC2_rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-! ## A growth-weighted geometric series -/

private theorem akhcWeakC2_geometricDiscount_one_nonneg {s : ℝ} (hs : 0 < s) :
    0 ≤ 1 - Real.rpow (3 : ℝ) (-s) := by
  have h1 : Real.rpow (3 : ℝ) (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  linarith only [h1]

private theorem akhcWeakC2_geometricWeight_nonneg {s : ℝ} (hs : 0 < s) (j : ℕ) :
    0 ≤ Ch02.geometricWeight s 1 j := by
  unfold Ch02.geometricWeight Ch02.geometricDiscount
  have h1 : 0 ≤ 1 - Real.rpow (3 : ℝ) (-s * 1) := by
    simpa using akhcWeakC2_geometricDiscount_one_nonneg hs
  exact mul_nonneg h1 (Real.rpow_nonneg (by norm_num) _)

/-- **The growth-weighted geometric series.** For `c < s`, the series
`sum_j geometricWeight s 1 j * 3^{c j}` is summable with value
`(1 - 3^{-s}) * (1 - 3^{c - s})^{-1}`. Specializing at `c := 0` gives `sum_j geometricWeight s 1
j = 1`. -/
private theorem akhcWeakC2_hasSum_geometricWeight_rpow {s c : ℝ} (_hs : 0 < s) (hcs : c < s) :
    HasSum (fun j : ℕ => Ch02.geometricWeight s 1 j * Real.rpow (3 : ℝ) (c * (j : ℝ)))
      ((1 - Real.rpow (3 : ℝ) (-s)) * (1 - Real.rpow (3 : ℝ) (c - s))⁻¹) := by
  set r : ℝ := Real.rpow (3 : ℝ) (c - s) with hr
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr_lt_one : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hcs])
  have hweight : ∀ j : ℕ,
      Ch02.geometricWeight s 1 j * Real.rpow (3 : ℝ) (c * (j : ℝ)) =
        (1 - Real.rpow (3 : ℝ) (-s)) * r ^ j := by
    intro j
    unfold Ch02.geometricWeight Ch02.geometricDiscount
    simp only [akhcWeakC2_rpow_eq] at hr ⊢
    rw [show (-s * 1 : ℝ) = -s by ring, hr, mul_assoc,
      ← Real.rpow_natCast ((3:ℝ) ^ (c - s)) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 3),
      show (-s * (j:ℝ) + c * (j:ℝ) : ℝ) = (c - s) * (j:ℝ) by ring]
  have hfun : (fun j : ℕ => Ch02.geometricWeight s 1 j * Real.rpow (3 : ℝ) (c * (j : ℝ))) =
      fun j => (1 - Real.rpow (3 : ℝ) (-s)) * r ^ j := funext hweight
  rw [hfun]
  exact (hasSum_geometric_of_lt_one hr_nonneg hr_lt_one).mul_left _

private theorem akhcWeakC2_summable_geometricWeight_rpow {s c : ℝ} (hs : 0 < s) (hcs : c < s) :
    Summable (fun j : ℕ => Ch02.geometricWeight s 1 j * Real.rpow (3 : ℝ) (c * (j : ℝ))) :=
  (akhcWeakC2_hasSum_geometricWeight_rpow hs hcs).summable

private theorem akhcWeakC2_tsum_geometricWeight_rpow {s c : ℝ} (hs : 0 < s) (hcs : c < s) :
    (∑' j : ℕ, Ch02.geometricWeight s 1 j * Real.rpow (3 : ℝ) (c * (j : ℝ))) =
      (1 - Real.rpow (3 : ℝ) (-s)) * (1 - Real.rpow (3 : ℝ) (c - s))⁻¹ :=
  (akhcWeakC2_hasSum_geometricWeight_rpow hs hcs).tsum_eq

private theorem akhcWeakC2_tsum_geometricWeight_one {s : ℝ} (hs : 0 < s) :
    (∑' j : ℕ, Ch02.geometricWeight s 1 j) = 1 := by
  have h := akhcWeakC2_tsum_geometricWeight_rpow hs (c := 0) hs
  have heq : (fun j : ℕ => Ch02.geometricWeight s 1 j * Real.rpow (3 : ℝ) (0 * (j : ℝ))) =
      fun j => Ch02.geometricWeight s 1 j := by
    funext j
    simp only [akhcWeakC2_rpow_eq]
    simp
  rw [heq] at h
  rw [h, zero_sub]
  have hne : (1 : ℝ) - Real.rpow (3 : ℝ) (-s) ≠ 0 := by
    have hlt : Real.rpow (3 : ℝ) (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
    linarith only [hlt]
  exact mul_inv_cancel₀ hne

/-- **`geometricWeight s 1` is summable.** Stated separately (rather than inlining
`akhcWeakC2_summable_geometricWeight_rpow hs (c := 0) hs`) because the two stated types differ by
the factor `Real.rpow 3 (0 * j)`, and closing that gap needs `Real.rpow_zero`, not a
defeq/`isDefEq` check (the latter is prohibitively expensive against `Real.rpow`'s definition). -/
private theorem akhcWeakC2_summable_geometricWeight {s : ℝ} (hs : 0 < s) :
    Summable (fun j : ℕ => Ch02.geometricWeight s 1 j) := by
  have hbase := akhcWeakC2_summable_geometricWeight_rpow hs (c := 0) hs
  have heq : (fun j : ℕ => Ch02.geometricWeight s 1 j * Real.rpow (3 : ℝ) (0 * (j : ℝ))) =
      fun j => Ch02.geometricWeight s 1 j := by
    funext j
    simp only [akhcWeakC2_rpow_eq]
    simp
  rwa [heq] at hbase


/-! ## Real-analysis packaging: from a per-scale linear bound to a bound on the square root -/

private theorem akhcWeakC2_rpow_half_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.rpow (x + y) (1 / 2 : ℝ) ≤ Real.rpow x (1 / 2 : ℝ) + Real.rpow y (1 / 2 : ℝ) := by
  simp only [akhcWeakC2_rpow_eq, ← Real.sqrt_eq_rpow]
  exact akhcWeak_sqrt_add_le hx hy

private theorem akhcWeakC2_rpow_half_sq {x : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x (1 / 2 : ℝ)) ^ 2 = x := by
  simp only [akhcWeakC2_rpow_eq]
  rw [pow_two, ← Real.rpow_add' hx (by norm_num : (1 / 2 + 1 / 2 : ℝ) ≠ 0),
    show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]

/-- **The per-scale square-root bound**, `sqrt(x_j) <= sqrt(sigma) * sqrt(1+M) * (1 + 3^{rho
j/2})`, from the linear per-scale bound `x_j <= sigma * (1+M) * (1 + 3^{rho j})`. -/
private theorem akhcWeakC2_rpow_half_le_of_le {σ M ρj x : ℝ} (hσ : 0 ≤ σ) (hM : 0 ≤ M)
    (hx0 : 0 ≤ x) (hx : x ≤ σ * (1 + M) * (1 + Real.rpow (3 : ℝ) ρj)) :
    Real.rpow x (1 / 2 : ℝ) ≤
      Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
        (1 + Real.rpow (3 : ℝ) (ρj / 2)) := by
  simp only [akhcWeakC2_rpow_eq] at hx ⊢
  have h1M : (0:ℝ) ≤ 1 + M := by linarith only [hM]
  have h1c : (0:ℝ) ≤ 1 + (3:ℝ) ^ ρj := by
    have hnn := Real.rpow_nonneg (show (0:ℝ) ≤ 3 by norm_num) ρj
    linarith only [hnn]
  have hxnn : 0 ≤ σ * (1 + M) * (1 + (3:ℝ) ^ ρj) :=
    mul_nonneg (mul_nonneg hσ h1M) h1c
  have hmono : x ^ (1/2:ℝ) ≤ (σ * (1 + M) * (1 + (3:ℝ) ^ ρj)) ^ (1/2:ℝ) :=
    Real.rpow_le_rpow hx0 hx (by norm_num)
  have hsplit :
      (σ * (1 + M) * (1 + (3:ℝ) ^ ρj)) ^ (1/2:ℝ) =
        σ ^ (1/2:ℝ) * (1 + M) ^ (1/2:ℝ) * (1 + (3:ℝ) ^ ρj) ^ (1/2:ℝ) := by
    rw [Real.mul_rpow (mul_nonneg hσ h1M) h1c, Real.mul_rpow hσ h1M]
  have htail : (1 + (3:ℝ) ^ ρj) ^ (1/2:ℝ) ≤ 1 + (3:ℝ) ^ (ρj / 2) := by
    have hbase := akhcWeakC2_rpow_half_add_le (show (0:ℝ) ≤ 1 by norm_num)
      (Real.rpow_nonneg (show (0:ℝ) ≤ 3 by norm_num) ρj)
    simp only [akhcWeakC2_rpow_eq] at hbase
    have hone : (1:ℝ) ^ (1/2:ℝ) = 1 := Real.one_rpow _
    have hpow : ((3:ℝ) ^ ρj) ^ (1/2:ℝ) = (3:ℝ) ^ (ρj / 2) := by
      rw [← Real.rpow_mul (show (0:ℝ) ≤ 3 by norm_num)]
      congr 1
      ring
    rw [hone, hpow] at hbase
    exact hbase
  calc
    x ^ (1/2:ℝ) ≤ (σ * (1 + M) * (1 + (3:ℝ) ^ ρj)) ^ (1/2:ℝ) := hmono
    _ = σ ^ (1/2:ℝ) * (1 + M) ^ (1/2:ℝ) * (1 + (3:ℝ) ^ ρj) ^ (1/2:ℝ) := hsplit
    _ ≤ σ ^ (1/2:ℝ) * (1 + M) ^ (1/2:ℝ) * (1 + (3:ℝ) ^ (ρj / 2)) := by
        refine mul_le_mul_of_nonneg_left htail ?_
        exact mul_nonneg (Real.rpow_nonneg hσ _) (Real.rpow_nonneg h1M _)

/-- **The tail sum** `S(s',rho) := sum_j geometricWeight s' 1 j * 3^{rho j / 2} =
(1-3^{-s'})*(1-3^{rho/2-s'})^{-1}`. -/
noncomputable def akhcWeakC2_tailSum (s' ρ : ℝ) : ℝ :=
  (1 - Real.rpow (3 : ℝ) (-s')) * (1 - Real.rpow (3 : ℝ) (ρ / 2 - s'))⁻¹

/-- **The port's maximizer constant**, `C(s',rho) := (1+S(s',rho))^2`. -/
noncomputable def akhcWeakC2_maximizerConst (s' ρ : ℝ) : ℝ :=
  (1 + akhcWeakC2_tailSum s' ρ) ^ 2

/-- **The termwise domination**, feeding into part 1 below. -/
private theorem akhcWeakC2_termwise_le {s' ρ σ M : ℝ} (hs' : 0 < s') (hσ : 0 ≤ σ) (hM : 0 ≤ M)
    {x : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hxle : ∀ j : ℕ, x j ≤ σ * (1 + M) * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ)))) :
    ∀ j : ℕ,
      Ch02.geometricWeight s' 1 j * Real.rpow (x j) (1 / 2 : ℝ) ≤
        Ch02.geometricWeight s' 1 j *
          (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
            (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2))) := by
  intro j
  refine mul_le_mul_of_nonneg_left ?_ (akhcWeakC2_geometricWeight_nonneg hs' j)
  exact akhcWeakC2_rpow_half_le_of_le hσ hM (hx0 j) (hxle j)

/-- **Summability of the `sigma`/`M`-scaled tail series.** -/
private theorem akhcWeakC2_summable_scaledTail {s' ρ : ℝ} (σ M : ℝ) (hs' : 0 < s') (hgap : ρ / 2 < s') :
    Summable (fun j : ℕ =>
      Ch02.geometricWeight s' 1 j *
        (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
          (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)))) := by
  have hsummable1 : Summable (fun j : ℕ => Ch02.geometricWeight s' 1 j) :=
    akhcWeakC2_summable_geometricWeight hs'
  have hpteq : ∀ j : ℕ,
      Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2) =
        Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ / 2 * (j : ℝ)) := by
    intro j; congr 2; ring
  have hsummable2 : Summable (fun j : ℕ => Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)) := by
    rw [funext hpteq]
    exact akhcWeakC2_summable_geometricWeight_rpow hs' (c := ρ / 2) hgap
  have hraw : Summable (fun j : ℕ =>
      Ch02.geometricWeight s' 1 j * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2))) := by
    have hbase := hsummable1.add hsummable2
    have heq : (fun j : ℕ =>
        Ch02.geometricWeight s' 1 j + Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)) =
        fun j : ℕ => Ch02.geometricWeight s' 1 j * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)) := by
      funext j; ring
    rwa [heq] at hbase
  have heq2 : (fun j : ℕ =>
      Ch02.geometricWeight s' 1 j *
        (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
          (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)))) =
      fun j => (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ)) *
        (Ch02.geometricWeight s' 1 j * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2))) := by
    funext j; ring
  rw [heq2]
  exact hraw.mul_left _

/-- **The value of the scaled tail series's tsum.** -/
private theorem akhcWeakC2_tsum_scaledTail_eq {s' ρ : ℝ} (σ M : ℝ) (hs' : 0 < s') (hgap : ρ / 2 < s') :
    (∑' j : ℕ,
        Ch02.geometricWeight s' 1 j *
          (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
            (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)))) =
      Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) * (1 + akhcWeakC2_tailSum s' ρ) := by
  have hsummable1 : Summable (fun j : ℕ => Ch02.geometricWeight s' 1 j) :=
    akhcWeakC2_summable_geometricWeight hs'
  have hpteq : ∀ j : ℕ,
      Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2) =
        Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ / 2 * (j : ℝ)) := by
    intro j; congr 2; ring
  have hsummable2 : Summable (fun j : ℕ => Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)) := by
    rw [funext hpteq]
    exact akhcWeakC2_summable_geometricWeight_rpow hs' (c := ρ / 2) hgap
  have heq : (fun j : ℕ =>
      Ch02.geometricWeight s' 1 j *
        (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
          (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)))) =
      fun j => (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ)) *
        (Ch02.geometricWeight s' 1 j * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2))) := by
    funext j; ring
  rw [heq, tsum_mul_left]
  have hsum_split :
      (∑' j : ℕ, Ch02.geometricWeight s' 1 j * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2))) =
        1 + akhcWeakC2_tailSum s' ρ := by
    have heq2 : (fun j : ℕ => Ch02.geometricWeight s' 1 j * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2))) =
        fun j =>
          Ch02.geometricWeight s' 1 j + Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2) := by
      funext j; ring
    rw [heq2, (hsummable1.hasSum.add hsummable2.hasSum).tsum_eq]
    have h1 : (∑' j : ℕ, Ch02.geometricWeight s' 1 j) = 1 := akhcWeakC2_tsum_geometricWeight_one hs'
    have h2 :
        (∑' j : ℕ, Ch02.geometricWeight s' 1 j * Real.rpow (3 : ℝ) (ρ * (j : ℝ) / 2)) =
          akhcWeakC2_tailSum s' ρ := by
      rw [tsum_congr hpteq, akhcWeakC2_tsum_geometricWeight_rpow hs' (c := ρ / 2) hgap]
      rfl
    rw [h1, h2]
  rw [hsum_split]

/-- **Part 1 of the shared assembly step**: the comparison of the geometric-weighted
sum-of-square-roots against its dominating bound `sqrt(sigma) * sqrt(1+M) * (1+S(s',rho))`. -/
private theorem akhcWeakC2_tsum_le_bound {s' ρ σ M : ℝ} (hs' : 0 < s') (hgap : ρ / 2 < s')
    (hσ : 0 ≤ σ) (hM : 0 ≤ M) {x : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hxle : ∀ j : ℕ, x j ≤ σ * (1 + M) * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ)))) :
    (∑' j : ℕ, Ch02.geometricWeight s' 1 j * Real.rpow (x j) (1 / 2 : ℝ)) ≤
      Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
        (1 + akhcWeakC2_tailSum s' ρ) := by
  have hterm_le := akhcWeakC2_termwise_le hs' hσ hM hx0 hxle
  have hg_nonneg : ∀ j : ℕ, 0 ≤ Ch02.geometricWeight s' 1 j * Real.rpow (x j) (1 / 2 : ℝ) := fun j =>
    mul_nonneg (akhcWeakC2_geometricWeight_nonneg hs' j) (Real.rpow_nonneg (hx0 j) _)
  have hsummableRHS := akhcWeakC2_summable_scaledTail σ M hs' hgap
  have hsummableLHS :
      Summable (fun j : ℕ => Ch02.geometricWeight s' 1 j * Real.rpow (x j) (1 / 2 : ℝ)) :=
    Summable.of_nonneg_of_le hg_nonneg hterm_le hsummableRHS
  have htsum_le := Summable.tsum_le_tsum hterm_le hsummableLHS hsummableRHS
  rwa [akhcWeakC2_tsum_scaledTail_eq σ M hs' hgap] at htsum_le

/-- **Part 2 of the shared assembly step**: squaring the dominating bound
`sqrt(sigma) * sqrt(1+M) * (1+S(s',rho))` lands inside `C(s',rho) * sigma * (1+M)^2`. -/
private theorem akhcWeakC2_bound_sq_le {s' ρ σ M : ℝ} (hσ : 0 ≤ σ) (hM : 0 ≤ M) :
    (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) *
        (1 + akhcWeakC2_tailSum s' ρ)) ^ 2 ≤
      akhcWeakC2_maximizerConst s' ρ * σ * (1 + M) ^ 2 := by
  set S : ℝ := akhcWeakC2_tailSum s' ρ with hSdef
  have hboundsq :
      (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) * (1 + S)) ^ 2 =
        σ * (1 + M) * (1 + S) ^ 2 := by
    have h1 : (Real.rpow σ (1 / 2 : ℝ)) ^ 2 = σ := akhcWeakC2_rpow_half_sq hσ
    have h2 : (Real.rpow (1 + M) (1 / 2 : ℝ)) ^ 2 = 1 + M :=
      akhcWeakC2_rpow_half_sq (by linarith only [hM])
    have hexpand :
        (Real.rpow σ (1 / 2 : ℝ) * Real.rpow (1 + M) (1 / 2 : ℝ) * (1 + S)) ^ 2 =
          (Real.rpow σ (1 / 2 : ℝ)) ^ 2 * (Real.rpow (1 + M) (1 / 2 : ℝ)) ^ 2 * (1 + S) ^ 2 := by
      ring
    rw [hexpand, h1, h2]
  have hCeq : akhcWeakC2_maximizerConst s' ρ = (1 + S) ^ 2 := by
    unfold akhcWeakC2_maximizerConst
    rw [hSdef]
  have hfin : σ * (1 + M) * (1 + S) ^ 2 ≤ akhcWeakC2_maximizerConst s' ρ * σ * (1 + M) ^ 2 := by
    rw [hCeq]
    have hMM : 1 + M ≤ (1 + M) ^ 2 := by nlinarith only [hM, mul_nonneg hM hM]
    have hSnn : 0 ≤ (1 + S) ^ 2 := sq_nonneg _
    have hstep :
        σ * (1 + S) ^ 2 * (1 + M) ≤ σ * (1 + S) ^ 2 * (1 + M) ^ 2 :=
      mul_le_mul_of_nonneg_left hMM (mul_nonneg hσ hSnn)
    calc
      σ * (1 + M) * (1 + S) ^ 2 = σ * (1 + S) ^ 2 * (1 + M) := by ring
      _ ≤ σ * (1 + S) ^ 2 * (1 + M) ^ 2 := hstep
      _ = (1 + S) ^ 2 * σ * (1 + M) ^ 2 := by ring
  rw [hboundsq]; exact hfin

/-- **The shared assembly step**: for a nonnegative per-scale family `x : ℕ -> ℝ` dominated,
termwise, by `sigma * (1+M) * (1 + 3^{rho j})`, the CG geometric-weighted sum-of-square-roots
`(sum_j geometricWeight s' 1 j * sqrt(x j))^2` is at most `C(s',rho) * sigma * (1+M)^2`. -/
theorem akhcWeakC2_tsum_sq_le {s' ρ σ M : ℝ} (hs' : 0 < s') (hgap : ρ / 2 < s')
    (hσ : 0 ≤ σ) (hM : 0 ≤ M) {x : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hxle : ∀ j : ℕ, x j ≤ σ * (1 + M) * (1 + Real.rpow (3 : ℝ) (ρ * (j : ℝ)))) :
    (∑' j : ℕ, Ch02.geometricWeight s' 1 j * Real.rpow (x j) (1 / 2 : ℝ)) ^ 2 ≤
      akhcWeakC2_maximizerConst s' ρ * σ * (1 + M) ^ 2 := by
  have hle := akhcWeakC2_tsum_le_bound hs' hgap hσ hM hx0 hxle
  have hLHSnn : 0 ≤ ∑' j : ℕ, Ch02.geometricWeight s' 1 j * Real.rpow (x j) (1 / 2 : ℝ) :=
    tsum_nonneg fun j =>
      mul_nonneg (akhcWeakC2_geometricWeight_nonneg hs' j) (Real.rpow_nonneg (hx0 j) _)
  exact (pow_le_pow_left₀ hLHSnn hle 2).trans (akhcWeakC2_bound_sq_le hσ hM)


end

end SuperdiffusionCLT.AKHC61.WeakNorms
