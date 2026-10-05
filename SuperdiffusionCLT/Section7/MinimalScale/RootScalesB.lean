/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.RootScales
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The minimal scale `m⋆`

For `N₀ ≥ 0` put `e j = j - ⌈N₀ log j⌉`.  The scale `ms_star N₀ L̂ X₀ ω` is the least `j ≥ j₀(N₀)`
with `L̂ ≤ e j` and `X₀ ω ≤ 3^{e j}`.  It is finite everywhere (when `X₀ ≥ 1`), measurable, the two
conditions persist for all larger `j`, and `m⋆ ≤ max (j₀, 2L̂, 2 log₃ X₀)` up to rounding.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory

/-- The exponent `j - ⌈N₀ log j⌉`. -/
noncomputable def ms_e (N₀ : ℝ) (j : ℕ) : ℤ := (j : ℤ) - ⌈N₀ * Real.log j⌉

/-- The threshold from which `ms_e` is monotone and at least `j / 2`. -/
noncomputable def ms_j0 (N₀ : ℝ) : ℕ := ⌈(4 * N₀ + 2) ^ 2⌉₊

theorem ms_j0_ge_one {N₀ : ℝ} (hN : 0 ≤ N₀) : 1 ≤ ms_j0 N₀ := by
  unfold ms_j0
  refine Nat.one_le_iff_ne_zero.2 ?_
  have : (0 : ℝ) < (4 * N₀ + 2) ^ 2 := by positivity
  exact (Nat.ceil_pos.2 this).ne'

theorem ms_j0_ge_N (N₀ : ℝ) : N₀ ≤ (ms_j0 N₀ : ℝ) := by
  unfold ms_j0
  refine le_trans ?_ (Nat.le_ceil _)
  nlinarith only [sq_nonneg (4 * N₀ + 1)]

theorem ms_e_succ {N₀ : ℝ} (hN : 0 ≤ N₀) {j : ℕ} (hj : ms_j0 N₀ ≤ j) :
    ms_e N₀ j ≤ ms_e N₀ (j + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (ms_j0_ge_one hN).trans hj
  have hjN : N₀ ≤ (j : ℝ) := (ms_j0_ge_N N₀).trans (by exact_mod_cast hj)
  have hj0 : (0 : ℝ) < j := by linarith only [hj1]
  have hlog : Real.log ((j : ℝ) + 1) - Real.log j ≤ 1 / j := by
    have : Real.log (((j : ℝ) + 1) / j) ≤ ((j : ℝ) + 1) / j - 1 := Real.log_le_sub_one_of_pos
      (by positivity)
    rw [Real.log_div (by positivity) hj0.ne'] at this
    have h2 : ((j : ℝ) + 1) / j - 1 = 1 / j := by field_simp; ring
    linarith only [this, h2]
  have h3 : N₀ * Real.log ((j : ℝ) + 1) ≤ N₀ * Real.log j + 1 := by
    have h4 : N₀ * (Real.log ((j : ℝ) + 1) - Real.log j) ≤ N₀ * (1 / j) :=
      mul_le_mul_of_nonneg_left hlog hN
    have h5 : N₀ * (1 / j) ≤ 1 := by
      rw [mul_one_div, div_le_one hj0]; exact hjN
    linarith only [h4, h5]
  have h6 : ⌈N₀ * Real.log ((j : ℝ) + 1)⌉ ≤ ⌈N₀ * Real.log j⌉ + 1 := by
    rw [Int.ceil_le]
    have := Int.le_ceil (N₀ * Real.log j)
    push_cast
    linarith only [h3, this]
  unfold ms_e
  push_cast
  linarith only [h6]

theorem ms_e_mono {N₀ : ℝ} (hN : 0 ≤ N₀) {i j : ℕ} (hi : ms_j0 N₀ ≤ i) (hij : i ≤ j) :
    ms_e N₀ i ≤ ms_e N₀ j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact ih.trans (ms_e_succ hN (hi.trans hk))

theorem ms_e_ge {N₀ : ℝ} (hN : 0 ≤ N₀) {j : ℕ} (hj : ms_j0 N₀ ≤ j) :
    (j : ℝ) / 2 ≤ (ms_e N₀ j : ℝ) := by
  have hjN : (4 * N₀ + 2) ^ 2 ≤ (j : ℝ) := by
    have : ((ms_j0 N₀ : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    exact le_trans (Nat.le_ceil _) this
  have hj0 : (0 : ℝ) ≤ j := by positivity
  set r := Real.sqrt j with hr
  have hr2 : r * r = j := Real.mul_self_sqrt hj0
  have hr1 : 4 * N₀ + 2 ≤ r := by
    rw [hr]; exact Real.le_sqrt_of_sq_le hjN
  have hlog : Real.log j ≤ 2 * r := by
    have := Real.log_le_rpow_div hj0 (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    have e : √(j : ℝ) / (1 / 2) = 2 * √(j : ℝ) := by ring
    linarith only [this, e]
  have hc : (⌈N₀ * Real.log j⌉ : ℝ) ≤ N₀ * Real.log j + 1 := (Int.ceil_lt_add_one _).le
  have h2 : N₀ * Real.log j ≤ N₀ * (2 * r) := mul_le_mul_of_nonneg_left hlog hN
  have h3 : N₀ * (2 * r) + 1 ≤ (j : ℝ) / 2 := by
    rw [← hr2]
    nlinarith only [hr1, hN]
  unfold ms_e
  push_cast
  linarith only [hc, h2, h3]

theorem ms_zpow_eq (e : ℤ) : (3 : ℝ) ^ e = Real.exp ((e : ℝ) * Real.log 3) := by
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num)]; ring_nf

/-- The defining predicate of `m⋆`. -/
def ms_P (N₀ L : ℝ) (X₀ : ℝ) (j : ℕ) : Prop :=
  ms_j0 N₀ ≤ j ∧ L ≤ (ms_e N₀ j : ℝ) ∧ X₀ ≤ (3 : ℝ) ^ (ms_e N₀ j)

/-- A good index below an explicit bound. -/
theorem ms_P_witness {N₀ L X₀ : ℝ} (hN : 0 ≤ N₀) (hX : 1 ≤ X₀) :
    ms_P N₀ L X₀ (max (ms_j0 N₀) (max ⌈2 * L⌉₊ ⌈2 * Real.log X₀ / Real.log 3⌉₊)) := by
  set j := max (ms_j0 N₀) (max ⌈2 * L⌉₊ ⌈2 * Real.log X₀ / Real.log 3⌉₊) with hj
  have hj0 : ms_j0 N₀ ≤ j := le_max_left _ _
  have hge := ms_e_ge hN hj0
  have h1 : 2 * L ≤ (j : ℝ) := by
    have : ⌈2 * L⌉₊ ≤ j := le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have h2 : 2 * Real.log X₀ / Real.log 3 ≤ (j : ℝ) := by
    have : ⌈2 * Real.log X₀ / Real.log 3⌉₊ ≤ j :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨hj0, by linarith only [hge, h1], ?_⟩
  rw [ms_zpow_eq]
  calc X₀ = Real.exp (Real.log X₀) := (Real.exp_log (by linarith only [hX])).symm
    _ ≤ _ := Real.exp_le_exp.2 ?_
  have h3 : 2 * Real.log X₀ ≤ (j : ℝ) * Real.log 3 := by
    rwa [div_le_iff₀ hl3] at h2
  have h4 : (j : ℝ) / 2 * Real.log 3 ≤ (ms_e N₀ j : ℝ) * Real.log 3 :=
    mul_le_mul_of_nonneg_right hge hl3.le
  linarith only [h3, h4]

/-- The scale `m⋆`. -/
noncomputable def ms_star (N₀ L : ℝ) (X₀ : ℝ) : ℕ := by
  classical
  exact if h : ∃ j, ms_P N₀ L X₀ j then Nat.find h else 0

theorem ms_star_spec {N₀ L X₀ : ℝ} (hN : 0 ≤ N₀) (hX : 1 ≤ X₀) :
    ms_P N₀ L X₀ (ms_star N₀ L X₀) := by
  classical
  have h : ∃ j, ms_P N₀ L X₀ j := ⟨_, ms_P_witness hN hX⟩
  unfold ms_star
  simp only [h, ↓reduceDIte]
  exact Nat.find_spec h

theorem ms_star_le {N₀ L X₀ : ℝ} (hN : 0 ≤ N₀) (hX : 1 ≤ X₀) {j : ℕ}
    (hj : ms_P N₀ L X₀ j) : ms_star N₀ L X₀ ≤ j := by
  classical
  have h : ∃ j, ms_P N₀ L X₀ j := ⟨_, ms_P_witness hN hX⟩
  unfold ms_star
  simp only [h, ↓reduceDIte]
  exact Nat.find_min' h hj

/-- **Persistence**: every `n ≥ m⋆` satisfies the defining conditions. -/
theorem ms_star_persist {N₀ L X₀ : ℝ} (hN : 0 ≤ N₀) (hX : 1 ≤ X₀) {n : ℕ}
    (hn : ms_star N₀ L X₀ ≤ n) : ms_P N₀ L X₀ n := by
  obtain ⟨h0, h1, h2⟩ := ms_star_spec hN hX
  have hmono := ms_e_mono hN h0 hn
  refine ⟨h0.trans hn, ?_, ?_⟩
  · have : (ms_e N₀ (ms_star N₀ L X₀) : ℝ) ≤ (ms_e N₀ n : ℝ) := by exact_mod_cast hmono
    linarith only [h1, this]
  · refine h2.trans ?_
    exact zpow_le_zpow_right₀ (by norm_num) hmono

/-- Measurability of `m⋆` in the sample. -/
theorem ms_star_measurable {Ω : Type*} [MeasurableSpace Ω] {N₀ L : ℝ} {X₀ : Ω → ℝ}
    (hN : 0 ≤ N₀) (hX : ∀ ω, 1 ≤ X₀ ω) (hm : Measurable X₀) :
    Measurable fun ω => ms_star N₀ L (X₀ ω) := by
  classical
  have hex : ∀ ω, ∃ j, ms_P N₀ L (X₀ ω) j := fun ω => ⟨_, ms_P_witness hN (hX ω)⟩
  have hmeas : Measurable fun ω => Nat.find (hex ω) := by
    refine measurable_find hex fun k => ?_
    have : {ω | ms_P N₀ L (X₀ ω) k} =
        {_ω : Ω | ms_j0 N₀ ≤ k ∧ L ≤ (ms_e N₀ k : ℝ)} ∩
          {ω | X₀ ω ≤ (3 : ℝ) ^ (ms_e N₀ k)} := by
      ext ω; simp only [ms_P, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    refine MeasurableSet.inter (MeasurableSet.const _) ?_
    exact measurableSet_le hm measurable_const
  have : (fun ω => ms_star N₀ L (X₀ ω)) = fun ω => Nat.find (hex ω) := by
    funext ω
    unfold ms_star
    simp only [hex ω, ↓reduceDIte]
  rw [this]; exact hmeas

/-- Upper bound on `m⋆` in terms of `log X₀`. -/
theorem ms_star_le_bound {N₀ L X₀ : ℝ} (hN : 0 ≤ N₀) (hL : 0 ≤ L) (hX : 1 ≤ X₀) :
    (ms_star N₀ L X₀ : ℝ) * Real.log 3 ≤
      2 * (ms_j0 N₀ + 2 * L + 2) + 2 * Real.log X₀ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl32 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith only [this]
  have hle := ms_star_le (L := L) hN hX (ms_P_witness (L := L) hN hX)
  have hlogX : 0 ≤ Real.log X₀ := Real.log_nonneg hX
  have hc1 : (⌈2 * L⌉₊ : ℝ) ≤ 2 * L + 1 := (Nat.ceil_lt_add_one (by linarith only [hL])).le
  have hc2 : (⌈2 * Real.log X₀ / Real.log 3⌉₊ : ℝ) ≤ 2 * Real.log X₀ / Real.log 3 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hmax : ((max (ms_j0 N₀) (max ⌈2 * L⌉₊ ⌈2 * Real.log X₀ / Real.log 3⌉₊) : ℕ) : ℝ) ≤
      (ms_j0 N₀ : ℝ) + (2 * L + 1) + (2 * Real.log X₀ / Real.log 3 + 1) := by
    have h1 : (0 : ℝ) ≤ 2 * L + 1 := by linarith only [hL]
    have h2 : (0 : ℝ) ≤ 2 * Real.log X₀ / Real.log 3 + 1 := by positivity
    have h3 : (0 : ℝ) ≤ (ms_j0 N₀ : ℝ) := by positivity
    rw [Nat.cast_max, Nat.cast_max]
    refine max_le (by linarith only [h1, h2]) (max_le ?_ ?_)
    · linarith only [hc1, h2, h3]
    · linarith only [hc2, h1, h3]
  have hle' : (ms_star N₀ L X₀ : ℝ) ≤ (ms_j0 N₀ : ℝ) + (2 * L + 1) +
      (2 * Real.log X₀ / Real.log 3 + 1) := le_trans (by exact_mod_cast hle) hmax
  have hm0 : (0 : ℝ) ≤ (ms_star N₀ L X₀ : ℝ) := by positivity
  have h5 : (ms_star N₀ L X₀ : ℝ) * Real.log 3 ≤
      ((ms_j0 N₀ : ℝ) + (2 * L + 1) + (2 * Real.log X₀ / Real.log 3 + 1)) * Real.log 3 :=
    mul_le_mul_of_nonneg_right hle' hl3.le
  have h6 : (2 * Real.log X₀ / Real.log 3 + 1) * Real.log 3 = 2 * Real.log X₀ + Real.log 3 := by
    field_simp
  have h7 : (0 : ℝ) ≤ (ms_j0 N₀ : ℝ) + (2 * L + 1) := by
    have : (0 : ℝ) ≤ (ms_j0 N₀ : ℝ) := by positivity
    linarith only [this, hL]
  have h8 : ((ms_j0 N₀ : ℝ) + (2 * L + 1)) * Real.log 3 ≤ ((ms_j0 N₀ : ℝ) + (2 * L + 1)) * 2 :=
    mul_le_mul_of_nonneg_left hl32 h7
  have h9 : ((ms_j0 N₀ : ℝ) + (2 * L + 1) + (2 * Real.log X₀ / Real.log 3 + 1)) * Real.log 3 =
      ((ms_j0 N₀ : ℝ) + (2 * L + 1)) * Real.log 3 + (2 * Real.log X₀ + Real.log 3) := by
    rw [add_mul, h6]
  linarith only [h5, h8, h9, hl32]

end SuperdiffusionCLT.Section7
