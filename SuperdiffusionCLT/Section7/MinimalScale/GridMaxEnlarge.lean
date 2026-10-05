/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section7.MinimalScale.RootScales
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Logarithmic enlargement of the scale of the grid maximum

For `x ≥ 1` put `b2c_enl κ C n₀ x = max (x · 3^C · (4 log x + 4)^{κ log 3}) 3^{n₀}`.  If
`b2c_enl … x ≤ 3^q` with `q` the bottom scale `n_s(N)` (or any scale within `C + κ log s` of
the bottom scale at `(N+1, s+b)`), then `x ≤ 3^{n_{s+b}(N+1)}`.  The enlargement is measurable,
`≥ 1`, and `log (b2c_enl x) ≤ a log x + B₀` with `a, B₀` depending on the parameters only, so the
`Γ_ρ` tail of `log x` transfers to `log (b2c_enl x)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory

noncomputable section

/-- The logarithmic enlargement of a scale. -/
def b2c_enl (κ C : ℝ) (n₀ : ℕ) (x : ℝ) : ℝ :=
  max (x * (3 : ℝ) ^ C * (4 * Real.log x + 4) ^ (κ * Real.log 3)) ((3 : ℝ) ^ n₀)

/-- The additive constant of the enlargement at `(N, b)`. -/
def b2c_C1 (N : ℝ) (b : ℕ) : ℝ := (N + 1) * Real.log (1 + (b : ℝ)) + 1

/-- The threshold index of the enlargement at `N`. -/
def b2c_n0 (N : ℝ) : ℕ := ⌈(4 * N + 6) ^ 2⌉₊

theorem b2c_enl_ge_pow (κ C : ℝ) (n₀ : ℕ) (x : ℝ) : (3 : ℝ) ^ n₀ ≤ b2c_enl κ C n₀ x :=
  le_max_right _ _

theorem b2c_enl_ge_one (κ C : ℝ) (n₀ : ℕ) (x : ℝ) : 1 ≤ b2c_enl κ C n₀ x :=
  (one_le_pow₀ (by norm_num)).trans (b2c_enl_ge_pow κ C n₀ x)

theorem b2c_enl_ge_main (κ C : ℝ) (n₀ : ℕ) (x : ℝ) :
    x * (3 : ℝ) ^ C * (4 * Real.log x + 4) ^ (κ * Real.log 3) ≤ b2c_enl κ C n₀ x :=
  le_max_left _ _

theorem b2c_enl_measurable {Ω : Type*} [MeasurableSpace Ω] {Xs : Ω → ℝ} (hX : Measurable Xs)
    (κ C : ℝ) (n₀ : ℕ) : Measurable fun ω => b2c_enl κ C n₀ (Xs ω) := by
  unfold b2c_enl
  have h1 : Measurable fun ω => 4 * Real.log (Xs ω) + 4 :=
    ((Real.measurable_log.comp hX).const_mul 4).add_const 4
  exact ((hX.mul_const _).mul (h1.pow_const _)).max measurable_const

/-- `1 < log 3`. -/
theorem b2c_one_lt_log3 : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact lt_trans Real.exp_one_lt_d9 (by norm_num)

/-- **The core inequality.** -/
theorem b2c_enl_core {κ C : ℝ} (hκ : 0 ≤ κ) {x : ℝ} {p s q : ℕ} (hs : 1 ≤ s)
    (hsp : (s : ℝ) ≤ 2 * p) (hp : (3 : ℝ) ^ p < x)
    (hq : (q : ℝ) ≤ p + C + κ * Real.log s) :
    (3 : ℝ) ^ q < x * (3 : ℝ) ^ C * (4 * Real.log x + 4) ^ (κ * Real.log 3) := by
  have h3 := b2c_one_lt_log3
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith only [hs1]
  have hlogx : (p : ℝ) * Real.log 3 < Real.log x := by
    have := Real.log_lt_log (by positivity) hp
    rwa [Real.log_pow] at this
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpl : (p : ℝ) ≤ p * Real.log 3 := le_mul_of_one_le_right hp0 h3.le
  have hG : (s : ℝ) ≤ 4 * Real.log x + 4 := by linarith only [hsp, hpl, hlogx]
  have hexp : 0 ≤ κ * Real.log 3 := mul_nonneg hκ (by linarith only [h3])
  have hGs : (s : ℝ) ^ (κ * Real.log 3) ≤ (4 * Real.log x + 4) ^ (κ * Real.log 3) :=
    Real.rpow_le_rpow hs0.le hG hexp
  have hseq : (s : ℝ) ^ (κ * Real.log 3) = (3 : ℝ) ^ (κ * Real.log (s : ℝ)) := by
    rw [Real.rpow_def_of_pos hs0, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hq3 : (3 : ℝ) ^ q ≤ (3 : ℝ) ^ ((p : ℝ) + C + κ * Real.log s) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
  have hsplit : (3 : ℝ) ^ ((p : ℝ) + C + κ * Real.log s) =
      (3 : ℝ) ^ p * ((3 : ℝ) ^ C * (3 : ℝ) ^ (κ * Real.log (s : ℝ))) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_natCast]
    ring
  have hpos : 0 < (3 : ℝ) ^ C * (3 : ℝ) ^ (κ * Real.log (s : ℝ)) := by positivity
  have hle : (3 : ℝ) ^ C * (3 : ℝ) ^ (κ * Real.log (s : ℝ)) ≤
      (3 : ℝ) ^ C * (4 * Real.log x + 4) ^ (κ * Real.log 3) := by
    rw [← hseq]
    exact mul_le_mul_of_nonneg_left hGs (by positivity)
  calc (3 : ℝ) ^ q ≤ (3 : ℝ) ^ p * ((3 : ℝ) ^ C * (3 : ℝ) ^ (κ * Real.log (s : ℝ))) := by
        rw [← hsplit]; exact hq3
    _ < x * ((3 : ℝ) ^ C * (3 : ℝ) ^ (κ * Real.log (s : ℝ))) :=
        mul_lt_mul_of_pos_right hp hpos
    _ ≤ x * ((3 : ℝ) ^ C * (4 * Real.log x + 4) ^ (κ * Real.log 3)) :=
        mul_le_mul_of_nonneg_left hle (by linarith only [hp, (by positivity : (0 : ℝ) < 3 ^ p)])
    _ = x * (3 : ℝ) ^ C * (4 * Real.log x + 4) ^ (κ * Real.log 3) := by ring

/-- The lower bound for the scale at `(N+1, s+b)`. -/
theorem b2c_p_ge {N : ℝ} (hN : 0 ≤ N) (b : ℕ) {s : ℕ} (hs : (4 * N + 6) ^ 2 ≤ (s : ℝ)) :
    (s : ℝ) ≤ (nK (N + 1) (s + b) : ℝ) + (N + 1) * Real.log s + b2c_C1 N b ∧
      (s : ℝ) ≤ 2 * (nK (N + 1) (s + b) : ℝ) := by
  have h36 : (36 : ℝ) ≤ (4 * N + 6) ^ 2 := by nlinarith only [hN]
  have hs1 : (1 : ℝ) ≤ s := by linarith only [hs, h36]
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hsb : (4 * (N + 1) + 2) ^ 2 ≤ ((s + b : ℕ) : ℝ) := by
    push_cast
    have : 4 * (N + 1) + 2 = 4 * N + 6 := by ring
    rw [this]
    linarith only [hs, hb0]
  have hcast := nK_cast (by linarith only [hN] : 0 ≤ N + 1) hsb
  have hceil : (⌈(N + 1) * Real.log ((s + b : ℕ) : ℝ)⌉₊ : ℝ) <
      (N + 1) * Real.log ((s + b : ℕ) : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith only [hN])
      (Real.log_nonneg (by push_cast; linarith only [hs1, hb0])))
  have hlog : Real.log ((s + b : ℕ) : ℝ) ≤ Real.log s + Real.log (1 + b) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by push_cast; linarith only [hs1, hb0]) ?_
    push_cast
    nlinarith only [hs1, hb0]
  have hN1 : 0 ≤ N + 1 := by linarith only [hN]
  have hmul : (N + 1) * Real.log ((s + b : ℕ) : ℝ) ≤
      (N + 1) * (Real.log s + Real.log (1 + b)) := mul_le_mul_of_nonneg_left hlog hN1
  have hcs : ((s + b : ℕ) : ℝ) = s + b := by push_cast; ring
  refine ⟨?_, ?_⟩
  · unfold b2c_C1
    rw [hcast]
    nlinarith only [hceil, hmul, hb0, hcs]
  · have := nK_ge_half hN1 hsb
    linarith only [this, hb0, hcs]

theorem b2c_n0_spec {N : ℝ} {n : ℕ} (h : b2c_n0 N ≤ n) : (4 * N + 6) ^ 2 ≤ (n : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast h)

/-- **The enlargement works at the bottom scale with the same `N`.** -/
theorem b2c_enl_spec {N : ℝ} (hN : 0 ≤ N) (b : ℕ) {x : ℝ} (n : ℕ)
    (h : b2c_enl 1 (b2c_C1 N b) (b2c_n0 N) x ≤ (3 : ℝ) ^ nK N n) :
    b2c_n0 N ≤ n ∧ x ≤ (3 : ℝ) ^ nK (N + 1) (n + b) := by
  have h0 : b2c_n0 N ≤ n := by
    have h1 : (3 : ℝ) ^ b2c_n0 N ≤ (3 : ℝ) ^ nK N n :=
      (b2c_enl_ge_pow _ _ _ x).trans h
    have h2 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
    exact h2.trans (nK_le N n)
  refine ⟨h0, ?_⟩
  by_contra hcon
  push Not at hcon
  have hn := b2c_n0_spec h0
  have hn1 : 1 ≤ n := by
    have h36 : (36 : ℝ) ≤ (4 * N + 6) ^ 2 := by nlinarith only [hN]
    have : (1 : ℝ) ≤ n := by linarith only [hn, h36]
    exact_mod_cast this
  have hgap := b2c_p_ge hN b hn
  have hq : (nK N n : ℝ) ≤ n - N * Real.log n := by
    have hK : (4 * N + 2) ^ 2 ≤ (n : ℝ) := by nlinarith only [hn, hN]
    rw [nK_cast hN hK]
    have := Nat.le_ceil (N * Real.log (n : ℝ))
    linarith only [this]
  have hcore := b2c_enl_core (κ := 1) (C := b2c_C1 N b) (by norm_num) (p := nK (N + 1) (n + b))
    (s := n) hn1 hgap.2 hcon (q := nK N n) (by linarith only [hq, hgap.1])
  exact absurd (hcore.trans_le (b2c_enl_ge_main _ _ _ _ |>.trans h)) (lt_irrefl _)

/-- **The enlargement at a scale below `m'`, with exponent `N + 1`.** -/
theorem b2c_enl_spec_succ {N : ℝ} (hN : 0 ≤ N) (b : ℕ) {x : ℝ} {n m' : ℕ} (hn : n < m')
    (h : b2c_enl (N + 1) (b2c_C1 N b) (b2c_n0 N) x ≤ (3 : ℝ) ^ n) :
    b2c_n0 N ≤ m' ∧ x ≤ (3 : ℝ) ^ nK (N + 1) (m' + b) := by
  have h0 : b2c_n0 N ≤ n :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 ((b2c_enl_ge_pow _ _ _ x).trans h)
  have h0' : b2c_n0 N ≤ m' := h0.trans hn.le
  refine ⟨h0', ?_⟩
  by_contra hcon
  push Not at hcon
  have hm := b2c_n0_spec h0'
  have hm1 : 1 ≤ m' := by
    have h36 : (36 : ℝ) ≤ (4 * N + 6) ^ 2 := by nlinarith only [hN]
    have : (1 : ℝ) ≤ m' := by linarith only [hm, h36]
    exact_mod_cast this
  have hgap := b2c_p_ge hN b hm
  have hnm : (n : ℝ) ≤ m' := by exact_mod_cast hn.le
  have hcore := b2c_enl_core (κ := N + 1) (C := b2c_C1 N b) (by linarith only [hN])
    (p := nK (N + 1) (m' + b)) (s := m') hm1 hgap.2 hcon (q := n)
    (by linarith only [hnm, hgap.1])
  exact absurd (hcore.trans_le ((b2c_enl_ge_main _ _ _ _).trans h)) (lt_irrefl _)

/-- The logarithm of the enlargement is at most an affine function of `log x`. -/
theorem b2c_enl_log_le {κ C : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (n₀ : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (b2c_enl κ C n₀ x) ≤
      (1 + 4 * κ * Real.log 3) * Real.log x + (C + 3 * κ + n₀) * Real.log 3 := by
  have h3 := b2c_one_lt_log3
  have h30 : 0 ≤ Real.log 3 := by linarith only [h3]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  have hG : (0 : ℝ) < 4 * Real.log x + 4 := by linarith only [hlx]
  have hx0 : 0 < x := by linarith only [hx]
  unfold b2c_enl
  rcases max_choice (x * (3 : ℝ) ^ C * (4 * Real.log x + 4) ^ (κ * Real.log 3))
      ((3 : ℝ) ^ n₀) with hm | hm
  · rw [hm, Real.log_mul (by positivity) (by positivity), Real.log_mul hx0.ne' (by positivity),
      Real.log_rpow (by norm_num), Real.log_rpow hG]
    have hlg : Real.log (4 * Real.log x + 4) ≤ 4 * Real.log x + 3 := by
      have := Real.log_le_sub_one_of_pos hG
      linarith only [this]
    have hk3 : 0 ≤ κ * Real.log 3 := mul_nonneg hκ h30
    have h1 : κ * Real.log 3 * Real.log (4 * Real.log x + 4) ≤
        κ * Real.log 3 * (4 * Real.log x + 3) := mul_le_mul_of_nonneg_left hlg hk3
    have h2 : 0 ≤ (n₀ : ℝ) * Real.log 3 := mul_nonneg hn0 h30
    nlinarith only [h1, h2]
  · rw [hm, Real.log_pow]
    have h1 : 0 ≤ (1 + 4 * κ * Real.log 3) * Real.log x := by
      have : 0 ≤ 1 + 4 * κ * Real.log 3 := by nlinarith only [hκ, h30]
      exact mul_nonneg this hlx
    have h2 : 0 ≤ (C + 3 * κ) * Real.log 3 := mul_nonneg (by linarith only [hC, hκ]) h30
    nlinarith only [h1, h2]

/-- **Transfer of the tail.** -/
theorem b2c_enl_isBigO {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {κ C : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (n₀ : ℕ) {ρ : ℝ} {Xs : Ω → ℝ} (h1 : ∀ ω, 1 ≤ Xs ω)
    {Lh : ℝ} (hO : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma ρ) (fun ω => Real.log (Xs ω)) Lh) :
    Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (b2c_enl κ C n₀ (Xs ω)))
      ((1 + 4 * κ * Real.log 3) * Lh + (C + 3 * κ + n₀) * Real.log 3) := by
  have h3 := b2c_one_lt_log3
  have h30 : 0 ≤ Real.log 3 := by linarith only [h3]
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
  have ha : 0 < 1 + 4 * κ * Real.log 3 := by nlinarith only [hκ, h30]
  have hB : 0 ≤ (C + 3 * κ + n₀) * Real.log 3 :=
    mul_nonneg (by linarith only [hC, hκ, hn0]) h30
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff] at hO ⊢
  intro t ht
  refine (measureReal_mono ?_).trans (hO ht)
  intro ω hω
  have hω' : ((1 + 4 * κ * Real.log 3) * Lh + (C + 3 * κ + n₀) * Real.log 3) * t <
      |Real.log (b2c_enl κ C n₀ (Xs ω))| := hω
  have hl0 : 0 ≤ Real.log (b2c_enl κ C n₀ (Xs ω)) := Real.log_nonneg (b2c_enl_ge_one _ _ _ _)
  rw [abs_of_nonneg hl0] at hω'
  have hle := b2c_enl_log_le hκ hC n₀ (h1 ω)
  have ht0 : 1 ≤ t := ht
  have hBt : (C + 3 * κ + n₀) * Real.log 3 ≤ (C + 3 * κ + n₀) * Real.log 3 * t := by
    nlinarith only [hB, ht0]
  have hlt : (1 + 4 * κ * Real.log 3) * (Lh * t) < (1 + 4 * κ * Real.log 3) * Real.log (Xs ω) := by
    nlinarith only [hω', hle, hBt]
  have := lt_of_mul_lt_mul_left hlt ha.le
  have hlx : 0 ≤ Real.log (Xs ω) := Real.log_nonneg (h1 ω)
  show Lh * t < |Real.log (Xs ω)|
  rw [abs_of_nonneg hlx]
  exact this

/-- Satisfiability: the hypothesis of `b2c_enl_spec` holds for `x = 1`, `N = 0`, `b = 0` and large
`n`, and then the conclusion is the trivial bound. -/
example : ∃ n : ℕ, b2c_enl 1 (b2c_C1 0 0) (b2c_n0 0) 1 ≤ (3 : ℝ) ^ nK 0 n ∧
    b2c_n0 0 ≤ n ∧ (1 : ℝ) ≤ (3 : ℝ) ^ nK (0 + 1) (n + 0) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b2c_enl 1 (b2c_C1 0 0) (b2c_n0 0) 1)
    (by norm_num : (1 : ℝ) < 3)
  have h0 : nK 0 n = n := by simp [nK]
  have hspec := b2c_enl_spec (N := 0) le_rfl 0 (x := 1) n (by rw [h0]; exact hn.le)
  exact ⟨n, by rw [h0]; exact hn.le, hspec.1, one_le_pow₀ (by norm_num)⟩

/-- Satisfiability of the tail transfer: the Dirac law at a point, `Xs ≡ 1`, scale `0`. -/
example : Homogenization.IndependentSums.IsBigO (Measure.dirac (0 : ℝ))
    (Homogenization.IndependentSums.gammaSigma (1 / 2 : ℝ))
    (fun _ => Real.log (b2c_enl 1 (b2c_C1 0 0) (b2c_n0 0) (1 : ℝ)))
    ((1 + 4 * 1 * Real.log 3) * 0 + (b2c_C1 0 0 + 3 * 1 + (b2c_n0 0 : ℝ)) * Real.log 3) :=
  b2c_enl_isBigO (μ := Measure.dirac (0 : ℝ)) (κ := 1) (C := b2c_C1 0 0) zero_le_one
    (by unfold b2c_C1; simp) (b2c_n0 0) (Xs := fun _ => (1 : ℝ)) (fun _ => le_rfl)
    (by
      rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
      intro t _
      simp [Homogenization.IndependentSums.absTailEvent,
        Homogenization.IndependentSums.upperTailEvent, Real.exp_nonneg])

end

end SuperdiffusionCLT.Section7
