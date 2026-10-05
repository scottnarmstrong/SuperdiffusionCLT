/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Scale separation and window lemmas for Section 7

The scale-separation estimate used at the start of the `L²`, Caccioppoli and `L^∞` proofs:
for the window width `h = ⌈M log m⌉` and `n = m - h`,
`m^A ν^{-A} σ̄_m^A 3^{θ(n-m)} ≤ m^{-P}` as soon as `M ≥ M₀(A, θ, P)` and `m` is above an explicit
threshold depending on `ν` and on the constant `C` in `σ̄_m ≤ C m`. The window lemmas record that
`h ≤ κ m` for large `m` and that `m - n ≤ c δ_m⁻¹` forces `n ≥ m/2` after enlarging the threshold,
with the comparison `δ_n ≤ 2 δ_m`.

## Main results

* `SuperdiffusionCLT.Section7.scale_separation`
* `SuperdiffusionCLT.Section7.scale_separation_ceil`
* `SuperdiffusionCLT.Section7.ceil_log_le_mul`
* `SuperdiffusionCLT.Section7.half_le_of_window`
* `SuperdiffusionCLT.Section7.deltaScale_le_two_mul`
* `SuperdiffusionCLT.Section7.window_consequences`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

/-- The scale `δ_j = ε j^{-(1-ρ)/2} log j` of `e.Dir.new.delta`. -/
noncomputable def deltaScale (ε ρ j : ℝ) : ℝ := ε * j ^ (-((1 - ρ) / 2)) * Real.log j

theorem a23_log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

/-- **Scale separation.** For `A ≥ 0` and `θ > 0` there is `M₀` (depending on `A, θ, P` only)
such that, for every `ν > 0` and every constant `Cs > 0`, there is `L₀ ≥ 1` with: whenever
`m ≥ L₀`, `0 ≤ σ ≤ Cs m` and the window satisfies `M log m ≤ m - n` with `M ≥ M₀`,
`m^A ν^{-A} σ^A 3^{θ(n-m)} ≤ m^{-P}`. -/
theorem scale_separation (A θ P : ℝ) (hA : 0 ≤ A) (hθ : 0 < θ) :
    ∃ M₀ : ℝ, ∀ ν Cs : ℝ, 0 < ν → 0 < Cs → ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ m n σ : ℝ, L₀ ≤ m → 0 ≤ σ → σ ≤ Cs * m →
        M * Real.log m ≤ m - n →
        m ^ A * ν ^ (-A) * σ ^ A * (3 : ℝ) ^ (θ * (n - m)) ≤ m ^ (-P) := by
  have hl3 := a23_log_three_pos
  refine ⟨(2 * A + P + 1) / (θ * Real.log 3), fun ν Cs hν hCs => ?_⟩
  refine ⟨max 1 (Cs ^ A * ν ^ (-A)), le_max_left _ _, fun M hM m n σ hm hσ hσm hwin => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm1
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm1
  -- the factor 3^{θ(n-m)}
  have hMθ : 2 * A + P + 1 ≤ M * (θ * Real.log 3) := by
    have := (div_le_iff₀ (mul_pos hθ hl3)).mp hM
    linarith only [this]
  have h3 : (3 : ℝ) ^ (θ * (n - m)) ≤ m ^ (-(θ * M * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hm0, Real.exp_le_exp]
    have h1 : θ * (n - m) ≤ -(θ * (M * Real.log m)) := by
      have := mul_le_mul_of_nonneg_left hwin hθ.le
      linarith only [this]
    have h2 := mul_le_mul_of_nonneg_right h1 hl3.le
    linarith only [h2]
  -- the factor σ^A
  have hσA : σ ^ A ≤ Cs ^ A * m ^ A := by
    rw [← Real.mul_rpow hCs.le hm0.le]
    exact Real.rpow_le_rpow hσ hσm hA
  have hmA : 0 ≤ m ^ A := Real.rpow_nonneg hm0.le A
  have hνA : 0 ≤ ν ^ (-A) := Real.rpow_nonneg hν.le _
  have hexp : m ^ A * ν ^ (-A) * σ ^ A * (3 : ℝ) ^ (θ * (n - m)) ≤
      (Cs ^ A * ν ^ (-A)) * m ^ (2 * A - θ * M * Real.log 3) := by
    have e1 : m ^ (2 * A - θ * M * Real.log 3) =
        m ^ A * m ^ A * m ^ (-(θ * M * Real.log 3)) := by
      rw [show 2 * A - θ * M * Real.log 3 = A + A + -(θ * M * Real.log 3) by ring,
        Real.rpow_add hm0, Real.rpow_add hm0]
    rw [e1]
    have h4 : 0 ≤ (3 : ℝ) ^ (θ * (n - m)) := Real.rpow_nonneg (by norm_num) _
    have hσ0 : 0 ≤ σ ^ A := Real.rpow_nonneg hσ A
    calc m ^ A * ν ^ (-A) * σ ^ A * (3 : ℝ) ^ (θ * (n - m))
        ≤ m ^ A * ν ^ (-A) * (Cs ^ A * m ^ A) * m ^ (-(θ * M * Real.log 3)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hσA (mul_nonneg hmA hνA)) h3 h4
            (mul_nonneg (mul_nonneg hmA hνA) (mul_nonneg (Real.rpow_nonneg hCs.le A) hmA))
      _ = (Cs ^ A * ν ^ (-A)) * (m ^ A * m ^ A * m ^ (-(θ * M * Real.log 3))) := by ring
  -- the exponent
  have hmono : m ^ (2 * A - θ * M * Real.log 3) ≤ m ^ (-P - 1) := by
    refine Real.rpow_le_rpow_of_exponent_le hm1 ?_
    linarith only [hMθ]
  have hsplit : m ^ (-P - 1) = m ^ (-P) * m⁻¹ := by
    rw [sub_eq_add_neg, Real.rpow_add hm0, Real.rpow_neg_one]
  have hK : Cs ^ A * ν ^ (-A) ≤ m := le_trans (le_max_right _ _) hm
  have hKnn : 0 ≤ Cs ^ A * ν ^ (-A) := mul_nonneg (Real.rpow_nonneg hCs.le A) hνA
  calc m ^ A * ν ^ (-A) * σ ^ A * (3 : ℝ) ^ (θ * (n - m))
      ≤ (Cs ^ A * ν ^ (-A)) * m ^ (2 * A - θ * M * Real.log 3) := hexp
    _ ≤ (Cs ^ A * ν ^ (-A)) * (m ^ (-P) * m⁻¹) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hmono hKnn
    _ = m ^ (-P) * ((Cs ^ A * ν ^ (-A)) / m) := by ring
    _ ≤ m ^ (-P) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hm0.le _)
        rw [div_le_one hm0]
        exact hK
    _ = m ^ (-P) := mul_one _

/-- The bottom of the window of the standing setup, `n ≤ m - ⌈M log m⌉` (the scale
`n = m - h_m` of the proofs), gives `M log m ≤ m - n`. -/
theorem window_ceil_le (M m : ℝ) (n : ℤ) (hn : (n : ℝ) ≤ m - ⌈M * Real.log m⌉) :
    M * Real.log m ≤ m - n := by
  have := Int.le_ceil (M * Real.log m)
  linarith only [this, hn]

/-- **Scale separation for the window `n = m - ⌈M log m⌉`**, with
natural-number exponent `N` in `m^{-N}` (`N = 3000` and `N = 300` in the text). -/
theorem scale_separation_ceil (A θ : ℝ) (N : ℕ) (hA : 0 ≤ A) (hθ : 0 < θ) :
    ∃ M₀ : ℝ, ∀ ν Cs : ℝ, 0 < ν → 0 < Cs → ∃ L₀ : ℝ, 1 ≤ L₀ ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ (m : ℝ) (n : ℤ) (σ : ℝ), L₀ ≤ m → 0 ≤ σ → σ ≤ Cs * m →
        (n : ℝ) ≤ (m : ℝ) - ⌈M * Real.log m⌉ →
        m ^ A * ν ^ (-A) * σ ^ A * (3 : ℝ) ^ (θ * ((n : ℝ) - m)) ≤ (m ^ N)⁻¹ := by
  obtain ⟨M₀, h⟩ := scale_separation A θ (N : ℝ) hA hθ
  refine ⟨M₀, fun ν Cs hν hCs => ?_⟩
  obtain ⟨L₀, hL₀, h'⟩ := h ν Cs hν hCs
  refine ⟨L₀, hL₀, fun M hM m n σ hm hσ hσm hn => ?_⟩
  have hm0 : 0 < m := lt_of_lt_of_le one_pos (le_trans hL₀ hm)
  have := h' M hM m n σ hm hσ hσm (window_ceil_le M m n hn)
  rwa [Real.rpow_neg hm0.le, Real.rpow_natCast] at this

/-- Witness at explicit numbers: `A = 1`, `θ = 1/2`, `N = 300`, `ν = 1`, `C = 1`; the
conclusion is not vacuous because the window and `σ ≤ m` are satisfiable for `m = 10^4`, `σ = 1`,
once `M` and `L₀` are chosen by the theorem. -/
example : ∃ M₀ : ℝ, ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ (m : ℝ) (n : ℤ),
    L₀ ≤ m → (n : ℝ) ≤ (m : ℝ) - ⌈M * Real.log m⌉ →
      m ^ (1 : ℝ) * (1 : ℝ) ^ (-(1 : ℝ)) * (1 : ℝ) ^ (1 : ℝ) * (3 : ℝ) ^ ((1 / 2 : ℝ) * ((n : ℝ) - m))
        ≤ (m ^ 300)⁻¹ := by
  obtain ⟨M₀, h⟩ := scale_separation_ceil 1 (1 / 2) 300 zero_le_one (by norm_num)
  obtain ⟨L₀, hL₀, h'⟩ := h 1 1 one_pos one_pos
  refine ⟨M₀, L₀, hL₀, fun M hM m n hm hn => ?_⟩
  have hm0 : (0 : ℝ) ≤ m := le_trans zero_le_one (le_trans hL₀ hm)
  exact h' M hM m n 1 hm zero_le_one (by
    have : (1 : ℝ) ≤ m := le_trans hL₀ hm
    linarith only [this]) hn

/-- Concrete hypotheses are satisfiable: the window and the bound `σ ≤ C m` hold for suitable
numbers (`m = 4`, `n = 3`, `M = 0`, `σ = 1`). -/
example : (0 : ℝ) * Real.log 4 ≤ (4 : ℝ) - (3 : ℤ) ∧ (1 : ℝ) ≤ 1 * 4 := by
  constructor <;> norm_num

theorem a23_log_le_mul (ε : ℝ) (hε : 0 < ε) : ∃ L : ℝ, ∀ m : ℝ, L ≤ m → Real.log m ≤ ε * m := by
  have h := Real.isLittleO_log_id_atTop.def hε
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp h
  refine ⟨max L 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have := hL m (le_trans (le_max_left _ _) hm)
  rw [Real.norm_of_nonneg (Real.log_nonneg hm1), Real.norm_of_nonneg (le_trans zero_le_one hm1 : (0 : ℝ) ≤ id m)] at this
  exact this

/-- **The window is short.** `⌈M log m⌉ ≤ κ m` for `m` large (`h_m ≤ m/10`, `h_K ≤ K/2`). -/
theorem ceil_log_le_mul (M κ : ℝ) (hκ : 0 < κ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ m : ℝ, L₀ ≤ m → (⌈M * Real.log m⌉ : ℝ) ≤ κ * m := by
  obtain ⟨L, hL⟩ := a23_log_le_mul (κ / (2 * (|M| + 1))) (by positivity)
  refine ⟨max (max L 1) (2 / κ), le_trans (le_max_right _ _) (le_max_left _ _), fun m hm => ?_⟩
  have hmL : L ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm1 : 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm2 : 2 / κ ≤ m := le_trans (le_max_right _ _) hm
  have hlog := hL m hmL
  have hMa : 0 < |M| + 1 := by positivity
  have h1 : M * Real.log m ≤ κ / 2 * m := by
    have h2 : M * Real.log m ≤ |M| * Real.log m :=
      mul_le_mul_of_nonneg_right (le_abs_self M) (Real.log_nonneg hm1)
    have h3 : |M| * Real.log m ≤ |M| * (κ / (2 * (|M| + 1)) * m) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg M)
    have h4 : |M| * (κ / (2 * (|M| + 1)) * m) ≤ κ / 2 * m := by
      have : |M| / (|M| + 1) ≤ 1 := by
        rw [div_le_one hMa]
        linarith only
      calc |M| * (κ / (2 * (|M| + 1)) * m) = (|M| / (|M| + 1)) * (κ / 2 * m) := by
            field_simp
        _ ≤ 1 * (κ / 2 * m) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = κ / 2 * m := one_mul _
    linarith only [h2, h3, h4]
  have h5 : (1 : ℝ) ≤ κ / 2 * m := by
    have := (div_le_iff₀ hκ).mp hm2
    linarith only [this]
  have h6 := Int.ceil_lt_add_one (M * Real.log m)
  linarith only [h1, h5, h6]

theorem a23_one_le_log {m : ℝ} (hm : 4 ≤ m) : 1 ≤ Real.log m := by
  rw [Real.le_log_iff_exp_le (by linarith only [hm])]
  have := Real.exp_one_lt_three
  linarith only [this, hm]

theorem deltaScale_pos {ε ρ m : ℝ} (hε : 0 < ε) (hm : 1 < m) : 0 < deltaScale ε ρ m := by
  unfold deltaScale
  exact mul_pos (mul_pos hε (Real.rpow_pos_of_pos (by linarith only [hm]) _))
    (Real.log_pos hm)

/-- **`m - n ≤ c δ_m⁻¹` forces `n ≥ m/2`**, for `m ≥ L₀ = max 4 (2c/ε)²`. -/
theorem half_le_of_window (c ε ρ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ L₀ : ℝ, 4 ≤ L₀ ∧ ∀ m n : ℝ, L₀ ≤ m →
      m - n ≤ c * (deltaScale ε ρ m)⁻¹ → m / 2 ≤ n := by
  refine ⟨max 4 ((2 * c / ε) ^ 2), le_max_left _ _, fun m n hm hwin => ?_⟩
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hm
  have hm0 : 0 < m := by linarith only [hm4]
  have hm1 : 1 ≤ m := by linarith only [hm4]
  have hlog := a23_one_le_log hm4
  set e : ℝ := (1 - ρ) / 2 with he
  have he0 : 0 ≤ e := by rw [he]; linarith only [hρ1]
  have he1 : e ≤ 1 / 2 := by rw [he]; linarith only [hρ0]
  set t : ℝ := m ^ e with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hm0 e
  have htle : t ≤ Real.sqrt m := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hm1 he1
  have hdel : deltaScale ε ρ m = ε * t⁻¹ * Real.log m := by
    unfold deltaScale
    rw [Real.rpow_neg hm0.le]
  have hinv : (deltaScale ε ρ m)⁻¹ ≤ Real.sqrt m / ε := by
    rw [hdel]
    have h1 : (ε * t⁻¹ * Real.log m)⁻¹ = t / (ε * Real.log m) := by
      field_simp
    rw [h1]
    calc t / (ε * Real.log m) ≤ t / ε := by
          refine div_le_div_of_nonneg_left ht0.le hε ?_
          exact le_mul_of_one_le_right hε.le hlog
      _ ≤ Real.sqrt m / ε := div_le_div_of_nonneg_right htle hε.le
  have hsq : 2 * c / ε ≤ Real.sqrt m := by
    have := Real.sqrt_le_sqrt (le_trans (le_max_right _ _) hm)
    rwa [Real.sqrt_sq (by positivity)] at this
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have h2 : c * (Real.sqrt m / ε) ≤ m / 2 := by
    have h3 : c / ε ≤ Real.sqrt m / 2 := by
      have : 2 * c / ε = 2 * (c / ε) := by ring
      linarith only [hsq, this]
    calc c * (Real.sqrt m / ε) = (c / ε) * Real.sqrt m := by ring
      _ ≤ (Real.sqrt m / 2) * Real.sqrt m :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg m)
      _ = m / 2 := by rw [div_mul_eq_mul_div, hsqm]
  have h4 : c * (deltaScale ε ρ m)⁻¹ ≤ c * (Real.sqrt m / ε) :=
    mul_le_mul_of_nonneg_left hinv hc.le
  linarith only [hwin, h4, h2]

/-- Comparison of `δ` at comparable scales: `m/2 ≤ n ≤ m` gives `δ_n ≤ 2 δ_m`. -/
theorem deltaScale_le_two_mul (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {m n : ℝ}
    (hn2 : 2 ≤ n) (hmn : m / 2 ≤ n) (hnm : n ≤ m) :
    deltaScale ε ρ n ≤ 2 * deltaScale ε ρ m := by
  have hn0 : 0 < n := by linarith only [hn2]
  have hm0 : 0 < m := by linarith only [hn2, hnm]
  have he0 : 0 ≤ (1 - ρ) / 2 := by linarith only [hρ1]
  have he1 : (1 - ρ) / 2 ≤ 1 := by linarith only [hρ0]
  have hpow : n ^ (-((1 - ρ) / 2)) ≤ 2 * m ^ (-((1 - ρ) / 2)) := by
    have h1 : (m / 2) ^ (-((1 - ρ) / 2)) = m ^ (-((1 - ρ) / 2)) * 2 ^ ((1 - ρ) / 2) := by
      rw [Real.div_rpow hm0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul]
    have h2 : n ^ (-((1 - ρ) / 2)) ≤ (m / 2) ^ (-((1 - ρ) / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith only [hm0]) hmn (by linarith only [he0])
    have h3 : (2 : ℝ) ^ ((1 - ρ) / 2) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 - ρ) / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
        _ = 2 := Real.rpow_one 2
    have hmp : 0 ≤ m ^ (-((1 - ρ) / 2)) := Real.rpow_nonneg hm0.le _
    calc n ^ (-((1 - ρ) / 2)) ≤ m ^ (-((1 - ρ) / 2)) * 2 ^ ((1 - ρ) / 2) := h1 ▸ h2
      _ ≤ m ^ (-((1 - ρ) / 2)) * 2 := mul_le_mul_of_nonneg_left h3 hmp
      _ = 2 * m ^ (-((1 - ρ) / 2)) := mul_comm _ _
  have hlog : Real.log n ≤ Real.log m := Real.log_le_log hn0 hnm
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith only [hn2])
  unfold deltaScale
  calc ε * n ^ (-((1 - ρ) / 2)) * Real.log n
      ≤ ε * (2 * m ^ (-((1 - ρ) / 2))) * Real.log m := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hε) hlog hlogn
          (mul_nonneg hε (mul_nonneg zero_le_two (Real.rpow_nonneg hm0.le _)))
    _ = 2 * (ε * m ^ (-((1 - ρ) / 2)) * Real.log m) := by ring

/-- **The window consequences used with the excess iteration**: for
`m ≥ L₀` and `m - n ≤ c δ_m⁻¹`, one has `n ≥ m/2`, `n ≥ 2` and `(m - n) δ_n ≤ 2 c`. -/
theorem window_consequences (c ε ρ : ℝ) (hc : 0 < c) (hε : 0 < ε) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ L₀ : ℝ, 4 ≤ L₀ ∧ ∀ m n : ℝ, L₀ ≤ m → n ≤ m →
      m - n ≤ c * (deltaScale ε ρ m)⁻¹ →
        m / 2 ≤ n ∧ 2 ≤ n ∧ deltaScale ε ρ n ≤ 2 * deltaScale ε ρ m ∧
          (m - n) * deltaScale ε ρ m ≤ c ∧ (m - n) * deltaScale ε ρ n ≤ 2 * c := by
  obtain ⟨L₀, hL₀, h⟩ := half_le_of_window c ε ρ hc hε hρ0 hρ1
  refine ⟨L₀, hL₀, fun m n hm hnm hwin => ?_⟩
  have hhalf := h m n hm hwin
  have hm4 : 4 ≤ m := le_trans hL₀ hm
  have hn2 : 2 ≤ n := by linarith only [hhalf, hm4]
  have hδ := deltaScale_le_two_mul ε ρ hε.le hρ0 hρ1 hn2 hhalf hnm
  have hδm : 0 < deltaScale ε ρ m := deltaScale_pos hε (by linarith only [hm4])
  have h1 : (m - n) * deltaScale ε ρ m ≤ c := by
    have := mul_le_mul_of_nonneg_right hwin hδm.le
    rwa [mul_assoc, inv_mul_cancel₀ hδm.ne', mul_one] at this
  refine ⟨hhalf, hn2, hδ, h1, ?_⟩
  have h2 : 0 ≤ m - n := by linarith only [hnm]
  calc (m - n) * deltaScale ε ρ n ≤ (m - n) * (2 * deltaScale ε ρ m) :=
        mul_le_mul_of_nonneg_left hδ h2
    _ = 2 * ((m - n) * deltaScale ε ρ m) := by ring
    _ ≤ 2 * c := by linarith only [h1]

/-- Witness: `c = 1`, `ε = 1`, `ρ = 1/2`; the window lemma is not vacuous because `n = m` always
satisfies `m - n = 0 ≤ c δ_m⁻¹` (the inverse is positive for `m ≥ 4`). -/
example : ∃ L₀ : ℝ, 4 ≤ L₀ ∧ ∀ m : ℝ, L₀ ≤ m →
    m - m ≤ 1 * (deltaScale 1 (1 / 2) m)⁻¹ ∧ m / 2 ≤ m := by
  refine ⟨4, le_refl _, fun m hm => ⟨?_, by linarith only [hm]⟩⟩
  have := deltaScale_pos (ε := 1) (ρ := 1 / 2) one_pos (by linarith only [hm])
  rw [sub_self]
  positivity

example : 2 ≤ (4 : ℝ) ∧ (8 : ℝ) / 2 ≤ 4 ∧ (4 : ℝ) ≤ 8 := by norm_num

end SuperdiffusionCLT.Section7
