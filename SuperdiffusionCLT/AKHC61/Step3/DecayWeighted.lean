/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The abstract weighted decay lemma, part 1: one step, comparison, profiles, constants

Pure real analysis on `ℕ`-indexed sequences, for the Step 3 induction of AK.HC Theorem 6.1
in the weighted form of `akhcRV2_weighted_recursion`
(`Step3/RecursionWC.lean`):

`F_n ≤ θ F_{n-Λ} + c F_n² + A Σ_{j<n-K₀} w^j (F_{n-j} - F_n) + B Σ_{j<n-K₀} w^j F(q(n-j))² + s_n`.

* `akhcDW_step`: split the drops at a block length `J ≥ Λ` and fill the hole: the first `J`
  drops are at most `(1-w)⁻¹(F_{n-J} - F_n)`, so with `a = A/(1-w)` and
  `D = 1 + a - (1-θ)/4` the bound becomes `F_n ≤ θ' F_{n-J} + (A/D) Σ_{j≥J} … + (B/D) Σ … + s/D`,
  `θ' = (θ+a)/D < 1`.
* `akhcDW_compare`: a comparison principle (strong induction) against any supersolution.
* `akhcDW_prof`, `akhcDW_prof_super`: the profile `σ` below a block start `P` and
  `max Φ (τ r^{i-N})` above it is a supersolution under explicit smallness conditions.
* The explicit constants `akhcDW_J`, `akhcDW_kappa`, `akhcDW_r = 3^{-κ}`, `akhcDW_eps`,
  `akhcDW_zeta`, `akhcDW_Z2`, `akhcDW_K`, `akhcDW_N0`, and the budget `akhcDW_budget`.

The decay theorem itself is `akhcDW_decay` in `Step3/DecayWeightedB.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-- `a := A/(1-w)`, the total weight of the drops after the block split. -/
def akhcDW_a (A w : ℝ) : ℝ := A / (1 - w)

/-- `D := 1 + a - (1-θ)/4`, the coefficient of `F_n` after the hole is filled. -/
def akhcDW_D (θ A w : ℝ) : ℝ := 1 + akhcDW_a A w - (1 - θ) / 4

/-- `θ' := (θ + a)/D`, the contraction factor over one block. -/
def akhcDW_thetaP (θ A w : ℝ) : ℝ := (θ + akhcDW_a A w) / akhcDW_D θ A w

theorem akhcDW_a_nonneg {A w : ℝ} (hA : 0 ≤ A) (hw1 : w < 1) : 0 ≤ akhcDW_a A w :=
  div_nonneg hA (by linarith only [hw1])

theorem akhcDW_D_pos {θ A w : ℝ} (hθ0 : 0 ≤ θ) (hA : 0 ≤ A) (hw1 : w < 1) :
    0 < akhcDW_D θ A w := by
  have := akhcDW_a_nonneg hA hw1
  unfold akhcDW_D
  linarith only [this, hθ0]

theorem akhcDW_thetaP_nonneg {θ A w : ℝ} (hθ0 : 0 ≤ θ) (hA : 0 ≤ A) (hw1 : w < 1) :
    0 ≤ akhcDW_thetaP θ A w :=
  div_nonneg (by linarith only [hθ0, akhcDW_a_nonneg hA hw1]) (akhcDW_D_pos hθ0 hA hw1).le

theorem akhcDW_geom_range_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, x ^ j ≤ 1 / (1 - x) := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hx0 hx1
  rw [pow_zero, ← Finset.range_eq_Ico] at h
  exact h

/-- **Block split and fill the hole.** One application of the recursion at `n`, with the drops of
the first `J ≥ Λ` lags bounded by `(1-w)⁻¹(F_{n-J} - F_n)` and the quadratic self term absorbed by
`F_n ≤ σ`, `cσ ≤ (1-θ)/4`. -/
theorem akhcDW_step {F : ℕ → ℝ} (hF0 : ∀ i, 0 ≤ F i) (hFanti : Antitone F)
    {θ c A B w σ : ℝ} {Λ J K0 n : ℕ} {q : ℕ → ℕ} {s : ℝ}
    (hθ0 : 0 ≤ θ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hcσ : c * σ ≤ (1 - θ) / 4) (hFn : F n ≤ σ) (hΛJ : Λ ≤ J) (hJn : K0 + J ≤ n)
    (hrec : F n ≤ θ * F (n - Λ) + c * F n ^ 2 +
      A * ∑ j ∈ Finset.range (n - K0), w ^ j * (F (n - j) - F n) +
      B * ∑ j ∈ Finset.range (n - K0), w ^ j * F (q (n - j)) ^ 2 + s) :
    F n ≤ akhcDW_thetaP θ A w * F (n - J) +
      A / akhcDW_D θ A w * ∑ j ∈ Finset.Ico J (n - K0), w ^ j * F (n - j) +
      B / akhcDW_D θ A w * ∑ j ∈ Finset.range (n - K0), w ^ j * F (q (n - j)) ^ 2 +
      s / akhcDW_D θ A w := by
  have hD0 : 0 < akhcDW_D θ A w := akhcDW_D_pos hθ0 hA hw1
  set D := akhcDW_D θ A w with hD
  set a := akhcDW_a A w with ha
  set St := ∑ j ∈ Finset.Ico J (n - K0), w ^ j * F (n - j) with hSt
  set Sl := ∑ j ∈ Finset.range (n - K0), w ^ j * F (q (n - j)) ^ 2 with hSl
  have hJK : J ≤ n - K0 := by omega
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => w ^ j * (F (n - j) - F n)) hJK
  have hdrop : 0 ≤ F (n - J) - F n := by
    have := hFanti (show n - J ≤ n by omega)
    linarith only [this]
  have h1 : ∑ j ∈ Finset.range J, w ^ j * (F (n - j) - F n) ≤
      (1 - w)⁻¹ * (F (n - J) - F n) := by
    have hle : ∀ j ∈ Finset.range J,
        w ^ j * (F (n - j) - F n) ≤ w ^ j * (F (n - J) - F n) := by
      intro j hj
      have hj' : j < J := Finset.mem_range.1 hj
      have : F (n - j) ≤ F (n - J) := hFanti (by omega)
      exact mul_le_mul_of_nonneg_left (by linarith only [this]) (pow_nonneg hw0 j)
    have hg := akhcDW_geom_range_le hw0 hw1 J
    calc ∑ j ∈ Finset.range J, w ^ j * (F (n - j) - F n)
        ≤ ∑ j ∈ Finset.range J, w ^ j * (F (n - J) - F n) := Finset.sum_le_sum hle
      _ = (∑ j ∈ Finset.range J, w ^ j) * (F (n - J) - F n) := by rw [Finset.sum_mul]
      _ ≤ (1 / (1 - w)) * (F (n - J) - F n) := mul_le_mul_of_nonneg_right hg hdrop
      _ = (1 - w)⁻¹ * (F (n - J) - F n) := by rw [one_div]
  have h2 : ∑ j ∈ Finset.Ico J (n - K0), w ^ j * (F (n - j) - F n) ≤ St := by
    apply Finset.sum_le_sum
    intro j _
    have := mul_nonneg (pow_nonneg hw0 j) (hF0 n)
    rw [mul_sub]
    linarith only [this]
  have hdropSum : A * ∑ j ∈ Finset.range (n - K0), w ^ j * (F (n - j) - F n) ≤
      a * F (n - J) - a * F n + A * St := by
    rw [← hsplit]
    have hA1 := mul_le_mul_of_nonneg_left h1 hA
    have hA2 := mul_le_mul_of_nonneg_left h2 hA
    have haeq : A * ((1 - w)⁻¹ * (F (n - J) - F n)) = a * F (n - J) - a * F n := by
      rw [ha, akhcDW_a]; ring
    rw [mul_add]
    linarith only [hA1, hA2, haeq]
  have hθ : θ * F (n - Λ) ≤ θ * F (n - J) :=
    mul_le_mul_of_nonneg_left (hFanti (by omega)) hθ0
  have hcF : c * F n ^ 2 ≤ (1 - θ) / 4 * F n := by
    have h3 : c * F n ≤ c * σ := mul_le_mul_of_nonneg_left hFn hc
    have h4 : c * F n * F n ≤ (1 - θ) / 4 * F n :=
      mul_le_mul_of_nonneg_right (h3.trans hcσ) (hF0 n)
    calc c * F n ^ 2 = c * F n * F n := by ring
      _ ≤ (1 - θ) / 4 * F n := h4
  have hX : D * F n ≤ (θ + a) * F (n - J) + A * St + B * Sl + s := by
    have hDF : D * F n = F n + a * F n - (1 - θ) / 4 * F n := by
      rw [hD, akhcDW_D]; ring
    rw [hDF]
    linarith only [hrec, hdropSum, hθ, hcF]
  calc F n = (D * F n) / D := by field_simp
    _ ≤ ((θ + a) * F (n - J) + A * St + B * Sl + s) / D :=
        div_le_div_of_nonneg_right hX hD0.le
    _ = akhcDW_thetaP θ A w * F (n - J) + A / D * St + B / D * Sl + s / D := by
        rw [akhcDW_thetaP]; ring

/-- **Comparison principle.** If `H` dominates `F` on `[Kσ, N)` and is a supersolution of the
reduced recursion of `akhcDW_step` from `N` on, then `F ≤ H` on `[Kσ, ∞)`. -/
theorem akhcDW_compare {F H : ℕ → ℝ} (hF0 : ∀ i, 0 ≤ F i) (hFanti : Antitone F)
    {θ c A B w σ : ℝ} {Λ J Kσ K0 N : ℕ} {q : ℕ → ℕ} {s : ℕ → ℝ}
    (hθ0 : 0 ≤ θ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hcσ : c * σ ≤ (1 - θ) / 4) (hFσ : ∀ i, Kσ ≤ i → F i ≤ σ)
    (hKK : Kσ ≤ K0) (hΛJ : Λ ≤ J) (hJ1 : 1 ≤ J) (hNJ : K0 + J ≤ N)
    (hq : ∀ i, K0 < i → Kσ ≤ q i ∧ q i < i)
    (hrec : ∀ n, N ≤ n → F n ≤ θ * F (n - Λ) + c * F n ^ 2 +
      A * ∑ j ∈ Finset.range (n - K0), w ^ j * (F (n - j) - F n) +
      B * ∑ j ∈ Finset.range (n - K0), w ^ j * F (q (n - j)) ^ 2 + s n)
    (hinit : ∀ i, Kσ ≤ i → i < N → F i ≤ H i)
    (hsuper : ∀ n, N ≤ n → akhcDW_thetaP θ A w * H (n - J) +
      A / akhcDW_D θ A w * ∑ j ∈ Finset.Ico J (n - K0), w ^ j * H (n - j) +
      B / akhcDW_D θ A w * ∑ j ∈ Finset.range (n - K0), w ^ j * H (q (n - j)) ^ 2 +
      s n / akhcDW_D θ A w ≤ H n) :
    ∀ i, Kσ ≤ i → F i ≤ H i := by
  have hD0 : 0 < akhcDW_D θ A w := akhcDW_D_pos hθ0 hA hw1
  have hθP := akhcDW_thetaP_nonneg hθ0 hA hw1
  intro i
  induction i using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hnN : n < N
    · exact hinit n hn hnN
    have hNn : N ≤ n := Nat.le_of_not_lt hnN
    have hstep := akhcDW_step hF0 hFanti (q := q) (s := s n) hθ0 hc hA hw0 hw1 hcσ
      (hFσ n hn) hΛJ (hNJ.trans hNn) (hrec n hNn)
    have hT1 : akhcDW_thetaP θ A w * F (n - J) ≤ akhcDW_thetaP θ A w * H (n - J) :=
      mul_le_mul_of_nonneg_left (ih (n - J) (by omega) (by omega)) hθP
    have hT2 : ∑ j ∈ Finset.Ico J (n - K0), w ^ j * F (n - j) ≤
        ∑ j ∈ Finset.Ico J (n - K0), w ^ j * H (n - j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_Ico.1 hj
      exact mul_le_mul_of_nonneg_left (ih (n - j) (by omega) (by omega)) (pow_nonneg hw0 j)
    have hT3 : ∑ j ∈ Finset.range (n - K0), w ^ j * F (q (n - j)) ^ 2 ≤
        ∑ j ∈ Finset.range (n - K0), w ^ j * H (q (n - j)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.1 hj
      obtain ⟨hq1, hq2⟩ := hq (n - j) (by omega)
      have hFH : F (q (n - j)) ≤ H (q (n - j)) := ih _ (by omega) hq1
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hF0 _) hFH 2) (pow_nonneg hw0 j)
    have hT2' := mul_le_mul_of_nonneg_left hT2 (div_nonneg hA hD0.le)
    have hT3' := mul_le_mul_of_nonneg_left hT3 (div_nonneg hB hD0.le)
    have hsup := hsuper n hNn
    linarith only [hstep, hT1, hT2', hT3', hsup]

/-- **The comparison profile**: `σ` below `P`, and `max Φ (τ r^{i-N})` from `P` on. -/
def akhcDW_prof (σ : ℝ) (P : ℕ) (Φ τ r : ℝ) (N i : ℕ) : ℝ :=
  if i < P then σ else max Φ (τ * r ^ (i - N))

theorem akhcDW_prof_of_ge {σ Φ τ r : ℝ} {P N i : ℕ} (hi : P ≤ i) :
    akhcDW_prof σ P Φ τ r N i = max Φ (τ * r ^ (i - N)) := by
  unfold akhcDW_prof
  rw [ite_eq_right (not_lt.2 hi)]

theorem akhcDW_prof_nonneg {σ Φ τ r : ℝ} {P N : ℕ} (hσ0 : 0 ≤ σ) (hΦ0 : 0 ≤ Φ) (i : ℕ) :
    0 ≤ akhcDW_prof σ P Φ τ r N i := by
  unfold akhcDW_prof
  split_ifs
  · exact hσ0
  · exact le_max_of_le_left hΦ0

theorem akhcDW_prof_le_sigma {σ Φ τ r : ℝ} {P N : ℕ} (hΦσ : Φ ≤ σ) (hτσ : τ ≤ σ)
    (hτ0 : 0 ≤ τ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (i : ℕ) :
    akhcDW_prof σ P Φ τ r N i ≤ σ := by
  unfold akhcDW_prof
  split_ifs
  · exact le_rfl
  · exact max_le hΦσ ((mul_le_of_le_one_right hτ0 (pow_le_one₀ hr0 hr1)).trans hτσ)

/-- **The profile decays at most at rate `r` per scale from `P` on.** -/
theorem akhcDW_prof_ratio {σ Φ τ r : ℝ} {P N : ℕ} (hΦ0 : 0 ≤ Φ) (hτ0 : 0 ≤ τ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) {i n : ℕ} (hPi : P ≤ i) (hin : i ≤ n) :
    r ^ (n - i) * akhcDW_prof σ P Φ τ r N i ≤ akhcDW_prof σ P Φ τ r N n := by
  rw [akhcDW_prof_of_ge hPi, akhcDW_prof_of_ge (hPi.trans hin),
    mul_max_of_nonneg _ _ (pow_nonneg hr0 _)]
  apply max_le_max
  · exact mul_le_of_le_one_left hΦ0 (pow_le_one₀ hr0 hr1)
  · rw [mul_left_comm, ← pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (by omega)) hτ0

/-- **The profile is a supersolution** of the reduced recursion of `akhcDW_step`, once the lag
squares are `ε`-small against the profile (`hlag`), the source is `ζ`-small (`hs`), the part of
the sums reaching below `P` has decayed (`hfar`), and the budget `hbudget` holds. -/
theorem akhcDW_prof_super {θ A B w σ Φ τ r v ε ζ : ℝ} {J K0 P N ℓ : ℕ} {q : ℕ → ℕ}
    {s : ℕ → ℝ}
    (hθ0 : 0 ≤ θ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hv0 : 0 ≤ v) (hv1 : v < 1) (hwv : w ≤ v * r)
    (hΦ0 : 0 ≤ Φ) (hτ0 : 0 ≤ τ) (hΦσ : Φ ≤ σ) (hτσ : τ ≤ σ) (hε0 : 0 ≤ ε) (hζ0 : 0 ≤ ζ)
    (hKP : K0 ≤ P) (hPJ : P + J ≤ N) (hPl : P + ℓ ≤ N)
    (hqP : ∀ i, P + ℓ < i → P ≤ q i)
    (hlag : ∀ i, P + ℓ < i →
      max Φ (τ * r ^ (q i - N)) ^ 2 ≤ ε * max Φ (τ * r ^ (i - N)))
    (hs : ∀ n, N ≤ n → s n ≤ ζ * (Φ + τ * r ^ (n - N)))
    (hfar : (A * σ + B * σ ^ 2) * w ^ (N - P - ℓ) ≤ ζ * (1 - w) * τ)
    (hbudget : akhcDW_thetaP θ A w + r ^ J * (A / akhcDW_D θ A w * (v ^ J / (1 - v)) +
      B / akhcDW_D θ A w * (ε / (1 - v)) + 3 * ζ / akhcDW_D θ A w) ≤ r ^ J) :
    ∀ n, N ≤ n → akhcDW_thetaP θ A w * akhcDW_prof σ P Φ τ r N (n - J) +
      A / akhcDW_D θ A w *
        ∑ j ∈ Finset.Ico J (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (n - j) +
      B / akhcDW_D θ A w *
        ∑ j ∈ Finset.range (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (q (n - j)) ^ 2 +
      s n / akhcDW_D θ A w ≤ akhcDW_prof σ P Φ τ r N n := by
  intro n hn
  have hD0 : 0 < akhcDW_D θ A w := akhcDW_D_pos hθ0 hA hw1
  have hθP := akhcDW_thetaP_nonneg hθ0 hA hw1
  set D := akhcDW_D θ A w with hD
  set θ' := akhcDW_thetaP θ A w with hθ'
  have hσ0 : 0 ≤ σ := hΦ0.trans hΦσ
  have h1w : 0 < 1 - w := by linarith only [hw1]
  have hwr : w ≤ r := hwv.trans (mul_le_of_le_one_left hr0.le hv1.le)
  have hH0 : ∀ i, 0 ≤ akhcDW_prof σ P Φ τ r N i := fun i => akhcDW_prof_nonneg hσ0 hΦ0 i
  have hHσ : ∀ i, akhcDW_prof σ P Φ τ r N i ≤ σ :=
    fun i => akhcDW_prof_le_sigma hΦσ hτσ hτ0 hr0.le hr1 i
  have hrat : ∀ i, P ≤ i → i ≤ n →
      r ^ (n - i) * akhcDW_prof σ P Φ τ r N i ≤ akhcDW_prof σ P Φ τ r N n :=
    fun i h1 h2 => akhcDW_prof_ratio hΦ0 hτ0 hr0.le hr1 h1 h2
  have hHn : akhcDW_prof σ P Φ τ r N n = max Φ (τ * r ^ (n - N)) :=
    akhcDW_prof_of_ge (by omega)
  have hHn0 := hH0 n
  set Hn := akhcDW_prof σ P Φ τ r N n with hHndef
  have hT1 : r ^ J * akhcDW_prof σ P Φ τ r N (n - J) ≤ Hn := by
    have h := hrat (n - J) (by omega) (by omega)
    rwa [show n - (n - J) = J by omega] at h
  have hwj : ∀ j : ℕ, w ^ j ≤ v ^ j * r ^ j := fun j => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hw0 hwv j
  -- the drop tail
  have hT2 : ∑ j ∈ Finset.Ico J (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (n - j) ≤
      v ^ J / (1 - v) * Hn + σ * (w ^ (n - P) / (1 - w)) := by
    rw [← Finset.sum_Ico_consecutive _ (show J ≤ n - P by omega)
      (show n - P ≤ n - K0 by omega)]
    have hA1 : ∑ j ∈ Finset.Ico J (n - P), w ^ j * akhcDW_prof σ P Φ τ r N (n - j) ≤
        (∑ j ∈ Finset.Ico J (n - P), v ^ j) * Hn := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_Ico.1 hj
      have h1 := hrat (n - j) (by omega) (by omega)
      rw [show n - (n - j) = j by omega] at h1
      calc w ^ j * akhcDW_prof σ P Φ τ r N (n - j)
          ≤ (v ^ j * r ^ j) * akhcDW_prof σ P Φ τ r N (n - j) :=
            mul_le_mul_of_nonneg_right (hwj j) (hH0 _)
        _ = v ^ j * (r ^ j * akhcDW_prof σ P Φ τ r N (n - j)) := by ring
        _ ≤ v ^ j * Hn := mul_le_mul_of_nonneg_left h1 (pow_nonneg hv0 j)
    have hA2 : ∑ j ∈ Finset.Ico (n - P) (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (n - j) ≤
        σ * ∑ j ∈ Finset.Ico (n - P) (n - K0), w ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [mul_comm σ]
      exact mul_le_mul_of_nonneg_left (hHσ _) (pow_nonneg hw0 j)
    have hg1 := geom_sum_Ico_le_of_lt_one (m := J) (n := n - P) hv0 hv1
    have hg2 := geom_sum_Ico_le_of_lt_one (m := n - P) (n := n - K0) hw0 hw1
    have hB1 := mul_le_mul_of_nonneg_right hg1 hHn0
    have hB2 := mul_le_mul_of_nonneg_left hg2 hσ0
    linarith only [hA1, hA2, hB1, hB2]
  -- the lag squares
  have hT3 : ∑ j ∈ Finset.range (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (q (n - j)) ^ 2 ≤
      ε / (1 - v) * Hn + σ ^ 2 * (w ^ (n - P - ℓ) / (1 - w)) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show n - P - ℓ ≤ n - K0 by omega)]
    have hA1 : ∑ j ∈ Finset.range (n - P - ℓ),
        w ^ j * akhcDW_prof σ P Φ τ r N (q (n - j)) ^ 2 ≤
        ε * ((∑ j ∈ Finset.range (n - P - ℓ), v ^ j) * Hn) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.1 hj
      have hi : P + ℓ < n - j := by omega
      have hqi := hqP (n - j) hi
      have hlagi := hlag (n - j) hi
      rw [← akhcDW_prof_of_ge (σ := σ) hqi,
        ← akhcDW_prof_of_ge (σ := σ) (show P ≤ n - j by omega)] at hlagi
      have h1 := hrat (n - j) (by omega) (by omega)
      rw [show n - (n - j) = j by omega] at h1
      calc w ^ j * akhcDW_prof σ P Φ τ r N (q (n - j)) ^ 2
          ≤ w ^ j * (ε * akhcDW_prof σ P Φ τ r N (n - j)) :=
            mul_le_mul_of_nonneg_left hlagi (pow_nonneg hw0 j)
        _ ≤ (v ^ j * r ^ j) * (ε * akhcDW_prof σ P Φ τ r N (n - j)) :=
            mul_le_mul_of_nonneg_right (hwj j) (mul_nonneg hε0 (hH0 _))
        _ = ε * (v ^ j * (r ^ j * akhcDW_prof σ P Φ τ r N (n - j))) := by ring
        _ ≤ ε * (v ^ j * Hn) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (pow_nonneg hv0 j)) hε0
    have hA2 : ∑ j ∈ Finset.Ico (n - P - ℓ) (n - K0),
        w ^ j * akhcDW_prof σ P Φ τ r N (q (n - j)) ^ 2 ≤
        σ ^ 2 * ∑ j ∈ Finset.Ico (n - P - ℓ) (n - K0), w ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [mul_comm (σ ^ 2)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hH0 _) (hHσ _) 2) (pow_nonneg hw0 j)
    have hg1 := akhcDW_geom_range_le hv0 hv1 (n - P - ℓ)
    have hg2 := geom_sum_Ico_le_of_lt_one (m := n - P - ℓ) (n := n - K0) hw0 hw1
    have hB1 : ε * ((∑ j ∈ Finset.range (n - P - ℓ), v ^ j) * Hn) ≤ ε / (1 - v) * Hn := by
      have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg1 hHn0) hε0
      calc ε * ((∑ j ∈ Finset.range (n - P - ℓ), v ^ j) * Hn) ≤ ε * (1 / (1 - v) * Hn) := h1
        _ = ε / (1 - v) * Hn := by ring
    have hB2 := mul_le_mul_of_nonneg_left hg2 (sq_nonneg σ)
    linarith only [hA1, hA2, hB1, hB2]
  -- the part of the sums below `P`
  have hwpow : w ^ (n - P) ≤ w ^ (n - P - ℓ) := pow_le_pow_of_le_one hw0 hw1.le (by omega)
  have hwsplit : w ^ (n - P - ℓ) ≤ w ^ (N - P - ℓ) * r ^ (n - N) := by
    rw [show n - P - ℓ = (N - P - ℓ) + (n - N) by omega, pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hwr (n - N)) (pow_nonneg hw0 _)
  have hτH : τ * r ^ (n - N) ≤ Hn := by rw [hHn]; exact le_max_right _ _
  have hΦH : Φ ≤ Hn := by rw [hHn]; exact le_max_left _ _
  have hfar' : A * (σ * (w ^ (n - P) / (1 - w))) + B * (σ ^ 2 * (w ^ (n - P - ℓ) / (1 - w))) ≤
      ζ * Hn := by
    have key : A * σ * w ^ (n - P) + B * σ ^ 2 * w ^ (n - P - ℓ) ≤
        ζ * (1 - w) * (τ * r ^ (n - N)) := by
      have e1 : A * σ * w ^ (n - P) ≤ A * σ * w ^ (n - P - ℓ) :=
        mul_le_mul_of_nonneg_left hwpow (mul_nonneg hA hσ0)
      have e2 : (A * σ + B * σ ^ 2) * w ^ (n - P - ℓ) ≤
          (A * σ + B * σ ^ 2) * (w ^ (N - P - ℓ) * r ^ (n - N)) :=
        mul_le_mul_of_nonneg_left hwsplit (by positivity)
      have e3 : (A * σ + B * σ ^ 2) * w ^ (N - P - ℓ) * r ^ (n - N) ≤
          ζ * (1 - w) * τ * r ^ (n - N) :=
        mul_le_mul_of_nonneg_right hfar (pow_nonneg hr0.le _)
      linear_combination e1 + e2 + e3
    calc A * (σ * (w ^ (n - P) / (1 - w))) + B * (σ ^ 2 * (w ^ (n - P - ℓ) / (1 - w)))
        = (A * σ * w ^ (n - P) + B * σ ^ 2 * w ^ (n - P - ℓ)) / (1 - w) := by ring
      _ ≤ (ζ * (1 - w) * (τ * r ^ (n - N))) / (1 - w) := div_le_div_of_nonneg_right key h1w.le
      _ = ζ * (τ * r ^ (n - N)) := by field_simp
      _ ≤ ζ * Hn := mul_le_mul_of_nonneg_left hτH hζ0
  have hsn : s n ≤ 2 * ζ * Hn := by
    have h1 := hs n hn
    have h2 : ζ * (Φ + τ * r ^ (n - N)) ≤ ζ * (2 * Hn) :=
      mul_le_mul_of_nonneg_left (by linarith only [hτH, hΦH]) hζ0
    linarith only [h1, h2]
  have hU : θ' * akhcDW_prof σ P Φ τ r N (n - J) +
      A / D * ∑ j ∈ Finset.Ico J (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (n - j) +
      B / D * ∑ j ∈ Finset.range (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (q (n - j)) ^ 2 +
      s n / D ≤ θ' * akhcDW_prof σ P Φ τ r N (n - J) +
        (A / D * (v ^ J / (1 - v)) + B / D * (ε / (1 - v)) + 3 * ζ / D) * Hn := by
    have a1 := mul_le_mul_of_nonneg_left hT2 (div_nonneg hA hD0.le)
    have a2 := mul_le_mul_of_nonneg_left hT3 (div_nonneg hB hD0.le)
    have a3 := div_le_div_of_nonneg_right hfar' hD0.le
    have a4 := div_le_div_of_nonneg_right hsn hD0.le
    linear_combination a1 + a2 + a3 + a4
  have hfin : r ^ J * (θ' * akhcDW_prof σ P Φ τ r N (n - J) +
      A / D * ∑ j ∈ Finset.Ico J (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (n - j) +
      B / D * ∑ j ∈ Finset.range (n - K0), w ^ j * akhcDW_prof σ P Φ τ r N (q (n - j)) ^ 2 +
      s n / D) ≤ r ^ J * Hn := by
    have b1 := mul_le_mul_of_nonneg_left hU (pow_nonneg hr0.le J)
    have b2 : θ' * (r ^ J * akhcDW_prof σ P Φ τ r N (n - J)) ≤ θ' * Hn :=
      mul_le_mul_of_nonneg_left hT1 hθP
    have b3 := mul_le_mul_of_nonneg_right hbudget hHn0
    linear_combination b1 + b2 + b3
  exact le_of_mul_le_mul_left hfin (pow_pos hr0 J)

/-! ## The explicit constants -/

/-- `g := 1 - θ'`, the gap of the block contraction. -/
def akhcDW_g (θ A w : ℝ) : ℝ := 1 - akhcDW_thetaP θ A w

/-- `√w`, the weight ratio the profiles are allowed to lose per scale. -/
def akhcDW_sw (w : ℝ) : ℝ := Real.sqrt w

/-- The lag-smallness level `ε := g D (1 - √w) / (4(B+1))`. -/
def akhcDW_eps (θ A B w : ℝ) : ℝ :=
  akhcDW_g θ A w * akhcDW_D θ A w * (1 - akhcDW_sw w) / (4 * (B + 1))

/-- The source-smallness level `ζ := g D / 12`. -/
def akhcDW_zeta (θ A w : ℝ) : ℝ := akhcDW_g θ A w * akhcDW_D θ A w / 12

/-- The block length forced by the drop tail: `√w^{J_A} ≤ g D (1 - √w)/(4(A+1))`. -/
def akhcDW_JA (θ A w : ℝ) : ℕ :=
  ⌈Real.log (akhcDW_g θ A w * akhcDW_D θ A w * (1 - akhcDW_sw w) / (4 * (A + 1))) /
    Real.log (akhcDW_sw w)⌉₊

/-- The block length `J := max{Λ, 1, J_A}`. -/
def akhcDW_J (θ A w : ℝ) (Λ : ℕ) : ℕ := max Λ (max 1 (akhcDW_JA θ A w))

/-- **The decay rate** `κ := min{g/(4 J log 3), log(1/w)/(2 log 3)}`. -/
def akhcDW_kappa (θ A w : ℝ) (Λ : ℕ) : ℝ :=
  min (akhcDW_g θ A w / (4 * (akhcDW_J θ A w Λ : ℝ) * Real.log 3))
    (-Real.log w / (2 * Real.log 3))

/-- The per-scale ratio `r := 3^{-κ}`. -/
def akhcDW_r (θ A w : ℝ) (Λ : ℕ) : ℝ := (3 : ℝ) ^ (-akhcDW_kappa θ A w Λ)

/-- The delay after which the part of the sums below a block start has decayed:
`w^{Z₂} ≤ 2ζ(1-w)/(A+B+1)`. -/
def akhcDW_Z2 (θ A B w : ℝ) : ℕ :=
  ⌈Real.log (2 * akhcDW_zeta θ A w * (1 - w) / (A + B + 1)) / Real.log w⌉₊

/-- The delay `Z := ℓ + J + M + Z₂` from a block start to the start of its profile. -/
def akhcDW_Zb (θ A B w : ℝ) (Λ ℓ M : ℕ) : ℕ := ℓ + akhcDW_J θ A w Λ + M + akhcDW_Z2 θ A B w

/-- The number of squaring blocks, `K := ⌊log₂ ⌈2κM⌉⌋ + 1`. -/
def akhcDW_K (θ A w : ℝ) (Λ M : ℕ) : ℕ := Nat.log 2 ⌈2 * akhcDW_kappa θ A w Λ * M⌉₊ + 1

/-- **The start of the decay**, `N₀ := K₀ + K (Z + M) + Z`. -/
def akhcDW_N0 (θ A B w : ℝ) (Λ K0 ℓ M : ℕ) : ℕ :=
  K0 + akhcDW_K θ A w Λ M * (akhcDW_Zb θ A B w Λ ℓ M + M) + akhcDW_Zb θ A B w Λ ℓ M

/-- `x^n ≤ t` once `n ≥ ⌈log t / log x⌉`, for `0 < x < 1`, `0 < t`. -/
theorem akhcDW_pow_le_of_ceil_le {x t : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (ht : 0 < t) {n : ℕ}
    (hn : ⌈Real.log t / Real.log x⌉₊ ≤ n) : x ^ n ≤ t := by
  have hlx : Real.log x < 0 := Real.log_neg hx0 hx1
  have hn' : Real.log t / Real.log x ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h1 : (n : ℝ) * Real.log x ≤ Real.log t := by
    have h2 := mul_le_mul_of_nonpos_right hn' hlx.le
    rwa [div_mul_cancel₀ _ hlx.ne] at h2
  calc x ^ n = Real.exp (Real.log (x ^ n)) := (Real.exp_log (pow_pos hx0 n)).symm
    _ = Real.exp ((n : ℝ) * Real.log x) := by rw [Real.log_pow]
    _ ≤ Real.exp (Real.log t) := Real.exp_le_exp.2 h1
    _ = t := Real.exp_log ht

section Constants

variable {θ A B w : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hw0 : 0 < w)
  (hw1 : w < 1)

include hθ0 hA hw1 in
theorem akhcDW_gD : akhcDW_g θ A w * akhcDW_D θ A w = 3 / 4 * (1 - θ) := by
  have hD0 := akhcDW_D_pos hθ0 hA hw1
  rw [akhcDW_g, akhcDW_thetaP, sub_mul, div_mul_cancel₀ _ hD0.ne', akhcDW_D]
  ring

include hθ0 hθ1 hA hw1 in
theorem akhcDW_g_pos : 0 < akhcDW_g θ A w := by
  have hD0 := akhcDW_D_pos hθ0 hA hw1
  have h := akhcDW_gD hθ0 hA hw1
  have h1 : 0 < akhcDW_g θ A w * akhcDW_D θ A w := by rw [h]; linarith only [hθ1]
  exact pos_of_mul_pos_left h1 hD0.le

include hθ0 hA hw1 in
theorem akhcDW_g_le_one : akhcDW_g θ A w ≤ 1 := by
  have := akhcDW_thetaP_nonneg hθ0 hA hw1
  unfold akhcDW_g
  linarith only [this]

include hw0 in
theorem akhcDW_sw_pos : 0 < akhcDW_sw w := Real.sqrt_pos.2 hw0

include hw0 hw1 in
theorem akhcDW_sw_lt_one : akhcDW_sw w < 1 := by
  unfold akhcDW_sw
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_lt_sqrt hw0.le hw1

include hw0 in
theorem akhcDW_sw_sq : akhcDW_sw w * akhcDW_sw w = w := Real.mul_self_sqrt hw0.le

include hθ0 hθ1 hA hw0 hw1 hB in
theorem akhcDW_eps_pos : 0 < akhcDW_eps θ A B w := by
  have hg := akhcDW_g_pos hθ0 hθ1 hA hw1
  have hD0 := akhcDW_D_pos hθ0 hA hw1
  have hsw := akhcDW_sw_lt_one hw0 hw1
  unfold akhcDW_eps
  have : 0 < 1 - akhcDW_sw w := by linarith only [hsw]
  positivity

include hθ0 hA hw0 hw1 hB in
theorem akhcDW_eps_le : akhcDW_eps θ A B w ≤ 1 / 4 := by
  have hgD := akhcDW_gD hθ0 hA hw1
  have hsw0 := akhcDW_sw_pos hw0
  have hsw1 := akhcDW_sw_lt_one hw0 hw1
  unfold akhcDW_eps
  rw [hgD, div_le_iff₀ (by positivity)]
  have h1 : 3 / 4 * (1 - θ) * (1 - akhcDW_sw w) ≤ 3 / 4 * 1 * 1 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hθ0]) (by norm_num))
      (by linarith only [hsw0]) (by linarith only [hsw1]) (by norm_num)
  nlinarith only [h1, hB]

include hθ0 hθ1 hA hw1 in
theorem akhcDW_zeta_pos : 0 < akhcDW_zeta θ A w := by
  have hg := akhcDW_g_pos hθ0 hθ1 hA hw1
  have hD0 := akhcDW_D_pos hθ0 hA hw1
  unfold akhcDW_zeta
  positivity

theorem akhcDW_one_le_J (Λ : ℕ) : 1 ≤ akhcDW_J θ A w Λ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem akhcDW_Λ_le_J (Λ : ℕ) : Λ ≤ akhcDW_J θ A w Λ := le_max_left _ _

theorem akhcDW_JA_le_J (Λ : ℕ) : akhcDW_JA θ A w ≤ akhcDW_J θ A w Λ :=
  (le_max_right _ _).trans (le_max_right _ _)

include hθ0 hθ1 hA hw0 hw1 in
theorem akhcDW_kappa_pos (Λ : ℕ) : 0 < akhcDW_kappa θ A w Λ := by
  have hg := akhcDW_g_pos hθ0 hθ1 hA hw1
  have hJ : (1 : ℝ) ≤ (akhcDW_J θ A w Λ : ℝ) := by exact_mod_cast akhcDW_one_le_J Λ
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlw : Real.log w < 0 := Real.log_neg hw0 hw1
  unfold akhcDW_kappa
  refine lt_min (by positivity) (div_pos (by linarith only [hlw]) (by positivity))

theorem akhcDW_r_pos (Λ : ℕ) : 0 < akhcDW_r θ A w Λ := by
  unfold akhcDW_r
  positivity

include hθ0 hθ1 hA hw0 hw1 in
theorem akhcDW_r_lt_one (Λ : ℕ) : akhcDW_r θ A w Λ < 1 := by
  unfold akhcDW_r
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith only [akhcDW_kappa_pos hθ0 hθ1 hA hw0 hw1 Λ])

theorem akhcDW_r_pow (Λ n : ℕ) :
    akhcDW_r θ A w Λ ^ n = (3 : ℝ) ^ (-(akhcDW_kappa θ A w Λ * (n : ℝ))) := by
  unfold akhcDW_r
  rw [← Real.rpow_mul_natCast (by norm_num), neg_mul]

include hθ0 hθ1 hA hw1 in
theorem akhcDW_r_pow_J (Λ : ℕ) :
    1 - akhcDW_g θ A w / 4 ≤ akhcDW_r θ A w Λ ^ akhcDW_J θ A w Λ := by
  have hg := akhcDW_g_pos hθ0 hθ1 hA hw1
  have hJ : (1 : ℝ) ≤ (akhcDW_J θ A w Λ : ℝ) := by exact_mod_cast akhcDW_one_le_J Λ
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hk : akhcDW_kappa θ A w Λ * (4 * (akhcDW_J θ A w Λ : ℝ) * Real.log 3) ≤
      akhcDW_g θ A w := by
    rw [← le_div_iff₀ (by positivity)]
    exact min_le_left _ _
  rw [akhcDW_r_pow, Real.rpow_def_of_pos (by norm_num)]
  have he := Real.add_one_le_exp
    (Real.log 3 * -(akhcDW_kappa θ A w Λ * (akhcDW_J θ A w Λ : ℝ)))
  linarith only [he, hk]

include hw0 in
theorem akhcDW_sw_le_r (Λ : ℕ) : akhcDW_sw w ≤ akhcDW_r θ A w Λ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hk : akhcDW_kappa θ A w Λ * (2 * Real.log 3) ≤ -Real.log w := by
    rw [← le_div_iff₀ (by positivity)]
    exact min_le_right _ _
  unfold akhcDW_sw akhcDW_r
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hw0, Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.2
  linarith only [hk]

include hw0 in
/-- `v := w/r ≤ √w`. -/
theorem akhcDW_v_le_sw (Λ : ℕ) : w / akhcDW_r θ A w Λ ≤ akhcDW_sw w := by
  have hsw0 := akhcDW_sw_pos hw0
  have hle := akhcDW_sw_le_r hw0 (θ := θ) (A := A) Λ
  calc w / akhcDW_r θ A w Λ ≤ w / akhcDW_sw w := div_le_div_of_nonneg_left hw0.le hsw0 hle
    _ = akhcDW_sw w := by
      rw [div_eq_iff hsw0.ne']
      exact (akhcDW_sw_sq hw0).symm

include hθ0 hθ1 hA hB hw0 hw1 in
/-- **The budget** of `akhcDW_prof_super` holds at the explicit constants, with `v := w/r`. -/
theorem akhcDW_budget (Λ : ℕ) :
    akhcDW_thetaP θ A w + akhcDW_r θ A w Λ ^ akhcDW_J θ A w Λ *
      (A / akhcDW_D θ A w * ((w / akhcDW_r θ A w Λ) ^ akhcDW_J θ A w Λ /
          (1 - w / akhcDW_r θ A w Λ)) +
        B / akhcDW_D θ A w * (akhcDW_eps θ A B w / (1 - w / akhcDW_r θ A w Λ)) +
        3 * akhcDW_zeta θ A w / akhcDW_D θ A w) ≤
      akhcDW_r θ A w Λ ^ akhcDW_J θ A w Λ := by
  have hg := akhcDW_g_pos hθ0 hθ1 hA hw1
  have hg1 := akhcDW_g_le_one hθ0 hA hw1
  have hD0 := akhcDW_D_pos hθ0 hA hw1
  have hsw0 := akhcDW_sw_pos hw0
  have hsw1 := akhcDW_sw_lt_one hw0 hw1
  have hr0 := akhcDW_r_pos (θ := θ) (A := A) (w := w) Λ
  have hrJ := akhcDW_r_pow_J hθ0 hθ1 hA hw1 Λ
  have hv := akhcDW_v_le_sw hw0 (θ := θ) (A := A) Λ
  have hε0 := akhcDW_eps_pos hθ0 hθ1 hA hB hw0 hw1
  set g := akhcDW_g θ A w with hgdef
  set D := akhcDW_D θ A w with hDdef
  set sw := akhcDW_sw w with hswdef
  set r := akhcDW_r θ A w Λ with hrdef
  set J := akhcDW_J θ A w Λ with hJdef
  set v := w / r with hvdef
  have hv0 : 0 ≤ v := div_nonneg hw0.le hr0.le
  have h1sw : 0 < 1 - sw := by linarith only [hsw1]
  have h1v : 1 - sw ≤ 1 - v := by linarith only [hv]
  have h1v0 : 0 < 1 - v := by linarith only [h1sw, h1v]
  -- the drop tail
  have hswJ : sw ^ J ≤ g * D * (1 - sw) / (4 * (A + 1)) := by
    have hJA : sw ^ J ≤ sw ^ akhcDW_JA θ A w :=
      pow_le_pow_of_le_one hsw0.le hsw1.le (akhcDW_JA_le_J Λ)
    refine hJA.trans (akhcDW_pow_le_of_ceil_le hsw0 hsw1 (by positivity) le_rfl)
  have hX1 : A / D * (v ^ J / (1 - v)) ≤ g / 4 := by
    have hvJ : v ^ J ≤ sw ^ J := pow_le_pow_left₀ hv0 hv J
    have h2 : v ^ J / (1 - v) ≤ sw ^ J / (1 - sw) :=
      div_le_div₀ (pow_nonneg hsw0.le J) hvJ h1sw h1v
    have h3 : sw ^ J / (1 - sw) ≤ g * D / (4 * (A + 1)) := by
      rw [div_le_iff₀ h1sw]
      calc sw ^ J ≤ g * D * (1 - sw) / (4 * (A + 1)) := hswJ
        _ = g * D / (4 * (A + 1)) * (1 - sw) := by ring
    have h4 : A / D * (g * D / (4 * (A + 1))) ≤ g / 4 := by
      rw [show A / D * (g * D / (4 * (A + 1))) = g / 4 * (A / (A + 1)) by
        field_simp]
      have : A / (A + 1) ≤ 1 := (div_le_one (by linarith only [hA])).2 (by linarith only)
      exact mul_le_of_le_one_right (by positivity) this
    calc A / D * (v ^ J / (1 - v)) ≤ A / D * (g * D / (4 * (A + 1))) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (div_nonneg hA hD0.le)
      _ ≤ g / 4 := h4
  have hX2 : B / D * (akhcDW_eps θ A B w / (1 - v)) ≤ g / 4 := by
    have h2 : akhcDW_eps θ A B w / (1 - v) ≤ akhcDW_eps θ A B w / (1 - sw) :=
      div_le_div_of_nonneg_left hε0.le h1sw h1v
    have h3 : B / D * (akhcDW_eps θ A B w / (1 - sw)) = g / 4 * (B / (B + 1)) := by
      unfold akhcDW_eps
      rw [← hgdef, ← hDdef, ← hswdef]
      field_simp
    have h4 : B / (B + 1) ≤ 1 := (div_le_one (by linarith only [hB])).2 (by linarith only)
    calc B / D * (akhcDW_eps θ A B w / (1 - v)) ≤ B / D * (akhcDW_eps θ A B w / (1 - sw)) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hB hD0.le)
      _ = g / 4 * (B / (B + 1)) := h3
      _ ≤ g / 4 := mul_le_of_le_one_right (by positivity) h4
  have hX3 : 3 * akhcDW_zeta θ A w / D = g / 4 := by
    unfold akhcDW_zeta
    rw [← hgdef, ← hDdef]
    field_simp
    ring
  have hθ' : akhcDW_thetaP θ A w = 1 - g := by rw [hgdef, akhcDW_g]; ring
  rw [hθ']
  set X := A / D * (v ^ J / (1 - v)) + B / D * (akhcDW_eps θ A B w / (1 - v)) +
    3 * akhcDW_zeta θ A w / D with hXdef
  have hX : X ≤ 3 * g / 4 := by rw [hXdef, hX3]; linarith only [hX1, hX2]
  have hrJ0 : 0 ≤ r ^ J := pow_nonneg hr0.le J
  nlinarith only [hX, hrJ, hrJ0, hg, hg1]

include hθ0 hθ1 hA hB hw0 hw1 in
theorem akhcDW_w_pow_Z2 :
    w ^ akhcDW_Z2 θ A B w ≤ 2 * akhcDW_zeta θ A w * (1 - w) / (A + B + 1) := by
  have hζ := akhcDW_zeta_pos hθ0 hθ1 hA hw1
  have h1w : 0 < 1 - w := by linarith only [hw1]
  exact akhcDW_pow_le_of_ceil_le hw0 hw1 (by positivity) le_rfl

include hθ0 hθ1 hA hw0 hw1 in
/-- **Enough squaring blocks**: `(1/2)^{2^K} ≤ r^M`. -/
theorem akhcDW_half_pow_K (Λ M : ℕ) :
    (1 / 2 : ℝ) ^ (2 ^ akhcDW_K θ A w Λ M) ≤ akhcDW_r θ A w Λ ^ M := by
  have hk := akhcDW_kappa_pos hθ0 hθ1 hA hw0 hw1 Λ
  set κ := akhcDW_kappa θ A w Λ with hκ
  have hn : 2 * κ * (M : ℝ) ≤ ((2 ^ akhcDW_K θ A w Λ M : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil (2 * κ * (M : ℝ))
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌈2 * κ * (M : ℝ)⌉₊
    have h3 : ((⌈2 * κ * (M : ℝ)⌉₊ : ℕ) : ℝ) ≤ ((2 ^ akhcDW_K θ A w Λ M : ℕ) : ℝ) := by
      exact_mod_cast h2.le
    linarith only [h1, h3]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl34 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  rw [akhcDW_r_pow, Real.rpow_def_of_pos (by norm_num)]
  set n := 2 ^ akhcDW_K θ A w Λ M with hndef
  calc (1 / 2 : ℝ) ^ n = Real.exp (Real.log ((1 / 2 : ℝ) ^ n)) :=
        (Real.exp_log (by positivity)).symm
    _ = Real.exp (-((n : ℝ) * Real.log 2)) := by
        rw [Real.log_pow, one_div, Real.log_inv]
        ring_nf
    _ ≤ Real.exp (Real.log 3 * -(κ * (M : ℝ))) := by
        apply Real.exp_le_exp.2
        have hM0 : (0 : ℝ) ≤ κ * (M : ℝ) := by positivity
        nlinarith only [hn, hl34, hM0, hl2]

end Constants

end

end SuperdiffusionCLT.AKHC61.Step3
