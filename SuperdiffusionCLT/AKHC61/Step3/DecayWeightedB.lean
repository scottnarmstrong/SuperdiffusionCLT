/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.DecayWeighted

/-!
# The abstract weighted decay lemma, part 2: the decay theorem

Continues `Step3/DecayWeighted.lean`. `akhcDW_decay` is the abstract decay lemma for the
weighted Step 3 recursion: from `F ≤ σ` (small) at the base, it reaches
`F_n ≤ S/ζ + ε r^M · r^{n-N₀}`, `r = 3^{-κ}` with the explicit `κ = akhcDW_kappa θ A w Λ`, for
`n ≥ N₀ = akhcDW_N0 …`.

The lag `q` (in the application `q(n) = n - ⌈L₁ log(L₂ n)⌉`) is handled in two phases.

* **Squaring blocks.** While the bound `u` is not yet small against `r^ℓ`, a block of length
  `Z + M` takes `u` to `max(u²/ε, floor)`: every lag square is then at most `u² ≤ ε u'`
  (`akhcDW_lag_pre`). `K = ⌊log₂⌈2κM⌉⌋ + 1` blocks bring `u` from `σ ≤ ε/2` down to
  `max(ε r^M, S/ζ)`.
* **Decay phase.** With `τ = ε r^M`, the lag square at `i` is `ε`-small against the profile at `i`
  either because the lag is paid back (`i - N₀ ≤ 2(q_i - N₀)`, from `N₀ + M` on) or because
  `i - N₀ ≤ M` and `τ ≤ ε r^M` (`akhcDW_lag_main`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

noncomputable section

/-! ## The comparison with the profile -/

/-- **`F` stays below the profile.** `akhcDW_compare` applied to `akhcDW_prof`, whose
supersolution property is `akhcDW_prof_super`: if `F ≤ σ̃` from `Kσ` on and `F ≤ max Φ τ` on
`[P, N)`, then `F_i ≤ max Φ (τ r^{i-N})` from `P` on. -/
theorem akhcDW_profile_bound {F : ℕ → ℝ} (hF0 : ∀ i, 0 ≤ F i) (hFanti : Antitone F)
    {θ c A B w σ σt Φ τ r v ε ζ : ℝ} {Λ J Kσ K0 Nrec P N ℓ : ℕ} {q : ℕ → ℕ} {s : ℕ → ℝ}
    (hθ0 : 0 ≤ θ) (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hcσ : c * σ ≤ (1 - θ) / 4) (hFσ : ∀ i, Kσ ≤ i → F i ≤ σ)
    (hKK : Kσ ≤ K0) (hΛJ : Λ ≤ J) (hJ1 : 1 ≤ J)
    (hq : ∀ i, K0 < i → Kσ ≤ q i ∧ q i < i)
    (hNrec : Nrec ≤ N)
    (hrec : ∀ n, Nrec ≤ n → F n ≤ θ * F (n - Λ) + c * F n ^ 2 +
      A * ∑ j ∈ Finset.range (n - K0), w ^ j * (F (n - j) - F n) +
      B * ∑ j ∈ Finset.range (n - K0), w ^ j * F (q (n - j)) ^ 2 + s n)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hv0 : 0 ≤ v) (hv1 : v < 1) (hwv : w ≤ v * r)
    (hΦ0 : 0 ≤ Φ) (hτ0 : 0 ≤ τ) (hΦσ : Φ ≤ σt) (hτσ : τ ≤ σt) (hε0 : 0 ≤ ε) (hζ0 : 0 ≤ ζ)
    (hFσt : ∀ i, Kσ ≤ i → F i ≤ σt)
    (hKP : K0 ≤ P) (hPJ : P + J ≤ N) (hPl : P + ℓ ≤ N)
    (hqP : ∀ i, P + ℓ < i → P ≤ q i)
    (hlag : ∀ i, P + ℓ < i →
      max Φ (τ * r ^ (q i - N)) ^ 2 ≤ ε * max Φ (τ * r ^ (i - N)))
    (hs : ∀ n, N ≤ n → s n ≤ ζ * (Φ + τ * r ^ (n - N)))
    (hfar : (A * σt + B * σt ^ 2) * w ^ (N - P - ℓ) ≤ ζ * (1 - w) * τ)
    (hbudget : akhcDW_thetaP θ A w + r ^ J * (A / akhcDW_D θ A w * (v ^ J / (1 - v)) +
      B / akhcDW_D θ A w * (ε / (1 - v)) + 3 * ζ / akhcDW_D θ A w) ≤ r ^ J)
    (hinitP : ∀ i, P ≤ i → i < N → F i ≤ max Φ τ) :
    ∀ i, P ≤ i → F i ≤ max Φ (τ * r ^ (i - N)) := by
  have hcmp := akhcDW_compare (H := akhcDW_prof σt P Φ τ r N) hF0 hFanti hθ0 hc hA hB hw0 hw1
    hcσ hFσ hKK hΛJ hJ1 (show K0 + J ≤ N by omega) hq
    (fun n hn => hrec n (hNrec.trans hn))
    (by
      intro i hi hiN
      by_cases hiP : i < P
      · unfold akhcDW_prof
        rw [ite_eq_left hiP]
        exact hFσt i hi
      · rw [akhcDW_prof_of_ge (Nat.le_of_not_lt hiP), show i - N = 0 by omega, pow_zero,
          mul_one]
        exact hinitP i (Nat.le_of_not_lt hiP) hiN)
    (akhcDW_prof_super hθ0 hA hB hw0 hw1 hr0 hr1 hv0 hv1 hwv hΦ0 hτ0 hΦσ hτσ hε0 hζ0 hKP hPJ
      hPl hqP hlag hs hfar hbudget)
  intro i hi
  have h := hcmp i (by omega)
  rwa [akhcDW_prof_of_ge hi] at h

theorem akhcDW_max_sq_le {a b X : ℝ} (h1 : a ^ 2 ≤ X) (h2 : b ^ 2 ≤ X) : max a b ^ 2 ≤ X := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact h2
  · rw [max_eq_left h]; exact h1

/-- **The lag squares in a squaring block**: `max Φ (τ r^a)² ≤ ε max Φ (τ r^b)` once `Φ ≤ ε` and
`τ² ≤ εΦ`. -/
theorem akhcDW_lag_pre {Φ τ r ε : ℝ} (hΦ0 : 0 ≤ Φ) (hτ0 : 0 ≤ τ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hΦε : Φ ≤ ε) (hτ2 : τ ^ 2 ≤ ε * Φ) (a b : ℕ) :
    max Φ (τ * r ^ a) ^ 2 ≤ ε * max Φ (τ * r ^ b) := by
  have hε0 : 0 ≤ ε := hΦ0.trans hΦε
  have h1 : Φ ^ 2 ≤ ε * Φ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hΦε hΦ0
  have h2 : (τ * r ^ a) ^ 2 ≤ ε * Φ := by
    have h3 : τ * r ^ a ≤ τ := mul_le_of_le_one_right hτ0 (pow_le_one₀ hr0 hr1)
    exact (pow_le_pow_left₀ (mul_nonneg hτ0 (pow_nonneg hr0 a)) h3 2).trans hτ2
  exact (akhcDW_max_sq_le h1 h2).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hε0)

/-- **The lag squares in the decay phase**: with `τ ≤ ε r^M`, the square of the profile at the
lagged index `a` is `ε`-small against the profile at `b`, provided `b ≤ 2a` (the lag has been
paid back) or `b ≤ M` (the start of the phase). -/
theorem akhcDW_lag_main {Φ τ r ε : ℝ} {M : ℕ} (hΦ0 : 0 ≤ Φ) (hτ0 : 0 ≤ τ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hΦε : Φ ≤ ε) (hτε : τ ≤ ε) (hτM : τ ≤ ε * r ^ M) {a b : ℕ}
    (hab : b ≤ 2 * a ∨ b ≤ M) :
    max Φ (τ * r ^ a) ^ 2 ≤ ε * max Φ (τ * r ^ b) := by
  have hε0 : 0 ≤ ε := hΦ0.trans hΦε
  have h1 : Φ ^ 2 ≤ ε * max Φ (τ * r ^ b) := by
    have : Φ ^ 2 ≤ ε * Φ := by rw [sq]; exact mul_le_mul_of_nonneg_right hΦε hΦ0
    exact this.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hε0)
  have h2 : (τ * r ^ a) ^ 2 ≤ ε * (τ * r ^ b) := by
    rcases hab with hab | hab
    · have hp : r ^ (2 * a) ≤ r ^ b := pow_le_pow_of_le_one hr0 hr1 hab
      have hτ2 : τ * τ ≤ ε * τ := mul_le_mul_of_nonneg_right hτε hτ0
      calc (τ * r ^ a) ^ 2 = (τ * τ) * r ^ (2 * a) := by ring
        _ ≤ (ε * τ) * r ^ b := mul_le_mul hτ2 hp (pow_nonneg hr0 _) (mul_nonneg hε0 hτ0)
        _ = ε * (τ * r ^ b) := by ring
    · have hp : r ^ M ≤ r ^ b := pow_le_pow_of_le_one hr0 hr1 hab
      have hra : r ^ a ≤ 1 := pow_le_one₀ hr0 hr1
      calc (τ * r ^ a) ^ 2 ≤ τ * τ := by
            rw [sq]
            have h3 : τ * r ^ a ≤ τ := mul_le_of_le_one_right hτ0 hra
            exact mul_le_mul h3 h3 (mul_nonneg hτ0 (pow_nonneg hr0 a)) hτ0
        _ ≤ τ * (ε * r ^ M) := mul_le_mul_of_nonneg_left hτM hτ0
        _ ≤ τ * (ε * r ^ b) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hε0) hτ0
        _ = ε * (τ * r ^ b) := by ring
  exact akhcDW_max_sq_le h1 (h2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hε0))

/-! ## The decay theorem -/

/-- **The abstract weighted decay lemma** (Step 3's induction). Let `F ≥ 0` be antitone with
`F ≤ σ` from `Kσ` on, and suppose that from `Nrec` on

`F_n ≤ θ F_{n-Λ} + c F_n² + A Σ_{j<n-K₀} w^j (F_{n-j} - F_n) + B Σ_{j<n-K₀} w^j F(q(n-j))² + s_n`,

with `s_n ≤ S + T r^{n-K₀}`, `r := 3^{-κ}` (`κ = akhcDW_kappa θ A w Λ` explicit), the lag `q`
reading at most `ℓ` back up to `Ntot ≥ N₀`, monotone, and paid back (`2(q_i - N₀) ≥ i - N₀`)
from `N₀ + M` on. If `σ ≤ ε/2`, `cσ ≤ (1-θ)/4`, `r^M ≤ 1/2`, `S ≤ ζε/2`, `T ≤ ζε r^M` (with the
explicit `ε = akhcDW_eps`, `ζ = akhcDW_zeta`), then for every `n ≥ N₀ = akhcDW_N0 …`

`F_n ≤ S/ζ + ε r^M · r^{n-N₀}`.

The proof runs `K = akhcDW_K` squaring blocks (each one squares the bound over a lag) and then
one decay phase, all by comparison with the profile `akhcDW_prof`. -/
theorem akhcDW_decay {F : ℕ → ℝ} {q : ℕ → ℕ} {s : ℕ → ℝ} {θ c A B w σ S T : ℝ}
    {Λ Kσ K0 Nrec ℓ M Ntot : ℕ}
    (hF0 : ∀ i, 0 ≤ F i) (hFanti : Antitone F)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hc : 0 ≤ c) (hA : 0 ≤ A) (hB : 0 ≤ B) (hw0 : 0 < w)
    (hw1 : w < 1)
    (hσ0 : 0 ≤ σ) (hσε : σ ≤ akhcDW_eps θ A B w / 2) (hcσ : c * σ ≤ (1 - θ) / 4)
    (hKK : Kσ ≤ K0) (hFσ : ∀ i, Kσ ≤ i → F i ≤ σ)
    (hq : ∀ i, K0 < i → Kσ ≤ q i ∧ q i < i)
    (hqlag : ∀ i, K0 < i → i ≤ Ntot → i ≤ q i + ℓ)
    (hqmono : ∀ i i', K0 < i → i ≤ i' → q i ≤ q i')
    (hNtot : akhcDW_N0 θ A B w Λ K0 ℓ M ≤ Ntot)
    (hqM : ∀ i, akhcDW_N0 θ A B w Λ K0 ℓ M + M ≤ i →
      i - akhcDW_N0 θ A B w Λ K0 ℓ M ≤ 2 * (q i - akhcDW_N0 θ A B w Λ K0 ℓ M))
    (hM : akhcDW_r θ A w Λ ^ M ≤ 1 / 2)
    (hS0 : 0 ≤ S) (hS : S ≤ akhcDW_zeta θ A w * akhcDW_eps θ A B w / 2)
    (hT : T ≤ akhcDW_zeta θ A w * akhcDW_eps θ A B w * akhcDW_r θ A w Λ ^ M)
    (hNrec : Nrec ≤ K0 + akhcDW_Zb θ A B w Λ ℓ M)
    (hs : ∀ n, Nrec ≤ n → s n ≤ S + T * akhcDW_r θ A w Λ ^ (n - K0))
    (hrec : ∀ n, Nrec ≤ n → F n ≤ θ * F (n - Λ) + c * F n ^ 2 +
      A * ∑ j ∈ Finset.range (n - K0), w ^ j * (F (n - j) - F n) +
      B * ∑ j ∈ Finset.range (n - K0), w ^ j * F (q (n - j)) ^ 2 + s n) :
    ∀ n, akhcDW_N0 θ A B w Λ K0 ℓ M ≤ n →
      F n ≤ S / akhcDW_zeta θ A w + akhcDW_eps θ A B w * akhcDW_r θ A w Λ ^ M *
        akhcDW_r θ A w Λ ^ (n - akhcDW_N0 θ A B w Λ K0 ℓ M) := by
  -- the constants
  have hε0 := akhcDW_eps_pos hθ0 hθ1 hA hB hw0 hw1
  have hε14 := akhcDW_eps_le hθ0 hA hB hw0 hw1 (θ := θ)
  have hζ0 := akhcDW_zeta_pos hθ0 hθ1 hA hw1
  have hr0 := akhcDW_r_pos (θ := θ) (A := A) (w := w) Λ
  have hr1 := (akhcDW_r_lt_one hθ0 hθ1 hA hw0 hw1 Λ).le
  have hvsw := akhcDW_v_le_sw hw0 (θ := θ) (A := A) Λ
  have hsw1 := akhcDW_sw_lt_one hw0 hw1
  have hbud := akhcDW_budget hθ0 hθ1 hA hB hw0 hw1 Λ
  have hZ2 := akhcDW_w_pow_Z2 hθ0 hθ1 hA hB hw0 hw1
  have hKhalf := akhcDW_half_pow_K hθ0 hθ1 hA hw0 hw1 Λ M
  have hJ1 := akhcDW_one_le_J (θ := θ) (A := A) (w := w) Λ
  have hΛJ := akhcDW_Λ_le_J (θ := θ) (A := A) (w := w) Λ
  set ε := akhcDW_eps θ A B w with hεdef
  set ζ := akhcDW_zeta θ A w with hζdef
  set r := akhcDW_r θ A w Λ with hrdef
  set J := akhcDW_J θ A w Λ with hJdef
  set Zb := akhcDW_Zb θ A B w Λ ℓ M with hZbdef
  set K := akhcDW_K θ A w Λ M with hKdef
  set N0 := akhcDW_N0 θ A B w Λ K0 ℓ M with hN0def
  have hN0eq : N0 = K0 + K * (Zb + M) + Zb := rfl
  have hZbeq : Zb = ℓ + J + M + akhcDW_Z2 θ A B w := rfl
  set v := w / r with hvdef
  have hv0 : 0 ≤ v := div_nonneg hw0.le hr0.le
  have hv1 : v < 1 := lt_of_le_of_lt hvsw hsw1
  have hwv : w ≤ v * r := by rw [hvdef, div_mul_cancel₀ _ hr0.ne']
  have hrM0 : 0 ≤ r ^ M := pow_nonneg hr0.le M
  -- the floor and the levels
  set Φf := S / ζ with hΦfdef
  have hΦf0 : 0 ≤ Φf := div_nonneg hS0 hζ0.le
  have hSΦ : S = ζ * Φf := by rw [hΦfdef, mul_div_cancel₀ _ hζ0.ne']
  have hΦfε : Φf ≤ ε / 2 := by
    rw [hΦfdef, div_le_iff₀ hζ0]
    linarith only [hS]
  set φ := max (ε * r ^ M) Φf with hφdef
  have hφ0 : 0 ≤ φ := le_max_of_le_right hΦf0
  have hεrM : ε * r ^ M ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_left hM hε0.le
    linarith only [this]
  have hφε : φ ≤ ε / 2 := max_le hεrM hΦfε
  set σt := max σ φ with hσtdef
  have hσt0 : 0 ≤ σt := le_max_of_le_left hσ0
  have hσtε : σt ≤ ε / 2 := max_le hσε hφε
  set y := σt / ε with hydef
  have hy0 : 0 ≤ y := div_nonneg hσt0 hε0.le
  have hy2 : y ≤ 1 / 2 := by
    rw [hydef, div_le_iff₀ hε0]
    linarith only [hσtε]
  have hεy : ε * y = σt := by rw [hydef, mul_div_cancel₀ _ hε0.ne']
  -- far parts of the sums
  have hfar : (A * σt + B * σt ^ 2) * w ^ (Zb - ℓ) ≤ ζ * (1 - w) * (ε * r ^ M) := by
    have hσt1 : σt ≤ 1 := by linarith only [hσtε, hε14]
    have h1 : A * σt + B * σt ^ 2 ≤ (A + B + 1) * (ε / 2) := by
      have h2 : B * σt ^ 2 ≤ B * σt := by
        apply mul_le_mul_of_nonneg_left _ hB
        rw [sq]; exact mul_le_of_le_one_right hσt0 hσt1
      nlinarith only [h2, hσtε, hσt0, hA, hB, hε0]
    have h3 : w ^ (Zb - ℓ) ≤ r ^ M * w ^ akhcDW_Z2 θ A B w := by
      rw [show Zb - ℓ = J + (M + akhcDW_Z2 θ A B w) by omega, pow_add, pow_add]
      have hwJ : w ^ J ≤ 1 := pow_le_one₀ hw0.le hw1.le
      have hwM : w ^ M ≤ r ^ M := pow_le_pow_left₀ hw0.le (hwv.trans
        (mul_le_of_le_one_left hr0.le hv1.le)) M
      calc w ^ J * (w ^ M * w ^ akhcDW_Z2 θ A B w) ≤ 1 * (w ^ M * w ^ akhcDW_Z2 θ A B w) :=
            mul_le_mul_of_nonneg_right hwJ (by positivity)
        _ ≤ r ^ M * w ^ akhcDW_Z2 θ A B w := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right hwM (by positivity)
    have hABpos : 0 < A + B + 1 := by linarith only [hA, hB]
    have hw1' : 0 < 1 - w := by linarith only [hw1]
    calc (A * σt + B * σt ^ 2) * w ^ (Zb - ℓ)
        ≤ ((A + B + 1) * (ε / 2)) * (r ^ M * w ^ akhcDW_Z2 θ A B w) :=
          mul_le_mul h1 h3 (pow_nonneg hw0.le _) (by positivity)
      _ ≤ ((A + B + 1) * (ε / 2)) * (r ^ M * (2 * ζ * (1 - w) / (A + B + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ2 hrM0) (by positivity)
      _ = ζ * (1 - w) * (ε * r ^ M) := by field_simp
  -- the lag reads above every block start
  have hJZ : J ≤ Zb := by rw [hZbeq]; omega
  have hℓZ : ℓ ≤ Zb := by rw [hZbeq]; omega
  have hNtotK0 : K0 < Ntot := by
    rw [hN0eq] at hNtot
    omega
  have hqPgen : ∀ P, K0 ≤ P → P + ℓ ≤ Ntot → ∀ i, P + ℓ < i → P ≤ q i := by
    intro P hK0P hP i hi
    by_cases hiN : i ≤ Ntot
    · have := hqlag i (by omega) hiN
      omega
    · have h1 := hqmono Ntot i hNtotK0 (by omega)
      have h2 := hqlag Ntot hNtotK0 le_rfl
      omega
  -- the squaring blocks
  set u : ℕ → ℝ := fun k => max (ε * y ^ (2 ^ k)) φ with hudef
  have hu0 : ∀ k, 0 ≤ u k := fun k => le_max_of_le_right hφ0
  have huσt : ∀ k, u k ≤ σt := by
    intro k
    refine max_le ?_ (le_max_right _ _)
    rw [← hεy]
    apply mul_le_mul_of_nonneg_left _ hε0.le
    calc y ^ (2 ^ k) ≤ y ^ 1 := pow_le_pow_of_le_one hy0 (by linarith only [hy2])
          (Nat.one_le_two_pow)
      _ = y := pow_one y
  have huε : ∀ k, u k ≤ ε := fun k => (huσt k).trans (by linarith only [hσtε, hε0])
  have huM : ∀ k, ε * r ^ M ≤ u k := fun k => (le_max_left _ _).trans (le_max_right _ _)
  have husq : ∀ k, u k ^ 2 ≤ ε * u (k + 1) := by
    intro k
    apply akhcDW_max_sq_le
    · calc (ε * y ^ (2 ^ k)) ^ 2 = ε * (ε * y ^ (2 ^ (k + 1))) := by
            rw [pow_succ 2 k, pow_mul]; ring
        _ ≤ ε * u (k + 1) := mul_le_mul_of_nonneg_left (le_max_left _ _) hε0.le
    · calc φ ^ 2 ≤ ε * φ := by
            rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith only [hφε, hε0]) hφ0
        _ ≤ ε * u (k + 1) := mul_le_mul_of_nonneg_left (le_max_right _ _) hε0.le
  have hblocks : ∀ k, k ≤ K → ∀ i, K0 + k * (Zb + M) ≤ i → F i ≤ u k := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      have h1 := hFσ i (by omega)
      have h2 : σ ≤ u 0 := by
        rw [hudef]
        dsimp only
        rw [pow_zero, pow_one, hεy]
        exact (le_max_left _ _).trans (le_max_left _ _)
      linarith only [h1, h2]
    | succ k ih =>
      intro hk i hi
      have ihk := ih (by omega)
      have hPtot : K0 + k * (Zb + M) + ℓ ≤ Ntot := by
        have : K0 + k * (Zb + M) + Zb ≤ N0 := by
          rw [hN0eq]
          have := Nat.mul_le_mul_right (Zb + M) (show k ≤ K by omega)
          omega
        omega
      have hbd := akhcDW_profile_bound hF0 hFanti (σt := σt) (Φ := u (k + 1)) (τ := u k)
        (r := r) (v := v) (ε := ε) (ζ := ζ) (J := J) (P := K0 + k * (Zb + M))
        (N := K0 + k * (Zb + M) + Zb) (ℓ := ℓ)
        hθ0 hc hA hB hw0.le hw1 hcσ hFσ hKK hΛJ hJ1 hq
        (by omega) hrec hr0 hr1 hv0 hv1 hwv (hu0 _) (hu0 _) (huσt _) (huσt _) hε0.le
        hζ0.le (fun i hi => (hFσ i hi).trans (le_max_left _ _)) (by omega)
        (by omega) (by omega) (hqPgen _ (by omega) hPtot)
        (fun i _ => akhcDW_lag_pre (hu0 _) (hu0 _) hr0.le hr1 (huε _) (husq k) _ _)
        (by
          intro n hn
          have h1 := hs n (by omega)
          have h2 : T * r ^ (n - K0) ≤ ζ * (u k * r ^ (n - (K0 + k * (Zb + M) + Zb))) := by
            have h3 : r ^ (n - K0) ≤ r ^ (n - (K0 + k * (Zb + M) + Zb)) :=
              pow_le_pow_of_le_one hr0.le hr1 (by omega)
            calc T * r ^ (n - K0) ≤ (ζ * ε * r ^ M) * r ^ (n - (K0 + k * (Zb + M) + Zb)) :=
                  mul_le_mul hT h3 (pow_nonneg hr0.le _) (by positivity)
              _ = ζ * ((ε * r ^ M) * r ^ (n - (K0 + k * (Zb + M) + Zb))) := by ring
              _ ≤ ζ * (u k * r ^ (n - (K0 + k * (Zb + M) + Zb))) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (huM k)
                    (pow_nonneg hr0.le _)) hζ0.le
          have h4 : S ≤ ζ * u (k + 1) := by
            rw [hSΦ]
            exact mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_right _ _))
              hζ0.le
          linarith only [h1, h2, h4])
        (by
          rw [show K0 + k * (Zb + M) + Zb - (K0 + k * (Zb + M)) - ℓ = Zb - ℓ by omega]
          exact hfar.trans (mul_le_mul_of_nonneg_left (huM k) (by
            have : 0 < 1 - w := by linarith only [hw1]
            positivity)))
        hbud
        (fun i hi _ => (ihk i hi).trans (le_max_right _ _))
      have e : (k + 1) * (Zb + M) = k * (Zb + M) + (Zb + M) := by ring
      have hF := hbd i (by omega)
      refine hF.trans (max_le le_rfl ?_)
      have hexp : M ≤ i - (K0 + k * (Zb + M) + Zb) := by omega
      calc u k * r ^ (i - (K0 + k * (Zb + M) + Zb)) ≤ ε * r ^ M :=
            mul_le_mul (huε k) (pow_le_pow_of_le_one hr0.le hr1 hexp) (pow_nonneg hr0.le _)
              hε0.le
        _ ≤ u (k + 1) := huM (k + 1)
  -- after the blocks the level is the floor
  have huK : u K ≤ φ := by
    refine max_le ?_ le_rfl
    have h1 : y ^ (2 ^ K) ≤ (1 / 2 : ℝ) ^ (2 ^ K) := pow_le_pow_left₀ hy0 hy2 _
    calc ε * y ^ (2 ^ K) ≤ ε * r ^ M :=
          mul_le_mul_of_nonneg_left (h1.trans hKhalf) hε0.le
      _ ≤ φ := le_max_left _ _
  -- the decay phase
  have hPtot : K0 + K * (Zb + M) + ℓ ≤ Ntot := by
    have : K0 + K * (Zb + M) + Zb ≤ N0 := by rw [hN0eq]
    omega
  have hmain := akhcDW_profile_bound hF0 hFanti (σt := σt) (Φ := Φf) (τ := ε * r ^ M)
    (r := r) (v := v) (ε := ε) (ζ := ζ) (J := J) (P := K0 + K * (Zb + M))
    (N := N0) (ℓ := ℓ)
    hθ0 hc hA hB hw0.le hw1 hcσ hFσ hKK hΛJ hJ1 hq
    (by rw [hN0eq]; omega) hrec hr0 hr1 hv0 hv1 hwv hΦf0 (mul_nonneg hε0.le hrM0)
    ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _))
    hε0.le hζ0.le (fun i hi => (hFσ i hi).trans (le_max_left _ _)) (by omega)
    (by rw [hN0eq]; omega) (by rw [hN0eq]; omega) (hqPgen _ (by omega) hPtot)
    (by
      intro i _
      apply akhcDW_lag_main hΦf0 (mul_nonneg hε0.le hrM0) hr0.le hr1
        (by linarith only [hΦfε, hε0]) (mul_le_of_le_one_right hε0.le (pow_le_one₀ hr0.le hr1))
        le_rfl
      by_cases hiM : N0 + M ≤ i
      · exact Or.inl (hqM i hiM)
      · exact Or.inr (by omega))
    (by
      intro n hn
      have h1 := hs n (by omega)
      have h3 : r ^ (n - K0) ≤ r ^ (n - N0) := pow_le_pow_of_le_one hr0.le hr1 (by omega)
      have h2 : T * r ^ (n - K0) ≤ ζ * (ε * r ^ M * r ^ (n - N0)) := by
        calc T * r ^ (n - K0) ≤ (ζ * ε * r ^ M) * r ^ (n - N0) :=
              mul_le_mul hT h3 (pow_nonneg hr0.le _) (by positivity)
          _ = ζ * (ε * r ^ M * r ^ (n - N0)) := by ring
      rw [hSΦ] at h1
      linarith only [h1, h2])
    (by
      rw [show N0 - (K0 + K * (Zb + M)) - ℓ = Zb - ℓ by rw [hN0eq]; omega]
      exact hfar)
    hbud
    (by
      intro i hi _
      have h1 := (hblocks K le_rfl i hi).trans huK
      rwa [hφdef, max_comm] at h1)
  intro n hn
  have h := hmain n (by rw [hN0eq] at hn; omega)
  refine h.trans (max_le ?_ ?_)
  · have : 0 ≤ ε * r ^ M * r ^ (n - N0) := by positivity
    linarith only [this]
  · linarith only [hΦf0]

/-! ## Satisfiability -/

end

end SuperdiffusionCLT.AKHC61.Step3
