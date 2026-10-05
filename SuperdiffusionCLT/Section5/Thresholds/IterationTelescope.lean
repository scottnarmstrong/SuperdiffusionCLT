/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Star.Real


/-!
# Telescoping along a step-size iteration

Pure lemma behind Steps 2-4 and 6 of the proof of `t.sstar.sharp.bounds`: iterate
`a₀ = N₀`, `a_{k+1} = a_k + step a_k`; if each increment of `f` over a step is at most `E`, steps
are at most `n` and at least `θ √n`, then `|f N - f N₀| ≤ (3 θ⁻¹ √N + 1) E`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

/-- The iteration `a₀ = N₀`, `a_{k+1} = a_k + step a_k`. -/
def stepIter (step : ℕ → ℕ) (N0 : ℕ) : ℕ → ℕ
  | 0 => N0
  | k + 1 => stepIter step N0 k + step (stepIter step N0 k)

theorem stepIter_succ (step : ℕ → ℕ) (N0 k : ℕ) :
    stepIter step N0 (k + 1) = stepIter step N0 k + step (stepIter step N0 k) := rfl

theorem stepIter_mono (step : ℕ → ℕ) (N0 : ℕ) : Monotone (stepIter step N0) :=
  monotone_nat_of_le_succ fun k => by rw [stepIter_succ]; omega

theorem le_stepIter (step : ℕ → ℕ) (N0 k : ℕ) : N0 ≤ stepIter step N0 k :=
  stepIter_mono step N0 (Nat.zero_le k)

/-- A real-sequence increment bound telescopes along the iteration. -/
theorem telescope_along_steps (f : ℕ → ℝ) (step : ℕ → ℕ) (N0 N : ℕ) (θ E : ℝ)
    (hθ : 0 < θ) (hE : 0 ≤ E) (hN : N0 ≤ N)
    (hpos : ∀ n, N0 ≤ n → n ≤ N → 1 ≤ step n)
    (hle : ∀ n, N0 ≤ n → n ≤ N → step n ≤ n)
    (hlb : ∀ n, N0 ≤ n → n ≤ N → θ * Real.sqrt n ≤ step n)
    (hf : ∀ n, N0 ≤ n → n ≤ N → ∀ h, h ≤ step n → |f (n + h) - f n| ≤ E) :
    |f N - f N0| ≤ (3 * θ⁻¹ * Real.sqrt N + 1) * E := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ, a = stepIter step N0 := ⟨_, rfl⟩
  have ha0 : a 0 = N0 := by rw [ha]; rfl
  have hasucc : ∀ k, a (k + 1) = a k + step (a k) := by intro k; rw [ha]; rfl
  have hamono : Monotone a := by rw [ha]; exact stepIter_mono step N0
  have hale : ∀ k, N0 ≤ a k := by intro k; rw [ha]; exact le_stepIter step N0 k
  -- the last index with `a K ≤ N`
  have hex : ∃ k, N < a k := by
    by_contra hcon
    push Not at hcon
    have key : ∀ k, k + N0 ≤ a k := by
      intro k
      induction k with
      | zero => rw [ha0]; omega
      | succ k ih =>
        have h1 := hpos (a k) (hale k) (hcon k)
        rw [hasucc]; omega
    have := key (N + 1)
    have := hcon (N + 1)
    omega
  classical
  set k0 := Nat.find hex with hk0
  have hk0spec : N < a k0 := Nat.find_spec hex
  have hk0ne : k0 ≠ 0 := by
    intro h0
    have : N < a 0 := by rw [← h0]; exact hk0spec
    omega
  obtain ⟨K, hK⟩ : ∃ K, k0 = K + 1 := ⟨k0 - 1, by omega⟩
  have hKN : a K ≤ N := by
    have := Nat.find_min hex (show K < k0 by omega)
    push Not at this; exact this
  have hKN' : N < a (K + 1) := by rw [← hK]; exact hk0spec
  have hmono : ∀ j, j ≤ K → a j ≤ N := fun j hj =>
    le_trans (hamono hj) hKN
  -- accumulated increments
  have hacc : ∀ j, j ≤ K → |f (a j) - f N0| ≤ j * E := by
    intro j
    induction j with
    | zero => intro _; simp [ha0]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hf (a j) (hale j) (hmono j (by omega)) (step (a j)) le_rfl
      have h3 : a (j + 1) = a j + step (a j) := hasucc j
      rw [← h3] at h2
      push_cast
      have := abs_sub_le (f (a (j + 1))) (f (a j)) (f N0)
      linarith only [this, h1, h2]
  -- growth of the square root
  have hgrow : ∀ j, j ≤ K → (j : ℝ) * (θ / 3) ≤ Real.sqrt (a j) - Real.sqrt N0 := by
    intro j
    induction j with
    | zero => intro _; simp [ha0]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hjN := hmono j (by omega)
      have hj1N := hmono (j + 1) hj
      have hN0j := hale j
      have h3 : a (j + 1) = a j + step (a j) := hasucc j
      have hs1 := hpos (a j) hN0j hjN
      have hs2 := hle (a j) hN0j hjN
      have hs3 := hlb (a j) hN0j hjN
      have haj : 0 < a j := by omega
      have haj' : (0 : ℝ) < a j := by exact_mod_cast haj
      have hb : (a (j + 1) : ℝ) = a j + step (a j) := by rw [h3]; push_cast; ring
      have hb2 : (a (j + 1) : ℝ) ≤ 2 * a j := by
        rw [hb]; have : (step (a j) : ℝ) ≤ a j := by exact_mod_cast hs2
        linarith only [this]
      set x := Real.sqrt (a j) with hx
      set y := Real.sqrt (a (j + 1)) with hy
      have hx0 : 0 < x := Real.sqrt_pos.2 haj'
      have hxx : x * x = a j := Real.mul_self_sqrt haj'.le
      have hyy : y * y = a (j + 1) := Real.mul_self_sqrt (by positivity)
      have hy0 : 0 ≤ y := Real.sqrt_nonneg _
      have hy2 : y ≤ 2 * x := by
        by_contra hcon
        push Not at hcon
        nlinarith only [hcon, hx0, hyy, hxx, hb2]
      have hxy : x ≤ y := Real.sqrt_le_sqrt (by rw [hb]; linarith only [show (0 : ℝ) ≤ step (a j) by positivity])
      have hdiff : θ * x ≤ y * y - x * x := by
        rw [hyy, hxx, hb]; linarith only [hs3]
      have : θ / 3 ≤ y - x := by
        by_contra hcon
        push Not at hcon
        have h4 : (y - x) * (y + x) < θ / 3 * (3 * x) := by
          apply mul_lt_mul hcon (by linarith only [hy2]) (by positivity) (by linarith only [hcon, hθ, hxy])
        nlinarith only [h4, hdiff]
      push_cast
      linarith only [h1, this]
  have hK1 : (K : ℝ) * (θ / 3) ≤ Real.sqrt N := by
    have := hgrow K le_rfl
    have h2 : Real.sqrt (a K) ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hKN)
    have := Real.sqrt_nonneg (N0 : ℝ)
    linarith only [this, h2, ‹(K : ℝ) * (θ / 3) ≤ _›]
  have hKb : (K : ℝ) ≤ 3 * θ⁻¹ * Real.sqrt N := by
    have : (K : ℝ) ≤ 3 / θ * Real.sqrt N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hθ]; linarith only [hK1]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- the final partial step
  have hfin := hf (a K) (hale K) hKN (N - a K) (by
    have h3 : a (K + 1) = a K + step (a K) := hasucc K
    omega)
  have hNe : a K + (N - a K) = N := by omega
  rw [hNe] at hfin
  have hK2 := hacc K le_rfl
  have := abs_sub_le (f N) (f (a K)) (f N0)
  have hKE : (K : ℝ) * E ≤ 3 * θ⁻¹ * Real.sqrt N * E := mul_le_mul_of_nonneg_right hKb hE
  nlinarith only [this, hfin, hK2, hKE]

end SuperdiffusionCLT.Section5
