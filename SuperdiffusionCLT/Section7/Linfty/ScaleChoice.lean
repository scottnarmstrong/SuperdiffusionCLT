/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockF

/-!
# The scale separation of the `L^∞` proposition

The choice of the window constant `N` against the exponents (`e.Dir.new.Linfty.scale.choice`,
with the exponents as parameters), and two bridges between the
integer scale `n - ⌈C log n⌉` of the contract and the natural-number scale `nK C n`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open scoped Real

/-- **The scale separation** (`e.Dir.new.Linfty.scale.choice`), with the
exponents as parameters: `N` is chosen from `A₀, E, θ` only. -/
theorem linf_scale_choice (A₀ E θ : ℝ) (hA : 0 ≤ A₀) (hE : 0 ≤ E) (hθ : 0 < θ) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ K : ℕ, 3 ≤ K → ∀ nu s : ℝ, 0 < nu → (K : ℝ)⁻¹ ≤ nu → 0 < s →
      s ≤ (K : ℝ) →
      (K : ℝ) ^ A₀ * nu ^ (-A₀) * s ^ A₀ *
          ((3 : ℝ) ^ (-(⌈N * Real.log (K : ℝ)⌉₊ : ℝ))) ^ θ ≤ (K : ℝ) ^ (-E) := by
  have _hE := hE
  refine ⟨max 1 ((3 * A₀ + E) / θ), le_max_left _ _, ?_⟩
  intro K hK nu s hnu hKnu hs hsK
  set N : ℝ := max 1 ((3 * A₀ + E) / θ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := le_max_left _ _
  have hNθ : 3 * A₀ + E ≤ N * θ := by
    have h1 : (3 * A₀ + E) / θ ≤ N := le_max_right _ _
    rw [div_le_iff₀ hθ] at h1
    exact h1
  have hK3 : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith only [hK3]
  have hK1 : (1 : ℝ) ≤ K := by linarith only [hK3]
  have hlog3 : (1 : ℝ) < Real.log 3 := SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hlogK0 : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK1
  -- the three factors `≤ K ^ A₀`
  have h2 : nu ^ (-A₀) ≤ (K : ℝ) ^ A₀ := by
    rw [Real.rpow_neg hnu.le]
    rw [← Real.inv_rpow hnu.le]
    refine Real.rpow_le_rpow (inv_nonneg.2 hnu.le) ?_ hA
    have := inv_anti₀ (inv_pos.2 hKpos) hKnu
    rwa [inv_inv] at this
  have h3 : s ^ A₀ ≤ (K : ℝ) ^ A₀ := Real.rpow_le_rpow hs.le hsK hA
  -- the decay factor
  have hceil : N * Real.log (K : ℝ) ≤ (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h4 : ((3 : ℝ) ^ (-(⌈N * Real.log (K : ℝ)⌉₊ : ℝ))) ^ θ ≤ (K : ℝ) ^ (-(N * θ)) := by
    have e1 : (3 : ℝ) ^ (-(⌈N * Real.log (K : ℝ)⌉₊ : ℝ)) =
        Real.exp (-(⌈N * Real.log (K : ℝ)⌉₊ : ℝ) * Real.log 3) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    have e2 : (K : ℝ) ^ (-(N * θ)) = Real.exp (-(N * θ) * Real.log (K : ℝ)) := by
      rw [Real.rpow_def_of_pos hKpos]
      ring_nf
    rw [e1, e2, ← Real.exp_mul]
    refine Real.exp_le_exp.2 ?_
    have hNl : 0 ≤ N * Real.log (K : ℝ) := mul_nonneg (by linarith only [hN1]) hlogK0
    have hc0 : 0 ≤ (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) := Nat.cast_nonneg _
    have : N * Real.log (K : ℝ) * 1 ≤ (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) * Real.log 3 :=
      mul_le_mul hceil hlog3.le (by norm_num) hc0
    have h5 : N * Real.log (K : ℝ) * θ ≤ (⌈N * Real.log (K : ℝ)⌉₊ : ℝ) * Real.log 3 * θ :=
      mul_le_mul_of_nonneg_right (by linarith only [this]) hθ.le
    linarith only [h5]
  have hA0 : 0 ≤ (K : ℝ) ^ A₀ := Real.rpow_nonneg hKpos.le _
  have hnu0 : 0 ≤ nu ^ (-A₀) := Real.rpow_nonneg hnu.le _
  have hs0 : 0 ≤ s ^ A₀ := Real.rpow_nonneg hs.le _
  calc (K : ℝ) ^ A₀ * nu ^ (-A₀) * s ^ A₀ *
          ((3 : ℝ) ^ (-(⌈N * Real.log (K : ℝ)⌉₊ : ℝ))) ^ θ
      ≤ (K : ℝ) ^ A₀ * (K : ℝ) ^ A₀ * (K : ℝ) ^ A₀ * (K : ℝ) ^ (-(N * θ)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul le_rfl h2 hnu0 hA0) h3 hs0
          (mul_nonneg hA0 hA0)) h4 (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
          (mul_nonneg (mul_nonneg hA0 hA0) hA0)
    _ = (K : ℝ) ^ (A₀ + A₀ + A₀ + -(N * θ)) := by
        rw [Real.rpow_add hKpos, Real.rpow_add hKpos, Real.rpow_add hKpos]
    _ ≤ (K : ℝ) ^ (-E) :=
        Real.rpow_le_rpow_of_exponent_le hK1 (by linarith only [hNθ])

/-- **Bridge 1.** The integer scale `n - ⌈C log n⌉` of the contract, when nonnegative, is the cast of
the natural-number scale `nK C n`. -/
theorem linf_scale_zcast {C : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (h : 0 ≤ (n : ℤ) - ⌈C * Real.log (n : ℝ)⌉) :
    ((n : ℤ) - ⌈C * Real.log (n : ℝ)⌉ : ℤ) = (nK C n : ℤ) := by
  have hn : (0 : ℝ) ≤ C * Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · exact mul_nonneg hC (Real.log_nonneg (by exact_mod_cast h0))
  have hceil : ((⌈C * Real.log (n : ℝ)⌉₊ : ℕ) : ℤ) = ⌈C * Real.log (n : ℝ)⌉ :=
    Int.natCast_ceil_eq_ceil hn
  rw [← hceil] at h ⊢
  have hle : ⌈C * Real.log (n : ℝ)⌉₊ ≤ n := by omega
  unfold nK
  omega

/-- **Bridge 2.** If `C ≥ N + j + 1` then the scale `nK C K` lies `j` below `nK N K`. -/
theorem linf_scale_nK_le_sub {N C : ℝ} (hN : 0 ≤ N) (j : ℕ) (hCN : N + j + 1 ≤ C)
    {K : ℕ} (hK : 3 ≤ K) : nK C K ≤ nK N K - j := by
  have hK3 : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog3 : (1 : ℝ) < Real.log 3 := SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hlogK : (1 : ℝ) ≤ Real.log (K : ℝ) :=
    le_trans hlog3.le (Real.log_le_log (by norm_num) hK3)
  have h1 : N * Real.log (K : ℝ) + j ≤ C * Real.log (K : ℝ) := by
    have : (N + j + 1) * Real.log (K : ℝ) ≤ C * Real.log (K : ℝ) :=
      mul_le_mul_of_nonneg_right hCN (by linarith only [hlogK])
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith only [this, hlogK, hj]
  have hNl : 0 ≤ N * Real.log (K : ℝ) := mul_nonneg hN (by linarith only [hlogK])
  have h2 : ⌈N * Real.log (K : ℝ)⌉₊ + j ≤ ⌈C * Real.log (K : ℝ)⌉₊ := by
    rw [← Nat.ceil_add_natCast hNl]
    exact Nat.ceil_mono h1
  unfold nK
  omega

/-- Witness: the scale choice for the exponents `A₀ = E = 0`, `θ = 1` exists, and both bridges
apply to concrete data. -/
example : ∃ N : ℝ, 1 ≤ N := (linf_scale_choice 0 0 1 le_rfl le_rfl one_pos).imp fun _ h => h.1

example : (((0 : ℕ) : ℤ) - ⌈(1 : ℝ) * Real.log ((0 : ℕ) : ℝ)⌉ : ℤ) = (nK 1 0 : ℤ) :=
  linf_scale_zcast zero_le_one 0 (by simp)

example : nK 1 3 ≤ nK 0 3 - 0 :=
  linf_scale_nK_le_sub le_rfl 0 (by norm_num) le_rfl

end SuperdiffusionCLT.Section7
