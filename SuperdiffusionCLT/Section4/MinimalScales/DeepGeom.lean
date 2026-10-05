/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometric

/-!
# Deep-scale tail sums

Pure real-analysis groundwork for `srootE_mathcalE_bounds_of_inputs`'s `hDeep`
hypothesis (`SuperdiffusionCLT/Section4/MinimalScales/SkeletonMathcalE.lean`),
the deep-scale half of `p.new.mixing.attempt` (`e.new.mixing.attempt.deep`). No probability,
no ellipticity: given a
per-term bound of a nonnegative sequence by a `geometricWeight`-weighted constant,
starting from any shift `N`, the tail is summable and its sum is exactly bounded
by that constant times the *exact* geometric factor `3^{-sq N}` (no `s`-dependent
prefactor survives, since `geometricDiscount` cancels against the tail of the
geometric series — this is what lets a single `A`, chosen before `s`, absorb the
whole deep-scale tail in `hDeep`). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

/-- The shifted `geometricWeight` series is itself a `geometricWeight` series,
rescaled by the exact geometric factor `3^{-sq N}`: `geometricWeight s q (l + N)
= 3^{-sq N} * geometricWeight s q l`. -/
theorem srootD_geometricWeight_shift_eq {s q : ℝ} (N l : ℕ) :
    Homogenization.geometricWeight s q (l + N) =
      (3 : ℝ) ^ (-(s * q * (N : ℝ))) * Homogenization.geometricWeight s q l := by
  have h := Homogenization.geometricWeight_shift (s := s) (q := q) N l
  have hback : (3 : ℝ) ^ (-(s * q * (N : ℝ))) * Homogenization.geometricWeight s q l =
      Homogenization.geometricWeight s q (l + N) := by
    rw [h, ← mul_assoc]
    show (3 : ℝ) ^ (-(s * q * (N : ℝ))) * (3 : ℝ) ^ (s * q * (N : ℝ)) *
        Homogenization.geometricWeight s q (l + N) = Homogenization.geometricWeight s q (l + N)
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  exact hback.symm

/-- The exact tail sum of `geometricWeight` from any shift `N`: no `s`-dependent
prefactor, only the geometric factor `3^{-sq N}` (`css_{2s} ∑_{r ≥ N} 3^{-2sr} =
3^{-2sN}` at `q = 2`, the identity behind `e.new.mixing.attempt.deep`'s constant
bookkeeping). -/
theorem srootD_tsum_geometricWeight_shift_eq {s q : ℝ} (hsq : 0 < s * q) (N : ℕ) :
    ∑' l : ℕ, Homogenization.geometricWeight s q (l + N) =
      (3 : ℝ) ^ (-(s * q * (N : ℝ))) := by
  calc ∑' l : ℕ, Homogenization.geometricWeight s q (l + N)
      = ∑' l : ℕ, (3 : ℝ) ^ (-(s * q * (N : ℝ))) * Homogenization.geometricWeight s q l :=
        tsum_congr (srootD_geometricWeight_shift_eq N)
    _ = (3 : ℝ) ^ (-(s * q * (N : ℝ))) * ∑' l : ℕ, Homogenization.geometricWeight s q l :=
        tsum_mul_left
    _ = (3 : ℝ) ^ (-(s * q * (N : ℝ))) * 1 := by
        rw [Homogenization.tsum_geometricWeight_eq_one hsq]
    _ = (3 : ℝ) ^ (-(s * q * (N : ℝ))) := mul_one _

/-- **The deep-scale tail bound.** If a nonnegative sequence `f` is dominated,
from shift `N` onward, by `geometricWeight s q (l + N) * R` for a single constant
`R ≥ 0`, then `f (· + N)` is summable and its sum is at most `R * 3^{-sq N}`:
the crude per-scale bound `R` (uniform in the scale index, as a deterministic
ellipticity envelope gives) survives only through this exact geometric factor,
with no further loss. -/
theorem srootD_tsum_le_of_le_geometricWeight {f : ℕ → ℝ} {s q R : ℝ}
    (hsq : 0 < s * q) (N : ℕ) (hf0 : ∀ l : ℕ, 0 ≤ f (l + N))
    (hle : ∀ l : ℕ, f (l + N) ≤ Homogenization.geometricWeight s q (l + N) * R) :
    Summable (fun l : ℕ => f (l + N)) ∧
      ∑' l : ℕ, f (l + N) ≤ R * (3 : ℝ) ^ (-(s * q * (N : ℝ))) := by
  have hsumWeight : Summable (fun l : ℕ => Homogenization.geometricWeight s q (l + N)) := by
    have hbase := Homogenization.summable_geometricWeight hsq
    have heq : (fun l : ℕ => Homogenization.geometricWeight s q (l + N)) =
        fun l : ℕ => (3 : ℝ) ^ (-(s * q * (N : ℝ))) * Homogenization.geometricWeight s q l :=
      funext (srootD_geometricWeight_shift_eq N)
    rw [heq]
    exact hbase.mul_left _
  have hsumG : Summable (fun l : ℕ => Homogenization.geometricWeight s q (l + N) * R) :=
    hsumWeight.mul_right R
  have hsum : Summable (fun l : ℕ => f (l + N)) :=
    Summable.of_nonneg_of_le hf0 hle hsumG
  refine ⟨hsum, ?_⟩
  calc ∑' l : ℕ, f (l + N)
      ≤ ∑' l : ℕ, Homogenization.geometricWeight s q (l + N) * R :=
        Summable.tsum_le_tsum hle hsum hsumG
    _ = (∑' l : ℕ, Homogenization.geometricWeight s q (l + N)) * R := tsum_mul_right
    _ = (3 : ℝ) ^ (-(s * q * (N : ℝ))) * R := by
        rw [srootD_tsum_geometricWeight_shift_eq hsq N]
    _ = R * (3 : ℝ) ^ (-(s * q * (N : ℝ))) := mul_comm _ _

end SuperdiffusionCLT.Section4.MinimalScales
