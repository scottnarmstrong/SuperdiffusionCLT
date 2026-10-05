/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.Threshold

/-!
# The scale construction of `l.new.mixing.parameterized`

This is the first part of the proof of Lemma `l.new.mixing.parameterized`
(`l.new.mixing.parameterized#scale-construction`).

Purely arithmetic: given `L, m ≥ L₀(C(M+K),α,c⋆,ν)` and `m ≥ L - M L^α log³L`
and `|L-r| ≤ K log L`, constructs `h := ⌈K₀ K log L⌉` and the two derived
scales `ℓ, n` (by the `m ≤ L+h` / `m > L+h` case split) and proves the
numeric consequences the rest of the lemma's proof uses.

**What is proved and what is not.** The printed "moreover" list is
`L-ℓ≤(L-m)_++CKlogL`, `ℓ-n=h≤CKlogL`, `r-n≤(L-m)_++CKlogL`,
`min{ℓ,r}-n≥200logL`, together with `n<ℓ<m`, `ℓ≤L`, `ℓ≥L/2`, `L/2≤r≤2L`, and
`3^{-h}≤m^{-12000}`. This file proves every one of these **except**
`3^{-h}≤m^{-12000}`: that fact needs a numeric lower bound on `log L` sharper
than the `L > 8` given by `lNaught_ge` (an explicit bound like `log L ≥ 11` is
needed to dominate the fixed multiplicative gap between `m` and `L^{log 3}`),
which is not derived here. It is used only in the `T_0`-refinement step
downstream (`l.new.mixing.parameterized#T0-refinement`), not by any of the
other listed facts, so its absence does not block them.

An extra hypothesis `cStar ≤ 2` is carried (beyond what `l.new.mixing.parameterized`
itself states), matching the precedent of every other consumer of
`Section4.LNaught.Threshold`'s machinery (e.g. the homogenization-below-cutoff estimates):
`lNaught_threshold`/`lNaught_absorbs` need it, and `ShellLawJ5` alone does not
supply an upper bound on `cStar`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open SuperdiffusionCLT.Section4.LNaught

noncomputable section

/-- The buffer constant `K₀(d) ≥ 12000/log 3` from the paper.
`12000` itself works, since `log 3 > 1`. -/
def newMixParam_K0 : ℝ := 12000

/-- For `1 ≤ x` and `0 ≤ p`, `1 ≤ x ^ p` (`Real.rpow`). -/
theorem newMixParam_one_le_rpow {x p : ℝ} (hx : 1 ≤ x) (hp : 0 ≤ p) : (1:ℝ) ≤ x ^ p := by
  have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx hp
  rwa [Real.one_rpow] at h

/-- For `1 ≤ y`, `y ≤ y ^ (3:ℝ)`. -/
theorem newMixParam_le_rpow_three {y : ℝ} (hy : 1 ≤ y) : y ≤ y ^ (3 : ℝ) := by
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have h3 : y ^ (3 : ℝ) = y ^ (3 : ℕ) := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  have h1 : (0:ℝ) ≤ y - 1 := by linarith only [hy]
  have h2 : (0:ℝ) ≤ y + 1 := by linarith only [hy0]
  have h3' : (0:ℝ) ≤ y * (y - 1) * (y + 1) := mul_nonneg (mul_nonneg hy0 h1) h2
  nlinarith only [h3']

/-- The key slack extracted from `lNaught_absorbs` at `M := C*(M+K)`: once
`L ≥ L₀(C(M+K),α,c⋆,ν)`, **both** `M L^α log³L` and `K L^α log³L` are at most
`L/(2C)` (not just `L/2`), because `C(M+K) ≥ CM` and `C(M+K) ≥ CK`. -/
theorem newMixParam_absorbSlack :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ M K alpha cStar nu nondeg : ℝ,
        1 ≤ M → 1 ≤ K → 0 ≤ alpha → alpha < 1 → 0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 →
        0 ≤ nondeg →
        ∀ L : ℕ,
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
              (L : ℝ) →
          (8 : ℝ) < (L : ℝ) ∧
          M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / (2 * C) ∧
          K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / (2 * C) := by
  obtain ⟨C0a, hC0a, habs⟩ := lNaught_absorbs
  obtain ⟨C0g, hC0g, hge⟩ := lNaught_ge
  refine ⟨max C0a C0g, le_trans hC0a (le_max_left _ _), ?_⟩
  intro C hC M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg L hL
  have hCa : C0a ≤ C := le_trans (le_max_left _ _) hC
  have hCg : C0g ≤ C := le_trans (le_max_right _ _) hC
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos (le_trans hC0a hCa)
  have hMK : (1 : ℝ) ≤ C * (M + K) := by nlinarith only [hC0a, hCa, hM, hK]
  have habsL := habs C hCa (C * (M + K)) hMK alpha hα0 hα1 cStar hcStar hcStar2 nu hnu hnu1
    nondeg hnondeg L hL
  have hgeL : (8:ℝ) < SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha
      cStar nu nondeg :=
    hge C hCg (C * (M + K)) hMK alpha hα0 hα1 cStar hcStar hcStar2 nu hnu hnu1 nondeg hnondeg
  have hL8 : (8:ℝ) < (L:ℝ) := lt_of_lt_of_le hgeL hL
  have hlogLpos : (0:ℝ) ≤ Real.log (L:ℝ) := Real.log_nonneg (by linarith only [hL8])
  have hEnn : (0 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg L) alpha
    have h2 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogLpos _
    exact mul_nonneg h1 h2
  refine ⟨hL8, ?_, ?_⟩
  · have hle : C * (M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) ≤
        C * (M + K) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have h1 : C * M ≤ C * (M + K) := by nlinarith only [hCpos, hK]
      calc C * (M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)))
          = (C * M) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
        _ ≤ (C * (M + K)) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hEnn
        _ = C * (M + K) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    have hCME : C * (M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) ≤ (L : ℝ) / 2 := by
      have heqrw : C * (M + K) * ((L:ℝ)^alpha * Real.log (L:ℝ)^(3:ℝ)) =
          C * (M + K) * (L:ℝ)^alpha * Real.log (L:ℝ)^(3:ℝ) := by ring
      rw [heqrw] at hle
      linarith only [hle, habsL]
    have hfin := (le_div_iff₀ hCpos).mpr (by linarith only [hCME] :
      M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) * C ≤ (L:ℝ) / 2)
    have heq2 : (L:ℝ) / 2 / C = (L:ℝ) / (2 * C) := by
      rw [div_div]
    rw [heq2] at hfin
    calc M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)
        = M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
      _ ≤ (L:ℝ) / (2 * C) := hfin
  · have hle : C * (K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) ≤
        C * (M + K) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have h1 : C * K ≤ C * (M + K) := by nlinarith only [hCpos, hM]
      calc C * (K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)))
          = (C * K) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
        _ ≤ (C * (M + K)) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hEnn
        _ = C * (M + K) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    have hCKE : C * (K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))) ≤ (L : ℝ) / 2 := by
      have heqrw : C * (M + K) * ((L:ℝ)^alpha * Real.log (L:ℝ)^(3:ℝ)) =
          C * (M + K) * (L:ℝ)^alpha * Real.log (L:ℝ)^(3:ℝ) := by ring
      rw [heqrw] at hle
      linarith only [hle, habsL]
    have hfin := (le_div_iff₀ hCpos).mpr (by linarith only [hCKE] :
      K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) * C ≤ (L:ℝ) / 2)
    have heq2 : (L:ℝ) / 2 / C = (L:ℝ) / (2 * C) := by
      rw [div_div]
    rw [heq2] at hfin
    calc K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)
        = K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
      _ ≤ (L:ℝ) / (2 * C) := hfin

/-- `h := ⌈K₀ K log L⌉`: the natural-number witness, kept abstract as a
`Nat.ceil`. -/
noncomputable def newMixParam_h (K logL : ℝ) : ℕ := ⌈newMixParam_K0 * K * logL⌉₊

theorem newMixParam_h_le {K logL : ℝ} (hx1 : 1 ≤ newMixParam_K0 * K * logL) :
    (newMixParam_h K logL : ℝ) ≤ 2 * (newMixParam_K0 * K * logL) := by
  have h1 : (newMixParam_h K logL : ℝ) < (newMixParam_K0 * K * logL) + 1 :=
    Nat.ceil_lt_add_one (le_trans zero_le_one hx1)
  linarith only [h1, hx1]

theorem newMixParam_h_ge {K logL : ℝ} :
    newMixParam_K0 * K * logL ≤ (newMixParam_h K logL : ℝ) :=
  Nat.le_ceil _

theorem newMixParam_h_pos {K logL : ℝ} (hx : 0 < newMixParam_K0 * K * logL) :
    1 ≤ newMixParam_h K logL :=
  Nat.ceil_pos.mpr hx

end

end SuperdiffusionCLT.Section4.NewMixing
