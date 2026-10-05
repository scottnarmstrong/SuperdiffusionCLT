/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssemblyB

/-!
# The auxiliary scale and the quadratic-form domination in the far regime

* `mixBaseC_ell_facts`: in the regime `6500 log(ν⁻¹L) < L - n` with the margin window
  `11000 log(ν⁻¹L) ≤ m - n ≤ 22000 (1 + log(ν⁻¹L))` and `log(ν⁻¹L) ≥ 20`, the choice
  `ell = n + ⌈5010 log(ν⁻¹L)⌉` satisfies `n ≤ ell < L`, `ell ≤ m`, both gaps of at least
  `5010 log(ν⁻¹L)`, and the case guard `m ≤ L + 16700 log(ν⁻¹L)`.
* `mixBaseC_dom`: a rate-`t` annealed comparison with `t ≤ 1/2` gives `Q_ell ≤ 2 Q_L` and
  `Q_L ≥ 0` for the annealed quadratic forms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-- **The auxiliary scale `ell`** in the far regime: `ell - n = ⌈5010 Lg⌉`, with both gaps and the
case guard of the localization bound. -/
theorem mixBaseC_ell_facts {Lg : ℝ} (hLg : 20 ≤ Lg) (n L mb : ℕ) (hn1 : 1 ≤ n) (hnm : n ≤ mb)
    (hfar : 6500 * Lg < (L : ℝ) - (n : ℝ)) (hm1 : 11000 * Lg ≤ ((mb - n : ℕ) : ℝ))
    (hm2 : ((mb - n : ℕ) : ℝ) ≤ 22000 * (1 + Lg)) :
    ∃ ell : ℕ, n ≤ ell ∧ ell < L ∧ ell ≤ mb ∧ 1 ≤ ell ∧ 5010 * Lg ≤ ((ell - n : ℕ) : ℝ) ∧
      5010 * Lg ≤ ((mb - ell : ℕ) : ℝ) ∧ (mb : ℝ) ≤ (L : ℝ) + 16700 * Lg := by
  have hLg0 : 0 ≤ Lg := by linarith only [hLg]
  set k : ℕ := ⌈5010 * Lg⌉₊ with hk
  have hk1 : 5010 * Lg ≤ (k : ℝ) := Nat.le_ceil _
  have hk2 : (k : ℝ) < 5010 * Lg + 1 := Nat.ceil_lt_add_one (by linarith only [hLg0])
  have hmbn : ((mb - n : ℕ) : ℝ) = (mb : ℝ) - (n : ℝ) := Nat.cast_sub hnm
  have hkle : k ≤ mb - n := by
    have : (k : ℝ) ≤ ((mb - n : ℕ) : ℝ) := by linarith only [hk2, hm1, hLg]
    exact_mod_cast this
  have hell_sub : (n + k) - n = k := by omega
  have hmb_sub : mb - (n + k) = (mb - n) - k := by omega
  have hmbk : (((mb - n) - k : ℕ) : ℝ) = ((mb - n : ℕ) : ℝ) - (k : ℝ) := Nat.cast_sub hkle
  refine ⟨n + k, Nat.le_add_right _ _, ?_, ?_, by omega, ?_, ?_, ?_⟩
  · have h : ((n + k : ℕ) : ℝ) < (L : ℝ) := by
      push_cast
      linarith only [hk2, hfar, hLg]
    exact_mod_cast h
  · omega
  · rw [hell_sub]; exact hk1
  · rw [hmb_sub, hmbk]
    linarith only [hk2, hm1, hLg]
  · linarith only [hmbn, hm2, hfar, hLg]

/-- **The `ell`-form is dominated by twice the `L`-form**, from a rate-`t` annealed comparison with
`t ≤ 1/2`; both forms are nonnegative. -/
theorem mixBaseC_dom [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (ell L n : ℕ) {t : ℝ} (ht : t ≤ 1 / 2)
    (hcomp : ∀ p q : BlockVec d,
      2 * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) -
            blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)) ≤
        t * (blockVecDot p (blockMatVecMul
                (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q (blockMatVecMul
                (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q))) :
    ∀ p : BlockVec d,
      0 ≤ blockVecDot p (blockMatVecMul
            (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) ∧
        blockVecDot p (blockMatVecMul
            (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) ≤
          2 * blockVecDot p (blockMatVecMul
            (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) := by
  intro p
  have ht1 : t < 1 := by linarith only [ht]
  obtain ⟨-, hs, -, hu⟩ := mixBase_invertB_of_annealedComparison hnu hJ4 ell L (n : ℤ) ht1 hcomp
  have hsL := sigmaBarScalar_originCube_pos hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have huL := sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hQL : 0 ≤ blockVecDot p (blockMatVecMul
      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) := by
    rw [mixMain_annealedBilinear_eq hnu L hJ4 (n : ℤ) p]
    nlinarith only [mul_nonneg hsL.le (vecNormSq_nonneg p.1),
      mul_nonneg huL.le (vecNormSq_nonneg p.2)]
  refine ⟨hQL, ?_⟩
  have hdom : blockVecDot p (blockMatVecMul
        (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) ≤
      (1 - t)⁻¹ * blockVecDot p
        (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) := by
    rw [mixMain_annealedBilinear_eq hnu ell hJ4 (n : ℤ) p,
      mixMain_annealedBilinear_eq hnu L hJ4 (n : ℤ) p]
    exact mixMain_quadraticForm_dom_of_scalar_bounds hs hu p
  have h1t : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith only [ht])]
    linarith only [ht]
  exact hdom.trans (mul_le_mul_of_nonneg_right h1t hQL)

end

end SuperdiffusionCLT.Section4.Mixing
