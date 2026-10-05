/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyD3
public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftField
public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespDescendantBound

/-!
# Near-scale assembly: the field-side translations

* `srootNSD_term_eq`, `srootNSD_mx_le`: the term `srootE_term` is the weight times the maximal
  descendant response, which is at most `z` once every descendant response is.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- `srootE_term` is the geometric weight times the maximal descendant response. -/
theorem srootNSD_term_eq {d : ℕ} [NeZero d] (s : ℝ) (a : Homogenization.CoeffField d)
    (a0 : Homogenization.Mat d) (n l : ℕ) :
    srootE_term s a a0 n l = Homogenization.geometricWeight s 2 l *
      Homogenization.maxDescendantNormalizedBlockResponseAtScale
        (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ)) a a0 := by
  have hk : (n : ℤ) - (l : ℤ) ≤ (Homogenization.originCube d (n : ℤ)).scale := by
    show (n : ℤ) - (l : ℤ) ≤ (n : ℤ)
    omega
  have hnn := Homogenization.maxDescendantNormalizedBlockResponseAtScale_nonneg
    (Homogenization.originCube d (n : ℤ)) hk a a0
  unfold srootE_term
  congr 1
  show (Homogenization.maxDescendantNormalizedBlockResponseAtScale
    (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ)) a a0 ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = _
  rw [← Real.rpow_mul hnn]
  norm_num

/-- The maximal descendant response is at most `z` when each descendant response is. -/
theorem srootNSD_mx_le {d : ℕ} [NeZero d] (n l : ℕ) (a : Homogenization.CoeffField d)
    (a0 : Homogenization.Mat d) {z : ℝ}
    (h : ∀ R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
      ((n : ℤ) - (l : ℤ)), Homogenization.normalizedBlockResponseMax R a a0 ≤ z) :
    Homogenization.maxDescendantNormalizedBlockResponseAtScale
      (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (l : ℤ)) a a0 ≤ z := by
  have hk : (n : ℤ) - (l : ℤ) ≤ (Homogenization.originCube d (n : ℤ)).scale := by
    show (n : ℤ) - (l : ℤ) ≤ (n : ℤ)
    omega
  unfold Homogenization.maxDescendantNormalizedBlockResponseAtScale Homogenization.finsetSsup
  have hne : (((fun R => Homogenization.normalizedBlockResponseMax R a a0) ''
      (↑(Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
        ((n : ℤ) - (l : ℤ))) : Set (Homogenization.TriadicCube d)))).Nonempty :=
    Set.Nonempty.image _ (Finset.coe_nonempty.2
      (Homogenization.descendantsAtScale_nonempty _ hk))
  refine csSup_le hne ?_
  rintro x ⟨R, hR, rfl⟩
  exact h R (Finset.mem_coe.mp hR)

end

end SuperdiffusionCLT.Section4.MinimalScales
