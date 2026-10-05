/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliD

/-!
# Grid-cube blackbox bounds in the shifted-index form of the interior Caccioppoli core

The two weak bounds of the right-hand-side lemma are available for the field
`ν Id + kf (y + z + ·)` on the origin cube `□_n`, for the shifts `z = 3^{n-3} k`, `k ∈ ℤ^d`, with
`z + □_n ⊆ □_m`.  The grid cubes of `ca1_interior_det` are the descendants `R` of `□_m` of depth
`h = m - n`; their shift `triadicCubeShift R` is `3^{n-3} k` with `k = 27 · index R`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The shift of a descendant of `□_m` at depth `h = m - n` is `3^{n-3} k` for `k = 27 · index`,
and the translated origin cube lies in `□_m`. -/
theorem ca1w_shift_form (m n h : ℕ) (hnh : n + h = m) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) h) :
    R.scale = (n : ℤ) ∧
      triadicCubeShift R = (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (((27 * R.index i : ℤ)) : ℝ)) ∧
      (fun x => triadicCubeShift R + x) '' cubeSet (originCube d (n : ℤ)) ⊆
        cubeSet (originCube d (m : ℤ)) := by
  have hs : R.scale = (n : ℤ) := by
    have := scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [this]
    have h' : (m : ℤ) = n + h := by exact_mod_cast hnh.symm
    simp only [originCube]
    omega
  refine ⟨hs, ?_, ?_⟩
  · funext i
    simp only [triadicCubeShift, cubeScaleFactor, hs]
    have h3 : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ ((n : ℤ) - 3) * 27 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [h3]
    push_cast
    ring
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have h1 := cubeSet_subset_of_mem_descendantsAtDepth hR
    refine h1 ?_
    rw [cubeSet_eq_translateSet_originCube_of_triadicCube R, hs]
    exact ⟨w, hw, add_comm _ _⟩

/-- **The grid-cube bounds of `ca1_interior_det` from the shifted blackbox bounds.** -/
theorem ca1w_hBB (m n h : ℕ) (hnh : n + h = m) {ν S α1 β1 α2 β2 : ℝ} (kf : Vec d → Mat d)
    (y : Vec d)
    (hBB0 : ∀ k : Fin d → ℤ,
      (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) '' cubeSet (originCube d (n : ℤ)) ⊆
        cubeSet (originCube d (m : ℤ)) →
      ∀ (u : H1Function (openCubeSet (originCube d (n : ℤ)))) (f : Vec d → ℝ),
      IsWeakSolutionOn (fun x => ν • (1 : Mat d) +
          kf (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (openCubeSet (originCube d (n : ℤ))) u f (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ))
          (1 / 4 : ℝ) (fun x => matVecMul (ν • (1 : Mat d) +
            kf (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) - S • (1 : Mat d)) (u.grad x))) ≤
        ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (n : ℤ)) (ENNReal.ofReal (sobStar d)).conjExponent f ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ))
          (1 / 4 : ℝ) u.grad) ≤
        ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (n : ℤ)) (ENNReal.ofReal (sobStar d)).conjExponent f) :
    ∀ R ∈ descendantsAtDepth (originCube d (m : ℤ)) h,
      ∀ (u' : H1Function (openCubeSet (originCube d R.scale))) (f' : Vec d → ℝ),
      IsWeakSolutionOn (fun x => (fun x => ν • (1 : Mat d) + kf (y + x)) (x + triadicCubeShift R))
        (openCubeSet (originCube d R.scale)) u' f' (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) (fun x => matVecMul ((fun x => ν • (1 : Mat d) + kf (y + x)) (x + triadicCubeShift R) -
            S • (1 : Mat d)) (u'.grad x))) ≤
        ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f' := by
  intro R hR
  obtain ⟨hs, hsh, himg⟩ := ca1w_shift_form m n h hnh hR
  have hk := hBB0 (fun i => 27 * R.index i)
  have hkk : (fun i : Fin d => (3 : ℝ) ^ ((n : ℤ) - 3) * (((fun i => 27 * R.index i) i : ℤ) : ℝ)) =
      triadicCubeShift R := hsh.symm
  have hk' := hk (by rw [hkk]; exact himg)
  rw [hkk] at hk'
  generalize triadicCubeShift R = z at hk'
  have hpt : ∀ x : Vec d, ν • (1 : Mat d) + kf (y + (x + z)) = ν • (1 : Mat d) + kf (y + z + x) := by
    intro x
    rw [add_comm x z, ← add_assoc]
  have gen : ∀ s : ℤ, s = (n : ℤ) → ∀ (u' : H1Function (openCubeSet (originCube d s))) (f' : Vec d → ℝ),
      IsWeakSolutionOn (fun x => (fun x => ν • (1 : Mat d) + kf (y + x)) (x + z))
        (openCubeSet (originCube d s)) u' f' (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d s)
          (1 / 4 : ℝ) (fun x => matVecMul ((fun x => ν • (1 : Mat d) + kf (y + x)) (x + z) -
            S • (1 : Mat d)) (u'.grad x))) ≤
        ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d s) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d s)
            (ENNReal.ofReal (sobStar d)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d s)
          (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d s) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d s)
            (ENNReal.ofReal (sobStar d)).conjExponent f' := by
    intro s hs0 u' f' hu'
    subst hs0
    beta_reduce at hu' ⊢
    simp only [hpt] at hu' ⊢
    exact hk' u' f' hu'
  exact gen R.scale hs

end SuperdiffusionCLT.Section7
