/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.StreamIncrementScaleEstimates
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockD

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

/-!
# Centring: coarse averages of the stream matrix at every depth

The window clause of the statement `streamIncrement_scale_estimates` bounds the operator
norm of the average of `k - (k)_{cu_m}` over every sub-cube of scale `n ≥ m - ⌈A log (B m)⌉` by
`A log (B m) δ m^σ`.  Choosing `A = max 1 (t / log m)` and `B = 1` turns it into a bound at *every*
depth `t ≤ m`: `max (log m) t · δ m^σ`.  Entries of a matrix are bounded by its operator norm, so the
bound holds entrywise, which is the form needed to pair a scalar entry against a scalar test
function.

## Main results

* `Section7.kc1_depth_average_bound`: the entrywise average bound at depth `t`.
* `Section7.kc1_child_parent_bound`: the same for a child minus its parent.
-/

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory Homogenization.Book.Ch02

variable {d : ℕ}

/-- `max 1 (t / L) * L = max L t` for `L > 0`. -/
theorem kc1_max_mul {L : ℝ} (hL : 0 < L) (t : ℝ) : max 1 (t / L) * L = max L t := by
  rcases le_total 1 (t / L) with h | h
  · rw [max_eq_right h, div_mul_cancel₀ _ hL.ne']
    rw [max_eq_right]
    rwa [le_div_iff₀ hL, one_mul] at h
  · rw [max_eq_left h, one_mul]
    rw [max_eq_left]
    rwa [div_le_iff₀ hL, one_mul] at h

/-- **Coarse averages at every depth.** If the window clause holds at scale `m ≥ 2`, then every
entrywise average of the field `κ` over a depth-`t` descendant of `cu_m` is at most
`max (log m) t · δ m^σ`. -/
theorem kc1_depth_average_bound {κ : Vec d → Mat d} {m : ℕ} {δ σ : ℝ} (hm : 2 ≤ m)
    (hwin : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∀ n : ℕ, (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
      n ≤ m → ∀ Q : TriadicCube d, Q.scale = (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
          matrixOperatorNorm (volumeAverageMat (cubeSet Q) κ) ≤
            A * Real.log (B * (m : ℝ)) * δ * (m : ℝ) ^ σ)
    {t : ℕ} (ht : t ≤ m) {Q : TriadicCube d}
    (hQ : Q ∈ descendantsAtDepth (originCube d (m : ℤ)) t) (i j : Fin d) :
    |volumeAverage (cubeSet Q) (fun y => κ y i j)| ≤
      max (Real.log (m : ℝ)) (t : ℝ) * δ * (m : ℝ) ^ σ := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hL : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith only [hmR])
  set A : ℝ := max 1 ((t : ℝ) / Real.log (m : ℝ)) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAL : A * Real.log (m : ℝ) = max (Real.log (m : ℝ)) (t : ℝ) := kc1_max_mul hL _
  have hQsub : Q ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d (m - t) m := by
    rw [SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes,
      show m - (m - t) = t by omega]
    exact hQ
  have hscale := SuperdiffusionCLT.Section2.Estimates.Stream.scale_of_mem_largeCubeSubcubes
    (by omega : m - t ≤ m) hQsub
  have hcenter : cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) :=
    cubeSet_subset_of_mem_descendantsAtDepth hQ (SuperdiffusionCLT.Section2.Estimates.Stream.cubeCenter_mem_cubeSet Q)
  have htA : (t : ℝ) ≤ A * Real.log (m : ℝ) := by
    rw [hAL]; exact le_max_right _ _
  have hceil : (m : ℤ) - ⌈A * Real.log (1 * (m : ℝ))⌉ ≤ ((m - t : ℕ) : ℤ) := by
    have h1 : (t : ℝ) ≤ ((⌈A * Real.log (1 * (m : ℝ))⌉ : ℤ) : ℝ) := by
      rw [one_mul]; exact htA.trans (Int.le_ceil _)
    have h2 : (t : ℤ) ≤ ⌈A * Real.log (1 * (m : ℝ))⌉ := by exact_mod_cast h1
    omega
  have hle := hwin A 1 hA1 le_rfl (m - t) hceil (by omega) Q hscale hcenter
  have hentry := abs_entry_le_matrixOperatorNorm (volumeAverageMat (cubeSet Q) κ) i j
  have : A * Real.log (1 * (m : ℝ)) * δ * (m : ℝ) ^ σ =
      max (Real.log (m : ℝ)) (t : ℝ) * δ * (m : ℝ) ^ σ := by rw [one_mul, hAL]
  rw [this] at hle
  exact hentry.trans hle

/-- **Child minus parent.** For a parent `P` at depth `t` and a child `R` of `P` (depth `t + 1`),
with `t + 1 ≤ m`, the entrywise averages of `κ` differ by at most
`(max (log m) t + max (log m) (t + 1)) δ m^σ`. -/
theorem kc1_child_parent_bound {κ : Vec d → Mat d} {m : ℕ} {δ σ : ℝ} (hm : 2 ≤ m)
    (hwin : ∀ A B : ℝ, 1 ≤ A → 1 ≤ B → ∀ n : ℕ, (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
      n ≤ m → ∀ Q : TriadicCube d, Q.scale = (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)) →
          matrixOperatorNorm (volumeAverageMat (cubeSet Q) κ) ≤
            A * Real.log (B * (m : ℝ)) * δ * (m : ℝ) ^ σ)
    {t : ℕ} (ht : t + 1 ≤ m) {P R : TriadicCube d}
    (hP : P ∈ descendantsAtDepth (originCube d (m : ℤ)) t) (hR : R ∈ childCubes P) (i j : Fin d) :
    |volumeAverage (cubeSet R) (fun y => κ y i j) - volumeAverage (cubeSet P) (fun y => κ y i j)| ≤
      (max (Real.log (m : ℝ)) (t : ℝ) + max (Real.log (m : ℝ)) ((t + 1 : ℕ) : ℝ)) * δ *
        (m : ℝ) ^ σ := by
  have hRd : R ∈ descendantsAtDepth (originCube d (m : ℤ)) (t + 1) := by
    rw [descendantsAtDepth_succ]
    exact Finset.mem_biUnion.2 ⟨P, hP, hR⟩
  have h1 := kc1_depth_average_bound hm hwin (by omega : t ≤ m) hP i j
  have h2 := kc1_depth_average_bound hm hwin ht hRd i j
  calc _ ≤ |volumeAverage (cubeSet R) (fun y => κ y i j)| +
        |volumeAverage (cubeSet P) (fun y => κ y i j)| := abs_sub _ _
    _ ≤ _ := by linarith only [h1, h2]

end SuperdiffusionCLT.Section7
