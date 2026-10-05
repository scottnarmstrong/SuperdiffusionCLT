/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.AverageNorms
public import Homogenization.Sobolev.Fractional.EuclideanWspLocalization

/-!
# The average over the subcubes `z + cu_n` of `cu_K`

`subcubeAvg Kc n f` is `avsum_{z ∈ 3^n ℤ^d ∩ cu_Kc} f(z + cu_n)`, the subcubes being the triadic
cubes `descendantsAtScale (originCube d Kc) n`. The exact partition identity
`subcubeAvg_lintegral_normalizedCubeMeasure`: the subcube average of the normalized integrals of a
function is its normalized integral on `cu_Kc`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory

variable {d : ℕ}

/-- `avsum_{z ∈ 3^n ℤ^d ∩ cu_Kc} f(z + cu_n)`; the subcubes are `descendantsAtScale`. -/
noncomputable def subcubeAvg (Kc n : ℕ) (f : TriadicCube d → ENNReal) : ENNReal :=
  ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ENNReal)⁻¹ *
    ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), f Q

theorem subcubeAvg_eq_descendantsENNAverage {Kc n : ℕ} (hn : n ≤ Kc)
    (f : TriadicCube d → ENNReal) :
    subcubeAvg Kc n f = descendantsENNAverage (originCube d (Kc : ℤ)) (Kc - n) f := by
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have h := descendantsAtScale_eq_descendantsAtDepth (originCube d (Kc : ℤ)) hk
  have hnat : Int.toNat ((originCube d (Kc : ℤ)).scale - (n : ℤ)) = Kc - n := by
    show Int.toNat ((Kc : ℤ) - (n : ℤ)) = Kc - n
    omega
  rw [hnat] at h
  unfold subcubeAvg descendantsENNAverage
  rw [h]

/-- The exact partition identity: the subcube average of normalized integrals is the normalized
integral on `cu_Kc`. -/
theorem subcubeAvg_lintegral_normalizedCubeMeasure {Kc n : ℕ} (hn : n ≤ Kc)
    (f : Vec d → ENNReal) :
    subcubeAvg Kc n (fun Q => ∫⁻ x, f x ∂normalizedCubeMeasure Q) =
      ∫⁻ x, f x ∂normalizedCubeMeasure (originCube d (Kc : ℤ)) := by
  rw [subcubeAvg_eq_descendantsENNAverage hn]
  exact descendantsENNAverage_lintegral_normalizedCubeMeasure_eq _ _ f

theorem subcubeAvg_mono {Kc n : ℕ} {f g : TriadicCube d → ENNReal} (h : ∀ Q, f Q ≤ g Q) :
    subcubeAvg Kc n f ≤ subcubeAvg Kc n g := by
  unfold subcubeAvg
  exact mul_le_mul' le_rfl (Finset.sum_le_sum fun Q _ => h Q)

theorem subcubeAvg_add {Kc n : ℕ} (f g : TriadicCube d → ENNReal) :
    subcubeAvg Kc n (fun Q => f Q + g Q) = subcubeAvg Kc n f + subcubeAvg Kc n g := by
  unfold subcubeAvg
  rw [Finset.sum_add_distrib, mul_add]

theorem subcubeAvg_const_mul {Kc n : ℕ} (c : ENNReal) (f : TriadicCube d → ENNReal) :
    subcubeAvg Kc n (fun Q => c * f Q) = c * subcubeAvg Kc n f := by
  unfold subcubeAvg
  rw [← Finset.mul_sum]
  ring

end SuperdiffusionCLT.Section5
