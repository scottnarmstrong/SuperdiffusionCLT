/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthC

/-!
# Coordinate algebra for the printed concentration comparison

The per-cube concentration `hconc` of the depth moment `_hConcDepth` of `term1_close` is the
printed comparison

`∫⁻ ‖⟨a_ℓ ∇ũ_n − q̃⟩_R‖² ≤ C 3^{−d (m − j − ℓ)} ∫⁻ ‖a_ℓ ∇ũ_n − q̃‖²_{L̲²(R)}`,

read on every depth-`j` descendant `R` of the centred cube `cu_m`.  This file collects the
coordinate algebra that reduces the vector statement to the scalar one: the Euclidean square of
a vector and the squared `HilbertVec` norm of a vector field are the sums of the squares of
their coordinates, a coordinate of a cube average is the cube average of the coordinate, and the
normalized `L̲²` energy of an `L̲²` vector field is the sum of the coordinate energies.

## Main results

* `vecNormSq_eq_sum_coordSq`, `norm_hilbertifyVecField_sq`: the coordinate decomposition of the
  norms.
* `volumeAverageVec_apply_coord`, `volumeAverage_cubeSet_finset_sum_of_integrableOn`: cube
  averages coordinatewise and of finite sums.
* `integrableOn_coord_sq_of_memLp`, `vecSqAvg_eq_sum_coordSq`: the squared coordinates of an
  `L̲²` field are integrable and sum to its energy.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The coordinate decomposition of the vector norm and the vector energy -/

/-- The Euclidean square of a vector is the sum of the squares of its
coordinates. -/
theorem vecNormSq_eq_sum_coordSq (v : Vec d) : vecNormSq v = ∑ i, (v i) ^ 2 := by
  rw [vecNormSq, vecDot]
  exact Finset.sum_congr rfl fun i _ => (sq (v i)).symm

/-- The `HilbertVec` reading of a vector field has squared norm the sum of the
squares of its coordinates.  The carrier `Vec d = Fin d → ℝ` is read in
`HilbertVec d`, whose norm is `vecNorm` (`norm_hilbertifyVecField_apply`), not the
supremum norm of `Vec d` itself. -/
theorem norm_hilbertifyVecField_sq (F : Vec d → Vec d) (x : Vec d) :
    ‖hilbertifyVecField F x‖ ^ 2 = ∑ i, (F x i) ^ 2 := by
  rw [norm_hilbertifyVecField_apply,
    SuperdiffusionCLT.Section3.Setup.vecNorm_sq_eq_vecNormSq]
  exact vecNormSq_eq_sum_coordSq (F x)

/-- A coordinate of the cube average of a vector field is the cube average of
that coordinate.  This is the definition of `volumeAverageVec` read as a rewrite
rule, and it is what carries every per-coordinate statement back to the vector
field. -/
theorem volumeAverageVec_apply_coord (U : Set (Vec d)) (f : Vec d → Vec d) (i : Fin d) :
    volumeAverageVec U f i = volumeAverage U (fun x => f x i) := rfl

/-- A finite sum comes out of a normalized cube average of integrable
integrands; this is `volumeAverage_cubeSet_finset_sum` with the continuity of the
summands weakened to their integrability on the cube. -/
theorem volumeAverage_cubeSet_finset_sum_of_integrableOn (R : TriadicCube d)
    (f : Fin d → Vec d → ℝ) (hf : ∀ i, IntegrableOn (f i) (cubeSet R) volume) :
    volumeAverage (cubeSet R) (fun x => ∑ i, f i x) = ∑ i, volumeAverage (cubeSet R) (f i) := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hf i), Finset.mul_sum]

/-- The squared coordinate of an `L̲²` vector field is integrable on the cube.
This is `integrableOn_coord_of_memLp` at exponent two, taken on the coordinate
itself rather than on its modulus. -/
theorem integrableOn_coord_sq_of_memLp (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    (i : Fin d) : IntegrableOn (fun x : Vec d => (F x i) ^ 2) (cubeSet Q) volume := by
  have := isFiniteMeasure_volume_restrict_cubeSet Q
  have h : MeasureTheory.MemLp (fun x : Vec d => F x i) 2 (volume.restrict (cubeSet Q)) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp'
      (SuperdiffusionCLT.Section3.ResponseFields.memLp_hilbertifyVecField_iff.1
        (memLp_two_volume_restrict_of_memLp Q hF))
  exact h.integrable_sq

/-- The normalized `L̲²` square average of an `L̲²` vector field is the sum of the
coordinate square averages.  This is the identity that lets the scalar
concentration engine be summed over the coordinates. -/
theorem vecSqAvg_eq_sum_coordSq (R : TriadicCube d) {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure R)) :
    vecSqAvg R F = ∑ i, volumeAverage (cubeSet R) (fun x => (F x i) ^ 2) := by
  have hpt : (fun x : Vec d => ‖hilbertifyVecField F x‖ ^ 2) =
      fun x : Vec d => ∑ i, (F x i) ^ 2 := funext fun x => norm_hilbertifyVecField_sq F x
  rw [vecSqAvg, cubeSquareAverage, hpt]
  exact volumeAverage_cubeSet_finset_sum_of_integrableOn R (fun i x => (F x i) ^ 2)
    fun i => integrableOn_coord_sq_of_memLp R hF i

end

end SuperdiffusionCLT.Section3.Terms
