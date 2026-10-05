/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedRoute
public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparison
public import SuperdiffusionCLT.Section3.Terms.SubcollectionSum

/-!
# The cube Jensen

The printed concentration comparison

`∫⁻ ‖⟨a_ℓ ∇ũ_n − q̃⟩_R‖² ≤ C 3^{−d (m − j − ℓ)} ∫⁻ ‖a_ℓ ∇ũ_n − q̃‖²_{L̲²(R)}`

consumes the cube form of Jensen's inequality for the square at our carrier.  This file proves
it and the `L̲²` membership of a coordinate on a sub-cube.

* `sq_volumeAverage_le_volumeAverage_sq` is the cube form of Jensen's inequality for the
  square: the square of a normalized cube average is at most the normalized cube average of the
  square.  It is `Mathlib`'s Jensen for the probability measure `normalizedCubeMeasure` read
  through `volumeAverage_cubeSet` and `cubeAverage_eq_integral_normalizedCubeMeasure`.
* `memLp_coord_of_memLp_subset`: a coordinate of an `L̲²` vector field is `L̲²` on any
  sub-cube.
* `lintegral_ofReal_sq_volumeAverage_le_volumeAverage_sq`: the pointwise cube Jensen
  integrated over the sample.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The scalar cube Jensen at the volume-average carrier -/

/-- **Jensen on one triadic cube, scalar form**: the square of the normalized
cube average of an `L̲²` function is at most the normalized cube average of its
square.  This is `Mathlib`'s `ConvexOn.map_integral_le` for `x ↦ x ^ 2` at the
probability measure `normalizedCubeMeasure Q`, read through the
identification of `volumeAverage (cubeSet Q)` with the normalized integral. -/
theorem sq_volumeAverage_le_volumeAverage_sq (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : MeasureTheory.MemLp g 2 (normalizedCubeMeasure Q)) :
    (volumeAverage (cubeSet Q) g) ^ 2 ≤ volumeAverage (cubeSet Q) (fun x => g x ^ 2) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hgint : Integrable g (normalizedCubeMeasure Q) := hg.integrable (by norm_num)
  have hg2int : Integrable (fun x => g x ^ 2) (normalizedCubeMeasure Q) := hg.integrable_sq
  have hJ := ConvexOn.map_integral_le (μ := normalizedCubeMeasure Q)
    (s := Set.univ) (f := g) (g := fun x : ℝ => x ^ 2)
    (Even.convexOn_pow (𝕜 := ℝ) (by norm_num : Even 2))
    (continuous_pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hgint hg2int
  have hbridge : ∀ f : Vec d → ℝ, volumeAverage (cubeSet Q) f =
      ∫ x, f x ∂normalizedCubeMeasure Q := fun f => by
    rw [SuperdiffusionCLT.Section3.Setup.volumeAverage_cubeSet,
      cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [hbridge g, hbridge (fun x => g x ^ 2)]
  exact hJ

/-! ## `L̲²` membership of a coordinate on a sub-cube -/

/-- A coordinate of an `L̲²` vector field is `L̲²` on any sub-cube.  This is the
membership the scalar cube Jensen consumes at each block of the printed
decomposition, and it follows from the `L̲²` hypothesis at the parent cube. -/
theorem memLp_coord_of_memLp_subset {Q B : TriadicCube d} (hsub : cubeSet B ⊆ cubeSet Q)
    {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    (i : Fin d) : MeasureTheory.MemLp (fun x => F x i) 2 (normalizedCubeMeasure B) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp_memLp'
    (memLp_hilbertifyVecField_iff.1 (memLp_two_cubeSet_subset hsub hF))

/-- **The cube Jensen integrated over the sample.**  For an `L̲²`
coordinate the pointwise cube Jensen is integrated over the sample; no
measurability of the integrand is needed, since `lintegral_mono` is
unconditional. -/
theorem lintegral_ofReal_sq_volumeAverage_le_volumeAverage_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {Q : TriadicCube d} {F : Ω → Vec d → Vec d} (i : Fin d)
    (hL2 : ∀ ω, MeasureTheory.MemLp (fun x => F ω x i) 2 (normalizedCubeMeasure Q)) :
    (∫⁻ ω, ENNReal.ofReal ((volumeAverage (cubeSet Q) (fun x => F ω x i)) ^ 2) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal (volumeAverage (cubeSet Q) (fun x => (F ω x i) ^ 2)) ∂μ := by
  refine MeasureTheory.lintegral_mono fun ω => ?_
  exact ENNReal.ofReal_le_ofReal (sq_volumeAverage_le_volumeAverage_sq Q (hL2 ω))

end

end SuperdiffusionCLT.Section3.Terms
