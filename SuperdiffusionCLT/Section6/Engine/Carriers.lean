/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.GrowthSpace
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import Homogenization.Multiscale.CubeAverage
public import Homogenization.Multiscale.NormalizedNorms

/-!
# Carriers of the regularity iteration
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- `u ∈ 𝒜(U; a)` with weak gradient `g`: `u` and `g` agree a.e. on `U` with an `a`-harmonic
`H¹(U)` function and its gradient. `IsBallSolution a R` is `IsSolOn a (euclidBall R)`. -/
def IsSolOn (a : CoeffField d) (U : Set (Vec d)) (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  ∃ v : AHarmonicFunction a U,
    v.toH1.toFun =ᵐ[volume.restrict U] u ∧ v.toH1.grad =ᵐ[volume.restrict U] g

/-- The open origin cube `□_n`, `n ∈ ℕ`. -/
abbrev engCube (d : ℕ) (n : ℕ) : Set (Vec d) := openCubeSet (originCube d (n : ℤ))

/-- Euclidean length of a vector of `Vec d`. -/
noncomputable def engNorm (e : Vec d) : ℝ := Real.sqrt (vecNormSq e)

/-- `‖f‖_{L̲²(□_n)}` as a real number. -/
noncomputable def cubeL2 (n : ℕ) (f : Vec d → ℝ) : ℝ :=
  cubeLpNorm (originCube d (n : ℤ)) 2 f

/-- `‖F‖_{L̲²(□_n)}` of a vector field (Euclidean length) as a real number. -/
noncomputable def cubeGradL2 (n : ℕ) (F : Vec d → Vec d) : ℝ :=
  cubeL2 n (fun x => engNorm (F x))

/-- The scale-normalized oscillation `3^{-n} ‖f - (f)_{□_n}‖_{L̲²(□_n)}`. -/
noncomputable def cubeFlat (n : ℕ) (f : Vec d → ℝ) : ℝ :=
  ((3 : ℝ)⁻¹) ^ n *
    cubeL2 n (fun x => f x - cubeAverage (originCube d (n : ℤ)) f)

/-- The slope of the `L²(□_n)`-best affine approximation of `f`:
`12 · 3^{-2n} ⨍_{□_n} f(x) x dx`. -/
noncomputable def affSlope (n : ℕ) (f : Vec d → ℝ) : Vec d :=
  fun i => 12 * (((3 : ℝ)⁻¹) ^ n) ^ 2 *
    cubeAverage (originCube d (n : ℤ)) (fun x => f x * x i)

theorem isBallSolution_iff_isSolOn (a : CoeffField d) (R : ℝ) (u : Vec d → ℝ)
    (g : Vec d → Vec d) : IsBallSolution a R u g ↔ IsSolOn a (euclidBall R) u g :=
  Iff.rfl

/-- Witness: the zero function is a solution on every set, with zero flatness and slope. -/
example (a : CoeffField d) (U : Set (Vec d)) : IsSolOn a U (fun _ => 0) (fun _ => 0) :=
  ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩

end SuperdiffusionCLT.Section6
