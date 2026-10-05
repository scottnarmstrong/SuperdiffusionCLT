/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.J5Reduction

/-!
# Rescaling the translation action

For a nonzero real `c` let `nv_Twist c Ω` be a copy of a space `Ω` whose translation action is
`z +ᵥ ω = (c • z) +ᵥ ω`. A horizontal gradient for the rescaled action is `c` times a horizontal
gradient for the original one, so the closed stationary potential subspace, and with it the
stationary potential projection, is the same for the two actions.

* `nv_hasHorizontalGradient_twist`: the gradient relation of the rescaled action.
* `nv_stationaryPotentialSubspace_twist`, `nv_stationarySolenoidalSubspace_twist`: equality of the
  potential and solenoidal subspaces.
* `nv_stationaryPotentialProjection_twist`: equality of the projections.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Probability.Stationary

noncomputable section

universe u

/-- A copy of `Ω` whose translation action is rescaled by `c`. -/
def nv_Twist (_c : ℝ) (Ω : Type u) : Type u := Ω

variable {d : ℕ} {Ω : Type u}

instance nv_Twist.instMeasurableSpace (c : ℝ) [m : MeasurableSpace Ω] :
    MeasurableSpace (nv_Twist c Ω) := m

/-- Forget the rescaling. -/
def nv_Twist.untwist {c : ℝ} (ω : nv_Twist c Ω) : Ω := ω

/-- Reinterpret a point of `Ω` on the rescaled copy. -/
def nv_Twist.twist (c : ℝ) (ω : Ω) : nv_Twist c Ω := ω

instance nv_Twist.instVAdd (c : ℝ) [VAdd (Vec d) Ω] : VAdd (Vec d) (nv_Twist c Ω) :=
  ⟨fun z ω ↦ nv_Twist.twist c ((c • z) +ᵥ ω.untwist)⟩

theorem nv_Twist.vadd_def (c : ℝ) [VAdd (Vec d) Ω] (z : Vec d) (ω : nv_Twist c Ω) :
    z +ᵥ ω = nv_Twist.twist c ((c • z) +ᵥ ω.untwist) :=
  rfl

instance nv_Twist.instAddAction (c : ℝ) [AddAction (Vec d) Ω] :
    AddAction (Vec d) (nv_Twist c Ω) where
  zero_vadd ω := by
    rw [nv_Twist.vadd_def, smul_zero, zero_vadd]
    rfl
  add_vadd z w ω := by
    rw [nv_Twist.vadd_def, nv_Twist.vadd_def, nv_Twist.vadd_def, smul_add, add_vadd]
    rfl

instance nv_Twist.instMeasurableConstVAdd (c : ℝ) [MeasurableSpace Ω] [AddAction (Vec d) Ω]
    [MeasurableConstVAdd (Vec d) Ω] : MeasurableConstVAdd (Vec d) (nv_Twist c Ω) where
  measurable_const_vadd z :=
    show Measurable fun ω : Ω ↦ (c • z) +ᵥ ω from measurable_const_vadd (c • z)

/-- The same measure, on the rescaled copy. -/
def nv_twistMeasure (c : ℝ) [MeasurableSpace Ω] (μ : Measure Ω) : Measure (nv_Twist c Ω) := μ

instance nv_twistMeasure.instInvariant (c : ℝ) [MeasurableSpace Ω] [AddAction (Vec d) Ω]
    (μ : Measure Ω) [VAddInvariantMeasure (Vec d) Ω μ] :
    VAddInvariantMeasure (Vec d) (nv_Twist c Ω) (nv_twistMeasure c μ) where
  measure_preimage_vadd z s hs :=
    VAddInvariantMeasure.measure_preimage_vadd (c • z) (μ := μ) (s := s) hs

variable [MeasurableSpace Ω] [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
  (μ : Measure Ω) [VAddInvariantMeasure (Vec d) Ω μ]

theorem nv_hasDerivAt_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    (hc : c ≠ 0) (g : ℝ → E) (v : E) :
    HasDerivAt g v 0 ↔ HasDerivAt (fun t : ℝ ↦ g (c * t)) (c • v) 0 := by
  constructor
  · intro h
    have h2 : HasDerivAt (fun t : ℝ ↦ c * t) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
    exact HasDerivAt.scomp_of_eq (0 : ℝ) (by simpa using h) h2 (by simp)
  · intro h
    have h2 : HasDerivAt (fun t : ℝ ↦ c⁻¹ * t) c⁻¹ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul c⁻¹
    have h3 := HasDerivAt.scomp_of_eq (0 : ℝ) (by simpa using h) h2 (by simp)
    have hfun : ((fun t : ℝ ↦ g (c * t)) ∘ fun t : ℝ ↦ c⁻¹ * t) = g := by
      funext t
      simp [mul_inv_cancel_left₀ hc]
    rw [hfun, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
    exact h3

theorem nv_hasHorizontalGradient_twist {c : ℝ} (hc : c ≠ 0) (φ : ScalarL2 μ) (F : VectorL2 d μ) :
    HasHorizontalGradient (μ := nv_twistMeasure c μ) (φ : ScalarL2 (nv_twistMeasure c μ))
        (F : VectorL2 d (nv_twistMeasure c μ)) ↔
      HasHorizontalGradient (μ := μ) φ (c⁻¹ • F) := by
  unfold HasHorizontalGradient
  refine forall_congr' fun i ↦ ?_
  have hfun : (fun t : ℝ ↦ koopman (μ := nv_twistMeasure c μ) (t • (Pi.single i 1 : Vec d))
      (φ : ScalarL2 (nv_twistMeasure c μ))) =
      fun t : ℝ ↦ (fun s : ℝ ↦ koopman (μ := μ) (s • (Pi.single i 1 : Vec d)) φ) (c * t) := by
    funext t
    change koopman (μ := μ) (c • t • (Pi.single i 1 : Vec d)) φ = _
    rw [smul_smul]
  rw [hfun, map_smul, nv_hasDerivAt_rescale hc, smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact Iff.rfl

theorem nv_horizontalGradientRange_twist {c : ℝ} (hc : c ≠ 0) :
    horizontalGradientRange (μ := μ) (d := d) =
      horizontalGradientRange (μ := nv_twistMeasure c μ) (d := d) := by
  refine Submodule.ext fun F ↦ ?_
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨c⁻¹ • φ, (nv_hasHorizontalGradient_twist μ hc (c⁻¹ • φ) F).2 (hφ.smul c⁻¹)⟩
  · rintro ⟨φ, hφ⟩
    have h := (nv_hasHorizontalGradient_twist μ hc φ F).1 hφ
    have h2 := h.smul c
    rw [smul_inv_smul₀ hc] at h2
    exact ⟨c • φ, h2⟩

theorem nv_stationaryPotentialSubspace_twist {c : ℝ} (hc : c ≠ 0) :
    stationaryPotentialSubspace (μ := μ) (d := d) =
      stationaryPotentialSubspace (μ := nv_twistMeasure c μ) (d := d) :=
  congrArg Submodule.topologicalClosure (nv_horizontalGradientRange_twist μ hc)

theorem nv_stationarySolenoidalSubspace_twist {c : ℝ} (hc : c ≠ 0) :
    stationarySolenoidalSubspace (μ := μ) (d := d) =
      stationarySolenoidalSubspace (μ := nv_twistMeasure c μ) (d := d) :=
  congrArg Submodule.orthogonal (nv_stationaryPotentialSubspace_twist μ hc)

/-- Rescaling the translation action leaves the stationary potential projection unchanged. -/
theorem nv_stationaryPotentialProjection_twist {c : ℝ} (hc : c ≠ 0) (F : VectorL2 d μ) :
    stationaryPotentialProjection (μ := nv_twistMeasure c μ) (d := d)
        (F : VectorL2 d (nv_twistMeasure c μ)) =
      stationaryPotentialProjection (μ := μ) (d := d) F := by
  symm
  have h1 : stationaryPotentialProjection (μ := μ) (d := d) F ∈
      stationaryPotentialSubspace (μ := nv_twistMeasure c μ) (d := d) := by
    rw [← nv_stationaryPotentialSubspace_twist μ hc]
    exact stationaryPotentialProjection_mem (μ := μ) (d := d) F
  have h2 : F - stationaryPotentialProjection (μ := μ) (d := d) F ∈
      stationarySolenoidalSubspace (μ := nv_twistMeasure c μ) (d := d) := by
    rw [← nv_stationarySolenoidalSubspace_twist μ hc]
    exact sub_stationaryPotentialProjection_mem_orthogonal (μ := μ) (d := d) F
  exact eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    (μ := nv_twistMeasure c μ) (d := d) h1 h2

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
