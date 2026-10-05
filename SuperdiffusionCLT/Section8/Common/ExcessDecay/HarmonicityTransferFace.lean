/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.HarmonicityTransferTests
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OddReflectionGlue

/-!
# The single-face harmonicity transfer

Let `U` be an open bounded convex domain symmetric under the reflection `r` in
the hyperplane `{yᵢ = a}`, and let `H = faceHalf U i a σ` be one of the two open
halves it cuts.  If `v` is weakly harmonic on `H`, then its **odd extension**
across the face — `w = v - v ∘ r` after zero extension off `H` — is weakly
harmonic on all of `U`.

## Scope

The `H¹(U)` *packaging* of the odd extension is an **input** here: the theorem
takes an `H1Function U` whose recorded gradient is the odd extension of the
zero-extended gradient of `v`, and proves that it is weakly harmonic.  Producing
that packaging from a *localized* zero-trace hypothesis on the met face is the
separate job of the weak-gradient locality lemma
(`WeakGradientLocality.lean`) — the harmonicity proved here never uses the
zero-trace hypothesis, only the harmonicity of `v` on the half.

## References

* CoarseGraining, `Homogenization/Sobolev/Foundations/CubeReflection/` (the
  reflection, its measure preservation, and the *even* fold
  `foldedCoordFaceTest`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization SuperdiffusionCLT.Section8.Common.Support MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Reflection algebra -/

/-- The coordinates of the face reflection: the normal coordinate is flipped
about `a`, the tangential ones are untouched. -/
theorem coordFaceReflection_apply (a : ℝ) (i : Fin d) (y : Vec d) (j : Fin d) :
    coordFaceReflection a i y j = if j = i then 2 * a - y j else y j := by
  have hsplit : coordFaceReflection a i y j =
      coordReflectionLinear i y j + coordFaceReflectionOffset a i j := rfl
  rw [hsplit]
  by_cases hj : j = i
  · subst hj
    have h2 : coordReflectionLinear j y j = -(y j) := by simp [coordReflectionLinear]
    have h3 : coordFaceReflectionOffset a j j = 2 * a := by simp [coordFaceReflectionOffset]
    rw [h2, h3, ite_eq_left rfl]
    ring
  · have h2 : coordReflectionLinear i y j = y j := by simp [coordReflectionLinear, hj]
    have h3 : coordFaceReflectionOffset a i j = 0 := by simp [coordFaceReflectionOffset, hj]
    rw [h2, h3, ite_eq_right hj, add_zero]

/-- A point of the reflecting hyperplane is fixed. -/
theorem coordFaceReflection_eq_self {a : ℝ} {i : Fin d} {y : Vec d} (hy : y i = a) :
    coordFaceReflection a i y = y := by
  funext j
  rw [coordFaceReflection_apply]
  by_cases hj : j = i
  · subst hj
    rw [ite_eq_left rfl]
    linarith only [hy]
  · rw [ite_eq_right hj]

/-- If `U` is invariant under the reflection, so is the closed support of any
test function supported in `U` — hence the reflected test is again supported in
`U`. -/
theorem tsupport_comp_coordFaceReflection_subset {U : Set (Vec d)} (a : ℝ) (i : Fin d)
    (hUsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ U ↔ y ∈ U)
    {φ : Vec d → ℝ} (hφU : tsupport φ ⊆ U) :
    tsupport (fun z => φ (coordFaceReflection a i z)) ⊆ U := by
  have hpre : Function.support (fun z => φ (coordFaceReflection a i z)) =
      coordFaceReflection a i ⁻¹' Function.support φ := rfl
  have hclos : coordFaceReflection a i ⁻¹' closure (Function.support φ) =
      closure (coordFaceReflection a i ⁻¹' Function.support φ) :=
    (coordFaceReflectionHomeomorph a i).preimage_closure (Function.support φ)
  show closure (Function.support fun z => φ (coordFaceReflection a i z)) ⊆ U
  rw [hpre, ← hclos]
  intro z hz
  exact (hUsymm z).1 (hφU hz)

/-! ## 2. Integrability of the tested pairing -/

/-! ## 3. The transfer -/

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
