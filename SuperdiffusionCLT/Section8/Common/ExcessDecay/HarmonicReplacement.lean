/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors

/-!
# Harmonic-replacement well-posedness: the constant-coefficient Dirichlet replacement

Nothing here claims the anchor or any source node.

ABK26's Step 1 introduces two constant-coefficient comparison functions on the child window
`W = x+□_n`:

```text
  -Δ v = 0            in W ,   v   = u  on ∂W ;
  -σ̄ Δ v_g = ∇·g      in W ,   v_g = u  on ∂W .
```

The existence and uniqueness of such replacements come from CoarseGraining, through the `H¹₀(U)`
weak solution of `−∇·a∇ρ = ∇·G` for any `G ∈ L²(U)` and any elliptic field `a`, followed by the
affine shift `v = u − ρ` that converts the *zero*-trace problem into the *`u`-trace* problem, by
moving the datum's own flux `a₀∇u` into the forcing.  This module holds the two measure-theoretic
ingredients of that shift on an open triadic cube.

## Main results

* `instIsFiniteMeasureVolumeMeasureOnOpenCubeSet` — the normalized volume measure of an open
  triadic cube is finite.
* `integral_vecDot_add_left_split` — the forcing pairing is additive in the force, in the form
  the affine shift produces it.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. Domain facts for the open triadic cube -/

section Window

variable [NeZero d] (Q : TriadicCube d)

instance instIsFiniteMeasureVolumeMeasureOnOpenCubeSet :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (Ch02.cubeDomain Q).instIsFiniteMeasureVolumeMeasureOn

end Window

/-! ## 2. Splitting a forcing pairing -/

section Pairing

variable {U : Set (Vec d)}

/-- The forcing pairing is additive in the force, in the form the affine shift
produces it (the combined field is given pointwise). -/
theorem integral_vecDot_add_left_split {F G H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) (hH : ∀ x, H x = F x + G x)
    (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂MeasureTheory.volume) +
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hFint : MeasureTheory.IntegrableOn
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : MeasureTheory.IntegrableOn
      (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) +
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, vecDot_add_left]
  rw [hfun, MeasureTheory.integral_add hFint hGint]

end Pairing

/-! ## 3. The corrector force -/

variable [NeZero d] {Q : TriadicCube d}

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
