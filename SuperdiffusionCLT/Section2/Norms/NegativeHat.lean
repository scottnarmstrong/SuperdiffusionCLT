/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.Gagliardo
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.CoarseGraining.Definitions
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The hatted negative fractional seminorms of a matrix field

The paper defines the hatted
negative seminorm at order one by duality against smooth mean-zero test
functions,

> `[f]_{Ŵ̲^{-1,p'}(U)} = sup { ⨍_U f g : g ∈ C^∞(U), [g]_{W̲^{1,p}(U)} ≤ 1,
>   (g)_U = 0 }`,

and adds that for vector fields the pairing is against gradients.
The display `e.kmn.Wminussp` uses the volume-normalized `Ŵ̲^{-s,p}(cu_l)` at a
fractional order, the third term of `e.kbounds.minscale.form` uses
the un-normalized `Ĥ^{-s}(cu_m)`, and the matrix pairing
is used in the estimate that `p · ⨍_{cu_m} (k_{ℓ'} − k_ℓ) ∇w` is at most
`‖(k_{ℓ'} − k_ℓ) p‖_{Ĥ̲^{-1/2}(cu_m)} ‖∇w‖_{H̲^{1/2}(cu_m)}`.

This module provides the rank-one gradient pairing density `v ⊗ ∇g` with `|v| ≤ 1`,
which is the class used in that estimate; the hatted norms themselves are defined
in `NegativeHatFullGradient`.

## The pairing, written without a gradient vector

For a matrix field `M` and a scalar `g`, the rank-one pairing is
`⟨M(x), v ⊗ ∇g(x)⟩ = ∑_{i,j} M(x)_{ij} v_i ∂_j g(x)`, and the inner sum over
`i` is the row vector `v ᵥ* M(x)`. Hence the density is the Fréchet
derivative of `g` evaluated at that vector, `fderiv ℝ g x (v ᵥ* M x)`, which
needs no inner-product structure on `Vec d`.

The pairing density is integrated with a Bochner integral, whose value on a
non-integrable function is `0`. **That branch is unreachable for the fields the
estimates quantify over**: `matGradientPairingDensity_integrableOn_cubeSet`
proves that for a continuous matrix field `M` and a smooth test field `g` the
density is integrable on every triadic cube, and
`continuous_matGradientPairingDensity` is the continuity it uses.

## Main definitions

* `matGradientPairingDensity`: the density `⟨M, v ⊗ ∇g⟩`.

## Main results

* `continuous_matGradientPairingDensity`,
  `matGradientPairingDensity_integrableOn_cubeSet`: the finiteness facts that
  keep the Bochner branch unreachable.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The density `⟨M(x), v ⊗ ∇g(x)⟩` of the rank-one gradient pairing,
written as `∂_{v ᵥ* M x} g (x)`. -/
noncomputable def matGradientPairingDensity (M : Vec d → Mat d) (v : Vec d)
    (g : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ g x (Matrix.vecMul v (M x))

theorem continuous_matGradientPairingDensity {M : Vec d → Mat d}
    (hM : Continuous M) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : Vec d) : Continuous (matGradientPairingDensity M v g) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  have hvm : Continuous (fun x : Vec d => Matrix.vecMul v (M x)) := by
    refine continuous_pi (fun j => ?_)
    have : Continuous (fun x : Vec d => ∑ i, v i * M x i j) :=
      continuous_finsetSum Finset.univ fun i _ =>
        continuous_const.mul
          ((continuous_apply j).comp ((continuous_apply i).comp hM))
    simpa [Matrix.vecMul, dotProduct, Matrix.transpose] using this
  exact hfd.clm_apply hvm

theorem integrableOn_cubeSet_of_continuous {f : Vec d → ℝ} (hf : Continuous f)
    (Q : TriadicCube d) : IntegrableOn f (cubeSet Q) volume :=
  (hf.continuousOn.integrableOn_compact
    ((isBounded_cubeSet Q).isCompact_closure)).mono_set subset_closure

theorem matGradientPairingDensity_integrableOn_cubeSet {M : Vec d → Mat d}
    (hM : Continuous M) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : Vec d) (Q : TriadicCube d) :
    IntegrableOn (matGradientPairingDensity M v g) (cubeSet Q) volume :=
  integrableOn_cubeSet_of_continuous
    (continuous_matGradientPairingDensity hM hg v) Q

end

end Norms
end Section2
end SuperdiffusionCLT
