/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.H1.LocalizedZeroTrace
public import Homogenization.Sobolev.H1.Algebra.H10Function
public import Homogenization.Sobolev.H1.BasicLemmas
public import Homogenization.Book.Ch03.Definitions

/-!
# The boundary datum on the covering cube

The last hypothesis CoarseGraining's boundary coarse Caccioppoli inequality
asks of its datum, once the covering cube is in place, is the *localized zero trace* through the
Dirichlet patch:

```text
  LocalizedZeroTraceFunctionOn (c + □_k) (openCubeAtScale x (k-1)) (u - v) .
```

Here the ambient domain is `□_m` but the Caccioppoli domain is the smaller
covering cube, so the `H¹₀` witness has to *descend*.  It does, and for exactly
the reason the covering was designed: a cutoff supported in the patch
multiplies the `H¹₀(□_m)` approximants into functions supported in `patch ∩
□_m`, and that set is inside the covering cube.

## Main results

* `h10RestrictOfApproxSupport` — an `H¹₀(Ω)` function whose approximants are all
  supported in an open `W ⊆ Ω` is an `H¹₀(W)` function, with the same value,
  gradient and approximating sequence.
* `localizedZeroTraceFunctionOn_of_memH10_of_inter_subset` — the descent: a
  global zero trace on `Ω` gives the localized zero trace on `W` through every
  window `V` with `V ∩ Ω ⊆ W`.

## What is not done here

This is stated in the **untranslated** frame, with the covering cube as a
translated set.  Feeding it to CoarseGraining's theorem, which is stated at a
`TriadicCube`, requires the A4 translation transport of the datum (sample
translation); that step belongs to the development's `TranslationTransport*`
lane and is *not* taken here.  Nothing in this module asserts the Caccioppoli
estimate.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; boundary application.
* CoarseGraining, `Sobolev/H1/LocalizedZeroTrace.lean`,
  `Sobolev/H1/Algebra/H10Function.lean`, `Sobolev/H1/BasicLemmas.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization Homogenization.Book.Ch03 MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. The `H¹₀` descent -/

/-- **`H¹₀` descends along the support of its approximants.**

If every smooth compactly supported approximant of `u ∈ H¹₀(Ω)` is supported in
the open subset `W ⊆ Ω`, then `u` is an `H¹₀(W)` function: the same value, the
same weak gradient, the same approximating sequence.  Only the two `L²`
convergences have to be re-read, and they are inherited because `eLpNorm` is
monotone in the measure. -/
def h10RestrictOfApproxSupport {Ω W : Set (Vec d)} (hWopen : IsOpen W) (hWΩ : W ⊆ Ω)
    (u : H10Function Ω) (hsupp : ∀ n, tsupport (u.approx n) ⊆ W) : H10Function W where
  toH1Function := u.toH1Function.restrict hWopen hWΩ
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := hsupp
  tendsto_approx := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds u.tendsto_approx
      (fun _ => zero_le) fun n => ?_
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hWΩ)
  tendsto_approx_grad := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (u.tendsto_approx_grad i) (fun _ => zero_le) fun n => ?_
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hWΩ)

@[simp] theorem h10RestrictOfApproxSupport_toFun {Ω W : Set (Vec d)} (hWopen : IsOpen W)
    (hWΩ : W ⊆ Ω) (u : H10Function Ω) (hsupp : ∀ n, tsupport (u.approx n) ⊆ W) :
    (h10RestrictOfApproxSupport hWopen hWΩ u hsupp).toH1Function.toFun =
      u.toH1Function.toFun :=
  rfl

/-! ## 2. The localized zero trace on a subdomain -/

/-- **The boundary datum descends to the covering set.**

A function with a *global* zero trace on `Ω` has the localized zero trace on
any open `W ⊆ Ω` through any window `V` with `V ∩ Ω ⊆ W`. -/
theorem localizedZeroTraceFunctionOn_of_memH10_of_inter_subset {Ω W V : Set (Vec d)}
    (hWopen : IsOpen W) (hWΩ : W ⊆ Ω) (hVW : V ∩ Ω ⊆ W) (u : H10Function Ω) :
    LocalizedZeroTraceFunctionOn W V u.toH1Function.toFun := by
  intro eta heta heta_compact heta_sub
  refine ⟨h10RestrictOfApproxSupport hWopen hWΩ
    (u.mulContDiffHasCompactSupport heta heta_compact) ?_, ?_⟩
  · intro n
    show tsupport (fun x => eta x * u.approx n x) ⊆ W
    intro p hp
    refine hVW ⟨heta_sub ?_, u.approx_support_subset n ?_⟩
    · exact tsupport_mul_subset_left (f := eta) (g := u.approx n) hp
    · exact tsupport_mul_subset_right (f := eta) (g := u.approx n) hp
  · rw [h10RestrictOfApproxSupport_toFun,
      H10Function.mulContDiffHasCompactSupport_toFun]

/-! ## 3. The instance at the well-placed covering cube -/

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
