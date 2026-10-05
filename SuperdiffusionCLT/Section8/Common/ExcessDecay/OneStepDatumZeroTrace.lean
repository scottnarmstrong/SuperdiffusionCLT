/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.H1.LocalizedZeroTrace
public import Homogenization.Book.Ch03.Definitions

/-!
# The `hzt` supplier: cutoff localization of `H¹₀`

The face-only zero trace of the datum-split competitor `V_odd = v − ℓ_h − v₁` (the paper asserts
that `v − ℓ_h − v₁` vanishes on the met portion of `∂□_m`) is
`LocalizedZeroTraceFunctionOn (truncatedWindow x m (n-2)) (reflectedWindow x m (n-2)) v.toFun`.
Its proof decomposes the competitor as

```text
  v − ℓ − v₁ = (v − u) + (u − h) + (h − ℓ − Ψ) + (Ψ − v₁) ,
```

and localizes each summand by a cutoff.  The common tool is the cutoff localization of `H¹₀`,
which is the declaration proved in this module.

## Main results

* `memH10_mul_of_tsupport_subset` — if `f ∈ H¹₀(B)` and `η` is a smooth compactly supported
  cutoff with `tsupport η ⊆ V`, then `η·f ∈ H¹₀(V ∩ B)`.

No trace operator, no max principle, no analytic input: this is pure `H¹₀` bookkeeping.

## References

* CoarseGraining `Homogenization/Sobolev/H1/LocalizedZeroTrace.lean` (the
  predicate), `Homogenization/Sobolev/H1/Algebra/H10Function.lean`
  (`mulContDiffHasCompactSupport`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 2. `H¹₀` localization by a cutoff -/

/-- **Cutoff localization of `H¹₀`.**  If `f ∈ H¹₀(B)` and `η` is a smooth
compactly supported cutoff with `tsupport η ⊆ V`, then `η·f ∈ H¹₀(V ∩ B)`:
the `H¹₀(B)` approximants of the product are supported in
`tsupport η ∩ tsupport (approx) ⊆ V ∩ B`, and every field of the witness
restricts. -/
theorem memH10_mul_of_tsupport_subset {B V : Set (Vec d)} (hB : IsOpen B)
    (hV : IsOpen V) {f : Vec d → ℝ} (hf : MemH10 B f) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) :
    MemH10 (V ∩ B) (fun y => η y * f y) := by
  obtain ⟨w, hw⟩ := hf
  set W : H10Function B := w.mulContDiffHasCompactSupport hη hηc with hWdef
  have hWfun : W.toH1Function.toFun = fun y => η y * f y := by
    rw [hWdef, H10Function.mulContDiffHasCompactSupport_toFun]
    funext y
    rw [show w y = w.toH1Function.toFun y from rfl, hw]
  have happrox : ∀ n, W.approx n = fun x => η x * w.approx n x := fun n => rfl
  have hmono : volume.restrict (V ∩ B) ≤ volume.restrict B :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  have hmemL2 : MemL2On (V ∩ B) fun y => η y * f y := by
    have h := W.toH1Function.memL2
    rw [hWfun] at h
    exact h.mono_measure hmono
  have hgradL2 : GradMemL2On (V ∩ B) W.toH1Function.grad :=
    fun i => (W.toH1Function.gradMemL2 i).mono_measure hmono
  have hweak : HasWeakGradientOn (V ∩ B) (fun y => η y * f y) W.toH1Function.grad := by
    have h := W.toH1Function.hasWeakGradient
    rw [hWfun] at h
    exact h.restrict (hV.inter hB) Set.inter_subset_right
  have hsupp : ∀ n, tsupport (W.approx n) ⊆ V ∩ B := by
    intro n
    rw [happrox n]
    refine Set.subset_inter ?_ ?_
    · exact (tsupport_mul_subset_left (f := η) (g := w.approx n)).trans hηV
    · exact (tsupport_mul_subset_right (f := η) (g := w.approx n)).trans
        (w.approx_support_subset n)
  have htend : Tendsto
      (fun n => eLpNorm (fun x => W.approx n x - η x * f x) 2
        (volume.restrict (V ∩ B))) atTop (nhds 0) := by
    have hbase := W.tendsto_approx
    rw [hWfun] at hbase
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbase
      (fun n => zero_le) (fun n => ?_)
    exact eLpNorm_mono_measure _ hmono
  have htendg : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm
        (fun x => (fderiv ℝ (W.approx n) x) (basisVec i) - W.toH1Function.grad x i) 2
        (volume.restrict (V ∩ B))) atTop (nhds 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (W.tendsto_approx_grad i) (fun n => zero_le) (fun n => ?_)
    exact eLpNorm_mono_measure _ hmono
  refine ⟨⟨⟨fun y => η y * f y, W.toH1Function.grad, hmemL2, hgradL2, hweak⟩,
    W.approx, W.approx_smooth, W.approx_hasCompactSupport, hsupp, htend, htendg⟩,
    rfl⟩

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
