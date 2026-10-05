/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.CubeSchauderExistence
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.AffineSplitHarmonic
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.EquationRestrictionZeroExtension
public import SuperdiffusionCLT.Section8.Common.Support.Dirichlet

/-!
# Cube Schauder: the freezing step (harmonic approximation with divergence forcing)

If `u` solves `-Δ u = ∇·G` on a window `U` and `V ⊆ U` is an interior sub-domain,
then for **any** constant vector `c` the same `u` solves `-Δ u = ∇·(G - c)` on
`V`, because a constant field is weakly divergence free.  Solving the zero-trace
problem `-Δ w = ∇·(G - c)` on `V` and setting `h := u - w` produces a *weakly
harmonic* comparison function on `V` together with the sharp energy bound

```text
  ∫_V |∇w|² ≤ ∫_V |G - c|² .
```

Taking `c = G(x₀)` for a point `x₀` of the sub-cube and using the `C^{0,1/2}`
bound on `G` gives the **freezing gain**: the harmonic approximation error is
controlled by the *oscillation* of the forcing over the sub-cube, hence by
`(side)^{1/2} · [G]_{C^{0,1/2}}` rather than by `‖G‖`.

This is the display `e.harmapprox.Schauder` of Armstrong--Kuusi, *Elliptic Regularity*,
specialized to `a = I_d` (where the `‖a - I_d‖_{L^∞}` leg vanishes identically), in the
development's own carriers.

## Main results

* `integral_vecDot_matVecMul_one`, `isDivFormWeakSolutionOn_one_iff`, `isEllipticFieldOn_one` —
  the identity coefficient field drops out of the flux pairing, the weak equation and the
  ellipticity.
* `exists_h10_isDivFormWeakSolutionOn_one` — the zero-trace solution of
  `-Δ w = ∇·F` on an arbitrary open bounded convex domain.
* `integrableOn_vecNormSq_grad`, `integrableOn_vecNormSq_of_memVectorL2` — the Dirichlet energy
  of an `H¹` function and the squared length of an `L²` field are integrable.

The freezing step itself (the constant `c` subtracted from the forcing, and the energy bound
`∫_V |∇w|² ≤ ∫_V |G - c|²`) is not part of this module.

## References

* Armstrong--Kuusi, *Elliptic Regularity*, Propositions `p.Schauder.Calpha` and
  `p.Schauder.C1alpha`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.Estimates.Schauder

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section8.Common.Support

variable {d : ℕ}

/-! ## 1. The identity background -/

/-- The identity coefficient field drops out of the flux pairing. -/
theorem integral_vecDot_matVecMul_one {U : Set (Vec d)} (F p : Vec d → Vec d) :
    ∫ x in U, vecDot (matVecMul ((fun _ => (1 : Mat d)) x) (F x)) (p x) ∂volume =
      ∫ x in U, vecDot (F x) (p x) ∂volume :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => by
    show vecDot (matVecMul (1 : Mat d) (F x)) (p x) = vecDot (F x) (p x)
    rw [matVecMul_one])

/-- `-Δ u = ∇·g` in the development's carrier, unfolded at the identity background. -/
theorem isDivFormWeakSolutionOn_one_iff {U : Set (Vec d)} {u : H1Function U}
    {g : Vec d → Vec d} :
    IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U u g ↔
      ∀ φ : H10Function U,
        ∫ x in U, vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume =
          -∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂volume := by
  unfold IsDivFormWeakSolutionOn
  simp only [integral_vecDot_matVecMul_one]

/-- The identity is the unit diffusivity. -/
theorem isEllipticFieldOn_one {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn 1 1 U (fun _ => (1 : Mat d)) := by
  have h := isEllipticFieldOn_smul_one (d := d) (sigma := 1) (by norm_num) hU
  simpa only [one_smul] using h

/-! ## 3. Zero-trace solvability and the sharp energy bound -/

/-- **The zero-datum comparator exists on any open bounded convex domain.**  For
`F ∈ L²(U)` there is `w ∈ H¹₀(U)` with `-Δ w = ∇·F` weakly. -/
theorem exists_h10_isDivFormWeakSolutionOn_one [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hUne : U.Nonempty)
    {F : Vec d → Vec d} (hF : MemVectorL2 U F) :
    ∃ w : H10Function U,
      IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U w.toH1Function F := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hreal :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hU
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := fun _ => (1 : Mat d)) (U := U) (g := fun x => -F x) (lam := 1) (Lam := 1)
      hF.neg hreal hUne (isEllipticFieldOn_one hU.isOpen.measurableSet)
  exact ⟨w,
    (isZeroTraceDirichletRhsWeakSolution_iff_isDivFormWeakSolutionOn
      (u := w.toH1Function) (w := w) (g := F) fun _ => rfl).1 hw⟩

/-- The Dirichlet energy of an `H¹` function is integrable on its domain. -/
theorem integrableOn_vecNormSq_grad {U : Set (Vec d)} (u : H1Function U) :
    IntegrableOn (fun x => vecNormSq (u.grad x)) U volume :=
  SuperdiffusionCLT.Section8.Common.ExcessDecay.integrableOn_vecDot_grad u u

/-- The squared Euclidean length of an `L²` field is integrable. -/
theorem integrableOn_vecNormSq_of_memVectorL2 {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : IntegrableOn (fun x => vecNormSq (F x)) U volume :=
  integrableOn_vecDot_of_memVectorL2 hF hF

end SuperdiffusionCLT.Section8.Common.Estimates.Schauder
