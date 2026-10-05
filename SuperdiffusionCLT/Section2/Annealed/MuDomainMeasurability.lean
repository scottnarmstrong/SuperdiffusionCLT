/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityInputs
public import Homogenization.Geometry.ConvexDomain
public import Homogenization.Probability.RegCoeffField.Sigma

/-!
# `Mu`-measurability on a bounded open convex domain from a measurable source

`Section2.BfAmEllipticityInputs` proves the carrier `Mu`-measurability engine
`measurable_Mu_of_aeeSlice_measurable_entryTest` on an arbitrary open set of
finite volume.  Its inputs are the two premises of the `AEE` slice assembly:

* `hSlice`, the carrier taking values pointwise in one quantitative `AEE` slice;
* `hEntry`, the measurability of the localized entry-test generators
  `ω ↦ entryTestR i j φ (A ω)` over the smooth compactly supported test functions.

This module discharges the second premise: on the carrier `RegCoeffField d`,
each entry generator `entryTestR i j φ` is measurable for a test function `φ`
(`Homogenization.measurable_entryTestR`), so `hEntry` is *automatic* from the
measurability of the source `A` — no separate hypothesis is needed.  Combining
this with the general-open-domain slice event and the domain bookkeeping
of `IsOpenBoundedConvexDomain` (openness, finite volume, and the finiteness of
the restricted measure) yields the `Mu`-measurability engine on every bounded
open convex domain, which is exactly the input `hMu` of
`measurable_blockMatrixOperatorNorm_envelopeRescale_of_measurable_Mu` on the domains of
`Homogenization.Book.Ch02.Domain`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- **The localized entry-test premise is automatic from a measurable source.**
For a measurable carrier `A : Ω → RegCoeffField d` and a smooth compactly
supported test function `φ`, the sample function `ω ↦ entryTestR i j φ (A ω)` is
measurable.  This is the composition of the carrier measurability of the
entry generator (`Homogenization.measurable_entryTestR`) with `hA`; the support
condition `tsupport φ ⊆ U` of the engine's `hEntry` plays no role in the
measurability and is dropped here. -/
theorem measurable_entryTestR_comp_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → RegCoeffField d} (hA : Measurable A) (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    Measurable (fun ω => entryTestR i j φ (A ω)) :=
  (measurable_entryTestR i j (IsProbeR.of_smooth hφ hcs)).comp hA

/-- **The carrier `Mu`-measurability engine on a bounded open convex domain,
from a measurable source.**  For a bounded open convex `U` and a carrier
`A : Ω → RegCoeffField d` taking values pointwise in the quantitative `AEE` slice
`k`, the coarse-grained energy `ω ↦ Mu U P (A ω).toFun` is measurable.

Compared with `measurable_Mu_of_aeeSlice_measurable_entryTest`, the entry-test
premise `hEntry` is *gone*: it is supplied by
`measurable_entryTestR_comp_of_measurable hA`, so the only remaining
mathematical input is the slice membership `hSlice`.  The three domain premises
of the engine (openness, finite Lebesgue volume and the finiteness of the
restricted measure) are read off `IsOpenBoundedConvexDomain`, and the positive
`toReal` volume from
`volume_toReal_pos_of_isOpenBoundedConvexDomain`. -/
theorem measurable_Mu_of_isOpenBoundedConvexDomain_of_measurable_source
    {Ω : Type*} [MeasurableSpace Ω] {U : Set (Vec d)} {k : ℕ}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A : Ω → RegCoeffField d} (hA : Measurable A)
    (hSlice : ∀ ω, AEEQuantitativeEllipticSlice U k (A ω).toFun)
    (P : BlockVec d) :
    Measurable (fun ω => Mu U P (A ω).toFun) := by
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isFiniteMeasure_restrict_volume
  exact measurable_Mu_of_aeeSlice_measurable_entryTest (U := U) (k := k)
    hU.isOpen hU.volume_lt_top.ne
    (volume_toReal_pos_of_isOpenBoundedConvexDomain hU hne)
    hSlice
    (fun i j φ hφ hcs _hsupp =>
      measurable_entryTestR_comp_of_measurable hA i j hφ hcs)
    P

end

end SuperdiffusionCLT.Section2.Annealed
