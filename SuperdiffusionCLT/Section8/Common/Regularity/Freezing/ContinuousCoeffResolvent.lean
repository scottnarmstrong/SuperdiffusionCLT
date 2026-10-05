/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.Regularity.BoxGeometry
public import SuperdiffusionCLT.Section8.Common.Regularity.Freezing.BoundaryFreezingRadius

/-!
# Ellipticity bounds for a continuous coefficient

A coefficient with scalar symmetric part `nu * I` and continuous skew part is
elliptic on every compact set, with an upper constant that compactness
supplies.  The closed axis cube and the closure of a bounded domain are
compact, so on those two carriers the ellipticity certificate is a consequence
of the continuity hypothesis and need not be assumed.

This file names the compact, cube, and bounded-domain ellipticity certificates
supplied by continuity.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.Regularity.Freezing

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section8.Common.ExcessDecay
open SuperdiffusionCLT.Section8.Common.Regularity

noncomputable section

variable {d : ℕ}

/-! ## 1. Two compact carriers -/

/-- The coordinatewise closure of an axis cube is compact. -/
theorem isCompact_memAxisCubeClosure (z : Vec d) (L : ℝ) :
    IsCompact {x | MemAxisCubeClosure z L x} := by
  have hset : {x | MemAxisCubeClosure z L x} =
      Set.pi Set.univ fun i => Set.Icc (z i) (z i + L) := by
    ext x
    simp only [MemAxisCubeClosure, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      Set.mem_Icc, forall_const]
  rw [hset]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-! ## 2. The ellipticity witness supplied by continuity -/

/-- The upper ellipticity constant of a coefficient with scalar symmetric part
and continuous skew part on a compact set. -/
def compactEllipticUpper {W K : Set (Vec d)} (hW : MeasurableSet W)
    (hK : IsCompact K) (hWK : W ⊆ K) {nu : ℝ} (hnu : 0 < nu)
    {a : CoeffField d} (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) K) : ℝ :=
  Classical.choose (exists_isEllipticFieldOn_of_symmPart_eq_of_isCompact
    hW hK hWK hnu hsymm hcont)

/-- The ellipticity certificate that the constant names. -/
theorem isEllipticFieldOn_compactEllipticUpper {W K : Set (Vec d)}
    (hW : MeasurableSet W) (hK : IsCompact K) (hWK : W ⊆ K) {nu : ℝ}
    (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d)) K) :
    IsEllipticFieldOn nu (compactEllipticUpper hW hK hWK hnu hsymm hcont) W a :=
  Classical.choose_spec (exists_isEllipticFieldOn_of_symmPart_eq_of_isCompact
    hW hK hWK hnu hsymm hcont)

/-- The upper ellipticity constant on an axis cube. -/
def axisCubeEllipticUpper (z : Vec d) (L : ℝ) {nu : ℝ} (hnu : 0 < nu)
    {a : CoeffField d} (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d))
      {x | MemAxisCubeClosure z L x}) : ℝ :=
  compactEllipticUpper (isOpen_axisCube z L).measurableSet
    (isCompact_memAxisCubeClosure z L) (axisCube_subset_closureSet z L)
    hnu hsymm hcont

/-- **An axis-cube ellipticity certificate from continuity alone.** -/
theorem isEllipticFieldOn_axisCubeEllipticUpper (z : Vec d) (L : ℝ) {nu : ℝ}
    (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d))
      {x | MemAxisCubeClosure z L x}) :
    IsEllipticFieldOn nu (axisCubeEllipticUpper z L hnu hsymm hcont)
      (axisCube z L) a :=
  isEllipticFieldOn_compactEllipticUpper (isOpen_axisCube z L).measurableSet
    (isCompact_memAxisCubeClosure z L) (axisCube_subset_closureSet z L)
    hnu hsymm hcont

end

end SuperdiffusionCLT.Section8.Common.Regularity.Freezing
