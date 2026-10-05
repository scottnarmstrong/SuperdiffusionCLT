/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3Assembly
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedData

/-!
# The averaged route to conjunct 3

The statement `Frozen.Section2.cutoff_localization` states its third
conjunct entirely at the volume average `⨍_U` of `vecNormSq (u.grad - v.grad)`.
A pointwise window carrier would be a strict strengthening of that target: it
would ask at every point of `U` for two *pointwise* gap identities, and those are
not consequences of the variational characterisation, whose every identity is an
integral over `U` (the implication fails for `d ≥ 2`).

This module therefore carries the route on the average.  It carries the averaged
gap identities, the averaged maximality inequalities and the averaged remainder.

## The loading convention

The block quadratic form of the carrier's loading `(-p, q)` is the response
carrier: `⟨(-p,q), 𝐀(A)(-p,q)⟩ = 2 (pointwiseResponse A p q + p·q)`.
The split of the carrier is at `(p, q)` (`(p,q) = (Z - Zt) + Y`), because that is
the pair whose adjoint slopes `p ± w` the block correspondence reads.  The
averaged data below therefore fixes the loading `(-p, q)` for the maximality and
the remainder while keeping the split, the slope and the averaged gap identities
at the split pair.  The two loadings differ by the skew cross term
`4 · q · ((symmPart A)⁻¹ (skewPart A) p)`.

## Main results

* `Conj3AveragedRouteData`: the averaged data of the route, all energy
  statements normalized by `volumeAverage U`.
* `volumeAverage_congr_on`: functions equal on `U` have equal volume averages.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The averaged data of the route -/

/-- **The averaged data of the conjunct-3 route at the carrier's loading.**

The split is an identity of fields at the split pair `(p, q)`, as in the
carrier and as the block correspondence requires.  Every energy statement — the
two gap identities, the two maximality inequalities and the quadratic remainder —
is normalized by `volumeAverage U`, and the maximality and the remainder are
taken at the loading `(-p, q)`, the pair that carries the response functional.
The two integrability families make the averaging lemmas applicable. -/
structure Conj3AveragedRouteData (U : Set (Vec d)) (A At : Vec d → Mat d)
    (p q : Vec d) (eta : ℝ) [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] where
  Z : Vec d → BlockVec d
  Zt : Vec d → BlockVec d
  Y : Vec d → BlockVec d
  hU : MeasurableSet U
  hsplit : ∀ x ∈ U, ((p, q) : BlockVec d) = (Z x - Zt x) + Y x
  hgapA : averagedBlockQuadraticOn U A (fun x => Z x - Zt x) =
    averagedBlockQuadraticOn U A Zt - averagedBlockQuadraticOn U A Z
  hgapAt : averagedBlockQuadraticOn U At (fun x => Z x - Zt x) =
    averagedBlockQuadraticOn U At Z - averagedBlockQuadraticOn U At Zt
  hmaxA : averagedBlockQuadraticOn U A Z ≤
    averagedBlockQuadraticOn U A (fun _ : Vec d => ((-p, q) : BlockVec d))
  hmaxAt : averagedBlockQuadraticOn U At Zt ≤
    averagedBlockQuadraticOn U At (fun _ : Vec d => ((-p, q) : BlockVec d))
  hY : averagedBlockQuadraticOn U A Y ≤
    eta * eta * averagedBlockQuadraticOn U At
      (fun _ : Vec d => ((-p, q) : BlockVec d))
  hratioA : ∀ x ∈ U, ∀ W : BlockVec d,
    averagedBlockQuadratic (A x) W ≤
      averagedBlockQuadratic (At x) W + eta * averagedBlockQuadratic (At x) W
  hratioAt : ∀ x ∈ U, ∀ W : BlockVec d,
    averagedBlockQuadratic (At x) W ≤
      averagedBlockQuadratic (A x) W + eta * averagedBlockQuadratic (A x) W
  hIntAD : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Z x - Zt x)) U
  hIntAtD : IntegrableOn (fun x => averagedBlockQuadratic (At x) (Z x - Zt x)) U
  hIntAZ : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Z x)) U
  hIntAtZ : IntegrableOn (fun x => averagedBlockQuadratic (At x) (Z x)) U
  hIntAZt : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Zt x)) U
  hIntAtZt : IntegrableOn (fun x => averagedBlockQuadratic (At x) (Zt x)) U
  hIntAY : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Y x)) U
  hIntAP : IntegrableOn (fun x => averagedBlockQuadratic (A x) ((-p, q) : BlockVec d)) U
  hIntAtP : IntegrableOn (fun x => averagedBlockQuadratic (At x) ((-p, q) : BlockVec d)) U

/-! ## Averaging bookkeeping -/

/-- Two functions equal on `U` have equal volume averages over `U`. -/
theorem volumeAverage_congr_on {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hU : MeasurableSet U) (hfg : ∀ x ∈ U, f x = g x) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae
    ((MeasureTheory.ae_restrict_iff' hU).2 (Filter.Eventually.of_forall hfg))

/-! ## The averaged form of `e.minimizers.block.diff` -/

/-! ## The loading-`(-p,q)` block energy is the response functional -/

/-! ## The averaged slope estimate -/

/-! ## Conjunct 3 from the averaged data -/

/-! ## Satisfiability of the averaged data -/

end

end SuperdiffusionCLT.Section2.Localization
