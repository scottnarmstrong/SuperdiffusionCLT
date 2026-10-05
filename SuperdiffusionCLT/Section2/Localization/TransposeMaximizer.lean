/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.AdjointCorrespondence
public import SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause
public import Homogenization.Book.Ch02.Theorems.GradientUniqueness

/-!
# The transpose maximizer exists

The averaged route to the third conjunct of `cutoff_localization` consumes, through
the scalar maximizer bridge and
`AdjointCorrespondence.doubledFieldOfScalarMaximizers_isDoubledMuMinimizer`, a
response maximizer of the **transpose** coefficient field at the reflected
loading `(p, -q)`.  The hypotheses of the statement name maximizers of the two forward
fields only, so the question is whether such a transpose maximizer can be
produced.

**It can, and unconditionally.**  `Book.Ch02.responseExistenceTheory` is the
Chapter 2 concave-maximum existence theorem: for every Chapter 2
coefficient object `a : CoeffOn U` and every loading `(p, q)` it supplies a
response maximizer.  The Chapter 2 adjoint `a.transpose` is again a `CoeffOn U`
with the same ellipticity and entry constants (`CoeffOn.transpose`, whose
`aeElliptic` field is `isEllipticMatrix_transpose` of the original), so applying
the existence theorem to `a.transpose` produces the maximizer the doubled-field
construction needs.  The forward maximizer `v` enters the *existence* statement
nowhere: the transpose problem has its own coercive quadratic part, driven by the
same symmetric part `symmPart (a x)` because `matTranspose` leaves `symmPart`
fixed.

The result below records this:

* `exists_isResponseMaximizer_transpose`: for every `CoeffOn U` and every
  loading, a response maximizer of the transpose field **exists**, with no
  maximizer hypothesis at all.

The construction is dimension-general; no dimension-one argument occurs.

## What this says about the `hdata` residual

The transpose maximizer is not a hypothesis that must be added: it
is a theorem about the coefficient object, proved by the same concave-maximum
argument that proves forward existence, holding at every loading and for every
Chapter 2 coefficient.  The doubled field is therefore constructible from the
standing Chapter 2 structure alone.  What the maximizer hypotheses
`hu`/`hv` fix is only the *forward* maximizers whose gradients the conclusion
measures; maximality of `v` does not by itself determine a transpose maximizer
(the two are different variational problems), but it does not need to, because
existence is independent of it.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Existence of the transpose maximizer -/

/-- **A response maximizer of the transpose field exists, unconditionally.**
For every Chapter 2 coefficient object `a` on `U` and every loading `(p, q)`,
the transpose field `a.transpose` — again a `CoeffOn U`, with the same
ellipticity and entry constants — has a response maximizer.  No hypothesis about
`a` or about any forward maximizer is used: `Book.Ch02.responseExistenceTheory`
is applied to `a.transpose` directly. -/
theorem exists_isResponseMaximizer_transpose (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    ∃ vStar : Book.Ch02.Solution U a.transpose,
      Book.Ch02.IsResponseMaximizer U a.transpose p q vStar := by
  obtain ⟨v, _hmean, hv⟩ := Book.Ch02.responseMaximizerExists U a.transpose p q
  exact ⟨v, hv⟩

end

end SuperdiffusionCLT.Section2.Localization
