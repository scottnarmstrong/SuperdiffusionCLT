/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.TransposeMaximizer
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence
public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedRoute

/-!
# Forward doubled fields for the averaged conjunct-3 route

`Conj3AveragedRoute.lean` reduces the conjunct-3 conclusion to the datum
`Conj3AveragedRouteData`, whose `Z` and `Zt` slots hold doubled fields built from scalar
maximizers: a forward and a transpose maximizer for each of the two coefficient objects.
The forward maximizers are given by the hypotheses of the statement; the transpose maximizers
are supplied by `TransposeMaximizer.exists_isResponseMaximizer_transpose`, which needs no
hypothesis beyond the coefficient object itself.

This module fixes the transpose maximizer and builds the doubled field from it:

* `transposeResponseMaximizer` names, by classical choice, the transpose maximizer whose
  existence is the content of `TransposeMaximizer.exists_isResponseMaximizer_transpose`, and
  `transposeResponseMaximizer_isMaximizer` records that it is one;
* `forwardDoubledField` is the doubled field attached to a forward maximizer `v` of `a` and
  the chosen transpose maximizer of `a`, the field stored in the `Z` slot of the route data.

The loading bookkeeping is the one point where a sign slip would produce a true-looking but
wrong statement.  The route data is built at the reflected loading `(-p, q)`, so the forward
maximizer hypothesis, which reads `IsResponseMaximizer U a (-(-p)) q v`, is the given
`IsResponseMaximizer U a p q v`; and the transpose maximizers sit at
`(-(-p), -q) = (p, -q)`.  For `d ≥ 2` the two loadings cannot be identified, so the reflection
is not cosmetic.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The chosen transpose maximizer -/

/-- **The transpose maximizer, by classical choice.**  For every Chapter 2
coefficient object `a` on `U` and every loading `(p, q)`, the transpose field
`a.transpose` has a response maximizer
(`TransposeMaximizer.exists_isResponseMaximizer_transpose`), and this names one
of them.  Fixing a choice makes the fields of `Conj3AveragedRouteData` definite:
the route's `Z`/`Zt` slots are built from a maximizer of `a` at `(p, q)` and a
maximizer of `a.transpose` at `(p, -q)`. -/
def transposeResponseMaximizer (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) : Book.Ch02.Solution U a.transpose :=
  Classical.choose (exists_isResponseMaximizer_transpose U a p q)

/-- **The chosen transpose maximizer is a maximizer.**  This is the defining
property of `transposeResponseMaximizer`; it is `Classical.choose_spec` of the
existence theorem. -/
theorem transposeResponseMaximizer_isMaximizer (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    Book.Ch02.IsResponseMaximizer U a.transpose p q
      (transposeResponseMaximizer U a p q) :=
  Classical.choose_spec (exists_isResponseMaximizer_transpose U a p q)

/-! ## The forward doubled field -/

/-- **The doubled field attached to a forward maximizer.**  Given a response
maximizer `v` of `a` at `(p, q)`, pair it with the chosen transpose maximizer of
`a` at the reflected loading `(p, -q)` and form the doubled field of the pair.
This is exactly the field the route data stores in its `Z` slot. -/
def forwardDoubledField (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) (v : Book.Ch02.Solution U a) : Book.Ch02.DoubledField d :=
  Book.Ch02.doubledFieldOfScalarMaximizers a v (transposeResponseMaximizer U a p (-q))

end

end SuperdiffusionCLT.Section2.Localization
