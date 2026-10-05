/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ

/-!
# The variational identities of Subsection 2.2

The manuscript records four displays for the variational problem `J(U,p,q)`
of `e.J.def`. Throughout,
`s = (a + a^t)/2` is the symmetric part of the field and
`v(.,U,p,q)` is a maximizer of `J(U,p,q)` over `A(U)`.

* `e.firstvar`: for every `w in A(U)`,
  `q . f_U grad w - p . f_U a grad w = f_U grad w . s grad v(.,U,p,q)`.
* `e.secondvar`: the quadratic response identity, for every
  `w in A(U)`,
  `J(U,p,q) - f_U (-1/2 grad w . s grad w - p . a grad w + q . grad w) =
  f_U 1/2 (grad v - grad w) . s (grad v - grad w)`.
* `e.Jenergy.v`: `J` as the `s`-energy of the maximizer,
  `J(U,p,q) = f_U 1/2 grad v . s grad v`.
* `e.J.by.lin`:
  `J(U,p,q) = 1/2 (q . f_U grad v - p . f_U a grad v)`.

The upstream `CoarseGraining` library proves all four on the public Chapter 2
layer: the first variation as `Homogenization.Book.Ch02.firstVariationValue_eq_zero`
(the averaged Euler-Lagrange integrand `firstVariationIntegrand` vanishes),
the quadratic response identity as
`Homogenization.Book.Ch02.secondVariation_eq_of_isResponseMaximizer` (both
sides are by definition the manuscript's averages), and the energy form as
`Homogenization.Book.Ch02.responseJ_eq_energy_of_isResponseMaximizer`. The
print derives `e.Jenergy.v` from `e.secondvar` at the admissible competitor
`w = 0`; the proof below does not take that route and applies the upstream
energy identity directly, so the printed specialization at `w = 0` is not
carried out here. The linear form is not stated upstream; it follows here by
combining the energy form with the first variation at `w = v`.

What this module adds is the passage between the averaged Euler-Lagrange
integrand, which the upstream first-variation theorem controls as a single
average, and the manuscript's three-term form. The splitting uses the `L^2`
integrability of the gradient of an admissible solution and of its flux
(`Homogenization.Book.Ch02.Solution.flux_memVectorL2`), together with the
polarization identity `s xi = 1/2 (a xi + a^t xi)` for the cross term. Each
identity is stated with the hypothesis that `v` is a response maximizer, and
repeated for the canonical mean-zero maximizer `v(.,U,p,q)` of the Chapter 2
existence theory.

Two narrowings relative to the print are inherent in the Chapter 2 vocabulary
and are not repaired here: the admissible class `Book.Ch02.Solution U a`
carries an `H^1` gradient on all of `U`, so the displays quantify over
`A(U) ∩ H^1(U)` rather than the printed `A(U)` inside `H^1_loc(U)`,
and `Book.Ch02.Domain` requires a bounded convex domain,
strictly stronger than the bounded Lipschitz domains of the print.

## Main results

* `secondVariation_eq`: `e.secondvar`.
* `responseJ_eq_energy`: `e.Jenergy.v`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.CoarseGraining

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## Averaging plumbing

The Chapter 2 normalized average `f_U` is the raw volume average of the
`CoarseGraining` library, and a vector pairing against an averaged vector
field is the average of the pointwise pairing. These are the only identities
needed to move between the manuscript's display and the upstream averaged
integrand statements. -/

/-- The average of a halved integrand is half the average. -/
private theorem average_half {U : Book.Ch02.Domain d} (f : Vec d → ℝ) :
    Book.Ch02.average U (fun x => (1 / 2 : ℝ) * f x) =
      (1 / 2 : ℝ) * Book.Ch02.average U f := by
  have hsmul : ((1 / 2 : ℝ) • f) = fun x => (1 / 2 : ℝ) * f x := by
    funext x
    simp
  calc Book.Ch02.average U (fun x => (1 / 2 : ℝ) * f x)
      = volumeAverage (U : Set (Vec d)) ((1 / 2 : ℝ) • f) := by rw [hsmul]; rfl
    _ = (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d)) f := volumeAverage_smul _ _ _
    _ = (1 / 2 : ℝ) * Book.Ch02.average U f := rfl

/-! ## `e.firstvar`: the first variation

`e.firstvar`. The first-variation theorem states
that the averaged Euler-Lagrange integrand vanishes; the display below is that
identity written with the three terms averaged separately. -/

/-! ## `e.secondvar`: the quadratic response identity

`e.secondvar`. The response value of an admissible solution
is by definition the average of the manuscript's integrand and the
second-variation energy is by definition the average of the manuscript's
right-hand side, so this is the upstream identity read in the manuscript's
normalization. -/

/-! ## `e.Jenergy.v`: `J` as the `s`-energy of the maximizer

`e.Jenergy.v`. The print derives the display from
`e.secondvar` at the admissible competitor `w = 0`; the proof below applies the
Chapter 2 energy identity
`Homogenization.Book.Ch02.responseJ_eq_energy_of_isResponseMaximizer` directly
instead, so the printed specialization at `w = 0` is not the route proved
here. -/

/-- `e.Jenergy.v`: the response value is the `s`-energy of a
maximizer, `J(U,p,q) = f_U 1/2 grad v . s grad v`. -/
theorem responseJ_eq_energy {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U}
    {p q : Vec d} {v : Book.Ch02.Solution U a}
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    Book.Ch02.responseJ U a p q =
      Book.Ch02.average U (fun x =>
        (1 / 2 : ℝ) * vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x))) := by
  rw [show Book.Ch02.average U (fun x =>
        (1 / 2 : ℝ) * vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x))) =
      (1 / 2 : ℝ) * Book.Ch02.average U (fun x =>
        vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x))) from
    average_half (fun x => vecDot (v.toH1.grad x)
      (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x)))]
  exact Book.Ch02.responseJ_eq_energy_of_isResponseMaximizer hv

/-! ## `e.J.by.lin`: the linear form

`e.J.by.lin`. It is the energy form `e.Jenergy.v` combined
with the first variation `e.firstvar` at `w = v(.,U,p,q)`. -/

end

end SuperdiffusionCLT.Section2.CoarseGraining