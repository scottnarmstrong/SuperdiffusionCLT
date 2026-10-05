/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD

/-!
# The measurability obligation at the canonical Dirichlet response

The paper defines `w` as *the* Dirichlet response of `e.def.w`, the zero-trace
weak solution on `cu_m` of
`−Δw = ∇·((k_{L'} − k_{ℓ'}) p)`; the carrier stores no quotient, so a selection
is unique only up to a spatial null set and `dirichletResponse` is a
`Classical.choose`.  `ResponseMeasurability` proves that this makes every
a.e.-invariant observable *selection-free as a function of the sample*, so the
measurability obligation is **one and the same obligation for every selection**,
reducible to the canonical object.  This module states that obligation exactly
and records that it holds, at the canonical object and at every selection.

## The obligation, precisely

Let `L' ℓ' m : ℕ`, `p : Vec d`, and let `w : ShellSeq d → H10Function (cu_m)` be
any family with `∀ omega, IsDirichletResponse omega L' ℓ' m p (w omega)` — the
`_hw` binder of the statements of `l.LHS.term1` and `l.RHS.term3`.  The obligation is that the map

`omega ↦ (w omega).toH1Function.gradToHilbertVectorL2`,

from the shell-sequence carrier into the weak-gradient class space
`HilbertVectorL2 (openCubeSet (originCube d m))`, is measurable for the Borel
`σ`-algebra of `ShellSeq d` (the ambient one, which is what `P.toMeasure` of a
`ProbabilityMeasure` is read against), and a fortiori for the smaller
`σ`-algebra `F_> = σ(j_r : r > ℓ')` of the printed measurability sentence.
Nothing weaker is asked anywhere: the displays read
the response only through `(w omega).toH1Function.grad`.

## What it needs, and what is already available

The response is *not* measured as a value of a choice function.  It factors
through the one choice-free object available: the flux class

`omega ↦ toHilbertVectorL2OfVecField (memVectorL2_dirichletRhsField omega L' ℓ' m p)`

is measurable in the sample (`measurable_toHilbertVectorL2OfVecField_dirichletRhsField`),
and the cube Dirichlet solution operator `cubeDirichletGradClass Q` on the class
space — itself a single `Classical.choose` taken *as a function of the class* —
is `1`-Lipschitz (`lipschitzWith_cubeDirichletGradClass`) hence continuous, and
every response of a flux has the class it assigns
(`cubeDirichletGradClass_eq_of_isCubeDirichletResponse`).  Composition gives
measurability of the canonical response's gradient class
(`measurable_gradToHilbertVectorL2_dirichletResponse`); selection-freeness
carries it to every selection.

The dependence on `omega` runs through `streamCutoff omega L'` and
`streamCutoff omega ℓ'` — **not** through `coefficientCutoff`: `e.def.w` is the
Poisson problem `−Δw = ∇·F` whose coefficient is the identity
(`isEllipticFieldOn_one`), so the elliptic-coefficient field of Section 2 never
enters the response map.  Continuity of the solution map in the *coefficient*
is therefore not needed anywhere, and is not used.

## Main results

* `measurable_gradToHilbertVectorL2_of_isDirichletResponse`: the obligation
  holds, for *every* selection, unconditionally.
* `measurable_vecCubeLpENorm_grad_of_isDirichletResponse`: the cube-energy
  conjunct of the Section 3 conclusions, strengthened from `AEStronglyMeasurable`
  to `Measurable` and freed of the measure.

## Consumers

* The proof of `l.LHS.term1` takes the cube energy of the Dirichlet selection
  from `aestronglyMeasurable_vecCubeLpENorm_grad`, and the Neumann twin `hNmeas`
  of its sandwich route from
  `aesm_vecCubeLpENorm_grad_neumann_of_fluxFormula`, unconditionally.
* The two response-gradient conjuncts of the residue `hData` of the final
  assembly of Section 3 — the `AEStronglyMeasurable` cube-energy
  maps of the Dirichlet and the Neumann selection — are the only conjuncts of
  that residue that are discharged *already*: a proof of `hData` may take
  `w := dirichletResponse` and discharge them by
  `aestronglyMeasurable_vecCubeLpENorm_grad` (and its Neumann twin), leaving
  the scale data, the realization block and the term residues as the content.
* The term-3 pairing and integrability chain reads the response through
  `measurable_gradToHilbertVectorL2_dirichletResponse`.

This module adds no hypothesis to any of them; it supplies the class-level,
selection-free statement and the measure-free `Measurable` energy.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The obligation is one and the same for every selection -/

section Family

variable [NeZero d] {LPrime ellPrime m : ℕ} {p : Vec d}

/-- **The canonical Dirichlet response has a measurable weak-gradient class, and
so does every selection.**  No hypothesis beyond the anchors' own `_hw` binder:
the response is the continuous solution operator applied to the measurable flux
class. -/
theorem measurable_gradToHilbertVectorL2_of_isDirichletResponse
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    Measurable (fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2) := by
  have hfun : (fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2) =
      fun omega : ShellSeq d => cubeDirichletGradClass (originCube d (m : ℤ))
        (toHilbertVectorL2OfVecField
          (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)) :=
    funext fun omega =>
      gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse omega (hw omega)
  rw [hfun]
  exact (continuous_cubeDirichletGradClass (originCube d (m : ℤ))).measurable.comp
    (measurable_toHilbertVectorL2OfVecField_dirichletRhsField LPrime ellPrime m p)

end Family

/-! ## The obligation for an arbitrary flux family

The same statement with the concrete flux of `e.def.w` replaced by an arbitrary
square-integrable family whose `L²` class is measurable in the sample.  This is
the form in which the obligation is independent of the Section 3 scale data. -/

section GeneralFlux

variable [NeZero d] {Q : TriadicCube d} {F : ShellSeq d → Vec d → Vec d}

end GeneralFlux

/-! ## The obligation on the `σ`-algebra `F_>` of the printed sentence

`F_> = σ(j_r : r > ℓ)` is generated by the shells strictly
above the proxy cutoff `ℓ`.  The flux `(k_{L'} − k_{ℓ'}) p` is the shell
increment over `(ℓ', L']`, so it reads only shells `r > ℓ` whenever `ℓ ≤ ℓ'`,
and its class is measurable for that smaller `σ`-algebra; the solution operator
being continuous, so is the response's gradient class. -/

section SubSigma

variable [NeZero d] {ell ellPrime LPrime m : ℕ} {p : Vec d}

end SubSigma

/-! ## The cube-energy conjunct of the Section 3 conclusions

The conclusions of Section 3 (`l.LHS.term1`, and the response-gradient
conjuncts assembled in the final assembly) read the response
through the normalized cube `L̲²` norm of its weak gradient, which is a fixed
constant multiple of the `enorm` of the gradient class
(`vecCubeLpENorm_grad_eq_enorm_gradToHilbertVectorL2`).  At the class-level
statement above this gives the `Measurable` form, for every selection and with no
measure. -/

section Energy

variable [NeZero d] {LPrime ellPrime m : ℕ} {p : Vec d}

/-- **The cube-energy map of any Dirichlet response of `e.def.w` is measurable
in the sample.**  This is the `AEStronglyMeasurable` conjunct of the Section 3
conclusions, strengthened to measurability and stated without a measure. -/
theorem measurable_vecCubeLpENorm_grad_of_isDirichletResponse
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    Measurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) := by
  have hfun : (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal ((cubeVolume (originCube d (m : ℤ)))⁻¹) ^
            ((1 : ENNReal) / 2).toReal *
          ‖(w omega).toH1Function.gradToHilbertVectorL2‖ₑ :=
    funext fun omega => vecCubeLpENorm_grad_eq_enorm_gradToHilbertVectorL2 _
  rw [hfun]
  exact (continuous_enorm.measurable.comp
    (measurable_gradToHilbertVectorL2_of_isDirichletResponse hw)).const_mul _

end Energy

end

end SuperdiffusionCLT.Section3.Setup
