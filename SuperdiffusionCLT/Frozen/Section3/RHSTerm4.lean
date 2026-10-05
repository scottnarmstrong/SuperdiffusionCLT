/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB

@[expose] public section

open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup

/-- **Lemma `l.RHS.term4`**, the fourth and final right-side term of the
separation display `e.ellsep.testing`, display `e.RHS.term4`:

```
| E[ p · ⨍_{cu_m} (κ_{ℓ'} − κ_ℓ) ∇w ] | ≤ C śhom_{L',*}^{-1}(cu_n) .
```

The scales `m, n, ℓ, ℓ', L'` are the auxiliary scales of the proof of
Proposition `p.sstar.lower.bound` fixed by `e.scale.selection` under the ordering
`e.scales.ordering`; `p` is the first half of `e.Sec3.p.q.def`,
`p = śhom_{L',*}^{-1/2}(cu_n) e` with `e` a unit vector; `w` is the Dirichlet response
`e.def.w`; `κ_j` is the infrared stream cutoff at scale `j`; and
`śhom_{L',*}^{-1}(cu_n)` is the annealed lower-right block on the origin cube
`cu_n` at cutoff `L'`.

The constant `C(d)` is quantified **before** every piece of section data —
before `nu`, the law `P`, the scale selection `S`, the direction `e`, the test
vector `p` and the response `w` — exactly as the paper's `C(d)` is: a
statement that quantifies the constant after the section data is vacuous, the
left-hand side being a finite real number. The `1 ≤ C` normalization is the
constant-first convention (`C` may be replaced by `max 1 C`, so the
added lower bound is free).

Readings this text fixes:

* **Constant scope.** `C : ℝ` with `1 ≤ C`; it depends on nothing but the
  ambient dimension (no dependence on `ν`, on the law, on the scale selection,
  on `e`, on `p` or on `w`).
* **Standing shell laws.** `ShellLawPrefix`, `ShellLawJ1Restriction` (the restriction
  version), `ShellLawJ2`, `ShellLawJ3`, `ShellLawJ4`. `ShellLawJ5` is **not**
  bound: the printed proof of this lemma does not use it, and no estimate appears
  among the hypotheses.
* **No carried estimates.** The printed proof consumes three estimates — the
  `W^{-1/2,2}` estimate `e.kmn.Wminussp` (clause (a) of
  `l.ellip.k.scales.estimates` instantiated at `s = 1/2`,
  `p = 2`, the cube `cu_m` and the shells `(ℓ, ℓ')`), the fractional
  `H̲^{1/2}` clause of `e.nablaw.Lt`, and the pointwise
  fractional duality — but none of them appears in the
  display, so none is a hypothesis here: the display is stateable without
  them. (This differs from `Section3/Terms/RHSTerm4V3.l_RHS_term4_v3`, whose hypothesis
  list carries them, with the closing constant `4 C₁ C₂`.)
* **`p`** is `e.Sec3.p.q.def` in the carrier
  `SuperdiffusionCLT.Section3.Setup.testVector`, with a unit direction
  `e`; `|p|² = śhom_{L',*}^{-1}(cu_n)` is
  `vecNormSq_testVector`, the closing identity of the proof.
* **`w`** is `e.def.w` rendered as `IsDirichletResponse`: the `H¹₀` response
  on the open cube to the flux field `(κ_{L'} − κ_{ℓ'}) p`. Its existence,
  uniqueness and `H²(cu_m)` regularity are **not** assumed here.
* **`κ_j`** is the infrared stream cutoff `streamCutoff omega j`, a global
  matrix field on `Vec d`; the pairing `p · (κ_{ℓ'} − κ_ℓ) ∇w` is
  `vecDot p (matVecMul (streamCutoff ω ℓ' − streamCutoff ω ℓ) (∇w))`.
* **The cube average `⨍_{cu_m}`** is `volumeAverage` over the **open** cube
  `openCubeSet (originCube d S.m)`, the cube on which the response and its
  gradient live; this is the interchangeability reading of the spaces on the
  open cube and the averages on the half-open cube recorded for
  `responseFields_apriori_orderOne`, the two cubes differing
  only by a null boundary.
* **The right-hand side `śhom_{L',*}^{-1}(cu_n)`** is the sequence
  `SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq
  nu S.LPrime P S.n`, the annealed lower-right block on the origin cube `cu_n`
  at cutoff `L'` (`e.homs.defs`), scalar by `J4`. Under the shell laws it
  equals the square `(sigmaBarStarInvSqrt nu S.LPrime P S.n)²` by
  `sq_sigmaBarStarInvSqrt`, the form in which the chain is closed
  against `|p|²`; the direct carrier is used because it is what the display
  names.
* **The expectation `E[·]`** is the `P`-integral over the shell-sequence
  carrier `ShellSeq d`. No measurability hypothesis is imposed, the paper
  stating none; for a response field that is not measurable in `omega` the
  printed left-hand side is `0` (Mathlib's total integral), so the intended
  application supplies a measurable response field.
* **`0 < ν` and `ν ≤ 1`** are the standing range of the molecular diffusivity; they are not
  used by the display and are carried only as the section's standing data.
* **Corrections of the printed text.** None of the corrections of the printed text
  (see `ERRATA.md`) amends this statement: they touch
  the first and third terms, the Section 2 endpoint and smaller items
  of the Section 3 bookkeeping, none of which enters the display or its proof
  (the proof's sources `e.kmn.Wminussp`, `e.nablaw.Lt` and
  `e.Sec3.p.q.def` are untouched by all of them). The order-one hatted vector
  norm is not invoked here because no norm appears in the display — the norms live
  inside the estimates the proof consumes.
* **`2 ≤ d`** is standing; the display uses it only through the constant, and
  the binder is spelled `_hd`, as is
  every hypothesis binder that later parts of the statement do not mention.
  The quantifier order after `∃ C` is the section's data order: `ν`, the law,
  the scale selection with its ordering, the direction, the test vector, the
  response. -/
theorem SuperdiffusionCLT.Frozen.Section3.rhs_term4_constFirst
    (d : ℕ) [NeZero d] (_hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
          ∂P.toMeasure| ≤
          C * SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq
            nu S.LPrime P S.n
    := by
  obtain ⟨C, hC1, hmain⟩ :=
    SuperdiffusionCLT.Section3.ResponseFields.l_RHS_term4_of_window d _hd
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
  rw [← sq_sigmaBarStarInvSqrt hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n]
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw