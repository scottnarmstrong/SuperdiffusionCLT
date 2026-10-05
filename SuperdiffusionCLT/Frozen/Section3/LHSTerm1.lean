/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Probability.LHSTerm1Closing
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

@[expose] public section

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

/-- **Lemma `l.LHS.term1`**: the lower bound `e.nabla.w.lower.bound` for the left-hand
side of the four-term decomposition `e.ellsep.testing`.  The printed statement is:

```
There exists C(d) < ∞ such that

    | E[ ⨍_{cu_m} |∇w|² ] − (log 3) c⋆ (m−n) |p|² |
        ≤ (C(1 + L' − m) + Ȧ) |p|² .                    (e.nabla.w.lower.bound)
```

Here `w = w_{D,𝐅}^{(m)}` is the Dirichlet response on `cu_m`
associated, as in `l.abstract.response.fields` with `M = m`, with the glued
flux `𝐅 = (κ_{L'} − κ_{ℓ'})p`; this is the function `w` of
`e.def.w`.

The single printed constant, truncated below at `1`, is quantified BEFORE every piece of
Section 3 data: the viscosity `nu`, the shell law `P`, the standing shell laws, the two
non-degeneracy constants `c⋆` and `Ȧ` of `a.j.nondeg`, the scale selection, the
unit direction `e`, the test vector `p`, the glued flux `𝐅` and the response
field `w`.  A statement that instead fixes the data first and then asks for
`C` is vacuous, since a finite left-hand side always admits some constant.

Readings this text fixes:

* **Carriers.** `|p|²` is the Euclidean squared norm
  `Homogenization.vecNormSq`; `⨍_{cu_m} |∇w|²` is
  `vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (∇w)²` — the volume-normalized
  `L̲²` norm of the gradient read in the `HilbertVec` carrier, i.e. the Euclidean
  magnitude on the half-open cube — squared; `E` is the `∫⁻`
  against `P.toMeasure`, read as a real number by `.toReal`.  The response lives
  on the open cube `openCubeSet (originCube d (S.m : ℤ))` (the domain on which
  the solvability inputs hold) while the norm is taken on the half-open cube,
  the two interchangeable by the measure-identity lemmas.  `w` is
  quantified over every realization of the Dirichlet response predicate, the
  print's `w_{D,𝐅}^{(m)}` being the function `w` of `e.def.w`: the carrier does not select a
  solution.
* **The two printed constants `c⋆` and `Ȧ`.** `Ȧ` is the paper's
  `\nondegconst` (`\breve{A}`) of assumption `a.j.nondeg`; `c⋆` is its `c⋆`.  They enter as the
  two parameters of `ShellLawJ5 d P cStar K`, and `ShellLawJ5` is a hypothesis of this
  statement because the printed proof consumes `a.j.nondeg`
  (`e.use.nondeg.ass`).  In the conclusion the summand `Ȧ` is the `K` of that
  structure.
* **Scales.** `S : ScaleSelection` is `e.scale.selection` and
  `ScalesOrdering S` is `e.scales.ordering`; the proof uses
  the scale identities `L' − ℓ' = m − n`.  `(m−n)` and `(1 + L'−m)`
  are the truncated natural differences, faithful under the ordering.
* **`p` and `e`.** `p` is the test vector of `e.Sec3.p.q.def`,
  `p = shom_{L',*}^{-1/2}(cu_n) e = testVector nu S.LPrime P S.n e`; the
  direction `e` is unit, carried in both carriers
  (`vecNormSq e = 1` and `Book.Ch02.vecNorm e = 1`), the first for the identity
  `|p|² = shom_{L',*}^{-1}(cu_n)` and the second to instantiate `ShellLawJ5`'s
  clause at `e`.
* **Shell laws.** The standing package `ShellLawPrefix` (the paper-wide
  dimension condition and the standing stationarity), `ShellLawJ1Restriction` (the
  restriction version),
  `ShellLawJ2`, `ShellLawJ3` and `ShellLawJ4`, plus `ShellLawJ5` as above.  The
  `VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure` instance is NOT a hypothesis here: it
  is derivable from the prefix and J2
  (`ShellField.vaddInvariantMeasure`).
* **No side conditions.** The statement carries no
  measurability, integrability or carried-estimate hypotheses:
  the display is stated with the raw `∫⁻`, which is defined without measurability.
* **Quantifier order.** `∃ C : ℝ, 1 ≤ C ∧ ∀ …`: the constant is shared by no
  other display and depends on nothing but `d` (`C(d) < ∞`).
* **Corrections of the printed text.** None changes this display.  The corrected prefactor
  `1 + (l−k)` of `e.jk.Hminus.endpoint` and the order-one vector hatted norm
  `vecHatNegENormOrderOne` (which replaces the printed "for instance" sentence in the paper's
  discussion of hatted norms; see `ERRATA.md`) concern the applied displays of the proof
  (`e.jk.Hminus.endpoint` and `e.abstract.response.ND.weak`), not the statement; their corrected
  forms are absorbed by the printed constant `C(d)`. -/
theorem SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P), ShellLawJ1Restriction d P →
          ∀ (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P), ShellLawJ4 d P →
          ∀ (cStar K : ℝ), ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ (S : ScaleSelection), ScalesOrdering S →
          ∀ (e : Vec d), Homogenization.vecNormSq e = 1 →
            Homogenization.Book.Ch02.vecNorm e = 1 →
            ∀ (p : Vec d), p = testVector nu S.LPrime P S.n e →
            ∀ (F : ShellSeq d → Vec d → Vec d),
              (∀ omega : ShellSeq d, F omega = fun x =>
                Homogenization.matVecMul
                  (SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.LPrime x -
                    SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.ellPrime x) p) →
              ∀ (w : ShellSeq d →
                  Homogenization.H10Function
                    (Homogenization.openCubeSet
                      (Homogenization.originCube d (S.m : ℤ)))),
                (∀ omega : ShellSeq d,
                  IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega)
                    (w omega)) →
                |(∫⁻ omega : ShellSeq d,
                      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                        (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                  ℝ≥0∞).toReal -
                  cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
                (C * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p
    := by exact SuperdiffusionCLT.Probability.Stationary.lhs_term1_closed d hd