/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section3.Terms.Term12Statements
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums

/-- **Lemma `l.RHS.term1`** (`e.RHS.term1`): there is a constant
`C(d) < ∞` such that

`|E[ ⨍_{cu_m} ∇w · (a_ℓ ∇u_n − q) ]| ≤ C ν^{-3} ℓ² h (3^{-(ℓ-n)/2} + 3^{-(ℓ'-ℓ)})`.

The display is the first term on the right side of `e.ellsep.testing`; it is estimated here
for the scale selection `e.scale.selection`, the unit vector `e`, and the section objects
`p`, `∇u_n`, `q` and `w` of `e.Sec3.p.q.def`, `e.u.k.def` and `e.def.w`.

The paper's `C(d)` is quantified **before** every piece of section data —
before `ν`, the law `P`, the five standing shell laws, the scale selection, the
unit direction `e`, the Dirichlet response `w` and the pigeonhole
comparability — exactly as the printed "There exists a constant `C(d) < ∞`
such that" reads: the constant is chosen for the whole section at once, not for
one shell, one scale selection or one response.  Only the ambient dimension `d`
(with its nonvanishing instance and the standing `2 ≤ d`) precedes the `∃ C`.

Readings this text fixes:

* **Constant scope.** `∃ C : ℝ, 1 ≤ C ∧ ∀ …`: the constant is a real number
  chosen first, with the normalization `1 ≤ C` (a smaller constant is
  divided away; this keeps the statement from being witnessed by `C = 0` on a
  vacuous branch), shared by no other lemma and quantified over nothing but the
  section data listed above.  The `d` in the printed `C(d)` is the ambient
  dimension of every carrier; no other dependence is permitted.
* **The response `w`.**  `w : ShellSeq d → H¹₀(cu_m)` is the Dirichlet response
  of `e.def.w` for the flux `(k_{L'} − k_{ℓ'}) p` in `cu_m`:
  the carrier is the predicate
  `SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime
  S.ellPrime S.m p (w omega)` at the printed test vector `p`; `∇w` in the
  display is `w.toH1Function.grad`.  Existence, uniqueness and the printed
  `H²(cu_m)` regularity are not assumed here: the statement quantifies over every `w` satisfying
  the defining weak-form condition, which is the minimum datum without which the
  display cannot even be stated.
* **`p` and the flux slot.**  The printed `p = shom_{L',*}^{-1/2}(cu_n) e`
  (first half of `e.Sec3.p.q.def`) is the definition
  `testVector nu S.LPrime P S.n e`; the display does not name `p`, so it enters
  the statement only inside the response condition.  The flux slot
  `Q = shom_{L',*}^{1/2}(cu_n) e` of `e.u.k.y.def` is
  `fluxSlot nu S.LPrime P S.n e`.
* **`∇u_n` and `q`.**  The glued maximizer field of `e.u.k.def` at cutoff `L'`
  and scale `n` is the definition
  `SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.n
  S.m (fluxSlot nu S.LPrime P S.n e)`, and `q` of the second half of
  `e.Sec3.p.q.def` is `SuperdiffusionCLT.Section3.Terms.qVector hnu P
  S.LPrime S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`; both are read as the
  paper defines them, not as free binders.
* **`a_ℓ` and the averages.**  `a_ℓ` is the infrared cutoff
  `coefficientCutoff nu omega S.ell` of the marginal coefficient field;
  `⨍_{cu_m}` is `volumeAverage` on the open cube
  `openCubeSet (originCube d (S.m : ℤ))`, and `E` is the Bochner integral
  against `P.toMeasure`.
* **Standing data.**  `0 < ν ≤ 1`; the five standing shell laws
  `ShellLawPrefix`, `ShellLawJ1Restriction`, `ShellLawJ2`, `ShellLawJ3`, `ShellLawJ4`
  (`ShellLawJ5` is not carried: the printed proof never uses
  the nondegeneracy assumption `a.j.nondeg`); the scale selection
  `S : ScaleSelection` of `e.scale.selection` with `ScalesOrdering S`
  (`e.scales.ordering`); and the pigeonhole comparability `2 * S.h ≤ S.m`,
  which `ScaleSelection` and `ScalesOrdering` do not imply and on
  which the closing coarsening of the printed proof (`m ≤ Cℓ` and
  `m − ℓ ≤ 2h`) rests — this is the standing data of the pigeonhole selection of
  `m`, not a lemma hypothesis.
* **No side conditions.**  No integrability, measurability or `L²`-membership
  hypothesis is carried: the Bochner integral and the cube average are total, so
  the display is statable without them.
* **Corrections of the printed text.**  None changes the displayed statement.  The step display
  `e.decompose.flux.u.n.second` inside the printed proof holds with the weaker rate
  `C ν^{-1} (ℓm)^{1/2} (m−ℓ) 3^{-(ℓ'−ℓ)}` (see `ERRATA.md`); the statement
  `e.RHS.term1` is unchanged because the Step 3 coarsening of the printed proof
  absorbs the extra factor into `ν^{-3} ℓ² h`.
  The order-one vector hatted negative norm also affects only the printed proof, through the
  hatted-negative-norm duality of Step 2; the hatted norm does not appear in the display of
  `e.RHS.term1`.
* **Spellings.**  The rate factors are read off the display exactly as printed:
  `3^{-1/2(ℓ-n)}` at `3 ^ (-((S.ell - S.n : ℕ) : ℝ) / 2)` and `3^{-(ℓ'-ℓ)}` at
  `3 ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))`, with `ν^{-3} ℓ² h` the product
  `nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ 2 * (S.h : ℝ))` — the same spellings as the
  other term statements. -/
theorem SuperdiffusionCLT.Frozen.Section3.rhs_term1
    (d : ℕ) [NeZero d] (_hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega))
        (_hPigeon : 2 * S.h ≤ S.m),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                  qVector hnu P S.LPrime S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
            ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ)))
    := by
  exact SuperdiffusionCLT.Section3.Terms.rhs_term1_statement d _hd
