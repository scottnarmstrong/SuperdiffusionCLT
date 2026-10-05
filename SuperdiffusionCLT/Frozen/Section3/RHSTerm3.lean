/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Closed
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section3.Setup.Parameters

@[expose] public section

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

/-- **Lemma `l.RHS.term3`** (`e.RHS.term3`): the printed display is, with `⨍` the cube
average over `cu_m = originCube d S.m`, `a_{L'}` the infrared cutoff of the coefficient field
at the enlarged scale `L'`, and `∇u_m`, `∇u_n` the glued gradient fields of
`e.u.k.def`:

> `E [ ⨍_{cu_m} ∇w · a_{L'} (∇u_m − ∇u_n) ]`
>   `≤ C (δ + η_L)^{1/2} ( (L'−ℓ)² σ̄_{L',*}^{-1}(cu_n)² + σ̄_ℓ(cu_n)² )^{1/2}`
>   `+ C ν^{-4} (L')⁴ ( 3^{−(ℓ'−n)/2} + 3^{−(ℓ−n)/8} + 3^{−(ℓ'−ℓ)/4} + 3^{−h/8} )`.

The proof splits the left side by `e.additivity.defect.splitting` and estimates the two parts in
Step 1 (`e.RHS.term3.B`) and Steps 2-3 (`e.RHS.term3.A` and `e.bL.to.bhomell`); Step 4
combines them.

The one constant `C(d) < ∞` of the printed statement is quantified **before**
every piece of section data, exactly as the paper scopes it: the paper fixes the
dimension and then asserts the inequality with a single `C(d)` shared by both
groups, with `δ` and `η_L` among the quantified data, not among the dependencies
of the constant.  A statement that quantifies the constant after `ν`, `P`, `S`,
`e`, `p`, `w` or the glued fields is vacuous — a finite left-hand side always
admits some constant.

Readings this text fixes:

* **Corrections of the printed text.**  The statement carries the corrected forms of two
  items (see `ERRATA.md`).
  (i) The rate: the printed `3^{-h/8}` is `3^{-h/16}` — the
  square root of the third polynomial term of `e.bL.to.bhomell`
  (`3^{-h/8}`) is `3^{-h/16}`, and `3^{-h/16} ≤ C 3^{-h/8}` fails for every
  `h`-independent `C`.
  (ii) The absorption: the
  `(δ + η_L)^{1/2}` that the contribution of `e.RHS.term3.B` carries in the proof is
  recorded explicitly as the factor `1 + (δ + η_L)^{1/2}` of the second group
  instead of being absorbed into the constant.  With `C` quantified first the
  absorption is not merely silent but impossible: `(δ + η_L)^{1/2}` is
  unbounded section data, so the corrected second group must carry the factor.
  The signed Hölder decomposition in the proof is a proof correction
  only and does not touch the statement.
* **Constant scope.**  `∃ C : ℝ, 1 ≤ C ∧ ∀ …`: the constant is chosen before
  `ν`, the law `P`, the shell laws, the scale selection `S`, the test vector
  `e`, `δ` and `η_L`, and the response `w`.  The bound `1 ≤ C` is the
  normalization of the printed `C(d) < ∞` (the constant may be
  increased to `1`); no dependence of `C` on any section datum is asserted or
  denied beyond that.
* **Carrier for `E [·]`.**  The expectation is the integral against
  `P.toMeasure` of `P : ProbabilityMeasure (ShellSeq d)`; the shell is
  `ShellSeq d` and the standing shell laws are `ShellLawPrefix`, `ShellLawJ1Restriction`
  (the restriction version),
  `ShellLawJ2`, `ShellLawJ3` and `ShellLawJ4`.  `ShellLawJ5` is NOT carried:
  the printed proof invokes `a.j.frd`, `a.j.indy` and the
  balanced and one-sided comparisons, but never the nondegeneracy law
  `a.j.nondeg`.
* **Carrier for `⨍_{cu_m}`.**  The cube average is `volumeAverage` on the open
  cube `openCubeSet (originCube d (S.m : ℤ))`, as in the response-field
  statements.
* **Carrier for `a_{L'}`.**  The cutoff field
  `SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega S.LPrime`
  (`a_{L'} = ν Id + κ_{L'}`), applied through `.toCoeffField`.
* **The glued fields are DEFINED, not free.**  `∇u_m` and `∇u_n` are the
  instances of `e.u.k.def` (see `Section3/Terms/GluedField.lean`),
  `SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu S.LPrime S.m S.m
  (fluxSlot nu S.LPrime P S.n e) omega` and
  `… S.n S.m (fluxSlot nu S.LPrime P S.n e) omega`, with the flux slot
  `Q = σ̄_{L',*}^{1/2}(cu_n) e` of `e.u.k.y.def` (`fluxSlot`).  Binding `∇u_m`, `∇u_n` as free data
  would make the statement FALSE (scale either field by a large constant), while the paper
  defines them; the carrier is the definition of exactly that.
* **The response `w` is a binder with its defining datum.**  `w` is carried as a
  binder over `H10Function (openCubeSet (originCube d (S.m : ℤ)))` together with
  `e.def.w`'s defining predicate `IsDirichletResponse omega S.LPrime S.ellPrime
  S.m p (w omega)`, `p = testVector nu S.LPrime P S.n e` being the substituted
  first half of `e.Sec3.p.q.def` (the paper defines `p`, so no `p` binder is
  carried).  As in the response-field statements, the response is a binder
  because its uniqueness and `H²(cu_m)` regularity are not assumed; no carried estimate or
  conclusion about `w` is assumed.
* **`δ` and `η_L` are nonnegative reals.**  The paper fixes `δ = c₀ c⋆²`
  and `η_L = C ν^{-5} L 3^{-(L'-m)}` with constants
  `c₀`, `C` whose values the proof selects; the lemma uses them only through
  `(δ + η_L)^{1/2}`, so the statement carries `0 ≤ δ`, `0 ≤ η_L`, the smallness hypothesis
  and the bound on `η_L` described below, and nothing else.
* **Hypothesis discipline.**  The hypotheses are the standing shell laws,
  `0 < ν ≤ 1` (the standing assumption ν ∈ (0,1]), the
  scale-selection ordering `ScalesOrdering S` (`e.scales.ordering`), the unit
  vector `|e| = 1`, the nonnegativity of `δ` and `η_L`, the defining
  predicate of `w`, and the scale and parameter hypotheses described below.  NO integrability or
  measurability side condition, NO
  carried estimate (`e.RHS.term3.B`, `e.RHS.term3.A`, `e.bL.to.bhomell`,
  `e.nablaw.Lt`, `e.secondvar`, `e.pigeon.scalar`, `e.blupbounds` and the
  Hölder split are inputs of the proof, not premises of the statement), NO
  conclusion of another lemma, and NO carrier of the proof's own scale `k = ⌈(4/(d+4))ℓ'
  + (d/(d+4))ℓ⌉` (Step 2): `k` names no object of the display.
* **Exponents.**  Every printed triadic power is a real power: `3^{-(ℓ'-n)/2}`,
  `3^{-(ℓ-n)/8}`, `3^{-(ℓ'-ℓ)/4}`, `3^{-h/16}` and the envelope
  `ν^{-4}(L')⁴` with `(L')⁴ = ((S.LPrime : ℕ) : ℝ)^(4:ℕ)`; the half powers are
  `Real.rpow` with exponent `(1:ℝ)/2` and `Real.sqrt`.  The scale data
  `σ̄_{L',*}^{-1}(cu_n)` and `σ̄_ℓ(cu_n)` are the
  sequences `sigmaBarStarInvSeq` and `sigmaBarSeq` on the origin cubes.

The binder `_hOffsetLower` is the lower bound `K log(ν⁻¹L) ≤ a` at the printed constant
`K = 8056 / log 3`. The printed scale selection `e.scale.selection`
fixes `a = ⌈K log(ν⁻¹L)⌉`, and the pigeonhole step `e.pigeon.scalar`
consumes that datum; the four scale binders
(`ScalesOrdering S`, `2h ≤ m`, `100a ≤ h`, `h + 1 ≤ 3^a`) provably do NOT imply
it, since they hold both at `ScaleSelection.ofBase 1213 1200 600 6` and at
`(L, m, h, a) = (4·10⁷, 3·10⁷, 1.5·10⁷, 150000)` with `ν = 1`, where the printed identity for
`a` fails.

The binder is the printed identity's LOWER BOUND rather than the identity
itself, because that is all the proof consumes: the identity implies it,
and the whole pigeonhole chain factors through it.

The binder `_hPigeonScalar` is the printed pigeonhole scalar conjunct `e.pigeon.scalar` at the
cutoff-`L` analogue of the pigeonhole range:
`σ̄*⁻¹_L(cu_{m-2h}) ≤ (1 + δ) σ̄*⁻¹_L(cu_m)`. The printed lemma `l.RHS.term3` is
stated in the standing context of the pigeonhole-SELECTED scales, where this
holds by `e.pigeon.matrix`; quantifying over all admissible
scale selections would allow it to fail -- the ordering supplies only the
opposite inequality (`antitone_sigmaBarStarInvSeq`), and at `δ = 0` the datum is
equivalent to the equality `σ̄*(m-2h) = σ̄*(m)`. The consumer supplies it: the
root assembly chooses its scale selection by the pigeonhole, and the `e.pigeon.matrix`
development (`Section3/Setup/Pigeonhole.lean`) produces the datum there.

The binders `_hDeltaEtaLeOne` and `_hEtaL` treat `δ` and `η_L` as the specific quantities of the
printed lemma, not free parameters: `δ = c₀c⋆²` with `c₀` small and `c⋆ ≤ 2`, and
`η_L = Cν⁻⁵L3^{-(L'-m)}`, the cost of moving the cutoff from `L` to `L'` in
`e.pigeon.scalar`. The proof uses a bounded `δ + η_L` (it absorbs `1 + δ + η_L` into `C`) and
uses `η_L` as that cutoff-move cost.
* `_hDeltaEtaLeOne : delta + etaL ≤ 1` is the printed smallness premise.
* `_hEtaL` is the definition of `η_L` relaxed from `=` to `≤`, written with
  the statement's own constant `C` (a larger `C` strengthens the hypothesis and
  weakens the conclusion, so this is equivalent to a separate constant). -/
theorem SuperdiffusionCLT.Frozen.Section3.rhs_term3_constFirst
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
        (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
        (_hOffsetLower :
          (8056 / Real.log 3) * Real.log (nu⁻¹ * ((S.L : ℕ) : ℝ)) ≤ ((S.a : ℕ) : ℝ))
        (e : Vec d) (_he : vecNormSq e = 1)
        (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL)
        (_hPigeonScalar : sigmaBarStarInvSeq nu S.L P (S.m - 2 * S.h) ≤
          (1 + delta) * sigmaBarStarInvSeq nu S.L P S.m)
        (_hDeltaEtaLeOne : delta + etaL ≤ 1)
        (_hEtaL : C * nu ^ (-(5 : ℝ)) * ((S.L : ℕ) : ℝ) *
            (3 : ℝ) ^ (-(((S.LPrime - S.m : ℕ) : ℝ))) ≤ etaL)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)),
        ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot ((w omega).toH1Function.grad y)
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu
                      S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega y -
                    SuperdiffusionCLT.Section3.Terms.gluedGradientField hnu
                      S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega y)))
          ∂P.toMeasure ≤
          C * (delta + etaL) ^ ((1 : ℝ) / 2) *
            Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) *
                (sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) +
              (sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) +
          C * (1 + (delta + etaL) ^ ((1 : ℝ) / 2)) * nu ^ (-(4 : ℝ)) *
            (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
            ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
              (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
              (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 16)))
    := by
  exact SuperdiffusionCLT.Section3.Terms.rhsTerm3_closed d hd
