/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Section3.Terms.Term12Statements
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section3.Terms.GluedField

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

/-- **Lemma `l.RHS.term2`**,
the display `e.RHS.term2`:

> There exists `C(d) < ∞` such that, for the scales selected in
> `e.scale.selection`,
> `|E[ avsum_{z ∈ 3^n ℤ^d ∩ cu_m} ⨍_{z+cu_n} ∇w · (k_{L'} − k_ℓ)(∇u_{n,z} − p) ]|`
> `≤ C ν^{-3} (L')^2 3^{-(ℓ-n)/2}`.

The constant comes **first**: one `C(d)`, quantified before `nu`, the shell law,
the scale selection, the unit vector and the Dirichlet response, so that the
display is asserted for every admissible choice of the section data against one
shared `C ≥ 1`.  A statement that quantifies the data before `C` is degenerate:
for one fixed choice of the data the left side is a fixed nonnegative real and
the right coefficient `nu^{-3}(L')^2 3^{-(ℓ-n)/2}` is a fixed positive real, so
some large enough `C` always exists.

Readings this text fixes:

* **Carriers.**  `k_L` is the infrared cutoff
  `SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L`,
  so the printed `k_{L'} − k_ℓ` is the
  difference of the two cutoff coefficient fields at `L'` and `ℓ` — the common
  summand `ν Id` cancels, which is the only place the molecular diffusivity
  enters the integrand.  `∇u_{n,z}` is the glued field of `e.u.k.def` at the flux slot of
  `e.u.k.y.def`:
  `gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)`,
  the gluing of the canonical maximizers
  `v_{L'}(·, z + cu_n, 0, shom_{L',*}^{1/2}(cu_n) e)` over the scale-`n`
  sub-cubes of `cu_m`; on each integration cube `z` it agrees pointwise with
  `∇u_{n,z}` by `gluedGradientField_apply_of_mem_openCubeSet`, which is exactly
  the printed remark "except on subdomains of a single cube of the form `z + cu_k`".
  `p` is the first half of `e.Sec3.p.q.def`,
  `p = shom_{L',*}^{-1/2}(cu_n) e`, namely `testVector`, written inline in
  the display rather than bound as a separate vector variable.
* **The averages.**  `avsum_{z ∈ 3^n ℤ^d ∩ cu_m}` is the lattice average over
  the scale-`n` sub-cube family `largeCubeSubcubes d S.n S.m` of `cu_m`, whose
  centres are exactly the lattice points `3^n ℤ^d ∩ cu_m`, normalised by the
  cardinality; `⨍_{z+cu_n}` is `volumeAverage` on the half-open realization
  `openCubeSet z` of the translated cube; `E` is the integral against the
  annealed measure `P.toMeasure`.
* **The scales.**  "for the scales selected in `e.scale.selection`"
  is the quantification over `S : ScaleSelection` with the
  ordering `e.scales.ordering` as `ScalesOrdering S`; the
  exponents of the printed right side are the `ℕ` differences `S.LPrime` and
  `S.ell - S.n` of the carrier.
* **The Dirichlet response.**  `w` is the solution of `e.def.w`,
  `−Δw = (f_{L'} − f_{ℓ'})·p` in `cu_m` with zero boundary
  values, bound by the predicate
  `SuperdiffusionCLT.Section3.Setup.IsDirichletResponse` at the test
  vector `p = testVector nu S.LPrime P S.n e`, i.e. the
  `IsCubeDirichletResponse` of the flux field `(k_{L'} − k_{ℓ'}) p` on the open
  cube.  Existence, uniqueness and the
  `H²(cu_m)` regularity are not assumed, so the predicate is carried instead of an existence
  hypothesis, and `w` is quantified over every field satisfying it.  The
  predicate is the *definition* of the named object `∇w`, not a carried
  estimate.
* **The unit vector.**  `e` has `|e| = 1`, carried as
  `vecNormSq e = 1`.
* **Quantifier order and constant scope.**  `d`, `[NeZero d]` and the standing
  `2 ≤ d` precede `∃ C`; everything else — `nu` with `0 < nu ≤ 1`, the shell
  law, the scale selection, `e`, `w` — is inside `1 ≤ C ∧ ∀ …`.  The one
  constant is shared over all choices; the paper gives no per-instance
  constant.
* **Shell laws.**  The printed proof uses the standing shell
  law (stationarity), `a.j.reg` (J3) and the `σ(j_r : r ≤ ℓ)` /
  `F_>` decoupling, which is `a.j.indy` (J2), and it runs the
  localization device of `l.RHS.term1`, which binds `ShellLawJ1Restriction`
  (`a.j.frd`); the dihedral law J4 is standing.  `a.j.nondeg` (J5) is not
  invoked, so `ShellLawJ5` is **not** a hypothesis.
* **No proof-side data.**  The three displays
  `e.RHS.term2.R.bounds`, `e.RHS.term2.proxy.error`, `e.RHS.term2.proxy.energy`
  and the two steps of the localization device (the per-cube Poincaré
  inequality and the decoupling identity) are inputs of the printed proof,
  not part of the statement; none of them, and
  no integrability, finiteness, measurability or weak-gradient datum, is
  carried here.
* **Corrections of the printed text.**  None changes this display: the corrected step display
  in the proof of `l.RHS.term1` is not used by the proof of
  `l.RHS.term2`; the order-one carrier of the hatted vector norm governs a hatted
  negative norm, which does not occur in `e.RHS.term2`; the other corrections
  concern `l.RHS.term3` and other displays.  The statement is exactly the
  printed one. -/
theorem SuperdiffusionCLT.Frozen.Section3.rhs_term2
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        testVector nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2))
    := by
  exact SuperdiffusionCLT.Section3.Terms.rhs_term2_statement d hd
