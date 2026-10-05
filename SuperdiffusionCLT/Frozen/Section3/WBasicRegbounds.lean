/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import Homogenization.Book.Ch04.Theorems.Concentration
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB

@[expose] public section

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-- **Lemma `l.w.basic.regbounds`** (Section 3): there is a constant
`C(d) < ∞` such that the display `e.nablaw.Lt`
holds,

> `h^{-1/2}‖∇w‖_{L̲⁸(cu_m)} + 3^{ℓ'}‖∇²w‖_{L̲⁸(cu_m)}
>   + 3^{ℓ'/2}‖∇w‖_{H̲^{1/2}(cu_m)} ≤ O_{Γ₂}(C|p|)`,

where `w` is the Dirichlet response `e.def.w` of the flux
`F = (k_{L'} − k_{ℓ'})p` on `cu_m`, `p` is the test vector
`e.Sec3.p.q.def` and the scales are those of `e.scale.selection`. The printed proof ends with
"The identity `m − ℓ' = h` from `e.scale.selection` completes the proof", which is the field
`S.ellPrime_add_h` of the `ScaleSelection` package.

## The splitting of the display

The print states one `O_{Γ₂}` bound for a single sum of three weighted norms.
`O_{Γ₂}` is a tail relation on one random variable at a time and the three
weights `h^{-1/2}`, `3^{ℓ'}`, `3^{ℓ'/2}` are deterministic, so the statement
fixes the per-term rendering of the display: each of the three clauses is the
print's term with its weight moved into the amplitude,

* `‖∇w‖_{L̲⁸(cu_m)} ≤ O_{Γ₂}(C |p| h^{1/2})`,
* `‖∇²w‖_{L̲⁸(cu_m)} ≤ O_{Γ₂}(C |p| √(1+h) 3^{-ℓ'})`, and
* `‖∇w‖_{H̲^{1/2}(cu_m)} ≤ O_{Γ₂}(C |p| 3^{-ℓ'/2})`,

and the one constant `C` of the lemma is shared by all three clauses. A
statement carrying the weights on the left, with a single `O_{Γ₂}` bound for the
sum, is equivalent to the three clauses up to the `Γ₂` triangle constant, which
is a constant depending on `d` and is absorbed by `C`.

## Corrections of the printed text

* The amplitude of the second clause is `C |p| √(1+h) 3^{-ℓ'}`, not the printed
  `C |p| 3^{-ℓ'}` (a correction of the printed text; see `ERRATA.md`; the row
  `e.nabla.kmn.Linfty` on the large cube). The paper bounds the second parenthesized term of
  its proof on the large cube `cu_m`; for the shells `k < m` the
  gradient of `j_k` on `cu_m` is a union bound over the sub-cubes of scale `k`
  covering `cu_m`, and the honest amplitude loses the window factor `√(1+h)`.
  The factor is absorbed into the clause's conclusion rather than recorded as a
  hypothesis. The first and third clauses are unaffected.
* The order-one vector hatted negative norm correction (item E2 of `ERRATA.md`) does
  **not** apply here: no hatted negative norm occurs in this display.

## Readings this text fixes

* **Constant scope.** `C` is quantified before every piece of section data —
  before `nu`, the shell law, the scale selection, the test vector `e` and `p`,
  and the response `w` — exactly as the paper prints "There exists a constant
  `C(d) < ∞`"; `1 ≤ C` is a normalization.
* **`O_{Γ₂}`.** `Homogenization.IndependentSums.IsBigO P.toMeasure
  (gammaSigma 2) Z A`, that is `P[|Z| > A·t] ≤ exp(−t²)` for every `t ≥ 1`. Each
  clause asserts a measurable witness `Z` with that tail, at the stated
  amplitude, together with the domination of the clause's norm by `Z`:
  pointwise in the shell sequence for the two `L̲⁸` clauses, and almost
  everywhere for the fractional clause — `cubeHsENorm` is a supremum over a
  test class and is dominated only almost surely, as in the proved chain.
* **`‖∇w‖_{L̲⁸(cu_m)}`** is `vecCubeLpENorm (originCube d (S.m : ℤ)) 8` of the
  gradient, the Euclidean magnitude (Section 1) integrated on the normalized
  cube measure.
* **`‖∇²w‖_{L̲⁸(cu_m)}`** is `cubeLpENorm` at `q = 8` of the Frobenius
  (`HilbertMat`) carrier of the weak Hessian, read **universally over
  weak-Hessian witnesses**: the clause bounds every witness and asserts neither
  the existence of a weak Hessian nor any regularity. This is the reading of the
  Hessian clause carried from the a priori statement
  `responseFields_apriori_orderOne`; the print's `w ∈ H²(cu_m)` is not assumed here. The
  Frobenius norm differs from the operator norm by a factor between
  `1` and `√d`, absorbed by `C(d)`.
* **`‖∇w‖_{H̲^{1/2}(cu_m)}`** is `cubeHsENorm` at `s = 1/2`, on the half-open cube while the
  function lives on the open cube; the two differ by a null set.
* **`|p|`** is the Euclidean magnitude `Real.sqrt (vecNormSq p)` of
  `p = testVector nu S.LPrime P S.n e = shom_{L',*}^{-1/2}(cu_n) e`
  (`e.Sec3.p.q.def`), with `e` the unit vector of the statement.
* **`w`** is quantified over together with its defining property `e.def.w`:
  `IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)`, the zero-trace weak
  solution of `−Δw = ∇·((k_{L'} − k_{ℓ'})p)` on
  the open cube (`f_j = ∇·k_j`, no transpose). **No**
  integrability, measurability or regularity side condition and **no** carried
  estimate is assumed: the four inputs the printed proof consumes — `e.kmn.Lp`
  (at `p = 8` and `p = 2`), `e.nabla.kmn.Linfty`, `e.kmn.Hs.osc` (at `s = 1/2`)
  and the stationarity/`a.j.reg`/`l.Gamma.sigma.triangle` step — are carried
  estimates, not premises.
* **The scales** are the `ScaleSelection` package (`e.scale.selection`)
  with the ordering `e.scales.ordering`; the
  identity `m − ℓ' = h` the proof closes with is `S.ellPrime_add_h`.
* **Standing shell laws.** `ShellLawPrefix`, `ShellLawJ1Restriction` (the restriction
  lane), `ShellLawJ2`
  (independence), `ShellLawJ3` (`a.j.reg`, used through `e.nabla.kmn.Linfty` and
  the low-shell Jacobian) and `ShellLawJ4` are bound; **`ShellLawJ5`
  (`a.j.nondeg`) is not bound** — the printed proof uses none
  of the non-degeneracy input.
* **The probability space** is the canonical shell-sequence carrier `ShellSeq d`
  with the law `P`; `0 < nu ≤ 1` are the standing assumptions of the section.
* `cu_m` is `originCube d (S.m : ℤ)`; functions live on the open cube, averages
  and norms on the half-open one (the convention of the a priori anchor). -/
theorem SuperdiffusionCLT.Frozen.Section3.w_basic_regbounds
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)),
        (∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) * (S.h : ℝ) ^ ((1 : ℝ) / 2))) ∧
          ∀ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 8
                (w omega).toH1Function.grad ≤ ENNReal.ofReal (Z omega)) ∧
        (∀ (HD : ∀ omega : ShellSeq d,
              HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
                (w omega).toH1Function),
          ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) *
                (Real.sqrt (1 + (S.h : ℝ)) *
                  (3 : ℝ) ^ (-(S.ellPrime : ℝ))))) ∧
            ∀ omega : ShellSeq d,
              cubeLpENorm (originCube d (S.m : ℤ)) 8
                  (fun x => HilbertMat.ofMat
                    (fun i j => (HD omega).hess i j x)) ≤
                ENNReal.ofReal (Z omega)) ∧
        (∃ Z : ShellSeq d → ℝ, Measurable Z ∧
            IsBigO P.toMeasure (gammaSigma 2) Z
              (C * (Real.sqrt (vecNormSq p) *
                (3 : ℝ) ^ (-((S.ellPrime : ℝ) / 2)))) ∧
          ∀ᵐ omega ∂P.toMeasure,
            cubeHsENorm (originCube d (S.m : ℤ)) ((1 : ℝ) / 2)
                (hilbertifyVecField (w omega).toH1Function.grad) ≤
              ENNReal.ofReal (Z omega))
    := by
  exact SuperdiffusionCLT.Section3.ResponseFields.l_w_basic_regbounds_window d hd

end