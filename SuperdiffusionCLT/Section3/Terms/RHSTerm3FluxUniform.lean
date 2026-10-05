/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscFluxSeminorm

/-!
# `hFluxUniform` of the final statement of `e.RHS.term3`

The target binder, quoted from the final statement of `e.RHS.term3`:

```
hFluxUniform : ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ nu hnu hnu1 P (ShellLawPrefix, ShellLawJ1Restriction,
    ShellLawJ2, ShellLawJ3, ShellLawJ4) S (ScalesOrdering, 2h≤m, 100a≤h,
    h+1≤3^a, offset lower bound) e he delta etaL hdelta hetaL w hw,
  ∀ R ∈ largeCubeSubcubes d S.n S.m,
    ∫ seminormFluxNeg nu hnu S P e omega R ^ (3/2) ∂P ≤
      C3 * 3 ^ (3 S.n / 2) * (L' ν⁻¹) ^ (3/4) *
        (∫ oscEnergy nu hnu S P e omega R ∂P) ^ (3/4)
```

This is the printed last member of the flux chain `_hFlux` of `e.RHS.term3.B`
(the multiscale Poincare / Hoelder chain):

```
E[ ‖ a_{L'} (∇u_m − ∇u_{n,z}) ‖_{H̲^{-1}(z+cu_n)}^{3/2} ]
  ≤ E[ (∑_{j=-∞}^n 3^j (avsum_{z'} |(a_{L'}(∇u_m−∇u_{n,z}))_{z'+cu_j}|^2)^{1/2})^{3/2} ]
  ≤ C 3^{3n/2} E[ ‖σ^{1/2}(∇u_m−∇u_{n,z})‖_{L̲²(z+cu_n)}^{3/2}
              ∑_{j=-∞}^n 3^{j-n} max_{z'} |b_{L'}(z'+cu_j)|^{3/4} ]
  ≤ C 3^{3n/2} (L'ν^{-1})^{3/4} E[ ‖σ^{1/2}(∇u_m−∇u_{n,z})‖_{L̲²(z+cu_n)}^2 ]^{3/4}
```

read at the seminorm dual flux norm `seminormFluxNeg`
(`RHSTerm3OscSeminormClose`), the norm the `_hOscBound` chain actually carries at this
point of the development.

## The chain of lemmas that gets closest

`oscFlux_seminorm` proves,
for one fixed `nu, S, P, e`, exactly the printed last member of the chain from:

* `blockWeight`, a per-`(omega, R)` scalar,
* `hPointwise` — the first two inequalities of the chain in
  one bound, at the named constant `C1` (fixed before `S`),
* `hBlockNonneg`, `hBlockOrlicz` — the block envelope of the chain, in the
  `O_{Γ₁}` shape of `e.Enaught.mixing`, at the named constant `Cb`,
* `hMemFluxCarrier`, `hProdInt`, `hMemE`, `hMemB` — the sample-side
  memberships the Hoelder step reads,

at the constant `oscFluxConst3 C1 Cb = C1 · (4 · Γ₁(1) · Cb)`, fixed before
`S`. This is the statement closest to `hFluxUniform`: the same
theorem, restated, is what `_hFlux` is reduced to throughout the development.  A norm
comparison does not help prove `hPointwise`: it
runs in the direction that would transport a bound from the order-one dual flux norm
to `seminormFluxNeg`, and that transport costs an extra printed
flux scale `3^{3n/2}` beyond the one `hFluxUniform` already carries, so it
cannot be used to prove `hPointwise` at a constant fixed before `S`.

## Reduction of `hFluxUniform`

`hFluxUniform` is not proved from `d`, `[NeZero d]`, `hd` alone in this file:
proving it requires supplying, for *every*
`nu, S, P, e, delta, etaL, w` satisfying only the binder's own premises, a
`blockWeight` together with proofs of `hPointwise` and
`hBlockOrlicz`. Both are printed displays that the paper
states without proof or citation.  The reduction
`fluxUniform_of_gaps` proved here isolates exactly those two displays
(bundled with the sample-side data `oscFlux_seminorm` reads into one
hypothesis `hGap`, universally quantified over the same environment as
`hFluxUniform` itself) and proves `hFluxUniform`'s exact statement from them.
The two printed displays are named precisely in `hGap`'s first two
conjuncts below; nothing else in `hFluxUniform`'s binder is left open by this
reduction.  The sample-side clauses of `hGap` are supplied in the subsequent files
(`RHSTerm3FluxUniformPart0` to `RHSTerm3FluxUniformPart4`), which end with
`fluxSample_fluxUniform_main`, leaving only the two printed flux-chain steps as
hypotheses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-- **`hFluxUniform` of the final statement of `e.RHS.term3`,
reduced to the two printed estimates of the flux chain plus the
sample-side data the Hoelder step reads.**

`blockWeight` and `hBlockNonneg` are the per-cube weight of the printed chain and its
nonnegativity, chosen once for every environment (they do not depend on
`delta`, `etaL` or `w`, matching the print, though nothing here forces that).
`hGap`, quantified over exactly the environment `hFluxUniform` itself
quantifies over, bundles:

1. `hPointwise` — the quenched `3/2`-power multiscale-Poincare step at `s=1`
   composed with the energy-map step `e.energymaps.nonsymm.flux` and the
   convexity rearrangement, at the constant `C1` fixed before
   `S`;
2. `hBlockOrlicz` — the block-maximum envelope of the printed chain, in the
   `O_{Γ₁}` shape of `e.Enaught.mixing`, at the constant `Cb` fixed before
   `S`;
3. `hMemFluxCarrier`, `hProdInt`, `hMemE`, `hMemB` — the sample-side
   memberships the Hoelder step of `multiscale_poincare_flux` reads.

The conclusion is `hFluxUniform`'s exact statement, at the constant
`oscFluxConst3 C1 Cb = C1 · (4 · Γ₁(1) · Cb)` fixed before the scale
selection, via `oscFlux_seminorm`. -/
theorem fluxUniform_of_gaps (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
    (C1 Cb : ℝ) (hC1 : 0 ≤ C1) (hCb : 0 < Cb)
    (blockWeight : ℝ → ScaleSelection → ProbabilityMeasure (ShellSeq d) →
      Vec d → ShellSeq d → TriadicCube d → ℝ)
    (hBlockNonneg : ∀ (nu : ℝ) (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d))
        (e : Vec d) (omega : ShellSeq d) (R : TriadicCube d),
      0 ≤ blockWeight nu S P e omega R)
    (hGap : ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
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
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)),
      (∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
        seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ≤
          C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
            (oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) *
              blockWeight nu S P e omega R)) ∧
      (∀ R ∈ largeCubeSubcubes d S.n S.m,
        IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
          (fun omega : ShellSeq d => blockWeight nu S P e omega R)
          (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4))) ∧
      (∀ R ∈ largeCubeSubcubes d S.n S.m,
        MemLp (fun omega : ShellSeq d => seminormFluxNeg nu hnu S P e omega R)
          (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure) ∧
      (∀ R ∈ largeCubeSubcubes d S.n S.m,
        Integrable (fun omega : ShellSeq d =>
          oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) * blockWeight nu S P e omega R)
          P.toMeasure) ∧
      (∀ R ∈ largeCubeSubcubes d S.n S.m,
        MemLp (fun omega : ShellSeq d => oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4))
          (ENNReal.ofReal ((4 : ℝ) / 3)) P.toMeasure) ∧
      (∀ R ∈ largeCubeSubcubes d S.n S.m,
        MemLp (fun omega : ShellSeq d => blockWeight nu S P e omega R)
          (ENNReal.ofReal (4 : ℝ)) P.toMeasure)) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
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
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
            omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)),
      ∀ R ∈ largeCubeSubcubes d S.n S.m,
        ∫ omega : ShellSeq d,
            seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)
            ∂P.toMeasure ≤
          C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
            (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
            (∫ omega : ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure) ^
              ((3 : ℝ) / 4) := by
  refine ⟨oscFluxConst3 C1 Cb, oscFluxConst3_nonneg hC1 hCb, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM hHundredALeH
    hWindowVsOffset hOffsetLower e he delta etaL hdelta hetaL w hw
  obtain ⟨hPointwise, hBlockOrlicz, hMemFluxCarrier, hProdInt, hMemE, hMemB⟩ :=
    hGap nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hTwoHLeM hHundredALeH
      hWindowVsOffset hOffsetLower e he delta etaL hdelta hetaL w hw
  exact oscFlux_seminorm d C1 Cb hC1 hCb (nu := nu) (P := P) (S := S) (e := e)
    hnu hSorder (blockWeight nu S P e) hPointwise
    (fun omega R => hBlockNonneg nu S P e omega R) hBlockOrlicz hMemFluxCarrier
    hProdInt hMemE hMemB

end

end SuperdiffusionCLT.Section3.Terms
