/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscFluxEnergy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscSeminormClose
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsA

/-!
# `_hFlux` at the seminorm flux norm `seminormFluxNeg`

The flux chain `_hFlux` of `e.RHS.term3.B` is the printed sequence of three
inequalities ending at

`C 3^{3n/2}(L'\nu^{-1})^{3/4} E[‖σ^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}]^{3/4}`.

The display `_hOscBound` is read at the seminorm carrier `centredSeminormAt`, which
the duality pairs with its **own** dual flux norm `seminormFluxNeg`
(`RHSTerm3OscSeminormClose.lean`); this module proves `_hFlux` at that norm, with
the named constant `oscFluxConst3 C1 Cb = C1 · (4 Γ₁(1) Cb)`.

## Why the chain is not transported from the order-one hatted flux norm

A transport would have to bound the seminorm flux moment by the order-one one,
i.e. it needs a constant `D`, fixed before `S`, with

`seminormFluxNeg^{3/2} ≤ D · (order-one flux norm)^{3/2}` pointwise.

The comparison `centredSeminormNegNorm_le_vecHatNegENormOrderOne` does run in that
direction — the seminorm norm is dominated by the order-one norm — but its
constant is the *per-cube scale* `K_R = 3^{scale R}·(C_d + 3)`, so raising to the
flux exponent costs

`K_R^{3/2} = 3^{3n/2}·(C_d + 3)^{3/2}`

on every scale-`n` sub-cube.  Composing with the chain for the order-one norm —
whose own right side already carries the printed `3^{3n/2}` — yields the bound

`∫ seminormFluxNeg^{3/2} ≤ C3·(C_d + 3)^{3/2}·3^{3n}·(L'\nu^{-1})^{3/4}·(∫ oscEnergy)^{3/4}`,

one factor `3^{3n/2}` *beyond* the printed flux scale; `3^{3n/2}` grows in `n`
and cannot be absorbed into a constant fixed before `S`.  So the transported
statement is strictly weaker than the displayed `_hFlux`.

## The route taken: the printed chain re-read at the seminorm norm

The engine `multiscale_poincare_flux` (`RHSTerm3StepsA.lean`) — the convexity
rearrangement with weights `∑_j 3^{j−n} = 3/2`, the Hölder decoupling at
`(4/3, 4)` and the `Γ₁`-tail-to-moment conversion — is generic in its flux norm:
it takes `fluxNegNorm energyL2 blockWeight` as free binders.  The seminorm chain
is its instantiation at `seminormFluxNeg` with `energyL2 := oscEnergy`, so
`oscFlux_seminorm` below is a re-reading of the printed chain rather than a
transported one, and it carries two printed steps as hypotheses: the quenched
`3/2`-power multiscale-Poincaré step (`hPointwise`, now at the seminorm's own dual
norm) and the block envelope (`hBlockOrlicz`).

## The powers of `3`

At the seminorm norm exactly one power of `3` survives, and it is the printed
one, entering at a single place:

* `3^{3n/2}` enters through `hPointwise`, the printed factor of the second
  inequality of the chain, and is carried verbatim into the conclusion;
  `multiscale_poincare_flux` multiplies it by nothing.
* `3^{scale R}` (the `K_R` of the comparison) does **not** enter: the seminorm
  norm is never compared with the order-one norm on this route, so nothing needs
  to cancel, and no `3^n` is created to cancel against the printed one.
* `3^{j−n}` over `j ≤ n` enters only inside the depth sum carried by
  `hPointwise` itself, where the weights sum to `3/2`; the engine consumes it
  there and contributes no further scale factor.
* The carriers of the chain carry no power of `3`: `centredSeminormAt` is the
  seminorm `‖∇²w‖_{L̲²(R)}` with no scale, and `seminormFluxNeg` is the dual of
  that seminorm, also unscaled — this is exactly why the seminorm carrier was
  chosen and why the printed `3^{3n/2}` stays where the paper puts it.

The constant is `oscFluxConst3 C1 Cb = C1 · (4 Γ₁(1) Cb)`: `C1` is the constant
of the printed multiscale-Poincaré step, `Cb` that of the printed block envelope,
and `4 Γ₁(1)` the moment conversion
`rpow_four_moment_le_of_isBigO_gammaSigma_one` at `σ = 1`.  It is the same
constant as for the order-one norm — the change of norm costs nothing — and it
mentions neither `S`, nor `nu`, nor `P`, nor any scale or power of `3`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## Integrability of the seminorm flux moment

The Hölder step of the chain reads the integrability of the flux power; at the
seminorm norm it is deduced from the `L^{3/2}` membership of the seminorm flux
norm itself, exactly as the old chain deduces it from `hMemFluxCarrier`. -/

/-- **The `3/2`-power of the seminorm flux norm is integrable.**  From the
`L^{3/2}(P)` membership of `seminormFluxNeg` — the sample-side membership the
display carries as `_hMemFlux` — via `norm`-`abs` and nonnegativity.  No
integrability hypothesis is added: this is the `hFluxInt` input of the chain. -/
theorem integrable_seminormFlux_rpow_of_memLp {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (S : ScaleSelection) (P : ProbabilityMeasure (ShellSeq d))
    (e : Vec d)
    (hMemFluxCarrier : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d => seminormFluxNeg nu hnu S P e omega R)
        (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)) P.toMeasure := by
  intro R hR
  have h1 : Integrable (fun omega : ShellSeq d =>
      ‖seminormFluxNeg nu hnu S P e omega R‖ ^ ((3 : ℝ) / 2)) P.toMeasure := by
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)] using
      (hMemFluxCarrier R hR).integrable_norm_rpow
        (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))) ENNReal.ofReal_ne_top
  refine h1.congr (Filter.Eventually.of_forall fun omega => ?_)
  show ‖seminormFluxNeg nu hnu S P e omega R‖ ^ ((3 : ℝ) / 2) =
    seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (seminormFluxNeg_nonneg nu hnu S P e omega R)]

/-! ## `_hFlux` at the seminorm flux norm -/

/-- **`_hFlux` of `e.RHS.term3.B` at the seminorm flux norm `seminormFluxNeg`.**
The conclusion is the printed last member of the chain, at the named constant
`oscFluxConst3 C1 Cb` — `C1` and `Cb` fixed before `S` — with the printed
`3^{3n/2}` intact and no scale factor on the norm.  It is *not* obtained by
transport from the chain for the order-one hatted norm: the comparison
`centredSeminormNegNorm_le_vecHatNegENormOrderOne` carries `K_R = 3^{scale R}(C_d + 3)`,
whose `3/2`-power `3^{3n/2}(C_d + 3)^{3/2}` would add one printed flux scale to the
right-hand side (see the module note).

The two printed steps carried as hypotheses, at the seminorm norm, are:

* `hPointwise`: the quenched `3/2`-power form of the multiscale-Poincaré step at
  `s = 1` with the energy-map step `e.energymaps.nonsymm.flux`, now stated for
  `seminormFluxNeg`, whose `3^{3n/2}` is the only power of `3` the chain carries;
* `hBlockOrlicz`, `hBlockNonneg`: the block envelope in the `O_{Γ₁}` shape of
  `e.Enaught.mixing`;

together with the sample-side data the Hölder step reads: `hMemFluxCarrier` (the
`L^{3/2}` membership of the flux, from which the integrability of the flux power
is deduced by `integrable_seminormFlux_rpow_of_memLp`), `hProdInt`, `hMemE` and
`hMemB`.  The measurability of the block weight is the `AEMeasurable` conjunct of
`hMemB`, not a separate hypothesis.

Everything between the two printed steps is `multiscale_poincare_flux`, applied
here with `fluxNegNorm := seminormFluxNeg` and `energyL2 := oscEnergy`. -/
theorem oscFlux_seminorm (d : ℕ) [NeZero d]
    (C1 Cb : ℝ) (hC1 : 0 ≤ C1) (hCb : 0 < Cb)
    {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    {S : ScaleSelection} (hSorder : ScalesOrdering S) {e : Vec d}
    (blockWeight : ShellSeq d → TriadicCube d → ℝ)
    (hPointwise : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ≤
        C1 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
          (oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) * blockWeight omega R))
    (hBlockNonneg : ∀ (omega : ShellSeq d) (R : TriadicCube d), 0 ≤ blockWeight omega R)
    (hBlockOrlicz : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
        (fun omega : ShellSeq d => blockWeight omega R)
        (Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4)))
    (hMemFluxCarrier : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d => seminormFluxNeg nu hnu S P e omega R)
        (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure)
    (hProdInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4) * blockWeight omega R)
        P.toMeasure)
    (hMemE : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d =>
        oscEnergy nu hnu S P e omega R ^ ((3 : ℝ) / 4))
        (ENNReal.ofReal ((4 : ℝ) / 3)) P.toMeasure)
    (hMemB : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d => blockWeight omega R)
        (ENNReal.ofReal (4 : ℝ)) P.toMeasure) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          seminormFluxNeg nu hnu S P e omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤
        oscFluxConst3 C1 Cb * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
          (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
          (∫ omega : ShellSeq d, oscEnergy nu hnu S P e omega R ∂P.toMeasure) ^
            ((3 : ℝ) / 4) := by
  have hFluxInt := integrable_seminormFlux_rpow_of_memLp (d := d) hnu S P e hMemFluxCarrier
  intro R hR
  have hmain := multiscale_poincare_flux (d := d) hnu P hSorder
    (fun omega (_ : TriadicCube d) => seminormFluxNeg nu hnu S P e omega R)
    (fun omega (_ : TriadicCube d) => oscEnergy nu hnu S P e omega R)
    (fun omega (_ : TriadicCube d) => blockWeight omega R)
    R hC1 hCb
    (fun omega => oscEnergy_nonneg hnu S P e omega R)
    (fun omega => hBlockNonneg omega R)
    (fun omega => hPointwise omega R hR)
    (hBlockOrlicz R hR) (hMemB R hR).aemeasurable
    (hFluxInt R hR) (hProdInt R hR) (hMemE R hR) (hMemB R hR)
  simpa only [oscFluxConst3] using hmain

end

end SuperdiffusionCLT.Section3.Terms
