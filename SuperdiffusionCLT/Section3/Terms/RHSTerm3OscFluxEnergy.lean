/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxEnergy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Energy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Duality
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCgB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscClose
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscProduct
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PrintedFinal

/-!
# `_hFlux` and `_hEnergy` of `e.RHS.term3.B`, at their named constants

## The two printed steps

The flux chain `_hFlux` of the proof of `e.RHS.term3.B` is the sequence of
inequalities

`E[‖a_{L'}(∇u_m − ∇u_{n,z})‖^{3/2}_{Ĥ̲⁻¹(z+cu_n)}]`
`≤ E[(∑_{j=-∞}^n 3^j (avsum_{z' ∈ z+3^jℤ^d ∩ cu_n}
  |(a_{L'}(∇u_m − ∇u_{n,z}))_{z'+cu_j}|²)^{1/2})^{3/2}]`
`≤ C 3^{3n/2} E[‖s^{1/2}(∇u_m − ∇u_{n,z})‖^{3/2}_{L̲²(z+cu_n)}
  ∑_{j=-∞}^n 3^{j-n} max_{z' ∈ z+3^jℤ^d ∩ cu_n} |b_{L'}(z'+cu_j)|^{3/4}]`
`≤ C 3^{3n/2} (L'ν⁻¹)^{3/4} E[‖s^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}]^{3/4}`,

and the labelled energy display `e.additivity.error.superdiff` is

`avsum_{z ∈ 3^nℤ^d ∩ cu_m} E[‖s^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}]`
`≤ C |1 − shom_{L',*}(cu_n) shom_{L',*}^{-1}(cu_m)| ≤ C(δ + η_L)`.

The conclusion of the term-3 statement reads the first chain only at its last member, at
the constant `C3`, and the second display at its last member, at the constant `1`.

## The constant of the flux chain

Reading the last member of the flux chain fixes the constant to the *named*
product

`oscFluxConst3 C1 Cb = C1 · (4 · Γ₁(1) · Cb)`

of the constant `C1` of the multiscale-Poincaré step (the first inequality) and the
constant `Cb` of the block-maximum envelope (the third inequality, read with the
fourth moment of `e.Enaught.mixing`); `Γ₁(1)` is `IndependentSums.gammaMomentConst 1`.
The factor `(L'ν⁻¹)^{3/4}` and the power `3^{3n/2}` are printed and are carried by
the carriers themselves, so they are not part of the constant.

## Main results

* `oscFluxConst3`, `oscFluxConst3_nonneg`: the named constant and its
  nonnegativity.
* `oscGluedGradM`, `oscGluedGradN`: the glued gradient fields of order `m` and `n`
  of the pure-flux slot, whose difference is the field `∇u_m − ∇u_{n,z}` of the
  display above.
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

/-! ## The named constants -/

/-- **The printed constant of the flux chain.**  The last member
of the printed chain carries the constant `C_1 · 4 \Gamma_1(1) · C_b`: `C_1` is
the constant of the multiscale-Poincaré step, `C_b` the constant
of the block-maximum envelope in the `O_{\Gamma_1}` shape of
`e.Enaught.mixing`, and `4 \Gamma_1(1)` the moment conversion of
`rpow_four_moment_le_of_isBigO_gammaSigma_one` at `\sigma = 1`.  The definition
mentions neither the sample law nor any scale: `C_1` and `C_b` are its only
inputs. -/
def oscFluxConst3 (C1 Cb : ℝ) : ℝ :=
  C1 * (4 * IndependentSums.gammaMomentConst 1 * Cb)

/-- The named flux constant is nonnegative at `C_1 ≥ 0`, `C_b > 0`. -/
theorem oscFluxConst3_nonneg {C1 Cb : ℝ} (hC1 : 0 ≤ C1) (hCb : 0 < Cb) :
    0 ≤ oscFluxConst3 C1 Cb :=
  mul_nonneg hC1 (mul_nonneg (mul_nonneg (by norm_num)
    (IndependentSums.gammaMomentConst_pos one_pos).le) hCb.le)

/-! ## The glued fields of the display -/

/-- The conclusion's own glued `\nabla u_m` field: the order-`m` glued
gradient of the pure-flux slot, the first field of the flux
`a_{L'}(\nabla u_m - \nabla u_{n,z})`. -/
def oscGluedGradM {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu) (S : ScaleSelection)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) : ShellSeq d → Vec d → Vec d :=
  fun omega y =>
    gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega y

/-- The conclusion's own glued `\nabla u_{n,z}` field: the order-`n`
glued gradient of the same slot, the second field of the flux. -/
def oscGluedGradN {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu) (S : ScaleSelection)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d) : ShellSeq d → Vec d → Vec d :=
  fun omega y =>
    gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega y

/-! ## `_hFlux` at the named constant

The constant is `oscFluxConst3 C1 Cb`, fixed before the scale selection.  The
integrability of the flux power is deduced from the `L^{3/2}` membership of the
flux carrier, which the display already carries as `_hMemFlux`. -/

/-! ## `_hEnergy` discharged, at its printed constant `1`

The two annealed response values are replaced by their deterministic quenched
counterparts. -/

/-! ## The display with `_hCS`, `_hFlux` and `_hEnergy` removed -/

end

end SuperdiffusionCLT.Section3.Terms
