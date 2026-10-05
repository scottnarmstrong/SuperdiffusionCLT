/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Parameters of the proof of AK.HC Theorem 6.1, Step 1

Proof of Theorem `t.weaker.P3` of [AK] ("Step 1"), together with the
constants `K`, `h_c` of Lemma `l.weaknorms.prime` (`e.L.and.hc`)
and the exponents `ρ′, ρ` of that lemma's own proof.

This file supplies literal, closed-form real/natural definitions of every
scalar parameter the Step 1 argument introduces. It is pure real and natural
number arithmetic: no probability law, no shell field, no measure. Every
underlying `(P2′)`/`(P3′)` witness constant (`γ, H, D, m₂, K_{Ψ_S}, p_{Ψ_S}`
from `a.ellipticity.weaker`, and `β, L₁, L₂, m₃, K_Ψ, p_Ψ` from
`a.CFS.weaker`) is a plain function argument here, in the ranges the two
assumptions fix:
`γ, β ∈ [0,1)`; `H, K_Ψ, K_{Ψ_S}, L₁, L₂ ∈ [1,∞)`; `D ∈ [0,∞)`;
`p_{Ψ_S} ∈ (2,∞)`; `p_Ψ ∈ (d,∞)`; `σ ∈ (0,1)`; `δ ∈ (0,(80d)^{-2}]`.

## The pigeonhole horizon `e.M.def.prime`

The printed pigeonhole horizon `N(σ,δ) := 2L⌈2δ⁻¹|log σ|⌉` (`e.M.def.prime`) is **not**
reproduced by this file. The printed `l.pigeon` conclusion, stated for the determinant-root
`ΞDet`, is unsupported at this horizon: only a single eigenvalue crosses the per-interval
threshold, so the determinant-ratio contraction is `(1+δ₁)^{-1/d}` per interval, not
`(1+δ₁)^{-1}`; and no weaker-mixing horizon is given for this specific invocation. Under
isotropy `(P4)` the coarse-grained matrices are scalar (`a.iso#adapted-cubes-trivial`), so the
pigeonhole is a genuine scalar dichotomy and the factor-`d` correction is not needed here;
what remains is the parameter substitution `δ₁ := σ²δ`, `σ₁ := σ/4`. The pigeonhole application
(`AKHC61/Step2/Launch.lean`) therefore uses the corrected horizon
`N′(σ,δ) := 2L⌈2σ⁻²δ⁻¹|log(σ/4)|⌉` (`akhcLaunchNprimeNat`), in place of the printed `N`.

## The parameter `akhcEta`

`ρ′, ρ` are fixed exactly by the paper. The moment/tail
exponent `η` used inside `e.this.is.so.nice.again#tail-cfs-weaker` is not
defined in the printed text at that point. `akhcEta` below records the natural choice
consistent with `Υ₁`'s own denominator `min{d+1,p_Ψ}-d`; it is not
tied to the moment argument that actually produces it
(the `K_Ψ^{4d²}` constant of that same display).

## Main definitions

`akhcK`, `akhcHc` (`e.L.and.hc`); `akhcUpsilon2` (the proof's own form — **not** the theorem
statement's asymptotic `Υ₁,Υ₂`, which carry an unspecified `C(d)` and are not used here);
`akhcRhoPrime`, `akhcRho`; `akhcEta` (tentative, see above).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Params

noncomputable section

/-- `K` (`e.L.and.hc`): `K := L₁ + 16D/(1-γ)`. -/
def akhcK (L1 D gamma : ℝ) : ℝ := L1 + 16 * D / (1 - gamma)

/-- `h_c` (`e.L.and.hc`):
`h_c := 2K log(2L₂) + (100/(1-γ))(D + log H + K_{Ψ_S})`. -/
def akhcHc (L1 L2 D H KPsiS gamma : ℝ) : ℝ :=
  2 * akhcK L1 D gamma * Real.log (2 * L2) +
    100 / (1 - gamma) * (D + Real.log H + KPsiS)

/-- `Υ₂`, the proof's own form:
`Υ₂ := 3^{h_c}/(min{3,p_{Ψ_S}}-2)`. -/
def akhcUpsilon2 (pPsiS hc : ℝ) : ℝ :=
  (3 : ℝ) ^ hc / (min (3 : ℝ) pPsiS - 2)

/-- `ρ′`: `ρ′ := max{γ, d/min{d+1,p_Ψ}, 2/min{3,p_{Ψ_S}}}`. -/
def akhcRhoPrime (d : ℕ) (gamma pPsi pPsiS : ℝ) : ℝ :=
  max gamma (max ((d : ℝ) / min ((d : ℝ) + 1) pPsi) (2 / min (3 : ℝ) pPsiS))

/-- `ρ = (1+ρ′)/2`. -/
def akhcRho (d : ℕ) (gamma pPsi pPsiS : ℝ) : ℝ :=
  (1 + akhcRhoPrime d gamma pPsi pPsiS) / 2

/-- Tentative tail-moment exponent; see the module docstring. NOT
independently pinned by the read Section 6 corpus. -/
def akhcEta (d : ℕ) (pPsi : ℝ) : ℝ := min ((d : ℝ) + 1) pPsi

end

end SuperdiffusionCLT.AKHC61.Params
