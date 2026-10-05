/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCubeB
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsGate

/-!
# The low-shell Jacobian display of `l.w.basic.regbounds`

The display in question
is the **second** parenthesized term of the printed proof of `l.w.basic.regbounds`,

`‖∇(k_{L'} − k_{ℓ'})‖_{L̲^8(cu_m)} ≤ ∑_{k=ℓ'+1}^{L'} ‖∇ j_k‖_{L̲^8(cu_m)}
   ≤ O_{Γ₂}(C 3^{-ℓ'})`,

whose shells `k < m` — the shells *below* the cube scale — are the hypothesis
`_hNablaKmnLow` of the assembly of `e.nablaw.Lt` (see
`Section3/ResponseFields/RegboundsB.lean` and `RegboundsGate.lean`).

## Where the display comes from

The shell derivative display `e.nabla.kmn.Linfty` is a statement about the
*natural* cube of a shell.  On the larger cube `cu_m` the printed proof reaches
the shells `k < m` by stationarity: `cu_m` is the disjoint union of the
`3^{d(m−k)}` triadic sub-cubes of scale `k`, on each of which the shell field
is a translate of the natural-cube one, and a union bound over that family
turns the one-cube tail into a tail on `cu_m`.

That whole route is carried out in the modules `ShellDerivLargeCube` and its
continuation `ShellDerivLargeCubeB` of the stream estimates: `descendantsAtDepth`
supplies the sub-cube family, the translation covariance of the shell fields
supplies the per-sub-cube law, and the union bound over the `3^{d(m−k)}` sub-cubes costs the factor
`(3 log N)^{1/2}` with `N = 3^{d(m−k)}`.  Its endpoint
`exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube` is exactly the
`∃ Z` clause `_hNablaKmnLow` asks for, at the amplitude

`(√d · shellDerivLargeCubeSumConst d · √(1 + (m − ℓ'))) · (|p| 3^{-ℓ'})`.

## The window hypothesis

The manuscript prints the amplitude `C |p| 3^{-ℓ'}` with a constant `C(d)`
depending on the dimension alone; the honest union bound produces the extra
factor `√(1 + (m − ℓ')) = √(1 + h)` (the scale-selection identity
`m − ℓ' = h`, `e.scale.selection`).

The loss is *not* absorbable inside the assembly of `e.nablaw.Lt`, because that
statement quantifies the amplitude constant `Cn` of `_hNablaKmnLow` — and its
own output constant `C` — **before** the scale selection `S`, while `√(1 + h)`
is unbounded over `S`.  So the discharge below carries exactly one explicit
named hypothesis, `hCnWindow : nablaKmnLowWindowConst d S.h ≤ Cn`, a numeric
comparison between the given constant and the window of the scale selection at
hand.  Nothing else about `S`, the law or the response is assumed.

## Main results

* `nablaKmnLowWindowConst`: the union-bound amplitude `√d · C_Σ(d) · √(1 + h)`.
* `nablaKmnLow_bridge`: the binder `_hNablaKmnLow` of the assembly of `e.nablaw.Lt`, in its
  exact shape, from the large-cube estimate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The union-bound amplitude -/

/-- **The amplitude the sub-cube union bound produces** for the low-shell
Jacobian on `cu_m`: `√d` for the `d` columns of the Jacobian,
`shellDerivLargeCubeSumConst d` for the summed one-shell envelope, and
`√(1 + h)` for the union bound over the `3^{d(m−k)}` scale-`k` sub-cubes of
`cu_m`, with `h = m − ℓ'` the window of `e.scale.selection`. -/
def nablaKmnLowWindowConst (d h : ℕ) : ℝ :=
  Real.sqrt (d : ℝ) *
    Section2.Estimates.Stream.shellDerivLargeCubeSumConst d *
    Real.sqrt (1 + (h : ℝ))

/-! ## The binder `_hNablaKmnLow`, discharged -/

/-- **The low-shell Jacobian display on `cu_m`**, in the exact shape of the
binder `_hNablaKmnLow` of the assembly of `e.nablaw.Lt`.

It is the large-cube estimate
`exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube`
— stationarity over the `3^{d(m−k)}` scale-`k` sub-cubes of `cu_m` — read at
`(a, b, m) = (ℓ', m − 1, m)` and at the exponent `8`, with its amplitude raised
from `nablaKmnLowWindowConst d S.h` to `Cn`.  The scale-selection identity
`ℓ' + h = m` turns the estimate's `√(1 + (m − ℓ'))` into `√(1 + h)`. -/
theorem nablaKmnLow_bridge {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {S : ScaleSelection} (hlt : S.ellPrime < S.m) (p : Vec d) {Cn : ℝ}
    (hCnWindow : nablaKmnLowWindowConst d S.h ≤ Cn) :
    ∃ Z : ShellSeq d → ℝ, Measurable Z ∧
      IsBigO P.toMeasure (gammaSigma 2) Z
        (Cn * (Real.sqrt (vecNormSq p) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)))) ∧
      ∀ omega : ShellSeq d,
        Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 8
            (fun x => HilbertMat.ofMat (fun i j =>
              streamFluxWeakGradient omega S.ellPrime (S.m - 1) p i x j)) ≤
          ENNReal.ofReal (Z omega) := by
  obtain ⟨Z, hZm, hZO, hZle⟩ :=
    Section2.Estimates.Stream.exists_witness_cubeLpENorm_streamFluxWeakGradient_largeCube
      hPrefix hJ3 p (a := S.ellPrime) (b := S.m - 1) (m := S.m)
      (by omega) (Nat.sub_le S.m 1)
  have hwindow : ((S.m - S.ellPrime : ℕ) : ℝ) = ((S.h : ℕ) : ℝ) := by
    have h := S.ellPrime_add_h
    have : S.m - S.ellPrime = S.h := by omega
    rw [this]
  refine ⟨Z, hZm, ?_, fun omega => hZle 8 omega⟩
  refine hZO.mono_scale ?_
  rw [hwindow]
  refine mul_le_mul_of_nonneg_right hCnWindow ?_
  exact mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)

end

end SuperdiffusionCLT.Section3.ResponseFields
