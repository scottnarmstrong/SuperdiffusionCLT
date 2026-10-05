/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays
public import SuperdiffusionCLT.Section3.Terms.GluedField
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1
public import SuperdiffusionCLT.Probability.OrliczIndexWeakening
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMomentLargeCube

/-!
# `l.RHS.term2`

The paper poses `l.RHS.term2` and proves it by the following steps.  This module carries the
assembly of that proof: the three-term splitting of the cubewise average, the two Cauchy-Schwarz
steps, the decoupled and centred proxy term, and the closing arithmetic.

The three displayed inputs `hRbounds`, `hProxyError`, `hProxyEnergy` are the
conclusions of `e.RHS.term2.R.bounds`,
`e.RHS.term2.proxy.error` and `e.RHS.term2.proxy.energy`; the third is proved in the module
`RHSTerm2Inputs` from the energy identity `e.un.tilde.un.energy`.  The identity
`|p| σ̄_{L',*}^{1/2}(cu_n) = 1` of `e.Sec3.p.q.def` is a proved identity,
not a hypothesis, and `ν ≤ 1` is the standing convention.

## The two step inputs and the typing data

The glued fields `∇u_n`, `∇ũ_n` and the proxy mean `p̃` are free binders, so
the statement carries no information about them beyond the three displays.  The
proof therefore takes, in addition:

* `hDecouple`, the step `l.RHS.term2#independence-decoupling`
  in the shape the assembly uses: the expectation of the proxy pairing equals
  the expectation of the pairing of the two *centred* fields.  It is the
  cube-by-cube cancellation `E[(R)_{z+cu_n}·((∇ũ_n)_{z+cu_n} − p̃)] = 0`, whose
  proof from `ShellLawJ2` is `independence_decoupling` of
  `RHSTerm2Displays.lean`, combined with the splitting of the cube average.
  It cannot be derived here: nothing in the statement makes `∇ũ_n` measurable
  with respect to the low shells.
* `hPoincare`, the step `l.RHS.term2#poincare-per-cube` on
  each sub-cube, in the exact shape produced by `poincare_per_cube` of
  `RHSTerm2Displays.lean` at `Q = z` (whose constant is
  `cubeScaleFactor z * C_d = 3^n C_d`).
* the typing data: square integrability of the three fields and of the
  Jacobian on the large cube, finiteness and measurability in `ω` of the four
  annealed cube norms, and integrability in `ω` of the three pieces of the
  splitting.  The print never states these; for the free binders of the
  rendered statement they are not derivable.

`l.RHS.term2` is not provable from the three displays alone with a constant
that does not depend on the scales: the proxy term
`E[⨍_{cu_m} R·(∇ũ_n − p̃)]` is only bounded by
`E[‖R‖²]^{1/2}E[‖∇ũ_n − p̃‖²]^{1/2} ≤ Cν⁻¹L'` without the decoupling, and
`ν⁻¹L'` exceeds `ν⁻³(L')²3^{-(ℓ-n)/2}` as soon as
`3^{(ℓ-n)/2} > ν⁻²L'`, which the scale selection `ℓ − n = a = ⌈K log(ν⁻¹L)⌉`
arranges for large `K`.  The decoupling step is what produces the decay.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The three-term splitting of the cubewise lattice average -/

/-- **The three-term decomposition**: the lattice average of
the pairing of `Rf` against `UN − pv` is the sum of the three large-cube
averages of the localization error, the centred proxy, and the mean defect. -/
theorem avsum_split {n m : ℕ}
    {Rf UN UT : Vec d → Vec d} {pT pv : Vec d}
    (hR : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) Rf)
    (hU : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) UN)
    (hT : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) UT) :
    ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m,
          volumeAverage (openCubeSet z) (fun y => vecDot (Rf y) (UN y - pv)) =
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
          (fun y => vecDot (Rf y) (UN y - UT y)) +
        volumeAverage (openCubeSet (originCube d (m : ℤ)))
          (fun y => vecDot (Rf y) (UT y - pT)) +
        volumeAverage (openCubeSet (originCube d (m : ℤ)))
          (fun y => vecDot (Rf y) (pT - pv)) := by
  have hUp : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (fun y => UN y - pv) :=
    memVectorL2_sub_const pv hU
  have h1 : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (fun y => UN y - UT y) :=
    hU.sub hT
  have h2 : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (fun y => UT y - pT) :=
    memVectorL2_sub_const pT hT
  have h3 : MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (fun _ : Vec d => pT - pv) := memVectorL2_const (pT - pv)
  have hsum : ∀ z ∈ largeCubeSubcubes d n m,
      IntegrableOn (fun y => vecDot (Rf y) (UN y - pv)) (openCubeSet z) volume :=
    fun z hz => integrableOn_vecDot (memVectorL2_subcube hz hR) (memVectorL2_subcube hz hUp)
  rw [← volumeAverage_avsum_openCubeSet hsum]
  have hpt : (fun y => vecDot (Rf y) (UN y - pv)) =
      fun y => (vecDot (Rf y) (UN y - UT y) + vecDot (Rf y) (UT y - pT)) +
        vecDot (Rf y) (pT - pv) := by
    funext y
    have hy : UN y - pv = ((UN y - UT y) + (UT y - pT)) + (pT - pv) := by abel
    rw [hy, vecDot_add_right, vecDot_add_right]
  rw [hpt]
  have hadd1 : IntegrableOn
      (fun y => vecDot (Rf y) (UN y - UT y) + vecDot (Rf y) (UT y - pT))
      (openCubeSet (originCube d (m : ℤ))) volume :=
    (integrableOn_vecDot hR h1).add (integrableOn_vecDot hR h2)
  rw [volumeAverage_add'
      (f := fun y => vecDot (Rf y) (UN y - UT y) + vecDot (Rf y) (UT y - pT))
      (g := fun y => vecDot (Rf y) (pT - pv)) hadd1 (integrableOn_vecDot hR h3),
    volumeAverage_add' (f := fun y => vecDot (Rf y) (UN y - UT y))
      (g := fun y => vecDot (Rf y) (UT y - pT))
      (integrableOn_vecDot hR h1) (integrableOn_vecDot hR h2)]

/-- The transposition step: since `k_{L'} − k_ℓ` is skew, pairing `∇w`
against `(k_{L'} − k_ℓ)v` is minus the pairing of the transported field
`(k_{L'} − k_ℓ)∇w` against `v`. -/
theorem vecDot_coefficientCutoff_sub_swap (nu : ℝ) (omega : ShellSeq d)
    {ell LPrime : ℕ} (h : ell < LPrime) (y g v : Vec d) :
    vecDot g (matVecMul ((coefficientCutoff nu omega LPrime).toCoeffField y -
        (coefficientCutoff nu omega ell).toCoeffField y) v) =
      -vecDot (matVecMul ((coefficientCutoff nu omega LPrime).toCoeffField y -
        (coefficientCutoff nu omega ell).toCoeffField y) g) v := by
  have hskew : matTranspose ((coefficientCutoff nu omega LPrime).toCoeffField y -
      (coefficientCutoff nu omega ell).toCoeffField y) =
      -((coefficientCutoff nu omega LPrime).toCoeffField y -
        (coefficientCutoff nu omega ell).toCoeffField y) := by
    rw [coefficientCutoff_sub_apply omega nu ell LPrime h y]
    exact finiteShellIncrement_skew omega ell LPrime y
  rw [SuperdiffusionCLT.Section3.Terms.vecDot_matVecMul_transpose, hskew,
    neg_matVecMul, vecDot_neg_left]

/-! ## The main theorem -/

/-! ## `e.RHS.term2.proxy.error` -/

/-! ## The glued fields -/

end

end SuperdiffusionCLT.Section3.Terms
