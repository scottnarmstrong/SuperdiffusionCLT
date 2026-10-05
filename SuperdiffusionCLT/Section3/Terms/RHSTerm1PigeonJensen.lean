/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1FrozenReduction
public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly

/-!
# `l.RHS.term1`: the constant gate of the concentration obligation

The reduction `term1_of_obligations` (in `RHSTerm1FrozenReduction`) carries the concentration
`_hConcDepth` at the section-wide constant `Cc`.  The printed sublattice concentration
`E[avsum_z |(a_ℓ ∇ũ_n − q̃)_{z+cu_k}|²] ≤ Cc 3^{-d(k-ℓ)_+} E[‖a_ℓ ∇ũ_n − q̃‖²_{L̲²(cu_m)}]`
has a right side that is linear in `Cc` against the nonnegative weight `3^{-d(m-j-ℓ)}` and the
nonnegative integral `∫⁻ ‖·‖²`.

## Main results

* `hConcDepth_gate_upgrade`: the clause at any `Cc₀` gives the clause at any larger constant, so
  the normalization `1 ≤ Cc` costs nothing and `hCc` is never an obstruction.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

/-! ## The constant gate -/

/-- **The `Cc` gate of `_hConcDepth` is free.**  The clause's right side is
`ENNReal.ofReal (Cc * w) * A`, where `w = 3^{-d(m-j-ℓ)} ≥ 0` and `A = ∫⁻ ‖·‖²` is
an arbitrary `ℝ≥0∞`.  The right side is monotone in `Cc` against the
nonnegative weight, with no sign hypothesis on `Cc` (`ℝ≥0∞.ofReal` is monotone),
so a proof of the clause at any real `Cc` yields it at any `Cc' ≥ Cc`; in
particular the gate `1 ≤ Cc` costs nothing. -/
theorem hConcDepth_gate_upgrade {Cc Cc' w : ℝ} (hle : Cc ≤ Cc') (hw : 0 ≤ w)
    (A : ℝ≥0∞) :
    ENNReal.ofReal (Cc * w) * A ≤ ENNReal.ofReal (Cc' * w) * A :=
  mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle hw)) A

end

end SuperdiffusionCLT.Section3.Terms
