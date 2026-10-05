/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3ConstFirst
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsWindowB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3InputsE
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The data-free inputs of `l.RHS.term3`

The paper's `l.RHS.term3` has one constant `C(d)`, chosen before every datum `ν`, `P`, `S`, `e`,
`p`, `w`, ….  With the data fixed first, a finite left-hand side always admits some `C`, so that
shape carries no information.  In the constant-first statement the constants of the discharge
chain must therefore be produced before the data.

This module records the nonnegativity of the four constants of that chain, built from the
regularity constant `Creg`, the dimension, `C0` and the one-sided amplitude `Cms` of
`l.mixing.minscale`.  The main quadratic-tail constant is taken at the absolute pigeonhole
constant `4`: under the hypotheses of the statement the comparability constant
`Cpig = 1 + δ + 6η_L` of `e.pigeon.scalar` is below `4`, since `δ ≤ 1` and the threshold data
of `e.L.vs.nu` force `η_L ≤ 1/4` at the selected gap `L' − m = 2a`.

## Main results

* `termThreeDisp1Const_nonneg`, `termThreeBlockConst_nonneg`,
  `termThreeQuadMainConst_nonneg`, `termThreeQuadErrConst_nonneg`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The four constants of the discharge chain, before the data -/

/-- Nonnegativity of the first-display constant `C1 = C₀ d C_{∇w,2}(C_reg)` of
the constant-first statement of `l.RHS.term3`, the witness `disp1_of_regbounds` produces. -/
theorem termThreeDisp1Const_nonneg (d : ℕ) {C0 Creg : ℝ} (hC0 : 0 ≤ C0)
    (hCreg : 1 ≤ Creg) : 0 ≤ C0 * (d : ℝ) * nablaW2Const Creg := by
  have h := one_le_nablaW2Const hCreg
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h0 : (0 : ℝ) ≤ nablaW2Const Creg := le_trans zero_le_one h
  positivity

/-- Nonnegativity of the block-concentration constant `C2 = blockDevConst` of
the constant-first statement of `l.RHS.term3`, the witness `blockDev_of_concentration` produces. -/
theorem termThreeBlockConst_nonneg (d : ℕ) {C0 Creg : ℝ} (hC0 : 0 ≤ C0) :
    0 ≤ blockDevConst d C0 (nablaW4SqrtConst Creg) :=
  blockDevConst_nonneg d hC0 (nablaW4SqrtConst_nonneg Creg)

/-- Nonnegativity of the main quadratic-tail constant
`C3a = C₀ C_main(streamTailConst d, C_{∇w,4}(C_reg), 4)` of
the constant-first statement of `l.RHS.term3`, at the absolute pigeonhole constant `4`. -/
theorem termThreeQuadMainConst_nonneg (d : ℕ) (hd : 0 < d) {C0 Creg : ℝ}
    (hC0 : 0 ≤ C0) :
    0 ≤ C0 * quadTailConstMain (streamTailConst d) (nablaW4SqrtConst Creg) 4 :=
  mul_nonneg hC0 (quadTailConstMain_nonneg (le_of_lt (streamTailConst_pos hd))
    (nablaW4SqrtConst_nonneg Creg) (by norm_num))

/-- Nonnegativity of the error quadratic-tail constant
`C3b = C₀ C_err(C_ms, streamTailConst d, C_{∇w,4}(C_reg))` of
the constant-first statement of `l.RHS.term3`. -/
theorem termThreeQuadErrConst_nonneg (d : ℕ) (hd : 0 < d) {C0 Cms Creg : ℝ}
    (hC0 : 0 ≤ C0) (hCms : 0 < Cms) :
    0 ≤ C0 * quadTailConstError Cms (streamTailConst d) (nablaW4SqrtConst Creg) :=
  mul_nonneg hC0 (quadTailConstError_nonneg (le_of_lt hCms)
    (le_of_lt (streamTailConst_pos hd)) (nablaW4SqrtConst_nonneg Creg))

end

end SuperdiffusionCLT.Section3.Terms
