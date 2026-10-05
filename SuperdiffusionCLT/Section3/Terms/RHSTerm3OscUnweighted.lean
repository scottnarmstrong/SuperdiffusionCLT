/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Duality
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Energy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCarriers
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC

/-!
# The unweighted order-one test norm, and the per-cube Poincare step in it

The duality step and the per-cube Poincare step of `e.RHS.term3.B` write the same
first factor, the printed bracket `[∇w − (∇w)_{z+\cu_n}]_{H̲¹}`.  This module reads
it with the **unweighted** order-one test class
`‖∇g‖_{L̲²(Q)} + ‖∇²g‖_{L̲²(Q)} ≤ 1`: the scaled class with
`|Q|^{1/d} = 3^{scale Q}` dropped from the Hessian summand.

## The readings of the bracket

The normalized norm is `‖f‖_{L̲^p(U)} := (⍍_U |f|^p)^{1/p}`.  The *full* norm adds
the zeroth-order term, weighted by `|U|^{-p/d}`.  The *seminorm*
`[f]_{W̲^{1,p}(U)} := ‖∇f‖_{L̲^p(U)}` drops that term and with it the
`|U|^{-p/d}`.  The first factor of the duality step is the bracket, so on
`U = z + \cu_n` it is `‖∇²w‖_{L̲²(U)}` — neither `3^{-n}` nor `3^{n}`; the
right-hand side of the Poincare step is the bare normalized `L̲³` Hessian norm,
with no power of `3`, and its only `3` is the envelope decay `3^{-3ℓ'}`.  So the
seminorm reading makes the Poincare step consistent **with `C = 1`**, while the
scaled two-summand reading is off by exactly `3^{3n}` there, which must come from
the flux side.

The scale-free Poincare step with constant one holds at the seminorm carrier
`oscH1SeminormAt H R = ‖∇²v‖_{L̲²(R)}`: `‖·‖_{L̲²} ≤ ‖·‖_{L̲³}` on a probability
measure supplies `C = 1` with no scale factor.  It does not hold with a `d`-only
constant at the centered-gradient carrier, because the per-cube
step there carries the scale, `oscPoincareConst d n = (termTwoPoincareConst d · 3^n)³`:
in the coercive regime the display forces `Cpo ≥ (c · 3^n)³` for every scale at
once.

## Main results

* `vecHatTestUnwNorm`: the unweighted order-one test norm.
* `oscH1SeminormAt`: the seminorm carrier on a sub-cube.
* `oscH1SeminormAt_avsum_le_hessCubeThree`: the per-cube Poincare average at the
  seminorm carrier, with constant one.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (euclideanGradientJacobian euclideanGradientJacobian_zero)

noncomputable section

variable {d : ℕ}

/-! ## The unweighted order-one test norm -/

/-- **The unweighted order-one test norm** `‖∇g‖_{L̲²(Q)} + ‖∇²g‖_{L̲²(Q)}`: the
scaled `vecHatTestH1ENorm` with the side length `3^{scale Q}` dropped from
the Hessian summand.  This is the test quantity of the convention in which the
printed displays are read with no `3^{±n}` anywhere in the `H̲¹` factor. -/
def vecHatTestUnwNorm (Q : TriadicCube d) (g : Vec d → ℝ) : ℝ≥0∞ :=
  vecCubeLpENorm Q 2 (euclideanGradient g) +
    cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (euclideanGradientJacobian g x))

@[simp] theorem vecHatTestUnwNorm_zero (Q : TriadicCube d) :
    vecHatTestUnwNorm Q (fun _ : Vec d => (0 : ℝ)) = 0 := by
  have hgrad : euclideanGradient (fun _ : Vec d => (0 : ℝ))
      = fun _ : Vec d => (0 : Vec d) := by
    funext x i
    simp [euclideanGradient, euclideanCoordDeriv]
  have hjac : (fun x : Vec d =>
      HilbertMat.ofMat (euclideanGradientJacobian (fun _ : Vec d => (0 : ℝ)) x))
      = (0 : Vec d → HilbertMat d) := by
    funext x
    rw [euclideanGradientJacobian_zero]
    ext i j
    rfl
  rw [vecHatTestUnwNorm, hgrad, hjac, vecCubeLpENorm_zero,
    cubeLpENorm_zero, add_zero]

/-! ## The unweighted test class and the unweighted hatted negative norm -/

/-! ## The bare seminorm carrier and the unweighted two-summand carrier

The seminorm of the centered gradient, read literally, is
`‖∇(∇w − (∇w)_Q)‖_{L̲²(Q)} = ‖∇²w‖_{L̲²(Q)}`: the Hessian norm — the primal
partner of the coefficient the print uses in the duality and Poincare steps. -/

/-! ## The duality against the unweighted norm -/

/-! ## The smooth unweighted test potential of a centered gradient -/

/-! ## The duality display at the unweighted carrier -/

/-! ## The per-cube Poincare at the seminorm carrier

The bracket `[∇w − (∇w)_R]_{H̲¹(R)} = ‖∇²w‖_{L̲²(R)}`, read on every
sub-cube `R`, is `oscH1SeminormAt H R` below, and against the bare normalized
`L̲³` Hessian norm the per-cube Poincare display then needs **no** constant. -/

/-- **The seminorm carrier on a sub-cube `R`**: the normalized `L̲²` norm
of the weak Hessian of the response, in real form.  No power of `3`, no
zeroth-order summand. -/
def oscH1SeminormAt {m : ℕ} {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v)
    (R : TriadicCube d) : ℝ :=
  (Section2.Norms.cubeLpENorm R 2
    (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal

/-- **The per-cube Poincare average at the seminorm carrier, with constant one.**
The average of the cubed seminorms over the scale-`n` sub-cubes of `cu_m` is dominated by the cubed
normalized `L̲³` Hessian norm of `cu_m`, with no scale factor and no constant at
all.  The per-cube step `oscH1Carrier_poincare` needs
`termTwoPoincareConst d · 3^n` because it is taken at `oscH1Carrier`, the
zeroth-order object, which is only bounded by `3^n` times this one; at
the seminorm that whole factor is gone. -/
theorem oscH1SeminormAt_avsum_le_hessCubeThree {n m : ℕ}
    {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v) :
    ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)⁻¹) *
        ∑ R ∈ largeCubeSubcubes d n m, (ENNReal.ofReal (oscH1SeminormAt H R)) ^ (3 : ℕ) ≤
      (Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 3
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))) ^ (3 : ℕ) := by
  have htile := cubeLpENorm_three_pow_eq_inv_card_mul_sum (Q := originCube d (m : ℤ))
    (m - n) (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
  rw [← largeCubeSubcubes_eq_descendantsAtDepth n m] at htile
  refine le_trans (b := ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)⁻¹) *
      ∑ R ∈ largeCubeSubcubes d n m,
        (Section2.Norms.cubeLpENorm R 3
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))) ^ (3 : ℕ))
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => ?_) bot_le) ?_
  · have hmono : Section2.Norms.cubeLpENorm R 2
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≤
        Section2.Norms.cubeLpENorm R 3
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) :=
      cubeLpENorm_mono_exponent R (by norm_num)
        (aestronglyMeasurable_hessMat_of_weakHessian_subcube H hR)
    exact pow_le_pow_left' (le_trans
      (by rw [oscH1SeminormAt]; exact ENNReal.ofReal_toReal_le) hmono) 3
  · rw [← htile]

/-! ## The Poincare display is false at `Raw`: the arithmetic

The per-cube estimate at the `Raw` carrier carries the scale,
`oscPoincareConst d n = (termTwoPoincareConst d · 3^n)³`, and its per-cube step
`oscH1Carrier_poincare` reads `Raw ≤ termTwoPoincareConst d · 3^n ·
‖∇²v‖_{L̲²(R)}`.  So in the coercive regime — centered gradient of size
`c · 3^n · mass`, weak Hessian of cube-independent normalized size `mass` — the
display at `Raw` forces `Cpo ≥ (c · 3^n)³` for every scale `n` at once, while
`Cpo` is quantified before `S` and so depends on `d` alone; `3^{3n}` is unbounded
and no such `Cpo` exists.  This is the *same* arithmetic that refutes the scaled
two-summand reading: the unweighted convention does not repair it, since the
missing `3^{R.scale}` was on the test-class side and the zeroth-order summand
reintroduces that scale through the per-cube Poincare inequality itself. -/

end

end SuperdiffusionCLT.Section3.Terms
