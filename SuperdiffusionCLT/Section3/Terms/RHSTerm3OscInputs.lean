/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCg
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RBounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays

/-!
# `hOscBound`: the carrier of `oscH1` and the per-cube Poincaré step

The second display of the proof of `e.RHS.term3.B`, whose first inequality is
the per-cube Poincaré inequality for the *centered* gradient on `z + cu_n`.

`Section3/Terms/RHSTerm3OscCg.lean` discharges the second inequality of that
display from the second clause of `e.nablaw.Lt`, but it keeps `oscH1` a free
binder and the per-cube Poincaré step a hypothesis `hPoincare`.  This module
gives `oscH1` an actual carrier and proves the per-cube step at it:

* `oscH1Carrier`: the normalized `L̲²` norm on the translated cube `R` of the
  centered gradient `∇w − (∇w)_R` of the response field — the quantity the
  print denotes `[∇w − (∇w)_{z+cu_n}]_{H̲¹(z+cu_n)}` up to the coercive
  constant, in the carrier of `poincare_per_subcube`
  (`Section3/Terms/RHSTerm2AnchorsConstFirst.lean`).
* `oscH1Carrier_poincare`: the per-cube Poincaré step
  `[∇w − (∇w)_R]³ ≤ C · ‖∇²w‖³_{L̲³(R)}` on every scale-`n` sub-cube of `cu_m`,
  at the constant `oscPoincareConst d n = (termTwoPoincareConst d · 3^n)³` of
  the coercive estimate.

The remaining side conditions — the measurability in the sample of the carrier
and the discharge of the clause of `e.nablaw.Lt` — are the next items; they are
not attempted here.
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
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The carrier of `oscH1` -/

/-- **The carrier of `oscH1`**: the normalized `L̲²` norm on the translated
cube `R` of the centered gradient `∇w − (∇w)_R` of the response field.  This is
the quantity the print denotes `[∇w − (∇w)_{z+cu_n}]_{H̲¹(z+cu_n)}` and estimates
by the per-cube Poincaré inequality, read in the carrier of
`poincare_per_subcube`: the coercive estimate of the centered unit cube scales
by the side length of `R` and is fed the weak Hessian as the gradient datum of
the components of `∇w`. -/
def oscH1Carrier {m : ℕ} (v : H1Function (openCubeSet (originCube d (m : ℤ))))
    (R : TriadicCube d) : ℝ≥0∞ :=
  vecCubeLpENorm R 2
    (fun x => v.grad x - volumeAverageVec (openCubeSet R) v.grad)

/-! ## The weak Hessian as the gradient datum of `∇w` -/

/-- The Hilbert-matrix realization of a weak Hessian, as an `L²` field for the
restricted volume of the cube. -/
theorem memLp_hessMat_of_weakHessian (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) :
    MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) 2
      (volume.restrict (openCubeSet Q)) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  rw [MeasureTheory.memLp_piLp_iff]
  intro j
  simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec, PiLp.toLp_apply]
    using H.hess_memL2 i j

/-- The weak Hessian of an `H¹` function is the weak gradient of each
component of its gradient. -/
theorem hasWeakGradient_hess_of_weakHessian (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v) (i : Fin d) :
    HasWeakGradientOn (openCubeSet Q) (fun x => v.grad x i) (fun x j => H.hess i j x) :=
  fun j => H.weak_second i j

/-- The gradient of an `H¹` function is an `L²` vector field on the cube. -/
theorem memVectorL2_of_gradMemL2On (U : Set (Vec d)) {g : Vec d → Vec d}
    (hg : GradMemL2On U g) : MemVectorL2 U g :=
  MeasureTheory.MemLp.of_eval hg

/-! ## The per-cube Poincaré step at the carrier -/

/-- The measurability of the weak Hessian for the normalized cube measure of a
sub-cube of the cube the `H¹` function lives on, the input of the exponent
monotonicity of the normalized cube norm. -/
theorem aestronglyMeasurable_hessMat_of_weakHessian_subcube {m : ℕ}
    {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v)
    {n : ℕ} {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) :
    AEStronglyMeasurable (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
      (normalizedCubeMeasure R) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact ((memLp_subcube hR (memLp_hessMat_of_weakHessian _ H)).smul_measure
    ENNReal.ofReal_ne_top).aestronglyMeasurable

/-- **The per-cube Poincaré step at the carrier**: on every scale-`n` sub-cube
`R` of `cu_m`, the centered-gradient carrier of `oscH1` is dominated by the
scaled coercive constant times the normalized `L̲²` norm of the weak Hessian on
`R` — the first inequality of the second display of `e.RHS.term3.B`, read at the
carrier of `poincare_per_subcube`. -/
theorem oscH1Carrier_poincare {n m : ℕ} (hnm : n ≤ m)
    {v : H1Function (openCubeSet (originCube d (m : ℤ)))}
    (H : HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) v)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) :
    oscH1Carrier v R ≤
      ENNReal.ofReal (termTwoPoincareConst d * (3 : ℝ) ^ ((n : ℕ) : ℝ)) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm R 2
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) :=
  poincare_per_subcube hnm (memVectorL2_of_gradMemL2On _ v.gradMemL2)
    (memLp_hessMat_of_weakHessian _ H) (hasWeakGradient_hess_of_weakHessian _ H) R hR

end

end SuperdiffusionCLT.Section3.Terms