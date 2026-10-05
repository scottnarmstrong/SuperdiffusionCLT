/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section6.Engine.Carriers
public import Homogenization.Sobolev.H1.LocalizedZeroTrace

/-!
# Carriers of the large-scale Lipschitz iteration
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- `‖f‖_{L̲²(S)}` as a real number. -/
noncomputable def lipL2 (S : Set (Vec d)) (f : Vec d → ℝ) : ℝ := (lpBar S 2 f).toReal

/-- `‖F‖_{L̲²(S)}` of a vector field (Euclidean length) as a real number. -/
noncomputable def lipGradL2 (S : Set (Vec d)) (F : Vec d → Vec d) : ℝ :=
  (lpBar S 2 (fun x => eucNorm (F x))).toReal

/-- The pinned flatness `3^{-j} ‖u - c - p·(x - x₀)‖_{L̲²(S)}`. -/
noncomputable def lipPin (S : Set (Vec d)) (j : ℕ) (x₀ : Vec d) (c : ℝ) (u : Vec d → ℝ)
    (p : Vec d) : ℝ :=
  ((3 : ℝ)⁻¹) ^ j * lipL2 S (fun x => u x - c - vecDot p (x - x₀))

/-- **Interior Caccioppoli at the scale `k`**, with loss of `rc` scales: every solution of
`-∇·a∇u = f` on `□_k` with `|f| ≤ F` has
`ν^{1/2} ‖∇u‖_{L̲²(□_{k-rc})} ≤ C (s^{1/2} 3^{-k}‖u - (u)_{□_k}‖_{L̲²(□_k)} + s^{-1/2} 3^k F)`. -/
def LipCaccInt (a : CoeffField d) (nu s C : ℝ) (rc k : ℕ) : Prop :=
  ∀ (f : Vec d → ℝ) (F : ℝ) (u : H1Function (Section6.engCube d k)),
    IsWeakSolutionOn a (Section6.engCube d k) u f (fun _ => 0) → 0 ≤ F →
    (∀ᵐ x ∂volume.restrict (Section6.engCube d k), |f x| ≤ F) →
    Real.sqrt nu * Section6.cubeGradL2 (k - rc) u.grad ≤
      C * (Real.sqrt s * Section6.cubeFlat k u.toFun + (Real.sqrt s)⁻¹ * (3 : ℝ) ^ k * F)

/-- **Interior harmonic approximation at the scale `k`**: every solution of `-∇·a∇u = f` on `□_k`
with `|f| ≤ F` is within `C (δ 3^k · 3^{-k}‖u - (u)‖_{L̲²(□_k)} + s⁻¹ 3^{2k} F)` in `L̲²(□_{k-3})`
of a harmonic function on `□_{k-3}`. -/
def LipHarmInt (a : CoeffField d) (s δ C : ℝ) (k : ℕ) : Prop :=
  ∀ (f : Vec d → ℝ) (F : ℝ) (u : H1Function (Section6.engCube d k)),
    IsWeakSolutionOn a (Section6.engCube d k) u f (fun _ => 0) → 0 ≤ F →
    (∀ᵐ x ∂volume.restrict (Section6.engCube d k), |f x| ≤ F) →
    ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
      Section6.IsSolOn (fun _ => (1 : Mat d)) (Section6.engCube d (k - 3)) w gw ∧
        Section6.cubeL2 (k - 3) (fun x => u.toFun x - w x) ≤
          C * (δ * (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun + s⁻¹ * ((3 : ℝ) ^ k) ^ 2 * F)

/-- **The `L²` homogenization estimate on one domain `V` at the scale `k`** (the display
`e.Dir.new.L2.homog` on `V`, with the exponent `A` in place of `100`). -/
def LipL2Block (a : CoeffField d) (nu s δ C : ℝ) (A k : ℕ) (V : Set (Vec d)) : Prop :=
  ∀ (f : Vec d → ℝ) (g u ub : H1Function V),
    IsWeakSolutionOn a V u f (fun _ => 0) →
    IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f (fun _ => 0) →
    MemH10 V (fun x => u.toFun x - g.toFun x) → MemH10 V (fun x => ub.toFun x - g.toFun x) →
    ENNReal.ofReal (((3 : ℝ)⁻¹) ^ k) * lpBar V 2 (fun x => u.toFun x - ub.toFun x) ≤
      ENNReal.ofReal (C * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu) *
          lpBar V 2 (fun x => eucNorm (u.grad x)) +
        ENNReal.ofReal (C * ((k : ℝ) ^ A)⁻¹) *
          (lpBar V 2 (fun x => eucNorm (g.grad x)) +
            ENNReal.ofReal ((3 : ℝ) ^ k) *
              lpBar V (ENNReal.ofReal (sobStar d)).conjExponent f)

/-- **Boundary Caccioppoli in local form** at the centre `z` and the scale `j`
(`e.Dir.new.Cacc.boundary` on `(z + □_j) ∩ W`, with the exponent `E` in place of `1000`): the
solution has the boundary values of the `C²` function `γ` on `∂W ∩ (z + □_j)` only. -/
def LipCaccBdry (a : CoeffField d) (nu s C E : ℝ) (W : Set (Vec d)) (z : Vec d) (j : ℕ) : Prop :=
  ∀ (f γ : Vec d → ℝ) (u : H1Function (shiftCube z (j : ℤ) ∩ W)), ContDiff ℝ 2 γ →
    IsWeakSolutionOn a (shiftCube z (j : ℤ) ∩ W) u f (fun _ => 0) →
    LocalizedZeroTraceFunctionOn (shiftCube z (j : ℤ) ∩ W) (shiftCube z (j : ℤ))
      (fun x => u.toFun x - γ x) →
    ENNReal.ofReal nu *
        lpBar (shiftCube z ((j : ℤ) - 1) ∩ W) 2 (fun x => eucNorm (u.grad x)) ^ 2 ≤
      ENNReal.ofReal (C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 (fun x => u.toFun x - γ x) ^ 2 +
        ENNReal.ofReal (C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 f ^ 2 +
        ENNReal.ofReal (C * s) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 (fun x => ‖fderiv ℝ γ x‖) ^ 2 +
        ENNReal.ofReal (C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 (fun x => ‖fderiv ℝ (fderiv ℝ γ) x‖) ^ 2

/-- **The interior Lipschitz estimate between the scales `n < m` at the centre `z`** (the display
`e.Dir.new.C01` for one field, in real numbers): the conclusion of the interior engine, consumed by
the boundary case analysis and by the two targets. -/
def LipIntAt (a : CoeffField d) (nu s C : ℝ) (z : Vec d) (n m : ℕ) : Prop :=
  ∀ (f : Vec d → ℝ) (F : ℝ) (u : H1Function (shiftCube z (m : ℤ))),
    IsWeakSolutionOn a (shiftCube z (m : ℤ)) u f (fun _ => 0) → 0 ≤ F →
    (∀ᵐ x ∂volume.restrict (shiftCube z (m : ℤ)), |f x| ≤ F) →
    (Real.sqrt s)⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (n : ℤ)) u.grad +
        ((3 : ℝ)⁻¹) ^ n * lipL2 (shiftCube z (n : ℤ))
          (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ), u.toFun w) ≤
      C * (((3 : ℝ)⁻¹) ^ m * lipL2 (shiftCube z (m : ℤ))
          (fun x => u.toFun x - ⨍ w in shiftCube z (m : ℤ), u.toFun w) +
        s⁻¹ * (3 : ℝ) ^ m * F)

/-- Witness: for zero data the zero function solves on every cube, so the blocks speak about a
nonempty class of solutions. -/
example (a : CoeffField d) (k : ℕ) :
    IsWeakSolutionOn a (Section6.engCube d k) (0 : H10Function (Section6.engCube d k)).toH1Function
      0 0 := by
  intro φ
  have h0 : ∀ x, (0 : H10Function (Section6.engCube d k)).toH1Function.grad x = 0 := fun _ => rfl
  simp [vecDot, matVecMul, h0]

end SuperdiffusionCLT.Section7
