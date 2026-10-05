/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.DirichletExistence
public import Homogenization.Sobolev.Foundations.AxisCube
public import Homogenization.Sobolev.W1p.Definitions

/-!
# Basic definitions for the Section 7 analytic inputs

Weak solutions on a set tested against `H¹₀`, the Euclidean norm, the Sobolev exponent `2^*`,
the concentric half cube, and the normalized `L^p` and `W^{-1,p}` norms.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Weak solution of `-∇·(a∇u) = f - ∇·g` in `U` (the convention of
`Section7.IsH10WeakSolution`), for an `H¹` function tested against `H¹₀(U)`. -/
def IsWeakSolutionOn (a : CoeffField d) (U : Set (Vec d)) (u : H1Function U) (f : Vec d → ℝ)
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function U,
    ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) =
      (∫ x in U, f x * φ.toH1Function.toFun x) + ∫ x in U, vecDot (g x) (φ.toH1Function.grad x)

/-- Euclidean norm of a vector. -/
noncomputable def eucNorm (v : Vec d) : ℝ := Real.sqrt (vecNormSq v)

/-- The Sobolev exponent `2^*` (`e.Dir.new.Sobolev.conjugates`). -/
noncomputable def sobStar (d : ℕ) : ℝ := if d = 2 then 6 else 2 * d / (d - 2)

/-- The concentric half cube of `axisCube z L`. -/
def halfCube (z : Vec d) (L : ℝ) : Set (Vec d) := axisCube (z + fun _ => L / 4) (L / 2)

/-- Normalized `L^p` norm on a set (part A's `lpBar`). -/
noncomputable def lpBar {E : Type*} [NormedAddCommGroup E] (V : Set (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → E) : ℝ≥0∞ :=
  eLpNorm F p (((volume V)⁻¹) • volume.restrict V)

/-- Normalized `W^{-1,p}(V)` seminorm of a scalar `h`: dual to the `H¹₀(V)` functions whose
gradient has normalized `L^{p'}` norm at most one (the class `W^{1,p'}_0` without a density
theorem; equal to it on smooth domains). -/
noncomputable def wMinusOneBar (V : Set (Vec d)) (p : ℝ≥0∞) (h : Vec d → ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : H10Function V) (_ : lpBar V p.conjExponent ψ.toH1Function.grad ≤ 1),
    ENNReal.ofReal |(volume V).toReal⁻¹ * ∫ x in V, h x * ψ.toH1Function.toFun x|

theorem isWeakSolutionOn_iff (a : CoeffField d) (U : Set (Vec d)) (f : Vec d → ℝ)
    (g : Vec d → Vec d) (u : H10Function U) :
    IsH10WeakSolution a U f g u ↔ IsWeakSolutionOn a U u.toH1Function f g := Iff.rfl

theorem sobStar_two : sobStar 2 = 6 := by simp [sobStar]

theorem two_lt_sobStar (hd : 2 ≤ d) : 2 < sobStar d := by
  unfold sobStar
  split_ifs with h
  · norm_num
  · have h3 : (3 : ℝ) ≤ d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    rw [lt_div_iff₀ (by linarith only [h3])]
    linarith only [h3]

theorem inv_sobStar (hd : 3 ≤ d) : (sobStar d)⁻¹ = 1 / 2 - 1 / d := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith only [h3]
  have hd2 : (d : ℝ) - 2 ≠ 0 := by linarith only [h3]
  have : d ≠ 2 := by omega
  simp only [sobStar, this, ite_false]
  field_simp

theorem halfCube_subset (z : Vec d) (L : ℝ) : halfCube z L ⊆ axisCube z L := by
  intro x hx j _
  have h := hx j (Set.mem_univ j)
  simp only [Set.mem_Ioo, Pi.add_apply] at h ⊢
  have hL : 0 < L := by
    by_contra hc
    have hc : L ≤ 0 := not_lt.mp hc
    linarith only [h.1, h.2, hc]
  constructor <;> linarith only [h.1, h.2, hL]

/-- Witness: zero is a weak solution with zero data. -/
example (a : CoeffField d) (U : Set (Vec d)) :
    IsWeakSolutionOn a U (0 : H10Function U).toH1Function 0 0 := by
  intro φ
  have h0 : ∀ x, (0 : H10Function U).toH1Function.grad x = 0 := fun _ => rfl
  simp [vecDot, matVecMul, h0]

/-- Witness: the half cube of the unit cube is nonempty. -/
example : (halfCube (0 : Vec 2) 1).Nonempty :=
  ⟨fun _ => 1 / 2, fun j _ => by simp only [Pi.add_apply, Pi.zero_apply, Set.mem_Ioo]; constructor <;> norm_num⟩

end SuperdiffusionCLT.Section7
