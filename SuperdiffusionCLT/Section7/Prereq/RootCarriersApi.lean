/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section7.Analytic.Geometry.WhitneyBallB
public import SuperdiffusionCLT.Section7.Analytic.Change.Dilation
public import SuperdiffusionCLT.Section7.MinimalScale.GridMax
public import SuperdiffusionCLT.Section6.Prereq.EuclidBall

/-!
# Basic facts about the statement carriers

The reference ball lies in the unit cube, translated cubes are axis cubes, the Whitney interior
is measurable and contained in its domain, and the Dirichlet problem is stable under scaling of
the coefficient field and the right-hand side and under dilation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-! ### Cubes -/

/-- Coordinatewise description of a translated cube. -/
theorem rc_mem_shiftCube {y x : Vec d} {m : ℤ} :
    x ∈ shiftCube y m ↔ ∀ i, |x i - y i| < (3 : ℝ) ^ m / 2 := wpd_mem_shiftCube

/-- A translated triadic cube is an axis cube of side `3^m`. -/
theorem rc_shiftCube_eq_axisCube (y : Vec d) (m : ℤ) :
    shiftCube y m = axisCube (fun i => y i - (3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m) := by
  ext x
  rw [rc_mem_shiftCube, axisCube, Set.mem_pi]
  refine forall_congr' fun i => ?_
  simp only [Set.mem_univ, true_implies, Set.mem_Ioo, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

/-- A translated cube is open. -/
theorem rc_isOpen_shiftCube (y : Vec d) (m : ℤ) : IsOpen (shiftCube y m) := by
  rw [rc_shiftCube_eq_axisCube]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

/-- A translated cube is measurable. -/
theorem rc_measurableSet_shiftCube (y : Vec d) (m : ℤ) : MeasurableSet (shiftCube y m) :=
  (rc_isOpen_shiftCube y m).measurableSet

/-- The cube translated by the origin is the origin cube. -/
theorem rc_shiftCube_zero (m : ℤ) : shiftCube (0 : Vec d) m = openCubeSet (originCube d m) := by
  simp [shiftCube]

/-- The translated cube `y + cu_m` contains `y`. -/
theorem rc_mem_shiftCube_self (y : Vec d) (m : ℤ) : y ∈ shiftCube y m := by
  rw [rc_mem_shiftCube]
  intro i
  simp only [sub_self, abs_zero]
  positivity

/-- The Whitney interior of `V` is contained in `V`. -/
theorem rc_whitneyInterior_subset (V : Set (Vec d)) (j : ℤ) : whitneyInterior V j ⊆ V := by
  intro x hx
  simp only [whitneyInterior, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨k, ⟨_, hsub⟩, hxk⟩ := hx
  apply hsub
  rw [rc_mem_shiftCube]
  have hc := (wpd_mem_cellImage (x := x) (j := j) k).1 hxk
  intro i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have h27 : (3 : ℝ) ^ (j + 3) = 27 * (3 : ℝ) ^ j := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  rw [h27, abs_lt]
  obtain ⟨h1, h2⟩ := hc i
  constructor <;> linarith only [h1, h2, h3]

/-- The Whitney interior is measurable (a countable union of translated cubes). -/
theorem rc_measurableSet_whitneyInterior (V : Set (Vec d)) (j : ℤ) :
    MeasurableSet (whitneyInterior V j) := by
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
  exact (MeasurableEquiv.addLeft (fun i => (3 : ℝ) ^ j * (k i : ℝ))).measurableEmbedding.measurableSet_image'
    (Homogenization.measurableSet_cubeSet _)

/-- The origin is a grid point: the centered case of the translated statements. -/
theorem rc_zero_mem_gridPts (j : ℤ) {R : ℝ} (hR : 0 ≤ R) : (0 : Vec d) ∈ gridPts d j R := by
  rw [mem_gridPts hR]
  exact ⟨fun _ => 0, fun i => by simp, fun i => by simpa using hR⟩

/-- Witness: the Whitney interior of the unit ball at scale `0` is nonempty-or-empty consistent
with measurability and containment (the origin cell is present when its cube fits). -/
example : MeasurableSet (whitneyInterior (SuperdiffusionCLT.Section6.euclidBall (d := 2) 1) 0) ∧
    whitneyInterior (SuperdiffusionCLT.Section6.euclidBall (d := 2) 1) 0 ⊆
      SuperdiffusionCLT.Section6.euclidBall (d := 2) 1 :=
  ⟨rc_measurableSet_whitneyInterior _ _, rc_whitneyInterior_subset _ _⟩

/-! ### The Dirichlet problem -/

/-- The zero function solves the Dirichlet problem with zero data, for every coefficient. -/
theorem rc_isDirichletSolution_zero (a : CoeffField d) (U : Set (Vec d)) :
    IsDirichletSolution a U (fun _ => 0) (0 : H1Function U) (0 : H1Function U) := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro φ
    have h0 : ∀ x, (0 : H1Function U).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, h0]
  · funext x
    have h1 : (0 : H1Function U).toFun x = 0 := rfl
    have h2 : (0 : H10Function U).toH1Function.toFun x = 0 := rfl
    rw [h1, h2, sub_zero]

/-- Scaling of the coefficient field and the right-hand side of a weak solution. -/
theorem rc_isWeakSolutionOn_smul {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} (c : ℝ) (h : IsWeakSolutionOn a U u f (fun _ => 0)) :
    IsWeakSolutionOn (fun x => c • a x) U u (fun x => c * f x) (fun _ => 0) := by
  have h1 := IsWeakSolutionOn.smul c h
  simpa using h1

/-- Scaling of the coefficient field and the right-hand side of a Dirichlet solution. -/
theorem rc_isDirichletSolution_smul {a : CoeffField d} {U : Set (Vec d)} {u g : H1Function U}
    {f : Vec d → ℝ} (c : ℝ) (h : IsDirichletSolution a U f g u) :
    IsDirichletSolution (fun x => c • a x) U (fun x => c * f x) g u :=
  ⟨rc_isWeakSolutionOn_smul c h.1, h.2⟩

/-- Scaling by a nonzero constant is reversible. -/
theorem rc_isDirichletSolution_smul_iff {a : CoeffField d} {U : Set (Vec d)} {u g : H1Function U}
    {f : Vec d → ℝ} {c : ℝ} (hc : c ≠ 0) :
    IsDirichletSolution (fun x => c • a x) U (fun x => c * f x) g u ↔
      IsDirichletSolution a U f g u := by
  refine ⟨fun h => ?_, rc_isDirichletSolution_smul c⟩
  have h1 := rc_isDirichletSolution_smul c⁻¹ h
  have e1 : (fun x => c⁻¹ • c • a x) = a := by
    funext x
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have e2 : (fun x => c⁻¹ * (c * f x)) = f := by
    funext x
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [e1, e2] at h1
  exact h1

/-- Transfer of a weak solution along pointwise equal data. -/
theorem rc_isWeakSolutionOn_congr {U : Set (Vec d)} {a a' : CoeffField d} {u : H1Function U}
    {f f' : Vec d → ℝ} {g g' : Vec d → Vec d} (ha : ∀ x, a x = a' x) (hf : ∀ x, f x = f' x)
    (hg : ∀ x, g x = g' x) (h : IsWeakSolutionOn a U u f g) : IsWeakSolutionOn a' U u f' g' := by
  have ha' : a = a' := funext ha
  have hf' : f = f' := funext hf
  have hg' : g = g' := funext hg
  subst ha' hf' hg'
  exact h

/-- Dilation of membership in `H¹₀`. -/
theorem rc_memH10_dilate {U : Set (Vec d)} {s : ℝ} (hs : s ≠ 0) {h : Vec d → ℝ}
    (hh : MemH10 U h) : MemH10 (s⁻¹ • U) (fun y => h (s • y)) := by
  obtain ⟨v, hv⟩ := hh
  refine ⟨v.dilateArg hs, ?_⟩
  funext y
  rw [H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun, hv]

/-- **Dilation of the Dirichlet problem.** A solution on `U` for the field
`x ↦ S⁻¹ A(ε⁻¹ x)` gives a solution on `ε⁻¹ • U` for the unscaled field `A`, with right-hand side
`S ε² f(ε ·)` and datum `g(ε ·)`. -/
theorem rc_isDirichletSolution_dilate {U : Set (Vec d)} {A : CoeffField d} {S ε : ℝ}
    (hS : S ≠ 0) (hε : ε ≠ 0) {f : Vec d → ℝ} {g u : H1Function U}
    (h : IsDirichletSolution (fun x => S⁻¹ • A (ε⁻¹ • x)) U f g u) :
    IsDirichletSolution A (ε⁻¹ • U) (fun y => S * ε ^ 2 * f (ε • y))
      (g.dilateArg hε) (u.dilateArg hε) := by
  refine ⟨?_, ?_⟩
  · have h1 := (IsWeakSolutionOn.dilate hε h.1).smul S
    refine rc_isWeakSolutionOn_congr (fun y => ?_) (fun y => ?_) (fun y => ?_) h1
    · simp only [smul_smul, inv_smul_smul₀ hε]
      rw [mul_inv_cancel₀ hS, one_smul]
    · ring
    · simp
  · have h2 := rc_memH10_dilate hε h.2
    convert h2 using 1
    funext y
    rw [H1Function.dilateArg_toFun, H1Function.dilateArg_toFun]

/-- **Dilation of the Laplace problem**: a solution for the identity field on `U` gives one for
`S • Id` on `ε⁻¹ • U`, with right-hand side `S ε² f(ε ·)`. -/
theorem rc_isDirichletSolution_dilate_const {U : Set (Vec d)} {S ε : ℝ} (hε : ε ≠ 0)
    {f : Vec d → ℝ} {g u : H1Function U}
    (h : IsDirichletSolution (fun _ => (1 : Mat d)) U f g u) :
    IsDirichletSolution (fun _ => S • (1 : Mat d)) (ε⁻¹ • U)
      (fun y => S * ε ^ 2 * f (ε • y)) (g.dilateArg hε) (u.dilateArg hε) := by
  refine ⟨?_, ?_⟩
  · have h1 := (IsWeakSolutionOn.dilate hε h.1).smul S
    refine rc_isWeakSolutionOn_congr (fun y => ?_) (fun y => ?_) (fun y => ?_) h1
    · simp
    · ring
    · simp
  · have h2 := rc_memH10_dilate hε h.2
    convert h2 using 1
    funext y
    rw [H1Function.dilateArg_toFun, H1Function.dilateArg_toFun]

/-- **Dilation for the rescaled field.** A solution for `S⁻¹ a^ε` on `U` gives a solution for the
unscaled recentered field `ν Id + (k - k(0))` on `ε⁻¹ • U`. -/
theorem rc_isDirichletSolution_dilate_epField {U : Set (Vec d)} {S ε nu : ℝ}
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (hS : S ≠ 0) (hε : ε ≠ 0)
    {f : Vec d → ℝ} {g u : H1Function U}
    (h : IsDirichletSolution (fun x => S⁻¹ • epField nu omega ε x) U f g u) :
    IsDirichletSolution (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
      (ε⁻¹ • U) (fun y => S * ε ^ 2 * f (ε • y)) (g.dilateArg hε) (u.dilateArg hε) :=
  rc_isDirichletSolution_dilate hS hε h

end SuperdiffusionCLT.Section7
