/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaF

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Transport of a zero-trace solution supported near the face to the half cube

An `H¹₀(U)` function whose smooth approximants are supported in an open subset `V ⊆ U` is in `H¹₀(V)`
(with the same representatives); translating `V` onto `flatHalfCube e m` carries a weak solution of a
scalar equation to a weak solution of the translated equation.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Restriction of an `H¹₀(U)` function to an open `V ⊆ U` containing the supports of its
approximants. -/
noncomputable def r3c_h10Restrict {U V : Set (Vec d)} (W : H10Function U) (hV : IsOpen V)
    (hVU : V ⊆ U) (hsupp : ∀ n, tsupport (W.approx n) ⊆ V) : H10Function V where
  toH1Function := W.toH1Function.restrict hV hVU
  approx := W.approx
  approx_smooth := W.approx_smooth
  approx_hasCompactSupport := W.approx_hasCompactSupport
  approx_support_subset := hsupp
  tendsto_approx := by
    have hle : (volume.restrict V : Measure (Vec d)) ≤ volume.restrict U :=
      Measure.restrict_mono hVU le_rfl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds W.tendsto_approx
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hle)
  tendsto_approx_grad := fun i => by
    have hle : (volume.restrict V : Measure (Vec d)) ≤ volume.restrict U :=
      Measure.restrict_mono hVU le_rfl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (W.tendsto_approx_grad i)
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hle)

theorem r3c_isWeakSolutionOn_castSet {a : CoeffField d} {S T : Set (Vec d)} (h : S = T)
    {u : H1Function S} {f : Vec d → ℝ} {g : Vec d → Vec d} (hu : IsWeakSolutionOn a S u f g) :
    IsWeakSolutionOn a T (u.castSet h) f g := by
  subst h
  exact hu

theorem r3c_translateSet_halfCube (e : Fin d) (m : ℤ) (z : Vec d) :
    translateSet z {x : Vec d | x + z ∈ flatHalfCube e m} = flatHalfCube e m := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  simp only [Set.mem_ofPred_eq, sub_add_cancel]

/-- **Transport to the half cube.** -/
theorem r3c_transport (e : Fin d) (m : ℤ) (z : Vec d) {U : Set (Vec d)} (hU : IsOpen U)
    {A : CoeffField d} {F : Vec d → ℝ} (w : H10Function U)
    (hVU : {x : Vec d | x + z ∈ flatHalfCube e m} ⊆ U)
    (hsupp : ∀ n, tsupport (w.approx n) ⊆ {x : Vec d | x + z ∈ flatHalfCube e m})
    (hsol : IsWeakSolutionOn A U w.toH1Function F (fun _ => 0)) :
    ∃ wV : H10Function (flatHalfCube e m),
      (∀ x, wV.toH1Function.toFun x = w.toH1Function.toFun (x - z)) ∧
      (∀ x, wV.toH1Function.grad x = w.toH1Function.grad (x - z)) ∧
      IsH10WeakSolution (fun x => A (x - z)) (flatHalfCube e m) (fun x => F (x - z))
        (fun _ => 0) wV := by
  set V : Set (Vec d) := {x : Vec d | x + z ∈ flatHalfCube e m} with hVdef
  have hV : IsOpen V := (isOpen_flatHalfCube e m).preimage (continuous_id.add continuous_const)
  set wR : H10Function V := r3c_h10Restrict w hV hVU hsupp with hwR
  have hsolR := p12_restrict_weak hU hV hVU hsol
  have hT := IsWeakSolutionOn.translate z hsolR
  have hS := r3c_translateSet_halfCube e m z
  refine ⟨(wR.translate z).castSet hS, fun x => ?_, fun x => ?_, ?_⟩
  · rw [H10Function.castSet_toH1Function, H1Function.castSet_toFun, H10Function.translate_toH1Function,
      H1Function.translate_toFun]
    rfl
  · rw [H10Function.castSet_toH1Function, H1Function.castSet_grad, H10Function.translate_toH1Function,
      H1Function.translate_grad]
    rfl
  · have := r3c_isWeakSolutionOn_castSet hS hT
    intro φ
    have h2 := this φ
    rw [H10Function.castSet_toH1Function, H10Function.translate_toH1Function]
    exact h2

end SuperdiffusionCLT.Section7
