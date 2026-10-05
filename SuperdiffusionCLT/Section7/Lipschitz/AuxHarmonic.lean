/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionB
public import SuperdiffusionCLT.Section7.Prereq.WellPosed
public import SuperdiffusionCLT.Section7.Analytic.Regularity.MaxPrincipleB

/-!
# The auxiliary `a`-harmonic function with the boundary values of a smooth datum

On a bounded open set with an elliptic field, the weak solution `w` of the homogeneous problem with
`w - ψ ∈ H¹₀` exists and is bounded by `sup |ψ|` (weak maximum principle for `w` and `-w`).
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The zero function is a weak solution with zero data. -/
theorem lip_aux_zero_solution (a : CoeffField d) (D : Set (Vec d)) :
    IsWeakSolutionOn a D (0 : H1Function D) 0 0 := by
  intro φ
  have h0 : ∀ x, (0 : H1Function D).grad x = 0 := fun _ => rfl
  simp [vecDot, matVecMul, h0]

/-- **The auxiliary problem** (`u - u_k`): the `a`-harmonic function with
the boundary values of `ψ`, and the weak maximum principle. -/
theorem lip_aux (d : ℕ) [NeZero d] (a : CoeffField d) {lam Lam : ℝ} (D : Set (Vec d))
    (hDo : IsOpen D) (hDb : IsBoundedDomain D) (hEll : IsEllipticFieldOn lam Lam D a)
    (ψ : Vec d → ℝ) (Mψ : ℝ) (hψ : ContDiff ℝ 2 ψ) (hM : ∀ x, |ψ x| ≤ Mψ) :
    ∃ w : H1Function D, IsWeakSolutionOn a D w 0 0 ∧
      MemH10 D (fun x => w.toFun x - ψ x) ∧
      ∀ᵐ x ∂volume.restrict D, |w.toFun x| ≤ Mψ := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  set g : H1Function D := li1_h1 hDo hDb hψ1 with hg
  have hgf : g.toFun = ψ := rfl
  obtain ⟨w, hw, hwb⟩ := w0_dirichlet_exists hDo hDb hEll (f := 0) (MeasureTheory.MemLp.zero) g
  have hw0 : IsWeakSolutionOn a D w 0 0 := hw
  rw [hgf] at hwb
  have hz := lip_aux_zero_solution a D
  refine ⟨w, hw0, hwb, ?_⟩
  have hup := weakMaxPrinciple_comparison hDo hDb hEll w 0 g 0 hw0 hz
    (by simpa [hgf] using hwb) (c := Mψ) (fun x => by
      simpa [hgf] using (abs_le.1 (hM x)).2)
  have hdown := weakMaxPrinciple_comparison hDo hDb hEll 0 w 0 g hz hw0
    (by
      have e : (fun x => (0 : H1Function D).toFun x - w.toFun x
          - ((0 : H1Function D).toFun x - g.toFun x)) = fun x => -(w.toFun x - ψ x) := by
        funext x
        rw [hgf]
        change (0 : ℝ) - w.toFun x - (0 - ψ x) = _
        ring
      rw [e]
      exact memH10_neg hwb) (c := Mψ) (fun x => by
      simpa [hgf] using neg_le.1 (abs_le.1 (hM x)).1)
  filter_upwards [hup, hdown] with x h1 h2
  have h0 : (0 : H1Function D).toFun x = 0 := rfl
  rw [h0] at h1 h2
  rw [abs_le]
  constructor <;> linarith only [h1, h2]

/-- Witness: zero datum on the unit ball with identity coefficients (the zero function solves). -/
example : ∃ w : H1Function (Metric.ball (0 : Vec 2) 1),
    IsWeakSolutionOn (fun _ => (1 : Mat 2)) (Metric.ball (0 : Vec 2) 1) w 0 0 ∧
      MemH10 (Metric.ball (0 : Vec 2) 1) (fun x => w.toFun x - (fun _ : Vec 2 => (0 : ℝ)) x) ∧
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec 2) 1), |w.toFun x| ≤ 0 := by
  refine ⟨0, lip_aux_zero_solution _ _, ?_, ?_⟩
  · have h := memH10_zero (U := Metric.ball (0 : Vec 2) 1)
    convert h using 1
    funext x
    exact sub_zero _
  · exact Filter.Eventually.of_forall fun x => by simp

end SuperdiffusionCLT.Section7
