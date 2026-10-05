/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.MaxPrinciple
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.Matched

/-!
# Comparison form of the weak maximum principle

Two weak solutions `u`, `v` whose difference is `g - g̃` modulo `H¹₀(U)`, with `g - g̃ ≤ c`
everywhere, satisfy `u - v ≤ c` almost everywhere.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

/-- The difference of two weak solutions with zero data is a weak solution with zero data. -/
theorem isWeakSolutionOn_sub {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {u v : H1Function U}
    (hu : IsWeakSolutionOn a U u 0 0) (hv : IsWeakSolutionOn a U v 0 0) :
    IsWeakSolutionOn a U (u - v) 0 0 := by
  intro φ
  have hint : ∀ w : H1Function U, MeasureTheory.IntegrableOn
      (fun x => vecDot (matVecMul (a x) (w.grad x)) (φ.toH1Function.grad x)) U :=
    fun w => integrableOn_vecDot_of_memVectorL2
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.grad_memVectorL2)
      φ.toH1Function.grad_memVectorL2
  have h1 := hu φ
  have h2 := hv φ
  have hsplit : (fun x => vecDot (matVecMul (a x) ((u - v).grad x)) (φ.toH1Function.grad x)) =
      fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
        vecDot (matVecMul (a x) (v.grad x)) (φ.toH1Function.grad x) := by
    funext x
    simp only [H1Function.sub_grad, Pi.sub_apply, vecDot, matVecMul, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rw [hsplit, integral_sub (hint u) (hint v), h1, h2]
  simp [vecDot]

/-- Comparison form of the weak maximum principle: the difference of two weak solutions is at
most `c` when its distance to the boundary datum `g - g̃ ≤ c` lies in `H¹₀(U)`.  The bound
`g - g̃ ≤ c` holds at every point, since `MemH10` is an equality of functions. -/
theorem weakMaxPrinciple_comparison [NeZero d] (hU : IsOpen U) (hUb : IsBoundedDomain U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    (u v g g' : H1Function U) (hu : IsWeakSolutionOn a U u 0 0)
    (hv : IsWeakSolutionOn a U v 0 0)
    (hbd : MemH10 U (fun x => u.toFun x - v.toFun x - (g.toFun x - g'.toFun x)))
    {c : ℝ} (hc : ∀ x, g.toFun x - g'.toFun x ≤ c) :
    ∀ᵐ x ∂(volume.restrict U), u.toFun x - v.toFun x ≤ c := by
  have hfin := volume_ne_top_of_isBoundedDomain hUb
  have hm := openH10Matched d hU hfin (u - v) (g - g') (by simpa using hbd) c
  have hfun : (fun x => max ((u - v).toFun x - c) 0 - max ((g - g').toFun x - c) 0) =
      fun x => max ((u - v).toFun x - c) 0 := by
    funext x
    have : max ((g - g').toFun x - c) 0 = 0 := by
      simp only [H1Function.sub_toFun]
      exact max_eq_right (by linarith only [hc x])
    rw [this, sub_zero]
  rw [hfun] at hm
  have := weakMaxPrinciple_core hU hUb hEll (u - v) (isWeakSolutionOn_sub hEll hu hv) hm
  simpa using this

/-- Witness: the zero function satisfies the hypotheses of the maximum principle on the unit
ball (identity coefficients), with `M = 0`. -/
example : MemH10 (Metric.ball (0 : Vec 2) 1)
    (fun x => max ((0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun x - 0) 0) ∧
    IsWeakSolutionOn (fun _ => (1 : Mat 2)) (Metric.ball (0 : Vec 2) 1)
      (0 : H1Function (Metric.ball (0 : Vec 2) 1)) 0 0 := by
  refine ⟨⟨H10Function.ofContDiff (U := Metric.ball (0 : Vec 2) 1) Metric.isOpen_ball
      (f := fun _ => (0 : ℝ)) contDiff_const HasCompactSupport.zero (by simp), ?_⟩, ?_⟩
  · funext x; simp [H10Function.ofContDiff, H1Function.ofContDiff]
  · intro φ
    have h0 : ∀ x, (0 : H1Function (Metric.ball (0 : Vec 2) 1)).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, h0]

end SuperdiffusionCLT.Section7
