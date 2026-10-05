/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.LinftyReduction
public import SuperdiffusionCLT.Section7.Analytic.Regularity.MaxPrincipleB
public import SuperdiffusionCLT.Section7.Prereq.WellPosed

/-!
# Reduction to smooth boundary data: the carrier of `g̃`, the maximum principle comparison and the
zero-trace reformulation
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

/-- A `C¹` function as an `H¹(U)` function on a bounded open set; its values are those of `f`
at every point. -/
noncomputable def li1_h1 (hU : IsOpen U) (hb : IsBoundedDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) : H1Function U :=
  H1Function.ofContDiffOnIsSobolevRegularDomain ⟨hU.measurableSet, hb⟩ hf

theorem li1_h1_toFun (hU : IsOpen U) (hb : IsBoundedDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) : (li1_h1 hU hb hf).toFun = f := rfl

theorem li1_h1_grad (hU : IsOpen U) (hb : IsBoundedDomain U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (x : Vec d) (i : Fin d) :
    (li1_h1 hU hb hf).grad x i = fderiv ℝ f x (basisVec i) := rfl

/-- The difference of two weak solutions with the same right-hand side is a weak solution with
zero data. -/
theorem li1_isWeakSolutionOn_sub {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ} {u v : H1Function U}
    (hu : IsWeakSolutionOn a U u f 0) (hv : IsWeakSolutionOn a U v f 0) :
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

/-- **Maximum principle comparison** (T:12864).  Two weak solutions with the same right-hand side
whose data differ by at most `c` everywhere differ by at most `c` almost everywhere, in either
direction. -/
theorem li1_linfty_comparison [NeZero d] (hU : IsOpen U) (hUb : IsBoundedDomain U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ}
    (g₁ g₂ u₁ u₂ : H1Function U)
    (h₁ : IsWeakSolutionOn a U u₁ f 0) (m₁ : MemH10 U (fun x => u₁.toFun x - g₁.toFun x))
    (h₂ : IsWeakSolutionOn a U u₂ f 0) (m₂ : MemH10 U (fun x => u₂.toFun x - g₂.toFun x))
    {c : ℝ} (hc : ∀ x, |g₁.toFun x - g₂.toFun x| ≤ c) :
    ∀ᵐ x ∂(volume.restrict U), |u₁.toFun x - u₂.toFun x| ≤ c := by
  have hz : IsWeakSolutionOn a U (0 : H1Function U) 0 0 := by
    intro φ
    have h0 : ∀ x, (0 : H1Function U).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, h0]
  have key : ∀ (u₁ u₂ g₁ g₂ : H1Function U), IsWeakSolutionOn a U u₁ f 0 →
      MemH10 U (fun x => u₁.toFun x - g₁.toFun x) → IsWeakSolutionOn a U u₂ f 0 →
      MemH10 U (fun x => u₂.toFun x - g₂.toFun x) → (∀ x, g₁.toFun x - g₂.toFun x ≤ c) →
      ∀ᵐ x ∂(volume.restrict U), u₁.toFun x - u₂.toFun x ≤ c := by
    intro u₁ u₂ g₁ g₂ h₁ m₁ h₂ m₂ hcc
    have := weakMaxPrinciple_comparison hU hUb hEll (u₁ - u₂) 0 (g₁ - g₂) 0
      (li1_isWeakSolutionOn_sub hEll h₁ h₂) hz ?_ (c := c) ?_
    · simpa using this
    · have := memH10_sub m₁ m₂
      convert this using 1
      funext x
      simp only [H1Function.sub_toFun]
      ring
    · intro x
      simpa using hcc x
  have e1 := key u₁ u₂ g₁ g₂ h₁ m₁ h₂ m₂ fun x => (abs_le.1 (hc x)).2
  have e2 := key u₂ u₁ g₂ g₁ h₂ m₂ h₁ m₁ fun x => by
    have := (abs_le.1 (hc x)).1
    linarith only [this]
  filter_upwards [e1, e2] with x a b
  exact abs_le.2 ⟨by linarith only [b], a⟩

/-- **Zero-trace reformulation** (`e.Dir.new.Linfty.smooth.reduction`, T:12887).  For a smooth
`g̃` the Dirichlet solution with datum `g̃` is `g̃ + v`, `v ∈ H¹₀(U)` solving the problem with
flux datum `-a∇g̃`; this holds for any coefficient field, in particular for `ν Id + k - (k)` and
for the constant field `shom Id`. -/
theorem li1_reduction (hU : IsOpen U) (hb : IsBoundedDomain U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ} {gt : Vec d → ℝ}
    (hgt : ContDiff ℝ 1 gt) (u : H1Function U) :
    (IsWeakSolutionOn a U u f (fun _ => 0) ∧ MemH10 U (fun x => u.toFun x - gt x)) ↔
      ∃ v : H10Function U, v.toH1Function.toFun = (fun x => u.toFun x - gt x) ∧
        IsH10WeakSolution a U f
          (fun x => -(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) v := by
  constructor
  · rintro ⟨h, ⟨v, hv⟩⟩
    refine ⟨v, hv, ?_⟩
    exact (w0_isWeakSolutionOn_iff_h10 hU hEll (li1_h1 hU hb hgt) u v hv).1 h
  · rintro ⟨v, hv, h⟩
    exact ⟨(w0_isWeakSolutionOn_iff_h10 hU hEll (li1_h1 hU hb hgt) u v hv).2 h, ⟨v, hv⟩⟩

/-- The solution with smooth datum is obtained from the `H¹₀` problem: existence. -/
theorem li1_dirichlet_exists [NeZero d] (hU : IsOpen U) (hb : IsBoundedDomain U) {lam Lam : ℝ}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ}
    (hf : MemScalarL2 U f) {gt : Vec d → ℝ} (hgt : ContDiff ℝ 1 gt) :
    ∃ u : H1Function U, IsWeakSolutionOn a U u f (fun _ => 0) ∧
      MemH10 U (fun x => u.toFun x - gt x) :=
  w0_dirichlet_exists hU hb hEll hf (li1_h1 hU hb hgt)

/-- Witness for the comparison: the zero solution on the unit ball with identity coefficients. -/
example : ∀ᵐ x ∂(volume.restrict (Section6.euclidBall (d := 2) 1)),
    |(0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
      (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x| ≤ 0 := by
  have hz : IsWeakSolutionOn (fun _ => (1 : Mat 2)) (Section6.euclidBall (d := 2) 1)
      (0 : H1Function (Section6.euclidBall (d := 2) 1)) 0 0 := by
    intro φ
    have h0 : ∀ x, (0 : H1Function (Section6.euclidBall (d := 2) 1)).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, h0]
  have hm : MemH10 (Section6.euclidBall (d := 2) 1) (fun x =>
      (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x) := by
    have : (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x) = 0 := by
      funext x; simp
    rw [this]
    exact memH10_zero
  exact li1_linfty_comparison (Section6.isOpen_euclidBall (d := 2) 1) (isBoundedDomain_euclidBall one_pos)
    isEllipticFieldOn_one_euclidBall 0 0 0 0 hz hm hz hm (c := 0) (fun x => by simp)

end SuperdiffusionCLT.Section7
