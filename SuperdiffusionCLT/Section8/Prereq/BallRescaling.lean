/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion
public import SuperdiffusionCLT.Section8.Prereq.ResolventMismatch

/-!
# Rescaling a ball to the unit ball

The dilation `u ↦ u(ρ ·)` carries `B₁` to `B_ρ`.  For the classical divergence-form operator
the chain rule needs no regularity (`fderiv` of a dilation is `ρ • fderiv`), which gives

* `ballResc_divForm_comp_smul`: the second-order scaling `ρ²`;
* `ballResc_coeff`: the field `a^ε(ρ ·)` is the field `a^{ε/ρ}`;
* `ballResc_equation_iff`: `lam u - s ∇·(a(·/ε)∇u) = f` in `B_ρ` if and only if
  `(lam ρ²) ũ - s ∇·(a(·/(ε/ρ))∇ũ) = ρ² f(ρ ·)` in `B₁`, for `ũ = u(ρ ·)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization SuperdiffusionCLT.Section8.Brownian

variable {d : ℕ}

theorem ballResc_fderiv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : ℝ} (hρ : ρ ≠ 0) (g : Vec d → E) (x : Vec d) :
    fderiv ℝ (fun y : Vec d => g (ρ • y)) x = ρ • fderiv ℝ g (ρ • x) := by
  have hlin : HasFDerivAt (fun y : Vec d => ρ • y) (ρ • ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).const_smul ρ
  by_cases hg : DifferentiableAt ℝ g (ρ • x)
  · have := hg.hasFDerivAt.comp x hlin
    have e : (fun y : Vec d => g (ρ • y)) = g ∘ (fun y : Vec d => ρ • y) := rfl
    rw [e, this.fderiv]
    ext v
    simp
  · have h2 : ¬ DifferentiableAt ℝ (fun y : Vec d => g (ρ • y)) x := by
      intro h
      apply hg
      have e : g = (fun y : Vec d => g (ρ • y)) ∘ (fun z : Vec d => ρ⁻¹ • z) := by
        funext z; simp [smul_smul, mul_inv_cancel₀ hρ]
      have e2 : ρ⁻¹ • (ρ • x) = x := by simp [smul_smul, inv_mul_cancel₀ hρ]
      rw [e]
      refine DifferentiableAt.comp (ρ • x) ?_ (by fun_prop)
      rw [e2]; exact h
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt h2]
    simp

/-- The divergence-form operator under dilation:
`∇·(a(ρ ·) ∇(u(ρ ·))) = ρ² (∇·(a ∇u))(ρ ·)`. -/
theorem ballResc_divForm_comp_smul (c : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (a : CoeffField d)
    (u : Vec d → ℝ) (x : Vec d) :
    divForm c (fun y : Vec d => a (ρ • y)) (fun y : Vec d => u (ρ • y)) x =
      ρ ^ 2 * divForm c a u (ρ • x) := by
  unfold divForm
  have h1 : fderiv ℝ (fun y : Vec d => u (ρ • y)) = fun y => ρ • fderiv ℝ u (ρ • y) :=
    funext fun y => ballResc_fderiv_comp_smul hρ u y
  have : Invertible ρ := invertibleOfNonzero hρ
  have key : ∀ i : Fin d,
      fderiv ℝ (fun y : Vec d => ∑ j : Fin d, a (ρ • y) i j *
        fderiv ℝ (fun z : Vec d => u (ρ • z)) y (Pi.single j 1)) x (Pi.single i 1) =
      ρ ^ 2 * fderiv ℝ (fun y : Vec d => ∑ j : Fin d, a y i j *
        fderiv ℝ u y (Pi.single j 1)) (ρ • x) (Pi.single i 1) := by
    intro i
    set G : Vec d → ℝ := fun z => ∑ j : Fin d, a z i j * fderiv ℝ u z (Pi.single j 1) with hG
    have e1 : (fun y : Vec d => ∑ j : Fin d, a (ρ • y) i j *
        fderiv ℝ (fun z : Vec d => u (ρ • z)) y (Pi.single j 1)) =
        ρ • (fun y : Vec d => G (ρ • y)) := by
      funext y
      rw [h1]
      simp only [hG, Pi.smul_apply, smul_eq_mul, smul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, fderiv_const_smul_of_invertible (f := fun y : Vec d => G (ρ • y)) ρ,
      ballResc_fderiv_comp_smul hρ G x]
    simp only [smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => key i, ← Finset.mul_sum]
  ring

theorem ballResc_vecNormSq_smul (ρ : ℝ) (x : Vec d) : vecNormSq (ρ • x) = ρ ^ 2 * vecNormSq x := by
  unfold vecNormSq vecDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The unit ball is the preimage of `B_ρ` under the dilation. -/
theorem ballResc_mem_iff {ρ : ℝ} (hρ : 0 < ρ) (x : Vec d) :
    x ∈ SuperdiffusionCLT.Section6.euclidBall (d := d) 1 ↔
      ρ • x ∈ SuperdiffusionCLT.Section6.euclidBall (d := d) ρ := by
  simp only [SuperdiffusionCLT.Section6.mem_euclidBall, ballResc_vecNormSq_smul]
  constructor
  · intro h
    have : 0 < ρ ^ 2 := by positivity
    nlinarith only [h, this]
  · intro h
    have : 0 < ρ ^ 2 := by positivity
    nlinarith only [h, this]

/-- The coefficient field of `L^ε` evaluated at `ρ x` is the coefficient field of `L^{ε/ρ}`. -/
theorem ballResc_coeff {ρ ε : ℝ} (a : CoeffField d) (x : Vec d) :
    a (ε⁻¹ • (ρ • x)) = a ((ε / ρ)⁻¹ • x) := by
  rw [smul_smul]
  congr 2
  rw [inv_div]
  ring

/-- **Ball rescaling of the resolvent equation (classical form).**  `u` solves
`lam u - s ∇·(a(·/ε)∇u) = f` in `B_ρ` if and only if `ũ = u(ρ ·)` solves
`(lam ρ²) ũ - s ∇·(a(·/(ε/ρ))∇ũ) = ρ² f(ρ ·)` in `B₁`. -/
theorem ballResc_equation_iff {ρ : ℝ} (hρ : 0 < ρ) (ε lam s : ℝ) (a : CoeffField d)
    (u f : Vec d → ℝ) :
    (∀ x ∈ SuperdiffusionCLT.Section6.euclidBall (d := d) ρ,
        lam * u x - divForm s (fun y => a (ε⁻¹ • y)) u x = f x) ↔
      ∀ x ∈ SuperdiffusionCLT.Section6.euclidBall (d := d) 1,
        (lam * ρ ^ 2) * u (ρ • x) -
          divForm s (fun y => a ((ε / ρ)⁻¹ • y)) (fun y => u (ρ • y)) x = ρ ^ 2 * f (ρ • x) := by
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hpt : ∀ x : Vec d, divForm s (fun y => a ((ε / ρ)⁻¹ • y)) (fun y => u (ρ • y)) x =
      ρ ^ 2 * divForm s (fun y => a (ε⁻¹ • y)) u (ρ • x) := fun x => by
    have := ballResc_divForm_comp_smul s hρ0 (fun y => a (ε⁻¹ • y)) u x
    rw [← this]
    congr 1
    funext y
    exact (ballResc_coeff a y).symm
  constructor
  · intro h x hx
    have := h (ρ • x) ((ballResc_mem_iff hρ x).mp hx)
    rw [hpt x]
    linear_combination ρ ^ 2 * this
  · intro h y hy
    have hx : ρ⁻¹ • y ∈ SuperdiffusionCLT.Section6.euclidBall (d := d) 1 := by
      rw [ballResc_mem_iff hρ, smul_smul, mul_inv_cancel₀ hρ0, one_smul]; exact hy
    have := h (ρ⁻¹ • y) hx
    rw [hpt, smul_smul, mul_inv_cancel₀ hρ0, one_smul] at this
    have hρ2 : ρ ^ 2 ≠ 0 := by positivity
    have h2 : ρ ^ 2 * (lam * u y - divForm s (fun y => a (ε⁻¹ • y)) u y - f y) = 0 := by
      linear_combination this
    have := (mul_eq_zero.mp h2).resolve_left hρ2
    linarith only [this]

end SuperdiffusionCLT.Section8
