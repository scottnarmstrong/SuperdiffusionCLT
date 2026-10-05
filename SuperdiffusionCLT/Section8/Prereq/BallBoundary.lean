/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.Basic
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-!
# A radial barrier for the divergence-form operator with a `C¹` skew part

For the coefficient field `a = ν Id + k` with `k` a `C¹` skew-symmetric matrix field, and the
Gaussian profile `ψ(x) = M (c - exp (-μ |x - e|²))`, the flux `a ∇ψ` is a `C¹` vector field whose
divergence is computed in coordinates (`ballBdry_div_flux`): the skew part contributes only
`(∇·k)·∇ψ`, because `k` is skew and the Hessian of `ψ` is symmetric.  On the region where
`ρ ≤ |x - e| ≤ Y` and for `μ` large, `-∇·(a ∇ψ) ≥ 1` (`ballBdry_neg_div_flux_ge`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization

variable {d : ℕ}

/-- The divergence of a vector field, in the coordinate basis. -/
noncomputable def ballBdry_div (B : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∑ i, fderiv ℝ (fun y => B y i) x (basisVec i)

/-- The squared distance to `e`, in coordinates. -/
noncomputable def ballBdry_sq (e x : Vec d) : ℝ := ∑ j, (x j - e j) ^ 2

/-- The Gaussian `exp (-μ |x - e|²)`. -/
noncomputable def ballBdry_gauss (μ : ℝ) (e x : Vec d) : ℝ := Real.exp (-μ * ballBdry_sq e x)

/-- The barrier `M (c - exp (-μ |x - e|²))`. -/
noncomputable def ballBdry_psi (M μ c : ℝ) (e x : Vec d) : ℝ := M * (c - ballBdry_gauss μ e x)

/-- The gradient of the barrier. -/
noncomputable def ballBdry_grad (M μ : ℝ) (e x : Vec d) : Vec d :=
  fun j => 2 * M * μ * ((x j - e j) * ballBdry_gauss μ e x)

theorem ballBdry_hasFDerivAt_sq (e x : Vec d) :
    HasFDerivAt (ballBdry_sq e)
      (∑ j, (2 * (x j - e j)) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)) x := by
  unfold ballBdry_sq
  refine HasFDerivAt.fun_sum fun j _ => ?_
  have h1 : HasFDerivAt (fun x : Vec d => x j - e j) (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) x :=
    (hasFDerivAt_apply j x).sub_const _
  simpa using h1.pow 2

theorem ballBdry_contDiff_sq (e : Vec d) {n : WithTop ℕ∞} : ContDiff ℝ n (ballBdry_sq e) := by
  unfold ballBdry_sq
  refine ContDiff.sum fun j _ => ?_
  exact (((contDiff_apply ℝ ℝ j).sub contDiff_const)).pow 2

theorem ballBdry_contDiff_gauss (μ : ℝ) (e : Vec d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (ballBdry_gauss μ e) := by
  unfold ballBdry_gauss
  exact Real.contDiff_exp.comp (contDiff_const.mul (ballBdry_contDiff_sq e))

theorem ballBdry_contDiff_psi (M μ c : ℝ) (e : Vec d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (ballBdry_psi M μ c e) := by
  unfold ballBdry_psi
  exact contDiff_const.mul (contDiff_const.sub (ballBdry_contDiff_gauss μ e))

theorem ballBdry_contDiff_grad (M μ : ℝ) (e : Vec d) (j : Fin d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x => ballBdry_grad M μ e x j) := by
  unfold ballBdry_grad
  exact contDiff_const.mul (((contDiff_apply ℝ ℝ j).sub contDiff_const).mul
    (ballBdry_contDiff_gauss μ e))

theorem ballBdry_hasFDerivAt_gauss (μ : ℝ) (e x : Vec d) :
    HasFDerivAt (ballBdry_gauss μ e)
      (ballBdry_gauss μ e x • ((-μ) •
        ∑ j, (2 * (x j - e j)) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))) x := by
  unfold ballBdry_gauss
  exact ((ballBdry_hasFDerivAt_sq e x).const_mul (-μ)).exp

theorem ballBdry_psi_apply_basis (M μ c : ℝ) (e x : Vec d) (i : Fin d) :
    fderiv ℝ (ballBdry_psi M μ c e) x (basisVec i) = ballBdry_grad M μ e x i := by
  have h : HasFDerivAt (ballBdry_psi M μ c e)
      (M • (-(ballBdry_gauss μ e x • ((-μ) •
        ∑ j, (2 * (x j - e j)) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))))) x := by
    unfold ballBdry_psi
    exact ((ballBdry_hasFDerivAt_gauss μ e x).const_sub c).const_mul M
  rw [h.fderiv]
  simp [basisVec, Pi.single_apply, ballBdry_grad]
  ring

theorem ballBdry_grad_apply_basis (M μ : ℝ) (e x : Vec d) (i j : Fin d) :
    fderiv ℝ (fun y => ballBdry_grad M μ e y j) x (basisVec i) =
      2 * M * μ * ((if i = j then 1 else 0) * ballBdry_gauss μ e x +
        (x j - e j) * (ballBdry_gauss μ e x * (-μ) * (2 * (x i - e i)))) := by
  have h1 : HasFDerivAt (fun y : Vec d => y j - e j) (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) x :=
    (hasFDerivAt_apply j x).sub_const _
  have h := ((h1.mul (ballBdry_hasFDerivAt_gauss μ e x)).const_mul (2 * M * μ))
  have h' : HasFDerivAt (fun y => ballBdry_grad M μ e y j) _ x := h
  rw [h'.fderiv]
  simp [basisVec, Pi.single_apply, eq_comm]
  split_ifs <;> ring

/-- The flux of the barrier, `a ∇ψ`, for `a = ν Id + k`. -/
noncomputable def ballBdry_flux (ν : ℝ) (k : Vec d → Mat d) (M μ : ℝ) (e x : Vec d) : Vec d :=
  matVecMul (ν • (1 : Mat d) + k x) (ballBdry_grad M μ e x)

/-- The column divergence of the skew part. -/
noncomputable def ballBdry_colDiv (k : Vec d → Mat d) (x : Vec d) (j : Fin d) : ℝ :=
  ∑ i, fderiv ℝ (fun y => k y i j) x (basisVec i)

theorem ballBdry_flux_apply (ν : ℝ) (k : Vec d → Mat d) (M μ : ℝ) (e x : Vec d) (i : Fin d) :
    ballBdry_flux ν k M μ e x i =
      ∑ j, ((if i = j then ν else 0) + k x i j) * ballBdry_grad M μ e x j := by
  unfold ballBdry_flux matVecMul
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.one_apply]

theorem ballBdry_contDiff_flux (ν : ℝ) {k : Vec d → Mat d}
    (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j)) (M μ : ℝ) (e : Vec d) (i : Fin d) :
    ContDiff ℝ 1 (fun x => ballBdry_flux ν k M μ e x i) := by
  simp only [ballBdry_flux_apply]
  refine ContDiff.sum fun j _ => ?_
  exact (contDiff_const.add (hk i j)).mul (ballBdry_contDiff_grad M μ e j)

theorem ballBdry_fderiv_flux (ν : ℝ) {k : Vec d → Mat d}
    (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j)) (M μ : ℝ) (e x : Vec d) (i : Fin d) :
    fderiv ℝ (fun y => ballBdry_flux ν k M μ e y i) x (basisVec i) =
      ∑ j, (((if i = j then ν else 0) + k x i j) *
          fderiv ℝ (fun y => ballBdry_grad M μ e y j) x (basisVec i) +
        fderiv ℝ (fun y => k y i j) x (basisVec i) * ballBdry_grad M μ e x j) := by
  have hd : ∀ j, HasFDerivAt (fun y => ((if i = j then ν else 0) + k y i j) * ballBdry_grad M μ e y j)
      (((if i = j then ν else 0) + k x i j) • fderiv ℝ (fun y => ballBdry_grad M μ e y j) x +
        (ballBdry_grad M μ e x j) • fderiv ℝ (fun y => k y i j) x) x := fun j => by
    have h1 : DifferentiableAt ℝ (fun y => k y i j) x :=
      ((hk i j).differentiable (by simp)) x
    have h2 : DifferentiableAt ℝ (fun y => ballBdry_grad M μ e y j) x :=
      ((ballBdry_contDiff_grad M μ e j (n := 1)).differentiable (by simp)) x
    have := ((h1.hasFDerivAt.const_add (if i = j then ν else 0)).mul h2.hasFDerivAt)
    convert this using 1
  have hfun : (fun y => ballBdry_flux ν k M μ e y i) =
      fun y => ∑ j, ((if i = j then ν else 0) + k y i j) * ballBdry_grad M μ e y j :=
    funext fun y => ballBdry_flux_apply ν k M μ e y i
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hd j
  rw [hfun, hs.fderiv]
  simp only [sum_apply, add_apply,
    smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem ballBdry_skew_diag {K : Mat d} (hK : ∀ i j, K i j = -K j i) : ∑ i, K i i = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have := hK i i
  linarith only [this]

theorem ballBdry_skew_quad {K : Mat d} (hK : ∀ i j, K i j = -K j i) (y : Vec d) :
    ∑ i, ∑ j, K i j * (y j * y i) = 0 := by
  have h : ∑ i, ∑ j, K i j * (y j * y i) = -∑ i, ∑ j, K i j * (y j * y i) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hK j i]
    ring
  linarith only [h]

theorem ballBdry_div_flux (ν : ℝ) {k : Vec d → Mat d}
    (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j)) (hskew : ∀ x i j, k x i j = -k x j i)
    (M μ : ℝ) (e x : Vec d) :
    ballBdry_div (ballBdry_flux ν k M μ e) x =
      2 * M * μ * ballBdry_gauss μ e x *
        (ν * ((d : ℝ) - 2 * μ * ballBdry_sq e x) +
          ∑ j, ballBdry_colDiv k x j * (x j - e j)) := by
  unfold ballBdry_div
  simp only [ballBdry_fderiv_flux ν hk]
  simp only [ballBdry_grad_apply_basis]
  simp only [ballBdry_grad, ballBdry_colDiv]
  set g := ballBdry_gauss μ e x with hg
  simp only [Finset.sum_add_distrib, add_mul]
  have h1 : ∑ i : Fin d, ∑ j : Fin d, (if i = j then ν else 0) *
      (2 * M * μ * ((if i = j then (1 : ℝ) else 0) * g +
        (x j - e j) * (g * (-μ) * (2 * (x i - e i))))) =
      2 * M * μ * g * (ν * ((d : ℝ) - 2 * μ * ballBdry_sq e x)) := by
    have : ∀ i : Fin d, ∑ j : Fin d, (if i = j then ν else 0) *
        (2 * M * μ * ((if i = j then (1 : ℝ) else 0) * g +
          (x j - e j) * (g * (-μ) * (2 * (x i - e i))))) =
        ν * (2 * M * μ * g) * (1 - 2 * μ * (x i - e i) ^ 2) := fun i => by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
    simp only [this]
    unfold ballBdry_sq
    rw [← Finset.mul_sum]
    have hs : ∑ i : Fin d, (1 - 2 * μ * (x i - e i) ^ 2) =
        (d : ℝ) - 2 * μ * ∑ j, (x j - e j) ^ 2 := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      simp
    rw [hs]
    ring
  have h2 : ∑ i : Fin d, ∑ j : Fin d, k x i j *
      (2 * M * μ * ((if i = j then (1 : ℝ) else 0) * g +
        (x j - e j) * (g * (-μ) * (2 * (x i - e i))))) = 0 := by
    have hterm : ∀ i j : Fin d, k x i j *
        (2 * M * μ * ((if i = j then (1 : ℝ) else 0) * g +
          (x j - e j) * (g * (-μ) * (2 * (x i - e i))))) =
        2 * M * μ * g * (if i = j then k x i j else 0) +
          (-(4 * M * μ ^ 2 * g)) * (k x i j * ((x j - e j) * (x i - e i))) := fun i j => by
      split_ifs <;> ring
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hd1 : ∑ i : Fin d, ∑ j : Fin d, (if i = j then k x i j else 0) = 0 := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      exact ballBdry_skew_diag (hskew x)
    have hd2 := ballBdry_skew_quad (hskew x) (fun j => x j - e j)
    rw [hd1, hd2]
    ring
  have h3 : ∑ i : Fin d, ∑ j : Fin d,
      (fderiv ℝ (fun y => k y i j) x) (basisVec i) * (2 * M * μ * ((x j - e j) * g)) =
      2 * M * μ * g * ∑ j : Fin d, (∑ i : Fin d, (fderiv ℝ (fun y => k y i j) x) (basisVec i)) *
        (x j - e j) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, h2, h3]
  ring

theorem ballBdry_sq_coord_le (e x : Vec d) (j : Fin d) : (x j - e j) ^ 2 ≤ ballBdry_sq e x :=
  Finset.single_le_sum (f := fun j => (x j - e j) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- The barrier is a supersolution of the unit forcing: `-∇·(a∇ψ) ≥ 1` where the distance to the
centre lies between `ρ` and `Y`. -/
theorem ballBdry_neg_div_flux_ge (ν : ℝ) {k : Vec d → Mat d}
    (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j)) (hskew : ∀ x i j, k x i j = -k x j i)
    {μ ρ Y Kb : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hY : 0 ≤ Y)
    (hμbig : ν * (d : ℝ) + Kb * Y + 1 ≤ 2 * μ * ν * ρ ^ 2)
    (e x : Vec d) (hs1 : ρ ^ 2 ≤ ballBdry_sq e x) (hs2 : ballBdry_sq e x ≤ Y ^ 2)
    (hKb : ∑ j, |ballBdry_colDiv k x j| ≤ Kb) :
    1 ≤ -ballBdry_div (ballBdry_flux ν k (Real.exp (μ * Y ^ 2) / (2 * μ)) μ e) x := by
  rw [ballBdry_div_flux ν hk hskew]
  set s := ballBdry_sq e x with hsdef
  set g := ballBdry_gauss μ e x with hg
  have hgge : Real.exp (-(μ * Y ^ 2)) ≤ g := by
    rw [hg, ballBdry_gauss, ← hsdef]
    exact Real.exp_le_exp.mpr (by nlinarith only [hμ, hs2])
  have hcoef : 1 ≤ 2 * (Real.exp (μ * Y ^ 2) / (2 * μ)) * μ * g := by
    have h1 : 2 * (Real.exp (μ * Y ^ 2) / (2 * μ)) * μ = Real.exp (μ * Y ^ 2) := by
      field_simp
    rw [h1]
    calc (1 : ℝ) = Real.exp (μ * Y ^ 2) * Real.exp (-(μ * Y ^ 2)) := by
          rw [← Real.exp_add]; simp
      _ ≤ Real.exp (μ * Y ^ 2) * g :=
          mul_le_mul_of_nonneg_left hgge (Real.exp_pos _).le
  have hbd : ∑ j, ballBdry_colDiv k x j * (x j - e j) ≤ Kb * Y := by
    have hy : ∀ j, |x j - e j| ≤ Y := fun j => by
      have := ballBdry_sq_coord_le e x j
      exact abs_le.mpr (abs_le_of_sq_le_sq' (by linarith only [this, hs2]) hY)
    calc ∑ j, ballBdry_colDiv k x j * (x j - e j)
        ≤ ∑ j, |ballBdry_colDiv k x j| * Y := Finset.sum_le_sum fun j _ => by
          calc ballBdry_colDiv k x j * (x j - e j)
              ≤ |ballBdry_colDiv k x j * (x j - e j)| := le_abs_self _
            _ = |ballBdry_colDiv k x j| * |x j - e j| := abs_mul _ _
            _ ≤ |ballBdry_colDiv k x j| * Y :=
                mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)
      _ = (∑ j, |ballBdry_colDiv k x j|) * Y := by rw [Finset.sum_mul]
      _ ≤ Kb * Y := mul_le_mul_of_nonneg_right hKb hY
  have hbr : 1 ≤ -(ν * ((d : ℝ) - 2 * μ * s) + ∑ j, ballBdry_colDiv k x j * (x j - e j)) := by
    have : 2 * μ * ν * ρ ^ 2 ≤ 2 * μ * ν * s := by
      have : 0 ≤ 2 * μ * ν := by positivity
      exact mul_le_mul_of_nonneg_left hs1 this
    nlinarith only [hbd, hμbig, this]
  have hexp : -(2 * (Real.exp (μ * Y ^ 2) / (2 * μ)) * μ * g *
      (ν * ((d : ℝ) - 2 * μ * s) + ∑ j, ballBdry_colDiv k x j * (x j - e j))) =
      (2 * (Real.exp (μ * Y ^ 2) / (2 * μ)) * μ * g) *
        (-(ν * ((d : ℝ) - 2 * μ * s) + ∑ j, ballBdry_colDiv k x j * (x j - e j))) := by ring
  rw [hexp]
  nlinarith only [hcoef, hbr]

end SuperdiffusionCLT.Section8
