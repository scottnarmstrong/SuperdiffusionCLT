/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion
public import SuperdiffusionCLT.Section8.Brownian.HeatGenerator

/-!
# The carriers `divForm`, `scalePath`, `opScale`, `timeScale`: elementary API

`scalePath` is continuous, the prefactors satisfy `ε² τ_ε = opScale`, `divForm` is linear and
local, a constant skew-symmetric matrix does not change `divForm` on `C²` functions, and the
dilation identity for `divForm` holds.
-/

@[expose] public section

open scoped NNReal

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess SuperdiffusionCLT.Section8.Brownian

variable {d : ℕ}

/-- `scalePath a c` is continuous on path space. -/
theorem continuous_scalePath (a : ℝ) (c : ℝ≥0) :
    Continuous (scalePath (d := d) a c) := by
  unfold scalePath
  exact (ContinuousMap.continuous_postcomp _).comp (ContinuousMap.continuous_precomp _)

/-- `scalePath` evaluated. -/
theorem scalePath_apply (a : ℝ) (c : ℝ≥0) (w : ContinuousPath (Vec d)) (t : ℝ≥0) :
    scalePath a c w t = a • w (c * t) := rfl

/-- `ε² τ_ε = opScale`. -/
theorem sq_mul_timeScale (cStar ε : ℝ) (hc : 0 < cStar) (hε : 0 < ε) :
    ε ^ 2 * timeScale cStar ε = opScale cStar ε := by
  unfold timeScale opScale
  have hε2 : (ε ^ 2) ≠ 0 := by positivity
  have h8 : (8 * cStar * |Real.log ε|) = 4 * (2 * cStar * |Real.log ε|) := by ring
  have hnn : 0 ≤ 2 * cStar * |Real.log ε| := by positivity
  rw [h8, Real.mul_rpow (by norm_num) hnn]
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h4, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hε2]
  ring

/-- For the constant coefficient `c • Id` and a `C²` function, `divForm 1` is `c` times the
Laplacian. -/
theorem divForm_const_smul_one (c : ℝ) (u : Vec d → ℝ) (hu : ContDiff ℝ 2 u) (x : Vec d) :
    divForm 1 (fun _ => c • (1 : Mat d)) u x = c * vecLaplacian u x := by
  have hdu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hdu.differentiable (by norm_num)).differentiableAt
  rw [vecLaplacian_eq_sum_fderiv, divForm, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun y : Vec d => ∑ j : Fin d,
      (c • (1 : Mat d)) i j * fderiv ℝ u y (Pi.single j 1)) =
      fun y => c * fderiv ℝ u y (Pi.single i 1) := by
    funext y
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Matrix.one_apply_ne (Ne.symm hji)]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hfun]
  have h1 : HasFDerivAt (fun y : Vec d => fderiv ℝ u y (Pi.single i 1))
      ((fderiv ℝ (fderiv ℝ u) x).flip (Pi.single i 1)) x := by
    have := hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ)) x)
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using this
  have h2 := (h1.const_mul c).fderiv
  rw [h2]
  simp

/-- `divForm` depends only on the germs of the coefficient and of the function at the point. -/
theorem divForm_congr_of_eventuallyEq (c : ℝ) {a a' : CoeffField d} {u u' : Vec d → ℝ}
    {x : Vec d} (ha : a =ᶠ[nhds x] a') (hu : u =ᶠ[nhds x] u') :
    divForm c a u x = divForm c a' u' x := by
  unfold divForm
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdu : fderiv ℝ u =ᶠ[nhds x] fderiv ℝ u' := hu.fderiv
  have hF : (fun y => ∑ j : Fin d, a y i j * fderiv ℝ u y (Pi.single j 1)) =ᶠ[nhds x]
      (fun y => ∑ j : Fin d, a' y i j * fderiv ℝ u' y (Pi.single j 1)) := by
    filter_upwards [ha, hdu] with y hy hy'
    simp [hy, hy']
  rw [hF.fderiv_eq]

/-- The `i`-th flux component whose derivative `divForm` sums. -/
private noncomputable def fd_flux (a : CoeffField d) (u : Vec d → ℝ) (i : Fin d) (y : Vec d) :
    ℝ :=
  ∑ j : Fin d, a y i j * fderiv ℝ u y (Pi.single j 1)

private theorem fd_flux_differentiableAt (a : CoeffField d) (u : Vec d → ℝ)
    (hu : ContDiff ℝ 2 u) (x : Vec d) (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (i : Fin d) : DifferentiableAt ℝ (fd_flux a u i) x := by
  have hdu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hdu.differentiable (by norm_num)).differentiableAt
  unfold fd_flux
  refine DifferentiableAt.fun_sum fun j _ => (ha i j).mul ?_
  exact hdiff.clm_apply (differentiableAt_const (Pi.single j (1 : ℝ) : Vec d))

/-- `divForm` is additive in the function. -/
theorem divForm_add (c : ℝ) (a : CoeffField d) {u v : Vec d → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (x : Vec d) (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) :
    divForm c a (u + v) x = divForm c a u x + divForm c a v x := by
  unfold divForm
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun y => ∑ j : Fin d, a y i j * fderiv ℝ (u + v) y (Pi.single j 1)) =
      fd_flux a u i + fd_flux a v i := by
    funext y
    have hu1 : DifferentiableAt ℝ u y := (hu.differentiable (by norm_num)) y
    have hv1 : DifferentiableAt ℝ v y := (hv.differentiable (by norm_num)) y
    simp only [Pi.add_apply, fd_flux, fderiv_add hu1 hv1, add_apply, mul_add,
      Finset.sum_add_distrib]
  rw [hfun, fderiv_add (fd_flux_differentiableAt a u hu x ha i)
    (fd_flux_differentiableAt a v hv x ha i)]
  rfl

/-- `divForm` is homogeneous in the function. -/
theorem divForm_smul (c : ℝ) (a : CoeffField d) (r : ℝ) {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u)
    (x : Vec d) (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) :
    divForm c a (r • u) x = r * divForm c a u x := by
  have key : ∀ i : Fin d, fderiv ℝ (fun y => ∑ j : Fin d, a y i j *
      fderiv ℝ (r • u) y (Pi.single j 1)) x (Pi.single i 1) =
      r * fderiv ℝ (fd_flux a u i) x (Pi.single i 1) := by
    intro i
    have hfun : (fun y => ∑ j : Fin d, a y i j * fderiv ℝ (r • u) y (Pi.single j 1)) =
        fun y => r * fd_flux a u i y := by
      funext y
      have hu1 : DifferentiableAt ℝ u y := (hu.differentiable (by norm_num)) y
      simp only [fd_flux, fderiv_const_smul hu1, smul_apply, smul_eq_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfun, fderiv_const_mul (fd_flux_differentiableAt a u hu x ha i)]
    simp
  unfold divForm
  simp only [key]
  rw [← Finset.mul_sum, mul_left_comm]
  rfl

/-- The second derivative contracted with a skew-symmetric matrix vanishes. -/
private theorem fd_skew_sum (S : Mat d) (hS : ∀ i j, S j i = -S i j)
    (B : Vec d →L[ℝ] Vec d →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v) :
    ∑ i : Fin d, ∑ j : Fin d, S i j * B (Pi.single i 1) (Pi.single j 1) = 0 := by
  have h : ∑ i : Fin d, ∑ j : Fin d, S i j * B (Pi.single i 1) (Pi.single j 1) =
      -∑ i : Fin d, ∑ j : Fin d, S i j * B (Pi.single i 1) (Pi.single j 1) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hS, hB (Pi.single j 1) (Pi.single i 1)]
    ring
  linarith only [h]

/-- A constant skew-symmetric matrix added to the coefficient does not change `divForm` on `C²`
functions. -/
theorem divForm_add_const_skew (c : ℝ) (a : CoeffField d) (S : Mat d)
    (hS : ∀ i j, S j i = -S i j) {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (x : Vec d)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) :
    divForm c (fun y => a y + S) u x = divForm c a u x := by
  have hdu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hdu.differentiable (by norm_num)).differentiableAt
  have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ u) x v w = fderiv ℝ (fderiv ℝ u) x w v := by
    have h := hu.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
    exact fun v w => h v w
  have hH : ∀ i : Fin d, DifferentiableAt ℝ
      (fun y => ∑ j : Fin d, S i j * fderiv ℝ u y (Pi.single j 1)) x := fun i =>
    DifferentiableAt.fun_sum fun j _ =>
      (differentiableAt_const _).mul
        (hdiff.clm_apply (differentiableAt_const (Pi.single j (1 : ℝ) : Vec d)))
  have hsplit : ∀ i : Fin d, fderiv ℝ (fun y => ∑ j : Fin d, (a y + S) i j *
      fderiv ℝ u y (Pi.single j 1)) x (Pi.single i 1) =
      fderiv ℝ (fd_flux a u i) x (Pi.single i 1) +
      fderiv ℝ (fun y => ∑ j : Fin d, S i j * fderiv ℝ u y (Pi.single j 1)) x (Pi.single i 1) := by
    intro i
    have hfun : (fun y => ∑ j : Fin d, (a y + S) i j * fderiv ℝ u y (Pi.single j 1)) =
        fd_flux a u i + fun y => ∑ j : Fin d, S i j * fderiv ℝ u y (Pi.single j 1) := by
      funext y
      simp only [fd_flux, Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hfun, fderiv_add (fd_flux_differentiableAt a u hu x ha i) (hH i)]
    rfl
  have hcalc : ∀ i : Fin d,
      fderiv ℝ (fun y => ∑ j : Fin d, S i j * fderiv ℝ u y (Pi.single j 1)) x (Pi.single i 1) =
      ∑ j : Fin d, S i j * fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single j 1) := by
    intro i
    have hj : ∀ j : Fin d, HasFDerivAt (fun y : Vec d => S i j * fderiv ℝ u y (Pi.single j 1))
        (S i j • (fderiv ℝ (fderiv ℝ u) x).flip (Pi.single j 1)) x := by
      intro j
      have := (hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single j (1 : ℝ) : Vec d) x)).const_mul (S i j)
      simpa only [ContinuousLinearMap.comp_zero, zero_add] using this
    have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hj j
    rw [hsum.fderiv]
    simp
  unfold divForm
  congr 1
  simp only [hsplit, hcalc, Finset.sum_add_distrib]
  rw [fd_skew_sum S hS _ hsymm, add_zero]
  rfl

/-- Dilation identity for `divForm`: for `ε ≠ 0`,
`∇·(a ∇ (u ∘ (ε • ·)))(z) = ε² (∇·(a(ε⁻¹ ·) ∇u))(ε z)`. -/
theorem divForm_comp_smul (c : ℝ) (a : CoeffField d) (u : Vec d → ℝ) {ε : ℝ} (hε : ε ≠ 0)
    (z : Vec d) :
    divForm c a (fun y => u (ε • y)) z =
      ε ^ 2 * divForm c (fun y => a (ε⁻¹ • y)) u (ε • z) := by
  let e : Vec d ≃L[ℝ] Vec d := ContinuousLinearEquiv.smulLeft (Units.mk0 ε hε)
  have he : ∀ y, e y = ε • y := fun y => rfl
  have hder : ∀ y j, fderiv ℝ (fun y => u (ε • y)) y (Pi.single j 1) =
      ε * fderiv ℝ u (ε • y) (Pi.single j 1) := by
    intro y j
    have h := e.comp_right_fderiv (f := u) (x := y)
    have h' : fderiv ℝ (fun y => u (ε • y)) y = fderiv ℝ (u ∘ e) y := rfl
    rw [h', h]
    simp [he]
  unfold divForm
  rw [mul_left_comm (ε ^ 2) c]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set G : Vec d → ℝ := fun y => ∑ j : Fin d, a (ε⁻¹ • y) i j * fderiv ℝ u y (Pi.single j 1)
    with hG
  have hfun : (fun y => ∑ j : Fin d, a y i j * fderiv ℝ (fun y => u (ε • y)) y (Pi.single j 1)) =
      fun y => ε * G (e y) := by
    funext y
    simp only [hder, hG, he, Finset.mul_sum, inv_smul_smul₀ hε]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hfun2 : (fun y => ε * G (e y)) = (fun w => ε * G w) ∘ e := rfl
  rw [hfun, hfun2, e.comp_right_fderiv]
  by_cases hd : DifferentiableAt ℝ G (e z)
  · rw [fderiv_const_mul hd]
    simp [he]
    ring
  · have hd' : ¬ DifferentiableAt ℝ (fun w => ε * G w) (e z) := by
      intro h
      apply hd
      have := h.const_mul ε⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ hε, one_mul] using this
    rw [fderiv_zero_of_not_differentiableAt hd',
      show fderiv ℝ G (ε • z) = 0 from fderiv_zero_of_not_differentiableAt hd]
    simp

/-! Witnesses: the hypotheses are met by a constant coefficient and a polynomial test function. -/

example (d : ℕ) : ContDiff ℝ 2 (fun x : Vec d => ∑ i, x i ^ 2) := by
  fun_prop

example (d : ℕ) (c : ℝ) (x : Vec d) :
    divForm 1 (fun _ => c • (1 : Mat d)) (fun y : Vec d => ∑ i, y i ^ 2) x =
      c * vecLaplacian (fun y : Vec d => ∑ i, y i ^ 2) x :=
  divForm_const_smul_one c _ (by fun_prop) x

example (d : ℕ) (x : Vec d) :
    divForm 1 (fun _ => (1 : Mat d)) ((fun y : Vec d => ∑ i, y i ^ 2) +
      (fun y : Vec d => ∑ i, y i ^ 2)) x =
    divForm 1 (fun _ => (1 : Mat d)) (fun y : Vec d => ∑ i, y i ^ 2) x +
      divForm 1 (fun _ => (1 : Mat d)) (fun y : Vec d => ∑ i, y i ^ 2) x :=
  divForm_add 1 _ (by fun_prop) (by fun_prop) x fun _ _ => differentiableAt_const _

example (d : ℕ) (x : Vec d) :
    divForm 1 (fun _ => (1 : Mat d)) ((3 : ℝ) • fun y : Vec d => ∑ i, y i ^ 2) x =
      3 * divForm 1 (fun _ => (1 : Mat d)) (fun y : Vec d => ∑ i, y i ^ 2) x :=
  divForm_smul 1 _ 3 (by fun_prop) x fun _ _ => differentiableAt_const _

example (x : Vec 2) :
    divForm 1 (fun _ => (1 : Mat 2) + !![0, 1; -1, 0]) (fun y : Vec 2 => ∑ i, y i ^ 2) x =
      divForm 1 (fun _ => (1 : Mat 2)) (fun y : Vec 2 => ∑ i, y i ^ 2) x :=
  divForm_add_const_skew 1 (fun _ => (1 : Mat 2)) !![0, 1; -1, 0]
    (by intro i j; fin_cases i <;> fin_cases j <;> simp) (by fun_prop) x
    fun _ _ => differentiableAt_const _

example (d : ℕ) (z : Vec d) :
    divForm 1 (fun _ => (1 : Mat d)) (fun y : Vec d => ∑ i, (2 • y) i ^ 2) z =
      (2 : ℝ) ^ 2 * divForm 1 (fun y => (fun _ => (1 : Mat d)) ((2 : ℝ)⁻¹ • y))
        (fun y : Vec d => ∑ i, y i ^ 2) ((2 : ℝ) • z) := by
  have h := divForm_comp_smul 1 (fun _ => (1 : Mat d)) (fun y : Vec d => ∑ i, y i ^ 2)
    (two_ne_zero : (2 : ℝ) ≠ 0) z
  simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul] using h

example (d : ℕ) : Continuous (scalePath (d := d) 2 1) :=
  continuous_scalePath 2 1

example : (2 : ℝ) ^ 2 * timeScale 1 2 = opScale 1 2 :=
  sq_mul_timeScale 1 2 one_pos two_pos

end SuperdiffusionCLT.Section8
