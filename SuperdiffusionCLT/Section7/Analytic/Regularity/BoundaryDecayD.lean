/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaN
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayC

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# The face inequality for a product-form test function

For `u` with localized zero trace on the face window and the tangential affine part
`m = a + ∑ b_k x_k`, a product test function turns the moments of `m` into a bound by the
gradient energy of `u` near the face and the `L²` norm of `u - m`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}


/-- The closed box of radius `r` around the face centre, inside the cube. -/
def r3d_Ebox (e : Fin d) (m : ℤ) (r : ℝ) : Set (Vec d) :=
  {x | ∀ i, |x i - r3c_z0 e m i| ≤ r} ∩ openCubeSet (originCube d m)

theorem r3d_Ebox_measurable (e : Fin d) (m : ℤ) (r : ℝ) : MeasurableSet (r3d_Ebox e m r) := by
  refine MeasurableSet.inter ?_ (isOpen_openCubeSet _).measurableSet
  have : {x : Vec d | ∀ i, |x i - r3c_z0 e m i| ≤ r} = ⋂ i, {x : Vec d | |x i - r3c_z0 e m i| ≤ r} := by
    ext x; simp
  rw [this]
  refine (isClosed_iInter fun i => ?_).measurableSet
  exact isClosed_le (by fun_prop) continuous_const

/-- The window of the face `x e = -3^m/2`. -/
def r3d_window (e : Fin d) (m : ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - r3c_z0 e m i| < (3 : ℝ) ^ m / 2}

theorem r3d_theta_window (e : Fin d) (m : ℤ) {ρ h : ℝ} (hh : 0 < h) (hhL : h < (3 : ℝ) ^ m / 2)
    (hρL : ρ < (3 : ℝ) ^ m / 2) (Ψ : Fin d → ℝ → ℝ)
    (hΨ : ∀ i, tsupport (Ψ i) ⊆ Set.Icc (-ρ) ρ) :
    tsupport (r3d_theta e ((3 : ℝ) ^ m / 2) h Ψ) ⊆ r3d_window e m := by
  intro x hx
  obtain ⟨h1, h2⟩ := r3d_theta_tsupport e hh Ψ hΨ hx
  intro i
  by_cases hi : i = e
  · subst hi
    simp only [r3c_z0, ite_true]
    have : x i - -((3 : ℝ) ^ m / 2) = x i + (3 : ℝ) ^ m / 2 := by ring
    rw [this]
    exact lt_of_le_of_lt h2 hhL
  · simp only [r3c_z0, hi, ite_false, sub_zero]
    exact lt_of_le_of_lt (h1 i hi) hρL

theorem r3d_theta_support_Ebox (e : Fin d) (m : ℤ) {ρ h r : ℝ} (hh : 0 < h) (hρr : ρ ≤ r) (hhr : h ≤ r)
    (Ψ : Fin d → ℝ → ℝ) (hΨ : ∀ i, tsupport (Ψ i) ⊆ Set.Icc (-ρ) ρ) {x : Vec d}
    (hxΩ : x ∈ openCubeSet (originCube d m)) (hx : r3d_theta e ((3 : ℝ) ^ m / 2) h Ψ x ≠ 0) :
    x ∈ r3d_Ebox e m r := by
  refine ⟨?_, hxΩ⟩
  have hxs : x ∈ tsupport (r3d_theta e ((3 : ℝ) ^ m / 2) h Ψ) := subset_tsupport _ hx
  obtain ⟨h1, h2⟩ := r3d_theta_tsupport e hh Ψ hΨ hxs
  intro i
  by_cases hi : i = e
  · subst hi
    simp only [r3c_z0, ite_true]
    have : x i - -((3 : ℝ) ^ m / 2) = x i + (3 : ℝ) ^ m / 2 := by ring
    rw [this]
    exact h2.trans hhr
  · simp only [r3c_z0, hi, ite_false, sub_zero]
    exact (h1 i hi).trans hρr

theorem r3d_face_core (e : Fin d) (m : ℤ) {ρ h r K : ℝ} (hh : 0 < h)
    (hhL : h < (3 : ℝ) ^ m / 2) (hρL : ρ < (3 : ℝ) ^ m / 2) (hρr : ρ ≤ r) (hhr : h ≤ r)
    (hK : ∀ t, |deriv (r3d_bump (r := 1) one_pos) t| ≤ K) (Ψ : Fin d → ℝ → ℝ)
    (hΨs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Ψ i)) (hΨk : ∀ i, HasCompactSupport (Ψ i))
    (hΨt : ∀ i, tsupport (Ψ i) ⊆ Set.Icc (-ρ) ρ)
    (u : H1Function (openCubeSet (originCube d m)))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) u.toFun)
    (a : ℝ) (b : Vec d) :
    (a * ∏ i ∈ Finset.univ.erase e, (∫ t in Set.Ioo (-((3 : ℝ) ^ m / 2)) ((3 : ℝ) ^ m / 2), Ψ i t) +
        ∑ k ∈ Finset.univ.erase e, b k * ∏ i ∈ Finset.univ.erase e,
          (if i = k then (∫ t in Set.Ioo (-((3 : ℝ) ^ m / 2)) ((3 : ℝ) ^ m / 2), t * Ψ i t)
            else (∫ t in Set.Ioo (-((3 : ℝ) ^ m / 2)) ((3 : ℝ) ^ m / 2), Ψ i t))) ^ 2 ≤
      2 * ((2 * h) * ∏ j ∈ Finset.univ.erase e,
          ∫ t in Set.Ioo (-((3 : ℝ) ^ m / 2)) ((3 : ℝ) ^ m / 2), Ψ j t ^ 2) *
        (∫ x in r3d_Ebox e m r, u.grad x e ^ 2) +
      2 * ((2 * K ^ 2 / h) * ∏ j ∈ Finset.univ.erase e,
          ∫ t in Set.Ioo (-((3 : ℝ) ^ m / 2)) ((3 : ℝ) ^ m / 2), Ψ j t ^ 2) *
        ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 := by
  set L : ℝ := (3 : ℝ) ^ m / 2 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  have hθs := r3d_theta_contDiff e L h Ψ hΨs
  have hθk := r3d_theta_compact e (L := L) hh Ψ hΨk
  have hθT := r3d_theta_window e m hh hhL hρL Ψ hΨt
  have hmc := r3d_m_continuous e a b
  have hmb : ∀ x ∈ openCubeSet (originCube d m), |r3d_m e a b x| ≤ |a| + L * ∑ k ∈ Finset.univ.erase e, |b k| := by
    intro x hx
    refine r3d_m_abs_le e a b (fun i => ?_)
    have := (hc_mem_openCubeSet_originCube_iff m x).1 hx i
    rw [abs_le]
    exact ⟨this.1.le, this.2.le⟩
  have hid := r3d_face_identity (originCube d m) e u hZ hθs hθk hθT hmc hmb
    (r3d_Ebox_measurable e m r) Set.inter_subset_right
    (fun x hx hθx => r3d_theta_support_Ebox e m hh hρr hhr Ψ hΨt hx hθx)
  -- evaluate the integrals over the cube
  have hQ := r3d_openCube_eq_pi (d := d) m
  have hPc : Continuous (deriv (r3d_prof L h)) := (r3d_prof_contDiff L h).continuous_deriv (by simp)
  have hPk : HasCompactSupport (deriv (r3d_prof L h)) := (r3d_prof_compact L hh).deriv
  have hP : ∫ t in Set.Ioo (-L) L, deriv (r3d_prof L h) t = -1 :=
    r3d_prof_integral_deriv L hh hLpos (by linarith only [hhL, hLpos])
  have hmom := r3d_moment e (L := L) a b Ψ (deriv (r3d_prof L h)) (fun i => (hΨs i).continuous)
    hΨk hPc hPk hP
  have hlhs : ∫ x in openCubeSet (originCube d m), r3d_m e a b x * p12_grad (r3d_theta e L h Ψ) x e =
      ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L),
        (a + ∑ k ∈ Finset.univ.erase e, b k * x k) *
          ((∏ j ∈ Finset.univ.erase e, Ψ j (x j)) * deriv (r3d_prof L h) (x e)) := by
    rw [hQ]
    congr 1
    funext x
    rw [r3d_theta_grad_e e L h Ψ hΨs x]
    rfl
  have e1 : ∫ x in openCubeSet (originCube d m), r3d_theta e L h Ψ x ^ 2 =
      ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L), r3d_theta e L h Ψ x ^ 2 := by
    rw [hQ]
  have e2 : ∫ x in openCubeSet (originCube d m), p12_grad (r3d_theta e L h Ψ) x e ^ 2 =
      ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-L) L),
        p12_grad (r3d_theta e L h Ψ) x e ^ 2 := by
    rw [hQ]
  rw [hlhs, hmom, e1, e2, r3d_theta_sq_integral e L h Ψ, r3d_dtheta_sq_integral e L h Ψ hΨs] at hid
  have hprodnn : 0 ≤ ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 :=
    Finset.prod_nonneg fun j _ => integral_nonneg fun t => sq_nonneg _
  have hX : 0 ≤ ∫ x in r3d_Ebox e m r, u.grad x e ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hG : 0 ≤ ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hP2 := r3d_prof_integral_sq_le L hh
  have hD2 := r3d_prof_integral_deriv_sq_le L hh hK
  have t1 : (∫ t in Set.Ioo (-L) L, r3d_prof L h t ^ 2) *
        ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 ≤
      (2 * h) * ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 :=
    mul_le_mul_of_nonneg_right hP2 hprodnn
  have t2 : (∫ t in Set.Ioo (-L) L, deriv (r3d_prof L h) t ^ 2) *
        ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 ≤
      (2 * K ^ 2 / h) * ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 :=
    mul_le_mul_of_nonneg_right hD2 hprodnn
  have t3 := mul_le_mul_of_nonneg_right t1 hX
  have t4 := mul_le_mul_of_nonneg_right t2 hG
  rw [neg_sq] at hid
  linarith only [hid, t3, t4]



theorem r3d_card_erase (e : Fin d) : (Finset.univ.erase e).card = d - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ e)]
  simp

theorem r3d_card_erase_erase {e k : Fin d} (hk : k ∈ Finset.univ.erase e) :
    ((Finset.univ.erase e).erase k).card = d - 1 - 1 := by
  rw [Finset.card_erase_of_mem hk, r3d_card_erase]


end SuperdiffusionCLT.Section7
