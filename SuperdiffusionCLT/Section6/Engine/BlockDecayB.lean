/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.BlockDecay

/-!
# One-block decay: the corrected affine functions and the telescoping of slopes

Facts about `V_j` from the flatness block, and the choice of a single affine function for all
target scales from the harmonic approximation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb4_slope_linear [NeZero d] {a : CoeffField d} {j l : ℕ} (hl : l ≤ j)
    (Vj : Vec d →ₗ[ℝ] (Vec d → ℝ))
    (hV : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (Vj e) g) :
    ∃ P : Vec d →ₗ[ℝ] Vec d, ∀ x, P x = affSlope l (Vj x) := by
  have hm : ∀ e : Vec d, MemLp (Vj e) 2 (eb4_mu d l) := fun e =>
    eb4_sol_memLp hl (hV e).choose_spec
  refine ⟨{ toFun := fun x => affSlope l (Vj x), map_add' := ?_, map_smul' := ?_ }, fun x => rfl⟩
  · intro x y
    have e : Vj (x + y) = fun z => Vj x z + Vj y z := by
      rw [map_add]
      rfl
    simp only [e]
    exact affSlope_add (hm x) (hm y)
  · intro c x
    have e : Vj (c • x) = fun z => c * Vj x z := by
      rw [map_smul]
      rfl
    simp only [e, RingHom.id_apply]
    exact affSlope_const_mul l c (Vj x)

theorem eb4_V_flat [NeZero d] {a : CoeffField d} {Hb j : ℕ} {Vj : Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q * ((Hb : ℝ) + 1) ≤ 1 / 2)
    (hVsol : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (Vj e) g)
    (hflat : ∀ k : ℕ, k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      cubeFlat k (fun x => Vj e x - vecDot (affSlope k (Vj e)) x) ≤ q * engNorm e ∧
        engNorm (affSlope k (Vj e) - e) ≤ q * ((j : ℝ) - (k : ℝ) + 1) * engNorm e)
    {k : ℕ} (hk : k ≤ j) (hjk : j ≤ k + Hb) (e : Vec d) :
    engNorm (affSlope k (Vj e) - e) ≤ 1 / 2 * engNorm e ∧ cubeFlat k (Vj e) ≤ engNorm e := by
  have hc : (j : ℝ) - (k : ℝ) + 1 ≤ (Hb : ℝ) + 1 := by
    have : (j : ℝ) ≤ (k : ℝ) + (Hb : ℝ) := by exact_mod_cast hjk
    linarith only [this]
  have hB : engNorm (affSlope k (Vj e) - e) ≤ 1 / 2 * engNorm e := by
    refine (hflat k hk hjk e).2.trans ?_
    have h1 : q * ((j : ℝ) - (k : ℝ) + 1) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left hc hq0).trans hq
    exact mul_le_mul_of_nonneg_right h1 (engNorm_nonneg e)
  refine ⟨hB, ?_⟩
  have hq2 : q ≤ 1 / 2 := by
    have : q ≤ q * ((Hb : ℝ) + 1) := by
      have h0 : (0 : ℝ) ≤ Hb := Nat.cast_nonneg Hb
      nlinarith only [hq0, h0]
    linarith only [this, hq]
  exact eb4_flat_le_of_slope (eb4_sol_memLp hk (hVsol e).choose_spec) e hq2
    (hflat k hk hjk e).1 hB

theorem eb4_V_drift [NeZero d] {a : CoeffField d} {Hb j : ℕ} {Vj : Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {q : ℝ}
    (hVsol : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (Vj e) g)
    (hflat : ∀ k : ℕ, k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      cubeFlat k (fun x => Vj e x - vecDot (affSlope k (Vj e)) x) ≤ q * engNorm e ∧
        engNorm (affSlope k (Vj e) - e) ≤ q * ((j : ℝ) - (k : ℝ) + 1) * engNorm e)
    {l k : ℕ} (hlk : l ≤ k) (hkj : k ≤ j) (hjl : j ≤ l + Hb) (e : Vec d) :
    cubeFlat k (fun y => Vj e y - vecDot (affSlope l (Vj e)) y) ≤
      (2 + eb4_rho d ^ (k - l)) * (q * engNorm e) :=
  eb4_drift hlk (eb4_sol_memLp hkj (hVsol e).choose_spec)
    (eb4_sol_memLp (hlk.trans hkj) (hVsol e).choose_spec) e
    (hflat k hkj (by omega) e).1 (hflat l (hlk.trans hkj) hjl e).1

theorem eb4_telescope [NeZero d] {τ l : ℕ} {f : Vec d → ℝ} (hf : MemLp f 2 (eb4_mu d τ))
    (p : ℕ → Vec d) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ i : ℕ, l ≤ i → i + 1 ≤ τ →
      cubeFlat i (fun y => f y - vecDot (p i) y) ≤ B * ((3 : ℝ)⁻¹) ^ (τ - i)) :
    ∀ i : ℕ, l ≤ i → i + 1 ≤ τ →
      cubeFlat i (fun y => f y - vecDot (p l) y) ≤
        (2 * eb4_rho d + 3) * (B * ((3 : ℝ)⁻¹) ^ (τ - i)) := by
  have hm : ∀ i : ℕ, i ≤ τ → ∀ r : Vec d, MemLp (fun y => f y - vecDot r y) 2 (eb4_mu d i) :=
    fun i hi r => (eb4_memLp_le hi hf).sub (e0c_memLp i (e0c_continuous_vecDot r))
  have hs3 : (0 : ℝ) < 2 * Real.sqrt 3 :=
    mul_pos two_pos (Real.sqrt_pos.2 (by norm_num))
  have hρ := eb4_rho_one_le d
  have key : ∀ i : ℕ, l ≤ i → i + 1 ≤ τ →
      engNorm (p i - p l) / (2 * Real.sqrt 3) ≤
        2 * (eb4_rho d + 1) * (B * ((3 : ℝ)⁻¹) ^ (τ - i)) := by
    intro i hli
    induction i, hli using Nat.le_induction with
    | base =>
      intro _
      have h0 : engNorm (p l - p l) = 0 := by
        rw [sub_self]
        simp [engNorm, vecNormSq, vecDot]
      rw [h0, zero_div]
      have : 0 ≤ ((3 : ℝ)⁻¹) ^ (τ - l) := by positivity
      positivity
    | succ i hli ih =>
      intro hi1
      have ih' := ih (by omega)
      have hτ : τ - i = (τ - (i + 1)) + 1 := by omega
      set a := B * ((3 : ℝ)⁻¹) ^ (τ - (i + 1)) with ha
      have ha0 : 0 ≤ a := by positivity
      have hai : B * ((3 : ℝ)⁻¹) ^ (τ - i) = a / 3 := by
        rw [hτ, pow_succ, ha]
        ring
      rw [hai] at ih'
      have h1 := hp i hli (by omega)
      have h2 := hp (i + 1) (by omega) (by omega)
      rw [hai] at h1
      rw [← ha] at h2
      have h3 := eb4_flat_mono (l := i) (k := i + 1) (Nat.le_succ i) (hm (i + 1) (by omega) (p (i + 1)))
      have hsub : i + 1 - i = 1 := by omega
      rw [hsub, pow_one] at h3
      have e1 : (fun y => vecDot (p (i + 1) - p i) y) =
          fun y => (f y - vecDot (p i) y) - (f y - vecDot (p (i + 1)) y) := by
        funext y
        rw [eb4_vecDot_sub]
        ring
      have h4 := eb4_flat_sub_le (hm i (by omega) (p i)) (hm i (by omega) (p (i + 1)))
      rw [← e1, cubeFlat_vecDot] at h4
      have h5 : eb4_rho d * cubeFlat (i + 1) (fun y => f y - vecDot (p (i + 1)) y) ≤
          eb4_rho d * a := mul_le_mul_of_nonneg_left h2 (by linarith only [hρ])
      have h6 := engNorm_add_le (p (i + 1) - p i) (p i - p l)
      rw [sub_add_sub_cancel] at h6
      have h7 : engNorm (p (i + 1) - p l) / (2 * Real.sqrt 3) ≤
          engNorm (p (i + 1) - p i) / (2 * Real.sqrt 3) +
            engNorm (p i - p l) / (2 * Real.sqrt 3) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right h6 hs3.le
      have : 0 ≤ eb4_rho d * a := mul_nonneg (by linarith only [hρ]) ha0
      have h8 : eb4_rho d * a + a / 3 + 2 * (eb4_rho d + 1) * (a / 3) ≤
          2 * (eb4_rho d + 1) * a := by nlinarith only [ha0, this]
      linarith only [h1, h3, h4, h5, h7, ih', h8]
  intro i hli hi1
  have h1 := hp i hli hi1
  have h2 := key i hli hi1
  have e1 : (fun y => f y - vecDot (p l) y) =
      fun y => (f y - vecDot (p i) y) + vecDot (p i - p l) y := by
    funext y
    rw [eb4_vecDot_sub]
    ring
  have h3 := cubeFlat_add_le (hm i (by omega) (p i)) (e0c_memLp i
    (e0c_continuous_vecDot (p i - p l)))
  rw [← e1, cubeFlat_vecDot] at h3
  nlinarith only [h1, h2, h3, hρ]

/-- The decay factor `3^{-η s}`. -/
noncomputable def eb4_R (η : ℝ) (s : ℕ) : ℝ := (3 : ℝ) ^ (-(η * (s : ℝ)))

theorem eb4_R_pos (η : ℝ) (s : ℕ) : 0 < eb4_R η s := Real.rpow_pos_of_pos (by norm_num) _

theorem eb4_R_add (η : ℝ) (s s' : ℕ) : eb4_R η (s + s') = eb4_R η s * eb4_R η s' := by
  unfold eb4_R
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

theorem eb4_R_anti {η : ℝ} (hη : 0 ≤ η) {s s' : ℕ} (h : s ≤ s') : eb4_R η s' ≤ eb4_R η s := by
  unfold eb4_R
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (s : ℝ) ≤ (s' : ℝ) := by exact_mod_cast h
  nlinarith only [this, hη]

theorem eb4_R_le_one {η : ℝ} (hη : 0 ≤ η) (s : ℕ) : eb4_R η s ≤ 1 := by
  have := eb4_R_anti hη (Nat.zero_le s)
  have h0 : eb4_R η 0 = 1 := by simp [eb4_R]
  rwa [h0] at this

theorem eb4_inv_pow_le_R {η : ℝ} (hη : η ≤ 1) (s : ℕ) : ((3 : ℝ)⁻¹) ^ s ≤ eb4_R η s := by
  unfold eb4_R
  have h1 : ((3 : ℝ)⁻¹) ^ s = (3 : ℝ) ^ (-((s : ℝ))) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  rw [h1]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  nlinarith only [this, hη]

end SuperdiffusionCLT.Section6
