/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.AffineSlopeB
public import SuperdiffusionCLT.Section6.Engine.BallCube
public import SuperdiffusionCLT.Section6.Engine.SolutionLimit

/-!
# One-block decay: calculus of the basic step

Restriction of solutions to lower cubes, the scale-comparison constant, subadditivity of the
scale-normalized oscillation for differences, and the two slope estimates (flatness of a
corrected affine function, and drift of its slope between two scales).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The normalized measure of the origin cube `□_n`. -/
noncomputable abbrev eb4_mu (d n : ℕ) : Measure (Vec d) := normalizedCubeMeasure (originCube d (n : ℤ))

/-- The scale-comparison constant `3^{(d+2)/2}`. -/
noncomputable def eb4_rho (d : ℕ) : ℝ := Real.sqrt ((3 : ℝ) ^ (d + 2))

theorem eb4_rho_sq (d : ℕ) : eb4_rho d ^ 2 = (3 : ℝ) ^ (d + 2) :=
  Real.sq_sqrt (by positivity)

theorem eb4_rho_one_le (d : ℕ) : 1 ≤ eb4_rho d := by
  unfold eb4_rho
  rw [Real.one_le_sqrt]
  exact one_le_pow₀ (by norm_num)

theorem eb4_rho_pos (d : ℕ) : 0 < eb4_rho d := lt_of_lt_of_le one_pos (eb4_rho_one_le d)

theorem eb4_memLp_down {u : Vec d → ℝ} {k : ℕ} :
    ∀ m : ℕ, MemLp u 2 (eb4_mu d (k + m)) → MemLp u 2 (eb4_mu d k)
  | 0, h => h
  | m + 1, h => eb4_memLp_down m (e0b_memLp_step (k := k + m) h).1

theorem eb4_memLp_le {u : Vec d → ℝ} {k n : ℕ} (hk : k ≤ n) (hu : MemLp u 2 (eb4_mu d n)) :
    MemLp u 2 (eb4_mu d k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact eb4_memLp_down m hu

theorem eb4_sol_memLp {a : CoeffField d} {n k : ℕ} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hk : k ≤ n) (h : IsSolOn a (engCube d n) u g) : MemLp u 2 (eb4_mu d k) :=
  eb4_memLp_le hk h.memLp.1

theorem eb4_flat_mono [NeZero d] {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (eb4_mu d k)) :
    cubeFlat l f ≤ eb4_rho d ^ (k - l) * cubeFlat k f := by
  have h := cubeFlat_mono_scale hlk hf
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlk
  have hm : l + m - l = m := by omega
  rw [hm]
  have hX : (0 : ℝ) < (3 : ℝ) ^ ((d + 2) * l) := by positivity
  have h0 : 0 ≤ eb4_rho d ^ m * cubeFlat (l + m) f :=
    mul_nonneg (pow_nonneg (eb4_rho_pos d).le _) (cubeFlat_nonneg _ _)
  refine (sq_le_sq₀ (cubeFlat_nonneg _ _) h0).1 ?_
  refine le_of_mul_le_mul_right ?_ hX
  have e1 : (3 : ℝ) ^ ((d + 2) * (l + m)) =
      (3 : ℝ) ^ ((d + 2) * l) * ((eb4_rho d ^ 2) ^ m) := by
    rw [eb4_rho_sq, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [e1] at h
  calc cubeFlat l f ^ 2 * (3 : ℝ) ^ ((d + 2) * l)
      ≤ cubeFlat (l + m) f ^ 2 * ((3 : ℝ) ^ ((d + 2) * l) * ((eb4_rho d ^ 2) ^ m)) := h
    _ = (eb4_rho d ^ m * cubeFlat (l + m) f) ^ 2 * (3 : ℝ) ^ ((d + 2) * l) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2]
      ring

theorem eb4_flat_sub_le [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (eb4_mu d n)) (hg : MemLp g 2 (eb4_mu d n)) :
    cubeFlat n (fun x => f x - g x) ≤ cubeFlat n f + cubeFlat n g := by
  have h := cubeFlat_add_le hf (hg.const_mul (-1))
  have e : (fun x => f x - g x) = fun x => f x + (-1) * g x := by
    funext x
    ring
  rw [e]
  have h2 := cubeFlat_const_mul n (-1) g
  simp only [abs_neg, abs_one, one_mul] at h2
  rw [h2] at h
  exact h

theorem eb4_flat_sub_comm [NeZero d] (n : ℕ) (f g : Vec d → ℝ) :
    cubeFlat n (fun x => f x - g x) = cubeFlat n (fun x => g x - f x) := by
  have h := cubeFlat_const_mul n (-1) (fun x => f x - g x)
  simp only [abs_neg, abs_one, one_mul] at h
  rw [← h]
  congr 1
  funext x
  ring

theorem eb4_vecDot_sub (p q x : Vec d) : vecDot (p - q) x = vecDot p x - vecDot q x := by
  unfold vecDot
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring

theorem eb4_three_halves_le_sqrt : (3 : ℝ) / 2 ≤ Real.sqrt 3 :=
  Real.le_sqrt_of_sq_le (by norm_num)

/-- Flatness of a function whose slope is `x`-close and whose affine remainder is small. -/
theorem eb4_flat_le_of_slope [NeZero d] {k : ℕ} {v : Vec d → ℝ} (hv : MemLp v 2 (eb4_mu d k))
    (x : Vec d) {q : ℝ} (hq : q ≤ 1 / 2)
    (hA : cubeFlat k (fun y => v y - vecDot (affSlope k v) y) ≤ q * engNorm x)
    (hB : engNorm (affSlope k v - x) ≤ 1 / 2 * engNorm x) :
    cubeFlat k v ≤ engNorm x := by
  have hl := e0c_memLp k (e0c_continuous_vecDot (affSlope k v))
  have hvl : MemLp (fun y => v y - vecDot (affSlope k v) y) 2 (eb4_mu d k) := hv.sub hl
  have h1 := cubeFlat_add_le hvl hl
  have e : (fun y => (v y - vecDot (affSlope k v) y) + vecDot (affSlope k v) y) = v := by
    funext y
    ring
  rw [e, cubeFlat_vecDot] at h1
  have hs : engNorm (affSlope k v) ≤ 3 / 2 * engNorm x := by
    have := engNorm_add_le (affSlope k v - x) x
    rw [sub_add_cancel] at this
    linarith only [this, hB]
  have hx := engNorm_nonneg x
  have h3 : (3 : ℝ) ≤ 2 * Real.sqrt 3 := by linarith only [eb4_three_halves_le_sqrt]
  have h4 : engNorm (affSlope k v) / (2 * Real.sqrt 3) ≤ 1 / 2 * engNorm x := by
    rw [div_le_iff₀ (by linarith only [h3])]
    nlinarith only [hs, h3, hx]
  have h5 : q * engNorm x ≤ 1 / 2 * engNorm x := by
    exact mul_le_mul_of_nonneg_right hq hx
  linarith only [h1, hA, h4, h5]

/-- Drift of the best affine slope between two scales. -/
theorem eb4_drift [NeZero d] {l k : ℕ} (hlk : l ≤ k) {v : Vec d → ℝ}
    (hvk : MemLp v 2 (eb4_mu d k)) (hvl : MemLp v 2 (eb4_mu d l)) (x : Vec d) {q : ℝ}
    (hAk : cubeFlat k (fun y => v y - vecDot (affSlope k v) y) ≤ q * engNorm x)
    (hAl : cubeFlat l (fun y => v y - vecDot (affSlope l v) y) ≤ q * engNorm x) :
    cubeFlat k (fun y => v y - vecDot (affSlope l v) y) ≤
      (2 + eb4_rho d ^ (k - l)) * (q * engNorm x) := by
  have hlk' := e0c_memLp k (e0c_continuous_vecDot (affSlope k v))
  have hll' := e0c_memLp l (e0c_continuous_vecDot (affSlope l v))
  have hlk'' := e0c_memLp k (e0c_continuous_vecDot (affSlope k v - affSlope l v))
  have e1 : (fun y => v y - vecDot (affSlope l v) y) =
      fun y => (v y - vecDot (affSlope k v) y) + vecDot (affSlope k v - affSlope l v) y := by
    funext y
    rw [eb4_vecDot_sub]
    ring
  have hvk' : MemLp (fun y => v y - vecDot (affSlope k v) y) 2 (eb4_mu d k) := hvk.sub hlk'
  have h1 := cubeFlat_add_le hvk' hlk''
  rw [← e1] at h1
  have e2 : (fun y => vecDot (affSlope k v - affSlope l v) y) =
      fun y => (v y - vecDot (affSlope l v) y) - (v y - vecDot (affSlope k v) y) := by
    funext y
    rw [eb4_vecDot_sub]
    ring
  have h2 : cubeFlat k (fun y => vecDot (affSlope k v - affSlope l v) y) =
      cubeFlat l (fun y => vecDot (affSlope k v - affSlope l v) y) := by
    rw [cubeFlat_vecDot, cubeFlat_vecDot]
  have hm1 : MemLp (fun y => v y - vecDot (affSlope l v) y) 2 (eb4_mu d l) := hvl.sub hll'
  have hm2 : MemLp (fun y => v y - vecDot (affSlope k v) y) 2 (eb4_mu d l) :=
    hvl.sub (e0c_memLp l (e0c_continuous_vecDot (affSlope k v)))
  have h3 := eb4_flat_sub_le hm1 hm2
  rw [← e2] at h3
  have h4 := eb4_flat_mono hlk hvk'
  have hx := engNorm_nonneg x
  have hρ := pow_nonneg (eb4_rho_pos d).le (k - l)
  have h5 : eb4_rho d ^ (k - l) * cubeFlat k (fun y => v y - vecDot (affSlope k v) y) ≤
      eb4_rho d ^ (k - l) * (q * engNorm x) := mul_le_mul_of_nonneg_left hAk hρ
  nlinarith only [h1, h2, h3, h4, h5, hAk, hAl, hρ]

end SuperdiffusionCLT.Section6
