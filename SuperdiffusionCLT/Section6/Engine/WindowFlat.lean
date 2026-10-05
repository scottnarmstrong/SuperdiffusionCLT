/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.AffineSlopeB
public import SuperdiffusionCLT.Section6.Engine.SolutionLimit

/-!
# Window flatness: scale and slope lemmas
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb3_memLp_le {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    MemLp f 2 (normalizedCubeMeasure (originCube d (l : ℤ))) := by
  induction k, hlk using Nat.le_induction with
  | base => exact hf
  | succ k _ ih => exact ih (e0b_memLp_step hf).1

theorem eb3_cube_mono {m n : ℕ} (h : m ≤ n) : engCube d m ⊆ engCube d n := by
  intro y hy
  have hy' := mem_openCubeSet_originCube_iff.1 hy
  show y ∈ openCubeSet (originCube d (n : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi := hy' i
  have hle : (3 : ℝ) ^ (m : ℤ) ≤ (3 : ℝ) ^ (n : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) h
  constructor <;> linarith only [hi.1, hi.2, hle]

theorem eb3_isElliptic_one (n : ℕ) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) (fun _ => (1 : Mat d)) :=
  ⟨1, 1, e0e_isElliptic_one (measurableSet_openCubeSet _)⟩

theorem eb3_sq_to_lin {a b P Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 < P) (hQ : 1 ≤ Q)
    (h : a ^ 2 * P ≤ b ^ 2 * (P * Q)) : a ≤ Q * b := by
  have h1 : a ^ 2 ≤ b ^ 2 * Q := by
    have h2 : a ^ 2 * P ≤ (b ^ 2 * Q) * P := by
      calc a ^ 2 * P ≤ b ^ 2 * (P * Q) := h
        _ = (b ^ 2 * Q) * P := by ring
    exact le_of_mul_le_mul_right h2 hP
  have h3 : b ^ 2 * Q ≤ (Q * b) ^ 2 := by
    have : 0 ≤ b ^ 2 := sq_nonneg b
    nlinarith only [this, hQ]
  exact (pow_le_pow_iff_left₀ ha (mul_nonneg (by linarith only [hQ]) hb) two_ne_zero).1
    (h1.trans h3)

theorem eb3_flat_le [NeZero d] {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    cubeFlat l f ≤ (3 : ℝ) ^ ((d + 2) * (k - l)) * cubeFlat k f := by
  have h := cubeFlat_mono_scale hlk hf
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlk
  have hm : l + m - l = m := by omega
  rw [hm]
  have hp : (3 : ℝ) ^ ((d + 2) * (l + m)) = 3 ^ ((d + 2) * l) * 3 ^ ((d + 2) * m) := by
    rw [mul_add, pow_add]
  rw [hp] at h
  exact eb3_sq_to_lin (cubeFlat_nonneg _ _) (cubeFlat_nonneg _ _) (by positivity)
    (one_le_pow₀ (by norm_num)) h

theorem eb3_l2_le [NeZero d] {l k : ℕ} (hlk : l ≤ k) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) :
    cubeL2 l f ≤ (3 : ℝ) ^ (d * (k - l)) * cubeL2 k f := by
  have h := cubeL2_mono_scale hlk hf
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hlk
  have hm : l + m - l = m := by omega
  rw [hm]
  have hp : (3 : ℝ) ^ (d * (l + m)) = 3 ^ (d * l) * 3 ^ (d * m) := by
    rw [mul_add, pow_add]
  rw [hp] at h
  exact eb3_sq_to_lin (cubeL2_nonneg _ _) (cubeL2_nonneg _ _) (by positivity)
    (one_le_pow₀ (by norm_num)) h

theorem eb3_flat_diff [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeFlat n f ≤ cubeFlat n g + ((3 : ℝ)⁻¹) ^ n * cubeL2 n (fun x => f x - g x) := by
  have hfg : MemLp (fun x => f x - g x) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hf.sub hg
  have h2 := cubeFlat_add_le hg hfg
  have h1 : (fun x => g x + (f x - g x)) = f := by funext x; ring
  rw [h1] at h2
  have h3 := cubeFlat_le_of_sub_const hfg 0
  simp only [sub_zero] at h3
  linarith only [h2, h3]

theorem eb3_slope_sub [NeZero d] {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (p : Vec d) :
    affSlope n (fun x => f x - vecDot p x) = affSlope n f - p := by
  have hl := e0c_memLp n (e0c_continuous_vecDot p)
  have hfl : MemLp (fun x => f x - vecDot p x) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := hf.sub hl
  have h := affSlope_add hfl hl
  have e1 : (fun x => (f x - vecDot p x) + vecDot p x) = f := by funext x; ring
  have h2 : affSlope n (fun x => vecDot p x) = p := by
    simpa using affSlope_affine n 0 p
  rw [e1, h2] at h
  have h3 := h
  exact eq_sub_of_add_eq h3.symm

theorem eb3_sqrt3_le : 2 * Real.sqrt 3 ≤ 4 := by
  have : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  linarith only [this]

theorem eb3_slope_dist [NeZero d] {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (p : Vec d) :
    engNorm (affSlope n f - p) ≤ 4 * cubeFlat n (fun x => f x - vecDot p x) := by
  have hl := e0c_memLp n (e0c_continuous_vecDot p)
  have hfl : MemLp (fun x => f x - vecDot p x) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := hf.sub hl
  rw [← eb3_slope_sub hf p]
  have h := engNorm_affSlope_le hfl
  have h0 := cubeFlat_nonneg n (fun x => f x - vecDot p x)
  have h1 := eb3_sqrt3_le
  nlinarith only [h, h0, h1]

theorem eb3_slope_step [NeZero d] {i : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d ((i + 1 : ℕ) : ℤ)))) :
    engNorm (affSlope i f - affSlope (i + 1) f) ≤ 4 * (3 : ℝ) ^ (d + 2) *
      cubeFlat (i + 1) (fun x => f x - vecDot (affSlope (i + 1) f) x) := by
  have hi := eb3_memLp_le (Nat.le_succ i) hf
  have h1 := eb3_slope_dist hi (affSlope (i + 1) f)
  have hl := e0c_memLp (i + 1) (e0c_continuous_vecDot (affSlope (i + 1) f))
  have hfl : MemLp (fun x => f x - vecDot (affSlope (i + 1) f) x) 2
      (normalizedCubeMeasure (originCube d ((i + 1 : ℕ) : ℤ))) := hf.sub hl
  have h2 := eb3_flat_le (Nat.le_succ i) hfl
  have h3 : i + 1 - i = 1 := by omega
  rw [h3, mul_one] at h2
  calc _ ≤ 4 * cubeFlat i (fun x => f x - vecDot (affSlope (i + 1) f) x) := h1
    _ ≤ 4 * ((3 : ℝ) ^ (d + 2) * cubeFlat (i + 1) (fun x => f x - vecDot (affSlope (i + 1) f) x)) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = _ := by ring

theorem eb3_slope_chain [NeZero d] {j : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (j : ℤ)))) (e : Vec d) (B0 B : ℝ)
    (h0 : cubeFlat j (fun x => f x - vecDot e x) ≤ B0) :
    ∀ n i : ℕ, i + n = j →
      (∀ i' : ℕ, i ≤ i' → i' ≤ j →
        cubeFlat i' (fun x => f x - vecDot (affSlope i' f) x) ≤ B) →
      engNorm (affSlope i f - e) ≤ 4 * B0 + 4 * (3 : ℝ) ^ (d + 2) * B * n := by
  intro n
  induction n with
  | zero =>
    intro i hij _
    have hj : i = j := by omega
    subst hj
    have h := eb3_slope_dist hf e
    simp only [Nat.cast_zero, mul_zero, add_zero]
    linarith only [h, h0]
  | succ n ih =>
    intro i hij hB
    have hi1 : i + 1 + n = j := by omega
    have hf1 : MemLp f 2 (normalizedCubeMeasure (originCube d ((i + 1 : ℕ) : ℤ))) :=
      eb3_memLp_le (by omega) hf
    have h1 := ih (i + 1) hi1 (fun i' h1 h2 => hB i' (by omega) h2)
    have h2 := eb3_slope_step hf1
    have h3 := hB (i + 1) (by omega) (by omega)
    have h4 : engNorm (affSlope i f - e) ≤
        engNorm (affSlope i f - affSlope (i + 1) f) + engNorm (affSlope (i + 1) f - e) := by
      have := engNorm_add_le (affSlope i f - affSlope (i + 1) f) (affSlope (i + 1) f - e)
      have e2 : affSlope i f - affSlope (i + 1) f + (affSlope (i + 1) f - e) =
          affSlope i f - e := by abel
      rwa [e2] at this
    have hc : (0 : ℝ) ≤ 4 * (3 : ℝ) ^ (d + 2) := by positivity
    have h5 := mul_le_mul_of_nonneg_left h3 hc
    push_cast
    nlinarith only [h1, h2, h4, h5]

end SuperdiffusionCLT.Section6
