/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.AffineSlope

/-!
# Finite-volume estimate: restriction and norm helpers

Restriction of solutions on origin cubes, `L²` membership on smaller cubes, the triangle
inequality for the flatness seminorm of differences, and the growth bound
`Ω_k(V_m x) ≤ C 3^{κ(m-k)} |x|` that follows from the chain and the flatness blocks.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb5b_cube_mono {k m : ℕ} (h : k ≤ m) : engCube d k ⊆ engCube d m := by
  intro y hy
  have hy' := mem_openCubeSet_originCube_iff.1 hy
  show y ∈ openCubeSet (originCube d (m : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi := hy' i
  have hle : (3 : ℝ) ^ (k : ℤ) ≤ (3 : ℝ) ^ (m : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact pow_le_pow_right₀ (by norm_num) h
  constructor <;> linarith only [hi.1, hi.2, hle]

theorem eb5b_restrict {a : CoeffField d} {k m : ℕ} {u : Vec d → ℝ}
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d k) a) (hkm : k ≤ m)
    (h : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) u g) :
    ∃ g : Vec d → Vec d, IsSolOn a (engCube d k) u g := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, IsSolOn.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _) (eb5b_cube_mono hkm)
    (volume_openCubeSet_lt_top _).ne hell hg⟩

theorem eb5b_memLp {a : CoeffField d} {k m : ℕ} {u : Vec d → ℝ}
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d k) a) (hkm : k ≤ m)
    (h : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) u g) :
    MemLp u 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := by
  obtain ⟨g, hg⟩ := eb5b_restrict hell hkm h
  exact hg.memLp.1

theorem eb5b_sol_sub {a : CoeffField d} {m : ℕ} {u v : Vec d → ℝ}
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d m) a)
    (hu : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) u g)
    (hv : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) v g) :
    ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) (fun x => u x - v x) g := by
  obtain ⟨g1, h1⟩ := hu
  obtain ⟨g2, h2⟩ := hv
  exact ⟨_, IsSolOn.sub hell h1 h2⟩

theorem eb5b_flat_sub_le [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeFlat n (fun x => f x - g x) ≤ cubeFlat n f + cubeFlat n g := by
  have hng : MemLp (fun x => (-1 : ℝ) * g x) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hg.const_mul (-1)
  have h := cubeFlat_add_le hf hng
  have e : cubeFlat n (fun x => (-1 : ℝ) * g x) = cubeFlat n g := by
    rw [cubeFlat_const_mul]; simp
  have e2 : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by
    funext x; ring
  rw [e2]
  linarith only [h, e]

theorem eb5b_engNorm_zero : engNorm (0 : Vec d) = 0 := by
  unfold engNorm vecNormSq vecDot
  simp

theorem eb5b_engNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Vec d) :
    engNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, engNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eb5b_engNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (engNorm_add_le _ _).trans (by linarith only [ih])

theorem eb5b_engNorm_sub_le (x y : Vec d) : engNorm (x - y) ≤ engNorm x + engNorm y := by
  have h : x - y = x + (-1 : ℝ) • y := by
    rw [neg_one_smul, sub_eq_add_neg]
  rw [h]
  refine (engNorm_add_le _ _).trans ?_
  rw [engNorm_smul]
  simp

/-- Growth of a corrected affine function at a lower scale. -/
theorem eb5b_V_bound [NeZero d] {a : CoeffField d} {K Cc δk κ : ℝ} {k m : ℕ}
    (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hKδ : K * δk ≤ 1) (hδ1 : δk ≤ 1) (hCc : 1 ≤ Cc) (hkm : k ≤ m)
    (hVk : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d k) (V k e) g)
    (hVm : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) (V m e) g)
    (hflat : ∀ e : Vec d,
      cubeFlat k (fun x => V k e x - vecDot (affSlope k (V k e)) x) ≤ K * δk * engNorm e ∧
        engNorm (affSlope k (V k e) - e) ≤ K * δk * ((k : ℝ) - (k : ℝ) + 1) * engNorm e)
    (hchain : ∀ e : Vec d, ∃ q : Vec d,
      affSlope k (V k q) = affSlope k (V m e) ∧
        cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δk * engNorm q ∧
        engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q)
    (x : Vec d) :
    cubeFlat k (V m x) ≤ Cc * (Cc + 2) * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm x := by
  obtain ⟨q, -, hq1, hq2, -⟩ := hchain x
  obtain ⟨hf1, hf2⟩ := hflat q
  have hmk := eb5b_memLp (hell k) le_rfl (hVk q)
  have hmm := eb5b_memLp (hell k) hkm (hVm x)
  have hell' : MemLp (fun y : Vec d => vecDot (affSlope k (V k q)) y) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    e0c_memLp k (e0c_continuous_vecDot _)
  set s := affSlope k (V k q) with hs
  have hq0 := engNorm_nonneg q
  have hx0 := engNorm_nonneg x
  -- Ω_k(V_k q)
  have hl : cubeFlat k (fun y => vecDot s y) = engNorm s / (2 * Real.sqrt 3) :=
    cubeFlat_vecDot k s
  have h3 : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
    have : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith only [this]
  have hsq : engNorm s ≤ 2 * engNorm q := by
    have h1 : engNorm s ≤ engNorm q + engNorm (s - q) := by
      have := eb5b_engNorm_sub_le s (s - q)
      have e : s - (s - q) = q := by abel
      rw [e] at this
      have h2 := engNorm_add_le q (s - q)
      have e2 : q + (s - q) = s := by abel
      rw [e2] at h2
      exact h2
    have h2 : ((k : ℝ) - (k : ℝ) + 1) = 1 := by ring
    rw [h2] at hf2
    nlinarith only [h1, hf2, hKδ, hq0]
  have hlq : cubeFlat k (fun y => vecDot s y) ≤ engNorm q := by
    rw [hl, div_le_iff₀ (by linarith only [h3])]
    have := mul_le_mul_of_nonneg_left h3 hq0
    linarith only [hsq, this]
  have hVq : cubeFlat k (V k q) ≤ 2 * engNorm q := by
    have e : cubeFlat k (V k q) =
        cubeFlat k (fun y => (V k q y - vecDot s y) + vecDot s y) := by
      congr 1; funext y; ring
    have hadd : cubeFlat k (fun y => (V k q y - vecDot s y) + vecDot s y) ≤
        cubeFlat k (fun y => V k q y - vecDot s y) + cubeFlat k (fun y => vecDot s y) :=
      cubeFlat_add_le (hmk.sub hell') hell'
    have : cubeFlat k (fun y => V k q y - vecDot s y) ≤ engNorm q := by
      nlinarith only [hf1, hKδ, hq0]
    linarith only [hadd, this, hlq, e]
  have hVx : cubeFlat k (V m x) ≤ (Cc + 2) * engNorm q := by
    have e : cubeFlat k (V m x) =
        cubeFlat k (fun y => (V m x y - V k q y) + V k q y) := by
      congr 1; funext y; ring
    have hadd : cubeFlat k (fun y => (V m x y - V k q y) + V k q y) ≤
        cubeFlat k (fun y => V m x y - V k q y) + cubeFlat k (V k q) :=
      cubeFlat_add_le (hmm.sub hmk) hmk
    have : Cc * δk * engNorm q ≤ Cc * engNorm q := by
      have := mul_le_mul_of_nonneg_left hδ1 (by linarith only [hCc] : 0 ≤ Cc)
      nlinarith only [this, hq0]
    linarith only [hadd, hq1, this, hVq, e]
  calc cubeFlat k (V m x) ≤ (Cc + 2) * engNorm q := hVx
    _ ≤ (Cc + 2) * (Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm x) :=
        mul_le_mul_of_nonneg_left hq2 (by linarith only [hCc])
    _ = Cc * (Cc + 2) * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm x := by ring

end SuperdiffusionCLT.Section6
