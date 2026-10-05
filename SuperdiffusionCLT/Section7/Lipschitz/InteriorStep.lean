/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section6.Engine.WindowFlat
public import SuperdiffusionCLT.Section6.Engine.Solutions

/-!
# The interior one-step inequality of the large-scale Lipschitz iteration
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ}

private theorem lip_int_step_vecDot_add (p q x : Vec d) :
    vecDot (p + q) x = vecDot p x + vecDot q x := by
  simp [vecDot, add_mul, Finset.sum_add_distrib]

private theorem lip_int_step_inv_mul (a b : ℕ) (h : a ≤ b) :
    ((3 : ℝ)⁻¹) ^ a * (3 : ℝ) ^ b = (3 : ℝ) ^ (b - a) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  have h3 : (3 : ℝ) ^ a ≠ 0 := by positivity
  rw [pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ h3, one_mul, Nat.add_sub_cancel_left]

private theorem lip_int_step_sq_lin {a b P Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hP : 0 < P)
    (hQ : 1 ≤ Q) (h : a ^ 2 * P ≤ b ^ 2 * (P * Q)) : a ≤ Q * b :=
  Section6.eb3_sq_to_lin ha hb hP hQ h

private theorem lip_int_step_memLp_vecDot [NeZero d] (n : ℕ) (p : Vec d) :
    MemLp (fun x => vecDot p x) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
  Section6.e0c_memLp n (Section6.e0c_continuous_vecDot p)


private theorem lip_int_step_L2_down [NeZero d] {l m K : ℕ} (hK : K = l + m) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (K : ℤ)))) :
    Section6.cubeL2 l f ≤ (3 : ℝ) ^ (d * m) * Section6.cubeL2 K f := by
  subst hK
  have h := Section6.cubeL2_mono_scale (Nat.le_add_right l m) hf
  refine lip_int_step_sq_lin (Section6.cubeL2_nonneg _ _) (Section6.cubeL2_nonneg _ _)
    (P := (3 : ℝ) ^ (d * l)) (Q := (3 : ℝ) ^ (d * m)) (by positivity)
    (one_le_pow₀ (by norm_num)) ?_
  rw [← pow_add, ← mul_add]
  exact h

private theorem lip_int_step_flat_down [NeZero d] {l m K : ℕ} (hK : K = l + m) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (K : ℤ)))) :
    Section6.cubeFlat l f ≤ (3 : ℝ) ^ ((d + 2) * m) * Section6.cubeFlat K f := by
  subst hK
  have h := Section6.cubeFlat_mono_scale (Nat.le_add_right l m) hf
  refine lip_int_step_sq_lin (Section6.cubeFlat_nonneg _ _) (Section6.cubeFlat_nonneg _ _)
    (P := (3 : ℝ) ^ ((d + 2) * l)) (Q := (3 : ℝ) ^ ((d + 2) * m)) (by positivity)
    (one_le_pow₀ (by norm_num)) ?_
  rw [← pow_add, ← mul_add]
  exact h

private theorem lip_int_step_decay {K L m : ℕ} (hK : K = L + m) {z Φ Ch : ℝ} (h : z * (9 : ℝ) ^ m ≤ Ch * (3 : ℝ) ^ K * Φ) :
    ((3 : ℝ)⁻¹) ^ L * z ≤ 9 * ((3 : ℝ)⁻¹) ^ (m + 2) * Ch * Φ := by
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hid : ((3 : ℝ)⁻¹) ^ L * (3 : ℝ) ^ K = (3 : ℝ) ^ m := by
    rw [lip_int_step_inv_mul L K (by omega), show K - L = m by omega]
  have h9 : (9 : ℝ) ^ m = (3 : ℝ) ^ m * (3 : ℝ) ^ m := by
    rw [← mul_pow]; norm_num
  have hL : 0 ≤ ((3 : ℝ)⁻¹) ^ L := by positivity
  have h1 : ((3 : ℝ)⁻¹) ^ L * (z * (9 : ℝ) ^ m) ≤
      ((3 : ℝ)⁻¹) ^ L * (Ch * (3 : ℝ) ^ K * Φ) := mul_le_mul_of_nonneg_left h hL
  have h2 : (((3 : ℝ)⁻¹) ^ L * z * (3 : ℝ) ^ m) * (3 : ℝ) ^ m ≤ (Ch * Φ) * (3 : ℝ) ^ m := by
    calc (((3 : ℝ)⁻¹) ^ L * z * (3 : ℝ) ^ m) * (3 : ℝ) ^ m
        = ((3 : ℝ)⁻¹) ^ L * (z * (9 : ℝ) ^ m) := by rw [h9]; ring
      _ ≤ ((3 : ℝ)⁻¹) ^ L * (Ch * (3 : ℝ) ^ K * Φ) := h1
      _ = (Ch * Φ) * (((3 : ℝ)⁻¹) ^ L * (3 : ℝ) ^ K) := by ring
      _ = (Ch * Φ) * (3 : ℝ) ^ m := by rw [hid]
  have h4 := le_of_mul_le_mul_right h2 h3m
  have hinv : ((3 : ℝ)⁻¹) ^ m * (3 : ℝ) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  have h9' : 9 * ((3 : ℝ)⁻¹) ^ (m + 2) = ((3 : ℝ)⁻¹) ^ m := by
    rw [pow_add]; norm_num; ring
  have h5 : 0 ≤ ((3 : ℝ)⁻¹) ^ m := by positivity
  calc ((3 : ℝ)⁻¹) ^ L * z
      = (((3 : ℝ)⁻¹) ^ L * z * (3 : ℝ) ^ m) * ((3 : ℝ)⁻¹) ^ m := by
        calc ((3 : ℝ)⁻¹) ^ L * z = ((3 : ℝ)⁻¹) ^ L * z * (((3 : ℝ)⁻¹) ^ m * (3 : ℝ) ^ m) := by
              rw [hinv, mul_one]
          _ = _ := by ring
    _ ≤ (Ch * Φ) * ((3 : ℝ)⁻¹) ^ m := mul_le_mul_of_nonneg_right h4 h5
    _ = 9 * ((3 : ℝ)⁻¹) ^ (m + 2) * Ch * Φ := by rw [← h9']; ring

/-- **The interior one-step inequality**.  `Cin` bounds the harmonic
approximation, `Ch` is the constant of `Section6.eng_harmonic_affine`.  The constant `C₁` of the
contraction does not depend on `k₀`. -/
theorem lip_int_step (d : ℕ) [NeZero d] (Cin Ch : ℝ) (hCin : 1 ≤ Cin) (hCh : 1 ≤ Ch) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ k₀ : ℕ, 3 ≤ k₀ → ∃ C₂ : ℝ, 1 ≤ C₂ ∧
      ∀ (a : CoeffField d) (s δ : ℝ) (k : ℕ), k₀ ≤ k → 0 < s → 0 ≤ δ →
        (∀ (K l : ℕ), l + 1 ≤ K → ∀ (w : Vec d → ℝ) (gw : Vec d → Vec d),
          Section6.IsSolOn (fun _ => (1 : Mat d)) (Section6.engCube d K) w gw →
          ∃ (p : Vec d) (c : ℝ),
            Section6.cubeL2 l (fun x => w x - c - vecDot p x) * (9 : ℝ) ^ (K - l) ≤
                Ch * (3 : ℝ) ^ K * Section6.cubeFlat K w ∧
              Section6.engNorm p ≤ Ch * Section6.cubeFlat K w) →
        LipHarmInt a s δ Cin (k + 1) →
        ∀ (f : Vec d → ℝ) (F : ℝ) (u : H1Function (Section6.engCube d (k + 1))),
          IsWeakSolutionOn a (Section6.engCube d (k + 1)) u f (fun _ => 0) → 0 ≤ F →
          (∀ᵐ x ∂volume.restrict (Section6.engCube d (k + 1)), |f x| ≤ F) →
          ∀ p : Vec d, ∃ p' : Vec d,
            Section6.cubeFlat (k - k₀) (fun x => u.toFun x - vecDot p' x) ≤
              (C₁ * ((3 : ℝ)⁻¹) ^ k₀ + C₂ * δ) *
                  Section6.cubeFlat (k + 1) (fun x => u.toFun x - vecDot p x) +
                C₂ * δ * Section6.engNorm p + C₂ * s⁻¹ * (3 : ℝ) ^ k * F := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  refine ⟨9 * Ch * (3 : ℝ) ^ ((d + 2) * 3), ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((d + 2) * 3) := one_le_pow₀ (by norm_num)
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (9 * Ch) * (3 : ℝ) ^ ((d + 2) * 3) :=
        mul_le_mul (by linarith only [hCh]) h1 zero_le_one (by linarith only [hCh])
      _ = _ := by ring
  intro k₀ hk₀
  obtain ⟨m, rfl⟩ : ∃ m, k₀ = m + 2 := ⟨k₀ - 2, by omega⟩
  have hX1 : (1 : ℝ) ≤ (3 : ℝ) ^ (d * (m + 2)) := one_le_pow₀ (by norm_num)
  have hY1 : (1 : ℝ) ≤ (3 : ℝ) ^ (m + 4) := one_le_pow₀ (by norm_num)
  have hW1 : (1 : ℝ) ≤ (3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4) :=
    one_le_mul_of_one_le_of_one_le hX1 hY1
  refine ⟨Cin * ((3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4)) * (1 + 729 * Ch), ?_, ?_⟩
  · have h2 : (1 : ℝ) ≤ Cin * ((3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4)) :=
      one_le_mul_of_one_le_of_one_le hCin hW1
    have h4 : (1 : ℝ) ≤ 1 + 729 * Ch := by linarith only [hCh]
    exact one_le_mul_of_one_le_of_one_le h2 h4
  intro a s δ k hk hs hδ hblk hharm f F u hu hF hfF p
  obtain ⟨w, gw, hw, hwb⟩ := hharm f F u hu hF hfF
  have e3 : k + 1 - 3 = k - 2 := by omega
  rw [e3] at hw hwb
  have hpl : ∀ (n : ℕ) (q : Vec d), MemLp (fun x => vecDot q x) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := fun n q => lip_int_step_memLp_vecDot n q
  have hU : MemLp u.toFun 2 (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ))) :=
    memL2On_openCubeSet_normalizedCubeMeasure u.memL2
  have hUp : MemLp (fun x => u.toFun x - vecDot p x) 2
      (normalizedCubeMeasure (originCube d ((k + 1 : ℕ) : ℤ))) := hU.sub (hpl _ p)
  have hUK : MemLp (fun x => u.toFun x - vecDot p x) 2
      (normalizedCubeMeasure (originCube d ((k - 2 : ℕ) : ℤ))) :=
    Section6.eb3_memLp_le (by omega) hUp
  have hwK : MemLp w 2 (normalizedCubeMeasure (originCube d ((k - 2 : ℕ) : ℤ))) :=
    (Section6.IsSolOn.memLp hw).1
  have hg1K : MemLp (fun x => u.toFun x - w x) 2
      (normalizedCubeMeasure (originCube d ((k - 2 : ℕ) : ℤ))) :=
    (Section6.eb3_memLp_le (by omega) hU).sub hwK
  have hvK : MemLp (fun x => w x - vecDot p x) 2
      (normalizedCubeMeasure (originCube d ((k - 2 : ℕ) : ℤ))) := hwK.sub (hpl _ p)
  have hv : Section6.IsSolOn (fun _ => (1 : Mat d)) (Section6.engCube d (k - 2))
      (fun x => w x - vecDot p x) (fun x => gw x - p) := by
    have h := Section6.IsSolOn.sub (Section6.eb3_isElliptic_one (d := d) (k - 2)) hw
      (Section6.isSolOn_one_affine (d := d) (k - 2) 0 p)
    have e1 : (fun x => w x - vecDot p x) = fun x => w x - (0 + vecDot p x) := by
      funext x; simp
    rw [e1]
    exact h
  obtain ⟨q, c, hq1, -⟩ := hblk (k - 2) (k - (m + 2)) (by omega) _ _ hv
  rw [show k - 2 - (k - (m + 2)) = m by omega] at hq1
  refine ⟨p + q, ?_⟩
  -- the flatness at the scale `k - (m+2)`
  have hg1L : MemLp (fun x => u.toFun x - w x) 2
      (normalizedCubeMeasure (originCube d ((k - (m + 2) : ℕ) : ℤ))) :=
    Section6.eb3_memLp_le (by omega) hg1K
  have hg2L : MemLp (fun x => w x - vecDot p x - c - vecDot q x) 2
      (normalizedCubeMeasure (originCube d ((k - (m + 2) : ℕ) : ℤ))) :=
    (((Section6.eb3_memLp_le (by omega) hvK).sub (memLp_const c))).sub (hpl _ q)
  have hfun : (fun x => u.toFun x - vecDot (p + q) x) = fun x =>
      ((u.toFun x - w x) + (w x - vecDot p x - c - vecDot q x)) + c := by
    funext x; rw [lip_int_step_vecDot_add]; ring
  have hS1 : Section6.cubeFlat (k - (m + 2)) (fun x => u.toFun x - vecDot (p + q) x) ≤
      Section6.cubeFlat (k - (m + 2)) (fun x => u.toFun x - w x) +
        Section6.cubeFlat (k - (m + 2)) (fun x => w x - vecDot p x - c - vecDot q x) := by
    have hsum : MemLp (fun x => (u.toFun x - w x) + (w x - vecDot p x - c - vecDot q x)) 2
        (normalizedCubeMeasure (originCube d ((k - (m + 2) : ℕ) : ℤ))) := hg1L.add hg2L
    rw [hfun, Section6.cubeFlat_add_const hsum]
    exact Section6.cubeFlat_add_le hg1L hg2L
  have hS2 : Section6.cubeFlat (k - (m + 2)) (fun x => u.toFun x - w x) ≤
      ((3 : ℝ)⁻¹) ^ (k - (m + 2)) * Section6.cubeL2 (k - (m + 2)) (fun x => u.toFun x - w x) := by
    have := Section6.cubeFlat_le_of_sub_const hg1L 0
    simpa only [sub_zero] using this
  have hS3 : Section6.cubeFlat (k - (m + 2))
        (fun x => w x - vecDot p x - c - vecDot q x) ≤
      ((3 : ℝ)⁻¹) ^ (k - (m + 2)) *
        Section6.cubeL2 (k - (m + 2)) (fun x => w x - vecDot p x - c - vecDot q x) := by
    have := Section6.cubeFlat_le_of_sub_const hg2L 0
    simpa only [sub_zero] using this
  -- second part: decay of the affine block
  have hS4 := lip_int_step_decay (K := k - 2) (L := k - (m + 2)) (m := m) (by omega)
    hq1
  -- first part: restriction
  have hS5 := lip_int_step_L2_down (l := k - (m + 2)) (m := m) (K := k - 2) (by omega) hg1K
  -- flatness of the affine function
  have hS6 : Section6.cubeFlat (k - 2) (fun x => w x - vecDot p x) ≤
      Section6.cubeFlat (k - 2) (fun x => u.toFun x - vecDot p x) +
        ((3 : ℝ)⁻¹) ^ (k - 2) * Section6.cubeL2 (k - 2) (fun x => u.toFun x - w x) := by
    have h := Section6.eb3_flat_diff hvK hUK
    have e : Section6.cubeL2 (k - 2) (fun x => (w x - vecDot p x) - (u.toFun x - vecDot p x)) =
        Section6.cubeL2 (k - 2) (fun x => u.toFun x - w x) := by
      have := Section6.cubeL2_const_mul (d := d) (k - 2) (-1) (fun x => u.toFun x - w x)
      rw [abs_neg, abs_one, one_mul] at this
      rw [← this]
      congr 1; funext x; ring
    rw [e] at h
    exact h
  have hS7 := lip_int_step_flat_down (l := k - 2) (m := 3) (K := k + 1) (by omega) hUp
  have hS8 : Section6.cubeFlat (k + 1) u.toFun ≤ Section6.cubeFlat (k + 1)
      (fun x => u.toFun x - vecDot p x) + Section6.engNorm p := by
    have h := Section6.cubeFlat_add_le hUp (hpl ((k + 1 : ℕ)) p)
    have e : (fun x => (u.toFun x - vecDot p x) + vecDot p x) = u.toFun := by
      funext x; ring
    rw [e, Section6.cubeFlat_vecDot] at h
    have hP := Section6.engNorm_nonneg p
    have : Section6.engNorm p / (2 * Real.sqrt 3) ≤ Section6.engNorm p := by
      refine div_le_self hP ?_
      have : (1 : ℝ) ≤ Real.sqrt 3 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      linarith only [this]
    linarith only [h, this]
  -- the arithmetic
  have hy0 : 0 ≤ Section6.cubeFlat (k + 1) (fun x => u.toFun x - vecDot p x) :=
    Section6.cubeFlat_nonneg _ _
  have hP0 : 0 ≤ Section6.engNorm p := Section6.engNorm_nonneg p
  have I1 : ((3 : ℝ)⁻¹) ^ (k - (m + 2)) * (3 : ℝ) ^ (k + 1) = (3 : ℝ) ^ (m + 2 + 1) := by
    rw [lip_int_step_inv_mul _ _ (by omega), show k + 1 - (k - (m + 2)) = m + 2 + 1 by omega]
  have I2 : ((3 : ℝ)⁻¹) ^ (k - (m + 2)) * ((3 : ℝ) ^ (k + 1)) ^ 2 =
      (3 : ℝ) ^ (m + 2 + 2) * (3 : ℝ) ^ k := by
    rw [← pow_mul, lip_int_step_inv_mul _ _ (by omega), ← pow_add]
    congr 1; omega
  have I3 : ((3 : ℝ)⁻¹) ^ (k - 2) * (3 : ℝ) ^ (k + 1) = 27 := by
    rw [lip_int_step_inv_mul _ _ (by omega), show k + 1 - (k - 2) = 3 by omega]; norm_num
  have I4 : ((3 : ℝ)⁻¹) ^ (k - 2) * ((3 : ℝ) ^ (k + 1)) ^ 2 = 81 * (3 : ℝ) ^ k := by
    rw [← pow_mul, lip_int_step_inv_mul _ _ (by omega),
      show (k + 1) * 2 - (k - 2) = 4 + k by omega, pow_add]
    norm_num
  have hα0 : 0 ≤ ((3 : ℝ)⁻¹) ^ (k - (m + 2)) := by positivity
  have hβ0 : 0 ≤ ((3 : ℝ)⁻¹) ^ (k - 2) := by positivity
  have hτ0 : 0 ≤ ((3 : ℝ)⁻¹) ^ (m + 2) := by positivity
  have hτ1 : ((3 : ℝ)⁻¹) ^ (m + 2) ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
  generalize hα : ((3 : ℝ)⁻¹) ^ (k - (m + 2)) = α at *
  generalize hβ : ((3 : ℝ)⁻¹) ^ (k - 2) = β at *
  generalize hτ : ((3 : ℝ)⁻¹) ^ (m + 2) = τ at *
  have hXm : (3 : ℝ) ^ (d * m) ≤ (3 : ℝ) ^ (d * (m + 2)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (by omega))
  have h33 : (3 : ℝ) ^ (m + 3) ≤ (3 : ℝ) ^ (m + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hXm0 : (0 : ℝ) ≤ (3 : ℝ) ^ (d * m) := by positivity
  have hQ0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((d + 2) * 3) := by positivity
  have hCin0 : 0 ≤ Cin := by linarith only [hCin]
  have hCh0 : 0 ≤ Ch := by linarith only [hCh]
  generalize hFqdef : Section6.cubeFlat (k - (m + 2)) (fun x => u.toFun x - vecDot (p + q) x) = Fq
    at hS1 ⊢
  generalize hEdef : Section6.cubeL2 (k - 2) (fun x => u.toFun x - w x) = E at *
  generalize hydef : Section6.cubeFlat (k + 1) (fun x => u.toFun x - vecDot p x) = y at *
  generalize hPdef : Section6.engNorm p = P at *
  generalize hFlv : Section6.cubeFlat (k - 2) (fun x => w x - vecDot p x) = Flv at *
  generalize hFU : Section6.cubeFlat (k - 2) (fun x => u.toFun x - vecDot p x) = FU at *
  generalize hFu : Section6.cubeFlat (k + 1) u.toFun = Fu at *
  generalize hL1 : Section6.cubeL2 (k - (m + 2)) (fun x => u.toFun x - w x) = L1 at *
  generalize hL2 : Section6.cubeL2 (k - (m + 2)) (fun x => w x - vecDot p x - c - vecDot q x)
    = L2 at *
  generalize hG1 : Section6.cubeFlat (k - (m + 2)) (fun x => u.toFun x - w x) = G1 at *
  generalize hG2 : Section6.cubeFlat (k - (m + 2)) (fun x => w x - vecDot p x - c - vecDot q x)
    = G2 at *
  have hE0 : 0 ≤ E := by rw [← hEdef]; exact Section6.cubeL2_nonneg _ _
  have hs0 : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have hW0 : (0 : ℝ) ≤ (3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4) := by positivity
  -- cE
  have hcE0 : 0 ≤ α * (3 : ℝ) ^ (d * m) + 9 * τ * Ch * β := by positivity
  have hF1 : Fq ≤ (α * (3 : ℝ) ^ (d * m) + 9 * τ * Ch * β) * E +
      9 * τ * Ch * (3 : ℝ) ^ ((d + 2) * 3) * y := by
    have a1 := mul_le_mul_of_nonneg_left hS5 hα0
    have a3 : 9 * τ * Ch * Flv ≤ 9 * τ * Ch * ((3 : ℝ) ^ ((d + 2) * 3) * y + β * E) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith only [hS6, hS7]
    linarith only [hS1, hS2, hS3, hS4, a1, a3]
  have hE2 : E ≤ Cin * (δ * (3 : ℝ) ^ (k + 1) * (y + P)) +
      Cin * (s⁻¹ * ((3 : ℝ) ^ (k + 1)) ^ 2 * F) := by
    have b1 : δ * (3 : ℝ) ^ (k + 1) * Fu ≤ δ * (3 : ℝ) ^ (k + 1) * (y + P) :=
      mul_le_mul_of_nonneg_left hS8 (by positivity)
    have b2 : Cin * (δ * (3 : ℝ) ^ (k + 1) * Fu + s⁻¹ * ((3 : ℝ) ^ (k + 1)) ^ 2 * F) ≤
        Cin * (δ * (3 : ℝ) ^ (k + 1) * (y + P) + s⁻¹ * ((3 : ℝ) ^ (k + 1)) ^ 2 * F) :=
      mul_le_mul_of_nonneg_left (by linarith only [b1]) hCin0
    linarith only [hwb, b2]
  have hF2 := mul_le_mul_of_nonneg_left hE2 hcE0
  have e1 : (α * (3 : ℝ) ^ (d * m) + 9 * τ * Ch * β) * (3 : ℝ) ^ (k + 1) =
      (3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 3) + 243 * τ * Ch := by
    calc _ = (α * (3 : ℝ) ^ (k + 1)) * (3 : ℝ) ^ (d * m) +
          9 * τ * Ch * (β * (3 : ℝ) ^ (k + 1)) := by ring
      _ = _ := by rw [I1, I3]; ring
  have e2 : (α * (3 : ℝ) ^ (d * m) + 9 * τ * Ch * β) * ((3 : ℝ) ^ (k + 1)) ^ 2 =
      ((3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 4) + 729 * τ * Ch) * (3 : ℝ) ^ k := by
    calc _ = (α * ((3 : ℝ) ^ (k + 1)) ^ 2) * (3 : ℝ) ^ (d * m) +
          9 * τ * Ch * (β * ((3 : ℝ) ^ (k + 1)) ^ 2) := by ring
      _ = _ := by rw [I2, I4]; ring
  have hmid : (α * (3 : ℝ) ^ (d * m) + 9 * τ * Ch * β) *
      (Cin * (δ * (3 : ℝ) ^ (k + 1) * (y + P)) + Cin * (s⁻¹ * ((3 : ℝ) ^ (k + 1)) ^ 2 * F)) =
      Cin * ((3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 3) + 243 * τ * Ch) * (δ * (y + P)) +
        Cin * ((3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 4) + 729 * τ * Ch) *
          (s⁻¹ * (3 : ℝ) ^ k * F) := by
    linear_combination (Cin * δ * (y + P)) * e1 + (Cin * s⁻¹ * F) * e2
  have hx1 : (3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 3) ≤
      (3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4) :=
    mul_le_mul hXm h33 (by positivity) (by positivity)
  have hx2 : (3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 4) ≤
      (3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4) :=
    mul_le_mul hXm le_rfl (by positivity) (by positivity)
  have hτCh : τ * Ch ≤ Ch := by
    have := mul_le_mul_of_nonneg_right hτ1 hCh0
    linarith only [this]
  have hCW : Ch ≤ Ch * ((3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4)) :=
    le_mul_of_one_le_right hCh0 hW1
  have hA1 : (3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 3) + 243 * τ * Ch ≤
      ((3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4)) * (1 + 729 * Ch) := by
    linarith only [hx1, hτCh, hCW, mul_nonneg hCh0 hW0]
  have hA2 : (3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 4) + 729 * τ * Ch ≤
      ((3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4)) * (1 + 729 * Ch) := by
    linarith only [hx2, hτCh, hCW, mul_nonneg hCh0 hW0]
  have hD0 : 0 ≤ δ * (y + P) := by positivity
  have hG0 : 0 ≤ s⁻¹ * (3 : ℝ) ^ k * F := by positivity
  have hB1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 hCin0) hD0
  have hB2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA2 hCin0) hG0
  rw [hmid] at hF2
  have h5 : Fq ≤ Cin * ((3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 3) + 243 * τ * Ch) * (δ * (y + P)) +
        Cin * ((3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 4) + 729 * τ * Ch) *
          (s⁻¹ * (3 : ℝ) ^ k * F) + 9 * τ * Ch * (3 : ℝ) ^ ((d + 2) * 3) * y := by
    linarith only [hF1, hF2]
  generalize (3 : ℝ) ^ (d * (m + 2)) * (3 : ℝ) ^ (m + 4) = W at hB1 hB2 ⊢
  generalize Cin * ((3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 3) + 243 * τ * Ch) * (δ * (y + P)) = Z1 at *
  generalize Cin * ((3 : ℝ) ^ (d * m) * (3 : ℝ) ^ (m + 4) + 729 * τ * Ch) *
          (s⁻¹ * (3 : ℝ) ^ k * F) = Z2 at *
  generalize (3 : ℝ) ^ ((d + 2) * 3) = Q at *
  linarith only [h5, hB1, hB2]

/-- Witness for the numerical hypotheses of `lip_int_step`: the dimension, the constants and the
parameters `k₀ = k = 3`, `s = 1`, `δ = 0` are admissible, and the theorem applies to them. -/
example : ∃ C₁ : ℝ, 1 ≤ C₁ ∧ (3 : ℕ) ≤ 3 ∧ (3 : ℕ) ≤ 3 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 0 := by
  obtain ⟨C₁, h1, -⟩ := lip_int_step 1 1 1 le_rfl le_rfl
  exact ⟨C₁, h1, le_rfl, le_rfl, one_pos, le_rfl⟩

end SuperdiffusionCLT.Section7
