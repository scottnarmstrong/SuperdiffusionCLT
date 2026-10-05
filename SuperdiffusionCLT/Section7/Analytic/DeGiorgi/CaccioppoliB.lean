/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs
public import Homogenization.Sobolev.Truncation.Basic

/-!
# Pointwise algebra for the truncation Caccioppoli inequality

The test gradient `T = 1_{u>k} η² ∇u + 2 (u-k)₊ η ∇η` of the test function `(u-k)₊ η²`, the
elementary inequalities for a nonsymmetric elliptic matrix, and the pointwise form of the
Caccioppoli estimate.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The gradient of a cutoff function. -/
noncomputable def cutoffGrad (η : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ η x (basisVec i)

/-- The gradient of the test function `(u - k)₊ η²`:
`T = 1_{u>k} η² ∇u + 2 (u-k)₊ η ∇η`. -/
noncomputable def levelTest {U : Set (Vec d)} (u : H1Function U) (k : ℝ) (η : Vec d → ℝ) :
    Vec d → Vec d :=
  fun x => {y | k < u.toFun y}.indicator (fun y => η y ^ 2 • u.grad y) x +
    (2 * max (u.toFun x - k) 0 * η x) • cutoffGrad η x

theorem eucNorm_nonneg (v : Vec d) : 0 ≤ eucNorm v := Real.sqrt_nonneg _

theorem eucNorm_sq (v : Vec d) : eucNorm v ^ 2 = vecNormSq v :=
  Real.sq_sqrt (vecNormSq_nonneg v)

theorem abs_apply_le_eucNorm (v : Vec d) (i : Fin d) : |v i| ≤ eucNorm v := by
  apply abs_le_of_sq_le_sq' _ (eucNorm_nonneg v) |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  rw [eucNorm_sq]
  exact sq_apply_le_vecNormSq v i

theorem abs_vecDot_le_eucNorm_mul (x y : Vec d) : |vecDot x y| ≤ eucNorm x * eucNorm y := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg (eucNorm_nonneg x) (eucNorm_nonneg y))
  rw [mul_pow, eucNorm_sq, eucNorm_sq]
  exact sq_vecDot_le_vecNormSq_mul_vecNormSq x y

theorem sum_abs_le_eucNorm (v : Vec d) : ∑ i, |v i| ≤ Real.sqrt d * eucNorm v := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1 : ℝ)) (fun i => |v i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, sq_abs] at h
  apply abs_le_of_sq_le_sq' _ (mul_nonneg (Real.sqrt_nonneg _) (eucNorm_nonneg v)) |>.elim
    (fun _ h2 => h2)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), eucNorm_sq]
  have : vecNormSq v = ∑ i, v i ^ 2 := by simp [vecNormSq, vecDot, pow_two]
  rw [this]
  exact h

theorem caccioppoli_abs_vecDot_matVecMul_le {A : Mat d} {Lam : ℝ} (hA : ∀ i j, |A i j| ≤ Lam)
    (W N : Vec d) :
    |vecDot (matVecMul A W) N| ≤ d * Lam * (eucNorm W * eucNorm N) := by
  by_cases hd : d = 0
  · subst hd
    simp [vecDot]
  have hLam : 0 ≤ Lam :=
    (abs_nonneg _).trans (hA ⟨0, Nat.pos_of_ne_zero hd⟩ ⟨0, Nat.pos_of_ne_zero hd⟩)
  have h1 : |vecDot (matVecMul A W) N| ≤ Lam * ((∑ i, |N i|) * ∑ j, |W j|) := by
    calc |vecDot (matVecMul A W) N|
        = |∑ i, ∑ j, A i j * W j * N i| := by
          simp only [vecDot, matVecMul, Finset.sum_mul]
      _ ≤ ∑ i, |∑ j, A i j * W j * N i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |A i j * W j * N i| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, Lam * (|N i| * |W j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have := mul_le_mul_of_nonneg_right (hA i j) (mul_nonneg (abs_nonneg (W j)) (abs_nonneg (N i)))
          linarith only [this, mul_comm |W j| |N i|]
      _ = Lam * ((∑ i, |N i|) * ∑ j, |W j|) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  have h2 := sum_abs_le_eucNorm N
  have h3 := sum_abs_le_eucNorm W
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hN0 : 0 ≤ ∑ i, |N i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hW0 : 0 ≤ ∑ i, |W i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h4 : (∑ i, |N i|) * ∑ j, |W j| ≤ (Real.sqrt d * eucNorm N) * (Real.sqrt d * eucNorm W) :=
    mul_le_mul h2 h3 hW0 (mul_nonneg (Real.sqrt_nonneg _) (eucNorm_nonneg N))
  have h5 : (Real.sqrt d * eucNorm N) * (Real.sqrt d * eucNorm W) = d * (eucNorm W * eucNorm N) := by
    calc _ = (Real.sqrt d * Real.sqrt d) * (eucNorm W * eucNorm N) := by ring
      _ = _ := by rw [hs]
  calc _ ≤ Lam * ((∑ i, |N i|) * ∑ j, |W j|) := h1
    _ ≤ Lam * (d * (eucNorm W * eucNorm N)) := by
        apply mul_le_mul_of_nonneg_left (h4.trans_eq h5) hLam
    _ = d * Lam * (eucNorm W * eucNorm N) := by ring

theorem scalar_caccioppoli {lam K G L Fb Gb x w η : ℝ} (hl : 0 < lam)
    (hw : 0 ≤ w) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hηG : η ≤ G * L) (hFb : 0 ≤ Fb) :
    lam / 2 * x ^ 2 ≤ lam * x ^ 2 - 2 * K * G * w * x - Fb * w * η ^ 2 - Gb * x -
      2 * Gb * G * w * η + ((4 * K ^ 2 * G ^ 2 / lam + 3 / 2 * lam * G ^ 2) * w ^ 2 +
        (L ^ 2 * Fb ^ 2 / (2 * lam) + 2 * Gb ^ 2 / lam)) := by
  have e1 : 0 ≤ (lam * x - 4 * K * G * w) ^ 2 / (4 * lam) := by positivity
  have e1' : (lam * x - 4 * K * G * w) ^ 2 / (4 * lam) =
      lam / 4 * x ^ 2 - 2 * K * G * w * x + 4 * K ^ 2 * G ^ 2 / lam * w ^ 2 := by
    field_simp
    ring
  have e3 : 0 ≤ (lam * x - 2 * Gb) ^ 2 / (4 * lam) := by positivity
  have e3' : (lam * x - 2 * Gb) ^ 2 / (4 * lam) = lam / 4 * x ^ 2 - Gb * x + Gb ^ 2 / lam := by
    field_simp
    ring
  have e2 : 0 ≤ (lam * (G * w * η) - Fb * L) ^ 2 / (2 * lam) := by positivity
  have e2' : (lam * (G * w * η) - Fb * L) ^ 2 / (2 * lam) =
      lam / 2 * (G * w * η) ^ 2 - (G * w * η) * (Fb * L) + (Fb * L) ^ 2 / (2 * lam) := by
    field_simp
    ring
  have e4 : 0 ≤ (lam * (G * w * η) - Gb) ^ 2 / lam := by positivity
  have e4' : (lam * (G * w * η) - Gb) ^ 2 / lam =
      lam * (G * w * η) ^ 2 - 2 * (G * w * η) * Gb + Gb ^ 2 / lam := by
    field_simp
    ring
  have hη2 : η ^ 2 ≤ 1 := pow_le_one₀ hη0 hη1
  have hGw2 : (G * w * η) ^ 2 ≤ G ^ 2 * w ^ 2 := by
    have : (G * w * η) ^ 2 = G ^ 2 * w ^ 2 * η ^ 2 := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hη2
  have hf : Fb * w * η ^ 2 ≤ Fb * w * η * (G * L) := by
    have := mul_le_mul_of_nonneg_left hηG (by positivity : 0 ≤ Fb * w * η)
    linarith only [this]
  have hfL : (Fb * L) ^ 2 = L ^ 2 * Fb ^ 2 := by ring
  have hdiv : (G * w * η) * (Fb * L) = Fb * w * η * (G * L) := by ring
  have hlG : lam / 2 * (G * w * η) ^ 2 ≤ lam / 2 * (G ^ 2 * w ^ 2) :=
    mul_le_mul_of_nonneg_left hGw2 (by positivity)
  have hlG2 : lam * (G * w * η) ^ 2 ≤ lam * (G ^ 2 * w ^ 2) :=
    mul_le_mul_of_nonneg_left hGw2 hl.le
  have hc2 : 2 * Gb ^ 2 / lam = 2 * (Gb ^ 2 / lam) := by ring
  rw [hfL] at e2'
  rw [hc2]
  linarith only [e1, e1', e2, e2', e3, e3', e4, e4', hf, hdiv, hlG, hlG2]

theorem vecDot_comm' (x y : Vec d) : vecDot x y = vecDot y x :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem pointwise_caccioppoli {lam Lam G L Fb Gb : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (hentry : ∀ i j, |A i j| ≤ Lam)
    (W N g : Vec d) (f w η s : ℝ) (hw : 0 ≤ w) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hηG : η ≤ G * L)
    (hN : eucNorm N ≤ G) (hf : |f| ≤ Fb) (hg : eucNorm g ≤ Gb) (hs0 : 0 ≤ s)
    (hs : η ≠ 0 → ¬(w = 0 ∧ W = 0) → s = 1) :
    lam / 2 * (η ^ 2 * vecNormSq W) ≤
      vecDot (matVecMul A W) (η ^ 2 • W + (2 * w * η) • N) - f * (η ^ 2 * w) -
        vecDot g (η ^ 2 • W + (2 * w * η) • N) +
      ((4 * (d * Lam) ^ 2 * G ^ 2 / lam + 3 / 2 * lam * G ^ 2) * w ^ 2 +
        (L ^ 2 * Fb ^ 2 / (2 * lam) + 2 * Gb ^ 2 / lam) * s) := by
  obtain ⟨hl, hlLam, hlow, -⟩ := hA
  have hLam : 0 ≤ Lam := hl.le.trans hlLam
  have hFb : 0 ≤ Fb := (abs_nonneg f).trans hf
  have hG : 0 ≤ G := (eucNorm_nonneg N).trans hN
  have hGb : 0 ≤ Gb := (eucNorm_nonneg g).trans hg
  by_cases hη : η = 0
  · subst hη
    have : 0 ≤ (4 * (d * Lam) ^ 2 * G ^ 2 / lam + 3 / 2 * lam * G ^ 2) * w ^ 2 +
        (L ^ 2 * Fb ^ 2 / (2 * lam) + 2 * Gb ^ 2 / lam) * s := by positivity
    simpa [vecDot] using this
  by_cases hz : w = 0 ∧ W = 0
  · obtain ⟨rfl, rfl⟩ := hz
    have : 0 ≤ (4 * (d * Lam) ^ 2 * G ^ 2 / lam + 3 / 2 * lam * G ^ 2) * 0 ^ 2 +
        (L ^ 2 * Fb ^ 2 / (2 * lam) + 2 * Gb ^ 2 / lam) * s := by positivity
    simpa [vecDot, vecNormSq, matVecMul] using this
  have hs1 := hs hη hz
  subst hs1
  set x := η * eucNorm W with hx
  have hx0 : 0 ≤ x := mul_nonneg hη0 (eucNorm_nonneg W)
  have hxsq : x ^ 2 = η ^ 2 * vecNormSq W := by rw [hx, mul_pow, eucNorm_sq]
  -- the elliptic term
  have hT : vecDot (matVecMul A W) (η ^ 2 • W + (2 * w * η) • N) =
      η ^ 2 * vecDot (matVecMul A W) W + (2 * w * η) * vecDot (matVecMul A W) N := by
    rw [vecDot_add_right, vecDot_smul_right, vecDot_smul_right]
  have hell : lam * vecNormSq W ≤ vecDot (matVecMul A W) W := by
    rw [vecDot_comm']; exact hlow W
  have hbd := caccioppoli_abs_vecDot_matVecMul_le hentry W N
  have hbd2 : eucNorm W * eucNorm N ≤ eucNorm W * G :=
    mul_le_mul_of_nonneg_left hN (eucNorm_nonneg W)
  have hK0 : 0 ≤ (d : ℝ) * Lam := mul_nonneg (Nat.cast_nonneg d) hLam
  have hbd3 : |vecDot (matVecMul A W) N| ≤ d * Lam * (eucNorm W * G) :=
    hbd.trans (mul_le_mul_of_nonneg_left hbd2 hK0)
  have hw2 : 0 ≤ 2 * w * η := by positivity
  have hcross : (2 * w * η) * vecDot (matVecMul A W) N ≥ -(2 * (d * Lam) * G * w * x) := by
    have h1 := neg_abs_le (vecDot (matVecMul A W) N)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans' (neg_le_neg hbd3)) hw2
    have h3 : (2 * w * η) * (-(d * Lam * (eucNorm W * G))) = -(2 * (d * Lam) * G * w * x) := by
      rw [hx]; ring
    linarith only [h2, h3]
  have hmain : η ^ 2 * vecDot (matVecMul A W) W ≥ lam * x ^ 2 := by
    have := mul_le_mul_of_nonneg_left hell (sq_nonneg η)
    rw [hxsq]; linarith only [this]
  have hfterm : f * (η ^ 2 * w) ≤ Fb * w * η ^ 2 := by
    have h1 : f * (η ^ 2 * w) ≤ |f| * (η ^ 2 * w) :=
      mul_le_mul_of_nonneg_right (le_abs_self f) (by positivity)
    have h2 : |f| * (η ^ 2 * w) ≤ Fb * (η ^ 2 * w) :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    linarith only [h1, h2]
  have hgT : vecDot g (η ^ 2 • W + (2 * w * η) • N) =
      η ^ 2 * vecDot g W + (2 * w * η) * vecDot g N := by
    rw [vecDot_add_right, vecDot_smul_right, vecDot_smul_right]
  have hg1 : vecDot g W ≤ Gb * eucNorm W :=
    (le_abs_self _).trans ((abs_vecDot_le_eucNorm_mul g W).trans
      (mul_le_mul_of_nonneg_right hg (eucNorm_nonneg W)))
  have hg2 : vecDot g N ≤ Gb * G :=
    (le_abs_self _).trans ((abs_vecDot_le_eucNorm_mul g N).trans
      (mul_le_mul hg hN (eucNorm_nonneg N) hGb))
  have hgterm : vecDot g (η ^ 2 • W + (2 * w * η) • N) ≤ Gb * x + 2 * Gb * G * w * η := by
    rw [hgT]
    have h1 : η ^ 2 * vecDot g W ≤ η ^ 2 * (Gb * eucNorm W) :=
      mul_le_mul_of_nonneg_left hg1 (sq_nonneg η)
    have h2 : (2 * w * η) * vecDot g N ≤ (2 * w * η) * (Gb * G) :=
      mul_le_mul_of_nonneg_left hg2 hw2
    have h3 : η ^ 2 * (Gb * eucNorm W) ≤ Gb * x := by
      have : η ^ 2 * (Gb * eucNorm W) = η * (Gb * x) := by rw [hx]; ring
      rw [this]
      have : 0 ≤ Gb * x := mul_nonneg hGb hx0
      exact mul_le_of_le_one_left this hη1
    have h4 : (2 * w * η) * (Gb * G) = 2 * Gb * G * w * η := by ring
    linarith only [h1, h2, h3, h4]
  have hsc := scalar_caccioppoli (K := d * Lam) (x := x) (G := G) (L := L) (Gb := Gb) hl hw hη0 hη1
    hηG hFb
  rw [hT]
  rw [← hxsq]
  linarith only [hsc, hcross, hmain, hfterm, hgterm]

section Integrability

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem memLp_two_mul_bdd {φ v : α → ℝ} {C : ℝ} (hφ : AEStronglyMeasurable φ μ)
    (hb : ∀ᵐ x ∂μ, |φ x| ≤ C) (hv : MemLp v 2 μ) : MemLp (fun x => φ x * v x) 2 μ :=
  hv.of_le_mul (c := C) (hφ.mul hv.aestronglyMeasurable)
    (hb.mono fun x hx => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))

theorem caccioppoli_integrable_vecDot_of_memLp {F G : α → Vec d} (hF : ∀ i, MemLp (fun x => F x i) 2 μ)
    (hG : ∀ i, MemLp (fun x => G x i) 2 μ) : Integrable (fun x => vecDot (F x) (G x)) μ := by
  unfold vecDot
  exact integrable_finsetSum _ fun i _ => (hF i).integrable_mul (hG i)

theorem memLp_matVecMul {A : α → Mat d} {F : α → Vec d} {Lam : ℝ}
    (hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (hAb : ∀ᵐ x ∂μ, ∀ i j, |A x i j| ≤ Lam) (hF : ∀ i, MemLp (fun x => F x i) 2 μ) (i : Fin d) :
    MemLp (fun x => matVecMul (A x) (F x) i) 2 μ := by
  unfold matVecMul
  exact memLp_finsetSum _ fun j _ =>
    memLp_two_mul_bdd (hAm i j) (hAb.mono fun x hx => hx i j) (hF j)

end Integrability

theorem abs_cutoff_le {z : Vec d} {L : ℝ} {η : Vec d → ℝ} (hd : 0 < d)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsupp : tsupport η ⊆ axisCube z L) {G : ℝ}
    (hG : ∀ x, eucNorm (cutoffGrad η x) ≤ G) {x : Vec d} (hx : x ∈ axisCube z L) :
    |η x| ≤ G * L := by
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  have hxi := hx i0 (Set.mem_univ _)
  simp only [Set.mem_Ioo] at hxi
  set t0 : ℝ := z i0 + L - x i0 with ht0
  set e : Vec d := basisVec i0 with he
  set y : Vec d := x + t0 • e with hy
  have hyi : y i0 = z i0 + L := by
    simp [hy, he, ht0, basisVec]
  have hyQ : y ∉ axisCube z L := by
    intro h
    have := h i0 (Set.mem_univ _)
    simp only [Set.mem_Ioo] at this
    rw [hyi] at this
    linarith only [this.2]
  have hy0 : η y = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hyQ (hsupp h)
  set h : ℝ → ℝ := fun t => η (x + t • e) with hh
  have hdiff : Differentiable ℝ η := hη.differentiable (by simp)
  have hderiv : ∀ t, HasDerivAt h (fderiv ℝ η (x + t • e) e) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    exact (hdiff (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le (f := h) (s := Set.univ) (C := G)
    (fun t _ => (hderiv t).differentiableAt)
    (fun t _ => by
      rw [(hderiv t).deriv, Real.norm_eq_abs]
      exact (abs_apply_le_eucNorm (cutoffGrad η (x + t • e)) i0).trans (hG _))
    convex_univ (Set.mem_univ 0) (Set.mem_univ t0)
  have h0 : h 0 = η x := by simp [hh]
  have h1 : h t0 = 0 := hy0
  rw [h0, h1] at hbound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at hbound
  have hL : |t0| ≤ L := by
    rw [abs_le]
    constructor <;> linarith only [hxi.1, hxi.2]
  have hG0 : 0 ≤ G := (eucNorm_nonneg _).trans (hG 0)
  calc |η x| = |0 - η x| := by simp
    _ ≤ G * |t0| := hbound
    _ ≤ G * L := mul_le_mul_of_nonneg_left hL hG0

end SuperdiffusionCLT.Section7
