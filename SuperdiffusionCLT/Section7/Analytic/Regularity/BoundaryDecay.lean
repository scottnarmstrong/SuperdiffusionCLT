/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaN
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Caccioppoli

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Boundary Caccioppoli inequality with a localized zero trace

For a weak solution `u` of `-∇·(A∇u) = f - ∇·g` on a cube with `A` close to the identity and a
localized zero trace on a window `T`, the test function `η² u` with `η` smooth, supported in `T`,
gives the unsigned Caccioppoli inequality for `∫ η² |∇u|²`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3d_eucNorm_le_of_abs_le {v : Vec d} {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, |v i| ≤ B) :
    eucNorm v ≤ Real.sqrt d * B := by
  unfold eucNorm
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  have : vecNormSq v = ∑ i, v i ^ 2 := by simp [vecNormSq, vecDot, pow_two]
  rw [this]
  calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin d, B ^ 2 := Finset.sum_le_sum fun i _ =>
        sq_le_sq' (abs_le.1 (h i)).1 (abs_le.1 (h i)).2
    _ = d * B ^ 2 := by simp

/-- Ellipticity of a matrix close to the identity. -/
theorem r3d_ell {A : Mat d} {δ : ℝ} (hδ : ∀ i j, |A i j - (1 : Mat d) i j| ≤ δ)
    (hdδ : (d : ℝ) * δ ≤ 1 / 2) (ξ : Vec d) :
    (1 / 2 : ℝ) * vecNormSq ξ ≤ vecDot (matVecMul A ξ) ξ := by
  have hδ0 : 0 ≤ δ ∨ d = 0 := by
    by_cases hd : d = 0
    · exact Or.inr hd
    · left
      have i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
      exact (abs_nonneg _).trans (hδ ⟨0, Nat.pos_of_ne_zero hd⟩ ⟨0, Nat.pos_of_ne_zero hd⟩)
  rcases hδ0 with hδ0 | hd0
  · have h1 : vecDot (matVecMul A ξ) ξ = vecNormSq ξ + ∑ i, ∑ j, (A i j - (1 : Mat d) i j) * ξ j * ξ i := by
      have e1 : ∀ i, ∑ j, (1 : Mat d) i j * ξ j = ξ i := fun i => by
        simp [Matrix.one_apply]
      have e2 : vecNormSq ξ = ∑ i, ξ i * ξ i := by simp [vecNormSq, vecDot]
      have e3 : vecDot (matVecMul A ξ) ξ = ∑ i, (∑ j, A i j * ξ j) * ξ i := by simp [vecDot, matVecMul]
      rw [e2, e3, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : ∑ j, (A i j - (1 : Mat d) i j) * ξ j * ξ i = (∑ j, A i j * ξ j) * ξ i - ξ i * ξ i := by
        rw [← Finset.sum_mul]
        simp only [sub_mul, Finset.sum_sub_distrib, e1]
      rw [this]; ring
    have h2 : |∑ i, ∑ j, (A i j - (1 : Mat d) i j) * ξ j * ξ i| ≤ δ * (∑ i, |ξ i|) ^ 2 := by
      calc |∑ i, ∑ j, (A i j - (1 : Mat d) i j) * ξ j * ξ i|
          ≤ ∑ i, |∑ j, (A i j - (1 : Mat d) i j) * ξ j * ξ i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, |(A i j - (1 : Mat d) i j) * ξ j * ξ i| :=
            Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, δ * (|ξ j| * |ξ i|) := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_right (hδ i j) (by positivity)
        _ = δ * (∑ i, |ξ i|) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : (∑ i, |ξ i|) ^ 2 ≤ d * vecNormSq ξ := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1 : ℝ)) (fun i => |ξ i|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, sq_abs] at this
      have e : vecNormSq ξ = ∑ i, ξ i ^ 2 := by simp [vecNormSq, vecDot, pow_two]
      rw [e]; exact this
    have h4 : δ * (∑ i, |ξ i|) ^ 2 ≤ δ * (d * vecNormSq ξ) := mul_le_mul_of_nonneg_left h3 hδ0
    have h5 : δ * (d * vecNormSq ξ) ≤ 1 / 2 * vecNormSq ξ := by
      have := mul_le_mul_of_nonneg_right hdδ (vecNormSq_nonneg ξ)
      linarith only [this]
    have := (abs_le.1 h2).1
    linarith only [h1, this, h4, h5]
  · subst hd0
    simp [vecNormSq, vecDot]

theorem r3d_scalar {lam K G L Fb Gb x w η : ℝ} (hl : 0 < lam) (hL : 0 < L)
    (hw : 0 ≤ w) (hη1 : η ≤ 1) (hGb : 0 ≤ Gb) (hG : 0 ≤ G) :
    2 * K * G * w * x + Fb * w + Gb * x + 2 * Gb * G * w * η ≤ lam / 2 * x ^ 2 +
      ((4 * K ^ 2 * G ^ 2 / lam + 1 / (2 * L ^ 2) + G ^ 2) * w ^ 2 +
        (L ^ 2 * Fb ^ 2 / 2 + (1 / lam + 1) * Gb ^ 2)) := by
  have e1 : 0 ≤ (lam * x - 4 * K * G * w) ^ 2 / (4 * lam) := by positivity
  have e1' : (lam * x - 4 * K * G * w) ^ 2 / (4 * lam) =
      lam / 4 * x ^ 2 - 2 * K * G * w * x + 4 * K ^ 2 * G ^ 2 / lam * w ^ 2 := by
    field_simp
    ring
  have e3 : 0 ≤ (lam * x - 2 * Gb) ^ 2 / (4 * lam) := by positivity
  have e3' : (lam * x - 2 * Gb) ^ 2 / (4 * lam) = lam / 4 * x ^ 2 - Gb * x + Gb ^ 2 / lam := by
    field_simp
    ring
  have e2 : 0 ≤ (L * Fb - w / L) ^ 2 / 2 := by positivity
  have e2' : (L * Fb - w / L) ^ 2 / 2 = L ^ 2 * Fb ^ 2 / 2 - Fb * w + w ^ 2 / (2 * L ^ 2) := by
    field_simp
    ring
  have e4 : 0 ≤ (Gb - G * w) ^ 2 := sq_nonneg _
  have hηw : 2 * Gb * G * w * η ≤ 2 * Gb * G * w := by
    have : 0 ≤ 2 * Gb * G * w := by positivity
    exact mul_le_of_le_one_right this hη1
  have e5 : 2 * Gb * G * w ≤ Gb ^ 2 + G ^ 2 * w ^ 2 := by
    have e4' : (Gb - G * w) ^ 2 = Gb ^ 2 - 2 * Gb * G * w + G ^ 2 * w ^ 2 := by ring
    linarith only [e4, e4']
  have hc1 : 1 / (2 * L ^ 2) * w ^ 2 = w ^ 2 / (2 * L ^ 2) := by ring
  have hc2 : (1 / lam + 1) * Gb ^ 2 = Gb ^ 2 / lam + Gb ^ 2 := by ring
  linarith only [e1, e1', e2, e2', e3, e3', hηw, e5, hc1, hc2]

theorem r3d_pointwise {A : Mat d} {lam Lam G L : ℝ} (hl : 0 < lam)
    (hell : ∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot (matVecMul A ξ) ξ)
    (hentry : ∀ i j, |A i j| ≤ Lam) (W N g : Vec d) (f u η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hN : eucNorm N ≤ G) (hL : 0 < L) :
    lam / 2 * (η ^ 2 * vecNormSq W) ≤
      vecDot (matVecMul A W) (η ^ 2 • W + (2 * u * η) • N) - f * (η ^ 2 * u) -
        vecDot g (η ^ 2 • W + (2 * u * η) • N) +
      ((4 * (d * Lam) ^ 2 * G ^ 2 / lam + 1 / (2 * L ^ 2) + G ^ 2) * u ^ 2 +
        (L ^ 2 / 2 * f ^ 2 + (1 / lam + 1) * vecNormSq g)) := by
  have hK0 : 0 ≤ (d : ℝ) * Lam := by
    by_cases hd : d = 0
    · subst hd; simp
    · exact mul_nonneg (Nat.cast_nonneg d)
        ((abs_nonneg _).trans (hentry ⟨0, Nat.pos_of_ne_zero hd⟩ ⟨0, Nat.pos_of_ne_zero hd⟩))
  have hG0 : 0 ≤ G := (eucNorm_nonneg N).trans hN
  set x := η * eucNorm W with hx
  have hx0 : 0 ≤ x := mul_nonneg hη0 (eucNorm_nonneg W)
  have hxsq : x ^ 2 = η ^ 2 * vecNormSq W := by rw [hx, mul_pow, eucNorm_sq]
  have hT : vecDot (matVecMul A W) (η ^ 2 • W + (2 * u * η) • N) =
      η ^ 2 * vecDot (matVecMul A W) W + (2 * u * η) * vecDot (matVecMul A W) N := by
    rw [vecDot_add_right, vecDot_smul_right, vecDot_smul_right]
  have hmain : η ^ 2 * vecDot (matVecMul A W) W ≥ lam * x ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hell W) (sq_nonneg η)
    rw [hxsq]; linarith only [this]
  have hbd := caccioppoli_abs_vecDot_matVecMul_le hentry W N
  have hbd2 : eucNorm W * eucNorm N ≤ eucNorm W * G :=
    mul_le_mul_of_nonneg_left hN (eucNorm_nonneg W)
  have hbd3 : |vecDot (matVecMul A W) N| ≤ d * Lam * (eucNorm W * G) :=
    hbd.trans (mul_le_mul_of_nonneg_left hbd2 hK0)
  have hcross : (2 * u * η) * vecDot (matVecMul A W) N ≥ -(2 * (d * Lam) * G * |u| * x) := by
    have h1 : |(2 * u * η) * vecDot (matVecMul A W) N| ≤ 2 * (d * Lam) * G * |u| * x := by
      rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hη0]
      calc 2 * |u| * η * |vecDot (matVecMul A W) N| ≤ 2 * |u| * η * (d * Lam * (eucNorm W * G)) :=
            mul_le_mul_of_nonneg_left hbd3 (by positivity)
        _ = 2 * (d * Lam) * G * |u| * x := by rw [hx]; ring
    have := neg_abs_le ((2 * u * η) * vecDot (matVecMul A W) N)
    linarith only [h1, this]
  have hfterm : f * (η ^ 2 * u) ≤ |f| * |u| := by
    have h1 : f * (η ^ 2 * u) ≤ |f * (η ^ 2 * u)| := le_abs_self _
    have h2 : |f * (η ^ 2 * u)| = |f| * (η ^ 2 * |u|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg η)]
    have h3 : η ^ 2 ≤ 1 := pow_le_one₀ hη0 hη1
    have h4 : |f| * (η ^ 2 * |u|) ≤ |f| * |u| := by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact mul_le_of_le_one_left (abs_nonneg _) h3
    linarith only [h1, h2, h4]
  have hgT : vecDot g (η ^ 2 • W + (2 * u * η) • N) =
      η ^ 2 * vecDot g W + (2 * u * η) * vecDot g N := by
    rw [vecDot_add_right, vecDot_smul_right, vecDot_smul_right]
  have hg1 : vecDot g W ≤ eucNorm g * eucNorm W :=
    (le_abs_self _).trans (abs_vecDot_le_eucNorm_mul g W)
  have hg2 : |vecDot g N| ≤ eucNorm g * G :=
    (abs_vecDot_le_eucNorm_mul g N).trans (mul_le_mul_of_nonneg_left hN (eucNorm_nonneg g))
  have hgterm : vecDot g (η ^ 2 • W + (2 * u * η) • N) ≤
      eucNorm g * x + 2 * eucNorm g * G * |u| * η := by
    rw [hgT]
    have h1 : η ^ 2 * vecDot g W ≤ η ^ 2 * (eucNorm g * eucNorm W) :=
      mul_le_mul_of_nonneg_left hg1 (sq_nonneg η)
    have h3 : η ^ 2 * (eucNorm g * eucNorm W) ≤ eucNorm g * x := by
      have : η ^ 2 * (eucNorm g * eucNorm W) = η * (eucNorm g * x) := by rw [hx]; ring
      rw [this]
      have : 0 ≤ eucNorm g * x := mul_nonneg (eucNorm_nonneg g) hx0
      exact mul_le_of_le_one_left this hη1
    have h2 : (2 * u * η) * vecDot g N ≤ 2 * eucNorm g * G * |u| * η := by
      have h5 : |(2 * u * η) * vecDot g N| ≤ 2 * |u| * η * (eucNorm g * G) := by
        rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg hη0]
        exact mul_le_mul_of_nonneg_left hg2 (by positivity)
      have h6 := (le_abs_self ((2 * u * η) * vecDot g N)).trans h5
      linarith only [h6]
    linarith only [h1, h3, h2]
  have hsc := r3d_scalar (lam := lam) (K := d * Lam) (G := G) (L := L) (Fb := |f|) (Gb := eucNorm g)
    (x := x) (w := |u|) (η := η) hl hL (abs_nonneg u) hη1 (eucNorm_nonneg g) hG0
  have hu2 : |u| ^ 2 = u ^ 2 := sq_abs u
  have hf2 : |f| ^ 2 = f ^ 2 := sq_abs f
  have hg2' : eucNorm g ^ 2 = vecNormSq g := eucNorm_sq g
  rw [hu2, hf2, hg2'] at hsc
  rw [hT, ← hxsq]
  linarith only [hsc, hcross, hmain, hfterm, hgterm]

theorem r3d_p12_grad_sq {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (x : Vec d) :
    p12_grad (fun y => η y ^ 2) x = (2 * η x) • p12_grad η x := by
  have h1 : HasFDerivAt η (fderiv ℝ η x) x :=
    ((hη.differentiable (by simp)) x).hasFDerivAt
  have h2 := h1.mul h1
  have h3 : (fun y => η y ^ 2) = fun y => η y * η y := funext fun y => sq (η y)
  have h4 : fderiv ℝ (fun y => η y ^ 2) x = η x • fderiv ℝ η x + η x • fderiv ℝ η x := by
    rw [h3]; exact h2.fderiv
  funext i
  simp only [p12_grad, h4, Pi.smul_apply, smul_eq_mul, add_apply,
    smul_apply]
  ring

theorem r3d_caccioppoli (Q : TriadicCube d) {A : CoeffField d} {δ G Gb L : ℝ}
    (hAc : ∀ i j, Continuous (fun x => A x i j)) (hδ1 : δ ≤ 1) (hdδ : (d : ℝ) * δ ≤ 1 / 2)
    (hAδ : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ)
    (u : H1Function (openCubeSet Q)) {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q)))
    (hgm : AEStronglyMeasurable g (volume.restrict (openCubeSet Q)))
    (hgb : ∀ x ∈ openCubeSet Q, eucNorm (g x) ≤ Gb)
    (hu : IsWeakSolutionOn A (openCubeSet Q) u f g) {T : Set (Vec d)}
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet Q) T u.toFun)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) (hηT : tsupport η ⊆ T)
    (hG : ∀ x, eucNorm (p12_grad η x) ≤ G) (hL : 0 < L) :
    ∫ x in openCubeSet Q, η x ^ 2 * vecNormSq (u.grad x) ≤
      4 * ((4 * ((d : ℝ) * 2) ^ 2 * G ^ 2 / (1 / 2) + 1 / (2 * L ^ 2) + G ^ 2) *
          (∫ x in openCubeSet Q, u.toFun x ^ 2) +
        (L ^ 2 / 2 * (∫ x in openCubeSet Q, f x ^ 2) +
          (1 / (1 / 2) + 1) * (∫ x in openCubeSet Q, vecNormSq (g x)))) := by
  classical
  have hQo : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  have hQm : MeasurableSet (openCubeSet Q) := hQo.measurableSet
  have hconv := r3c_isOpenBoundedConvex_cube Q
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet Q)) := hconv.isFiniteMeasure_restrict_volume
  set μ : Measure (Vec d) := volume.restrict (openCubeSet Q) with hμ
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x ^ 2) := hη.pow 2
  have hχc : HasCompactSupport (fun x => η x ^ 2) :=
    hηc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hχT : tsupport (fun x => η x ^ 2) ⊆ T :=
    (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) η).trans hηT
  obtain ⟨W, hW⟩ := hZ (fun x => η x ^ 2) hχ hχc hχT
  have hWf : ∀ x, W.toH1Function.toFun x = η x ^ 2 * u.toFun x := fun x => congrFun hW x
  have hWg := p12_grad_ae Q hχ hχc u W hWf
  set N : Vec d → Vec d := p12_grad η with hNdef
  set Tv : Vec d → Vec d := fun x => η x ^ 2 • u.grad x + (2 * u.toFun x * η x) • N x with hTv
  have hWT : ∀ᵐ x ∂μ, W.toH1Function.grad x = Tv x := by
    filter_upwards [hWg] with x hx
    rw [hx, r3d_p12_grad_sq hη, hTv]
    simp only [smul_smul]
    congr 2
    ring
  have hAb : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j| ≤ 2 := fun x hx i j =>
    r3c_abs_entry_le_two x (hAδ x hx) hδ1 i j
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ := fun i j =>
    (hAc i j).aestronglyMeasurable
  have hAb' : ∀ᵐ x ∂μ, ∀ i j, |A x i j| ≤ 2 := by
    filter_upwards [ae_restrict_mem hQm] with x hx i j using hAb x hx i j
  have hui : ∀ i, MemLp (fun x => u.grad x i) 2 μ := fun i => u.grad_memL2 i
  have huL : MemLp u.toFun 2 μ := u.memL2
  have hNc := p12_continuous_grad hη
  have hNb : ∀ i x, |N x i| ≤ G := fun i x => (abs_apply_le_eucNorm _ i).trans (hG x)
  have hηc' : Continuous η := hη.continuous
  have hηb : ∀ x, |η x| ≤ 1 := fun x => by rw [abs_of_nonneg (hη0 x)]; exact hη1 x
  have hη2b : ∀ x, |η x ^ 2| ≤ 1 := fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ (hη0 x) (hη1 x)
  have hTi : ∀ i, MemLp (fun x => Tv x i) 2 μ := by
    intro i
    have h1 := memLp_two_mul_bdd (μ := μ) (φ := fun x => η x ^ 2) (C := 1)
      (hηc'.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall hη2b) (hui i)
    have h2 := memLp_two_mul_bdd (μ := μ) (φ := fun x => N x i) (C := G)
      ((continuous_apply i).comp hNc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hNb i x) huL
    have h3 := memLp_two_mul_bdd (μ := μ) (φ := fun x => 2 * η x) (C := 2)
      ((continuous_const.mul hηc').aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        rw [abs_mul, abs_of_nonneg (hη0 x)]
        have := hη1 x
        simp only [abs_two]; linarith only [this]) h2
    refine (h1.add h3).ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp only [hTv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgi : ∀ i, MemLp (fun x => g x i) 2 μ := fun i =>
    MemLp.of_bound ((continuous_apply i).comp_aestronglyMeasurable hgm) Gb
      (by
        filter_upwards [ae_restrict_mem hQm] with x hx
        rw [Real.norm_eq_abs]; exact (abs_apply_le_eucNorm (g x) i).trans (hgb x hx))
  have hf0 : ∀ x, W.toH1Function.toFun x = η x ^ 2 * u.toFun x := hWf
  have I1 : Integrable (fun x => vecDot (matVecMul (A x) (u.grad x)) (Tv x)) μ :=
    r3c_integrable_vecDot (fun i => r3c_memLp_matVec hQm hAm hAb hui i) hTi
  have hηuL : MemLp (fun x => η x ^ 2 * u.toFun x) 2 μ :=
    memLp_two_mul_bdd (μ := μ) (φ := fun x => η x ^ 2) (C := 1)
      (hηc'.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall hη2b) huL
  have I2 : Integrable (fun x => f x * (η x ^ 2 * u.toFun x)) μ := hf.integrable_mul hηuL
  have I3 : Integrable (fun x => vecDot (g x) (Tv x)) μ := r3c_integrable_vecDot hgi hTi
  have I4 : Integrable (fun x => η x ^ 2 * vecNormSq (u.grad x)) μ := by
    have hc : ∀ i, MemLp (fun x => η x * u.grad x i) 2 μ := fun i =>
      memLp_two_mul_bdd (μ := μ) (φ := η) (C := 1) hηc'.aestronglyMeasurable
        (Filter.Eventually.of_forall hηb) (hui i)
    have : (fun x => η x ^ 2 * vecNormSq (u.grad x)) = fun x => ∑ i, (η x * u.grad x i) ^ 2 := by
      funext x
      simp only [vecNormSq, vecDot, mul_pow, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hc i).integrable_sq
  have I5 : Integrable (fun x => u.toFun x ^ 2) μ := huL.integrable_sq
  have I6 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have I7 : Integrable (fun x => vecNormSq (g x)) μ := by
    have : (fun x => vecNormSq (g x)) = fun x => ∑ i, (g x i) ^ 2 := by
      funext x; simp [vecNormSq, vecDot, pow_two]
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hgi i).integrable_sq
  set c1 : ℝ := 4 * ((d : ℝ) * 2) ^ 2 * G ^ 2 / (1 / 2) + 1 / (2 * L ^ 2) + G ^ 2 with hc1
  set c2 : ℝ := L ^ 2 / 2 with hc2
  set c3 : ℝ := 1 / (1 / 2) + 1 with hc3
  have hpt : ∀ᵐ x ∂μ, (1 / 2) / 2 * (η x ^ 2 * vecNormSq (u.grad x)) ≤
      (vecDot (matVecMul (A x) (u.grad x)) (Tv x) - f x * (η x ^ 2 * u.toFun x) -
        vecDot (g x) (Tv x)) +
      (c1 * u.toFun x ^ 2 + (c2 * f x ^ 2 + c3 * vecNormSq (g x))) := by
    filter_upwards [ae_restrict_mem hQm] with x hx
    exact r3d_pointwise (A := A x) (lam := 1 / 2) (Lam := 2) (G := G) (L := L) (by norm_num)
      (fun ξ => r3d_ell (hAδ x hx) hdδ ξ) (fun i j => hAb x hx i j) (u.grad x) (N x) (g x) (f x)
      (u.toFun x) (η x) (hη0 x) (hη1 x) (hG x) hL
  have heq := hu W
  have e1 : ∫ x in openCubeSet Q, vecDot (matVecMul (A x) (u.grad x)) (W.toH1Function.grad x) =
      ∫ x, vecDot (matVecMul (A x) (u.grad x)) (Tv x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hWT] with x hx
    rw [hx]
  have e2 : ∫ x in openCubeSet Q, f x * W.toH1Function.toFun x =
      ∫ x, f x * (η x ^ 2 * u.toFun x) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f x * W.toH1Function.toFun x = _
    rw [hWf x]
  have e3 : ∫ x in openCubeSet Q, vecDot (g x) (W.toH1Function.grad x) =
      ∫ x, vecDot (g x) (Tv x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hWT] with x hx
    rw [hx]
  rw [e1, e2, e3] at heq
  have I12 : Integrable (fun x => vecDot (matVecMul (A x) (u.grad x)) (Tv x) -
      f x * (η x ^ 2 * u.toFun x)) μ := I1.sub I2
  have I123 : Integrable (fun x => vecDot (matVecMul (A x) (u.grad x)) (Tv x) -
      f x * (η x ^ 2 * u.toFun x) - vecDot (g x) (Tv x)) μ := I12.sub I3
  have I567 : Integrable (fun x => c1 * u.toFun x ^ 2 + (c2 * f x ^ 2 + c3 * vecNormSq (g x))) μ :=
    (I5.const_mul c1).add ((I6.const_mul c2).add (I7.const_mul c3))
  have Isum : Integrable (fun x => (vecDot (matVecMul (A x) (u.grad x)) (Tv x) -
      f x * (η x ^ 2 * u.toFun x) - vecDot (g x) (Tv x)) +
      (c1 * u.toFun x ^ 2 + (c2 * f x ^ 2 + c3 * vecNormSq (g x)))) μ := I123.add I567
  have hH : ∫ x, (vecDot (matVecMul (A x) (u.grad x)) (Tv x) - f x * (η x ^ 2 * u.toFun x) -
      vecDot (g x) (Tv x)) ∂μ = 0 := by
    rw [integral_sub I12 I3, integral_sub I1 I2]
    linarith only [heq]
  have hJ := integral_mono_ae (I4.const_mul ((1 / 2) / 2)) Isum hpt
  have J5 : Integrable (fun x => c1 * u.toFun x ^ 2) μ := I5.const_mul c1
  have J6 : Integrable (fun x => c2 * f x ^ 2) μ := I6.const_mul c2
  have J7 : Integrable (fun x => c3 * vecNormSq (g x)) μ := I7.const_mul c3
  have J67 : Integrable (fun x => c2 * f x ^ 2 + c3 * vecNormSq (g x)) μ := J6.add J7
  have hR : ∫ x, (c1 * u.toFun x ^ 2 + (c2 * f x ^ 2 + c3 * vecNormSq (g x))) ∂μ =
      c1 * ∫ x, u.toFun x ^ 2 ∂μ + (c2 * ∫ x, f x ^ 2 ∂μ + c3 * ∫ x, vecNormSq (g x) ∂μ) := by
    rw [integral_add J5 J67, integral_add J6 J7, integral_const_mul, integral_const_mul,
      integral_const_mul]
  rw [integral_const_mul, integral_add I123 I567, hH, hR] at hJ
  have hfin2 : (1 / 2 : ℝ) / 2 * ∫ x, η x ^ 2 * vecNormSq (u.grad x) ∂μ ≤
      c1 * ∫ x, u.toFun x ^ 2 ∂μ + (c2 * ∫ x, f x ^ 2 ∂μ + c3 * ∫ x, vecNormSq (g x) ∂μ) := by
    linarith only [hJ]
  have h4 := mul_le_mul_of_nonneg_left hfin2 (by norm_num : (0 : ℝ) ≤ 4)
  refine le_trans (le_of_eq ?_) h4
  ring

end SuperdiffusionCLT.Section7
