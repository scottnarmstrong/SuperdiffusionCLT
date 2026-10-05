/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayF

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# The `L²` energy estimate for the face problem

Unsigned Caccioppoli near the face (`r3d_cacc_step`) combined with the face control of the
tangential affine part (`r3d_F1`): the gradient energy of `u = φ - c n` near the face and
`‖u‖²_{L²}` are bounded by `‖φ - ℓ₀‖²_{L²}`, the data and the slope term `δ |c|`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3d_integrable_cut_grad (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) {η : Vec d → ℝ}
    (hη : Continuous η) (hηb : ∀ x, |η x| ≤ 1) :
    Integrable (fun x => η x ^ 2 * vecNormSq (u.grad x)) (volume.restrict (openCubeSet Q)) := by
  have hc : ∀ i, MemLp (fun x => η x * u.grad x i) 2 (volume.restrict (openCubeSet Q)) := fun i =>
    memLp_two_mul_bdd (φ := η) (C := 1) hη.aestronglyMeasurable
      (Filter.Eventually.of_forall hηb) (u.grad_memL2 i)
  have : (fun x => η x ^ 2 * vecNormSq (u.grad x)) = fun x => ∑ i, (η x * u.grad x i) ^ 2 := by
    funext x
    simp only [vecNormSq, vecDot, mul_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact integrable_finsetSum _ fun i _ => (hc i).integrable_sq

theorem r3d_vecNormSq_continuous {g : Vec d → Vec d} (hg : ∀ i, Continuous fun x => g x i) :
    Continuous fun x => vecNormSq (g x) := by
  have : (fun x => vecNormSq (g x)) = fun x => ∑ i, g x i * g x i := by
    funext x; simp [vecNormSq, vecDot]
  rw [this]
  exact continuous_finsetSum _ fun i _ => (hg i).mul (hg i)

theorem r3d_cacc_step (e : Fin d) (m : ℤ) {A : CoeffField d} {δ G₁ c : ℝ} (hG1 : 0 ≤ G₁)
    (hcut : ∀ lam : ℝ, 0 < lam → ∀ x i, |p12_grad (r3c_cutS (r3c_z0 e m) lam) x i| ≤ G₁ / lam)
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdδ : (d : ℝ) * δ ≤ 1 / 2)
    (hAδ : ∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))))
    {φ u : H1Function (openCubeSet (originCube d m))}
    (hφ : IsWeakSolutionOn A (openCubeSet (originCube d m)) φ f (fun _ => 0))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) φ.toFun)
    (hu1 : ∀ x, u.toFun x = φ.toFun x - c * r3c_nrm e m x)
    (hu2 : ∀ x, u.grad x = φ.grad x - c • basisVec e) :
    ((3 : ℝ) ^ m) ^ 2 * (∫ x in r3d_Ebox e m ((3 : ℝ) ^ m / 3), vecNormSq (u.grad x)) ≤
      4 * ((32 * (d : ℝ) ^ 2 + 1) * d * (9 * G₁ ^ 2 / 16) + 1 / 2) *
          (∫ x in openCubeSet (originCube d m), u.toFun x ^ 2) +
        2 * ((3 : ℝ) ^ m) ^ 4 * (∫ x in openCubeSet (originCube d m), f x ^ 2) +
        12 * d * ((3 : ℝ) ^ m) ^ (d + 2) * (|c| * δ) ^ 2 := by
  classical
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓd
  have hℓ : 0 < ℓ := zpow_pos (by norm_num) m
  have hlam : 0 < 4 * ℓ / 3 := by positivity
  set lam : ℝ := 4 * ℓ / 3 with hlamd
  set η : Vec d → ℝ := r3c_cutS (r3c_z0 e m) lam with hηd
  have hAb : ∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j| ≤ 2 := fun x hx i j =>
    r3c_abs_entry_le_two x (hAδ x hx) hδ1 i j
  have hu' : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (r3c_slopeField A e c) :=
    r3c_slope_equation (originCube d m) e hAs hAb c hφ hu2
  have hZu : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) u.toFun :=
    r3c_localized_sub e m c hZ hu1
  have hgc : ∀ i, Continuous fun x => r3c_slopeField A e c x i := fun i =>
    (r3c_slopeField_contDiff hAs e c i).continuous
  have hgm : AEStronglyMeasurable (r3c_slopeField A e c) (volume.restrict (openCubeSet (originCube d m))) :=
    (continuous_pi hgc).aestronglyMeasurable
  have hsq0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hgb : ∀ x ∈ openCubeSet (originCube d m),
      eucNorm (r3c_slopeField A e c x) ≤ Real.sqrt d * (|c| * δ) := fun x hx =>
    r3d_eucNorm_le_of_abs_le (by positivity) fun i => r3c_slopeField_abs_le e c x (hAδ x hx) i
  have hηT : tsupport η ⊆ r3d_window e m := by
    intro x hx i
    have := r3c_cutS_tsupport (r3c_z0 e m) hlam hx i
    calc |x i - r3c_z0 e m i| ≤ 5 * lam / 16 := this
      _ < ℓ / 2 := by rw [hlamd]; linarith only [hℓ]
  have hG : ∀ x, eucNorm (p12_grad η x) ≤ Real.sqrt d * (G₁ / lam) := fun x =>
    r3d_eucNorm_le_of_abs_le (by positivity) fun i => hcut lam hlam x i
  have hcacc := r3d_caccioppoli (originCube d m) (A := A) (δ := δ) (G := Real.sqrt d * (G₁ / lam))
    (Gb := Real.sqrt d * (|c| * δ)) (L := ℓ) (fun i j => (hAs i j).continuous) hδ1 hdδ hAδ u hf
    hgm hgb hu' hZu (r3c_cutS_contDiff _ _) (r3c_cutS_hasCompactSupport _ hlam)
    (fun x => (r3c_cutS_01 _ _ x).1) (fun x => (r3c_cutS_01 _ _ x).2) hηT hG hℓ
  set U : ℝ := ∫ x in openCubeSet (originCube d m), u.toFun x ^ 2 with hU
  set F2 : ℝ := ∫ x in openCubeSet (originCube d m), f x ^ 2 with hF2
  set Sg : ℝ := ∫ x in openCubeSet (originCube d m), vecNormSq (r3c_slopeField A e c x) with hSg
  set Y : ℝ := ∫ x in openCubeSet (originCube d m), η x ^ 2 * vecNormSq (u.grad x) with hY
  set Y' : ℝ := ∫ x in r3d_Ebox e m (ℓ / 3), vecNormSq (u.grad x) with hY'
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (r3d_volume_openCube_ne_top m)⟩
  have hηb : ∀ x, |η x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (r3c_cutS_01 _ _ x).1]; exact (r3c_cutS_01 _ _ x).2
  have hYint := r3d_integrable_cut_grad (originCube d m) u (η := η) (r3c_cutS_contDiff _ _).continuous hηb
  have hY'Y : Y' ≤ Y := by
    have h1 : Y' = ∫ x in r3d_Ebox e m (ℓ / 3), η x ^ 2 * vecNormSq (u.grad x) := by
      refine setIntegral_congr_fun (r3d_Ebox_measurable e m _) fun x hx => ?_
      have : η x = 1 := r3c_cutS_eq_one (r3c_z0 e m) hlam fun i => by
        have := hx.1 i
        rw [hlamd]; linarith only [this, hℓ]
      simp [this]
    rw [h1]
    have hYint' : IntegrableOn (fun x => η x ^ 2 * vecNormSq (u.grad x)) (openCubeSet (originCube d m)) volume := hYint
    refine setIntegral_mono_set hYint' ?_ ?_
    · exact Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    · exact Filter.Eventually.of_forall fun x hx => hx.2
  have hSgb : Sg ≤ (Real.sqrt d * (|c| * δ)) ^ 2 * ℓ ^ d := by
    have hcont := r3d_vecNormSq_continuous hgc
    have h1 : Sg ≤ ∫ x in openCubeSet (originCube d m), (Real.sqrt d * (|c| * δ)) ^ 2 := by
      refine integral_mono_ae ?_ (integrable_const _) ?_
      · refine (integrable_const ((Real.sqrt d * (|c| * δ)) ^ 2)).mono' hcont.aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem (isOpen_openCubeSet (originCube d m)).measurableSet] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _), ← eucNorm_sq]
        exact pow_le_pow_left₀ (eucNorm_nonneg _) (hgb x hx) 2
      · filter_upwards [ae_restrict_mem (isOpen_openCubeSet (originCube d m)).measurableSet] with x hx
        rw [← eucNorm_sq]
        exact pow_le_pow_left₀ (eucNorm_nonneg _) (hgb x hx) 2
    have h2 : ∫ x in openCubeSet (originCube d m), (Real.sqrt d * (|c| * δ)) ^ 2 =
        (Real.sqrt d * (|c| * δ)) ^ 2 * ℓ ^ d := by
      rw [integral_const, smul_eq_mul]
      simp only [Measure.real, Measure.restrict_apply_univ]
      rw [r3d_volume_openCube m, mul_comm]
    linarith only [h1, h2]
  have hGsq : (Real.sqrt d * (G₁ / lam)) ^ 2 = d * (9 * G₁ ^ 2 / (16 * ℓ ^ 2)) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), hlamd]
    field_simp
    ring
  have hsd : (Real.sqrt d * (|c| * δ)) ^ 2 = d * (|c| * δ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [hGsq] at hcacc
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left (hY'Y.trans hcacc) hℓ2.le
  have hU0 : 0 ≤ U := integral_nonneg fun x => sq_nonneg _
  have hSg0 : 0 ≤ Sg := integral_nonneg fun x => vecNormSq_nonneg _
  have e1 : ℓ ^ 2 * (4 * ((4 * ((d : ℝ) * 2) ^ 2 * (d * (9 * G₁ ^ 2 / (16 * ℓ ^ 2))) / (1 / 2) +
        1 / (2 * ℓ ^ 2) + d * (9 * G₁ ^ 2 / (16 * ℓ ^ 2))) * U + (ℓ ^ 2 / 2 * F2 + (1 / (1 / 2) + 1) * Sg))) =
      4 * ((32 * (d : ℝ) ^ 2 + 1) * d * (9 * G₁ ^ 2 / 16) + 1 / 2) * U + 2 * ℓ ^ 4 * F2 + 12 * ℓ ^ 2 * Sg := by
    field_simp
    ring
  rw [e1] at hmul
  have hSg2 : 12 * ℓ ^ 2 * Sg ≤ 12 * d * ℓ ^ (d + 2) * (|c| * δ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hSgb (by positivity : (0 : ℝ) ≤ 12 * ℓ ^ 2)
    rw [hsd] at this
    have e2 : 12 * ℓ ^ 2 * (↑d * (|c| * δ) ^ 2 * ℓ ^ d) = 12 * d * ℓ ^ (d + 2) * (|c| * δ) ^ 2 := by
      rw [pow_add]; ring
    linarith only [this, e2]
  linarith only [hmul, hSg2]

theorem r3d_energy_L2 (hd : 2 ≤ d) (e : Fin d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (m : ℤ) (A : CoeffField d) (δ c a : ℝ) (b : Vec d),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) → 0 ≤ δ → δ ≤ ε →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ) →
        ∀ f : Vec d → ℝ, MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) →
        ∀ φ u : H1Function (openCubeSet (originCube d m)),
          IsWeakSolutionOn A (openCubeSet (originCube d m)) φ f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) φ.toFun →
          (∀ x, u.toFun x = φ.toFun x - c * r3c_nrm e m x) →
          (∀ x, u.grad x = φ.grad x - c • basisVec e) →
          ((3 : ℝ) ^ m) ^ 2 * (∫ x in r3d_Ebox e m ((3 : ℝ) ^ m / 3), vecNormSq (u.grad x)) +
              (∫ x in openCubeSet (originCube d m), u.toFun x ^ 2) ≤
            C * ((∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2) +
              ((3 : ℝ) ^ m) ^ 4 * (∫ x in openCubeSet (originCube d m), f x ^ 2) +
              ((3 : ℝ) ^ m) ^ (d + 2) * (|c| * δ) ^ 2) := by
  classical
  obtain ⟨K, hK0, hK⟩ := r3d_exists_deriv_bound
  obtain ⟨G₁, G₂, hG1, hG2, Hcut⟩ := r3c_cutS_bounds d
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hd0 : (0 : ℝ) < d := by linarith only [hd1]
  set C₁ : ℝ := 144 * 2 ^ (d - 1) * 7 ^ (d + 1) with hC₁
  have hC₁0 : 0 < C₁ :=
    mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
  set κ : ℝ := (32 * (d : ℝ) ^ 2 + 1) * d * (9 * G₁ ^ 2 / 16) + 1 / 2 with hκ
  have hκ12 : 1 / 2 ≤ κ := by
    have : 0 ≤ (32 * (d : ℝ) ^ 2 + 1) * d * (9 * G₁ ^ 2 / 16) :=
      mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) zero_le_one) hd0.le)
        (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
    linarith only [this, hκ]
  have hκ0 : 0 < κ := by linarith only [hκ12]
  have hden : 0 < 192 * κ * (d : ℝ) ^ 2 * C₁ :=
    mul_pos (mul_pos (mul_pos (by norm_num) hκ0) (pow_pos hd0 2)) hC₁0
  set θ : ℝ := min (1 / 3) (1 / (192 * κ * (d : ℝ) ^ 2 * C₁)) with hθ
  have hθ0 : 0 < θ := lt_min (by norm_num) (one_div_pos.2 hden)
  have hθ3 : θ ≤ 1 / 3 := min_le_left _ _
  have hθ2 : 192 * κ * (d : ℝ) ^ 2 * C₁ * θ ≤ 1 := by
    have h1 : θ ≤ 1 / (192 * κ * (d : ℝ) ^ 2 * C₁) := min_le_right _ _
    have h2 := hden
    calc 192 * κ * (d : ℝ) ^ 2 * C₁ * θ ≤ 192 * κ * (d : ℝ) ^ 2 * C₁ * (1 / (192 * κ * (d : ℝ) ^ 2 * C₁)) :=
          mul_le_mul_of_nonneg_left h1 h2.le
      _ = 1 := mul_one_div_cancel hden.ne'
  set T : ℝ := 1 + 12 * (d : ℝ) ^ 2 * C₁ * K ^ 2 / θ with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ 12 * (d : ℝ) ^ 2 * C₁ * K ^ 2 / θ :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hC₁0.le)
        (sq_nonneg K)) hθ0.le
    linarith only [this]
  have hT0 : 0 < T := by linarith only [hT1]
  have hκT : 0 ≤ κ * T := mul_nonneg hκ0.le hT0.le
  refine ⟨1 / (2 * d), 20 * κ * T + 2 * T + 30 * d + 5,
    div_pos one_pos (mul_pos two_pos hd0), by linarith only [hκT, hT0, hd0], ?_⟩
  intro m A δ c a b hAs hδ0 hδε hAδ f hf φ u hφ hZ hu1 hu2
  have hdδ : (d : ℝ) * δ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hδε hd0.le
    have hdi : (d : ℝ) * (d : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hd0.ne'
    have e1 : (d : ℝ) * (1 / (2 * d)) = 1 / 2 := by linear_combination (1 / 2) * hdi
    linarith only [this, e1]
  have hδ1 : δ ≤ 1 := by
    have : (1 : ℝ) / (2 * d) ≤ 1 := by
      rw [div_le_one (mul_pos two_pos hd0)]; linarith only [hd1]
    linarith only [hδε, this]
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓd
  have hℓ : 0 < ℓ := zpow_pos (by norm_num) m
  have hA := r3d_cacc_step e m (A := A) (δ := δ) (G₁ := G₁) (c := c) hG1
    (fun lam hlam x i => (Hcut _ lam hlam).1 x i) hAs hδ0 hδ1 hdδ hAδ hf hφ hZ hu1 hu2
  -- the energy near the face dominates the `e`-component
  have hh : 0 < θ * ℓ := mul_pos hθ0 hℓ
  have hℓl : ℓ * ℓ⁻¹ = 1 := mul_inv_cancel₀ hℓ.ne'
  have hh3 : θ * ℓ ≤ ℓ / 3 := by
    have := mul_le_mul_of_nonneg_right hθ3 hℓ.le
    linarith only [this]
  have hF1 := r3d_F1 hd e m (h := θ * ℓ) (K := K) hh hh3 hK u (by
    have := r3c_localized_sub e m c hZ hu1
    exact this) a b
  have hX : ∫ x in r3d_Ebox e m (ℓ / 3), u.grad x e ^ 2 ≤
      ∫ x in r3d_Ebox e m (ℓ / 3), vecNormSq (u.grad x) := by
    have hi1 : Integrable (fun x => u.grad x e ^ 2) (volume.restrict (openCubeSet (originCube d m))) :=
      (u.grad_memL2 e).integrable_sq
    have hi2 : Integrable (fun x => vecNormSq (u.grad x)) (volume.restrict (openCubeSet (originCube d m))) := by
      have : (fun x => vecNormSq (u.grad x)) = fun x => ∑ i, (u.grad x i) ^ 2 := by
        funext x; simp [vecNormSq, vecDot, pow_two]
      rw [this]
      exact integrable_finsetSum _ fun i _ => (u.grad_memL2 i).integrable_sq
    have hi1' : IntegrableOn (fun x => u.grad x e ^ 2) (r3d_Ebox e m (ℓ / 3)) volume :=
      (show IntegrableOn (fun x => u.grad x e ^ 2) (openCubeSet (originCube d m)) volume from hi1).mono_set
        Set.inter_subset_right
    have hi2' : IntegrableOn (fun x => vecNormSq (u.grad x)) (r3d_Ebox e m (ℓ / 3)) volume :=
      (show IntegrableOn (fun x => vecNormSq (u.grad x)) (openCubeSet (originCube d m)) volume from hi2).mono_set
        Set.inter_subset_right
    exact setIntegral_mono_on hi1' hi2' (r3d_Ebox_measurable e m _) fun x _ => sq_apply_le_vecNormSq _ e
  rw [← hℓd] at hA hF1
  rw [← hκ] at hA
  rw [← hC₁] at hF1
  set Y' : ℝ := ∫ x in r3d_Ebox e m (ℓ / 3), vecNormSq (u.grad x) with hY'
  set X : ℝ := ∫ x in r3d_Ebox e m (ℓ / 3), u.grad x e ^ 2 with hXd
  set U : ℝ := ∫ x in openCubeSet (originCube d m), u.toFun x ^ 2 with hU
  set G2 : ℝ := ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 with hG2
  set F2 : ℝ := ∫ x in openCubeSet (originCube d m), f x ^ 2 with hF2
  set S : ℝ := ℓ ^ (d + 2) * (|c| * δ) ^ 2 with hS
  have hU0 : 0 ≤ U := integral_nonneg fun x => sq_nonneg _
  have hG0 : 0 ≤ G2 := integral_nonneg fun x => sq_nonneg _
  have hF0 : 0 ≤ F2 := integral_nonneg fun x => sq_nonneg _
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have hY0 : 0 ≤ Y' := integral_nonneg fun x => vecNormSq_nonneg _
  have hS0 : 0 ≤ S := by rw [hS]; exact mul_nonneg (pow_nonneg hℓ.le _) (sq_nonneg _)
  have hFl0 : 0 ≤ ℓ ^ 4 * F2 := mul_nonneg (pow_nonneg hℓ.le 4) hF0
  set Z : ℝ := ℓ ^ 2 * Y' with hZd
  have hZ0 : 0 ≤ Z := by rw [hZd]; exact mul_nonneg (sq_nonneg ℓ) hY0
  set β : ℝ := 24 * (d : ℝ) ^ 2 * C₁ * θ with hβ
  have hβ0 : 0 ≤ β := by
    rw [hβ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hC₁0.le) hθ0.le
  have hβκ : 8 * κ * β ≤ 1 := by
    have : 8 * κ * β = 192 * κ * (d : ℝ) ^ 2 * C₁ * θ := by rw [hβ]; ring
    rw [this]; exact hθ2
  have hβ4 : β ≤ 1 / 4 := by
    have := mul_nonneg (by linarith only [hκ12] : 0 ≤ 8 * κ - 4) hβ0
    linarith only [this, hβκ]
  have hU2 : U ≤ 2 * T * G2 + β * Z := by
    have e1 : 6 * (d : ℝ) ^ 2 * C₁ * ℓ * (4 * (θ * ℓ) * X + 4 * K ^ 2 / (θ * ℓ) * G2) =
        β * (ℓ ^ 2 * X) + 24 * (d : ℝ) ^ 2 * C₁ * K ^ 2 / θ * G2 := by
      rw [hβ]
      linear_combination (24 * (d : ℝ) ^ 2 * C₁ * K ^ 2 * G2 * θ⁻¹) * hℓl
    have e2 : 2 * T * G2 = 2 * G2 + 24 * (d : ℝ) ^ 2 * C₁ * K ^ 2 / θ * G2 := by
      rw [hT]; ring
    have h3 : β * (ℓ ^ 2 * X) ≤ β * Z := by
      rw [hZd]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (sq_nonneg ℓ)) hβ0
    rw [e1] at hF1
    linarith only [hF1, e2, h3]
  have hZ2 : Z ≤ 16 * κ * T * G2 + 4 * (ℓ ^ 4 * F2) + 24 * d * S := by
    have h1 : Z ≤ 4 * κ * U + 2 * (ℓ ^ 4 * F2) + 12 * d * S := by
      have : Z = ℓ ^ 2 * Y' := hZd
      linarith only [hA, this, hS]
    have h2 := mul_le_mul_of_nonneg_left hU2 (by linarith only [hκ0] : (0 : ℝ) ≤ 4 * κ)
    have h3 : 8 * κ * β * Z ≤ 1 * Z := mul_le_mul_of_nonneg_right hβκ hZ0
    linarith only [h1, h2, h3]
  have hU3 : U ≤ 2 * T * G2 + Z / 4 := by
    have := mul_le_mul_of_nonneg_right hβ4 hZ0
    linarith only [hU2, this]
  have hfinal : Z + U ≤ (20 * κ * T + 2 * T) * G2 + 5 * (ℓ ^ 4 * F2) + 30 * d * S := by
    linarith only [hZ2, hU3]
  have hC : 0 ≤ (30 * (d : ℝ) + 5) * G2 + (20 * κ * T + 2 * T + 30 * d) * (ℓ ^ 4 * F2) +
      (20 * κ * T + 2 * T + 5) * S :=
    add_nonneg (add_nonneg (mul_nonneg (by linarith only [hd0]) hG0)
      (mul_nonneg (by linarith only [hκT, hT0, hd0]) hFl0))
      (mul_nonneg (by linarith only [hκT, hT0]) hS0)
  have hZeq : ℓ ^ 2 * Y' + U = Z + U := by rw [hZd]
  rw [hZeq]
  have : (20 * κ * T + 2 * T + 30 * d + 5) * (G2 + ℓ ^ 4 * F2 + S) =
      (20 * κ * T + 2 * T) * G2 + 5 * (ℓ ^ 4 * F2) + 30 * d * S +
        ((30 * (d : ℝ) + 5) * G2 + (20 * κ * T + 2 * T + 30 * d) * (ℓ ^ 4 * F2) +
          (20 * κ * T + 2 * T + 5) * S) := by ring
  linarith only [hfinal, hC, this]

end SuperdiffusionCLT.Section7
