/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaM
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaC

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3c_cutS_mul_cut (e : Fin d) (m : ℤ) (x : Vec d) :
    r3c_cutS (r3c_z0 e m) ((3 : ℝ) ^ m / 3) x * p12_cut (r3c_z0 e m) ((3 : ℝ) ^ m) d d x =
      r3c_cutS (r3c_z0 e m) ((3 : ℝ) ^ m / 3) x := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hlam : (0 : ℝ) < (3 : ℝ) ^ m / 3 := div_pos hℓ (by norm_num)
  by_cases hx : x ∈ tsupport (r3c_cutS (r3c_z0 e m) ((3 : ℝ) ^ m / 3))
  · have hbox := r3c_cutS_tsupport (r3c_z0 e m) hlam hx
    have hbox4 : ∀ i, |x i - r3c_z0 e m i| ≤ (3 : ℝ) ^ m / 4 := fun i => by
      refine (hbox i).trans ?_
      linarith only [hℓ]
    rw [p12_cut_last _ hℓ d hbox4, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

theorem r3c_preimage_faceCube (e : Fin d) (m : ℤ) (s : ℝ) :
    (fun x : Vec d => x + r3c_shift e m) ⁻¹' r3c_faceCube e s =
      axisCube (r3c_z0 e m + r3c_faceBase e s) s := by
  ext x
  have hz : ∀ i, r3c_z0 e m i + r3c_shift e m i = 0 := fun i => by
    have := congrFun (r3c_z0_add_shift e m) i
    simpa using this
  simp only [r3c_faceCube, axisCube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo, Pi.add_apply]
  refine forall_congr' fun i => ?_
  have := hz i
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2, this]

theorem r3c_abs_le_of_mem_cube (e : Fin d) (m : ℤ) {s : ℝ} {x : Vec d}
    (hx : x ∈ axisCube (r3c_z0 e m + r3c_faceBase e s) s) (i : Fin d) :
    |x i - r3c_z0 e m i| ≤ s := by
  have h := hx i (Set.mem_univ i)
  simp only [Set.mem_Ioo, Pi.add_apply] at h
  rw [abs_le]
  by_cases hi : i = e
  · subst hi
    simp only [r3c_z0, r3c_faceBase, ite_true] at h ⊢
    constructor <;> linarith only [h.1, h.2]
  · simp only [r3c_z0, r3c_faceBase, hi, ite_false] at h ⊢
    constructor <;> linarith only [h.1, h.2]

theorem r3c_center_mem_cube (e : Fin d) (m : ℤ) {s : ℝ} (hs : 0 < s) :
    (fun i => (r3c_z0 e m + r3c_faceBase e s) i + s / 2) ∈
      axisCube (r3c_z0 e m + r3c_faceBase e s) s := by
  intro i _
  simp only [Set.mem_Ioo]
  constructor <;> linarith only [hs]

theorem r3c_flat_cutoff_decay [NeZero d] (hd : 2 ≤ d) (e : Fin d) {p : ℝ} (hp : (d : ℝ) < p) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ (m : ℤ) (A : CoeffField d) (K δ : ℝ),
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) → 0 ≤ δ → δ ≤ ε →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        K * (3 : ℝ) ^ m ≤ δ →
        ∀ f : Vec d → ℝ, MemLp f (ENNReal.ofReal p) (normalizedCubeMeasure (originCube d m)) →
        ∀ φ : H1Function (openCubeSet (originCube d m)),
          IsWeakSolutionOn A (openCubeSet (originCube d m)) φ f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m))
            {x | ∀ i, |x i - r3c_z0 e m i| < (3 : ℝ) ^ m / 2} φ.toFun →
          ∀ c s : ℝ, 0 < s → s ≤ (3 : ℝ) ^ m / 12 →
            ∃ (a : ℝ) (b : Vec d),
              ∀ᵐ x ∂(volume.restrict (axisCube (r3c_z0 e m + r3c_faceBase e s) s)),
                |φ.toFun x - c * r3c_nrm e m x - (a + vecDot b (x - r3c_z0 e m))| ≤
                  C * s * (s / (3 : ℝ) ^ m) ^ (1 - (d : ℝ) / p) *
                    ((eLpNorm (fun x => φ.grad x - c • basisVec e) 2
                        (normalizedCubeMeasure (originCube d m))).toReal +
                      ((3 : ℝ) ^ m)⁻¹ * (eLpNorm (fun x => φ.toFun x - c * r3c_nrm e m x) 2
                        (normalizedCubeMeasure (originCube d m))).toReal +
                      (3 : ℝ) ^ m * (eLpNorm f (ENNReal.ofReal p)
                        (normalizedCubeMeasure (originCube d m))).toReal + δ * |c|) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hp0 : 0 < p := by linarith only [hd1, hp]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h3d : (0 : ℝ) < 3 ^ d := pow_pos (by norm_num) d
  have hp2 : (2 : ℝ) < p := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this, hp]
  obtain ⟨ε₁, C₁, hε₁, hC₁, Hl⟩ := p12_ladder hd hp2 d
  obtain ⟨ε₂, C₂, hε₂, hC₂, Hd⟩ := r3c_flat_decay hd e hp
  obtain ⟨G₁, G₂, hG₁, hG₂, Hcut⟩ := r3c_cutS_bounds d
  set M : ℝ := max (12 * (d : ℝ) ^ 2 * G₁) (9 * (d : ℝ) ^ 2 * (G₁ + 2 * G₂)) with hM
  have hM0 : 0 ≤ M :=
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ))) hG₁).trans (le_max_left _ _)
  have hq0 : 0 ≤ 3 * (2 * (d : ℝ) * G₁ + d) :=
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hd0) hG₁) hd0)
  refine ⟨min (min ε₁ ε₂) 1, C₂ * 3 ^ d * (1 + M * C₁ + 3 * (2 * d * G₁ + d)),
    lt_min (lt_min hε₁ hε₂) one_pos,
    mul_pos (mul_pos hC₂ h3d)
      (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg one_pos (mul_nonneg hM0 hC₁.le)) hq0), ?_⟩
  intro m A K δ hAs hδ0 hδε hδ hK hKl f hf φ hφ hZ c s hs hsm
  have hδ1 : δ ≤ 1 := hδε.trans (min_le_right _ _)
  have hδ₁ : δ ≤ ε₁ := hδε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₂ : δ ≤ ε₂ := hδε.trans ((min_le_left _ _).trans (min_le_right _ _))
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓdef
  have hℓ : 0 < ℓ := zpow_pos (by norm_num) m
  have hQℓ : cubeScaleFactor (originCube d m) = ℓ := cubeScaleFactor_originCube m
  have hprob := p12_isProb (originCube d m)
  set μ := normalizedCubeMeasure (originCube d m) with hμ
  set z₀ : Vec d := r3c_z0 e m with hz₀
  -- the function `u = φ - c n`
  obtain ⟨u, hu1, hu2⟩ := r3c_exists_sub_nrm (originCube d m) e m c φ
  have hu1f : u.toFun = fun x => φ.toFun x - c * r3c_nrm e m x := funext hu1
  have hu2f : u.grad = fun x => φ.grad x - c • basisVec e := funext hu2
  have hAb : ∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j| ≤ 2 := fun x hx i j =>
    r3c_abs_entry_le_two x (hδ x hx) hδ1 i j
  have hu' : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (r3c_slopeField A e c) :=
    r3c_slope_equation (originCube d m) e hAs hAb c hφ hu2
  have hZu := r3c_localized_sub e m c hZ hu1
  have hAmeas : ∀ i j, AEStronglyMeasurable (fun x => A x i j)
      (volume.restrict (openCubeSet (originCube d m))) := fun i j =>
    (hAs i j).continuous.aestronglyMeasurable
  have hε1 : ∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε₁ :=
    fun x hx i j => (hδ x hx i j).trans hδ₁
  have hpge : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp2.le
  have hf2 : MemLp f 2 μ := hf.mono_exponent hpge
  have hpstar : p12_pstar d p ≤ p := by
    unfold p12_pstar
    have hdp : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 (by linarith only [hd1])
    have : p⁻¹ ≤ p⁻¹ + (d : ℝ)⁻¹ := by linarith only [hdp]
    calc (p⁻¹ + (d : ℝ)⁻¹)⁻¹ ≤ (p⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hp0) this
      _ = p := inv_inv p
  have hfp : MemLp f (ENNReal.ofReal (p12_pstar d p)) μ :=
    hf.mono_exponent (ENNReal.ofReal_le_ofReal hpstar)
  have hgm : AEStronglyMeasurable (r3c_slopeField A e c) μ :=
    (continuous_pi fun i => (r3c_slopeField_contDiff hAs e c i).continuous).aestronglyMeasurable
  have hgb : ∀ᵐ x ∂μ, ‖r3c_slopeField A e c x‖ ≤ |c| * δ :=
    r3c_ae_normalized_of_mem (originCube d m) fun x hx => r3c_slopeField_norm_le e c x (hδ x hx) hδ0
  have hgP : MemLp (r3c_slopeField A e c) (ENNReal.ofReal p) μ :=
    (MemLp.of_bound hgm (|c| * δ) hgb).mono_exponent le_top
  obtain ⟨W, hW1, hW2, hWp, hWgp, hWb⟩ := Hl (originCube d m) z₀ A hAmeas hε1 f
    (r3c_slopeField A e c) u hu' hf2 hfp hgP (by rw [hQℓ]; exact hZu)
  rw [p12_tk_last hd hp2] at hWp hWgp hWb
  rw [hQℓ] at hWb
  simp only [hQℓ] at hW1 hW2
  -- the real form of the ladder inequality
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := le_trans (by norm_num) hpge
  have hu2L : MemLp u.grad 2 μ := memLp_normalized_of_memVectorL2 (originCube d m) u.grad_memVectorL2
  have huL : MemLp u.toFun 2 μ := memLp_normalized_of_restrict (originCube d m) u.memL2
  have hfpstar : (eLpNorm f (ENNReal.ofReal (p12_pstar d p)) μ).toReal ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top (p12_eLpNorm_mono_exp (originCube d m)
      (ENNReal.ofReal_le_ofReal hpstar))
  have hgnorm : (eLpNorm (r3c_slopeField A e c) (ENNReal.ofReal p) μ).toReal ≤ |c| * δ := by
    have h1 : eLpNorm (r3c_slopeField A e c) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (|c| * δ) := by
      refine (eLpNorm_le_of_ae_bound hgm hgb).trans ?_
      simp [hprob.measure_univ]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (mul_nonneg (abs_nonneg c) hδ0)] at this
  set X : ℝ := (eLpNorm W.toH1Function.grad (ENNReal.ofReal p) μ).toReal with hX
  set Y : ℝ := (eLpNorm W.toH1Function.toFun (ENNReal.ofReal p) μ).toReal with hY
  set Ru : ℝ := (eLpNorm u.toFun 2 μ).toReal with hRu
  set Rg : ℝ := (eLpNorm u.grad 2 μ).toReal with hRg
  set Rf : ℝ := (eLpNorm f (ENNReal.ofReal p) μ).toReal with hRf
  set Rp : ℝ := (eLpNorm f (ENNReal.ofReal (p12_pstar d p)) μ).toReal with hRp
  set Rc : ℝ := (eLpNorm (r3c_slopeField A e c) (ENNReal.ofReal p) μ).toReal with hRc
  have hlad0 : ℓ * X + Y ≤ C₁ * (ℓ * Rg + Ru + ℓ ^ 2 * Rp + ℓ * Rc) := by
    have hfin1 : eLpNorm W.toH1Function.grad (ENNReal.ofReal p) μ ≠ ⊤ := hWgp.eLpNorm_ne_top
    have hfin2 : eLpNorm W.toH1Function.toFun (ENNReal.ofReal p) μ ≠ ⊤ := hWp.eLpNorm_ne_top
    have hfin3 : eLpNorm u.grad 2 μ ≠ ⊤ := hu2L.eLpNorm_ne_top
    have hfin4 : eLpNorm u.toFun 2 μ ≠ ⊤ := huL.eLpNorm_ne_top
    have hfin5 : eLpNorm f (ENNReal.ofReal (p12_pstar d p)) μ ≠ ⊤ := hfp.eLpNorm_ne_top
    have hfin6 : eLpNorm (r3c_slopeField A e c) (ENNReal.ofReal p) μ ≠ ⊤ := hgP.eLpNorm_ne_top
    have hWb' : ENNReal.ofReal ℓ * eLpNorm W.toH1Function.grad (ENNReal.ofReal p) μ +
        eLpNorm W.toH1Function.toFun (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C₁ *
          ((ENNReal.ofReal ℓ * eLpNorm u.grad 2 μ + eLpNorm u.toFun 2 μ) +
            ENNReal.ofReal ℓ ^ 2 * eLpNorm f (ENNReal.ofReal (p12_pstar d p)) μ +
              ENNReal.ofReal ℓ * eLpNorm (r3c_slopeField A e c) (ENNReal.ofReal p) μ) := hWb
    rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin2, ← ENNReal.ofReal_toReal hfin3,
      ← ENNReal.ofReal_toReal hfin4, ← ENNReal.ofReal_toReal hfin5, ← ENNReal.ofReal_toReal hfin6,
      ← ENNReal.ofReal_mul hℓ.le,
      ← ENNReal.ofReal_add (mul_nonneg hℓ.le ENNReal.toReal_nonneg) ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul hℓ.le,
      ← ENNReal.ofReal_add (mul_nonneg hℓ.le ENNReal.toReal_nonneg) ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_pow hℓ.le, ← ENNReal.ofReal_mul (pow_nonneg hℓ.le 2),
      ← ENNReal.ofReal_add
        (add_nonneg (mul_nonneg hℓ.le ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
        (mul_nonneg (pow_nonneg hℓ.le 2) ENNReal.toReal_nonneg),
      ← ENNReal.ofReal_mul hℓ.le,
      ← ENNReal.ofReal_add
        (add_nonneg (add_nonneg (mul_nonneg hℓ.le ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
          (mul_nonneg (pow_nonneg hℓ.le 2) ENNReal.toReal_nonneg))
        (mul_nonneg hℓ.le ENNReal.toReal_nonneg),
      ← ENNReal.ofReal_mul hC₁.le,
      ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hC₁.le (add_nonneg (add_nonneg (add_nonneg
          (mul_nonneg hℓ.le ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
          (mul_nonneg (pow_nonneg hℓ.le 2) ENNReal.toReal_nonneg))
          (mul_nonneg hℓ.le ENNReal.toReal_nonneg)))] at hWb'
    exact hWb'
  have hlad : ℓ * X + Y ≤ C₁ * (ℓ * Rg + Ru + ℓ ^ 2 * Rf + ℓ * (|c| * δ)) := by
    refine hlad0.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₁.le
    have h1 : ℓ ^ 2 * Rp ≤ ℓ ^ 2 * Rf := mul_le_mul_of_nonneg_left hfpstar (sq_nonneg ℓ)
    have h2 : ℓ * Rc ≤ ℓ * (|c| * δ) := mul_le_mul_of_nonneg_left hgnorm hℓ.le
    linarith only [h1, h2]
  -- the cutoff datum and its `L^p` bound
  set lam : ℝ := ℓ / 3 with hlamdef
  have hlam : 0 < lam := div_pos hℓ (by norm_num)
  set η : Vec d → ℝ := r3c_cutS z₀ lam with hηdef
  set F' : Vec d → ℝ := r3c_cutoffData A η f (r3c_slopeField A e c) u with hF'
  have hμeq : μ = ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ • volume.restrict (openCubeSet (originCube d m)) :=
    normalizedCubeMeasure_eq_smul _
  have hmeasμ : ∀ {g : Vec d → ℝ}, AEStronglyMeasurable g (volume.restrict (openCubeSet (originCube d m))) →
      AEStronglyMeasurable g μ := fun h => by rw [hμeq]; exact h.smul_measure _
  have hF'm : AEStronglyMeasurable F' μ :=
    r3c_cutoffData_aesm hAs (r3c_cutS_contDiff z₀ lam)
      (fun i => (r3c_slopeField_contDiff hAs e c i)) u hf.aestronglyMeasurable
      (fun i => hmeasμ (u.grad_memL2 i).aestronglyMeasurable) (hmeasμ u.memL2.aestronglyMeasurable)
  have hKl' : K * ℓ ≤ δ := hKl
  have hbd := r3c_F_bound_ae e m hAs c hG₁ hG₂ hδ0 hδ1 hKl hδ hK
    (fun z₀ lam hl x i => (Hcut z₀ lam hl).1 x i) (fun z₀ lam hl x j k => (Hcut z₀ lam hl).2 x j k)
    f (u := u) (W := W.toH1Function) hW1 hW2
  have hLp := r3c_lpBound4 (originCube d m) hP1 (F := F') (f := f) (W := W.toH1Function.toFun)
    (Y := W.toH1Function.grad) (a1 := 4 * (d : ℝ) ^ 2 * G₁ / lam)
    (a2 := (d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2) (a3 := (2 * d * G₁ + d) * (|c| * δ / lam))
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ))) hG₁) hlam.le)
    (div_nonneg (mul_nonneg (sq_nonneg (d : ℝ)) (add_nonneg hG₁ (mul_nonneg zero_le_two hG₂)))
      (sq_nonneg lam))
    (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hd0) hG₁) hd0)
      (div_nonneg (mul_nonneg (abs_nonneg c) hδ0) hlam.le)) hF'm hf hWgp hWp hbd
  obtain ⟨hFmem, hFnorm⟩ := hLp
  set N : ℝ := (eLpNorm F' (ENNReal.ofReal p) μ).toReal with hN
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hRf0 : 0 ≤ Rf := ENNReal.toReal_nonneg
  have hRg0 : 0 ≤ Rg := ENNReal.toReal_nonneg
  have hRu0 : 0 ≤ Ru := ENNReal.toReal_nonneg
  have hlam3 : lam = ℓ / 3 := hlamdef
  have hℓl : ℓ * ℓ⁻¹ = 1 := mul_inv_cancel₀ hℓ.ne'
  have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.2 hℓ.le
  have hℓa1 : ℓ * (4 * (d : ℝ) ^ 2 * G₁ / lam) ≤ M := by
    have : ℓ * (4 * (d : ℝ) ^ 2 * G₁ / lam) = 12 * (d : ℝ) ^ 2 * G₁ := by
      rw [hlam3]; linear_combination (12 * (d : ℝ) ^ 2 * G₁) * hℓl
    rw [this]; exact le_max_left _ _
  have hℓa2 : ℓ * ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2) ≤ M / ℓ := by
    have : ℓ * ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2) = 9 * (d : ℝ) ^ 2 * (G₁ + 2 * G₂) / ℓ := by
      rw [hlam3]; linear_combination (9 * (d : ℝ) ^ 2 * (G₁ + 2 * G₂) * ℓ⁻¹) * hℓl
    rw [this]
    exact div_le_div_of_nonneg_right (le_max_right _ _) hℓ.le
  have hℓa3 : ℓ * ((2 * d * G₁ + d) * (|c| * δ / lam)) = 3 * (2 * d * G₁ + d) * (|c| * δ) := by
    rw [hlam3]; linear_combination (3 * (2 * d * G₁ + d) * (|c| * δ)) * hℓl
  have hMX : M * X + M / ℓ * Y ≤ M * C₁ * (Rg + ℓ⁻¹ * Ru + ℓ * Rf + |c| * δ) := by
    have h1 : M * X + M / ℓ * Y = (M / ℓ) * (ℓ * X + Y) := by
      linear_combination (-(M * X)) * hℓl
    rw [h1]
    exact calc (M / ℓ) * (ℓ * X + Y) ≤ (M / ℓ) * (C₁ * (ℓ * Rg + Ru + ℓ ^ 2 * Rf + ℓ * (|c| * δ))) :=
          mul_le_mul_of_nonneg_left hlad (div_nonneg hM0 hℓ.le)
      _ = M * C₁ * (Rg + ℓ⁻¹ * Ru + ℓ * Rf + |c| * δ) := by
          linear_combination (M * C₁ * (Rg + ℓ * Rf + |c| * δ)) * hℓl
  have hℓN : ℓ * N ≤ (1 + M * C₁ + 3 * (2 * d * G₁ + d)) * (Rg + ℓ⁻¹ * Ru + ℓ * Rf + δ * |c|) := by
    have e1 : ℓ * N ≤ ℓ * (Rf + 4 * (d : ℝ) ^ 2 * G₁ / lam * X + (d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2 * Y +
        (2 * d * G₁ + d) * (|c| * δ / lam)) := mul_le_mul_of_nonneg_left hFnorm hℓ.le
    have e2 : ℓ * (Rf + 4 * (d : ℝ) ^ 2 * G₁ / lam * X + (d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2 * Y +
        (2 * d * G₁ + d) * (|c| * δ / lam)) =
        ℓ * Rf + (ℓ * (4 * (d : ℝ) ^ 2 * G₁ / lam)) * X + (ℓ * ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2)) * Y +
          ℓ * ((2 * d * G₁ + d) * (|c| * δ / lam)) := by ring
    have e3 : (ℓ * (4 * (d : ℝ) ^ 2 * G₁ / lam)) * X ≤ M * X := mul_le_mul_of_nonneg_right hℓa1 hX0
    have e4 : (ℓ * ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2)) * Y ≤ M / ℓ * Y :=
      mul_le_mul_of_nonneg_right hℓa2 hY0
    rw [hℓa3] at e2
    have hcδ : 0 ≤ δ * |c| := mul_nonneg hδ0 (abs_nonneg c)
    have hq := hq0
    have hMC : 0 ≤ M * C₁ := mul_nonneg hM0 hC₁.le
    have hT1 : ℓ * Rf ≤ Rg + ℓ⁻¹ * Ru + ℓ * Rf + δ * |c| := by
      have : 0 ≤ ℓ⁻¹ * Ru := mul_nonneg hℓi hRu0
      linarith only [hRg0, this, hcδ]
    have hT2 : 3 * (2 * d * G₁ + d) * (|c| * δ) ≤ 3 * (2 * (d : ℝ) * G₁ + d) *
        (Rg + ℓ⁻¹ * Ru + ℓ * Rf + δ * |c|) := by
      refine mul_le_mul_of_nonneg_left ?_ hq
      have : 0 ≤ ℓ⁻¹ * Ru := mul_nonneg hℓi hRu0
      have : 0 ≤ ℓ * Rf := mul_nonneg hℓ.le hRf0
      rw [mul_comm |c| δ]
      linarith only [hRg0, ‹0 ≤ ℓ⁻¹ * Ru›, ‹0 ≤ ℓ * Rf›]
    have hT3 : M * C₁ * (Rg + ℓ⁻¹ * Ru + ℓ * Rf + |c| * δ) = M * C₁ * (Rg + ℓ⁻¹ * Ru + ℓ * Rf + δ * |c|) := by
      rw [mul_comm |c| δ]
    linarith only [e1, e2, e3, e4, hMX, hT1, hT2, hT3, hMC]
  -- the cutoff function `w' = η u` as an `H¹₀` function
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := r3c_cutS_contDiff z₀ lam
  have hηc : HasCompactSupport η := r3c_cutS_hasCompactSupport z₀ hlam
  let w' : H10Function (openCubeSet (originCube d m)) := W.mulContDiffHasCompactSupport hη hηc
  have hw'f : ∀ x, w'.toH1Function.toFun x = η x * u.toFun x := by
    intro x
    show η x * W.toH1Function.toFun x = η x * u.toFun x
    rw [hW1 x, ← mul_assoc]
    have := r3c_cutS_mul_cut (d := d) e m x
    exact congrArg (· * u.toFun x) this
  set z : Vec d := r3c_shift e m with hz
  have hsupp : ∀ n, tsupport (w'.approx n) ⊆ {x : Vec d | x + z ∈ flatHalfCube e (m - 1)} := by
    intro n x hx
    have h1 : x ∈ tsupport η := tsupport_mul_subset_left hx
    have h2 : x ∈ tsupport (W.approx n) := tsupport_mul_subset_right hx
    have hxD : x ∈ openCubeSet (originCube d m) := W.approx_support_subset n h2
    exact r3c_near_face_mem e m hxD (r3c_cutS_tsupport z₀ hlam h1)
  have hAb' : ∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j| ≤ 2 := hAb
  have hK' : ∀ x ∈ openCubeSet (originCube d m), ∀ y : Vec d, ‖matVecMul (A x) y‖ ≤ (2 * d) * ‖y‖ :=
    fun x hx y => r3c_norm_matVec_le x (hδ x hx) hδ1 y
  have hg2 : MemLp (r3c_slopeField A e c) 2 μ := hgP.mono_exponent hpge
  have hMη : ∀ x, |η x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (r3c_cutS_01 z₀ lam x).1]; exact (r3c_cutS_01 z₀ lam x).2
  have hΛ : ∀ x, ‖p12_grad η x‖ ≤ G₁ / lam := fun x =>
    r3c_norm_grad_le x (div_nonneg hG₁ hlam.le) (fun i => (Hcut z₀ lam hlam).1 x i)
  have hsol := r3c_cutoff_scalar (originCube d m) hAs hAb' hK' (r3c_slopeField_contDiff hAs e c) hf2 hg2
    hu' hη hηc hMη hΛ w' hw'f
  obtain ⟨wV, hwV1, hwV2, hwVsol⟩ := r3c_transport e (m - 1) z (isOpen_openCubeSet _) (A := A) (F := F') w'
    (r3c_halfCube_preimage_subset e m) hsupp hsol
  -- the flat decay for `wV`
  have hVD := r3c_halfCube_preimage_subset e m
  have hmemV : ∀ x ∈ flatHalfCube e (m - 1), x - z ∈ openCubeSet (originCube d m) := fun x hx =>
    hVD (by
      show x - z + z ∈ flatHalfCube e (m - 1)
      rwa [sub_add_cancel])
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 (r3c_zero_mem_cube m) e e e)
  have hAV : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => (fun y => A (y - z)) x i j) := fun i j =>
    (hAs i j).comp (contDiff_id.sub contDiff_const)
  have hAVε : ∀ x ∈ flatHalfCube e (m - 1), ∀ i j,
      |(fun y => A (y - z)) x i j - (1 : Mat d) i j| ≤ ε₂ := fun x hx i j =>
    (hδ _ (hmemV x hx) i j).trans hδ₂
  have hAVK : ∀ x ∈ flatHalfCube e (m - 1), ∀ i j k,
      |fderiv ℝ (fun y => (fun y => A (y - z)) y i j) x (basisVec k)| ≤ K := by
    intro x hx i j k
    have : fderiv ℝ (fun y => A (y - z) i j) x = fderiv ℝ (fun y => A y i j) (x - z) := by
      have h := fderiv_comp_add_right (𝕜 := ℝ) (f := fun w => A w i j) (x := x) (-z)
      simpa only [sub_eq_add_neg] using h
    simp only
    rw [this]
    exact hK _ (hmemV x hx) i j k
  have h3m1 : (3 : ℝ) ^ (m - 1) = ℓ / 3 := by rw [hℓdef, zpow_sub_one₀ (by norm_num)]; ring
  have hKℓ₂ : K * cubeScaleFactor (originCube d (m - 1)) ≤ ε₂ := by
    rw [cubeScaleFactor_originCube, h3m1]
    refine le_trans ?_ hδ₂
    refine le_trans ?_ hKl
    exact mul_le_mul_of_nonneg_left (by linarith only [hℓ]) hK0
  have hVF := r3c_flatHalf_translate_norm e m z (q := ENNReal.ofReal p) hP1
    ENNReal.ofReal_ne_top hFmem hVD
  have hsm2 : s ≤ (3 : ℝ) ^ (m - 1) / 2 := by
    rw [h3m1]; linarith only [hsm, hℓ]
  obtain ⟨ŵ, c', hŵc, hŵae, hŵb⟩ := Hd (m - 1) (fun y => A (y - z)) K hAV hAVε hAVK hKℓ₂
    (fun x => F' (x - z)) hVF.1 wV hwVsol s hs hsm2
  -- back to the cube geometry
  set α : ℝ := 1 - (d : ℝ) / p with hα
  have hα1 : α ≤ 1 := by
    have : 0 ≤ (d : ℝ) / p := div_nonneg hd0 hp0.le
    linarith only [this]
  have hpow : (s / (ℓ / 3)) ^ α ≤ 3 * (s / ℓ) ^ α := by
    have e1 : s / (ℓ / 3) = 3 * (s / ℓ) := by
      rw [div_div_eq_mul_div]; ring
    rw [e1, Real.mul_rpow (by norm_num) (div_nonneg hs.le hℓ.le)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (div_nonneg hs.le hℓ.le) _)
    exact calc (3 : ℝ) ^ α ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 3 := Real.rpow_one 3
  set Rhs : ℝ := Rg + ℓ⁻¹ * Ru + ℓ * Rf + δ * |c| with hRhs
  have hRhs0 : 0 ≤ Rhs :=
    add_nonneg (add_nonneg (add_nonneg hRg0 (mul_nonneg hℓi hRu0)) (mul_nonneg hℓ.le hRf0))
      (mul_nonneg hδ0 (abs_nonneg c))
  set Cq : ℝ := 1 + M * C₁ + 3 * (2 * d * G₁ + d) with hCq
  have hbnd : ∀ x ∈ r3c_faceCube e s, ∀ y ∈ r3c_faceCube e s,
      |ŵ x - ŵ y - vecDot c' (x - y)| ≤
        C₂ * 3 ^ d * Cq * s * (s / ℓ) ^ α * Rhs := by
    intro x hx y hy
    refine (hŵb x hx y hy).trans ?_
    rw [h3m1]
    have hFb : flatHalfNorm e (m - 1) (ENNReal.ofReal p) (fun x => F' (x - z)) ≤ 3 ^ d * N := hVF.2
    have hFb0 : 0 ≤ flatHalfNorm e (m - 1) (ENNReal.ofReal p) (fun x => F' (x - z)) :=
      ENNReal.toReal_nonneg
    have hCs : 0 ≤ C₂ * s := mul_nonneg hC₂.le hs.le
    have hsα : 0 ≤ (s / ℓ) ^ α := Real.rpow_nonneg (div_nonneg hs.le hℓ.le) _
    have hℓ3 : 0 ≤ ℓ / 3 := div_nonneg hℓ.le (by norm_num)
    exact calc
      C₂ * s * (s / (ℓ / 3)) ^ α * (ℓ / 3) *
          flatHalfNorm e (m - 1) (ENNReal.ofReal p) (fun x => F' (x - z))
        ≤ C₂ * s * (3 * (s / ℓ) ^ α) * (ℓ / 3) * (3 ^ d * N) := by
          refine mul_le_mul ?_ hFb hFb0
            (mul_nonneg (mul_nonneg hCs (mul_nonneg (by norm_num) hsα)) hℓ3)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCs) hℓ3
      _ = C₂ * 3 ^ d * s * (s / ℓ) ^ α * (ℓ * N) := by ring
      _ ≤ C₂ * 3 ^ d * s * (s / ℓ) ^ α * (Cq * Rhs) := by
          refine mul_le_mul_of_nonneg_left hℓN
            (mul_nonneg (mul_nonneg (mul_nonneg hC₂.le h3d.le) hs.le) hsα)
      _ = C₂ * 3 ^ d * Cq * s * (s / ℓ) ^ α * Rhs := by ring
  -- the affine function and the almost-everywhere statement
  set y0 : Vec d := fun i => (z₀ + r3c_faceBase e s) i + s / 2 with hy0
  have hy0mem : y0 ∈ axisCube (z₀ + r3c_faceBase e s) s := r3c_center_mem_cube e m hs
  have hpre := r3c_preimage_faceCube e m s
  have hmpf : MeasurePreserving (fun x : Vec d => x + z)
      (volume.restrict (axisCube (z₀ + r3c_faceBase e s) s)) (volume.restrict (r3c_faceCube e s)) := by
    rw [← hpre]
    exact (measurePreserving_add_right volume z).restrict_preimage
      (by simp only [r3c_faceCube]; exact (isOpen_axisCube _ _).measurableSet)
  have hae1 : ∀ᵐ x ∂(volume.restrict (axisCube (z₀ + r3c_faceBase e s) s)),
      ŵ (x + z) = wV.toH1Function.toFun (x + z) :=
    hmpf.quasiMeasurePreserving.ae hŵae
  refine ⟨ŵ (y0 + z) - vecDot c' (y0 - z₀), c', ?_⟩
  have hcubeM : MeasurableSet (axisCube (z₀ + r3c_faceBase e s) s) := (isOpen_axisCube _ _).measurableSet
  filter_upwards [hae1, ae_restrict_mem hcubeM] with x hx1 hxc
  have hxF : x + z ∈ r3c_faceCube e s := by
    have : x ∈ (fun x : Vec d => x + z) ⁻¹' r3c_faceCube e s := by rw [hpre]; exact hxc
    exact this
  have hyF : y0 + z ∈ r3c_faceCube e s := by
    have : y0 ∈ (fun x : Vec d => x + z) ⁻¹' r3c_faceCube e s := by rw [hpre]; exact hy0mem
    exact this
  have hηx : η x = 1 := by
    refine r3c_cutS_eq_one z₀ hlam fun i => ?_
    refine (r3c_abs_le_of_mem_cube e m hxc i).trans ?_
    rw [hlamdef]; linarith only [hsm]
  have hux : u.toFun x = ŵ (x + z) := by
    rw [hx1, hwV1 (x + z), add_sub_cancel_right, hw'f x, hηx, one_mul]
  have hdiff := hbnd (x + z) hxF (y0 + z) hyF
  have e1 : x + z - (y0 + z) = x - y0 := by abel
  have e2 : vecDot c' (x - z₀) - vecDot c' (y0 - z₀) = vecDot c' (x - y0) := by
    rw [← r3c_vecDot_sub]; congr 1; abel
  rw [e1] at hdiff
  have hux' : φ.toFun x - c * r3c_nrm e m x = ŵ (x + z) := by rw [← hux, hu1 x]
  have hRg' : (eLpNorm (fun x => φ.grad x - c • basisVec e) 2 μ).toReal = Rg := by rw [hRg, hu2f]
  have hRu' : (eLpNorm (fun x => φ.toFun x - c * r3c_nrm e m x) 2 μ).toReal = Ru := by rw [hRu, hu1f]
  rw [hRg', hRu', hux']
  refine le_trans (le_of_eq ?_) hdiff
  congr 1
  linarith only [e2]

end SuperdiffusionCLT.Section7
