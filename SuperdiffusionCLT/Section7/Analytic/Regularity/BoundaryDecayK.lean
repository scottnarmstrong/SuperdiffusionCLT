/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayJ

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# The flat boundary excess decay in `L²` form

For a weak solution on the cube with zero trace on the face `x_e = -3^m/2` (localized to the
face window), the excess over the best affine function on the face box of side `s` decays like
`(s / 3^m)^{1 - d/p}` against the `L²` excess over any affine function `ℓ₀`, the `L^p` norm of the
data and the slope term `δ |∂_e ℓ₀|`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The energy bracket of the flat decay: the data `G2`, `F2` and `δ |c|` against `Bq²`. -/
private lemma r3d_K_energy_alg {d : ℕ} {ℓ G2 F2 RG Rf Rf2 c δ Bq CE X : ℝ} (hℓ : 0 < ℓ)
    (hδ0 : 0 ≤ δ) (hCE : 0 < CE) (hRG0 : 0 ≤ RG) (hRf0 : 0 ≤ Rf) (hRf20 : 0 ≤ Rf2)
    (hRf2le : Rf2 ≤ Rf) (hG2e : G2 = ℓ ^ d * RG ^ 2) (hF2e : F2 = ℓ ^ d * Rf2 ^ 2)
    (hBq : Bq = RG + ℓ ^ 2 * Rf + ℓ * (|c| * δ))
    (hE : X ≤ CE * (G2 + ℓ ^ 4 * F2 + ℓ ^ (d + 2) * (|c| * δ) ^ 2)) :
    X ≤ CE * ℓ ^ d * Bq ^ 2 := by
  have hℓ4 : 0 ≤ ℓ ^ 4 := pow_nonneg hℓ.le 4
  have hℓ2 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hℓd0 : 0 < ℓ ^ d := pow_pos hℓ d
  refine hE.trans ?_
  have h1 : ℓ ^ 4 * F2 ≤ ℓ ^ d * (ℓ ^ 2 * Rf) ^ 2 := by
    rw [hF2e]
    have : Rf2 ^ 2 ≤ Rf ^ 2 := pow_le_pow_left₀ hRf20 hRf2le 2
    exact calc ℓ ^ 4 * (ℓ ^ d * Rf2 ^ 2) = ℓ ^ d * (ℓ ^ 4 * Rf2 ^ 2) := by ring
      _ ≤ ℓ ^ d * (ℓ ^ 4 * Rf ^ 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hℓ4) hℓd0.le
      _ = ℓ ^ d * (ℓ ^ 2 * Rf) ^ 2 := by ring
  have h2 : ℓ ^ (d + 2) * (|c| * δ) ^ 2 = ℓ ^ d * (ℓ * (|c| * δ)) ^ 2 := by rw [pow_add]; ring
  have h3 : G2 + ℓ ^ 4 * F2 + ℓ ^ (d + 2) * (|c| * δ) ^ 2 ≤ ℓ ^ d * Bq ^ 2 := by
    rw [hG2e, h2]
    have hx := mul_nonneg hRG0 (mul_nonneg hℓ2 hRf0)
    have hy := mul_nonneg hRG0 (mul_nonneg hℓ.le (mul_nonneg (abs_nonneg c) hδ0))
    have hz := mul_nonneg (mul_nonneg hℓ2 hRf0)
      (mul_nonneg hℓ.le (mul_nonneg (abs_nonneg c) hδ0))
    have e1 : Bq ^ 2 = RG ^ 2 + (ℓ ^ 2 * Rf) ^ 2 + (ℓ * (|c| * δ)) ^ 2 +
        2 * (RG * (ℓ ^ 2 * Rf)) + 2 * (RG * (ℓ * (|c| * δ))) +
        2 * ((ℓ ^ 2 * Rf) * (ℓ * (|c| * δ))) := by rw [hBq]; ring
    have h4 : 0 ≤ ℓ ^ d * (2 * (RG * (ℓ ^ 2 * Rf)) + 2 * (RG * (ℓ * (|c| * δ))) +
        2 * ((ℓ ^ 2 * Rf) * (ℓ * (|c| * δ)))) :=
      mul_nonneg hℓd0.le (add_nonneg (add_nonneg (mul_nonneg zero_le_two hx)
        (mul_nonneg zero_le_two hy)) (mul_nonneg zero_le_two hz))
    have h5 : ℓ ^ d * Bq ^ 2 = ℓ ^ d * (RG ^ 2 + (ℓ ^ 2 * Rf) ^ 2 + (ℓ * (|c| * δ)) ^ 2) +
        ℓ ^ d * (2 * (RG * (ℓ ^ 2 * Rf)) + 2 * (RG * (ℓ * (|c| * δ))) +
          2 * ((ℓ ^ 2 * Rf) * (ℓ * (|c| * δ)))) := by rw [e1]; ring
    linarith only [h1, h4, h5]
  have := mul_le_mul_of_nonneg_left h3 hCE.le
  linarith only [this]

/-- The two slope bounds from the energy bound. -/
private lemma r3d_K_slopes_alg {d : ℕ} {ℓ κ CE Bq Y' U Rg' Ru' : ℝ} (hℓ : 0 < ℓ) (hκ0 : 0 ≤ κ)
    (hBq0 : 0 ≤ Bq) (hRg0 : 0 ≤ Rg') (hRu0 : 0 ≤ Ru') (hY0 : 0 ≤ Y') (hU0 : 0 ≤ U)
    (hκ2 : κ ^ 2 = 3 ^ d * CE) (hE' : ℓ ^ 2 * Y' + U ≤ CE * ℓ ^ d * Bq ^ 2)
    (hsg : Rg' ^ 2 ≤ ((ℓ / 3) ^ d)⁻¹ * Y') (hsu : Ru' ^ 2 ≤ ((ℓ / 3) ^ d)⁻¹ * U) :
    ℓ * Rg' ≤ κ * Bq ∧ Ru' ≤ κ * Bq := by
  have hℓ2 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hℓ3 : 0 ≤ ℓ / 3 := div_nonneg hℓ.le (by norm_num)
  have hcoef : ((ℓ / 3) ^ d)⁻¹ * ℓ ^ d = 3 ^ d := by
    rw [div_pow, inv_div]; exact div_mul_cancel₀ _ (pow_ne_zero d hℓ.ne')
  have hkB : 0 ≤ κ * Bq := mul_nonneg hκ0 hBq0
  have hiq : 0 ≤ ((ℓ / 3) ^ d)⁻¹ := inv_nonneg.2 (pow_nonneg hℓ3 d)
  have h8 : ((ℓ / 3) ^ d)⁻¹ * (CE * ℓ ^ d * Bq ^ 2) = (κ * Bq) ^ 2 := by
    rw [mul_pow, hκ2]
    exact calc ((ℓ / 3) ^ d)⁻¹ * (CE * ℓ ^ d * Bq ^ 2) =
          (((ℓ / 3) ^ d)⁻¹ * ℓ ^ d) * (CE * Bq ^ 2) := by ring
      _ = _ := by rw [hcoef]; ring
  constructor
  · refine r3d_sq_to_le (mul_nonneg hℓ.le hRg0) hkB ?_
    have h5 : ℓ ^ 2 * Rg' ^ 2 ≤ ℓ ^ 2 * (((ℓ / 3) ^ d)⁻¹ * Y') :=
      mul_le_mul_of_nonneg_left hsg hℓ2
    have h6 : ℓ ^ 2 * (((ℓ / 3) ^ d)⁻¹ * Y') = ((ℓ / 3) ^ d)⁻¹ * (ℓ ^ 2 * Y') := by ring
    have h7 : ((ℓ / 3) ^ d)⁻¹ * (ℓ ^ 2 * Y') ≤ ((ℓ / 3) ^ d)⁻¹ * (CE * ℓ ^ d * Bq ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hE', hU0]) hiq
    exact calc (ℓ * Rg') ^ 2 = ℓ ^ 2 * Rg' ^ 2 := by ring
      _ ≤ _ := by linarith only [h5, h6, h7, h8]
  · refine r3d_sq_to_le hRu0 hkB ?_
    have h0 : 0 ≤ ℓ ^ 2 * Y' := mul_nonneg hℓ2 hY0
    have h7 : ((ℓ / 3) ^ d)⁻¹ * U ≤ ((ℓ / 3) ^ d)⁻¹ * (CE * ℓ ^ d * Bq ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hE', h0]) hiq
    linarith only [hsu, h7, h8]

/-- The bracket of the flat decay. -/
private lemma r3d_K_bracket_alg {d : ℕ} {ℓ κ Bq RG Rf Rg' Ru' Rf' δ c B1 : ℝ} (hℓ : 0 < ℓ)
    (hδ0 : 0 ≤ δ) (hRG0 : 0 ≤ RG) (hRf0 : 0 ≤ Rf)
    (hBq : Bq = RG + ℓ ^ 2 * Rf + ℓ * (|c| * δ)) (hB1 : B1 = ℓ⁻¹ * RG + ℓ * Rf + δ * |c|)
    (hRgle : ℓ * Rg' ≤ κ * Bq) (hRule : Ru' ≤ κ * Bq) (hRf'le : Rf' ≤ 3 ^ d * Rf) :
    Rg' + (ℓ / 3)⁻¹ * Ru' + ℓ / 3 * Rf' + δ * |c| ≤ (4 * κ + 3 ^ d + 1) * B1 := by
  have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.2 hℓ.le
  have hl : ℓ⁻¹ * ℓ = 1 := inv_mul_cancel₀ hℓ.ne'
  have h3d : (0 : ℝ) ≤ 3 ^ d := pow_nonneg (by norm_num) d
  have hℓ3 : 0 ≤ ℓ / 3 := div_nonneg hℓ.le (by norm_num)
  have e1 : ℓ⁻¹ * Bq = ℓ⁻¹ * RG + ℓ * Rf + |c| * δ := by
    rw [hBq]
    linear_combination (ℓ * Rf + |c| * δ) * hl
  have h1' : Rg' ≤ κ * (ℓ⁻¹ * Bq) := by
    have := mul_le_mul_of_nonneg_left hRgle (inv_nonneg.2 hℓ.le)
    exact calc Rg' = ℓ⁻¹ * (ℓ * Rg') := by rw [← mul_assoc, hl, one_mul]
      _ ≤ ℓ⁻¹ * (κ * Bq) := this
      _ = κ * (ℓ⁻¹ * Bq) := by ring
  have h2' : (ℓ / 3)⁻¹ * Ru' ≤ 3 * κ * (ℓ⁻¹ * Bq) := by
    have : (ℓ / 3)⁻¹ = 3 * ℓ⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [this]
    exact calc 3 * ℓ⁻¹ * Ru' ≤ 3 * ℓ⁻¹ * (κ * Bq) :=
          mul_le_mul_of_nonneg_left hRule (mul_nonneg (by norm_num) hℓi)
      _ = 3 * κ * (ℓ⁻¹ * Bq) := by ring
  have h3' : ℓ / 3 * Rf' ≤ 3 ^ d * (ℓ * Rf) := by
    exact calc ℓ / 3 * Rf' ≤ ℓ / 3 * (3 ^ d * Rf) := mul_le_mul_of_nonneg_left hRf'le hℓ3
      _ ≤ 3 ^ d * (ℓ * Rf) := by
          have : 0 ≤ (3 : ℝ) ^ d * (ℓ * Rf) := mul_nonneg h3d (mul_nonneg hℓ.le hRf0)
          have e3 : ℓ / 3 * (3 ^ d * Rf) = 3 ^ d * (ℓ * Rf) / 3 := by ring
          linarith only [this, e3]
  have hB1' : ℓ⁻¹ * Bq = B1 := by rw [e1, hB1]; ring
  rw [hB1'] at h1' h2'
  have hlRf : ℓ * Rf ≤ B1 := by
    rw [hB1]
    have : 0 ≤ ℓ⁻¹ * RG := mul_nonneg hℓi hRG0
    have : 0 ≤ δ * |c| := mul_nonneg hδ0 (abs_nonneg c)
    linarith only [‹0 ≤ ℓ⁻¹ * RG›, this]
  have hdc : δ * |c| ≤ B1 := by
    rw [hB1]
    have : 0 ≤ ℓ⁻¹ * RG := mul_nonneg hℓi hRG0
    have : 0 ≤ ℓ * Rf := mul_nonneg hℓ.le hRf0
    linarith only [‹0 ≤ ℓ⁻¹ * RG›, this]
  have h3'' : 3 ^ d * (ℓ * Rf) ≤ 3 ^ d * B1 := mul_le_mul_of_nonneg_left hlRf h3d
  linarith only [h1', h2', h3', h3'', hdc]

theorem r3d_flat_decay [NeZero d] (hd : 2 ≤ d) (e : Fin d) {p : ℝ} (hp : (d : ℝ) < p) :
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
          LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) φ.toFun →
          ∀ (a₀ : ℝ) (b₀ : Vec d) (s : ℝ), 0 < s → s ≤ (3 : ℝ) ^ m / 36 →
            ∃ (a : ℝ) (b : Vec d),
              ∀ᵐ x ∂(volume.restrict (axisCube (r3c_z0 e m + r3c_faceBase e s) s)),
                |φ.toFun x - (a + vecDot b (x - r3c_z0 e m))| ≤
                  C * s * (s / (3 : ℝ) ^ m) ^ (1 - (d : ℝ) / p) *
                    (((3 : ℝ) ^ m)⁻¹ * (eLpNorm (fun x => φ.toFun x - (a₀ + vecDot b₀ (x - r3c_z0 e m))) 2
                        (normalizedCubeMeasure (originCube d m))).toReal +
                      (3 : ℝ) ^ m * (eLpNorm f (ENNReal.ofReal p)
                        (normalizedCubeMeasure (originCube d m))).toReal + δ * |b₀ e|) := by
  classical
  obtain ⟨εN, CN, hεN, hCN, HN⟩ := r3c_flat_cutoff_decay hd e hp
  obtain ⟨εE, CE, hεE, hCE, HE⟩ := r3d_energy_L2 hd e
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hp2 : (2 : ℝ) < p := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this, hp]
  set κ : ℝ := Real.sqrt (3 ^ d * CE) with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have h3d : (0 : ℝ) ≤ 3 ^ d := pow_nonneg (by norm_num) d
  have hκ2 : κ ^ 2 = 3 ^ d * CE := Real.sq_sqrt (mul_nonneg h3d hCE.le)
  refine ⟨min εN εE, 3 * CN * (4 * κ + 3 ^ d + 1), lt_min hεN hεE,
    mul_pos (mul_pos (by norm_num) hCN)
      (add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg (by norm_num) hκ0) h3d) one_pos), ?_⟩
  intro m A K δ hAs hδ0 hδε hAδ hAK hKℓ f hf φ hφ hZ a₀ b₀ s hs hsm
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓd
  have hℓ : 0 < ℓ := zpow_pos (by norm_num) m
  have hℓ2 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hℓ4 : 0 ≤ ℓ ^ 4 := pow_nonneg hℓ.le 4
  have hℓi : 0 ≤ ℓ⁻¹ := inv_nonneg.2 hℓ.le
  have hl : ℓ⁻¹ * ℓ = 1 := inv_mul_cancel₀ hℓ.ne'
  have hℓ3 : 0 ≤ ℓ / 3 := div_nonneg hℓ.le (by norm_num)
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith only [hp2])
  have hPt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpge : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp2.le
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (r3d_volume_openCube_ne_top m)⟩
  have hfΩ : MemLp f (ENNReal.ofReal p) (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_restrict_of_normalized _ hf
  have hf2Ω : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) := hfΩ.mono_exponent hpge
  obtain ⟨u, hu1, hu2⟩ := r3c_exists_sub_nrm (originCube d m) e m (b₀ e) φ
  have hu1f : ∀ x, u.toFun x = φ.toFun x - b₀ e * r3c_nrm e m x := hu1
  have hE := HE m A δ (b₀ e) a₀ b₀ hAs hδ0 (hδε.trans (min_le_right _ _)) hAδ f hf2Ω φ u hφ hZ hu1f hu2
  rw [← hℓd] at hE
  set Y' : ℝ := ∫ x in r3d_Ebox e m (ℓ / 3), vecNormSq (u.grad x) with hY'
  set U : ℝ := ∫ x in openCubeSet (originCube d m), u.toFun x ^ 2 with hU
  set G2 : ℝ := ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a₀ b₀ x) ^ 2 with hG2
  set F2 : ℝ := ∫ x in openCubeSet (originCube d m), f x ^ 2 with hF2
  have hY0 : 0 ≤ Y' := integral_nonneg fun x => vecNormSq_nonneg _
  have hU0 : 0 ≤ U := integral_nonneg fun x => sq_nonneg _
  have hgfun : (fun x => φ.toFun x - (a₀ + vecDot b₀ (x - r3c_z0 e m))) =
      fun x => u.toFun x - r3d_m e a₀ b₀ x := funext fun x => (r3d_u_sub_m e m a₀ b₀ hu1f x).symm
  -- `m` is square integrable on the cube
  have hQm : MeasurableSet (openCubeSet (originCube d m)) := (isOpen_openCubeSet _).measurableSet
  have hmc : Continuous (r3d_m e a₀ b₀) := r3d_m_continuous e a₀ b₀
  have hm2 : MemLp (r3d_m e a₀ b₀) 2 (volume.restrict (openCubeSet (originCube d m))) :=
    MemLp.of_bound hmc.aestronglyMeasurable (|a₀| + ℓ / 2 * ∑ k ∈ Finset.univ.erase e, |b₀ k|) (by
      filter_upwards [ae_restrict_mem hQm] with x hx
      rw [Real.norm_eq_abs]
      exact r3d_m_abs_le e a₀ b₀ (L := ℓ / 2) (fun i => by
        have := (hc_mem_openCubeSet_originCube_iff m x).1 hx i
        rw [abs_le]; exact ⟨this.1.le, this.2.le⟩))
  have hgΩ : MemLp (fun x => u.toFun x - r3d_m e a₀ b₀ x) 2
      (volume.restrict (openCubeSet (originCube d m))) := u.memL2.sub hm2
  have hgQ : MemLp (fun x => u.toFun x - r3d_m e a₀ b₀ x) 2
      (normalizedCubeMeasure (originCube d m)) := memLp_normalized_of_restrict _ hgΩ
  have hf2Q : MemLp f 2 (normalizedCubeMeasure (originCube d m)) :=
    memLp_normalized_of_restrict _ hf2Ω
  set RG : ℝ := (eLpNorm (fun x => φ.toFun x - (a₀ + vecDot b₀ (x - r3c_z0 e m))) 2
    (normalizedCubeMeasure (originCube d m))).toReal with hRG
  set Rf : ℝ := (eLpNorm f (ENNReal.ofReal p) (normalizedCubeMeasure (originCube d m))).toReal with hRf
  set Rf2 : ℝ := (eLpNorm f 2 (normalizedCubeMeasure (originCube d m))).toReal with hRf2
  have hRG0 : 0 ≤ RG := ENNReal.toReal_nonneg
  have hRf0 : 0 ≤ Rf := ENNReal.toReal_nonneg
  have hRf20 : 0 ≤ Rf2 := ENNReal.toReal_nonneg
  have hRGsq : RG ^ 2 = (ℓ ^ d)⁻¹ * G2 := by
    have := r3d_norm_sq_normalized m hgQ
    rw [hRG, hgfun]
    exact this
  have hRf2sq : Rf2 ^ 2 = (ℓ ^ d)⁻¹ * F2 := r3d_norm_sq_normalized m hf2Q
  have hRf2le : Rf2 ≤ Rf :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top (p12_eLpNorm_mono_exp (originCube d m) hpge)
  have hℓd0 : 0 < ℓ ^ d := pow_pos hℓ d
  have hG2e : G2 = ℓ ^ d * RG ^ 2 := by rw [hRGsq, ← mul_assoc, mul_inv_cancel₀ hℓd0.ne', one_mul]
  have hF2e : F2 = ℓ ^ d * Rf2 ^ 2 := by rw [hRf2sq, ← mul_assoc, mul_inv_cancel₀ hℓd0.ne', one_mul]
  set c : ℝ := b₀ e with hc
  set Bq : ℝ := RG + ℓ ^ 2 * Rf + ℓ * (|c| * δ) with hBq
  have hBq0 : 0 ≤ Bq := by
    rw [hBq]
    exact add_nonneg (add_nonneg hRG0 (mul_nonneg hℓ2 hRf0))
      (mul_nonneg hℓ.le (mul_nonneg (abs_nonneg c) hδ0))
  have hE' : ℓ ^ 2 * Y' + U ≤ CE * ℓ ^ d * Bq ^ 2 :=
    r3d_K_energy_alg hℓ hδ0 hCE hRG0 hRf0 hRf20 hRf2le hG2e hF2e hBq hE
  -- the sub-cube problem
  obtain ⟨φ'', h1, h2, h3, h4⟩ := r3d_subcube_data e m hφ hZ
  have hVU := r3d_subV_subset e m
  have hK0 : 0 ≤ K := by
    have i0 : Fin d := ⟨0, by omega⟩
    exact (abs_nonneg _).trans (hAK 0 (r3c_zero_mem_cube m) ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hmemV : ∀ x ∈ openCubeSet (originCube d (m - 1)), x - r3d_zT e m ∈ openCubeSet (originCube d m) :=
    fun x hx => hVU (by
      show x - r3d_zT e m + r3d_zT e m ∈ openCubeSet (originCube d (m - 1))
      rwa [sub_add_cancel])
  have hAs'' : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => (fun y => A (y - r3d_zT e m)) x i j) := fun i j =>
    (hAs i j).comp (contDiff_id.sub contDiff_const)
  have hAδ'' : ∀ x ∈ openCubeSet (originCube d (m - 1)), ∀ i j,
      |(fun y => A (y - r3d_zT e m)) x i j - (1 : Mat d) i j| ≤ δ := fun x hx i j =>
    hAδ _ (hmemV x hx) i j
  have hAK'' : ∀ x ∈ openCubeSet (originCube d (m - 1)), ∀ i j k,
      |fderiv ℝ (fun y => (fun y => A (y - r3d_zT e m)) y i j) x (basisVec k)| ≤ K := by
    intro x hx i j k
    have : fderiv ℝ (fun y => A (y - r3d_zT e m) i j) x = fderiv ℝ (fun y => A y i j) (x - r3d_zT e m) := by
      have h := fderiv_comp_add_right (𝕜 := ℝ) (f := fun w => A w i j) (x := x) (-r3d_zT e m)
      simpa only [sub_eq_add_neg] using h
    simp only
    rw [this]
    exact hAK _ (hmemV x hx) i j k
  have hKℓ'' : K * (3 : ℝ) ^ (m - 1) ≤ δ := by
    rw [r3d_pow_pred]
    refine le_trans ?_ hKℓ
    exact mul_le_mul_of_nonneg_left (by linarith only [hℓ]) hK0
  have hf'' := r3d_cube_translate_norm e m hP1 hPt hf
  have hsm' : s ≤ (3 : ℝ) ^ (m - 1) / 12 := by
    rw [r3d_pow_pred]; linarith only [hsm]
  obtain ⟨a, b, hae⟩ := HN (m - 1) (fun y => A (y - r3d_zT e m)) K δ hAs'' hδ0
    (hδε.trans (min_le_left _ _)) hAδ'' hAK'' hKℓ'' (fun y => f (y - r3d_zT e m)) hf''.1 φ'' h3 h4
    c s hs hsm'
  -- bounds for the sub-cube norms
  obtain ⟨hsg, hsu⟩ := r3d_sub_norms e m u
  have hRg : (fun y => φ''.grad y - c • basisVec e) = fun y => u.grad (y - r3d_zT e m) :=
    funext fun y => by rw [h2 y, hu2 (y - r3d_zT e m)]
  have hRu : (fun y => φ''.toFun y - c * r3c_nrm e (m - 1) y) = fun y => u.toFun (y - r3d_zT e m) :=
    funext fun y => by
      rw [h1 y, hu1f (y - r3d_zT e m)]
      have := r3d_nrm_sub e m (y - r3d_zT e m)
      rw [sub_add_cancel] at this
      rw [this]
  rw [hRg, hRu] at hae
  set Rg' : ℝ := (eLpNorm (fun y => u.grad (y - r3d_zT e m)) 2
    (normalizedCubeMeasure (originCube d (m - 1)))).toReal with hRg'
  set Ru' : ℝ := (eLpNorm (fun y => u.toFun (y - r3d_zT e m)) 2
    (normalizedCubeMeasure (originCube d (m - 1)))).toReal with hRu'
  set Rf' : ℝ := (eLpNorm (fun y => f (y - r3d_zT e m)) (ENNReal.ofReal p)
    (normalizedCubeMeasure (originCube d (m - 1)))).toReal with hRf'
  have hRg0 : 0 ≤ Rg' := ENNReal.toReal_nonneg
  have hRu0 : 0 ≤ Ru' := ENNReal.toReal_nonneg
  have hRf'0 : 0 ≤ Rf' := ENNReal.toReal_nonneg
  have hRf'le : Rf' ≤ 3 ^ d * Rf := hf''.2
  have hcoef : ((ℓ / 3) ^ d)⁻¹ * ℓ ^ d = 3 ^ d := by
    rw [div_pow, inv_div]; exact div_mul_cancel₀ _ (pow_ne_zero d hℓ.ne')
  obtain ⟨hRgle, hRule⟩ := r3d_K_slopes_alg hℓ hκ0 hBq0 hRg0 hRu0 hY0 hU0 hκ2 hE' hsg hsu
  -- the bracket
  have hpm : (3 : ℝ) ^ (m - 1) = ℓ / 3 := r3d_pow_pred m
  set B1 : ℝ := ℓ⁻¹ * RG + ℓ * Rf + δ * |c| with hB1
  have hB10 : 0 ≤ B1 := by
    rw [hB1]
    exact add_nonneg (add_nonneg (mul_nonneg hℓi hRG0) (mul_nonneg hℓ.le hRf0))
      (mul_nonneg hδ0 (abs_nonneg c))
  have hbr : Rg' + (3 ^ (m - 1) : ℝ)⁻¹ * Ru' + 3 ^ (m - 1) * Rf' + δ * |c| ≤ (4 * κ + 3 ^ d + 1) * B1 := by
    rw [hpm]
    exact r3d_K_bracket_alg hℓ hδ0 hRG0 hRf0 hBq hB1 hRgle hRule hRf'le
  -- transfer back to the original coordinates
  set α : ℝ := 1 - (d : ℝ) / p with hα
  have hα1 : α ≤ 1 := by
    have : 0 ≤ (d : ℝ) / p :=
      div_nonneg (Nat.cast_nonneg d) (by linarith only [hp2])
    linarith only [this]
  have hpow : (s / (ℓ / 3)) ^ α ≤ 3 * (s / ℓ) ^ α := by
    have e1 : s / (ℓ / 3) = 3 * (s / ℓ) := by
      rw [div_div_eq_mul_div]; ring
    rw [e1, Real.mul_rpow (by norm_num) (div_nonneg hs.le hℓ.le)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (div_nonneg hs.le hℓ.le) _)
    exact calc (3 : ℝ) ^ α ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      _ = 3 := Real.rpow_one 3
  have hpre := r3d_preimage_faceBox e m s
  have hmpf : MeasurePreserving (fun x : Vec d => x + r3d_zT e m)
      (volume.restrict (axisCube (r3c_z0 e m + r3c_faceBase e s) s))
      (volume.restrict (axisCube (r3c_z0 e (m - 1) + r3c_faceBase e s) s)) := by
    rw [← hpre]
    exact (measurePreserving_add_right volume (r3d_zT e m)).restrict_preimage
      (isOpen_axisCube _ _).measurableSet
  have hae' := hmpf.quasiMeasurePreserving.ae hae
  refine ⟨a, b + c • (basisVec e : Vec d), ?_⟩
  filter_upwards [hae'] with x hx
  have hz0 : x + r3d_zT e m - r3c_z0 e (m - 1) = x - r3c_z0 e m := by
    rw [← r3d_z0_sub_zT e m]; abel
  rw [h1 (x + r3d_zT e m), add_sub_cancel_right, r3d_nrm_sub, hz0, hpm] at hx
  have hLHS : φ.toFun x - (a + vecDot (b + c • (basisVec e : Vec d)) (x - r3c_z0 e m)) =
      φ.toFun x - c * r3c_nrm e m x - (a + vecDot b (x - r3c_z0 e m)) := by
    rw [r3d_affine_merge]; ring
  rw [hLHS]
  refine hx.trans ?_
  have hTnn : 0 ≤ Rg' + (ℓ / 3)⁻¹ * Ru' + ℓ / 3 * Rf' + δ * |c| :=
    add_nonneg (add_nonneg (add_nonneg hRg0 (mul_nonneg (inv_nonneg.2 hℓ3) hRu0))
      (mul_nonneg hℓ3 hRf'0)) (mul_nonneg hδ0 (abs_nonneg c))
  have hCs : 0 ≤ CN * s := mul_nonneg hCN.le hs.le
  have hstep : CN * s * (s / (ℓ / 3)) ^ α * (Rg' + (ℓ / 3)⁻¹ * Ru' + ℓ / 3 * Rf' + δ * |c|) ≤
      CN * s * (3 * (s / ℓ) ^ α) * ((4 * κ + 3 ^ d + 1) * B1) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hCs) ?_ hTnn
      (mul_nonneg hCs (mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg hs.le hℓ.le) _)))
    rw [hpm] at hbr
    exact hbr
  have hrearr : CN * s * (3 * (s / ℓ) ^ α) * ((4 * κ + 3 ^ d + 1) * B1) =
      3 * CN * (4 * κ + 3 ^ d + 1) * s * (s / ℓ) ^ α * B1 := by ring
  refine hstep.trans_eq ?_
  rw [hrearr, hB1, hc]

end SuperdiffusionCLT.Section7
