/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryS
public import SuperdiffusionCLT.Section7.Lipschitz.CarriersS
public import SuperdiffusionCLT.Section7.Lipschitz.WitnessBdryB
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarmC

/-!
# From the deterministic boundary core to the sup-norm block

The deterministic inequality, stated with integrals normalized by `|□_m|`, implies the block
`LipCaccBdryS` (norms normalized by the measures of the sets `□_m ∩ W`, `□_{m-1} ∩ W`) when
`|□_{m-1} ∩ W| ≥ c |□_m|`.  The cases of a right-hand side in `L²`, measurable but not in `L²`, and not
almost everywhere measurable are treated separately.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2w_real {ν S C Cd cden Vq vD vD' X' Xw Xf L ℓ2 G1 G2 e2 : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (hCd : 0 ≤ Cd) (hcden : 0 < cden) (hVq : 0 < Vq) (hvD : vD ≤ Vq) (hvD0 : 0 < vD)
    (hden : cden * Vq ≤ vD') (hXn : 0 ≤ X') (hXw : 0 ≤ Xw) (hXf : 0 ≤ Xf) (hL : 0 < L)
    (hcore : ν * X' ≤ Cd * Vq * (S * L⁻¹ ^ 2 * (Vq⁻¹ * Xw) + S⁻¹ * L ^ 2 * (Vq⁻¹ * Xf) + S * G1 ^ 2 +
      S * ℓ2 * G2 ^ 2))
    (hC1 : Cd / cden ≤ C) (hC2 : Cd / cden * (S * ℓ2) ≤ e2) :
    ν * (vD'⁻¹ * X') ≤ C * S * L⁻¹ ^ 2 * (vD⁻¹ * Xw) + C * S⁻¹ * L ^ 2 * (vD⁻¹ * Xf) + C * S * G1 ^ 2 +
      e2 * G2 ^ 2 := by
  have hvD'0 : 0 < vD' := lt_of_lt_of_le (by positivity) hden
  have hinv : vD'⁻¹ ≤ (cden * Vq)⁻¹ := by
    rw [inv_le_inv₀ hvD'0 (by positivity)]; exact hden
  have hVv : Vq⁻¹ ≤ vD⁻¹ := by rw [inv_le_inv₀ hVq hvD0]; exact hvD
  have hCn : 0 ≤ Cd / cden := by positivity
  have h1 : ν * (vD'⁻¹ * X') ≤ ν * ((cden * Vq)⁻¹ * X') := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv hXn) hν.le
  have h2 : ν * ((cden * Vq)⁻¹ * X') = (cden * Vq)⁻¹ * (ν * X') := by ring
  have h3 : (cden * Vq)⁻¹ * (ν * X') ≤ (cden * Vq)⁻¹ * (Cd * Vq * (S * L⁻¹ ^ 2 * (Vq⁻¹ * Xw) +
      S⁻¹ * L ^ 2 * (Vq⁻¹ * Xf) + S * G1 ^ 2 + S * ℓ2 * G2 ^ 2)) :=
    mul_le_mul_of_nonneg_left hcore (by positivity)
  have h4 : (cden * Vq)⁻¹ * (Cd * Vq * (S * L⁻¹ ^ 2 * (Vq⁻¹ * Xw) + S⁻¹ * L ^ 2 * (Vq⁻¹ * Xf) +
      S * G1 ^ 2 + S * ℓ2 * G2 ^ 2)) = (Cd / cden) * (S * L⁻¹ ^ 2 * (Vq⁻¹ * Xw) +
      S⁻¹ * L ^ 2 * (Vq⁻¹ * Xf) + S * G1 ^ 2 + S * ℓ2 * G2 ^ 2) := by
    field_simp
  have hw : S * L⁻¹ ^ 2 * (Vq⁻¹ * Xw) ≤ S * L⁻¹ ^ 2 * (vD⁻¹ * Xw) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hVv hXw) (by positivity)
  have hf : S⁻¹ * L ^ 2 * (Vq⁻¹ * Xf) ≤ S⁻¹ * L ^ 2 * (vD⁻¹ * Xf) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hVv hXf) (by positivity)
  have hsum : (Cd / cden) * (S * L⁻¹ ^ 2 * (Vq⁻¹ * Xw) + S⁻¹ * L ^ 2 * (Vq⁻¹ * Xf) + S * G1 ^ 2 +
      S * ℓ2 * G2 ^ 2) ≤ (Cd / cden) * (S * L⁻¹ ^ 2 * (vD⁻¹ * Xw) + S⁻¹ * L ^ 2 * (vD⁻¹ * Xf) +
      S * G1 ^ 2 + S * ℓ2 * G2 ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hCn
    linarith only [hw, hf]
  have hCw : Cd / cden * (S * L⁻¹ ^ 2 * (vD⁻¹ * Xw)) ≤ C * S * L⁻¹ ^ 2 * (vD⁻¹ * Xw) := by
    have := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ S * L⁻¹ ^ 2 * (vD⁻¹ * Xw))
    linarith only [this]
  have hCf : Cd / cden * (S⁻¹ * L ^ 2 * (vD⁻¹ * Xf)) ≤ C * S⁻¹ * L ^ 2 * (vD⁻¹ * Xf) := by
    have := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ S⁻¹ * L ^ 2 * (vD⁻¹ * Xf))
    linarith only [this]
  have hCg : Cd / cden * (S * G1 ^ 2) ≤ C * S * G1 ^ 2 := by
    have := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ S * G1 ^ 2)
    linarith only [this]
  have hCe : Cd / cden * (S * ℓ2 * G2 ^ 2) ≤ e2 * G2 ^ 2 := by
    have := mul_le_mul_of_nonneg_right hC2 (sq_nonneg G2)
    linarith only [this]
  have e5 : (Cd / cden) * (S * L⁻¹ ^ 2 * (vD⁻¹ * Xw) + S⁻¹ * L ^ 2 * (vD⁻¹ * Xf) + S * G1 ^ 2 +
      S * ℓ2 * G2 ^ 2) = Cd / cden * (S * L⁻¹ ^ 2 * (vD⁻¹ * Xw)) +
        Cd / cden * (S⁻¹ * L ^ 2 * (vD⁻¹ * Xf)) + Cd / cden * (S * G1 ^ 2) +
          Cd / cden * (S * ℓ2 * G2 ^ 2) := by ring
  linarith only [h1, h2, h3, h4, hsum, e5, hCw, hCf, hCg, hCe]

theorem ca2w_lip_of_core [NeZero d] {a A : CoeffField d} {ν S C E Cd cden lam Lam ℓ2 : ℝ} (m : ℕ)
    {W : Set (Vec d)} (hWo : IsOpen W) (hν : 0 < ν) (hS : 0 < S) (hC : 0 < C) (hCd : 0 ≤ Cd)
    (hcden : 0 < cden)
    (hEllA : IsEllipticFieldOn lam Lam (openCubeSet (originCube d (m : ℤ)) ∩ W) A)
    (hflux : ∀ u : H1Function (openCubeSet (originCube d (m : ℤ)) ∩ W),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ)) ∩ W) (fun x => matVecMul (a x) (u.grad x)))
    (hbridge : ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)) ∩ W)) (f : Vec d → ℝ),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ)) ∩ W) (fun x => matVecMul (a x) (u.grad x)) →
      IsWeakSolutionOn a (openCubeSet (originCube d (m : ℤ)) ∩ W) u f (fun _ => 0) →
      IsWeakSolutionOn A (openCubeSet (originCube d (m : ℤ)) ∩ W) u f (fun _ => 0))
    (hcore : ∀ (u : H1Function (openCubeSet (originCube d (m : ℤ)) ∩ W)) (f : Vec d → ℝ)
      (γ : Vec d → ℝ), ContDiff ℝ 2 γ → ∀ (G1 G2 : ℝ), 0 ≤ G1 → 0 ≤ G2 →
      (∀ x ∈ openCubeSet (originCube d (m : ℤ)) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1) →
      (∀ x ∈ openCubeSet (originCube d (m : ℤ)) ∩ W, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) →
      MemLp f 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W)) →
      IsWeakSolutionOn A (openCubeSet (originCube d (m : ℤ)) ∩ W) u f (fun _ => 0) →
      LocalizedZeroTraceFunctionOn (openCubeSet (originCube d (m : ℤ)) ∩ W)
        (openCubeSet (originCube d (m : ℤ))) (fun x => u.toFun x - γ x) →
      ν * ∫ x in openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W, vecNormSq (u.grad x) ≤
        Cd * cubeVolume (originCube d (m : ℤ)) *
          (S * (((3 : ℝ) ^ m)⁻¹) ^ 2 * ((cubeVolume (originCube d (m : ℤ)))⁻¹ *
              ∫ x in openCubeSet (originCube d (m : ℤ)) ∩ W, (u.toFun x - γ x) ^ 2) +
            S⁻¹ * ((3 : ℝ) ^ m) ^ 2 * ((cubeVolume (originCube d (m : ℤ)))⁻¹ *
              ∫ x in openCubeSet (originCube d (m : ℤ)) ∩ W, f x ^ 2) +
            S * G1 ^ 2 + S * ℓ2 * G2 ^ 2))
    (hden : cden * cubeVolume (originCube d (m : ℤ)) ≤
      (volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W)).toReal)
    (hC1 : Cd / cden ≤ C)
    (hC2 : Cd / cden * (S * ℓ2) ≤ C * ((m : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ m) ^ 2) :
    LipCaccBdryS a ν S C E W 0 m := by
  classical
  unfold LipCaccBdryS
  rw [rc_shiftCube_zero, rc_shiftCube_zero]
  intro f γ G1 G2 u hγ hG1 hG2 hb1 hb2 hu hZ
  have hDo : IsOpen (openCubeSet (originCube d (m : ℤ)) ∩ W) := (isOpen_openCubeSet _).inter hWo
  have hDb : Bornology.IsBounded (openCubeSet (originCube d (m : ℤ)) ∩ W) :=
    (isBounded_openCubeSet (originCube d (m : ℤ))).subset Set.inter_subset_left
  have hD'sub : openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W ⊆ openCubeSet (originCube d (m : ℤ)) ∩ W :=
    Set.inter_subset_inter_left _ (ca1_openCube_pred_subset (m : ℤ))
  have hvD'fin : volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W) ≠ ⊤ :=
    ((isBounded_openCubeSet (originCube d ((m : ℤ) - 1))).subset Set.inter_subset_left).measure_lt_top.ne
  have hV0 : 0 < cubeVolume (originCube d (m : ℤ)) := cubeVolume_pos _
  have hvD'pos : 0 < (volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W)).toReal :=
    lt_of_lt_of_le (by positivity) hden
  have hvD'0 : volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W) ≠ 0 := by
    intro h0; rw [h0] at hvD'pos; simp at hvD'pos
  have hvDfin : volume (openCubeSet (originCube d (m : ℤ)) ∩ W) ≠ ⊤ := hDb.measure_lt_top.ne
  have hvD0 : volume (openCubeSet (originCube d (m : ℤ)) ∩ W) ≠ 0 := by
    intro h0
    exact hvD'0 (measure_mono_null hD'sub h0)
  have hvDpos : 0 < (volume (openCubeSet (originCube d (m : ℤ)) ∩ W)).toReal :=
    ENNReal.toReal_pos hvD0 hvDfin
  have hvDle : (volume (openCubeSet (originCube d (m : ℤ)) ∩ W)).toReal ≤
      cubeVolume (originCube d (m : ℤ)) := by
    have h0 : (volume (openCubeSet (originCube d (m : ℤ)))).toReal = cubeVolume (originCube d (m : ℤ)) :=
      ca2_volume_openCube_toReal _
    rw [← h0]
    exact ENNReal.toReal_mono (isBounded_openCubeSet (originCube d (m : ℤ))).measure_lt_top.ne
      (measure_mono Set.inter_subset_left)
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hwL : MemLp (fun x => u.toFun x - γ x) 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W)) :=
    u.memL2.sub (lip_witness_bdry_memLp_cont hDo hDb hγ1.continuous)
  have hgL : MemLp (fun x => eucNorm (u.grad x)) 2
      (volume.restrict (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W)) :=
    (memLp_eucNorm_grad u).mono_measure (Measure.restrict_mono hD'sub le_rfl)
  have hL : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDb.measure_lt_top⟩
  -- the key estimate for `f` in `L²`
  have key : ∀ f' : Vec d → ℝ, MemLp f' 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W)) →
      IsWeakSolutionOn A (openCubeSet (originCube d (m : ℤ)) ∩ W) u f' (fun _ => 0) →
      ENNReal.ofReal ν * lpBar (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W) 2
          (fun x => eucNorm (u.grad x)) ^ 2 ≤
        ENNReal.ofReal (C * S * (((3 : ℝ)⁻¹) ^ m) ^ 2) *
            lpBar (openCubeSet (originCube d (m : ℤ)) ∩ W) 2 (fun x => u.toFun x - γ x) ^ 2 +
          ENNReal.ofReal (C * S⁻¹ * ((3 : ℝ) ^ m) ^ 2) *
            lpBar (openCubeSet (originCube d (m : ℤ)) ∩ W) 2 f' ^ 2 +
          ENNReal.ofReal (C * S * G1 ^ 2) +
          ENNReal.ofReal (C * ((m : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ m) ^ 2 * G2 ^ 2) := by
    intro f' hf' hu'
    have hc := hcore u f' γ hγ G1 G2 hG1 hG2 hb1 hb2 hf' hu' hZ
    have hX' : ∫ x in openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W, eucNorm (u.grad x) ^ 2 =
        ∫ x in openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W, vecNormSq (u.grad x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      unfold eucNorm
      exact Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    have hreal := ca2w_real (ν := ν) (S := S) (C := C) (Cd := Cd) (cden := cden)
      (Vq := cubeVolume (originCube d (m : ℤ)))
      (vD := (volume (openCubeSet (originCube d (m : ℤ)) ∩ W)).toReal)
      (vD' := (volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W)).toReal)
      (X' := ∫ x in openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W, vecNormSq (u.grad x))
      (Xw := ∫ x in openCubeSet (originCube d (m : ℤ)) ∩ W, (u.toFun x - γ x) ^ 2)
      (Xf := ∫ x in openCubeSet (originCube d (m : ℤ)) ∩ W, f' x ^ 2) (L := (3 : ℝ) ^ m)
      (ℓ2 := ℓ2) (G1 := G1) (G2 := G2) (e2 := C * ((m : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ m) ^ 2) hν hS hCd hcden
      hV0 hvDle hvDpos hden (integral_nonneg fun x => by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _) hL hc hC1 hC2
    rw [lip_witness_bdry_lpBar_sq hvD'0 hvD'fin hgL, lip_witness_bdry_lpBar_sq hvD0 hvDfin hwL,
      lip_witness_bdry_lpBar_sq hvD0 hvDfin hf', hX']
    have hn1 : 0 ≤ ν * ((volume (openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W)).toReal⁻¹ *
        ∫ x in openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W, vecNormSq (u.grad x)) := by
      have : 0 ≤ ∫ x in openCubeSet (originCube d ((m : ℤ) - 1)) ∩ W, vecNormSq (u.grad x) :=
        integral_nonneg fun x => by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      positivity
    rw [← ENNReal.ofReal_mul hν.le, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : (((3 : ℝ)⁻¹) ^ m) ^ 2 = (((3 : ℝ) ^ m)⁻¹) ^ 2 := by rw [inv_pow]
    rw [e1]
    have := hreal
    nlinarith only [this]
  by_cases hfm : AEStronglyMeasurable f (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W))
  · by_cases hfL : MemLp f 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W))
    · exact key f hfL (hbridge u f (hflux u) hu)
    · have hne : eLpNorm f 2 (volume.restrict (openCubeSet (originCube d (m : ℤ)) ∩ W)) = ⊤ := by
        by_contra h'
        exact hfL (lt_top_iff_ne_top.2 h')
      have hpos : ((volume (openCubeSet (originCube d (m : ℤ)) ∩ W))⁻¹ ^ (1 / 2 : ℝ)) ≠ 0 := by
        intro h0
        rcases ENNReal.rpow_eq_zero_iff.1 h0 with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hvDfin (ENNReal.inv_eq_zero.1 h1)
        · norm_num at h2
      have hlp : lpBar (openCubeSet (originCube d (m : ℤ)) ∩ W) 2 f = ⊤ := by
        rw [rc_lpBar_two_eq _ f hfm, hne, ENNReal.mul_top hpos]
      have hcoef : ENNReal.ofReal (C * S⁻¹ * ((3 : ℝ) ^ m) ^ 2) ≠ 0 := by
        have : 0 < C * S⁻¹ * ((3 : ℝ) ^ m) ^ 2 := by positivity
        exact (ENNReal.ofReal_pos.2 this).ne'
      rw [hlp, ENNReal.top_pow (by norm_num), ENNReal.mul_top hcoef]
      simp
  · have hu0 := lip_int_harm_of_l2_weak_zero_of_not_meas hDo hEllA (hbridge u f (hflux u) hu) hfm
    have h0 := key (fun _ => 0) (memLp_const 0) hu0
    have hz0 : lpBar (openCubeSet (originCube d (m : ℤ)) ∩ W) 2 (fun _ : Vec d => (0 : ℝ)) = 0 := by
      simp [lpBar]
    rw [hz0] at h0
    have hzz : ENNReal.ofReal (C * S⁻¹ * ((3 : ℝ) ^ m) ^ 2) * (0 : ℝ≥0∞) ^ 2 = 0 := by simp
    rw [hzz, add_zero] at h0
    refine h0.trans ?_
    gcongr
    exact le_self_add

end SuperdiffusionCLT.Section7
