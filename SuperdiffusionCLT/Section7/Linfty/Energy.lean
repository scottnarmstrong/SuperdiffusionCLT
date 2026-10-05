/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.FirstRootB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiB
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC
public import SuperdiffusionCLT.Section7.Analytic.Regularity.MaxPrinciple
public import SuperdiffusionCLT.Section7.Root.InteriorApprox

/-!
# The crude energy estimate and the weak norm of a gradient by a sup bound
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A function bounded almost everywhere by `B` on a set of positive finite measure has normalized
`L²` norm at most `B`. -/
theorem linf_lpBar_le_of_ae_le {W : Set (Vec d)} (h0 : volume W ≠ 0) (ht : volume W ≠ ⊤)
    {p : Vec d → ℝ} (hp : AEStronglyMeasurable p (volume.restrict W)) {B : ℝ}
    (hB : ∀ᵐ x ∂volume.restrict W, |p x| ≤ B) : lpBar W 2 p ≤ ENNReal.ofReal B := by
  rw [li1_lpBar_two_eq W p hp h0 ht]
  have h1 : eLpNorm p 2 (volume.restrict W) ≤
      volume W ^ (1 / 2 : ℝ) * ENNReal.ofReal B := by
    have := eLpNorm_le_of_ae_bound (μ := volume.restrict W) (p := 2) (f := p) (C := B) hp
      (hB.mono fun x hx => by rwa [Real.norm_eq_abs])
    simpa [Measure.restrict_apply_univ] using this
  calc (volume W)⁻¹ ^ (1 / 2 : ℝ) * eLpNorm p 2 (volume.restrict W)
      ≤ (volume W)⁻¹ ^ (1 / 2 : ℝ) * (volume W ^ (1 / 2 : ℝ) * ENNReal.ofReal B) := by gcongr
    _ = ENNReal.ofReal B := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.inv_mul_cancel h0 ht, ENNReal.one_rpow, one_mul]

/-- **A2c — the weak norm of a gradient is bounded by the sup norm**: integration by parts
against `H¹₀`. -/
theorem linf_hMinus_grad_le_sup [NeZero d] {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : IsBoundedDomain W) (hW0 : volume W ≠ 0) (φ : H1Function W) {c : ℝ} (hc : 0 ≤ c)
    (hφ : ∀ᵐ x ∂volume.restrict W, |φ.toFun x| ≤ c) :
    hMinusOneVec W φ.grad ≤ ENNReal.ofReal (d * c) := by
  have _ := hW
  have _ := hc
  have ht := volume_ne_top_of_isBoundedDomain hWb
  refine (rc_hMinusOneVec_grad_le W hW0 ht φ).trans ?_
  have h := linf_lpBar_le_of_ae_le hW0 ht φ.memL2.aestronglyMeasurable hφ
  calc (d : ℝ≥0∞) * lpBar W 2 φ.toFun ≤ (d : ℝ≥0∞) * ENNReal.ofReal c := by gcongr
    _ = ENNReal.ofReal (d * c) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]

/-- Euclidean length of the image of a vector under an elliptic matrix. -/
theorem linf_vecNormSq_matVecMul_le {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (ξ : Vec d) : vecNormSq (matVecMul A ξ) ≤ Lam ^ 2 * vecNormSq ξ :=
  vecNormSq_matVecMul_le_of_isEllipticMatrix hA ξ

/-- Coercivity in the order `(A ξ) · ξ`. -/
theorem linf_coercive {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (ξ : Vec d) :
    lam * vecNormSq ξ ≤ vecDot (matVecMul A ξ) ξ := by
  rw [vecDot_comm]
  exact hA.2.2.1 ξ

/-- Cross term: `|(A T) · ξ| ≤ Λ² |T|² / λ + λ |ξ|² / 4`. -/
theorem linf_cross_le {lam Lam : ℝ} {A : Mat d} (hlam : 0 < lam)
    (hA : IsEllipticMatrix lam Lam A) (T ξ : Vec d) :
    |vecDot (matVecMul A T) ξ| ≤ Lam ^ 2 * vecNormSq T / lam + lam * vecNormSq ξ / 4 := by
  have h1 := s5_abs_vecDot_le_weighted (matVecMul A T) ξ (s := 2 / lam) (by positivity)
  have h2 := linf_vecNormSq_matVecMul_le hA T
  have h3 : 2 / lam * vecNormSq (matVecMul A T) ≤ 2 / lam * (Lam ^ 2 * vecNormSq T) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e : (2 / lam * (Lam ^ 2 * vecNormSq T) + vecNormSq ξ / (2 / lam)) / 2 =
      Lam ^ 2 * vecNormSq T / lam + lam * vecNormSq ξ / 4 := by
    field_simp
    ring
  have h4 : (2 / lam * vecNormSq (matVecMul A T) + vecNormSq ξ / (2 / lam)) / 2 ≤
      (2 / lam * (Lam ^ 2 * vecNormSq T) + vecNormSq ξ / (2 / lam)) / 2 := by
    linarith only [h3]
  linarith only [h1, h4, e]

/-- The Poincaré inequality in squared integral form. -/
theorem linf_poincare_sq [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {W : Set (Vec d)}, IsOpen W → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      W ⊆ axisCube z L → ∀ ψ : H10Function W,
        ∫ x in W, ψ.toH1Function.toFun x ^ 2 ≤
          (c * L) ^ 2 * ∫ x in W, vecNormSq (ψ.toH1Function.grad x) := by
  obtain ⟨c, hc, hP⟩ := p13_poincare (d := d)
  refine ⟨c, hc, ?_⟩
  intro W hWo z L hL hWL ψ
  have hcL : 0 < c * L := mul_pos hc hL
  have hv2 : MemLp ψ.toH1Function.toFun 2 (volume.restrict W) := ψ.toH1Function.memL2
  have hgv : MemLp ψ.toH1Function.grad 2 (volume.restrict W) := ψ.toH1Function.grad_memVectorL2
  set I := ∫ x in W, vecNormSq (ψ.toH1Function.grad x) with hI
  set V2 := ∫ x in W, ψ.toH1Function.toFun x ^ 2 with hV2
  have hI0 : 0 ≤ I := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hV20 : 0 ≤ V2 := integral_nonneg fun x => sq_nonneg _
  have hPo' := hP hWo z hL hWL (φ := ψ)
  have hGe : eLpNorm ψ.toH1Function.grad 2 (volume.restrict W) ≤
      eLpNorm (fun x => eucNorm (ψ.toH1Function.grad x)) 2 (volume.restrict W) := by
    refine eLpNorm_mono hgv.aestronglyMeasurable fun x => ?_
    have h0 : 0 ≤ eucNorm (ψ.toH1Function.grad x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0]
    exact p13_sup_le_euc _
  rw [p13_eLpNorm_euc hgv] at hGe
  rw [s12_integral_sq_eq hv2] at hPo'
  have hPo2 := hPo'.trans (mul_le_mul' le_rfl hGe)
  rw [← ENNReal.ofReal_mul hcL.le] at hPo2
  have hPo3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hPo2
  have h1 : (V2 ^ (1 / 2 : ℝ)) ^ 2 ≤ ((c * L) * I ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hV20 _) hPo3 2
  have e1 : (V2 ^ (1 / 2 : ℝ)) ^ 2 = V2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV20]; norm_num
  have e2 : ((c * L) * I ^ (1 / 2 : ℝ)) ^ 2 = (c * L) ^ 2 * I := by
    rw [mul_pow, ← Real.rpow_natCast (I ^ (1 / 2 : ℝ)), ← Real.rpow_mul hI0]; norm_num
  linarith only [h1, e1, e2]

/-- **Energy inequality for an `H¹₀` test function** with a right-hand side `f` and a forcing
term `A T`: `‖∇ψ‖² ≤ 2 ((c L)² ‖f‖² + Λ² ‖T‖²) / λ²`. -/
theorem linf_energy_h10 [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {W : Set (Vec d)}, IsOpen W → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      W ⊆ axisCube z L → ∀ {lam Lam : ℝ} {a : CoeffField d}, 0 < lam →
      IsEllipticFieldOn lam Lam W a → ∀ {f : Vec d → ℝ} (ψ : H10Function W) (T : Vec d → Vec d),
      MemLp f 2 (volume.restrict W) → MemLp T 2 (volume.restrict W) →
      ∫ x in W, vecDot (matVecMul (a x) (ψ.toH1Function.grad x)) (ψ.toH1Function.grad x) =
        (∫ x in W, f x * ψ.toH1Function.toFun x) -
          ∫ x in W, vecDot (matVecMul (a x) (T x)) (ψ.toH1Function.grad x) →
      ∫ x in W, vecNormSq (ψ.toH1Function.grad x) ≤
        2 * ((c * L) ^ 2 * (∫ x in W, f x ^ 2) + Lam ^ 2 * ∫ x in W, vecNormSq (T x)) / lam ^ 2 := by
  obtain ⟨c, hc, hP⟩ := linf_poincare_sq (d := d)
  refine ⟨c, hc, ?_⟩
  intro W hWo z L hL hWL lam Lam a hlam hEll f ψ T hf hT hid
  have hcL : 0 < c * L := mul_pos hc hL
  set t := (c * L) ^ 2 with ht
  have ht0 : 0 < t := pow_pos hcL 2
  have hVI := hP hWo z hL hWL ψ
  have hv2 : MemLp ψ.toH1Function.toFun 2 (volume.restrict W) := ψ.toH1Function.memL2
  have hgv : MemLp ψ.toH1Function.grad 2 (volume.restrict W) := ψ.toH1Function.grad_memVectorL2
  set I := ∫ x in W, vecNormSq (ψ.toH1Function.grad x) with hI
  set V2 := ∫ x in W, ψ.toH1Function.toFun x ^ 2 with hV2
  set F2 := ∫ x in W, f x ^ 2 with hF2
  set Q := ∫ x in W, vecNormSq (T x) with hQ
  have hiv : Integrable (fun x => ψ.toH1Function.toFun x ^ 2) (volume.restrict W) :=
    hv2.integrable_sq
  have hif : Integrable (fun x => f x ^ 2) (volume.restrict W) := hf.integrable_sq
  have hiI := p13_integrable_vecNormSq hgv
  have hiQ := p13_integrable_vecNormSq hT
  have hI0 : 0 ≤ I := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hV20 : 0 ≤ V2 := integral_nonneg fun x => sq_nonneg _
  have hF20 : 0 ≤ F2 := integral_nonneg fun x => sq_nonneg _
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hmem : ∀ᵐ x ∂volume.restrict W, x ∈ W := ae_restrict_mem hWo.measurableSet
  have hfluxξ : MemVectorL2 W (fun x => matVecMul (a x) (ψ.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll ψ.toH1Function.grad_memVectorL2
  have hfluxT : MemVectorL2 W (fun x => matVecMul (a x) (T x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hT
  have hi1 : Integrable (fun x => vecDot (matVecMul (a x) (ψ.toH1Function.grad x))
      (ψ.toH1Function.grad x)) (volume.restrict W) :=
    integrableOn_vecDot_of_memVectorL2 hfluxξ ψ.toH1Function.grad_memVectorL2
  have hi2 : Integrable (fun x => vecDot (matVecMul (a x) (T x)) (ψ.toH1Function.grad x))
      (volume.restrict W) :=
    integrableOn_vecDot_of_memVectorL2 hfluxT ψ.toH1Function.grad_memVectorL2
  have hifv : Integrable (fun x => f x * ψ.toH1Function.toFun x) (volume.restrict W) :=
    integrableOn_mul_of_memL2On hf ψ.toH1Function.memL2
  -- coercivity
  have hco : lam * I ≤ ∫ x in W, vecDot (matVecMul (a x) (ψ.toH1Function.grad x))
      (ψ.toH1Function.grad x) := by
    rw [hI, ← integral_const_mul]
    refine integral_mono_ae (hiI.const_mul lam) hi1 ?_
    filter_upwards [hmem] with x hx
    exact linf_coercive (hEll.2 x hx) _
  -- the forcing term
  have hcross : -∫ x in W, vecDot (matVecMul (a x) (T x)) (ψ.toH1Function.grad x) ≤
      Lam ^ 2 * Q / lam + lam * I / 4 := by
    have h1 : |∫ x in W, vecDot (matVecMul (a x) (T x)) (ψ.toH1Function.grad x)| ≤
        ∫ x in W, (Lam ^ 2 * vecNormSq (T x) / lam +
          lam * vecNormSq (ψ.toH1Function.grad x) / 4) := by
      have h0 := norm_integral_le_integral_norm (μ := volume.restrict W)
        (fun x => vecDot (matVecMul (a x) (T x)) (ψ.toH1Function.grad x))
      rw [Real.norm_eq_abs] at h0
      refine h0.trans ?_
      refine integral_mono_ae hi2.norm
        (((hiQ.const_mul (Lam ^ 2)).div_const lam).add ((hiI.const_mul lam).div_const 4)) ?_
      filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs]
      exact linf_cross_le hlam (hEll.2 x hx) _ _
    have h2 : ∫ x in W, (Lam ^ 2 * vecNormSq (T x) / lam +
        lam * vecNormSq (ψ.toH1Function.grad x) / 4) = Lam ^ 2 * Q / lam + lam * I / 4 := by
      rw [integral_add ((hiQ.const_mul (Lam ^ 2)).div_const lam)
        ((hiI.const_mul lam).div_const 4), integral_div, integral_div, integral_const_mul,
        integral_const_mul]
    have h3 := neg_abs_le (∫ x in W, vecDot (matVecMul (a x) (T x)) (ψ.toH1Function.grad x))
    linarith only [h1, h2, h3]
  -- the right-hand side
  have hfv : ∫ x in W, f x * ψ.toH1Function.toFun x ≤ t * F2 / lam + lam * I / 4 := by
    have hα : 0 < 2 * t / lam := by positivity
    have hm : ∫ x in W, f x * ψ.toH1Function.toFun x ≤
        ∫ x in W, ((2 * t / lam) * f x ^ 2 + ψ.toH1Function.toFun x ^ 2 / (2 * t / lam)) / 2 :=
      integral_mono hifv (((hif.const_mul (2 * t / lam)).add
        (hiv.div_const (2 * t / lam))).div_const 2) (fun x => s5_mul_le_weighted hα)
    rw [integral_div, integral_add (hif.const_mul (2 * t / lam)) (hiv.div_const (2 * t / lam)),
      integral_const_mul, integral_div] at hm
    have e : ((2 * t / lam) * F2 + V2 / (2 * t / lam)) / 2 = t * F2 / lam + lam * V2 / (4 * t) := by
      field_simp
      ring
    have h4 : lam * V2 / (4 * t) ≤ lam * I / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : lam * V2 ≤ lam * (t * I) := mul_le_mul_of_nonneg_left hVI hlam.le
      linarith only [this]
    linarith only [hm, e, h4]
  have hmain : lam * I ≤ t * F2 / lam + lam * I / 4 + (Lam ^ 2 * Q / lam + lam * I / 4) := by
    linarith only [hco, hid, hfv, hcross]
  have hmain2 : lam * I / 2 ≤ (t * F2 + Lam ^ 2 * Q) / lam := by
    have e : (t * F2 + Lam ^ 2 * Q) / lam = t * F2 / lam + Lam ^ 2 * Q / lam := by ring
    linarith only [hmain, e]
  rw [le_div_iff₀ (by positivity)]
  have h5 : lam * I / 2 * lam ≤ (t * F2 + Lam ^ 2 * Q) := by
    have := mul_le_mul_of_nonneg_right hmain2 hlam.le
    rwa [div_mul_cancel₀ _ hlam.ne'] at this
  have h6 : I * lam ^ 2 ≤ 2 * (t * F2 + Lam ^ 2 * Q) := by linarith only [h5]
  exact h6

/-- The normalized `L²` norm of the length of a vector field from its squared integral. -/
theorem linf_lpBar_euc_le {W : Set (Vec d)} (h0 : volume W ≠ 0) (ht : volume W ≠ ⊤)
    {ξ : Vec d → Vec d} (hξ : MemLp ξ 2 (volume.restrict W)) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫ x in W, vecNormSq (ξ x) ≤ K ^ 2 * (volume W).toReal) :
    lpBar W 2 (fun x => eucNorm (ξ x)) ≤ ENNReal.ofReal K := by
  rw [li1_lpBar_two_eq W _ (p13_memLp_euc hξ).aestronglyMeasurable h0 ht, p13_eLpNorm_euc hξ]
  have hJ0 : 0 ≤ ∫ x in W, vecNormSq (ξ x) := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hm0 : 0 ≤ (volume W).toReal := ENNReal.toReal_nonneg
  have h1 : (∫ x in W, vecNormSq (ξ x)) ^ (1 / 2 : ℝ) ≤ K * (volume W).toReal ^ (1 / 2 : ℝ) := by
    refine (Real.rpow_le_rpow hJ0 h (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (sq_nonneg K) hm0, ← Real.rpow_natCast, ← Real.rpow_mul hK]
    norm_num
  have h2 : ENNReal.ofReal ((∫ x in W, vecNormSq (ξ x)) ^ (1 / 2 : ℝ)) ≤
      volume W ^ (1 / 2 : ℝ) * ENNReal.ofReal K := by
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [ENNReal.ofReal_mul hK, mul_comm,
      ← ENNReal.ofReal_rpow_of_nonneg hm0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_toReal ht]
  calc (volume W)⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal ((∫ x in W, vecNormSq (ξ x)) ^ (1 / 2 : ℝ))
      ≤ (volume W)⁻¹ ^ (1 / 2 : ℝ) * (volume W ^ (1 / 2 : ℝ) * ENNReal.ofReal K) := by gcongr
    _ = ENNReal.ofReal K := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.inv_mul_cancel h0 ht, ENNReal.one_rpow, one_mul]

/-- The Euclidean length of the gradient vector of a linear form is at most `d + 1` times its
operator norm. -/
theorem linf_euc_basis_le (ℓ : Vec d →L[ℝ] ℝ) :
    eucNorm (fun i => ℓ (basisVec i)) ≤ ((d : ℝ) + 1) * ‖ℓ‖ := by
  have h2 : ∀ i : Fin d, ‖basisVec (d := d) i‖ = 1 := fun i => by
    simp [basisVec, Pi.norm_single]
  have h3 : ‖fun i => ℓ (basisVec i)‖ ≤ ‖ℓ‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg ℓ)).2 fun i => ?_
    calc ‖ℓ (basisVec i)‖ ≤ ‖ℓ‖ * ‖basisVec (d := d) i‖ := ℓ.le_opNorm _
      _ = ‖ℓ‖ := by rw [h2, mul_one]
  refine (p13_euc_le_sup _).trans ?_
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **A2a — the crude energy estimate** for the Dirichlet problem with a smooth datum. -/
theorem linf_energy [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W →
      ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L → volume W ≠ 0 →
      ∀ {lam Lam : ℝ} {a : CoeffField d}, 0 < lam → IsEllipticFieldOn lam Lam W a →
      ∀ {f : Vec d → ℝ} (v : H1Function W) {gt : Vec d → ℝ}, ContDiff ℝ 1 gt →
      AEStronglyMeasurable f (volume.restrict W) →
      IsWeakSolutionOn a W v f (fun _ => 0) → MemH10 W (fun x => v.toFun x - gt x) →
      ∀ {F G : ℝ}, 0 ≤ F → 0 ≤ G → (∀ᵐ x ∂volume.restrict W, |f x| ≤ F) →
        (∀ x ∈ W, ‖fderiv ℝ gt x‖ ≤ G) →
        lpBar W 2 (fun x => eucNorm (v.grad x)) ≤
          ENNReal.ofReal (C * (Lam / lam * G + L / lam * F)) := by
  obtain ⟨c, hc, hE⟩ := linf_energy_h10 (d := d)
  refine ⟨2 * c + 3 * ((d : ℝ) + 1), by positivity, ?_⟩
  intro W hWo hWb z L hL hWL hW0 lam Lam a hlam hEll f v gt hgt hfm hv hmem F G hF hG hfF hgG
  have ht := volume_ne_top_of_isBoundedDomain hWb
  obtain ⟨ψ, hψ⟩ := hmem
  set gH := li1_h1 hWo hWb hgt with hgH
  have : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 ht⟩
  have hmemW : ∀ᵐ x ∂volume.restrict W, x ∈ W := ae_restrict_mem hWo.measurableSet
  have hf2 : MemLp f 2 (volume.restrict W) :=
    MemLp.of_bound hfm F (hfF.mono fun x hx => by rwa [Real.norm_eq_abs])
  have hT2 : MemLp gH.grad 2 (volume.restrict W) := gH.grad_memVectorL2
  have hξ2 : MemLp ψ.toH1Function.grad 2 (volume.restrict W) := ψ.toH1Function.grad_memVectorL2
  have hv2 : MemLp v.grad 2 (volume.restrict W) := v.grad_memVectorL2
  have hgrad : ψ.toH1Function.grad =ᵐ[volume.restrict W] fun x => v.grad x - gH.grad x :=
    w0_h10_grad_ae hWo gH v ψ (by rw [hψ]; rfl)
  have hvT : ∀ᵐ x ∂volume.restrict W, v.grad x = ψ.toH1Function.grad x + gH.grad x := by
    filter_upwards [hgrad] with x hx
    rw [hx]; abel
  -- the energy identity
  have hfluxξ : MemVectorL2 W (fun x => matVecMul (a x) (ψ.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll ψ.toH1Function.grad_memVectorL2
  have hfluxT : MemVectorL2 W (fun x => matVecMul (a x) (gH.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll gH.grad_memVectorL2
  have hi1 : Integrable (fun x => vecDot (matVecMul (a x) (ψ.toH1Function.grad x))
      (ψ.toH1Function.grad x)) (volume.restrict W) :=
    integrableOn_vecDot_of_memVectorL2 hfluxξ ψ.toH1Function.grad_memVectorL2
  have hi2 : Integrable (fun x => vecDot (matVecMul (a x) (gH.grad x))
      (ψ.toH1Function.grad x)) (volume.restrict W) :=
    integrableOn_vecDot_of_memVectorL2 hfluxT ψ.toH1Function.grad_memVectorL2
  have hid : ∫ x in W, vecDot (matVecMul (a x) (ψ.toH1Function.grad x))
        (ψ.toH1Function.grad x) =
      (∫ x in W, f x * ψ.toH1Function.toFun x) -
        ∫ x in W, vecDot (matVecMul (a x) (gH.grad x)) (ψ.toH1Function.grad x) := by
    have h1 := hv ψ
    simp only [vecDot_zero_left, integral_zero, add_zero] at h1
    have h2 : ∫ x in W, vecDot (matVecMul (a x) (v.grad x)) (ψ.toH1Function.grad x) =
        (∫ x in W, vecDot (matVecMul (a x) (ψ.toH1Function.grad x)) (ψ.toH1Function.grad x)) +
          ∫ x in W, vecDot (matVecMul (a x) (gH.grad x)) (ψ.toH1Function.grad x) := by
      rw [← integral_add hi1 hi2]
      refine integral_congr_ae ?_
      filter_upwards [hvT] with x hx
      rw [hx, matVecMul_add, vecDot_add_left]
    linarith only [h1, h2]
  have hIbd := hE hWo z hL hWL hlam hEll ψ gH.grad hf2 hT2 hid
  -- the bounds on the data
  set m : ℝ := (volume W).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hF2 : ∫ x in W, f x ^ 2 ≤ F ^ 2 * m := by
    have h1 : ∫ x in W, f x ^ 2 ≤ ∫ _x in W, F ^ 2 :=
      integral_mono_ae hf2.integrable_sq (integrable_const _)
        (hfF.mono fun x hx => by
          have := pow_le_pow_left₀ (abs_nonneg (f x)) hx 2
          rwa [sq_abs] at this)
    rw [setIntegral_const, smul_eq_mul, mul_comm] at h1
    exact h1
  have hg' : ∀ x ∈ W, vecNormSq (gH.grad x) ≤ (((d : ℝ) + 1) * G) ^ 2 := by
    intro x hx
    have h1 : eucNorm (gH.grad x) ≤ ((d : ℝ) + 1) * G := by
      refine (linf_euc_basis_le (fderiv ℝ gt x)).trans ?_
      exact mul_le_mul_of_nonneg_left (hgG x hx) (by positivity)
    rw [p13_vecNormSq_eq]
    exact pow_le_pow_left₀ (eucNorm_nonneg _) h1 2
  have hQ : ∫ x in W, vecNormSq (gH.grad x) ≤ (((d : ℝ) + 1) * G) ^ 2 * m := by
    have h1 : ∫ x in W, vecNormSq (gH.grad x) ≤ ∫ _x in W, (((d : ℝ) + 1) * G) ^ 2 :=
      integral_mono_ae (p13_integrable_vecNormSq hT2) (integrable_const _)
        (by filter_upwards [hmemW] with x hx using hg' x hx)
    rw [setIntegral_const, smul_eq_mul, mul_comm] at h1
    exact h1
  -- the gradient of `v`
  have hV : ∫ x in W, vecNormSq (v.grad x) ≤
      2 * (∫ x in W, vecNormSq (ψ.toH1Function.grad x)) + 2 * ∫ x in W, vecNormSq (gH.grad x) := by
    have h1 : ∫ x in W, vecNormSq (v.grad x) ≤
        ∫ x in W, (2 * vecNormSq (ψ.toH1Function.grad x) + 2 * vecNormSq (gH.grad x)) :=
      integral_mono_ae (p13_integrable_vecNormSq hv2)
        (((p13_integrable_vecNormSq hξ2).const_mul 2).add
          ((p13_integrable_vecNormSq hT2).const_mul 2))
        (by
          filter_upwards [hvT] with x hx
          rw [hx]
          exact s5_vecNormSq_add_le _ _)
    rw [integral_add ((p13_integrable_vecNormSq hξ2).const_mul 2)
      ((p13_integrable_vecNormSq hT2).const_mul 2), integral_const_mul, integral_const_mul] at h1
    exact h1
  -- the arithmetic
  have hlamLam : lam ≤ Lam := by
    obtain ⟨x₀, hx₀⟩ : W.Nonempty := nonempty_of_measure_ne_zero hW0
    exact (hEll.2 x₀ hx₀).2.1
  have hr : 1 ≤ Lam / lam := by rw [le_div_iff₀ hlam]; linarith only [hlamLam]
  set r := Lam / lam with hrdef
  set X : ℝ := c * L * F / lam with hX
  set Y : ℝ := ((d : ℝ) + 1) * r * G with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  set g' : ℝ := ((d : ℝ) + 1) * G with hg'def
  have hg'0 : 0 ≤ g' := by positivity
  have hYg : g' ≤ Y := by
    rw [hY, hg'def]
    have : 0 ≤ ((d : ℝ) + 1) * G := by positivity
    nlinarith only [hr, this]
  have hI2 : ∫ x in W, vecNormSq (ψ.toH1Function.grad x) ≤ (2 * X ^ 2 + 2 * Y ^ 2) * m := by
    refine hIbd.trans ?_
    have h1 : 2 * ((c * L) ^ 2 * (∫ x in W, f x ^ 2) +
        Lam ^ 2 * ∫ x in W, vecNormSq (gH.grad x)) ≤
        2 * ((c * L) ^ 2 * (F ^ 2 * m) + Lam ^ 2 * (g' ^ 2 * m)) := by
      have := mul_le_mul_of_nonneg_left hF2 (sq_nonneg (c * L))
      have := mul_le_mul_of_nonneg_left hQ (sq_nonneg Lam)
      linarith only [this, ‹(c * L) ^ 2 * (∫ x in W, f x ^ 2) ≤ (c * L) ^ 2 * (F ^ 2 * m)›]
    refine (div_le_div_of_nonneg_right h1 (by positivity)).trans (le_of_eq ?_)
    rw [hX, hY, hrdef, hg'def]
    field_simp
  have hK2 : ∫ x in W, vecNormSq (v.grad x) ≤ (2 * X + 3 * Y) ^ 2 * m := by
    have hg2 : g' ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hg'0 hYg 2
    have hQ2 : ∫ x in W, vecNormSq (gH.grad x) ≤ Y ^ 2 * m :=
      hQ.trans (mul_le_mul_of_nonneg_right hg2 hm0)
    have h3 : (2 * X + 3 * Y) ^ 2 ≥ 4 * X ^ 2 + 4 * Y ^ 2 + 2 * Y ^ 2 := by
      nlinarith only [mul_nonneg hX0 hY0, sq_nonneg Y]
    have h4 : 2 * ((2 * X ^ 2 + 2 * Y ^ 2) * m) + 2 * (Y ^ 2 * m) ≤ (2 * X + 3 * Y) ^ 2 * m := by
      nlinarith only [h3, hm0]
    linarith only [hV, hI2, hQ2, h4]
  have hK0 : 0 ≤ 2 * X + 3 * Y := by positivity
  refine (linf_lpBar_euc_le hW0 ht hv2 hK0 hK2).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : X = c * (L / lam * F) := by rw [hX]; ring
  have hLF : 0 ≤ L / lam * F := by positivity
  have hrG : 0 ≤ r * G := by positivity
  have e2 : Y = ((d : ℝ) + 1) * (r * G) := by rw [hY]; ring
  rw [e1, e2]
  nlinarith only [hLF, hrG, hc, Nat.cast_nonneg (α := ℝ) d, mul_nonneg hc.le hLF]

/-- Satisfiability data on the unit disc with the identity field and zero data. -/
theorem linf_ball_zero_weak :
    IsWeakSolutionOn (fun _ => (1 : Mat 2)) (Section6.euclidBall (d := 2) 1)
      (0 : H1Function (Section6.euclidBall (d := 2) 1)) (fun _ => 0) (fun _ => 0) := by
  intro φ
  have h0 : ∀ x, (0 : H1Function (Section6.euclidBall (d := 2) 1)).grad x = 0 := fun _ => rfl
  simp [vecDot, matVecMul, h0]

theorem linf_ball_zero_memH10 :
    MemH10 (Section6.euclidBall (d := 2) 1) (fun x =>
      (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x - (fun _ : Vec 2 => (0 : ℝ)) x) := by
  have : (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
      (fun _ : Vec 2 => (0 : ℝ)) x) = 0 := by
    funext x; simp
  rw [this]
  exact memH10_zero

theorem linf_ball_volume_ne_zero : volume (Section6.euclidBall (d := 2) 1) ≠ 0 := by
  refine ((Section6.isOpen_euclidBall (d := 2) 1).measure_pos volume ⟨0, ?_⟩).ne'
  simp [Section6.euclidBall, vecNormSq, vecDot]

/-- Witness for the crude energy estimate: the unit disc, identity field, zero data. -/
example : ∃ C : ℝ, 0 < C ∧ lpBar (Section6.euclidBall (d := 2) 1) 2
    (fun x => eucNorm ((0 : H1Function (Section6.euclidBall (d := 2) 1)).grad x)) ≤
      ENNReal.ofReal (C * (1 / 1 * 0 + 2 / 1 * 0)) := by
  obtain ⟨C, hC, h⟩ := linf_energy (d := 2)
  exact ⟨C, hC, h (Section6.isOpen_euclidBall 1) (isBoundedDomain_euclidBall one_pos)
    (fun _ => -1) two_pos ia_euclidBall_subset_axisCube linf_ball_volume_ne_zero one_pos
    isEllipticFieldOn_one_euclidBall (f := fun _ => 0) 0 (gt := fun _ => 0) contDiff_const
    aestronglyMeasurable_const linf_ball_zero_weak linf_ball_zero_memH10 le_rfl le_rfl
    (Filter.Eventually.of_forall fun x => by simp) (fun x _ => by simp)⟩

/-- Witness for the weak norm of a gradient: the zero function on the unit disc. -/
example : hMinusOneVec (Section6.euclidBall (d := 2) 1)
    (0 : H1Function (Section6.euclidBall (d := 2) 1)).grad ≤ ENNReal.ofReal (2 * 0) :=
  linf_hMinus_grad_le_sup (Section6.isOpen_euclidBall 1) (isBoundedDomain_euclidBall one_pos)
    linf_ball_volume_ne_zero 0 le_rfl (Filter.Eventually.of_forall fun x => by simp)

end SuperdiffusionCLT.Section7
