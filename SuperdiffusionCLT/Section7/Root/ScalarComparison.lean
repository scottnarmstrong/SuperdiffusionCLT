/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.RescalingB
public import SuperdiffusionCLT.Section7.Analytic.CZ.Uniform
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Boundary
public import SuperdiffusionCLT.Section7.Prereq.WellPosed

/-!
# The two Laplace problems: the zero-datum bounds

For `w ∈ H¹₀(W)` with `-Δw = f` in `W ⊆ (z, z + L)^d`:
`‖w‖_{L²} ≤ (cL)² ‖f‖_{L²}`, `‖∇w‖_{L²} ≤ cL ‖f‖_{L²}`, and (De Giorgi up to the boundary)
`‖w‖_{L^∞} ≤ C L² ‖f‖_{L^∞}`, with `c, C` depending on `d` only.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ}

theorem s12_integral_sq_eq {μ : Measure (Vec d)} {w : Vec d → ℝ} (hw : MemLp w 2 μ) :
    eLpNorm w 2 μ = ENNReal.ofReal ((∫ x, w x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
  rw [hw.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  congr 3
  · funext x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  · norm_num

/-- Energy and `L²` bounds for the Laplace problem with zero datum on a set in a cube. -/
theorem s12_energy [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {W : Set (Vec d)}, IsOpen W → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      W ⊆ axisCube z L → ∀ (f : Vec d → ℝ) (w : H10Function W),
        IsWeakSolutionOn (fun _ => (1 : Mat d)) W w.toH1Function f (fun _ => 0) →
          eLpNorm w.toH1Function.toFun 2 (volume.restrict W) ≤
              ENNReal.ofReal ((c * L) ^ 2) * eLpNorm f 2 (volume.restrict W) ∧
            eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 (volume.restrict W) ≤
              ENNReal.ofReal (c * L) * eLpNorm f 2 (volume.restrict W) := by
  obtain ⟨c, hc, hP⟩ := p13_poincare (d := d)
  refine ⟨c, hc, ?_⟩
  intro W hW z L hL hWL f w hw
  have hcL : 0 < c * L := mul_pos hc hL
  by_cases hfin : eLpNorm f 2 (volume.restrict W) = ⊤
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (pow_pos hcL 2)).ne',
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hcL).ne']
    exact ⟨le_top, le_top⟩
  have hf : MemLp f 2 (volume.restrict W) := lt_top_iff_ne_top.2 hfin
  have hw2 : MemLp w.toH1Function.toFun 2 (volume.restrict W) := w.toH1Function.memL2
  have hg2 : MemLp w.toH1Function.grad 2 (volume.restrict W) := w.toH1Function.grad_memVectorL2
  set t := (c * L) ^ 2 with ht
  have ht0 : 0 < t := pow_pos hcL 2
  set Ig := ∫ x in W, vecNormSq (w.toH1Function.grad x) with hIg
  set Iw := ∫ x in W, w.toH1Function.toFun x ^ 2 with hIw
  set If := ∫ x in W, f x ^ 2 with hIf
  have hIg0 : 0 ≤ Ig := integral_nonneg fun x => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hIw0 : 0 ≤ Iw := integral_nonneg fun x => sq_nonneg _
  have hIf0 : 0 ≤ If := integral_nonneg fun x => sq_nonneg _
  have hiw : Integrable (fun x => w.toH1Function.toFun x ^ 2) (volume.restrict W) := hw2.integrable_sq
  have hif : Integrable (fun x => f x ^ 2) (volume.restrict W) := hf.integrable_sq
  -- the energy identity
  have hE : Ig = ∫ x in W, f x * w.toH1Function.toFun x := by
    have h := hw w
    simp only [p13_matVecMul_one, vecDot_zero_left, integral_zero, add_zero] at h
    exact h
  have hprod : Integrable (fun x => f x * w.toH1Function.toFun x) (volume.restrict W) :=
    integrableOn_mul_of_memL2On hf w.toH1Function.memL2
  have hCS : Ig ≤ (t * If + Iw / t) / 2 := by
    rw [hE]
    have hm : ∫ x in W, f x * w.toH1Function.toFun x ≤
        ∫ x in W, (t * f x ^ 2 + w.toH1Function.toFun x ^ 2 / t) / 2 :=
      integral_mono hprod (((hif.const_mul t).add (hiw.div_const t)).div_const 2) (fun x => by
        have h1 : 0 ≤ (t * f x - w.toH1Function.toFun x) ^ 2 := sq_nonneg _
        have h2 : (t * f x - w.toH1Function.toFun x) ^ 2 =
            t * (t * f x ^ 2 + w.toH1Function.toFun x ^ 2 / t - 2 * (f x * w.toH1Function.toFun x)) := by
          field_simp
          ring
        have h3 : 0 ≤ t * (t * f x ^ 2 + w.toH1Function.toFun x ^ 2 / t -
            2 * (f x * w.toH1Function.toFun x)) := h2 ▸ h1
        have h4 := nonneg_of_mul_nonneg_right h3 ht0
        simp only
        linarith only [h4])
    rw [integral_div, integral_add (hif.const_mul t) (hiw.div_const t), integral_const_mul,
      integral_div] at hm
    exact hm
  -- Poincaré
  have hPo := hP hW z hL hWL w
  have hGe : eLpNorm w.toH1Function.grad 2 (volume.restrict W) ≤
      eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 (volume.restrict W) := by
    refine eLpNorm_mono hg2.aestronglyMeasurable fun x => ?_
    have h0 : 0 ≤ eucNorm (w.toH1Function.grad x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0]
    exact p13_sup_le_euc _
  rw [p13_eLpNorm_euc hg2] at hGe
  rw [s12_integral_sq_eq hw2] at hPo
  have hPo2 := hPo.trans (mul_le_mul' le_rfl hGe)
  rw [← ENNReal.ofReal_mul hcL.le] at hPo2
  have hPo3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hPo2
  have hIwG : Iw ≤ t * Ig := by
    have h1 : (Iw ^ (1 / 2 : ℝ)) ^ 2 ≤ ((c * L) * Ig ^ (1 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hIw0 _) hPo3 2
    have e1 : (Iw ^ (1 / 2 : ℝ)) ^ 2 = Iw := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hIw0]; norm_num
    have e2 : ((c * L) * Ig ^ (1 / 2 : ℝ)) ^ 2 = t * Ig := by
      rw [mul_pow, ht, ← Real.rpow_natCast (Ig ^ (1 / 2 : ℝ)), ← Real.rpow_mul hIg0]; norm_num
    linarith only [h1, e1, e2]
  have hIgF : Ig ≤ t * If := by
    have h1 : Ig ≤ (t * If + t * Ig / t) / 2 := by
      have : Iw / t ≤ t * Ig / t := div_le_div_of_nonneg_right hIwG ht0.le
      linarith only [hCS, this]
    have h2 : t * Ig / t = Ig := by field_simp
    rw [h2] at h1
    linarith only [h1]
  have hIwF : Iw ≤ t * (t * If) := by
    have := mul_le_mul_of_nonneg_left hIgF ht0.le
    linarith only [hIwG, this]
  have hrt : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ t * b → a ^ (1 / 2 : ℝ) ≤ (c * L) * b ^ (1 / 2 : ℝ) := by
    intro a b ha hb hab
    have := Real.rpow_le_rpow ha hab (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow ht0.le hb, ht, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hcL.le, Real.sqrt_eq_rpow] at this
    exact this
  have hIf2 : (t * If) ^ (1 / 2 : ℝ) ≤ (c * L) * If ^ (1 / 2 : ℝ) :=
    hrt (mul_nonneg ht0.le hIf0) hIf0 le_rfl
  have hA := hrt hIw0 (mul_nonneg ht0.le hIf0) hIwF
  have hB := hrt hIg0 hIf0 hIgF
  rw [s12_integral_sq_eq hf, s12_integral_sq_eq hw2, p13_eLpNorm_euc hg2]
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_mul ht0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : t * If ^ (1 / 2 : ℝ) = (c * L) * ((c * L) * If ^ (1 / 2 : ℝ)) := by rw [ht]; ring
    rw [this]
    exact hA.trans (mul_le_mul_of_nonneg_left hIf2 hcL.le)
  · rw [← ENNReal.ofReal_mul hcL.le]
    exact ENNReal.ofReal_le_ofReal hB

theorem s12_weak_const_smul {W : Set (Vec d)} {f : Vec d → ℝ} {w : H10Function W} (c : ℝ)
    (hw : IsWeakSolutionOn (fun _ => (1 : Mat d)) W w.toH1Function f (fun _ => 0)) :
    IsWeakSolutionOn (fun _ => (1 : Mat d)) W (c • w).toH1Function (fun x => c * f x)
      (fun _ => 0) := by
  intro φ
  have h := hw φ
  simp only [vecDot_zero_left, integral_zero, add_zero] at h ⊢
  have e1 : ∀ x, vecDot (matVecMul (1 : Mat d) ((c • w).toH1Function.grad x))
      (φ.toH1Function.grad x) = c * vecDot (matVecMul (1 : Mat d) (w.toH1Function.grad x))
      (φ.toH1Function.grad x) := by
    intro x
    rw [a18_h10_smul_grad, matVecMul_smul, vecDot_smul_left]
  simp only [e1, mul_assoc, integral_const_mul]
  rw [h]

/-- The positive part, from De Giorgi up to the boundary. -/
theorem s12_sup_pos [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → ∀ (z : Vec d) {L : ℝ},
      0 < L → W ⊆ axisCube z L → ∀ (f : Vec d → ℝ) (w : H10Function W),
        IsWeakSolutionOn (fun _ => (1 : Mat d)) W w.toH1Function f (fun _ => 0) →
          eLpNorm (fun x => max (w.toH1Function.toFun x) 0) ⊤ (volume.restrict W) ≤
            ENNReal.ofReal (C * L ^ 2) * eLpNorm f ⊤ (volume.restrict W) := by
  obtain ⟨c, hc, hE⟩ := s12_energy (d := d)
  obtain ⟨Cg, hCg, hDG⟩ := deGiorgi_boundary_bound (d := d) hd
  refine ⟨Cg * (c ^ 2 + 4), by positivity, ?_⟩
  intro W hWo hWb z L hL hWL f w hw
  set M := eLpNorm f ⊤ (volume.restrict W) with hM
  have hCL : 0 < Cg * (c ^ 2 + 4) * L ^ 2 := by positivity
  by_cases hMt : M = ⊤
  · rw [hMt, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  have hfm : AEStronglyMeasurable f (volume.restrict W) := aestronglyMeasurable_of_eLpNorm_ne_top hMt
  -- the cubes
  set z' : Vec d := z - fun _ => L / 2 with hz'
  have hQ : W ⊆ axisCube z' (2 * L) := by
    refine hWL.trans fun x hx j hj => ?_
    have h := hx j hj
    simp only [Set.mem_Ioo, hz', Pi.sub_apply] at h ⊢
    constructor <;> linarith only [h.1, h.2, hL]
  have hHalf : halfCube z' (2 * L) = axisCube z L := by
    unfold halfCube
    have e2 : (z' + fun _ => 2 * L / 4) = z := by
      funext i
      simp only [hz', Pi.add_apply, Pi.sub_apply]
      ring
    rw [e2, show 2 * L / 2 = L by ring]
  have hI1 : W ∩ axisCube z' (2 * L) = W := Set.inter_eq_left.2 hQ
  have hI2 : W ∩ halfCube z' (2 * L) = W := by
    rw [hHalf]; exact Set.inter_eq_left.2 hWL
  have hEll : IsEllipticFieldOn (d := d) 1 1 W (fun _ => (1 : Mat d)) := by
    classical
    refine ⟨?_, fun x _ => isEllipticMatrix_one⟩
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact Measurable.ite hWo.measurableSet measurable_const measurable_const
  have key := hDG hWo hWb hEll z' (by positivity : 0 < 2 * L) f (fun _ => (0 : Vec d))
    aestronglyMeasurable_const w hw
  have hz0 : eLpNorm (fun x => eucNorm ((fun _ => (0 : Vec d)) x)) ⊤
      (volume.restrict (W ∩ axisCube z' (2 * L))) = 0 := by
    have : (fun x : Vec d => eucNorm ((fun _ => (0 : Vec d)) x)) = fun _ => (0 : ℝ) := by
      funext x
      simp [eucNorm, vecNormSq, vecDot]
    rw [this]
    simp
  rw [hz0, hI1, hI2] at key
  simp only [div_one, div_self one_ne_zero, Real.one_rpow, mul_one, mul_zero, add_zero] at key
  have hvol : volume (axisCube z L) = ENNReal.ofReal (L ^ d) := by
    rw [axisCube, Real.volume_pi_Ioo]
    simp only [add_sub_cancel_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ENNReal.ofReal_pow hL.le]
  have hfC : ∀ᵐ x ∂(volume.restrict W), ‖f x‖ₑ ≤ M := by
    rw [hM, eLpNorm_exponent_top hfm]
    exact ae_le_eLpNormEssSup
  have h1 := eLpNorm_le_of_ae_enorm_bound (p := 2) hfm hfC
  rw [Measure.restrict_apply_univ] at h1
  have h2 : volume W ^ ((2 : ℝ≥0∞).toReal⁻¹) ≤ ENNReal.ofReal ((L ^ d) ^ (1 / 2 : ℝ)) := by
    have hv : volume W ≤ ENNReal.ofReal (L ^ d) := hvol ▸ measure_mono hWL
    refine (ENNReal.rpow_le_rpow hv (by norm_num)).trans_eq ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    norm_num
  have hf2 : eLpNorm f 2 (volume.restrict W) ≤ M * ENNReal.ofReal ((L ^ d) ^ (1 / 2 : ℝ)) := by
    refine h1.trans ?_
    rw [smul_eq_mul]
    exact mul_le_mul' le_rfl h2
  obtain ⟨hw2, -⟩ := hE hWo z hL hWL f w hw
  have hwp : eLpNorm (fun x => max (w.toH1Function.toFun x) 0) 2 (volume.restrict W) ≤
      eLpNorm w.toH1Function.toFun 2 (volume.restrict W) := by
    refine eLpNorm_mono (w.toH1Function.memL2.aestronglyMeasurable.sup
      aestronglyMeasurable_const) fun x => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total (w.toH1Function.toFun x) 0 with h | h
    · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h]
  have hmain : eLpNorm (fun x => max (w.toH1Function.toFun x) 0) 2 (volume.restrict W) ≤
      ENNReal.ofReal ((c * L) ^ 2) * (M * ENNReal.ofReal ((L ^ d) ^ (1 / 2 : ℝ))) :=
    hwp.trans (hw2.trans (mul_le_mul' le_rfl hf2))
  have hreal : (2 * L) ^ (-(d : ℝ) / 2) * ((c * L) ^ 2 * (L ^ d) ^ (1 / 2 : ℝ)) + (2 * L) ^ 2 ≤
      (c ^ 2 + 4) * L ^ 2 := by
    have hA : (2 * L) ^ (-(d : ℝ) / 2) ≤ L ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hL (by linarith only [hL]) (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith only [this] : -(d : ℝ) / 2 ≤ 0)
    have hB : L ^ (-(d : ℝ) / 2) * (L ^ d) ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
      have : -(d : ℝ) / 2 + (d : ℝ) * (1 / 2) = 0 := by ring
      rw [this, Real.rpow_zero]
    have hC : 0 ≤ (c * L) ^ 2 * (L ^ d) ^ (1 / 2 : ℝ) := by positivity
    have h3 : (2 * L) ^ (-(d : ℝ) / 2) * ((c * L) ^ 2 * (L ^ d) ^ (1 / 2 : ℝ)) ≤ c ^ 2 * L ^ 2 := by
      calc (2 * L) ^ (-(d : ℝ) / 2) * ((c * L) ^ 2 * (L ^ d) ^ (1 / 2 : ℝ))
          ≤ L ^ (-(d : ℝ) / 2) * ((c * L) ^ 2 * (L ^ d) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right hA hC
        _ = (c * L) ^ 2 * (L ^ (-(d : ℝ) / 2) * (L ^ d) ^ (1 / 2 : ℝ)) := by ring
        _ = c ^ 2 * L ^ 2 := by rw [hB]; ring
    have h4 : (2 * L) ^ 2 = 4 * L ^ 2 := by ring
    linarith only [h3, h4]
  calc eLpNorm (fun x => max (w.toH1Function.toFun x) 0) ⊤ (volume.restrict W)
      ≤ ENNReal.ofReal Cg * (ENNReal.ofReal ((2 * L) ^ (-(d : ℝ) / 2)) *
          eLpNorm (fun x => max (w.toH1Function.toFun x) 0) 2 (volume.restrict W) +
          ENNReal.ofReal ((2 * L) ^ 2) * M) := key
    _ ≤ ENNReal.ofReal Cg * (ENNReal.ofReal ((2 * L) ^ (-(d : ℝ) / 2)) *
          (ENNReal.ofReal ((c * L) ^ 2) * (M * ENNReal.ofReal ((L ^ d) ^ (1 / 2 : ℝ)))) +
          ENNReal.ofReal ((2 * L) ^ 2) * M) :=
        mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hmain) le_rfl)
    _ = ENNReal.ofReal (Cg * ((2 * L) ^ (-(d : ℝ) / 2) * ((c * L) ^ 2 * (L ^ d) ^ (1 / 2 : ℝ)) +
          (2 * L) ^ 2)) * M := by
        rw [ENNReal.ofReal_mul hCg.le, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (sq_nonneg (c * L))]
        ring
    _ ≤ ENNReal.ofReal (Cg * (c ^ 2 + 4) * L ^ 2) * M := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        have := mul_le_mul_of_nonneg_left hreal hCg.le
        linarith only [this]

/-- **`L^∞` bound for the Laplace problem with zero datum** on a set in a cube of side `L`:
`‖w‖_{L^∞(W)} ≤ C L² ‖f‖_{L^∞(W)}`, with `C` depending on `d` only. -/
theorem s12_sup_bound [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → ∀ (z : Vec d) {L : ℝ},
      0 < L → W ⊆ axisCube z L → ∀ (f : Vec d → ℝ) (w : H10Function W),
        IsWeakSolutionOn (fun _ => (1 : Mat d)) W w.toH1Function f (fun _ => 0) →
          eLpNorm w.toH1Function.toFun ⊤ (volume.restrict W) ≤
            ENNReal.ofReal (C * L ^ 2) * eLpNorm f ⊤ (volume.restrict W) := by
  obtain ⟨C, hC, hpos⟩ := s12_sup_pos (d := d) hd
  refine ⟨C, hC, ?_⟩
  intro W hWo hWb z L hL hWL f w hw
  set M := eLpNorm f ⊤ (volume.restrict W) with hM
  by_cases hMt : M = ⊤
  · rw [hMt, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top
  set B := ENNReal.ofReal (C * L ^ 2) * M with hB
  have hwm : AEStronglyMeasurable w.toH1Function.toFun (volume.restrict W) :=
    w.toH1Function.memL2.aestronglyMeasurable
  have hneg := hpos hWo hWb z hL hWL (fun x => (-1 : ℝ) * f x) ((-1 : ℝ) • w)
    (s12_weak_const_smul (-1) hw)
  have hMn : eLpNorm (fun x => (-1 : ℝ) * f x) ⊤ (volume.restrict W) = M := by
    have : (fun x => (-1 : ℝ) * f x) = (-1 : ℝ) • f := by
      funext x
      simp
    rw [this, eLpNorm_const_smul]
    simp [hM]
  rw [hMn] at hneg
  have hp := hpos hWo hWb z hL hWL f w hw
  have a1 : ∀ᵐ x ∂(volume.restrict W), ‖max (w.toH1Function.toFun x) 0‖ₑ ≤ B := by
    have h := enorm_ae_le_eLpNormEssSup (fun x => max (w.toH1Function.toFun x) 0)
      (volume.restrict W)
    have hm1 : AEStronglyMeasurable (fun x => max (w.toH1Function.toFun x) 0)
        (volume.restrict W) := hwm.sup aestronglyMeasurable_const
    rw [← eLpNorm_exponent_top hm1] at h
    filter_upwards [h] with x hx
    exact hx.trans hp
  have a2 : ∀ᵐ x ∂(volume.restrict W), ‖max (-1 * w.toH1Function.toFun x) 0‖ₑ ≤ B := by
    have h := enorm_ae_le_eLpNormEssSup (fun x => max ((-1 : ℝ) * w.toH1Function.toFun x) 0)
      (volume.restrict W)
    have hm2 : AEStronglyMeasurable (fun x => max ((-1 : ℝ) * w.toH1Function.toFun x) 0)
        (volume.restrict W) := (hwm.const_mul (-1 : ℝ)).sup aestronglyMeasurable_const
    rw [← eLpNorm_exponent_top hm2] at h
    filter_upwards [h] with x hx
    exact hx.trans hneg
  rw [eLpNorm_exponent_top hwm]
  refine eLpNormEssSup_le_of_ae_enorm_bound ?_
  filter_upwards [a1, a2] with x h1 h2
  rcases le_total (w.toH1Function.toFun x) 0 with h | h
  · have e : ‖w.toH1Function.toFun x‖ₑ = ‖max (-1 * w.toH1Function.toFun x) 0‖ₑ := by
      rw [max_eq_left (by linarith only [h]), Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        abs_mul, abs_neg, abs_one, one_mul]
    rw [e]; exact h2
  · have e : ‖w.toH1Function.toFun x‖ₑ = ‖max (w.toH1Function.toFun x) 0‖ₑ := by
      rw [max_eq_left h]
    rw [e]; exact h1

/-! ### Satisfiability: the zero solution on the unit square -/

example : True := by
  obtain ⟨C, hC, hmain⟩ := s12_sup_bound (d := 2) le_rfl
  have := hmain (isOpen_axisCube (0 : Vec 2) 1)
    (isOpenBoundedConvexDomain_axisCube (0 : Vec 2) 1).isBoundedDomain (0 : Vec 2) one_pos
    subset_rfl (fun _ => 0) witnessZeroH10 witnessZeroH10_weak
  obtain ⟨c, hc, hE⟩ := s12_energy (d := 2)
  have := hE (isOpen_axisCube (0 : Vec 2) 1) (0 : Vec 2) one_pos subset_rfl (fun _ => 0)
    witnessZeroH10 witnessZeroH10_weak
  trivial

end SuperdiffusionCLT.Section7
