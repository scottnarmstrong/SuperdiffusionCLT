/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.FirstRoot

/-!
# The gradient of a Dirichlet solution of the Laplace problem, in `L²` and in `H^{-1}`

For `-Δ uh = f` in `W ⊆ (z, z + L)^d` with datum `g ∈ H¹(W)`:
`‖∇uh‖_{L²} ≤ 3 (c L ‖f‖_{L²} + ‖∇g‖_{L²})` and
`[∇uh]_{H^{-1}(W)} ≤ C (L² ‖f‖_{L^∞} + L ‖∇g‖_{L^∞})`, with `c, C` depending on `d` only.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ}

theorem s5_mul_le_weighted {x y s : ℝ} (hs : 0 < s) : x * y ≤ (s * x ^ 2 + y ^ 2 / s) / 2 := by
  have h : 0 ≤ (s * x - y) ^ 2 / s := by positivity
  have e : (s * x - y) ^ 2 / s = s * x ^ 2 + y ^ 2 / s - 2 * (x * y) := by
    field_simp
    ring
  linarith only [h, e]

theorem s5_abs_vecDot_le_weighted (a b : Vec d) {s : ℝ} (hs : 0 < s) :
    |vecDot a b| ≤ (s * vecNormSq a + vecNormSq b / s) / 2 := by
  have h1 := abs_vecDot_le_eucNorm_mul a b
  have h2 := s5_mul_le_weighted (x := eucNorm a) (y := eucNorm b) hs
  rw [p13_vecNormSq_eq, p13_vecNormSq_eq]
  linarith only [h1, h2]

theorem s5_vecNormSq_add_le (a b : Vec d) : vecNormSq (a + b) ≤ 2 * vecNormSq a + 2 * vecNormSq b := by
  have h := s5_abs_vecDot_le_weighted a b one_pos
  have e : vecNormSq (a + b) = vecNormSq a + 2 * vecDot a b + vecNormSq b := by
    unfold vecNormSq vecDot
    simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    have : ∑ i, b i * a i = ∑ i, a i * b i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this]
    ring
  have h3 := le_abs_self (vecDot a b)
  rw [e]
  linarith only [h, h3]

theorem s5_vecNormSq_nonneg (a : Vec d) : 0 ≤ vecNormSq a := by
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **Energy estimate for the Dirichlet problem with `H¹` datum.** -/
theorem s5_dirichlet_energy [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {W : Set (Vec d)}, IsOpen W → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      W ⊆ axisCube z L → ∀ (f : Vec d → ℝ), MemLp f 2 (volume.restrict W) →
        ∀ (g uh : H1Function W),
          s12_IsDirichletSolution (fun _ => (1 : Mat d)) W f g uh →
            eLpNorm (fun x => eucNorm (uh.grad x)) 2 (volume.restrict W) ≤
              ENNReal.ofReal (3 * (c * L)) * eLpNorm f 2 (volume.restrict W) +
                ENNReal.ofReal 3 * eLpNorm (fun x => eucNorm (g.grad x)) 2 (volume.restrict W) := by
  obtain ⟨c, hc, hP⟩ := p13_poincare (d := d)
  refine ⟨c, hc, ?_⟩
  intro W hWo z L hL hWL f hf g uh h
  obtain ⟨v, hv⟩ := h.2
  have hcL : 0 < c * L := mul_pos hc hL
  set t := (c * L) ^ 2 with ht
  have ht0 : 0 < t := pow_pos hcL 2
  have hgrad : v.toH1Function.grad =ᵐ[volume.restrict W] fun x => uh.grad x - g.grad x :=
    w0_h10_grad_ae hWo g uh v hv
  have hv2 : MemLp v.toH1Function.toFun 2 (volume.restrict W) := v.toH1Function.memL2
  have hgv : MemLp v.toH1Function.grad 2 (volume.restrict W) := v.toH1Function.grad_memVectorL2
  have hgu : MemLp uh.grad 2 (volume.restrict W) := uh.grad_memVectorL2
  have hgg : MemLp g.grad 2 (volume.restrict W) := g.grad_memVectorL2
  set I := ∫ x in W, vecNormSq (v.toH1Function.grad x) with hI
  set V2 := ∫ x in W, v.toH1Function.toFun x ^ 2 with hV2
  set F2 := ∫ x in W, f x ^ 2 with hF2
  set G2 := ∫ x in W, vecNormSq (g.grad x) with hG2
  set U2 := ∫ x in W, vecNormSq (uh.grad x) with hU2
  have hiv : Integrable (fun x => v.toH1Function.toFun x ^ 2) (volume.restrict W) := hv2.integrable_sq
  have hif : Integrable (fun x => f x ^ 2) (volume.restrict W) := hf.integrable_sq
  have hiI := p13_integrable_vecNormSq hgv
  have hiG := p13_integrable_vecNormSq hgg
  have hiU := p13_integrable_vecNormSq hgu
  have hI0 : 0 ≤ I := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hV20 : 0 ≤ V2 := integral_nonneg fun x => sq_nonneg _
  have hF20 : 0 ≤ F2 := integral_nonneg fun x => sq_nonneg _
  have hG20 : 0 ≤ G2 := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hU20 : 0 ≤ U2 := integral_nonneg fun x => s5_vecNormSq_nonneg _
  -- Poincare: V2 ≤ t I
  have hVI : V2 ≤ t * I := by
    have hPo' := hP hWo z hL hWL (φ := v)
    have hGe : eLpNorm v.toH1Function.grad 2 (volume.restrict W) ≤
        eLpNorm (fun x => eucNorm (v.toH1Function.grad x)) 2 (volume.restrict W) := by
      refine eLpNorm_mono hgv.aestronglyMeasurable fun x => ?_
      have h0 : 0 ≤ eucNorm (v.toH1Function.grad x) := Real.sqrt_nonneg _
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
    have e2 : ((c * L) * I ^ (1 / 2 : ℝ)) ^ 2 = t * I := by
      rw [mul_pow, ht, ← Real.rpow_natCast (I ^ (1 / 2 : ℝ)), ← Real.rpow_mul hI0]; norm_num
    linarith only [h1, e1, e2]
  -- the energy identity
  have hweak : ∫ x in W, vecDot (uh.grad x) (v.toH1Function.grad x) =
      ∫ x in W, f x * v.toH1Function.toFun x := by
    have h1 := h.1 v
    simp only [p13_matVecMul_one, vecDot_zero_left, integral_zero, add_zero] at h1
    exact h1
  have hiuv : Integrable (fun x => vecDot (uh.grad x) (v.toH1Function.grad x)) (volume.restrict W) :=
    integrableOn_vecDot_of_memVectorL2 hgu hgv
  have higv : Integrable (fun x => vecDot (g.grad x) (v.toH1Function.grad x)) (volume.restrict W) :=
    integrableOn_vecDot_of_memVectorL2 hgg hgv
  have hifv : Integrable (fun x => f x * v.toH1Function.toFun x) (volume.restrict W) :=
    integrableOn_mul_of_memL2On hf hv2
  have hIeq : I = (∫ x in W, f x * v.toH1Function.toFun x) -
      ∫ x in W, vecDot (g.grad x) (v.toH1Function.grad x) := by
    rw [← hweak, ← integral_sub hiuv higv]
    rw [hI]
    refine integral_congr_ae (hgrad.mono fun x hx => ?_)
    have hx' : v.toH1Function.grad x = uh.grad x - g.grad x := hx
    calc vecNormSq (v.toH1Function.grad x) = vecDot (v.toH1Function.grad x) (v.toH1Function.grad x) := rfl
      _ = vecDot (uh.grad x - g.grad x) (v.toH1Function.grad x) := by rw [← hx']
      _ = _ := s12_vecDot_sub_left _ _ _
  -- bound the two integrals
  have hfv : ∫ x in W, f x * v.toH1Function.toFun x ≤ (4 * t * F2 + V2 / (4 * t)) / 2 := by
    have hm : ∫ x in W, f x * v.toH1Function.toFun x ≤
        ∫ x in W, ((4 * t) * f x ^ 2 + v.toH1Function.toFun x ^ 2 / (4 * t)) / 2 :=
      integral_mono hifv (((hif.const_mul (4 * t)).add (hiv.div_const (4 * t))).div_const 2)
        (fun x => s5_mul_le_weighted (by positivity))
    rw [integral_div, integral_add (hif.const_mul (4 * t)) (hiv.div_const (4 * t)),
      integral_const_mul, integral_div] at hm
    exact hm
  have hgv' : |∫ x in W, vecDot (g.grad x) (v.toH1Function.grad x)| ≤ (4 * G2 + I / 4) / 2 := by
    have h1 : |∫ x in W, vecDot (g.grad x) (v.toH1Function.grad x)| ≤
        ∫ x in W, |vecDot (g.grad x) (v.toH1Function.grad x)| := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict W) (fun x => vecDot (g.grad x) (v.toH1Function.grad x))
    refine h1.trans ?_
    have hm : ∫ x in W, |vecDot (g.grad x) (v.toH1Function.grad x)| ≤
        ∫ x in W, (4 * vecNormSq (g.grad x) + vecNormSq (v.toH1Function.grad x) / 4) / 2 :=
      integral_mono higv.abs (((hiG.const_mul 4).add (hiI.div_const 4)).div_const 2)
        (fun x => s5_abs_vecDot_le_weighted _ _ (by norm_num))
    rw [integral_div, integral_add (hiG.const_mul 4) (hiI.div_const 4), integral_const_mul,
      integral_div] at hm
    exact hm
  have hI8 : I ≤ 8 / 3 * (t * F2 + G2) := by
    have h3 := le_abs_self (∫ x in W, vecDot (g.grad x) (v.toH1Function.grad x))
    have h4 := neg_abs_le (∫ x in W, vecDot (g.grad x) (v.toH1Function.grad x))
    have hVt : V2 / (4 * t) ≤ I / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [hVI]
    linarith only [hIeq, hfv, hgv', h4, hVt]
  have hU : U2 ≤ 8 * (t * F2 + G2) := by
    have hm : U2 ≤ ∫ x in W, (2 * vecNormSq (v.toH1Function.grad x) + 2 * vecNormSq (g.grad x)) := by
      refine integral_mono_ae hiU ((hiI.const_mul 2).add (hiG.const_mul 2))
        (hgrad.mono fun x hx => ?_)
      have hx' : v.toH1Function.grad x = uh.grad x - g.grad x := hx
      have e : uh.grad x = v.toH1Function.grad x + g.grad x := by
        rw [hx', sub_add_cancel]
      show vecNormSq (uh.grad x) ≤ _
      rw [e]
      exact s5_vecNormSq_add_le _ _
    rw [integral_add (hiI.const_mul 2) (hiG.const_mul 2), integral_const_mul,
      integral_const_mul] at hm
    linarith only [hm, hI8, hG20, mul_nonneg ht0.le hF20]
  set Nf := F2 ^ (1 / 2 : ℝ) with hNf
  set Ng := G2 ^ (1 / 2 : ℝ) with hNg
  set A := U2 ^ (1 / 2 : ℝ) with hA
  have hNf0 : 0 ≤ Nf := Real.rpow_nonneg hF20 _
  have hNg0 : 0 ≤ Ng := Real.rpow_nonneg hG20 _
  have hA0 : 0 ≤ A := Real.rpow_nonneg hU20 _
  have hsq : ∀ {x : ℝ}, 0 ≤ x → (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun {x} hx => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have hA2 : A ^ 2 = U2 := hsq hU20
  have hNf2 : Nf ^ 2 = F2 := hsq hF20
  have hNg2 : Ng ^ 2 = G2 := hsq hG20
  have hAle : A ≤ 3 * (c * L) * Nf + 3 * Ng := by
    have hb0 : 0 ≤ 3 * (c * L) * Nf + 3 * Ng := by positivity
    refine (pow_le_pow_iff_left₀ hA0 hb0 (two_ne_zero)).1 ?_
    have e : (3 * (c * L) * Nf + 3 * Ng) ^ 2 = 9 * (t * F2 + G2) +
        18 * ((c * L) * Nf * Ng) := by
      rw [ht, ← hNf2, ← hNg2]
      ring
    have hx : 0 ≤ (c * L) * Nf * Ng := by positivity
    rw [hA2, e]
    linarith only [hU, hx, ht0, hF20, hG20, mul_nonneg ht0.le hF20]
  rw [p13_eLpNorm_euc hgu, s12_integral_sq_eq hf, p13_eLpNorm_euc hgg,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hAle

/-- **The `H^{-1}` seminorm of the gradient of a Dirichlet solution of the Laplace problem.** -/
theorem s5_hMinus_dirichlet_grad [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → W.Nonempty →
      ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L → ∀ (f : Vec d → ℝ) (g uh : H1Function W),
        s12_IsDirichletSolution (fun _ => (1 : Mat d)) W f g uh →
          s12_hMinusOneVec W uh.grad ≤
            ENNReal.ofReal (C * L ^ 2) * eLpNorm f ⊤ (volume.restrict W) +
              ENNReal.ofReal (C * L) *
                eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict W) := by
  obtain ⟨c₁, hc₁, hE⟩ := s5_dirichlet_energy (d := d)
  obtain ⟨c₂, hc₂, hWb⟩ := s12_wMinusOneBar_le (d := d)
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  refine ⟨d * (3 * c₁ * c₂ + 3 * c₂), by positivity, ?_⟩
  intro W hWo hWd hne z L hL hWL f g uh h
  set M := eLpNorm f ⊤ (volume.restrict W) with hM
  set N := eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict W) with hN
  have hCL2 : 0 < (d : ℝ) * (3 * c₁ * c₂ + 3 * c₂) * L ^ 2 := by positivity
  have hCL : 0 < (d : ℝ) * (3 * c₁ * c₂ + 3 * c₂) * L := by positivity
  by_cases hMt : M = ⊤
  · rw [hMt, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCL2).ne']
    simp
  by_cases hNt : N = ⊤
  · rw [hNt, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCL).ne']
    simp
  have hWt : volume W ≠ ⊤ := by
    simpa using hWd.isFiniteMeasure_restrict_volume.measure_univ_lt_top.ne
  have hW0 : volume W ≠ 0 := (hWo.measure_pos volume hne).ne'
  set a : ℝ≥0∞ := volume W ^ (1 / 2 : ℝ) with ha
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hW0) hWt).ne'
  have hat : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hWt
  have hainv : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha0 hat
  have hf2 := s12_eLpNorm_two_le W f hMt
  have hfm : MemLp f 2 (volume.restrict W) := lt_of_le_of_lt hf2
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hMt) (lt_top_iff_ne_top.2 hat))
  have hg2 := s12_eLpNorm_two_le W (fun x => eucNorm (g.grad x)) hNt
  have hen := hE hWo z hL hWL f hfm g uh h
  have hgu : MemLp uh.grad 2 (volume.restrict W) := uh.grad_memVectorL2
  have hcomp : ∀ i : Fin d, wMinusOneBar W 2 (fun x => uh.grad x i) ≤
      ENNReal.ofReal (c₂ * L) *
        (a⁻¹ * eLpNorm (fun x => eucNorm (uh.grad x)) 2 (volume.restrict W)) := by
    intro i
    have hi : MemLp (fun x => uh.grad x i) 2 (volume.restrict W) := uh.gradMemL2 i
    refine (hWb hWo hW0 hWt z hL hWL _ hi).trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_))
    refine eLpNorm_mono hi.aestronglyMeasurable fun x => ?_
    have h0 : 0 ≤ eucNorm (uh.grad x) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0, Real.norm_eq_abs]
    exact abs_le_eucNorm _ i
  have hsum : s12_hMinusOneVec W uh.grad ≤
      (d : ℝ≥0∞) * (ENNReal.ofReal (c₂ * L) *
        (a⁻¹ * eLpNorm (fun x => eucNorm (uh.grad x)) 2 (volume.restrict W))) := by
    unfold s12_hMinusOneVec
    refine (Finset.sum_le_sum fun i _ => hcomp i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hA : a⁻¹ * eLpNorm (fun x => eucNorm (uh.grad x)) 2 (volume.restrict W) ≤
      ENNReal.ofReal (3 * (c₁ * L)) * M + ENNReal.ofReal 3 * N := by
    have h1 : eLpNorm (fun x => eucNorm (uh.grad x)) 2 (volume.restrict W) ≤
        ENNReal.ofReal (3 * (c₁ * L)) * (M * a) + ENNReal.ofReal 3 * (N * a) :=
      hen.trans (add_le_add (mul_le_mul' le_rfl hf2) (mul_le_mul' le_rfl hg2))
    calc a⁻¹ * eLpNorm (fun x => eucNorm (uh.grad x)) 2 (volume.restrict W)
        ≤ a⁻¹ * (ENNReal.ofReal (3 * (c₁ * L)) * (M * a) + ENNReal.ofReal 3 * (N * a)) :=
          mul_le_mul' le_rfl h1
      _ = (a⁻¹ * a) * (ENNReal.ofReal (3 * (c₁ * L)) * M + ENNReal.ofReal 3 * N) := by ring
      _ = _ := by rw [hainv, one_mul]
  refine hsum.trans ?_
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hA)).trans ?_
  have e : (d : ℝ≥0∞) * (ENNReal.ofReal (c₂ * L) *
      (ENNReal.ofReal (3 * (c₁ * L)) * M + ENNReal.ofReal 3 * N)) =
      ENNReal.ofReal (d * (3 * c₁ * c₂) * L ^ 2) * M + ENNReal.ofReal (d * (3 * c₂) * L) * N := by
    have e1 : ENNReal.ofReal (d * (3 * c₁ * c₂) * L ^ 2) =
        (d : ℝ≥0∞) * (ENNReal.ofReal (c₂ * L) * ENNReal.ofReal (3 * (c₁ * L))) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast d,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    have e2 : ENNReal.ofReal (d * (3 * c₂) * L) =
        (d : ℝ≥0∞) * (ENNReal.ofReal (c₂ * L) * ENNReal.ofReal 3) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast d,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [e1, e2]
    ring
  rw [e]
  refine add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  · have : 0 ≤ (d : ℝ) * (3 * c₂) * L ^ 2 := by positivity
    linarith only [this]
  · have : 0 ≤ (d : ℝ) * (3 * c₁ * c₂) * L := by positivity
    linarith only [this]

end SuperdiffusionCLT.Section7
