/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.DetB
public import SuperdiffusionCLT.Section7.Linfty.CoreB
public import SuperdiffusionCLT.Section7.Linfty.WeakB
public import SuperdiffusionCLT.Section7.Linfty.Energy

/-!
# The deterministic assembly of the `L^∞` proposition

`linf_det`: for the Dirichlet solution `v` with a smooth datum `g̃` and the homogenized solution `v̄`
with the same datum, the sup norm of `v - v̄` and the two weak norms of the gradient and flux
defects are bounded by `linfErr`, from the local gradient bound on the interior cells, the local
`L²` bound of `v - g̃` on the boundary cubes and the sup bounds of the mollified fluxes.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **The deterministic assembly** of the `L^∞` proposition for a smooth datum: from the
local gradient bound `Gb` on the interior cells, the local `L²` bound `Bb` of `v - g̃` on the
boundary cubes, and sup bounds of the mollified fluxes on the interior cells. -/
theorem linf_det [NeZero d] (hd : 2 ≤ d) (M₁ κ ρ : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → r₀ * M₂ ≤ κ → D ≤ ρ * r₀ →
      ∀ {n : ℕ}, 3 * (4 * (3 : ℝ) ^ n) ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
      volume W ≠ 0 → ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L →
      ∀ {θ : ℝ}, 0 ≤ θ →
        (volume (boundaryLayer W (3 * (4 * (3 : ℝ) ^ n))) / volume W) ^ (1 / (2 * (d : ℝ))) ≤
          ENNReal.ofReal θ →
      ∀ {ν Λ s : ℝ} (a : CoeffField d), 0 < ν → ν ≤ Λ → 0 < s → IsEllipticFieldOn ν Λ W a →
      ∀ (v vh : H1Function W) (f : Vec d → ℝ) {gt : Vec d → ℝ}, ContDiff ℝ 1 gt →
        AEStronglyMeasurable f (volume.restrict W) →
        IsWeakSolutionOn a W v f (fun _ => 0) →
        IsWeakSolutionOn (fun _ => s • (1 : Mat d)) W vh f (fun _ => 0) →
        MemH10 W (fun x => v.toFun x - gt x) → MemH10 W (fun x => vh.toFun x - gt x) →
      ∀ {α β α' β' Gb Bb F G : ℝ}, 0 ≤ α → 0 ≤ β → 0 ≤ α' → 0 ≤ β' → 0 ≤ Gb → 0 ≤ Bb → 0 ≤ F →
        0 ≤ G → (∀ᵐ x ∂volume.restrict W, |f x| ≤ F) → (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
        (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
          lpBar (shiftCube (l2b_pt n k) ((n : ℤ) + 1)) 2 (fun x => eucNorm (v.grad x)) ≤
            ENNReal.ofReal Gb) →
        (∀ k : Fin d → ℤ,
          (∃ x ∈ l2b_cell (l2b_pt n k) n ∩ W, Metric.infDist x Wᶜ < 10 * (3 : ℝ) ^ n) →
          eLpNorm (fun x => v.toFun x - gt x) 2
              (volume.restrict (W ∩ shiftCube (l2b_pt n k) ((n : ℤ) + 2))) ≤
            ENNReal.ofReal (((3 : ℝ) ^ (n + 2)) ^ ((d : ℝ) / 2) * Bb)) →
        (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W → ∀ x ∈ l2b_cell (l2b_pt n k) n,
          ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
              (fun y => l2d_flux a W v y - s • l2d_gradc W v y) x‖ ≤ α * Gb + β * F ∧
            ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d) (l2d_flux a W v) x‖ ≤ α' * Gb + β' * F) →
        eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
            hMinusOneVec W (fun x => v.grad x - vh.grad x) +
            hMinusOneVec W (fun x => s⁻¹ • matVecMul (a x) (v.grad x) - vh.grad x) ≤
          ENNReal.ofReal (C * linfErr L ((3 : ℝ) ^ n) s ν Λ ((Λ / ν) ^ (deGiorgiPower d + 1)) θ
            α β α' β' Gb Bb F G) := by
  obtain ⟨Cc, hCc, HC⟩ := linf_core hd M₁ κ ρ
  obtain ⟨Cw, hCw, HW⟩ := linf_weak (d := d) M₁
  obtain ⟨Ce, hCe, HE⟩ := linf_energy (d := d)
  obtain ⟨CI, hCI, HI⟩ := linf_det_int hd
  obtain ⟨CB, hCB, HB⟩ := linf_det_bdry hd
  obtain ⟨Bη, hBη⟩ := (li1_bump_contDiff d).continuous.bounded_above_of_compact_support
    (li1_bump_compact d)
  obtain ⟨hη, hη0, hη1, hηs⟩ := l2c_mollifier_witness d
  have hηB : ∀ w, |li1_bump d w| ≤ Bη := fun w => (Real.norm_eq_abs _).symm.le.trans (hBη w)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set K : ℝ := 1 + CI + CB + (1 + 2 * (d : ℝ)) * Cc * (CB + 8) + 2 * Cw * (4 * Ce + CB + 6)
    with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ CI + CB + (1 + 2 * (d : ℝ)) * Cc * (CB + 8) + 2 * Cw * (4 * Ce + CB + 6) := by
      positivity
    linarith only [this, hK]
  refine ⟨K, hK1, ?_⟩
  intro r₀ W M₂ D hU hκ hρ n h3r hW0 z L hL hWL θ hθ hθl ν Λ s a hν hνΛ hs hEll v vh f gt hgt
    hfm hv hvh hmem hmemh α β α' β' Gb Bb F G hα hβ hα' hβ' hGb0 hBb0 hF hG hfF hgtG hGb hBb
    hflux
  have hWo : IsOpen W := hU.1
  have hWb := l2c_bounded hU
  have hWbd := p14g_isBoundedDomain hU
  have hWm : MeasurableSet W := hWo.measurableSet
  have h0 : (0 : ℝ) < 3 ^ n := by positivity
  have hr : (0 : ℝ) < 4 * 3 ^ n := by positivity
  have hΛ0 : 0 ≤ Λ := hν.le.trans hνΛ
  have hsi : 0 ≤ s⁻¹ := (inv_pos.2 hs).le
  have hν2 : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ 2 / ν := div_nonneg (sq_nonneg _) hν.le
  have hΛν : 1 ≤ Λ / ν := by rw [le_div_iff₀ hν, one_mul]; exact hνΛ
  have hp0 : 0 ≤ deGiorgiPower d := by
    rcases Nat.lt_or_ge d 3 with h3 | h3
    · have : d = 2 := le_antisymm (Nat.le_of_lt_succ h3) hd
      subst this; rw [deGiorgiPower_two]; norm_num
    · rw [deGiorgiPower_of_three_le h3]; positivity
  set q : ℝ := (Λ / ν) ^ (deGiorgiPower d + 1) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hΛν (by linarith only [hp0])
  have hPq : (Λ / ν) ^ deGiorgiPower d ≤ q :=
    Real.rpow_le_rpow_of_exponent_le hΛν (by linarith only)
  set ũ := l2c_ext hWo hWb hr v with hũdef
  have hũ : ∀ y ∈ W, 2 * (3 : ℝ) ^ n ≤ Metric.infDist y Wᶜ → ũ.toFun y = v.toFun y :=
    fun y hy hdy => l2c_ext_toFun hWo hWb hr v hy (by linarith only [hdy])
  have hũl : LocallyIntegrable ũ.toFun volume := l2a_locInt_of_memL2_univ ũ.memL2
  -- the two De Giorgi bounds
  have hint := HI hWo hν hEll f v hv hfm hF hGb0 hfF hGb ũ.toFun hũ
  have hbd := HB hWo hWbd hν hνΛ hEll f v hgt hv hmem hfm hF hG hBb0 hfF hgtG hBb
  set X1 : ℝ := CI * (Λ / ν) ^ deGiorgiPower d *
    ((3 : ℝ) ^ n * Gb + ((3 : ℝ) ^ n) ^ 2 / ν * F) with hX1
  set X2 : ℝ := CB * q * (Bb + ((3 : ℝ) ^ n) ^ 2 / ν * F + (3 : ℝ) ^ n * G) with hX2
  have hX10 : 0 ≤ X1 :=
    mul_nonneg (mul_nonneg hCI.le (Real.rpow_nonneg (div_nonneg hΛ0 hν.le) _))
      (add_nonneg (mul_nonneg h0.le hGb0) (mul_nonneg hν2 hF))
  have hX20 : 0 ≤ X2 :=
    mul_nonneg (mul_nonneg hCB.le (zero_le_one.trans hq1))
      (add_nonneg (add_nonneg hBb0 (mul_nonneg hν2 hF)) (mul_nonneg h0.le hG))
  -- the sup bounds of the mollified fluxes and of the datum term
  have hB1 : ∀ x ∈ W, l2a_cutoff W (4 * 3 ^ n) x ≠ 0 →
      ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d)
        (fun y => l2d_flux a W v y - s • l2d_gradc W v y) x‖ ≤ α * Gb + β * F := by
    intro x _ hx
    obtain ⟨⟨k, hk⟩, hxk⟩ := l2b_exists_cell n (l2b_cutoff_marg hr (by linarith only [h0]) x hx)
    exact (hflux k hk x hxk).1
  have hB5 : ∀ x ∈ W, lipGradient (l2a_cutoff W (4 * 3 ^ n)) x ≠ 0 →
      ‖a16_mollify d ((3 : ℝ) ^ n) (li1_bump d) (l2d_flux a W v) x‖ ≤ α' * Gb + β' * F := by
    intro x _ hx
    have hxA : x ∈ l2b_layerA W (4 * 3 ^ n) := by
      by_contra hc; exact hx (l2b_lipGradient_zero_off hr x hc)
    obtain ⟨⟨k, hk⟩, hxk⟩ := l2b_exists_cell n (l2b_layerA_marg (by linarith only [h0]) x hxA)
    exact (hflux k hk x hxk).2
  have hB2 : ∀ x ∈ W, lipGradient (l2a_cutoff W (4 * 3 ^ n)) x ≠ 0 →
      |l2a_moll d ((3 : ℝ) ^ n) (li1_bump d) ũ.toFun x - gt x| ≤ X2 + 3 ^ n * G :=
    linf_det_B2 h0 hũl hgt hgtG hũ hbd
  have hB10 : 0 ≤ α * Gb + β * F := add_nonneg (mul_nonneg hα hGb0) (mul_nonneg hβ hF)
  have hB50 : 0 ≤ α' * Gb + β' * F := add_nonneg (mul_nonneg hα' hGb0) (mul_nonneg hβ' hF)
  have hB20 : 0 ≤ X2 + 3 ^ n * G := add_nonneg hX20 (mul_nonneg h0.le hG)
  -- the crude energies
  have hEv := HE hWo hWbd z hL hWL hW0 hν hEll v hgt hfm hv hmem hF hG hfF (fun x _ => hgtG x)
  set Ev : ℝ := Ce * (Λ / ν * G + L / ν * F) with hEvdef
  have hEv0 : 0 ≤ Ev :=
    mul_nonneg hCe.le (add_nonneg (mul_nonneg (div_nonneg hΛ0 hν.le) hG)
      (mul_nonneg (div_nonneg hL.le hν.le) hF))
  have hflux2 : MemVectorL2 W (fun x => matVecMul (a x) (v.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.grad_memVectorL2
  have hEa : lpBar W 2 (fun x => eucNorm (matVecMul (a x) (v.grad x))) ≤
      ENNReal.ofReal (Λ * Ev) := by
    have hpt : ∀ᵐ x ∂(((volume W)⁻¹) • volume.restrict W),
        ‖eucNorm (matVecMul (a x) (v.grad x))‖ ≤ Λ * ‖eucNorm (v.grad x)‖ := by
      refine Measure.ae_smul_measure ?_ _
      filter_upwards [ae_restrict_mem hWm] with x hx
      have h1 := linf_vecNormSq_matVecMul_le (hEll.2 x hx) (v.grad x)
      have e0 : ∀ ξ : Vec d, ‖eucNorm ξ‖ = eucNorm ξ := fun ξ =>
        Real.norm_of_nonneg (Real.sqrt_nonneg _)
      rw [e0, e0]
      unfold eucNorm
      rw [← Real.sqrt_sq hΛ0, ← Real.sqrt_mul (sq_nonneg Λ)]
      exact Real.sqrt_le_sqrt h1
    calc lpBar W 2 (fun x => eucNorm (matVecMul (a x) (v.grad x)))
        ≤ ENNReal.ofReal Λ * lpBar W 2 (fun x => eucNorm (v.grad x)) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((p13_continuous_eucNorm.comp_aestronglyMeasurable
            (show MemLp _ 2 (volume.restrict W) from hflux2).aestronglyMeasurable).smul_measure _)
            hpt 2
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal Ev := by gcongr
      _ = ENNReal.ofReal (Λ * Ev) := (ENNReal.ofReal_mul hΛ0).symm
  -- the comparison function against the homogenized solution
  obtain ⟨φ, hφeq, hφ⟩ := HC hU hκ hρ (n := n) hr h3r (by linarith only [h0])
    (by linarith only [h0]) hW0 z hL hWL (η := li1_bump d) (Bη := Bη) hη hηB hη0 hη1 hηs hθl a hs
    v vh f hgt hfm hflux2 hv hvh hmem hmemh (B1 := α * Gb + β * F) (B2 := X2 + 3 ^ n * G)
    (B5 := α' * Gb + β' * F) hB10 hB20 hB50 hF hG hfF (fun x _ => hgtG x) hB1 hB2 hB5
  -- the two weak norms of `v` against the comparison function
  obtain ⟨hw1, hw2⟩ := HW hU (n := n) hr h3r (by linarith only [h0]) (by linarith only [h0]) hW0
    z hL hWL (η := li1_bump d) (Bη := Bη) hη hηB hη0 hη1 hηs a hs v hgt hflux2 hmem
    (B1 := α * Gb + β * F) (B2 := X2 + 3 ^ n * G) (G := G) (Ev := Ev) (Ea := Λ * Ev) hB10 hB20 hG
    hEv0 (mul_nonneg hΛ0 hEv0) (fun x _ => hgtG x) hEv hEa hB1 hB2
  set w := l2d_w hU.1 (l2c_bounded hU) hr (pow_pos (by norm_num : (0 : ℝ) < 3) n) hη hηs
    (l2c_ext hU.1 (l2c_bounded hU) hr v) (li1_h1 hU.1 (p14g_isBoundedDomain hU) hgt) with hwdef
  -- the sup bound of `w - v̄`
  set Xφ : ℝ := Cc * L * (s⁻¹ * (α * Gb + β * F) + θ * ((X2 + 3 ^ n * G) / (4 * 3 ^ n) + G) +
    s⁻¹ * (4 * 3 ^ n) * F + θ * (s⁻¹ * (α' * Gb + β' * F))) with hXφ
  have hQa : 0 ≤ s⁻¹ * (α * Gb + β * F) := mul_nonneg hsi hB10
  have hQb : 0 ≤ (X2 + 3 ^ n * G) / (4 * 3 ^ n) + G := add_nonneg (div_nonneg hB20 hr.le) hG
  have hQc : 0 ≤ s⁻¹ * (4 * 3 ^ n) * F := mul_nonneg (mul_nonneg hsi hr.le) hF
  have hQe : 0 ≤ s⁻¹ * (α' * Gb + β' * F) := mul_nonneg hsi hB50
  have hXφ0 : 0 ≤ Xφ :=
    mul_nonneg (mul_nonneg hCc.le hL.le)
      (add_nonneg (add_nonneg (add_nonneg hQa (mul_nonneg hθ hQb)) hQc) (mul_nonneg hθ hQe))
  have hφinf : eLpNorm φ.toH1Function.toFun ⊤ (volume.restrict W) ≤ ENNReal.ofReal Xφ := by
    refine le_self_add.trans (hφ.trans (le_of_eq ?_))
    exact linf_det_ofReal_core (mul_nonneg hCc.le hL.le) hQa hQb hQc hQe hθ
  have hφae := linf_det_ae_of_eLpNorm_top φ.toH1Function.memL2.aestronglyMeasurable hXφ0 hφinf
  have hφfun : ∀ x, φ.toH1Function.toFun x = w.toFun x - vh.toFun x := fun x => by
    rw [hφeq, H1Function.sub_toFun]
  have hφgrad : φ.toH1Function.grad = fun x => w.grad x - vh.grad x := by
    rw [hφeq, H1Function.sub_grad]
  -- the sup bound of `v - w`
  have hvw : ∀ᵐ y ∂volume.restrict W, |v.toFun y - w.toFun y| ≤ X1 + X2 := by
    rw [ae_restrict_iff' hWm]
    filter_upwards [hint, hbd] with y hy1 hy2 hyW
    have ew : w.toFun y = l2a_cutoff W (4 * 3 ^ n) y *
        l2a_moll d ((3 : ℝ) ^ n) (li1_bump d) ũ.toFun y +
        (1 - l2a_cutoff W (4 * 3 ^ n) y) * gt y := rfl
    rw [ew]
    refine linf_det_mix (l2a_cutoff_nonneg _ _ _) (l2a_cutoff_le_one _ _ _) hX10 hX20 hy1
      (fun hζ => hy2 hyW ?_)
    by_contra hc
    exact hζ (l2a_cutoff_eq_one hr (by linarith only [not_lt.1 hc, h0]))
  have hvvh : ∀ᵐ y ∂volume.restrict W, ‖v.toFun y - vh.toFun y‖ ≤ X1 + X2 + Xφ := by
    filter_upwards [hvw, hφae] with y h1 h2
    rw [hφfun] at h2
    rw [Real.norm_eq_abs]
    calc |v.toFun y - vh.toFun y| = |(v.toFun y - w.toFun y) + (w.toFun y - vh.toFun y)| := by
          ring_nf
      _ ≤ |v.toFun y - w.toFun y| + |w.toFun y - vh.toFun y| := abs_add_le _ _
      _ ≤ X1 + X2 + Xφ := by linarith only [h1, h2]
  have hT1 : eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) ≤
      ENNReal.ofReal (X1 + X2 + Xφ) := by
    have hm : AEStronglyMeasurable (fun x => v.toFun x - vh.toFun x) (volume.restrict W) :=
      v.memL2.aestronglyMeasurable.sub vh.memL2.aestronglyMeasurable
    rw [eLpNorm_exponent_top hm]
    exact eLpNormEssSup_le_of_ae_bound hvvh
  -- the weak norm of `∇(w - v̄)`
  have hgφ : hMinusOneVec W (fun x => w.grad x - vh.grad x) ≤ ENNReal.ofReal (d * Xφ) := by
    rw [← hφgrad]
    exact linf_hMinus_grad_le_sup hWo hWbd hW0 φ.toH1Function hXφ0 hφae
  have hPφ : s12_PairInt W (fun x => w.grad x - vh.grad x) := by
    rw [← hφgrad]; exact s12_pairInt_grad _
  have hPv : s12_PairInt W (fun x => v.grad x - w.grad x) := by
    have := s12_pairInt_grad (v - w)
    rwa [H1Function.sub_grad] at this
  have hPa : s12_PairInt W (fun x => s⁻¹ • matVecMul (a x) (v.grad x) - w.grad x) := by
    refine s12_pairInt_of_gradMemL2On fun i => ?_
    have h1 : MemLp (fun x => matVecMul (a x) (v.grad x) i) 2 (volume.restrict W) :=
      MeasureTheory.memLp_pi_iff.1 hflux2 i
    have h2 := (h1.const_mul s⁻¹).sub (w.gradMemL2 i)
    exact h2
  have hT2 : hMinusOneVec W (fun x => v.grad x - vh.grad x) ≤
      ENNReal.ofReal (Cw * (4 * 3 ^ n * (Ev + G) + (X2 + 3 ^ n * G))) +
        ENNReal.ofReal (d * Xφ) := by
    have e : (fun x => v.grad x - vh.grad x) =
        fun x => (v.grad x - w.grad x) + (w.grad x - vh.grad x) := by
      funext x; abel
    rw [e]
    exact (s12_hMinusOneVec_add_le W hPv hPφ).trans (add_le_add hw1 hgφ)
  have hT3 : hMinusOneVec W (fun x => s⁻¹ • matVecMul (a x) (v.grad x) - vh.grad x) ≤
      ENNReal.ofReal (Cw * (L * (s⁻¹ * (α * Gb + β * F)) +
        4 * 3 ^ n * (s⁻¹ * (Λ * Ev) + Ev + G) + (X2 + 3 ^ n * G))) +
        ENNReal.ofReal (d * Xφ) := by
    have e : (fun x => s⁻¹ • matVecMul (a x) (v.grad x) - vh.grad x) =
        fun x => (s⁻¹ • matVecMul (a x) (v.grad x) - w.grad x) + (w.grad x - vh.grad x) := by
      funext x; abel
    rw [e]
    exact (s12_hMinusOneVec_add_le W hPa hPφ).trans (add_le_add hw2 hgφ)
  -- the collection
  have hA0 : 0 ≤ Cw * (4 * 3 ^ n * (Ev + G) + (X2 + 3 ^ n * G)) :=
    mul_nonneg hCw.le (add_nonneg (mul_nonneg hr.le (add_nonneg hEv0 hG)) hB20)
  have hB0 : 0 ≤ Cw * (L * (s⁻¹ * (α * Gb + β * F)) + 4 * 3 ^ n * (s⁻¹ * (Λ * Ev) + Ev + G) +
      (X2 + 3 ^ n * G)) :=
    mul_nonneg hCw.le (add_nonneg (add_nonneg (mul_nonneg hL.le hQa)
      (mul_nonneg hr.le (add_nonneg (add_nonneg (mul_nonneg hsi (mul_nonneg hΛ0 hEv0)) hEv0) hG)))
      hB20)
  have hdX : 0 ≤ (d : ℝ) * Xφ := mul_nonneg hd0 hXφ0
  have hreal := linf_det_real (L := L) (h := (3 : ℝ) ^ n) (s := s) (ν := ν) (Λ := Λ) (q := q)
    (θ := θ) (α := α) (β := β) (α' := α') (β' := β') (Gb := Gb) (Bb := Bb) (F := F) (G := G)
    (P := (Λ / ν) ^ deGiorgiPower d) (CI := CI) (CB := CB) (Cc := Cc) (Cw := Cw) (Ce := Ce)
    (D := d) (X1 := X1) (X2 := X2) (B2 := X2 + 3 ^ n * G) (Ev := Ev) (Xφ := Xφ) hL h0 hs hν hΛ0
    hq1 hθ hα hβ hα' hβ' hGb0 hBb0 hF hG hPq hCI.le hCB.le hCc.le hCw.le hCe.le hd0
    (by rw [hX1, mul_assoc]) rfl rfl rfl rfl
  calc eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
          hMinusOneVec W (fun x => v.grad x - vh.grad x) +
          hMinusOneVec W (fun x => s⁻¹ • matVecMul (a x) (v.grad x) - vh.grad x)
      ≤ ENNReal.ofReal (X1 + X2 + Xφ) +
          (ENNReal.ofReal (Cw * (4 * 3 ^ n * (Ev + G) + (X2 + 3 ^ n * G))) +
            ENNReal.ofReal (d * Xφ)) +
          (ENNReal.ofReal (Cw * (L * (s⁻¹ * (α * Gb + β * F)) +
            4 * 3 ^ n * (s⁻¹ * (Λ * Ev) + Ev + G) + (X2 + 3 ^ n * G))) +
            ENNReal.ofReal (d * Xφ)) := add_le_add (add_le_add hT1 hT2) hT3
    _ = ENNReal.ofReal (X1 + X2 + Xφ +
          (Cw * (4 * 3 ^ n * (Ev + G) + (X2 + 3 ^ n * G)) + d * Xφ) +
          (Cw * (L * (s⁻¹ * (α * Gb + β * F)) + 4 * 3 ^ n * (s⁻¹ * (Λ * Ev) + Ev + G) +
            (X2 + 3 ^ n * G)) + d * Xφ)) := by
      have hS0 : 0 ≤ X1 + X2 + Xφ := add_nonneg (add_nonneg hX10 hX20) hXφ0
      rw [ENNReal.ofReal_add (add_nonneg hS0 (add_nonneg hA0 hdX)) (add_nonneg hB0 hdX),
        ENNReal.ofReal_add hS0 (add_nonneg hA0 hdX), ENNReal.ofReal_add hA0 hdX,
        ENNReal.ofReal_add hB0 hdX]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The identity field is elliptic with constants `1, 1` on every measurable set. -/
theorem linf_det_isEllipticFieldOn_one {W : Set (Vec d)} (hW : MeasurableSet W) :
    IsEllipticFieldOn 1 1 W (fun _ => (1 : Mat d)) := by
  classical
  refine ⟨?_, fun x _ => isEllipticMatrix_one⟩
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact Measurable.ite hW measurable_const measurable_const

/-- Satisfiability of `linf_det`: zero data, the identity field and `s = 1` on a dilate of the unit
ball, at the scale `n = 0`, with all bounds equal to zero and `θ = 1`. -/
example : True := by
  obtain ⟨W, r₀, M₁, M₂, D, hU, h3r, hW0⟩ := l2d_witness_domain4 (d := 2)
  have hr0 : 0 < r₀ := hU.2.1
  obtain ⟨C, -, H⟩ := linf_det (d := 2) le_rfl M₁ (r₀ * M₂) (D / r₀)
  have hWb := l2c_bounded hU
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec 2)).1 hWb
  have hWL : W ⊆ axisCube (fun _ => -(|ρ| + 1)) (2 * (|ρ| + 1)) := by
    intro x hx j _
    have h1 := hρ hx
    rw [mem_closedBall_zero_iff] at h1
    have h2 : |x j| ≤ ‖x‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x j
    have h3 := abs_le.1 h2
    have h4 := le_abs_self ρ
    simp only [Set.mem_Ioo]
    constructor <;> linarith only [h1, h3.1, h3.2, h4, abs_nonneg ρ]
  have h3r' : 3 * (4 * (3 : ℝ) ^ 0) ≤
      r₀ / (3 * (((2 : ℕ) : ℝ) + (1 + ((2 : ℕ) : ℝ)) * max M₁ 0) + 4) := by
    simpa using h3r
  have hθl : (volume (boundaryLayer W (3 * (4 * (3 : ℝ) ^ 0))) / volume W) ^
      (1 / (2 * ((2 : ℕ) : ℝ))) ≤ ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_one]
    refine ENNReal.rpow_le_one ?_ (by positivity)
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact measure_mono fun x hx => hx.1
  have hz : ∀ x, (0 : H1Function W).grad x = 0 := fun _ => rfl
  have _ := H hU le_rfl (div_mul_cancel₀ D hr0.ne').ge (n := 0) h3r' hW0
    (fun _ => -(|ρ| + 1)) (L := 2 * (|ρ| + 1)) (by positivity) hWL (θ := 1) zero_le_one hθl
    (ν := 1) (Λ := 1) (s := 1) (fun _ => (1 : Mat 2)) one_pos le_rfl one_pos
    (linf_det_isEllipticFieldOn_one hU.1.measurableSet) (0 : H1Function W) (0 : H1Function W)
    (fun _ => 0) (gt := fun _ => 0) contDiff_const aestronglyMeasurable_const
    (fun φ => by simp [vecDot, matVecMul, hz]) (fun φ => by simp [vecDot, matVecMul, hz])
    ⟨0, by funext x; simp; rfl⟩ ⟨0, by funext x; simp; rfl⟩
    (α := 0) (β := 0) (α' := 0) (β' := 0) (Gb := 0) (Bb := 0) (F := 0) (G := 0) le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Filter.Eventually.of_forall fun x => by simp)
    (fun x => by simp) (fun k _ => by simp [lpBar, eucNorm, vecNormSq, vecDot, hz])
    (fun k _ => by simp)
    (fun k _ x _ => by
      simp [l2d_flux, l2d_gradc, l2d_matVecMul_zero, Set.indicator_zero', l2d_mollify_zero, hz])
  trivial

end SuperdiffusionCLT.Section7
