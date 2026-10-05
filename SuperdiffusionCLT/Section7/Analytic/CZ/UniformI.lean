/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformH

/-!
# Global `W^{1,p}` estimate on uniformly `C^{1,1}` domains (divergence form, `p ≥ 2`)

`cz_unif_div`: for `2 ≤ p < ∞` and a uniformly `C^{1,1}` domain `U` with chart data `(r, M₁, M₂, D)`,
`r M₂ ≤ κ`, `D ≤ ρ r`, the zero-trace solution `φ ∈ H¹₀(U)` of `-Δφ = -∇·F` (tested against `H¹₀(U)`)
satisfies `‖∇φ‖_{L̲^p(U)} ≤ C ‖F‖_{L̲^p(U)}`, with `C` depending only on `d, p, M₁, κ, ρ`.

The proof covers `U` by a grid of cells of side comparable to `r`; a cell near the frontier is
controlled by the boundary estimate, any other cell by the interior estimate; the local estimates are
summed with bounded overlap, and the lower-order terms are removed by the energy bound and the
Poincare inequality.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem p13_scale_exists {τ : ℝ} (hτ : 0 < τ) :
    ∃ m : ℤ, (3 : ℝ) ^ m ≤ τ ∧ τ < 3 * (3 : ℝ) ^ m := by
  obtain ⟨n, h1, h2⟩ := exists_mem_Ico_zpow hτ (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, h1, ?_⟩
  rw [zpow_add_one₀ (by norm_num)] at h2
  linarith only [h2]

/-- The elementary inequalities between the scales. -/
theorem p13_scales {K c ℓi : ℝ} (hK : 1 ≤ K) (hc : 32 * K ≤ c) (hℓ : 0 < ℓi) :
    ℓi ≤ c * ℓi / (4 * K) / 2 ∧ 8 * ℓi ≤ c * ℓi / (4 * K) := by
  have hK0 : 0 < K := by linarith only [hK]
  have h8 : 8 * ℓi ≤ c * ℓi / (4 * K) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hc hℓ.le
    linarith only [this]
  exact ⟨by linarith only [h8, hℓ], h8⟩

theorem p13_const_int {Λi Λb Lii Lib : ℝ≥0∞} {Ci A c e : ℝ} (hCi : 0 ≤ Ci)
    (he : 0 ≤ e) (hΛ : Λi ≤ ENNReal.ofReal e * Λb) (hL : Lii = ENNReal.ofReal c * Lib)
    (hA1 : Ci * e ≤ A) (hA2 : Ci * e * c ≤ A) :
    ENNReal.ofReal Ci * Λi ≤ ENNReal.ofReal A * Λb ∧
      ENNReal.ofReal Ci * (Λi * Lii) ≤ ENNReal.ofReal A * (Λb * Lib) := by
  constructor
  · calc ENNReal.ofReal Ci * Λi ≤ ENNReal.ofReal Ci * (ENNReal.ofReal e * Λb) :=
          mul_le_mul_right hΛ _
      _ = ENNReal.ofReal (Ci * e) * Λb := by rw [ENNReal.ofReal_mul hCi, mul_assoc]
      _ ≤ ENNReal.ofReal A * Λb := mul_le_mul_left (ENNReal.ofReal_le_ofReal hA1) _
  · calc ENNReal.ofReal Ci * (Λi * Lii)
        ≤ ENNReal.ofReal Ci * ((ENNReal.ofReal e * Λb) * (ENNReal.ofReal c * Lib)) := by
          rw [hL]; exact mul_le_mul_right (mul_le_mul_left hΛ _) _
      _ = ENNReal.ofReal (Ci * e * c) * (Λb * Lib) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCi]; ring
      _ ≤ ENNReal.ofReal A * (Λb * Lib) := mul_le_mul_left (ENNReal.ofReal_le_ofReal hA2) _

theorem p13_rpow_le_max {X θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ENNReal.ofReal X ^ θ ≤ ENNReal.ofReal (max 1 X) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 X) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  calc ENNReal.ofReal X ^ θ ≤ ENNReal.ofReal (max 1 X) ^ θ :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_max_right _ _)) hθ0
    _ ≤ ENNReal.ofReal (max 1 X) ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h1 hθ1
    _ = _ := ENNReal.rpow_one _

theorem p13_natrpow_le {N : ℕ} (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ≤ 1) :
    (N : ℝ≥0∞) ^ θ ≤ ENNReal.ofReal (N : ℝ) := by
  have h1 : (1 : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by exact_mod_cast hN
  calc (N : ℝ≥0∞) ^ θ ≤ (N : ℝ≥0∞) ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h1 hθ
    _ = ENNReal.ofReal (N : ℝ) := by rw [ENNReal.rpow_one, ENNReal.ofReal_natCast]

/-- **Global `W^{1,p}` estimate on uniformly `C^{1,1}` domains, divergence form, `p ≥ 2`.** -/
theorem cz_unif_div [NeZero d] (hd : 2 ≤ d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤)
    (M₁ κ ρ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Set (Vec d)} {r M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
      r * M₂ ≤ κ → D ≤ ρ * r → ∀ (F : Vec d → Vec d) (φ : H10Function U),
        MemVectorL2 U F →
        IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function (fun _ => 0) F →
        lpBar U p φ.toH1Function.grad ≤ ENNReal.ofReal C * lpBar U p F := by
  set P : ℝ := p.toReal with hPdef
  have hpP : p = ENNReal.ofReal P := (ENNReal.ofReal_toReal hpt.ne).symm
  have hP : 2 ≤ P := by
    have := ENNReal.toReal_mono hpt.ne hp2
    simpa using this
  have hP0 : 0 < P := by linarith only [hP]
  obtain ⟨εb, Cb, K, hεb, hCb, hK, Hb⟩ := p13_bdy_local hd hP M₁
  obtain ⟨Ci, hCi, Hi⟩ := p13_int_local hd hP
  obtain ⟨c₀, hc₀, Hpo⟩ := p13_poincare (d := d)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (32 * K) (by norm_num : (1 : ℝ) < 3)
  set cL : ℝ := (2 * (d : ℝ) ^ 2 + 4 * (d : ℝ) ^ 3 * M₁) *
    (2 * (1 + (d : ℝ)) * ((1 + (1 + (d : ℝ)) * M₁) * ((d : ℝ) * (1 + 2 * (d : ℝ) * M₁)))) with hcL
  set κ' : ℝ := max κ 0 with hκ'
  set θ₀ : ℝ := min (1 / K) (εb / (|cL| * κ' + 1)) with hθ₀
  set cc : ℝ := (3 : ℝ) ^ j with hcc
  set A : ℝ := max Cb Ci * cc ^ d * cc with hA
  set Nn : ℕ := (⌈4 * (K + 1) * cc⌉₊ + 1) ^ d with hNn
  set Zr : ℝ := 6 * max (ρ + 1) 0 / θ₀ with hZr
  set Z : ℝ := max 1 (Zr ^ d) with hZ
  set Y : ℝ := c₀ * Zr with hY
  have hK0 : 0 < K := by linarith only [hK]
  have hκ'0 : 0 ≤ κ' := le_max_right _ _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hden1 : 0 < |cL| * κ' + 1 := add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg _) hκ'0) one_pos
  have hθ₀ : 0 < θ₀ := lt_min (one_div_pos.2 hK0) (div_pos hεb hden1)
  have hZr0 : 0 ≤ Zr := div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hθ₀.le
  have hcc1 : 1 ≤ cc := one_le_pow₀ (by norm_num)
  have hcc0 : 0 < cc := by linarith only [hcc1]
  have hAp : 0 < A := by
    have : 0 < max Cb Ci := lt_max_of_lt_left hCb
    exact mul_pos (mul_pos this (pow_pos hcc0 d)) hcc0
  have hN1 : 1 ≤ Nn := Nat.one_le_pow _ _ (by omega)
  have hNr : (0 : ℝ) < (Nn : ℝ) := by exact_mod_cast hN1
  have hZ1 : 1 ≤ Z := le_max_left _ _
  have hY0 : 0 ≤ Y := mul_nonneg hc₀.le hZr0
  have hZ0 : 0 ≤ Z := by linarith only [hZ1]
  have hd1' : (0 : ℝ) ≤ (d : ℝ) + 1 := add_nonneg hd0 zero_le_one
  have hCfpos : 0 < 4 * A * (Nn : ℝ) * (Z * ((d : ℝ) + 1) * (1 + Y) + 1) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hAp) hNr)
      (add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg hZ0 hd1') (add_nonneg zero_le_one hY0)) one_pos)
  refine ⟨4 * A * (Nn : ℝ) * (Z * ((d : ℝ) + 1) * (1 + Y) + 1), hCfpos, ?_⟩
  intro U r M₂ D hUc hκ hD F φ hF hw
  obtain ⟨hUo, hr, hdiam, hchart⟩ := hUc
  set Cf : ℝ := 4 * A * (Nn : ℝ) * (Z * ((d : ℝ) + 1) * (1 + Y) + 1) with hCf
  have hCf0 : 0 < Cf := hCfpos
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp2; exact absurd hp2 (by norm_num)
  have hlp : ∀ g : Vec d → Vec d, lpBar U p g =
      ((volume U)⁻¹) ^ (1 / p).toReal * eLpNorm g p (volume.restrict U) := fun g => by
    unfold lpBar
    rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hpt.ne]
    rfl
  suffices hcore : eLpNorm φ.toH1Function.grad p (volume.restrict U) ≤
      ENNReal.ofReal Cf * eLpNorm F p (volume.restrict U) by
    rw [hlp, hlp]
    calc ((volume U)⁻¹) ^ (1 / p).toReal * eLpNorm φ.toH1Function.grad p (volume.restrict U)
        ≤ ((volume U)⁻¹) ^ (1 / p).toReal * (ENNReal.ofReal Cf * eLpNorm F p (volume.restrict U)) :=
          mul_le_mul_right hcore _
      _ = _ := by ring
  by_cases hU0 : U = ∅
  · subst hU0; simp
  obtain ⟨x₁, hx₁⟩ := Set.nonempty_iff_ne_empty.2 hU0
  by_cases hTF : eLpNorm F p (volume.restrict U) = ⊤
  · rw [hTF, ENNReal.mul_top (by simpa using hCf0)]
    exact le_top
  have hFmem : MemLp F (ENNReal.ofReal P) (volume.restrict U) :=
    (by rw [← hpP]; exact lt_top_iff_ne_top.2 hTF)
  obtain ⟨x₀', hx₀'⟩ := layerPoincare_frontier_nonempty hdiam hU0
  obtain ⟨e', ψ', he', hψ', hb1', hb2', hch'⟩ := hchart x₀' hx₀'
  have hM₂ : 0 ≤ M₂ := by
    have hz : (0 : ℝ) < ‖(0 : Vec d) - (fun _ => (1 : ℝ))‖ := by
      rw [norm_pos_iff]
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    have := hb2' 0 (fun _ => (1 : ℝ))
    exact le_of_mul_le_mul_right (by simpa using (norm_nonneg _).trans this) hz
  obtain ⟨m, hm1, hm2⟩ := p13_scale_exists (mul_pos hr hθ₀)
  set ℓb : ℝ := (3 : ℝ) ^ m with hℓb
  have hℓb0 : 0 < ℓb := zpow_pos (by norm_num) m
  have hθK : θ₀ * K ≤ 1 := (le_div_iff₀ hK0).1 (min_le_left _ _)
  have hθε : θ₀ * (|cL| * κ' + 1) ≤ εb := (le_div_iff₀ hden1).1 (min_le_right _ _)
  have hKr : K * ℓb ≤ r := by
    have h1 : K * ℓb ≤ K * (r * θ₀) := mul_le_mul_of_nonneg_left hm1 hK0.le
    have h2 : K * (r * θ₀) = r * (θ₀ * K) := by ring
    have h3 : r * (θ₀ * K) ≤ r * 1 := mul_le_mul_of_nonneg_left hθK hr.le
    linarith only [h1, h2, h3]
  have hflat : flattenLipConst d M₁ M₂ * ℓb ≤ εb := by
    have hfl : flattenLipConst d M₁ M₂ = cL * M₂ := by
      unfold flattenLipConst; rw [hcL]; ring
    have h1 : M₂ * ℓb ≤ M₂ * (r * θ₀) := mul_le_mul_of_nonneg_left hm1 hM₂
    have h2 : M₂ * (r * θ₀) = (r * M₂) * θ₀ := by ring
    have h3 : (r * M₂) * θ₀ ≤ κ' * θ₀ :=
      mul_le_mul_of_nonneg_right (hκ.trans (le_max_left _ _)) hθ₀.le
    have h4 : cL * (M₂ * ℓb) ≤ |cL| * (M₂ * ℓb) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hM₂ hℓb0.le)
    have h5 : |cL| * (M₂ * ℓb) ≤ |cL| * (κ' * θ₀) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, h2, h3]) (abs_nonneg _)
    have h6 : |cL| * (κ' * θ₀) + θ₀ = θ₀ * (|cL| * κ' + 1) := by ring
    rw [hfl]
    exact calc cL * M₂ * ℓb = cL * (M₂ * ℓb) := by ring
      _ ≤ εb := by linarith only [h4, h5, h6, hθε, hθ₀]
  set ℓi : ℝ := (3 : ℝ) ^ (m - (j : ℤ)) with hℓi
  have hℓi0 : 0 < ℓi := zpow_pos (by norm_num) _
  have hℓic : ℓi * cc = ℓb := by
    rw [hℓi, hcc, hℓb, zpow_sub₀ (by norm_num), zpow_natCast]
    exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))
  have hcc32 : 32 * K ≤ cc := hj.le
  obtain ⟨hs1, hs8⟩ := p13_scales hK hcc32 hℓi0
  rw [mul_comm cc ℓi, hℓic] at hs1 hs8
  have hℓiℓb : ℓi ≤ ℓb := by
    have := mul_le_mul_of_nonneg_left hcc1 hℓi0.le
    linarith only [this, hℓic]
  set R₀ : ℝ := ℓb / (4 * K) with hR₀
  set ρ₁ : ℝ := R₀ / 2 with hρ₁def
  set s : ℝ := ℓi / 2 with hsdef
  set R : ℝ := (K + 1) * ℓb with hRdef
  have hρ₁ : 0 < ρ₁ := by
    have : 0 < R₀ := div_pos hℓb0 (mul_pos (by norm_num) hK0)
    exact div_pos this two_pos
  have hs : 0 < s := div_pos hℓi0 two_pos
  have hsR : ρ₁ + s ≤ R₀ := by linarith only [hs8, hℓi0, hρ₁def, hsdef]
  have hR₀ℓ : R₀ ≤ ℓb := by
    rw [hR₀]
    exact div_le_self hℓb0.le (by linarith only [hK])
  have hRw : K * ℓb + ρ₁ + s / 2 ≤ R := by
    have hKℓ : 0 ≤ K * ℓb := mul_nonneg hK0.le hℓb0.le
    have : (K + 1) * ℓb = K * ℓb + ℓb := by ring
    linarith only [hR₀ℓ, hℓiℓb, hρ₁def, hsdef, this, hℓb0, hℓi0]
  have hρℓ : 3 * ℓi / 4 ≤ ρ₁ := by linarith only [hs8, hρ₁def, hℓi0]
  have hRi : ℓi / 2 ≤ R := by
    have hKℓ : 0 ≤ K * ℓb := mul_nonneg hK0.le hℓb0.le
    have : (K + 1) * ℓb = K * ℓb + ℓb := by ring
    linarith only [hℓiℓb, this, hKℓ, hℓi0, hRdef]
  have hsl : s ≤ ℓi / 2 := le_rfl
  have hθ0 : (0 : ℝ) ≤ 1 / 2 - 1 / P := by
    have : 1 / P ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hP
    linarith only [this]
  have hθ1 : (1 / 2 - 1 / P : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / P := one_div_nonneg.2 hP0.le
    linarith only [this]
  set Λb : ℝ≥0∞ := ENNReal.ofReal ((ℓb ^ d)⁻¹) ^ (1 / 2 - 1 / P : ℝ) with hΛb
  set Lib : ℝ≥0∞ := ENNReal.ofReal ℓb⁻¹ with hLib
  have hAC : max Cb Ci ≤ A := by
    have h1 : 1 ≤ cc ^ d * cc := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hcc1) hcc1
    have h2 : A = max Cb Ci * (cc ^ d * cc) := by rw [hA]; ring
    rw [h2]
    exact le_mul_of_one_le_right (le_trans hCb.le (le_max_left Cb Ci)) h1
  have hcell : ∀ k : Fin d → ℤ,
      (U ∩ {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| ≤ s / 2}).Nonempty →
      ∃ B : Set (Vec d), MeasurableSet B ∧ B ⊆ U ∧ (∀ y ∈ B, ∀ i, |y i - (k i : ℝ) * s| < R) ∧
        eLpNorm φ.toH1Function.grad (ENNReal.ofReal P)
            (volume.restrict (U ∩ {y : Vec d | ∀ i, |y i - (k i : ℝ) * s| ≤ s / 2})) ≤
          (ENNReal.ofReal A * Λb) * eLpNorm φ.toH1Function.grad 2 (volume.restrict B) +
            (ENNReal.ofReal A * (Λb * Lib)) * eLpNorm φ.toH1Function.toFun 2 (volume.restrict B) +
              ENNReal.ofReal A * eLpNorm F (ENNReal.ofReal P) (volume.restrict B) := by
    rintro k ⟨x, hxU, hxk⟩
    by_cases hnear : ∃ x₀ ∈ frontier U, dist x x₀ < ρ₁
    · obtain ⟨x₀, hx₀F, hdist⟩ := hnear
      obtain ⟨e, ψ, he, hψ, hb1, hb2, hch⟩ := hchart x₀ hx₀F
      have hgr := vecDot_eq_of_mem_frontier hUo hψ.continuous hch hx₀F (Metric.mem_ball_self hr)
      have hFloc : MemLp F (ENNReal.ofReal P) (volume.restrict (U ∩ Metric.ball x₀ (K * ℓb))) :=
        hFmem.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
      have hbd := Hb U e ψ x₀ r M₂ m hUo he hψ hb1 hb2 hgr hch hflat hKr φ F hw hFloc
      have hCbA : Cb ≤ A := (le_max_left _ _).trans hAC
      have hCbA' : ENNReal.ofReal Cb ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal hCbA
      exact p13_cell_bdy hUo hs hxk hdist hsR hRw hbd (mul_le_mul_left hCbA' _)
        (mul_le_mul_left hCbA' _) hCbA'
    · push Not at hnear
      have hCiM : Ci ≤ max Cb Ci := le_max_right _ _
      have hecc : 0 ≤ cc ^ d := pow_nonneg hcc0.le d
      have hA2 : Ci * cc ^ d * cc ≤ A := by
        rw [hA]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCiM hecc) hcc0.le
      have hA1 : Ci * cc ^ d ≤ A := by
        have : Ci * cc ^ d ≤ Ci * cc ^ d * cc :=
          le_mul_of_one_le_right (mul_nonneg hCi.le hecc) hcc1
        exact this.trans hA2
      have hΛ := p13_Lam_le (d := d) hℓi0 hcc1 hθ0 hθ1
      rw [mul_comm cc ℓi, hℓic] at hΛ
      have hL : ENNReal.ofReal ℓi⁻¹ = ENNReal.ofReal cc * Lib := by
        have hccc : cc * cc⁻¹ = 1 := mul_inv_cancel₀ hcc0.ne'
        have : ℓi⁻¹ = cc * ℓb⁻¹ := by
          rw [← hℓic]; linear_combination (-ℓi⁻¹) * hccc
        rw [this, ENNReal.ofReal_mul hcc0.le]
      obtain ⟨ha, ha'⟩ := p13_const_int hCi.le hecc hΛ hL hA1 hA2
      exact p13_cell_int hUo hℓi0 hsl hxU hxk hρ₁ hnear hρℓ hRi
        (fun hBU => Hi U (m - (j : ℤ)) (fun i => (k i : ℝ) * s) hUo hBU φ.toH1Function F hw
          (hFmem.mono_measure (Measure.restrict_mono hBU le_rfl))) ha ha'
        (ENNReal.ofReal_le_ofReal (hCiM.trans hAC))
  have hgm : AEStronglyMeasurable φ.toH1Function.grad (volume.restrict U) :=
    φ.toH1Function.grad_memVectorL2.aestronglyMeasurable
  have hφm : AEStronglyMeasurable φ.toH1Function.toFun (volume.restrict U) :=
    φ.toH1Function.memL2.aestronglyMeasurable
  have hsum := p13_cells_sum hUo.measurableSet hgm hφm hF.aestronglyMeasurable hP hs hcell
  have h2R : 2 * R / s = 4 * (K + 1) * cc := by
    have hℓiℓ : ℓi * ℓi⁻¹ = 1 := mul_inv_cancel₀ hℓi0.ne'
    rw [hRdef, hsdef, ← hℓic]
    linear_combination (4 * (K + 1) * cc) * hℓiℓ
  rw [h2R, ← hpP] at hsum
  have hD0 : 0 ≤ D := by simpa using hdiam x₁ hx₁ x₁ hx₁
  have hsub := p13_subset_axisCube hdiam hx₁ hr
  set L : ℝ := 2 * (D + r) with hLdef
  have hL0 : 0 < L := mul_pos two_pos (add_pos_of_nonneg_of_pos hD0 hr)
  have hPo := Hpo hUo (fun i => x₁ i - (D + r)) hL0 hsub φ
  have hEn := p13_energy hF φ hw
  have hHo := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict U) (f := F)
    (p := 2) (q := ENNReal.ofReal P) (by rw [← hpP]; exact hp2) hF.aestronglyMeasurable
  have hHo' : eLpNorm F 2 (volume.restrict U) ≤
      (volume U) ^ (1 / 2 - 1 / P : ℝ) * eLpNorm F (ENNReal.ofReal P) (volume.restrict U) := by
    rw [mul_comm]
    simpa [Measure.restrict_apply_univ, ENNReal.toReal_ofReal hP0.le] using hHo
  rw [← hpP] at hHo'
  have hV : volume U ≤ ENNReal.ofReal (L ^ d) := by
    calc volume U ≤ volume (axisCube (fun i => x₁ i - (D + r)) L) := measure_mono hsub
      _ = ENNReal.ofReal L ^ d := p13_volume_axisCube _ _
      _ = ENNReal.ofReal (L ^ d) := (ENNReal.ofReal_pow hL0.le d).symm
  have hLℓ : L / ℓb ≤ Zr := by
    have hm : 0 ≤ max (ρ + 1) 0 := le_max_right _ _
    have hLm : L ≤ 2 * max (ρ + 1) 0 * r := by
      have h1 : D + r ≤ (ρ + 1) * r := by linarith only [hD]
      have h2 : (ρ + 1) * r ≤ max (ρ + 1) 0 * r :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hr.le
      linarith only [h1, h2, hLdef]
    rw [div_le_iff₀ hℓb0]
    have h3 : r * θ₀ / 3 ≤ ℓb := by linarith only [hm2]
    have h4 : Zr * (r * θ₀ / 3) ≤ Zr * ℓb := mul_le_mul_of_nonneg_left h3 hZr0
    have h5 : Zr * (r * θ₀ / 3) = 2 * max (ρ + 1) 0 * r := by
      have hθθ : θ₀ * θ₀⁻¹ = 1 := mul_inv_cancel₀ hθ₀.ne'
      rw [hZr]; linear_combination (2 * max (ρ + 1) 0 * r) * hθθ
    linarith only [hLm, h4, h5]
  have hLℓ0 : 0 ≤ L / ℓb := div_nonneg hL0.le hℓb0.le
  have hW5 : Λb * (volume U) ^ (1 / 2 - 1 / P : ℝ) ≤ ENNReal.ofReal Z := by
    calc Λb * (volume U) ^ (1 / 2 - 1 / P : ℝ)
        = (ENNReal.ofReal ((ℓb ^ d)⁻¹) * volume U) ^ (1 / 2 - 1 / P : ℝ) := by
          rw [hΛb, ENNReal.mul_rpow_of_nonneg _ _ hθ0]
      _ ≤ (ENNReal.ofReal ((ℓb ^ d)⁻¹) * ENNReal.ofReal (L ^ d)) ^ (1 / 2 - 1 / P : ℝ) :=
          ENNReal.rpow_le_rpow (mul_le_mul_right hV _) hθ0
      _ = ENNReal.ofReal ((L / ℓb) ^ d) ^ (1 / 2 - 1 / P : ℝ) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hℓb0.le d)), div_pow]
          congr 2
          ring
      _ ≤ ENNReal.ofReal (max 1 ((L / ℓb) ^ d)) := p13_rpow_le_max hθ0 hθ1
      _ ≤ ENNReal.ofReal Z := by
          refine ENNReal.ofReal_le_ofReal (max_le_max le_rfl ?_)
          exact pow_le_pow_left₀ hLℓ0 hLℓ d
  have hW6 : Lib * ENNReal.ofReal (c₀ * L) ≤ ENNReal.ofReal Y := by
    rw [hLib, ← ENNReal.ofReal_mul (inv_nonneg.2 hℓb0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : ℓb⁻¹ * (c₀ * L) = c₀ * (L / ℓb) := by ring
    rw [this, hY]
    exact mul_le_mul_of_nonneg_left hLℓ hc₀.le
  refine p13_final_alg (A := A) (Q := c₀ * L) (dd := (d : ℝ) + 1) (Z := Z) (Y := Y)
    (Nr := (Nn : ℝ)) (Nh := (Nn : ℝ≥0∞) ^ (1 / 2 : ℝ)) (Nq := (Nn : ℝ≥0∞) ^ (1 / P)) hAp.le hd1' hZ0 hY0 hNr.le ?_ ?_ ?_ hPo hEn hHo' hW5 hW6
  · exact hsum
  · exact p13_natrpow_le hN1 (by norm_num)
  · exact p13_natrpow_le hN1 (by
      have : 0 ≤ 1 / P := one_div_nonneg.2 hP0.le
      rw [div_le_one hP0]
      linarith only [hP])

end SuperdiffusionCLT.Section7
