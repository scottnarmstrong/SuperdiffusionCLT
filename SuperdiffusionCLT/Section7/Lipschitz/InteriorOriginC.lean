/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.Analytic.Geometry.RoundedCubeD
public import SuperdiffusionCLT.Section7.Analytic.ElementaryB
public import SuperdiffusionCLT.Section7.Prereq.Domains

/-!
# Helpers for the interior estimate in the frame of the centre

Monotonicity of the `L²` block in its constant, the numerical threshold relating `σ̄` and the
scale `δ`, and the rounded cubes as origin cubes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- The `L²` block is monotone in its constant. -/
theorem LipL2Block.mono_const {a : CoeffField d} {nu s δ C C' : ℝ} {A k : ℕ} {V : Set (Vec d)}
    (h : LipL2Block a nu s δ C A k V) (hδ : 0 ≤ δ) (hCC : C ≤ C') :
    LipL2Block a nu s δ C' A k V := by
  intro f g u ub hu hub hg hgb
  refine (h f g u ub hu hub hg hgb).trans ?_
  have hx : 0 ≤ δ * (Real.sqrt s)⁻¹ * Real.sqrt nu :=
    mul_nonneg (mul_nonneg hδ (inv_nonneg.2 (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
  have hy : 0 ≤ ((k : ℝ) ^ A)⁻¹ := inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg k) A)
  have e1 : C * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu ≤ C' * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu := by
    have := mul_le_mul_of_nonneg_right hCC hx
    calc C * δ * (Real.sqrt s)⁻¹ * Real.sqrt nu = C * (δ * (Real.sqrt s)⁻¹ * Real.sqrt nu) := by ring
      _ ≤ C' * (δ * (Real.sqrt s)⁻¹ * Real.sqrt nu) := this
      _ = _ := by ring
  have e2 : C * ((k : ℝ) ^ A)⁻¹ ≤ C' * ((k : ℝ) ^ A)⁻¹ := mul_le_mul_of_nonneg_right hCC hy
  gcongr

/-- The numerical thresholds for the harmonic approximation: for `k` large, `σ̄ ≤ k` forces
`(k^3)⁻¹ √σ̄ ≤ δ_{k-1} √ν` and `(k^3)⁻¹ σ̄ ≤ 1`. -/
theorem lip_interior_origin_thresh (ε ρ nu : ℝ) (hε : 0 < ε) (hρ0 : 0 ≤ ρ)
    (hnu : 0 < nu) :
    ∃ L : ℝ, 5 ≤ L ∧ ∀ (k : ℕ) (s : ℝ), L ≤ (k : ℝ) → 1 ≤ s → s ≤ (k : ℝ) →
      ((k : ℝ) ^ 3)⁻¹ * Real.sqrt s ≤ deltaScale ε ρ (((k - 1 : ℕ) : ℝ)) * Real.sqrt nu ∧
        ((k : ℝ) ^ 3)⁻¹ * s ≤ 1 := by
  have hsn : 0 < Real.sqrt nu := Real.sqrt_pos.2 hnu
  refine ⟨max 5 (1 / (ε * Real.sqrt nu)), le_max_left _ _, fun k s hk hs1 hsk => ?_⟩
  have hk5 : (5 : ℝ) ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : (1 : ℝ) ≤ k := by linarith only [hk5]
  have hk0 : (0 : ℝ) < k := by linarith only [hk5]
  have hkn : 1 / (ε * Real.sqrt nu) ≤ k := le_trans (le_max_right _ _) hk
  have hk3 : (0 : ℝ) < (k : ℝ) ^ 3 := by positivity
  constructor
  · -- first inequality
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by exact_mod_cast hk1)]; simp
    have hx4 : (4 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by rw [hc]; linarith only [hk5]
    have hx1 : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by linarith only [hx4]
    have hlog := a23_one_le_log hx4
    have hrp : (((k - 1 : ℕ) : ℝ)) ^ (-(1 : ℝ)) ≤
        (((k - 1 : ℕ) : ℝ)) ^ (-((1 - ρ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hρ0])
    have hrp1 : (((k - 1 : ℕ) : ℝ)) ^ (-(1 : ℝ)) = ((((k - 1 : ℕ) : ℝ)))⁻¹ := Real.rpow_neg_one _
    have hxk : (k : ℝ)⁻¹ ≤ ((((k - 1 : ℕ) : ℝ)))⁻¹ := by
      apply inv_anti₀ (by linarith only [hx4])
      rw [hc]; linarith only
    have hδ : ε * (k : ℝ)⁻¹ ≤ deltaScale ε ρ (((k - 1 : ℕ) : ℝ)) := by
      unfold deltaScale
      have h1 : (k : ℝ)⁻¹ ≤ (((k - 1 : ℕ) : ℝ)) ^ (-((1 - ρ) / 2)) := by
        linarith only [hxk, hrp, hrp1]
      calc ε * (k : ℝ)⁻¹ = ε * (k : ℝ)⁻¹ * 1 := by ring
        _ ≤ ε * (((k - 1 : ℕ) : ℝ)) ^ (-((1 - ρ) / 2)) * Real.log (((k - 1 : ℕ) : ℝ)) := by
          have h2 : 0 ≤ ε * (k : ℝ)⁻¹ := by positivity
          calc ε * (k : ℝ)⁻¹ * 1 ≤ ε * (((k - 1 : ℕ) : ℝ)) ^ (-((1 - ρ) / 2)) * 1 :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hε.le) zero_le_one
            _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
    have hs0 : Real.sqrt s ≤ k := by
      calc Real.sqrt s ≤ s := by
            rw [Real.sqrt_le_left (by linarith only [hs1])]
            nlinarith only [hs1]
        _ ≤ k := hsk
    have h1 : ((k : ℝ) ^ 3)⁻¹ * Real.sqrt s ≤ ((k : ℝ) ^ 3)⁻¹ * k :=
      mul_le_mul_of_nonneg_left hs0 (inv_nonneg.2 hk3.le)
    have h2 : ((k : ℝ) ^ 3)⁻¹ * k = ((k : ℝ)⁻¹) * ((k : ℝ)⁻¹) := by
      field_simp
    have h3 : (k : ℝ)⁻¹ ≤ ε * Real.sqrt nu := by
      rw [inv_eq_one_div]
      have hpos : 0 < ε * Real.sqrt nu := mul_pos hε hsn
      rw [div_le_iff₀ hk0]
      rw [div_le_iff₀ hpos] at hkn
      linarith only [hkn]
    have h4 : ((k : ℝ)⁻¹) * ((k : ℝ)⁻¹) ≤ ε * (k : ℝ)⁻¹ * Real.sqrt nu := by
      have h5 : (k : ℝ)⁻¹ * (k : ℝ)⁻¹ ≤ (ε * Real.sqrt nu) * (k : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right h3 (inv_nonneg.2 hk0.le)
      calc _ ≤ _ := h5
        _ = _ := by ring
    calc ((k : ℝ) ^ 3)⁻¹ * Real.sqrt s ≤ ε * (k : ℝ)⁻¹ * Real.sqrt nu := by
          linarith only [h1, h2, h4]
      _ ≤ deltaScale ε ρ (((k - 1 : ℕ) : ℝ)) * Real.sqrt nu :=
          mul_le_mul_of_nonneg_right hδ hsn.le
  · -- second inequality
    have h1 : ((k : ℝ) ^ 3)⁻¹ * s ≤ ((k : ℝ) ^ 3)⁻¹ * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hsk (inv_nonneg.2 hk3.le)
    have h2 : ((k : ℝ) ^ 3)⁻¹ * (k : ℝ) ≤ 1 := by
      rw [inv_mul_le_iff₀ hk3]
      have : (k : ℝ) ≤ (k : ℝ) ^ 3 := by
        calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1 (by norm_num)
      linarith only [this]
    linarith only [h1, h2]

/-- The origin cube as a ball for the sup norm. -/
theorem lip_interior_origin_engCube_eq_ball (j : ℕ) :
    Section6.engCube d j = Metric.ball (0 : Vec d) ((3 : ℝ) ^ j / 2) := by
  ext x
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by positivity)]
  simp only [Section6.engCube, mem_openCubeSet_originCube_iff, zpow_natCast, Real.norm_eq_abs,
    abs_lt]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, ?_⟩ <;> linarith only [h1, h2]

/-- The rounded cubes as origin cubes, with the uniform data of the `L²` block. -/
theorem lip_interior_origin_family [NeZero d] :
    ∃ (N : ℕ) (r M₁ M₂ D : ℝ), 0 < r ∧ ∀ j : ℕ, 1 ≤ j →
      IsOpen (g1_V d N j 0) ∧ g1_V d N j 0 ⊆ Section6.engCube d j ∧
        Section6.engCube d (j - 1) ⊆ g1_V d N j 0 ∧
        IsUniformC11Domain (((3 : ℝ) ^ j)⁻¹ • g1_V d N j 0) (1 / 2 * r) M₁ (M₂ / (1 / 2))
          (1 / 2 * D) := by
  obtain ⟨N, r, M₁, M₂, D, -, hr, h⟩ := g1_uniform_family (d := d)
  refine ⟨N, r, M₁, M₂, D, hr, fun j hj => ⟨g1_V_isOpen j 0, ?_, ?_, ?_⟩⟩
  · rw [lip_interior_origin_engCube_eq_ball]
    have h' := (h j 0).2.2.2
    exact h'
  · rw [lip_interior_origin_engCube_eq_ball]
    have h' := (h j 0).2.2.1
    refine subset_trans (fun x hx => ?_) h'
    have e : (3 : ℝ) ^ j / 2 / 3 = (3 : ℝ) ^ (j - 1) / 2 := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]; ring
    rw [e]
    exact hx
  · have h' := (h j 0).1
    have e : (fun y : Vec d => ((3 : ℝ) ^ j)⁻¹ • (y - 0)) '' g1_V d N j 0 =
        ((3 : ℝ) ^ j)⁻¹ • g1_V d N j 0 := by
      simp only [sub_zero]
      exact Set.image_smul
    rw [e] at h'
    exact h'

/-- The harmonic approximation at the scale `k` from the `L²` block at the scale `k - 1` and the
Caccioppoli block at the scale `k`, moved between the neighbouring values of `σ̄` and `δ`. -/
theorem lip_interior_origin_harm_step {d : ℕ} {CL2 CCA CH : ℝ} (hCL2 : 1 ≤ CL2) (hCCA : 1 ≤ CCA)
    (hH : ∀ (a : CoeffField d) (nu s δ lam Lam : ℝ) (k : ℕ) (V : Set (Vec d)),
      0 < nu → 0 < s → 0 ≤ δ → 3 ≤ k →
      ((k : ℝ) ^ 3)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu → ((k : ℝ) ^ 3)⁻¹ * s ≤ 1 →
      IsOpen V → Section6.engCube d (k - 2) ⊆ V → V ⊆ Section6.engCube d (k - 1) →
      IsEllipticFieldOn lam Lam (Section6.engCube d k) a → 0 < lam →
      LipL2Block a nu s δ (2 * max CL2 CCA) 3 (k - 1) V →
        LipCaccInt a nu s (2 * max CL2 CCA) 1 k → LipHarmInt a s δ CH k)
    (hCH : 0 ≤ CH)
    (a : CoeffField d) (nu s0 s1 δ0 δ1 lam Lam : ℝ) (k : ℕ) (V : Set (Vec d))
    (hnu : 0 < nu) (hs0 : 0 < s0) (hs1 : 0 < s1) (h10 : s1 ≤ 2 * s0) (h01 : s0 ≤ 2 * s1)
    (hδ0 : 0 ≤ δ0) (hδ : δ0 ≤ 2 * δ1) (hk : 3 ≤ k)
    (hth1 : ((k : ℝ) ^ 3)⁻¹ * Real.sqrt s0 ≤ δ0 * Real.sqrt nu)
    (hth2 : ((k : ℝ) ^ 3)⁻¹ * s0 ≤ 1) (hV : IsOpen V)
    (hV1 : Section6.engCube d (k - 2) ⊆ V) (hV2 : V ⊆ Section6.engCube d (k - 1))
    (hE : IsEllipticFieldOn lam Lam (Section6.engCube d k) a) (hlam : 0 < lam)
    (hL2 : LipL2Block a nu s0 δ0 CL2 3 (k - 1) V) (hCA : LipCaccInt a nu s1 CCA 1 k) :
    LipHarmInt a s1 δ1 (2 * CH) k := by
  have hm : max CL2 CCA ≥ 1 := le_trans hCL2 (le_max_left _ _)
  have hL2' : LipL2Block a nu s0 δ0 (2 * max CL2 CCA) 3 (k - 1) V :=
    hL2.mono_const hδ0 (by linarith only [le_max_left CL2 CCA, hm])
  have hCA' : LipCaccInt a nu s0 (2 * max CL2 CCA) 1 k :=
    hCA.mono hs1 h10 h01 (by linarith only [hCCA]) (by linarith only [le_max_right CL2 CCA])
  have hh := hH a nu s0 δ0 lam Lam k V hnu hs0 hδ0 hk hth1 hth2 hV hV1 hV2 hE hlam hL2' hCA'
  exact hh.mono hs1 h10 hδ0 hδ hCH le_rfl

end SuperdiffusionCLT.Section7
