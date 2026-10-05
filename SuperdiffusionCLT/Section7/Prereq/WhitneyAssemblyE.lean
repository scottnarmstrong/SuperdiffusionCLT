/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyAssemblyD
public import SuperdiffusionCLT.Section7.Prereq.WhitneyLocalD
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC
public import SuperdiffusionCLT.Section7.Analytic.Geometry.Atlas
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# The coarse-grained Poincare inequality in dilated domains: the assembly

`wh3_det` is the deterministic part: for a smooth bounded domain `U`, the summed local oscillation
bound of the local estimate (`wh2_ae_whitney`), the scaled Poincare hypothesis on the Whitney
interior and the boundary-layer inequality give the squared `L²` estimate of `u - (u)_W`.
`wh3_whitney_poincare` assembles it with the random scale, the lower and upper bounds for the running
diffusivity, and the normalization of the norms.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- `σ̄ ≥ ν / (2 C)`: the lower bound for the infinite-volume running diffusivity. -/
theorem wh3_sigma_lower [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) :
    nu ≤ 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d *
      SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P := by
  open SuperdiffusionCLT.Section2.Annealed in
  have hL := sigmaBarStarInvLimit_pos hnu m hPrefix hJ2 hJ3 hJ4
  open SuperdiffusionCLT.Section2.Annealed in
  have hle : sigmaBarStarInvLimit nu m P ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ :=
    (sigmaBarStarInvLimit_le hnu m hPrefix hJ2 hJ3 hJ4 0).trans
      (sigmaBarStarInvSeq_le_envelopeLowerScalar hnu m hPrefix hJ2 hJ3 hJ4 0)
  unfold SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
  have h1 : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit nu m P * nu ≤
      2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d := by
    calc _ ≤ (2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d * nu⁻¹) * nu :=
          mul_le_mul_of_nonneg_right hle hnu.le
      _ = _ := by field_simp
  rw [← div_eq_mul_inv, le_div_iff₀ hL]
  linarith only [h1]

/-- The upper bound for the running diffusivity from the sharp bounds, in polynomial form. -/
theorem wh3_sigma_upper {σ cStar K Cσ : ℝ} {m : ℕ} (hc : 0 < cStar) (hCσ : 0 ≤ Cσ) (hm : 1 ≤ m)
    (hb : |σ - (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
      Cσ * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) :
    σ ≤ (1 + 2 * cStar * Real.log 3 + Cσ * cStar⁻¹ * (1 + |K|)) * (m : ℝ) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1]
  have hm3 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hm1]
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hy0 : 0 ≤ 2 * cStar * Real.log 3 * (m : ℝ) := by positivity
  have hsq : (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2) ≤
      1 + 2 * cStar * Real.log 3 * (m : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
    refine ⟨by linarith only [hy0], ?_⟩
    nlinarith only [hy0]
  have hlog : Real.log (m : ℝ) ≤ (m : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith only [hm1] : (0 : ℝ) < m)
    linarith only [this]
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlog2 : Real.log (m : ℝ) ^ (2 : ℝ) ≤ (m : ℝ) ^ 2 := by
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ hlog0 hlog 2
  have hK : K ≤ |K| := le_abs_self K
  have hR : Cσ * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K) ≤
      Cσ * cStar⁻¹ * (1 + |K|) * (m : ℝ) ^ 2 := by
    have h0 : 0 ≤ Cσ * cStar⁻¹ := by positivity
    have : Real.log (m : ℝ) ^ (2 : ℝ) + K ≤ (1 + |K|) * (m : ℝ) ^ 2 := by
      nlinarith only [hlog2, hK, hm3, abs_nonneg K]
    calc Cσ * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)
        ≤ Cσ * cStar⁻¹ * ((1 + |K|) * (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have h1 := (abs_le.1 hb).2
  have h2 : 2 * cStar * Real.log 3 * (m : ℝ) ≤ 2 * cStar * Real.log 3 * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hm2 (by positivity)
  have : (1 + 2 * cStar * Real.log 3 + Cσ * cStar⁻¹ * (1 + |K|)) * (m : ℝ) ^ 2 =
      (m : ℝ) ^ 2 + 2 * cStar * Real.log 3 * (m : ℝ) ^ 2 + Cσ * cStar⁻¹ * (1 + |K|) * (m : ℝ) ^ 2 := by
    ring
  rw [this]
  linarith only [h1, hsq, hR, h2, hm3]

/-- `m^8 ≤ 3^{⌈M log m⌉}` for `M ≥ 8`. -/
theorem wh3_three_pow_ge {M : ℝ} (hM : 8 ≤ M) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ 8 ≤ (3 : ℝ) ^ (⌈M * Real.log m⌉ : ℤ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hk : 8 * Real.log m ≤ ((⌈M * Real.log m⌉ : ℤ) : ℝ) :=
    (by nlinarith only [hM, hl0] : 8 * Real.log m ≤ M * Real.log m).trans (Int.le_ceil _)
  have hlog3 : 1 ≤ Real.log 3 := by
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith only [this]
    exact ((Real.lt_log_iff_exp_lt (by norm_num)).2 this).le
  rw [← Real.rpow_intCast]
  have e : (m : ℝ) ^ 8 = Real.exp (8 * Real.log m) := by
    rw [show (8 : ℝ) * Real.log m = ((8 : ℕ) : ℝ) * Real.log m by norm_num, Real.exp_nat_mul,
      Real.exp_log hm0]
  calc (m : ℝ) ^ 8 = Real.exp (8 * Real.log m) := e
    _ ≤ Real.exp (Real.log 3 * (8 * Real.log m)) :=
        Real.exp_le_exp.2 (by nlinarith only [hlog3, hl0])
    _ = (3 : ℝ) ^ (8 * Real.log m) := (Real.rpow_def_of_pos (by norm_num) _).symm
    _ ≤ (3 : ℝ) ^ (((⌈M * Real.log m⌉ : ℤ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hk



theorem wh3_enn_combine {P2 Q Pq A0 B0 Lr : ℝ} (hP2 : 0 ≤ P2) (hQ : 0 ≤ Q) (hPq : 0 ≤ Pq)
    (hA0 : 0 ≤ A0) (hB0 : 0 ≤ B0) (hL : 0 ≤ Lr) {S G F : ℝ≥0∞}
    (hS : S ≤ 27 ^ d * (2 * ENNReal.ofReal Pq ^ 2 *
      (ENNReal.ofReal A0 ^ 2 * G + ENNReal.ofReal B0 ^ 2 * F))) :
    (4 * 9 ^ d + 4 * ENNReal.ofReal P2 * ENNReal.ofReal Q) * S + 2 * ENNReal.ofReal Lr * G ≤
      ENNReal.ofReal ((4 * 9 ^ d + 4 * P2 * Q) * 27 ^ d * (2 * Pq ^ 2 * A0 ^ 2) + 2 * Lr) * G +
        ENNReal.ofReal ((4 * 9 ^ d + 4 * P2 * Q) * 27 ^ d * (2 * Pq ^ 2 * B0 ^ 2)) * F := by
  have h9 : ENNReal.ofReal ((9 : ℝ) ^ d) = 9 ^ d := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h27 : ENNReal.ofReal ((27 : ℝ) ^ d) = 27 ^ d := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hΩ : ENNReal.ofReal (4 * 9 ^ d + 4 * P2 * Q) =
      4 * 9 ^ d + 4 * ENNReal.ofReal P2 * ENNReal.ofReal Q := by
    simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, h9,
      ENNReal.ofReal_ofNat]
  have e1 : ENNReal.ofReal ((4 * 9 ^ d + 4 * P2 * Q) * 27 ^ d * (2 * Pq ^ 2 * A0 ^ 2) + 2 * Lr) =
      (4 * 9 ^ d + 4 * ENNReal.ofReal P2 * ENNReal.ofReal Q) * 27 ^ d *
        (2 * ENNReal.ofReal Pq ^ 2 * ENNReal.ofReal A0 ^ 2) + 2 * ENNReal.ofReal Lr := by
    simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, ENNReal.ofReal_pow, h9, h27,
      ENNReal.ofReal_ofNat]
  have e2 : ENNReal.ofReal ((4 * 9 ^ d + 4 * P2 * Q) * 27 ^ d * (2 * Pq ^ 2 * B0 ^ 2)) =
      (4 * 9 ^ d + 4 * ENNReal.ofReal P2 * ENNReal.ofReal Q) * 27 ^ d *
        (2 * ENNReal.ofReal Pq ^ 2 * ENNReal.ofReal B0 ^ 2) := by
    simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, ENNReal.ofReal_pow, h9, h27,
      ENNReal.ofReal_ofNat]
  rw [e1, e2]
  calc (4 * 9 ^ d + 4 * ENNReal.ofReal P2 * ENNReal.ofReal Q) * S + 2 * ENNReal.ofReal Lr * G
      ≤ (4 * 9 ^ d + 4 * ENNReal.ofReal P2 * ENNReal.ofReal Q) *
          (27 ^ d * (2 * ENNReal.ofReal Pq ^ 2 *
            (ENNReal.ofReal A0 ^ 2 * G + ENNReal.ofReal B0 ^ 2 * F))) + 2 * ENNReal.ofReal Lr * G := by
        gcongr
    _ = _ := by ring

theorem wh3_union_subset {W : Set (Vec d)} {h : ℝ} (hh : 0 < h) {Zg : Finset (Fin d → ℤ)}
    (hZg : ∀ k, k ∈ Zg ↔ k ∈ wh3_good h W) : (⋃ k ∈ Zg, wh3_cell h k) ⊆ W := by
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  exact ((hZg k).1 hk) (wh1_box_mono _ (by linarith only [hh]) hxk)

/-- **The deterministic part of the coarse-grained Poincare inequality.**  For a smooth bounded
domain `U` there are constants `Γ` and `Λ` (depending on `U`, `d` and the constants `Cp, C₂, Ce`
only) such that, for every dilate `W = t U`, grid scale `h = 3^j`, and every `H¹` function `u`
whose summed local oscillations obey the bound `hS` and for which the scaled Poincare inequality
holds on `whitneyInterior W j`, the squared `L²` distance of `u` to its mean is bounded by the
gradient and right-hand-side energies. -/
theorem wh3_det [NeZero d] {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) (Cp C₂ Ce : ℝ)
    (hCp : 0 < Cp) (hC₂ : 1 ≤ C₂) (hCe : 0 < Ce) :
    ∃ Γ Λ : ℝ, 1 ≤ Γ ∧ 0 ≤ Λ ∧
      ∀ {t R T D ν σ : ℝ} {j : ℤ}, 0 < t → (∀ x ∈ t • U, ∀ i, |x i| ≤ R) →
        (3 : ℝ) ^ j ≤ T → t ≤ T → 1 ≤ D → 0 < ν → 0 < σ → ν ≤ 2 * Ce * σ →
        (3 : ℝ) ^ j * σ ≤ T * ν → Λ * (3 : ℝ) ^ j ≤ t →
        ∀ (u : H1Function (t • U)) (f : Vec d → ℝ) (c : (Fin d → ℤ) → ℝ),
          (∀ φ : H1Function (t • U),
            eLpNorm (fun x => φ.toFun x - ⨍ z in whitneyInterior (t • U) j, φ.toFun z) 2
                (volume.restrict (whitneyInterior (t • U) j)) ≤
              ENNReal.ofReal (D * T) *
                eLpNorm (fun x => eucNorm (φ.grad x)) 2
                  (volume.restrict (whitneyInterior (t • U) j))) →
          (∀ Z : Finset (Fin d → ℤ),
            (∀ k ∈ Z, wh1_box (wh1_pt ((3 : ℝ) ^ j) k) (27 * (3 : ℝ) ^ j / 2) ⊆ t • U) →
              ∑ k ∈ Z, wh1_osc ((3 : ℝ) ^ j) (27 * (3 : ℝ) ^ j / 2) u.toFun c k ≤
                27 ^ d * (2 * ENNReal.ofReal (Cp * (27 * (3 : ℝ) ^ j)) ^ 2 *
                  (ENNReal.ofReal (C₂ * (Real.sqrt σ)⁻¹ * Real.sqrt ν) ^ 2 *
                      (∫⁻ x in t • U, ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) +
                    ENNReal.ofReal ((C₂ * (Real.sqrt σ)⁻¹ * Real.sqrt ν + C₂) *
                        (C₂ * (27 * (3 : ℝ) ^ j) / ν)) ^ 2 *
                      ∫⁻ x in t • U, ENNReal.ofReal (f x ^ 2)))) →
          ∫⁻ x in t • U, ENNReal.ofReal ((u.toFun x - ⨍ z in t • U, u.toFun z) ^ 2) ≤
            ENNReal.ofReal ((Γ * D * T * ((Real.sqrt σ)⁻¹ * Real.sqrt ν)) ^ 2) *
                (∫⁻ x in t • U, ENNReal.ofReal (eucNorm (u.grad x) ^ 2)) +
              ENNReal.ofReal ((Γ * D * T * (3 : ℝ) ^ j / ν) ^ 2) *
                ∫⁻ x in t • U, ENNReal.ofReal (f x ^ 2) := by
  obtain ⟨r₀, M₁, M₂, D₀, hU'⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hU
  have hr₀ : 0 < r₀ := hU'.2.1
  obtain ⟨Cl, hCl0, hcore⟩ := wh3_core (d := d) M₁
  obtain ⟨Γ, hΓ1, hnum⟩ := wh3_numeric d Cp C₂ Ce Cl r₀ hCp hC₂ hCe hCl0 hr₀
  refine ⟨Γ, 28 * Cl / r₀, hΓ1, by positivity, ?_⟩
  intro t R T D ν σ j ht hR hjT htT hD hν hσ hσlow hKI hΛ u f c hP hS
  have hh : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hT : 0 < T := lt_of_lt_of_le hh hjT
  have hW' := hU'.smul ht
  have hfin := wh3_finite_of_bounded hR hh
  set Zg : Finset (Fin d → ℤ) := hfin.toFinset with hZgdef
  have hZg : ∀ k, k ∈ Zg ↔ k ∈ wh3_good ((3 : ℝ) ^ j) (t • U) := fun k => hfin.mem_toFinset
  have hsm : Cl * (14 * (3 : ℝ) ^ j / (t * r₀)) ≤ 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have h1 : 28 * Cl * (3 : ℝ) ^ j ≤ t * r₀ := by
      have := mul_le_mul_of_nonneg_right hΛ hr₀.le
      have e : 28 * Cl / r₀ * (3 : ℝ) ^ j * r₀ = 28 * Cl * (3 : ℝ) ^ j := by field_simp
      linarith only [this, e]
    linarith only [h1]
  have hae := wh3_whitneyInterior_ae (W := t • U) (j := j) hZg
  have hUW := wh3_union_subset hh hZg
  have hP' := wh3_hyp_conv hae hUW (by positivity : 0 ≤ D * T) hP
  have hc := hcore hW' hh Zg hZg hsm u c (P := D * T) hP'
  have hS' := hS Zg (fun k hk => (hZg k).1 hk)
  set s : ℝ := (Real.sqrt σ)⁻¹ * Real.sqrt ν with hsdef
  have hs0 : 0 ≤ s := by positivity
  have hs : s ^ 2 * σ = ν := by
    rw [hsdef, mul_pow, inv_pow, Real.sq_sqrt hσ.le, Real.sq_sqrt hν.le]
    field_simp
  have hs2 : s ^ 2 ≤ 2 * Ce := by
    have : s ^ 2 = ν / σ := by rw [← hs]; field_simp
    rw [this, div_le_iff₀ hσ]
    linarith only [hσlow]
  have e1 : C₂ * (Real.sqrt σ)⁻¹ * Real.sqrt ν = C₂ * s := by rw [hsdef]; ring
  rw [e1] at hS'
  have hnum' := hnum (ν := ν) (σ := σ) (s := s) (D := D) (T := T) (h := (3 : ℝ) ^ j)
    (q := 27 * (3 : ℝ) ^ j) (rr := t * r₀) hν hσ hs0 hs hs2 hD hT hh hjT hKI rfl
    (mul_le_mul_of_nonneg_right htT hr₀.le) (by positivity)
  have hcomb := wh3_enn_combine (d := d) (P2 := (D * T) ^ 2)
    (Q := 4 * (d : ℝ) ^ 3 * 27 ^ d / ((3 : ℝ) ^ j) ^ 2) (Pq := Cp * (27 * (3 : ℝ) ^ j))
    (A0 := C₂ * s) (B0 := (C₂ * s + C₂) * (C₂ * (27 * (3 : ℝ) ^ j) / ν))
    (Lr := Cl * (14 * (3 : ℝ) ^ j * (t * r₀))) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) hS'
  refine hc.trans (hcomb.trans ?_)
  gcongr
  · refine le_trans (le_of_eq ?_) hnum'.1
    ring
  · refine le_trans (le_of_eq ?_) hnum'.2
    ring


theorem wh3_pow27 (n : ℕ) :
    (3 : ℝ) ^ n = 27 * (3 : ℝ) ^ ((n : ℤ) - 3) ∧
      (3 : ℝ) ^ (n : ℤ) = 27 * (3 : ℝ) ^ ((n : ℤ) - 3) := by
  have h : (3 : ℝ) ^ (n : ℤ) = 27 * (3 : ℝ) ^ ((n : ℤ) - 3) := by
    have : (n : ℤ) = ((n : ℤ) - 3) + 3 := by ring
    conv_lhs => rw [this]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  exact ⟨by rw [← zpow_natCast]; exact h, h⟩

/-- Transfer of an `L²` estimate to the normalized norms. -/
theorem wh3_lpBar_final {W : Set (Vec d)} {F G H : Vec d → ℝ} {a b : ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict W))
    (hG : AEStronglyMeasurable G (volume.restrict W))
    (hH : AEStronglyMeasurable H (volume.restrict W))
    (h : eLpNorm F 2 (volume.restrict W) ≤
      ENNReal.ofReal a * eLpNorm G 2 (volume.restrict W) +
        ENNReal.ofReal b * eLpNorm H 2 (volume.restrict W)) :
    lpBar W 2 F ≤ ENNReal.ofReal a * lpBar W 2 G + ENNReal.ofReal b * lpBar W 2 H := by
  rw [rc_lpBar_two_eq W F hF, rc_lpBar_two_eq W G hG, rc_lpBar_two_eq W H hH]
  calc (volume W)⁻¹ ^ (1 / 2 : ℝ) * eLpNorm F 2 (volume.restrict W)
      ≤ (volume W)⁻¹ ^ (1 / 2 : ℝ) * (ENNReal.ofReal a * eLpNorm G 2 (volume.restrict W) +
        ENNReal.ofReal b * eLpNorm H 2 (volume.restrict W)) := by gcongr
    _ = _ := by ring

/-- A function that is not a.e. strongly measurable has infinite normalized norm. -/
theorem wh3_lpBar_top {W : Set (Vec d)} {f : Vec d → ℝ} (hW : volume W ≠ ⊤)
    (hf : ¬ AEStronglyMeasurable f (volume.restrict W)) : lpBar W 2 f = ⊤ := by
  unfold lpBar
  apply eLpNorm_of_not_aestronglyMeasurable
  intro hmeas
  apply hf
  have h0 : volume W ≠ 0 := by
    intro h0
    apply hf
    rw [Measure.restrict_eq_zero.2 h0]
    exact aestronglyMeasurable_zero_measure f
  have := hmeas.smul_measure (volume W)
  rwa [smul_smul, ENNReal.mul_inv_cancel h0 hW, one_smul] at this

open scoped Matrix.Norms.L2Operator in
/-- **Coarse-grained Poincare inequality in dilated domains** (`l.Dirichlet.Whitney.Poincare`),
with the statements of `sharp_scale_inputs` (`hInputs`) and `sigmaBar_sharp_bounds`
(`hSigma`) as hypotheses.  The proof interpolates the cube averages on the grid `3^j ℤ^d`,
`j = m - ⌈M log m⌉`, uses the summed local oscillation bound of `wh2_ae_whitney` and the
assumed Poincare inequality on the Whitney interior for the interpolant, and treats the
boundary layer with the `H¹` layer inequality applied to `u` itself. -/
theorem wh3_whitney_poincare
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ,
          0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
          MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
          SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0
          omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ᵐ
          omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
          omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m
          → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
          (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 :
          Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
          (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
          Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n :
          ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n :
          ℤ))), ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1
          : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^
          ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
          d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1
          - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
          Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
          (u.toH1.grad x))) ∧ ∃ w : Homogenization.AHarmonicFunction (fun _ => (1 :
          Homogenization.Mat d)) (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) -
          1))), ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n : ℤ) -
          1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ) ^
          (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) + Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n :
          ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m :
          ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m
          : ℤ)) ∞ (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ)
          ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
          (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ)
          ^ ρ))
    (hSigma :
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
            ∀ cStar : ℝ, 0 < cStar →
              ∀ K : ℝ,
                ∃ M : ℕ,
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                      ∀ m : ℕ, M ≤ m →
                        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
                            (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
                          C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) :
    ∀ U : Set (Homogenization.Vec d),
      SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
      U ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∀ ρ D M : ℝ, 0 < ρ → ρ < 1 → 1 ≤ D → C ≤ M →
                ∃ Lhat : ℝ, 1 ≤ Lhat ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                      Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                      -- e.Dir.new.Whitney.minscale.tail
                      Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma ρ)
                        (fun omega => Real.log (X omega)) Lhat ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ (t : ℝ) (m : ℕ),
                          X omega ≤ t → (3 : ℝ) ^ m < 3 * t → t ≤ (3 : ℝ) ^ m →
                          -- e.Dir.new.Whitney.Poincare.assumption.scaled
                          (∀ φ : Homogenization.H1Function (t • U),
                            MeasureTheory.eLpNorm
                                (fun x => φ.toFun x -
                                  ⨍ z in SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                      ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉),
                                    φ.toFun z)
                                2
                                (MeasureTheory.volume.restrict
                                  (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                    ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉))) ≤
                              ENNReal.ofReal (D * (3 : ℝ) ^ m) *
                                MeasureTheory.eLpNorm
                                  (fun x => SuperdiffusionCLT.Section7.eucNorm (φ.grad x))
                                  2
                                  (MeasureTheory.volume.restrict
                                    (SuperdiffusionCLT.Section7.whitneyInterior (t • U)
                                      ((m : ℤ) - ⌈M * Real.log (m : ℝ)⌉)))) →
                          ∀ (f : Homogenization.Vec d → ℝ)
                            (u : Homogenization.H1Function (t • U)),
                            SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                  nu omega)
                                (t • U) u f (fun _ => 0) →
                            -- e.Dir.new.Whitney.Poincare
                            SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                (fun x => u.toFun x - ⨍ z in t • U, u.toFun z) ≤
                              ENNReal.ofReal
                                  (C * D * (3 : ℝ) ^ m *
                                    (Real.sqrt
                                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                        nu m P))⁻¹ *
                                    Real.sqrt nu) *
                                SuperdiffusionCLT.Section7.lpBar (t • U) 2
                                  (fun x => SuperdiffusionCLT.Section7.eucNorm (u.grad x)) +
                              ENNReal.ofReal
                                  (C * D *
                                    (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) *
                                    nu⁻¹) *
                                SuperdiffusionCLT.Section7.lpBar (t • U) 2 f
  := by
  intro U hU hUc
  obtain ⟨C₂, Cp, hC₂, hCp, H⟩ := wh2_ae_whitney d hd hInputs
  obtain ⟨Cσ, hCσ, Hσ⟩ := hSigma
  have hCe := SuperdiffusionCLT.Section2.Annealed.one_le_cutoffEnvelopeConst d
  obtain ⟨Γ, Λ, hΓ, hΛ, hdet⟩ := wh3_det hU Cp C₂
    (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) hCp hC₂
    (by linarith only [hCe])
  refine ⟨max (max C₂ 8) Γ, le_max_of_le_left (le_max_of_le_left hC₂), ?_⟩
  intro nu hnu hnu1 cStar hcStar K ρ D M hρ hρ1 hD hCM
  have hC2M : C₂ ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans hCM)
  have hM8 : 8 ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans hCM)
  have hΓC : Γ ≤ max (max C₂ 8) Γ := le_max_right _ _
  obtain ⟨Lhat₂, hL₂, H2⟩ := H nu hnu hnu1 cStar hcStar K ρ M hρ hρ1 hC2M
  obtain ⟨M0, HM0⟩ := Hσ nu hnu hnu1 cStar hcStar K
  set A : ℝ := 1 + 2 * cStar * Real.log 3 + Cσ * cStar⁻¹ * (1 + |K|) with hA
  set m₁ : ℝ := max (max 1 (A / nu)) (max (3 * Λ) (M0 : ℝ)) with hm₁
  set L'' : ℝ := max Lhat₂ m₁ with hL''
  have hm₁1 : 1 ≤ m₁ := (le_max_left _ _).trans (le_max_left _ _)
  have hL''1 : 1 ≤ L'' := hm₁1.trans (le_max_right _ _)
  refine ⟨2 * L'', by linarith only [hL''1], fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hσb := HM0 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun ω => max (X0 ω) ((3 : ℝ) ^ L''), hm.max measurable_const,
    fun ω => (h1 ω).trans (le_max_left _ _),
    wh2_isBigO_max h1 (le_max_left _ _) (by linarith only [hL''1]) hO, ?_⟩
  filter_upwards [hae] with ω hω
  intro t m hXt h3t htm hPoinc f u hsol
  have hX0 : X0 ω ≤ t := (le_max_left _ _).trans hXt
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ((h1 ω).trans hX0)
  have hmL : L'' ≤ (m : ℝ) := by
    have h3 : (3 : ℝ) ^ L'' ≤ (3 : ℝ) ^ (m : ℝ) := by
      rw [Real.rpow_natCast]; exact (le_max_right _ _).trans (hXt.trans htm)
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h3
  have hm1 : (1 : ℝ) ≤ m := hL''1.trans hmL
  have hm1n : 1 ≤ m := by exact_mod_cast hm1
  have hm₁m : m₁ ≤ (m : ℝ) := (le_max_right _ _).trans hmL
  have hmM0 : M0 ≤ m := by
    have : (M0 : ℝ) ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm₁m
    exact_mod_cast this
  obtain ⟨n, hn, hnm, Hn⟩ := hω t m hX0 h3t htm
  have hjm : (n : ℤ) - 3 = (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ := by omega
  have hjle : (n : ℤ) - 3 ≤ (m : ℤ) := by omega
  have hjh : (n : ℤ) - 3 + ⌈M * Real.log (m : ℝ)⌉ = (m : ℤ) := by omega
  set σb := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P with hσbdef
  have hσpos : 0 < σb :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4
  have hlow := wh3_sigma_lower hnu m hPrefix hJ2 hJ3 hJ4
  have hσup := wh3_sigma_upper hcStar (by linarith only [hCσ]) hm1n (hσb m hmM0)
  have hAm : A ≤ (m : ℝ) * nu := by
    have : A / nu ≤ m :=
      ((le_max_right (1 : ℝ) (A / nu)).trans (le_max_left _ (max (3 * Λ) (M0 : ℝ)))).trans hm₁m
    exact (div_le_iff₀ hnu).1 this
  have hpow := wh3_three_pow_ge hM8 hm1n
  set hm' : ℤ := ⌈M * Real.log (m : ℝ)⌉ with hmdef
  have hjpos : 0 < (3 : ℝ) ^ ((n : ℤ) - 3) := zpow_pos (by norm_num) _
  have h3j : (3 : ℝ) ^ ((n : ℤ) - 3) * (3 : ℝ) ^ hm' = (3 : ℝ) ^ m := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), hjh, zpow_natCast]
  have hsig : σb ≤ nu * (3 : ℝ) ^ hm' := by
    calc σb ≤ A * (m : ℝ) ^ 2 := hσup
      _ ≤ ((m : ℝ) * nu) * (m : ℝ) ^ 2 := by gcongr
      _ = nu * (m : ℝ) ^ 3 := by ring
      _ ≤ nu * (m : ℝ) ^ 8 := by
          gcongr
          norm_num
      _ ≤ nu * (3 : ℝ) ^ hm' := by gcongr
  have hKI : (3 : ℝ) ^ ((n : ℤ) - 3) * σb ≤ (3 : ℝ) ^ m * nu := by
    calc (3 : ℝ) ^ ((n : ℤ) - 3) * σb ≤ (3 : ℝ) ^ ((n : ℤ) - 3) * (nu * (3 : ℝ) ^ hm') := by
          gcongr
      _ = nu * ((3 : ℝ) ^ ((n : ℤ) - 3) * (3 : ℝ) ^ hm') := by ring
      _ = (3 : ℝ) ^ m * nu := by rw [h3j]; ring
  have hjT : (3 : ℝ) ^ ((n : ℤ) - 3) ≤ (3 : ℝ) ^ m := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (by norm_num) hjle
  have hΛt : Λ * (3 : ℝ) ^ ((n : ℤ) - 3) ≤ t := by
    have h1 : 3 * Λ ≤ (3 : ℝ) ^ hm' := by
      calc 3 * Λ ≤ (m : ℝ) :=
            ((le_max_left (3 * Λ) (M0 : ℝ)).trans (le_max_right _ _)).trans hm₁m
        _ ≤ (m : ℝ) ^ 8 := le_self_pow₀ hm1 (by norm_num)
        _ ≤ (3 : ℝ) ^ hm' := hpow
    have h2 : 3 * Λ * (3 : ℝ) ^ ((n : ℤ) - 3) ≤ (3 : ℝ) ^ hm' * (3 : ℝ) ^ ((n : ℤ) - 3) :=
      mul_le_mul_of_nonneg_right h1 hjpos.le
    have h4 : (3 : ℝ) ^ hm' * (3 : ℝ) ^ ((n : ℤ) - 3) = (3 : ℝ) ^ m := by
      rw [mul_comm]; exact h3j
    linarith only [h2, h4, h3t]
  have hWsub : t • U ⊆ openCubeSet (originCube d (m : ℤ)) :=
    w0_smul_subset_openCubeSet_originCube hUc ht0 (m : ℤ) (by rw [zpow_natCast]; exact htm)
  have hR : ∀ x ∈ t • U, ∀ i, |x i| ≤ (3 : ℝ) ^ m := by
    intro x hx i
    have h := hWsub hx i
    simp only [originCube, cubeScaleFactor, Pi.zero_apply, Int.cast_zero, zero_sub,
      zero_add] at h
    change -(1 / 2) * (3 : ℝ) ^ (m : ℤ) < x i ∧ x i < 1 / 2 * (3 : ℝ) ^ (m : ℤ) at h
    rw [zpow_natCast] at h
    have : (0 : ℝ) < 3 ^ m := by positivity
    rw [abs_le]
    constructor <;> linarith only [h.1, h.2, this]
  have hWfin : volume (t • U) ≠ ⊤ := by
    have hsub : t • U ⊆ wh1_box (0 : Vec d) ((3 : ℝ) ^ m + 1) := by
      intro x hx i
      have := hR x hx i
      show |x i - (0 : Vec d) i| < _
      simp only [Pi.zero_apply, sub_zero]
      linarith only [this]
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [wh1_volume_box _ (by positivity)]
    exact ENNReal.ofReal_ne_top
  have hCpos : 0 < max (max C₂ 8) Γ :=
    lt_of_lt_of_le (by norm_num) (le_max_of_le_left (le_max_right _ _))
  by_cases hf : AEStronglyMeasurable f (volume.restrict (t • U))
  swap
  · rw [wh3_lpBar_top hWfin hf]
    have hb : ENNReal.ofReal (max (max C₂ 8) Γ * D *
        (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) * nu⁻¹) ≠ 0 := by
      refine (ENNReal.ofReal_pos.2 ?_).ne'
      have : 0 < D := by linarith only [hD]
      positivity
    rw [ENNReal.mul_top hb, add_top]
    exact le_top
  have hu_meas : AEStronglyMeasurable (fun x => u.toFun x - ⨍ z in t • U, u.toFun z)
      (volume.restrict (t • U)) :=
    u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hg_meas : AEStronglyMeasurable (fun x => eucNorm (u.grad x))
      (volume.restrict (t • U)) := (memLp_eucNorm_grad u).aestronglyMeasurable
  have hfm : AEMeasurable f (volume.restrict (t • U)) := hf.aemeasurable
  have Hn' := Hn U hUc u f hfm hsol
  obtain ⟨e1, e2⟩ := wh3_pow27 n
  have hP' := hPoinc
  rw [← hjm] at hP'
  have key := hdet (j := (n : ℤ) - 3) ht0 hR hjT htm hD hnu hσpos hlow hKI hΛt u f _ hP'
    (fun Z hZ => by
      have := Hn' Z (fun k hk => by
        show translateSet (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
          (openCubeSet (originCube d (n : ℤ))) ⊆ t • U
        rw [← wh2_box_eq]
        exact hZ k hk)
      rw [e1, e2] at this
      exact this)
  have hD0 : 0 < D := by linarith only [hD]
  have hT0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hs0 : 0 ≤ (Real.sqrt σb)⁻¹ * Real.sqrt nu := by positivity
  have ha : 0 ≤ Γ * D * (3 : ℝ) ^ m * ((Real.sqrt σb)⁻¹ * Real.sqrt nu) := by positivity
  have hb : 0 ≤ Γ * D * (3 : ℝ) ^ m * (3 : ℝ) ^ ((n : ℤ) - 3) / nu := by positivity
  have hsq := wh3_sqrt_step
    (E := eLpNorm (fun x => u.toFun x - ⨍ z in t • U, u.toFun z) 2 (volume.restrict (t • U)))
    (Eg := eLpNorm (fun x => eucNorm (u.grad x)) 2 (volume.restrict (t • U)))
    (Ef := eLpNorm f 2 (volume.restrict (t • U))) ha hb (by
    rw [wh3_eLpNorm_sq hu_meas, wh3_eLpNorm_sq hg_meas, wh3_eLpNorm_sq hf]
    exact key)
  have hfinal := wh3_lpBar_final hu_meas hg_meas hf hsq
  refine hfinal.trans ?_
  have e3 : (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) =
      (3 : ℝ) ^ m * (3 : ℝ) ^ ((n : ℤ) - 3) := by
    have : 2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ) = (m : ℝ) + (((n : ℤ) - 3 : ℤ) : ℝ) := by
      have h := congrArg (Int.cast (R := ℝ)) hjm
      push_cast at h ⊢
      linarith only [h]
    rw [this, Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_intCast]
  have ha' : Γ * D * (3 : ℝ) ^ m * ((Real.sqrt σb)⁻¹ * Real.sqrt nu) ≤
      max (max C₂ 8) Γ * D * (3 : ℝ) ^ m * (Real.sqrt σb)⁻¹ * Real.sqrt nu := by
    rw [mul_assoc (max (max C₂ 8) Γ * D * (3 : ℝ) ^ m)]
    gcongr
  have hb' : Γ * D * (3 : ℝ) ^ m * (3 : ℝ) ^ ((n : ℤ) - 3) / nu ≤
      max (max C₂ 8) Γ * D * (3 : ℝ) ^ (2 * (m : ℝ) - (⌈M * Real.log (m : ℝ)⌉ : ℝ)) * nu⁻¹ := by
    rw [e3]
    calc Γ * D * (3 : ℝ) ^ m * (3 : ℝ) ^ ((n : ℤ) - 3) / nu
        = (Γ * D * ((3 : ℝ) ^ m * (3 : ℝ) ^ ((n : ℤ) - 3))) * nu⁻¹ := by ring
      _ ≤ (max (max C₂ 8) Γ * D * ((3 : ℝ) ^ m * (3 : ℝ) ^ ((n : ℤ) - 3))) * nu⁻¹ := by gcongr
      _ = _ := by ring
  gcongr


/-- Satisfiability: the Poincare hypothesis of `wh3_whitney_poincare` holds on a smooth bounded
domain inside the unit origin cube (the Euclidean ball of radius `1/2`), for every large dilate. -/
example [NeZero d] := @rc_whitney_hypothesis_witness d _

end SuperdiffusionCLT.Section7
