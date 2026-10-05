/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsM

/-!
# The generator approximation for one sample

`gen_core`: for one sample at which the decay estimate and the resolvent estimates hold, and
`u ∈ C_c^∞`, the functions `u^ε` of `p.generators`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal Pointwise Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_core [NeZero d] (hd : 2 ≤ d) {nu cs : ℝ} (hnu : 0 < nu) (hcs : 0 < cs)
    {omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega))
    (hS : ContDiff ℝ 2 (fullStreamRecentered omega))
    (hEll : ∀ ε : ℝ, ε ≠ 0 → ∀ W : Set (Vec d), Bornology.IsBounded W → MeasurableSet W →
      ∃ Lam, IsEllipticFieldOn nu Lam W (epCoeff nu omega ε))
    {γ Cd Xd : ℝ} (hγ : 0 < γ) (hCd : 0 ≤ Cd) (hXd : 0 < Xd)
    (hdec : ∀ ε : ℝ, 0 < ε → Xd ≤ ε⁻¹ →
      ∀ r R : ℝ, 8 ≤ r → r ≤ R → ∀ (u : H10Function (euclidBall (d := d) R))
      (F : Vec d → ℝ), MemLp F 2 (volume.restrict (euclidBall (d := d) 1)) →
      (∀ x, x ∉ euclidBall (d := d) 1 → F x = 0) → (∫ x in euclidBall (d := d) 1, F x = 0) →
      IsWeakSolutionOn (fun x => opScale cs ε • epCoeff nu omega ε x)
        (euclidBall R) u.toH1Function F (fun _ => 0) →
      eLpNorm u.toH1Function.toFun ⊤ (volume.restrict (euclidBall (d := d) R \ euclidBall r)) ≤
        ENNReal.ofReal (Cd * r ^ (-((d : ℝ) - 2 + γ))) *
          eLpNorm F 2 (volume.restrict (euclidBall (d := d) 1)))
    {α : ℝ} (hα : 0 < α) (Cm Zm : ℕ → ℝ) (hCm : ∀ m, 16 ≤ m → 0 ≤ Cm m)
    (hroot : ∀ m : ℕ, 16 ≤ m → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Zm m ≤ ε⁻¹ →
      ∀ (f : Vec d → ℝ) (g u uhom : H1Function (euclidBall (d := d) (m : ℝ))),
      IsDirichletSolution (fun x => opScale cs ε • epField nu omega ε x)
        (euclidBall (m : ℝ)) (fun x => f x - 0 * u.toFun x) g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclidBall (m : ℝ))
        (fun x => f x - 0 * uhom.toFun x) g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ))) ≤
        ENNReal.ofReal (4 * (Cm m * |Real.log ε| ^ (-α))) *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (euclidBall (m : ℝ))) +
            eLpNorm (fun x => f x - 0 * u.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ)))))
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcsu : HasCompactSupport u) :
    ∃ uep : ℝ → Vec d → ℝ,
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ContDiff ℝ 2 (uep ε) ∧ IsC0Function (uep ε) ∧
          IsC0Function (divForm (opScale cs ε) (epCoeff nu omega ε) (uep ε))) ∧
      Tendsto (fun ε : ℝ => ⨆ x : Vec d, ENNReal.ofReal |uep ε x - u x|) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ε : ℝ => ⨆ x : Vec d, ENNReal.ofReal
        |divForm (opScale cs ε) (epCoeff nu omega ε) (uep ε) x -
          (1 / 2) * Brownian.vecLaplacian u x|) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨ρ, hρ, u0, hu0, hu0s, hu0u⟩ := gen_prep_u hu hcsu
  subst hu0u
  have hρ0 : 0 < ρ := by linarith only [hρ]
  have hu0c : HasCompactSupport u0 := by
    refine HasCompactSupport.intro (K := tsupport u0) ?_ fun x hx => image_eq_zero_of_notMem_tsupport hx
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _) ?_
    exact (Metric.isBounded_ball.subset (euclidBall_subset_ball zero_lt_one)).subset hu0s
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hu : ContDiff ℝ (⊤ : ℕ∞) fun x => u0 (ρ⁻¹ • x) := hu0.comp (contDiff_const_smul _)
  obtain ⟨M0, hM0⟩ := hu0.continuous.bounded_above_of_compact_support hu0c
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, ∀ y, |(1 / 2) * Brownian.vecLaplacian u0 y| ≤ B0 := by
    have hc : Continuous fun y => (1 / 2) * Brownian.vecLaplacian u0 y :=
      continuous_const.mul (gen_lap_contDiff hu0).continuous
    have hs : HasCompactSupport fun y => (1 / 2) * Brownian.vecLaplacian u0 y :=
      (gen_lap_hasCompactSupport hu0c).mul_left (f := fun _ => (1 / 2 : ℝ))
    obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨B, fun y => by simpa [Real.norm_eq_abs] using hB y⟩
  have hM0' : ∀ y, |u0 y| ≤ M0 := fun y => by simpa [Real.norm_eq_abs] using hM0 y
  have hεpos : ∀ ε : ℝ, 0 < ε → 0 < ε / ρ := fun ε h => div_pos h hρ0
  have hinv : ∀ ε : ℝ, 0 < ε → ε⁻¹ ≤ (ε / ρ)⁻¹ := fun ε h => by
    rw [inv_div, inv_eq_one_div]; exact div_le_div_of_nonneg_right hρ h.le
  have hconstr := fun (ε : ℝ) (h : 0 < ε ∧ ε ≤ 1 / 2 ∧ Xd ≤ ε⁻¹) =>
    gen_eps_construction hd hnu hcs D hS hu0 hu0s hρ h.1 h.2.1
      (fun W hb hm => hEll (ε / ρ) (hεpos ε h.1).ne' W hb hm) hγ hCd
      (hdec (ε / ρ) (hεpos ε h.1) (h.2.2.trans (hinv ε h.1))) hB0 hM0'
  classical
  let uep : ℝ → Vec d → ℝ := fun ε =>
    if h : (0 < ε ∧ ε ≤ 1 / 2 ∧ Xd ≤ ε⁻¹) then Classical.choose (hconstr ε h)
    else fun x => u0 (ρ⁻¹ • x)
  have hdef : ∀ (ε : ℝ) (h : 0 < ε ∧ ε ≤ 1 / 2 ∧ Xd ≤ ε⁻¹),
      uep ε = Classical.choose (hconstr ε h) := fun ε h => by
    simp only [uep]
    split_ifs
    rfl
  have hdef' : ∀ ε : ℝ, ¬ (0 < ε ∧ ε ≤ 1 / 2 ∧ Xd ≤ ε⁻¹) → uep ε = fun x => u0 (ρ⁻¹ • x) :=
    fun ε h => by
    simp only [uep]
    split_ifs
    rfl
  have hLu : IsC0Function fun z => (1 / 2) * Brownian.vecLaplacian (fun x => u0 (ρ⁻¹ • x)) z :=
    gen_isC0_of_compactSupport (continuous_const.mul (gen_lap_contDiff hu).continuous)
      ((gen_lap_hasCompactSupport hcsu).mul_left (f := fun _ => (1 / 2 : ℝ)))
  have hP1 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ContDiff ℝ 2 (uep ε) ∧ IsC0Function (uep ε) ∧
        IsC0Function (divForm (opScale cs ε) (epCoeff nu omega ε) (uep ε)) := by
    intro ε hε hε2
    by_cases h : Xd ≤ ε⁻¹
    · have hh : 0 < ε ∧ ε ≤ 1 / 2 ∧ Xd ≤ ε⁻¹ := ⟨hε, hε2, h⟩
      obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (hconstr ε hh)
      rw [← hdef ε hh] at h1 h2 h3
      refine ⟨h1, h2, ?_⟩
      have : divForm (opScale cs ε) (epCoeff nu omega ε) (uep ε) =
          fun z => (1 / 2) * Brownian.vecLaplacian (fun x => u0 (ρ⁻¹ • x)) z := funext h3
      rw [this]; exact hLu
    · rw [hdef' ε (fun hh => h hh.2.2)]
      exact ⟨hu.of_le (by simp), gen_isC0_of_compactSupport hu.continuous hcsu,
        gen_divForm_isC0 nu _ omega ε hS hu hcsu⟩
  have hev0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, (0 < ε ∧ ε ≤ 1 / 2 ∧ Xd ≤ ε⁻¹) := by
    have hb : (0 : ℝ) < min (1 / 2) Xd⁻¹ := lt_min (by norm_num) (inv_pos.2 hXd)
    filter_upwards [Ioo_mem_nhdsGT hb] with ε hε
    refine ⟨hε.1, hε.2.le.trans (min_le_left _ _), ?_⟩
    rw [le_inv_comm₀ hXd hε.1]
    exact hε.2.le.trans (min_le_right _ _)
  have hT2 : Tendsto (fun ε : ℝ => ⨆ x : Vec d, ENNReal.ofReal
      |divForm (opScale cs ε) (epCoeff nu omega ε) (uep ε) x -
        (1 / 2) * Brownian.vecLaplacian (fun x => u0 (ρ⁻¹ • x)) x|) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev0] with ε hh
    obtain ⟨-, -, h3, -⟩ := Classical.choose_spec (hconstr ε hh)
    rw [← hdef ε hh] at h3
    simp [h3]
  refine ⟨uep, hP1, ?_, hT2⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro t ht
  obtain ⟨η, hη, hηt⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ t := by
    rcases eq_or_ne t ⊤ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨t.toReal, ENNReal.toReal_pos ht.ne' h, by rw [ENNReal.ofReal_toReal h]⟩
  set E0 : ℝ := (eLpNorm (fun y => (1 / 2) * Brownian.vecLaplacian u0 y) 2
    (volume.restrict (euclidBall (d := d) 1))).toReal with hE0
  have hE00 : 0 ≤ E0 := ENNReal.toReal_nonneg
  have hexp : 0 < (d : ℝ) - 2 + γ := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this, hγ]
  have hmT : ∀ᶠ m : ℕ in atTop,
      Cd * ((m : ℝ) / 2) ^ (-((d : ℝ) - 2 + γ)) * (2 * E0) < η / 3 := by
    have h1 : Tendsto (fun m : ℕ => ((m : ℝ) / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    have h2 := (((tendsto_rpow_neg_atTop hexp).comp h1).const_mul Cd).mul_const (2 * E0)
    rw [mul_zero, zero_mul] at h2
    exact h2.eventually (gt_mem_nhds (by linarith only [hη]))
  obtain ⟨m, hmT', hm16⟩ := (hmT.and (eventually_ge_atTop 16)).exists
  have hs := gen_scale_ratio_tendsto hcs hρ0
  have hl := gen_logpow_tendsto hρ0 hα
  set Φ : ℝ → ℝ := fun ε => 4 * (Cm m * |Real.log (ε / ρ)| ^ (-α)) *
    ((opScale cs (ε / ρ) / opScale cs ε) * B0) +
    |opScale cs (ε / ρ) / opScale cs ε - 1| * M0 with hΦdef
  have hΦ : Tendsto Φ (𝓝[>] 0) (𝓝 0) := by
    have := (((tendsto_const_nhds (x := (4 : ℝ))).mul ((tendsto_const_nhds (x := Cm m)).mul hl)).mul (hs.mul_const B0)).add
      (((hs.sub_const 1).abs).mul_const M0)
    simpa using this
  have hΦ' : ∀ᶠ ε in 𝓝[>] 0, Φ ε < 2 * η / 3 :=
    hΦ.eventually (gt_mem_nhds (by linarith only [hη]))
  have hs2 : ∀ᶠ ε in 𝓝[>] 0, opScale cs (ε / ρ) / opScale cs ε < 2 :=
    hs.eventually (gt_mem_nhds (by norm_num))
  have hZ : ∀ᶠ ε : ℝ in 𝓝[>] 0, Zm m ≤ ε⁻¹ := by
    have hb : (0 : ℝ) < (|Zm m| + 1)⁻¹ := by positivity
    filter_upwards [Ioo_mem_nhdsGT hb] with ε hε
    have : |Zm m| + 1 ≤ ε⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hε.1]; exact hε.2.le
    linarith only [this, le_abs_self (Zm m)]
  filter_upwards [hev0, hΦ', hs2, hZ] with ε hh hΦε hsε hZε
  refine le_trans ?_ hηt
  refine iSup_le fun z => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨h1, h2, h3, h4⟩ := Classical.choose_spec (hconstr ε hh)
  rw [← hdef ε hh] at h1 h2 h3 h4
  have hε' : 0 < ε / ρ := hεpos ε hh.1
  have hε'2 : ε / ρ ≤ 1 / 2 := (div_le_self hh.1.le hρ).trans hh.2.1
  have hCe : 0 ≤ 4 * (Cm m * |Real.log (ε / ρ)| ^ (-α)) :=
    mul_nonneg (by norm_num) (mul_nonneg (hCm m hm16) (Real.rpow_nonneg (abs_nonneg _) _))
  have hb := h4 m hm16 _ hCe (hroot m hm16 (ε / ρ) hε' hε'2 (hZε.trans (hinv ε hh.1))) z
  set s : ℝ := opScale cs (ε / ρ) / opScale cs ε with hsdef
  have hT1 : Cd * ((m : ℝ) / 2) ^ (-((d : ℝ) - 2 + γ)) * (s * E0) ≤
      Cd * ((m : ℝ) / 2) ^ (-((d : ℝ) - 2 + γ)) * (2 * E0) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsε.le hE00)
      (mul_nonneg hCd (Real.rpow_nonneg (by positivity) _))
  show |uep ε z - u0 (ρ⁻¹ • z)| ≤ η
  have hΦe : Φ ε = 4 * (Cm m * |Real.log (ε / ρ)| ^ (-α)) * (s * B0) + |s - 1| * M0 := rfl
  linarith only [hb, hT1, hmT', hΦε, hΦe]

end SuperdiffusionCLT.Section8
