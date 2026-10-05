/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsJ
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApiB
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateD

/-!
# The approximate corrector at one scale

`gen_eps_construction`: for a smooth `u₀` supported in the unit ball and the dilate
`u(x) = u₀(x/ρ)`, one scale `ε` and one sample at which the decay estimate and the resolvent
estimate on the balls `B_m` hold, there is `v ∈ C² ∩ C₀` with `L^ε v = ½Δu` pointwise and an
explicit bound for `|v - u|`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal Pointwise Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_eLpNorm_smul_toReal {μ : Measure (Vec d)} (s : ℝ) (hs : 0 ≤ s) (g : Vec d → ℝ) :
    (eLpNorm (fun y => (-s) * g y) 2 μ).toReal = s * (eLpNorm g 2 μ).toReal := by
  have := eLpNorm_const_smul (p := (2 : ℝ≥0∞)) (μ := μ) (-s) g
  have e : (fun y => (-s) * g y) = (-s) • g := rfl
  rw [e, this, ENNReal.toReal_mul, enorm_neg, Real.enorm_eq_ofReal hs, ENNReal.toReal_ofReal hs]

theorem gen_eps_construction [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) {cs : ℝ} (hcs : 0 < cs)
    {omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega))
    (hS : ContDiff ℝ 2 (fullStreamRecentered omega))
    {u0 : Vec d → ℝ} (hu0 : ContDiff ℝ (⊤ : ℕ∞) u0) (hu0s : tsupport u0 ⊆ euclidBall (d := d) 1)
    {ρ ε : ℝ} (hρ : 1 ≤ ρ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hEllEp : ∀ W : Set (Vec d), Bornology.IsBounded W → MeasurableSet W →
      ∃ Lam, IsEllipticFieldOn nu Lam W (epCoeff nu omega (ε / ρ)))
    {γ Cd : ℝ} (hγ : 0 < γ) (hCd : 0 ≤ Cd)
    (hdecay : ∀ r R : ℝ, 8 ≤ r → r ≤ R → ∀ (u : H10Function (euclidBall (d := d) R))
      (F : Vec d → ℝ), MemLp F 2 (volume.restrict (euclidBall (d := d) 1)) →
      (∀ x, x ∉ euclidBall (d := d) 1 → F x = 0) → (∫ x in euclidBall (d := d) 1, F x = 0) →
      IsWeakSolutionOn (fun x => opScale cs (ε / ρ) • epCoeff nu omega (ε / ρ) x)
        (euclidBall R) u.toH1Function F (fun _ => 0) →
      eLpNorm u.toH1Function.toFun ⊤ (volume.restrict (euclidBall (d := d) R \ euclidBall r)) ≤
        ENNReal.ofReal (Cd * r ^ (-((d : ℝ) - 2 + γ))) *
          eLpNorm F 2 (volume.restrict (euclidBall (d := d) 1)))
    {B0 M0 : ℝ} (hB0 : ∀ y, |(1 / 2) * Brownian.vecLaplacian u0 y| ≤ B0) (hM0 : ∀ y, |u0 y| ≤ M0) :
    ∃ v : Vec d → ℝ, ContDiff ℝ 2 v ∧ IsC0Function v ∧
      (∀ z, divForm (opScale cs ε) (epCoeff nu omega ε) v z =
        (1 / 2) * Brownian.vecLaplacian (fun x => u0 (ρ⁻¹ • x)) z) ∧
      ∀ m : ℕ, 16 ≤ m → ∀ Ce : ℝ, 0 ≤ Ce →
      (∀ (f : Vec d → ℝ) (g u uhom : H1Function (euclidBall (d := d) (m : ℝ))),
        IsDirichletSolution (fun x => opScale cs (ε / ρ) • epField nu omega (ε / ρ) x)
          (euclidBall (m : ℝ)) (fun x => f x - 0 * u.toFun x) g u →
        IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclidBall (m : ℝ))
          (fun x => f x - 0 * uhom.toFun x) g uhom →
        eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ))) ≤
          ENNReal.ofReal Ce *
            (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (euclidBall (m : ℝ))) +
              eLpNorm (fun x => f x - 0 * u.toFun x) ⊤ (volume.restrict (euclidBall (m : ℝ))))) →
      ∀ z, |v z - u0 (ρ⁻¹ • z)| ≤
        Cd * ((m : ℝ) / 2) ^ (-((d : ℝ) - 2 + γ)) *
            ((opScale cs (ε / ρ) / opScale cs ε) *
              (eLpNorm (fun y => (1 / 2) * Brownian.vecLaplacian u0 y) 2
                (volume.restrict (euclidBall (d := d) 1))).toReal) +
          Ce * ((opScale cs (ε / ρ) / opScale cs ε) * B0) +
          |opScale cs (ε / ρ) / opScale cs ε - 1| * M0 := by
  have hρ0 : 0 < ρ := by linarith only [hρ]
  have hε' : 0 < ε / ρ := div_pos hε hρ0
  have hε'1 : ε / ρ < 1 := by
    have : ε / ρ ≤ ε := div_le_self hε.le hρ
    linarith only [this, hε2]
  have hc : 0 < opScale cs ε := exitEst_opScale_pos hcs hε (by linarith only [hε2])
  have hc' : 0 < opScale cs (ε / ρ) := exitEst_opScale_pos hcs hε' hε'1
  set s : ℝ := opScale cs (ε / ρ) / opScale cs ε with hs
  have hs0 : 0 < s := div_pos hc' hc
  have hu0c : HasCompactSupport u0 := by
    refine HasCompactSupport.intro (K := tsupport u0) ?_ fun x hx => image_eq_zero_of_notMem_tsupport hx
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _) ?_
    exact (Metric.isBounded_ball.subset (euclidBall_subset_ball zero_lt_one)).subset hu0s
  set G : Vec d → ℝ := fun y => -(s * ((1 / 2) * Brownian.vecLaplacian u0 y)) with hG
  have hG1 : ContDiff ℝ 1 G :=
    (contDiff_const.mul (contDiff_const.mul (gen_lap_contDiff hu0))).neg
  have hGc : Continuous G := hG1.continuous
  have hGs : HasCompactSupport G :=
    HasCompactSupport.intro hu0c.isCompact fun x hx => by simp [hG, gen_lap_eq_zero hx]
  have hGsupp : ∀ x, x ∉ euclidBall (d := d) 1 → G x = 0 := fun x hx => by
    simp [hG, gen_lap_eq_zero (fun h => hx (hu0s h))]
  have hGmean : ∫ x in euclidBall (d := d) 1, G x = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hGsupp]
    have : G = fun x => (-(s * (1 / 2))) * Brownian.vecLaplacian u0 x := by
      funext x; simp only [hG]; ring
    rw [this, integral_const_mul, gen_integral_lap hu0 hu0c, mul_zero]
  have hEll' : ∀ W : Set (Vec d), Bornology.IsBounded W → MeasurableSet W →
      ∃ Lam, IsEllipticFieldOn nu Lam W (epCoeff nu omega (ε / ρ)) := hEllEp
  obtain ⟨U, hU2, hU0, hUeq, hUm⟩ := gen_fixed_scale hd hnu cs D hS hε' hc' hEll' hγ hCd
    hdecay hG1 hGs hGsupp hGmean
  have hρne : ρ ≠ 0 := hρ0.ne'
  refine ⟨fun z => U (ρ⁻¹ • z), hU2.comp (contDiff_const_smul _), ?_, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := hU0
    exact ⟨fd_dilC0 ρ⁻¹ (inv_ne_zero hρne) g, by funext x; rw [fd_dilC0_apply, hg]⟩
  · intro z
    rw [gen_divForm_dilate nu _ omega hε hρ0, gen_divForm_scaled _ (opScale cs (ε / ρ)) hc'.ne',
      hUeq, gen_lap_comp_smul (hu0.of_le (by simp) : ContDiff ℝ 2 u0) (inv_ne_zero hρne)]
    simp only [hG, hs]
    field_simp
  · intro m hm Ce hCe hhom z
    obtain ⟨wR, uR, hwc, hw0, hae, hsol, hb⟩ := hUm m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hGb : ∀ y, |G y| ≤ s * B0 := fun y => by
      simp only [hG, abs_neg]
      rw [abs_mul, abs_of_pos hs0]
      exact mul_le_mul_of_nonneg_left (hB0 y) hs0.le
    have hhb := gen_hom_bound (m := (m : ℝ)) hm1 hCe hhom hu0 hu0s s (fun y => rfl)
      hGc hGb hwc hw0 uR hae hsol (ρ⁻¹ • z)
    have hE : (eLpNorm G 2 (volume.restrict (euclidBall (d := d) 1))).toReal =
        s * (eLpNorm (fun y => (1 / 2) * Brownian.vecLaplacian u0 y) 2
          (volume.restrict (euclidBall (d := d) 1))).toReal := by
      rw [← gen_eLpNorm_smul_toReal s hs0.le]
      congr 3
      funext y; simp only [hG]; ring
    have h1 := hb (ρ⁻¹ • z)
    rw [hE] at h1
    have h3 : |s * u0 (ρ⁻¹ • z) - u0 (ρ⁻¹ • z)| ≤ |s - 1| * M0 := by
      rw [show s * u0 (ρ⁻¹ • z) - u0 (ρ⁻¹ • z) = (s - 1) * u0 (ρ⁻¹ • z) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM0 _) (abs_nonneg _)
    calc |U (ρ⁻¹ • z) - u0 (ρ⁻¹ • z)|
        = |(U (ρ⁻¹ • z) - wR (ρ⁻¹ • z)) + (wR (ρ⁻¹ • z) - s * u0 (ρ⁻¹ • z)) +
            (s * u0 (ρ⁻¹ • z) - u0 (ρ⁻¹ • z))| := by ring_nf
      _ ≤ |U (ρ⁻¹ • z) - wR (ρ⁻¹ • z)| + |wR (ρ⁻¹ • z) - s * u0 (ρ⁻¹ • z)| +
            |s * u0 (ρ⁻¹ • z) - u0 (ρ⁻¹ • z)| := abs_add_three _ _ _
      _ ≤ _ := by linarith only [h1, hhb, h3]

end SuperdiffusionCLT.Section8
