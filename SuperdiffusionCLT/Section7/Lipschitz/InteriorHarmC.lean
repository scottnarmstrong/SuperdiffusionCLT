/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarmB
public import SuperdiffusionCLT.Section7.Prereq.WellPosed
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The interior harmonic approximation from the `L²` block

`lip_int_harm_of_l2` (`e.Dir.new.L2.homog` on a domain between `□_{k-2}` and `□_{k-1}` together
with the interior Caccioppoli block): the interior harmonic approximation `LipHarmInt` at the scale
`k`.  A right-hand side that is not almost everywhere measurable is handled first: then the
solution is harmonic for the field `a` (`lip_int_harm_of_l2_weak_zero_of_not_meas`).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal
namespace SuperdiffusionCLT.Section7
variable {d : ℕ}

/-- A function that is not almost everywhere measurable on an open set fails to be so on every
small ball around some point of the set. -/
theorem lip_int_harm_of_l2_exists_bad_point {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ¬ AEStronglyMeasurable f (volume.restrict W)) :
    ∃ x ∈ W, ∀ ρ : ℝ, 0 < ρ → Metric.ball x ρ ⊆ W →
      ¬ AEStronglyMeasurable f (volume.restrict (Metric.ball x ρ)) := by
  by_contra hno
  push Not at hno
  have hch : ∀ x ∈ W, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ W ∧
      AEStronglyMeasurable f (volume.restrict (Metric.ball x ρ)) := by
    intro x hx
    exact hno x hx
  choose! ρ hρ hρW hρm using hch
  obtain ⟨t, htW, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => Metric.ball x (ρ x)) (s := W)
    (fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (hρ x hx)))
  have : Countable t := htc.to_subtype
  refine hf ?_
  have hU : AEStronglyMeasurable f (volume.restrict (⋃ x ∈ t, Metric.ball x (ρ x))) := by
    rw [Set.biUnion_eq_iUnion, aestronglyMeasurable_iUnion_iff]
    exact fun i => hρm i (htW i.2)
  exact hU.mono_measure (Measure.restrict_mono hcov le_rfl)

theorem lip_int_harm_of_l2_lin2 {x y t₁ t₂ : ℝ} (h : t₁ ≠ t₂) (e₁ : x + t₁ * y = 0)
    (e₂ : x + t₂ * y = 0) : x = 0 := by
  have h1 : (t₂ - t₁) * y = 0 := by linarith only [e₁, e₂]
  have h2 : y = 0 := by
    rcases mul_eq_zero.1 h1 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm h
    · exact h3
  rw [h2] at e₁
  linarith only [e₁]

theorem lip_int_harm_of_l2_bump (x : Vec d) {W : Set (Vec d)} (hW : IsOpen W) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball x ρ ⊆ W) :
    ∃ φ : H10Function W, ∀ y ∈ Metric.ball x (ρ / 2), 0 < φ.toH1Function.toFun y := by
  let b : ContDiffBump x := ⟨ρ / 4, ρ / 2, by positivity, by linarith only [hρ]⟩
  have hmem : MemH10 W (⇑b) := by
    refine memH10_of_contDiff hW (b.contDiff (n := ⊤)) b.hasCompactSupport ?_
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show ρ / 2 < ρ; linarith only [hρ])).trans hball
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨φ, fun y hy => ?_⟩
  rw [hφ]
  exact b.pos_of_mem_ball hy

/-- **A non-measurable right-hand side forces a harmonic solution.** If `u` solves the equation
with a datum `f` that is not almost everywhere measurable, then `u` solves it with datum zero: the
equation tested against two functions `ψ + t φ₀` with `f φ₀` non-measurable cannot involve `f`. -/
theorem lip_int_harm_of_l2_weak_zero_of_not_meas {W : Set (Vec d)} (hW : IsOpen W) {lam Lam : ℝ}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam W a) {u : H1Function W} {f : Vec d → ℝ}
    (hu : IsWeakSolutionOn a W u f (fun _ => 0))
    (hf : ¬ AEStronglyMeasurable f (volume.restrict W)) :
    IsWeakSolutionOn a W u (fun _ => 0) (fun _ => 0) := by
  obtain ⟨x, hxW, hx⟩ := lip_int_harm_of_l2_exists_bad_point hf
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW x hxW
  have hεW2 : Metric.ball x (ε / 2) ⊆ W :=
    (Metric.ball_subset_ball (by linarith only [hε])).trans hεW
  obtain ⟨φ0, hφ0⟩ := lip_int_harm_of_l2_bump x hW hε hεW
  have hbad : ¬ AEStronglyMeasurable (fun y => f y * φ0.toH1Function.toFun y)
      (volume.restrict W) := by
    intro hm
    refine hx (ε / 2) (by linarith only [hε]) hεW2 ?_
    have hm2 : AEStronglyMeasurable (fun y => f y * φ0.toH1Function.toFun y)
        (volume.restrict (Metric.ball x (ε / 2))) :=
      hm.mono_measure (Measure.restrict_mono hεW2 le_rfl)
    have hinv : AEStronglyMeasurable (fun y => (φ0.toH1Function.toFun y)⁻¹)
        (volume.restrict (Metric.ball x (ε / 2))) :=
      (((φ0.toH1Function.memL2.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono hεW2 le_rfl)).aemeasurable).inv).aestronglyMeasurable
    refine (hm2.mul hinv).congr ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
    simp only [Pi.mul_apply]
    rw [mul_assoc, mul_inv_cancel₀ (hφ0 y hy).ne', mul_one]
  intro ψ
  simp only [vecDot_zero_left, integral_zero, zero_mul, add_zero]
  set F : Vec d → Vec d := fun y => matVecMul (a y) (u.grad y) with hF
  have hint : ∀ φ : H10Function W,
      IntegrableOn (fun y => vecDot (F y) (φ.toH1Function.grad y)) W :=
    fun φ => w0_integrableOn_flux hEll u φ
  have heq : ∀ t : ℝ, ∫ y in W, vecDot (F y) ((ψ + t • φ0).toH1Function.grad y) =
      ∫ y in W, f y * (ψ + t • φ0).toH1Function.toFun y := by
    intro t
    have := hu (ψ + t • φ0)
    simpa only [vecDot_zero_left, integral_zero, add_zero] using this
  have hlin : ∀ t : ℝ, ∫ y in W, vecDot (F y) ((ψ + t • φ0).toH1Function.grad y) =
      (∫ y in W, vecDot (F y) (ψ.toH1Function.grad y)) +
        t * ∫ y in W, vecDot (F y) (φ0.toH1Function.grad y) := by
    intro t
    have : ∀ y, vecDot (F y) ((ψ + t • φ0).toH1Function.grad y) =
        vecDot (F y) (ψ.toH1Function.grad y) + t * vecDot (F y) (φ0.toH1Function.grad y) :=
      fun y => by
        show vecDot (F y) (ψ.toH1Function.grad y + t • φ0.toH1Function.grad y) = _
        rw [vecDot_add_right, vecDot_smul_right]
    simp only [this]
    rw [integral_add (hint ψ) ((hint φ0).const_mul t), integral_const_mul]
  have hn : ∀ t : ℝ, ¬ AEStronglyMeasurable
      (fun y => f y * (ψ + t • φ0).toH1Function.toFun y) (volume.restrict W) →
      (∫ y in W, vecDot (F y) (ψ.toH1Function.grad y)) +
        t * ∫ y in W, vecDot (F y) (φ0.toH1Function.grad y) = 0 := by
    intro t ht
    rw [← hlin t, heq t]
    exact integral_undef (fun hi => ht hi.aestronglyMeasurable)
  have hex : ∀ t t' : ℝ, t ≠ t' →
      AEStronglyMeasurable (fun y => f y * (ψ + t • φ0).toH1Function.toFun y)
        (volume.restrict W) →
      AEStronglyMeasurable (fun y => f y * (ψ + t' • φ0).toH1Function.toFun y)
        (volume.restrict W) → False := by
    intro t t' htt h1 h2
    refine hbad ?_
    have h3 := (h1.sub h2).const_mul (t - t')⁻¹
    refine h3.congr (Filter.Eventually.of_forall fun y => ?_)
    have e : (ψ + t • φ0).toH1Function.toFun y = ψ.toH1Function.toFun y +
        t * φ0.toH1Function.toFun y := rfl
    have e' : (ψ + t' • φ0).toH1Function.toFun y = ψ.toH1Function.toFun y +
        t' * φ0.toH1Function.toFun y := rfl
    have hne : t - t' ≠ 0 := sub_ne_zero.2 htt
    simp only [Pi.sub_apply, e, e']
    field_simp
    ring
  by_cases m0 : AEStronglyMeasurable (fun y => f y * (ψ + (0 : ℝ) • φ0).toH1Function.toFun y)
      (volume.restrict W)
  · have n1 := fun h => hex 0 1 (by norm_num) m0 h
    have n2 := fun h => hex 0 2 (by norm_num) m0 h
    exact lip_int_harm_of_l2_lin2 (t₁ := 1) (t₂ := 2) (by norm_num) (hn 1 n1) (hn 2 n2)
  · by_cases m1 : AEStronglyMeasurable
        (fun y => f y * (ψ + (1 : ℝ) • φ0).toH1Function.toFun y) (volume.restrict W)
    · have n2 := fun h => hex 1 2 (by norm_num) m1 h
      exact lip_int_harm_of_l2_lin2 (t₁ := 0) (t₂ := 2) (by norm_num) (hn 0 m0) (hn 2 n2)
    · exact lip_int_harm_of_l2_lin2 (t₁ := 0) (t₂ := 1) (by norm_num) (hn 0 m0) (hn 1 m1)


/-- **The interior harmonic approximation from the `L²` block on a domain between `□_{k-2}`
and `□_{k-1}` and the interior Caccioppoli block** (with the comparison of the
Poisson problem with the Laplace problem). -/
theorem lip_int_harm_of_l2 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cin : ℝ) (hCin : 1 ≤ Cin) (A : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (a : CoeffField d) (nu s δ lam Lam : ℝ) (k : ℕ) (V : Set (Vec d)),
        0 < nu → 0 < s → 0 ≤ δ → 3 ≤ k →
        ((k : ℝ) ^ A)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu → ((k : ℝ) ^ A)⁻¹ * s ≤ 1 →
        IsOpen V → Section6.engCube d (k - 2) ⊆ V → V ⊆ Section6.engCube d (k - 1) →
        IsEllipticFieldOn lam Lam (Section6.engCube d k) a → 0 < lam →
        LipL2Block a nu s δ Cin A (k - 1) V → LipCaccInt a nu s Cin 1 k →
        LipHarmInt a s δ C k := by
  have _hd2 : 2 ≤ d := hd
  obtain ⟨C, hC1, hmain⟩ := lip_int_harm_of_l2_core d Cin hCin A
  refine ⟨C, hC1, ?_⟩
  intro a nu s δ lam Lam k V hnu hs hδ hk H1 H2 hVo hV2 hV1 hell _ hblk hcacc f F u hu hF hfb
  by_cases hfm : AEStronglyMeasurable f (volume.restrict (Section6.engCube d k))
  · exact hmain a nu s δ k V hnu hs hδ hk H1 H2 hVo hV2 hV1 hblk hcacc f F u hu hF hfb hfm
  · have hu0 := lip_int_harm_of_l2_weak_zero_of_not_meas (Section6.eh_isOpen_engCube k) hell hu hfm
    exact hmain a nu s δ k V hnu hs hδ hk H1 H2 hVo hV2 hV1 hblk hcacc (fun _ => 0) F u hu0 hF
      (Filter.Eventually.of_forall fun x => by simpa using hF) aestronglyMeasurable_const

/-- Witness: the numerical hypotheses of `lip_int_harm_of_l2` hold together, for the identity field
on `□_3` and `V = □_2`. -/
example (d : ℕ) [NeZero d] : ∃ (a : CoeffField d) (nu s δ lam Lam : ℝ) (k : ℕ) (V : Set (Vec d)),
    0 < nu ∧ 0 < s ∧ 0 ≤ δ ∧ 3 ≤ k ∧
      ((k : ℝ) ^ 1)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu ∧ ((k : ℝ) ^ 1)⁻¹ * s ≤ 1 ∧
      IsOpen V ∧ Section6.engCube d (k - 2) ⊆ V ∧ V ⊆ Section6.engCube d (k - 1) ∧
      IsEllipticFieldOn lam Lam (Section6.engCube d k) a ∧ 0 < lam := by
  refine ⟨fun _ => (1 : Mat d), 1, 1, 1, 1, 1, 3, Section6.engCube d 2, one_pos, one_pos,
    zero_le_one, le_rfl, ?_, ?_, Section6.eh_isOpen_engCube 2, ?_, Set.Subset.rfl,
    lip_int_harm_of_l2_ell_one (Section6.eh_measurableSet_engCube 3), one_pos⟩
  · simp
    norm_num
  · norm_num
  · exact Section6.eh_engCube_mono (by norm_num)

end SuperdiffusionCLT.Section7
