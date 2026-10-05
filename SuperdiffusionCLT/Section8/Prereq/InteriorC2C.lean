/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2B
public import Mathlib.Order.CompletePartialOrder

/-!
# The weak equation against smooth tests, and its restrictions

`intC2_Weak a μ g U u` is the weak form of `-∇·(a∇u) + μ u = g` in `U`, tested against smooth
compactly supported functions with support in `U`.  It restricts to open subsets and, for a
bounded set and a `C²` coefficient of the form `ν Id + skew`, upgrades to the `H¹₀`-tested forms
`IsScalarForcedWeakSolution` and `IsWeakSolutionOn` used by the Calderón-Zygmund estimates.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- `-∇·(a∇u) + μ u = g` weakly in `U`, tested against smooth compactly supported functions. -/
def intC2_Weak (a : CoeffField d) (mu : ℝ) (g : Vec d → ℝ) (U : Set (Vec d))
    (u : H1Function U) : Prop :=
  ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (fun i ↦ fderiv ℝ φ x (basisVec i))) +
      mu * ∫ x in U, u.toFun x * φ x = ∫ x in U, g x * φ x

theorem intC2_set_eq {U V : Set (Vec d)} (hVU : V ⊆ U) {F : Vec d → ℝ}
    (h0 : ∀ x, x ∉ V → F x = 0) : ∫ x in U, F x = ∫ x in V, F x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ h0 x fun h ↦ hx (hVU h)),
    setIntegral_eq_integral_of_forall_compl_eq_zero h0]

theorem intC2_Weak.restrict {a : CoeffField d} {mu : ℝ} {g : Vec d → ℝ} {U V : Set (Vec d)}
    {u : H1Function U} (h : intC2_Weak a mu g U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    intC2_Weak a mu g V (u.restrict hV hVU) := by
  intro φ hφ hc hs
  have h1 := h φ hφ hc (hs.trans hVU)
  have e1 := intC2_set_eq hVU (F := fun x ↦ vecDot (matVecMul (a x) (u.grad x))
    (fun i ↦ fderiv ℝ φ x (basisVec i))) (fun x hx ↦ by
      have : x ∉ tsupport φ := fun h' ↦ hx (hs h')
      simp [fderiv_of_notMem_tsupport ℝ this, vecDot])
  have e2 : ∀ F : Vec d → ℝ, ∫ x in U, F x * φ x = ∫ x in V, F x * φ x := fun F ↦
    intC2_set_eq hVU (F := fun x ↦ F x * φ x) (fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hx (hs h')), mul_zero])
  rw [e1, e2, e2] at h1
  exact h1

theorem intC2_memLp_bdd {U : Set (Vec d)} (hb : Bornology.IsBounded U) (hU : MeasurableSet U)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f (volume.restrict U)) {M : ℝ}
    (hM : ∀ x ∈ U, |f x| ≤ M) (p : ENNReal) : MemLp f p (volume.restrict U) := by
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hb.measure_lt_top⟩
  refine MemLp.of_bound hf M ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  simpa only [Real.norm_eq_abs] using hM x hx

theorem intC2_bound_on {U : Set (Vec d)} (hb : Bornology.IsBounded U) {f : Vec d → ℝ}
    (hf : Continuous f) : ∃ M, ∀ x ∈ U, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun x hx ↦ by simpa only [Real.norm_eq_abs] using hM x (subset_closure hx)⟩

theorem intC2_memLp_flux_coord {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) (z : H1Function U) (i : Fin d) :
    MemLp (fun x ↦ matVecMul (a x) (z.grad x) i) 2 (volume.restrict U) := by
  unfold matVecMul
  refine memLp_finsetSum _ fun j _ ↦ ?_
  obtain ⟨M, hM⟩ := intC2_bound_on hb (ha i j).continuous
  exact intW2p_memLp_mul_bdd (b := fun x ↦ a x i j) (ha i j).continuous.aestronglyMeasurable hM
    hU.measurableSet (z.grad_memL2 j)

/-- **Smooth tests give `H¹₀` tests.** -/
theorem intC2_scalarForced {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {mu : ℝ} {g : Vec d → ℝ}
    (hg : Continuous g) {u : H1Function U} (hu : intC2_Weak a mu g U u) :
    SuperdiffusionCLT.Section8.DivergenceForm.IsScalarForcedWeakSolution a U
      (fun x ↦ g x - mu * u.toFun x) u := by
  obtain ⟨M, hM⟩ := intC2_bound_on hb hg
  have hgL : MemLp g 2 (volume.restrict U) :=
    intC2_memLp_bdd hb hU.measurableSet hg.aestronglyMeasurable hM 2
  have hf : MemLp (fun x ↦ g x - mu * u.toFun x) 2 (volume.restrict U) :=
    hgL.sub (u.memL2.const_mul mu)
  refine ⟨hf, fun v ↦ ?_⟩
  have key := intW2p_h10_of_smooth (U := U) (W := fun x ↦ matVecMul (a x) (u.grad x))
    (s := fun x ↦ -(g x - mu * u.toFun x)) (intC2_memLp_flux_coord hU hb ha u) hf.neg
    (fun φ hφ hc hs ↦ by
      have h1 := hu φ hφ hc hs
      have i1 : Integrable (fun x ↦ g x * φ x) (volume.restrict U) :=
        ((hg.mul hφ.continuous).integrable_of_hasCompactSupport (μ := volume)
          hc.mul_left).restrict
      have i2 : Integrable (fun x ↦ u.toFun x * φ x) (volume.restrict U) :=
        intW2p_integrable_mul u.memL2 hφ.continuous hc
      have e : ∫ x in U, -(g x - mu * u.toFun x) * φ x =
          -(∫ x in U, g x * φ x) + mu * ∫ x in U, u.toFun x * φ x := by
        have i1' : Integrable (fun x ↦ -(g x * φ x)) (volume.restrict U) := i1.neg
        rw [← integral_neg, ← integral_const_mul, ← integral_add i1' (i2.const_mul mu)]
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only
        ring
      rw [e]
      linarith only [h1]) v
  have e : ∫ x in U, -(g x - mu * u.toFun x) * v.toH1Function.toFun x =
      -∫ x in U, (g x - mu * u.toFun x) * v.toH1Function.toFun x := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  rw [e] at key
  linarith only [key]

end SuperdiffusionCLT.Section8
