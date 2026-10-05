/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.MaxPrincipleB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion

/-!
# The weak maximum principle for the shifted operator

For an elliptic field `a` on a bounded open set `U`, a shift `μ > 0` and a function `w ∈ H¹₀(U)`
solving `-∇·(a∇w) = h - μ w` weakly with `h ≤ μ M` almost everywhere, one has `w ≤ M` almost
everywhere.  The proof tests the equation with `(w - M)₊ ∈ H¹₀(U)`.

* `resEst_shift_max_upper`, `resEst_shift_max_lower`, `resEst_shift_max_abs`: the maximum
  principle for the shifted operator.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- The positive part `(w - M)₊` of a zero-trace function lies in `H¹₀`, for `M ≥ 0`. -/
theorem resEst_memH10_posPart {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (w : H1Function U) (hw : MemH10 U w.toFun) {M : ℝ} (hM : 0 ≤ M) :
    MemH10 U (fun x => max (w.toFun x - M) 0) := by
  have h0 : MemH10 U (fun x => w.toFun x - (0 : H1Function U).toFun x) := by
    simpa using hw
  have h := SuperdiffusionCLT.Section7.openH10Matched d hU hfin w 0 h0 M
  have hfun : (fun x => max (w.toFun x - M) 0 - max ((0 : H1Function U).toFun x - M) 0) =
      fun x => max (w.toFun x - M) 0 := by
    funext x
    have : max ((0 : H1Function U).toFun x - M) 0 = 0 := by
      simp only [H1Function.zero_toFun, Pi.zero_apply]
      exact max_eq_right (by linarith only [hM])
    rw [this, sub_zero]
  rwa [hfun] at h

/-- Negation of a weak solution with zero flux datum. -/
theorem resEst_weak_neg {U : Set (Vec d)} {a : CoeffField d} {w : H1Function U} {F : Vec d → ℝ}
    (h : SuperdiffusionCLT.Section7.IsWeakSolutionOn a U w F (fun _ => 0)) :
    SuperdiffusionCLT.Section7.IsWeakSolutionOn a U (-w) (fun x => -F x) (fun _ => 0) := by
  intro φ
  have h1 := h φ
  have e1 : (fun x => vecDot (matVecMul (a x) ((-w).grad x)) (φ.toH1Function.grad x)) =
      fun x => -vecDot (matVecMul (a x) (w.grad x)) (φ.toH1Function.grad x) := by
    funext x
    simp only [H1Function.neg_grad, matVecMul_neg, vecDot_neg_left]
  have e2 : (fun x => -F x * φ.toH1Function.toFun x) =
      fun x => -(F x * φ.toH1Function.toFun x) := by
    funext x
    ring
  rw [e1, e2, integral_neg, integral_neg]
  simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero] at h1 ⊢
  rw [h1]

/-- **Weak maximum principle for the shifted operator, upper bound.**  Let `w ∈ H¹₀(U)` solve
`-∇·(a∇w) = h - μ w` weakly in a bounded open set, for an elliptic field `a`, `μ > 0` and `h` in
`L²` with `h ≤ μ M` almost everywhere, `M ≥ 0`.  Then `w ≤ M` almost everywhere. -/
theorem resEst_shift_max_upper [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (w : H1Function U) (hw0 : MemH10 U w.toFun)
    {mu : ℝ} (hmu : 0 < mu) {h : Vec d → ℝ} (hh : MemLp h 2 (volume.restrict U))
    (hsol : SuperdiffusionCLT.Section7.IsWeakSolutionOn a U w
      (fun x => h x - mu * w.toFun x) (fun _ => 0))
    {M : ℝ} (hM : 0 ≤ M) (hhM : ∀ᵐ x ∂(volume.restrict U), h x ≤ mu * M) :
    ∀ᵐ x ∂(volume.restrict U), w.toFun x ≤ M := by
  have hbd := Homogenization.Bornology.IsBounded.isBoundedDomain hUb
  have hfin := SuperdiffusionCLT.Section7.volume_ne_top_of_isBoundedDomain hbd
  obtain ⟨v, hv⟩ := resEst_memH10_posPart hU hfin w hw0 hM
  have hgrad := SuperdiffusionCLT.Section7.grad_ae_eq_posPartGrad hU hfin w M v hv
  have hpair : ∀ᵐ x ∂(volumeMeasureOn U),
      vecDot (matVecMul (a x) (w.grad x)) (v.toH1Function.grad x) =
        vecDot (matVecMul (a x) (v.toH1Function.grad x)) (v.toH1Function.grad x) := by
    filter_upwards [hgrad] with x hx
    refine SuperdiffusionCLT.Section7.flux_pair_eq (a x) (w.grad x) _ M (w.toFun x) ?_
    rw [hx]
    rfl
  have hv2 : MemLp v.toH1Function.toFun 2 (volume.restrict U) := v.toH1Function.memL2
  have hint : Integrable (fun x => (h x - mu * w.toFun x) * v.toH1Function.toFun x)
      (volume.restrict U) :=
    (hh.sub (w.memL2.const_mul mu)).integrable_mul hv2
  have heq : (∫ x in U, vecDot (matVecMul (a x) (v.toH1Function.grad x))
      (v.toH1Function.grad x)) = ∫ x in U, (h x - mu * w.toFun x) * v.toH1Function.toFun x := by
    have := hsol v
    simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero,
      add_zero] at this
    rw [← this]
    exact (integral_congr_ae hpair).symm
  have hnn : 0 ≤ ∫ x in U, vecDot (matVecMul (a x) (v.toH1Function.grad x))
      (v.toH1Function.grad x) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have := (hEll.2 x hx).2.2.1 (v.toH1Function.grad x)
    rw [vecDot_comm] at this
    exact le_trans (mul_nonneg (hEll.2 x hx).1.le (vecNormSq_nonneg _)) this
  have hsq : Integrable (fun x => v.toH1Function.toFun x ^ 2) (volume.restrict U) :=
    hv2.integrable_sq
  have hle : (∫ x in U, (h x - mu * w.toFun x) * v.toH1Function.toFun x) ≤
      ∫ x in U, -(mu * v.toH1Function.toFun x ^ 2) := by
    refine integral_mono_ae hint (hsq.const_mul mu).neg ?_
    filter_upwards [hhM] with x hx
    have hvx : v.toH1Function.toFun x = max (w.toFun x - M) 0 := congrFun hv x
    by_cases hc : M < w.toFun x
    · rw [hvx, max_eq_left (by linarith only [hc])]
      have h1 : h x - mu * w.toFun x ≤ -(mu * (w.toFun x - M)) := by
        linarith only [hx]
      have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ w.toFun x - M by linarith only [hc])
      linarith only [h2]
    · rw [hvx, max_eq_right (by linarith only [hc])]
      simp
  rw [integral_neg, integral_const_mul] at hle
  have hz : ∫ x in U, v.toH1Function.toFun x ^ 2 ≤ 0 := by
    by_contra hc
    have := mul_pos hmu (not_le.mp hc)
    linarith only [this, hle, heq, hnn]
  have hz0 : ∫ x in U, v.toH1Function.toFun x ^ 2 = 0 :=
    le_antisymm hz (integral_nonneg fun x => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (v.toH1Function.toFun x)) hsq).1
    hz0
  filter_upwards [hae] with x hx
  have hx' : v.toH1Function.toFun x = 0 := by
    have : v.toH1Function.toFun x ^ 2 = 0 := hx
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have hvx : v.toH1Function.toFun x = max (w.toFun x - M) 0 := congrFun hv x
  have := le_max_left (w.toFun x - M) 0
  linarith only [this, hx', hvx]

/-- **Weak maximum principle for the shifted operator, lower bound.** -/
theorem resEst_shift_max_lower [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (w : H1Function U) (hw0 : MemH10 U w.toFun)
    {mu : ℝ} (hmu : 0 < mu) {h : Vec d → ℝ} (hh : MemLp h 2 (volume.restrict U))
    (hsol : SuperdiffusionCLT.Section7.IsWeakSolutionOn a U w
      (fun x => h x - mu * w.toFun x) (fun _ => 0))
    {M : ℝ} (hM : 0 ≤ M) (hhM : ∀ᵐ x ∂(volume.restrict U), -(mu * M) ≤ h x) :
    ∀ᵐ x ∂(volume.restrict U), -M ≤ w.toFun x := by
  have hneg := resEst_weak_neg hsol
  have hsol' : SuperdiffusionCLT.Section7.IsWeakSolutionOn a U (-w)
      (fun x => -h x - mu * (-w).toFun x) (fun _ => 0) := by
    refine SuperdiffusionCLT.Section7.rc_isWeakSolutionOn_congr (fun _ => rfl)
      (fun x => ?_) (fun _ => rfl) hneg
    simp only [H1Function.neg_toFun]
    ring
  have h0 : MemH10 U (-w).toFun := by
    have := memH10_neg hw0
    simpa using this
  have := resEst_shift_max_upper hU hUb hEll (-w) h0 hmu hh.neg hsol' hM
    (by filter_upwards [hhM] with x hx; show -h x ≤ mu * M; linarith only [hx])
  filter_upwards [this] with x hx
  simp only [H1Function.neg_toFun] at hx
  linarith only [hx]

/-- **Weak maximum principle for the shifted operator**: `|h| ≤ μ M` gives `|w| ≤ M`. -/
theorem resEst_shift_max_abs [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (w : H1Function U) (hw0 : MemH10 U w.toFun)
    {mu : ℝ} (hmu : 0 < mu) {h : Vec d → ℝ} (hh : MemLp h 2 (volume.restrict U))
    (hsol : SuperdiffusionCLT.Section7.IsWeakSolutionOn a U w
      (fun x => h x - mu * w.toFun x) (fun _ => 0))
    {M : ℝ} (hM : 0 ≤ M) (hhM : ∀ᵐ x ∂(volume.restrict U), |h x| ≤ mu * M) :
    ∀ᵐ x ∂(volume.restrict U), |w.toFun x| ≤ M := by
  have h1 := resEst_shift_max_upper hU hUb hEll w hw0 hmu hh hsol hM
    (by filter_upwards [hhM] with x hx; exact (le_abs_self _).trans hx)
  have h2 := resEst_shift_max_lower hU hUb hEll w hw0 hmu hh hsol hM
    (by filter_upwards [hhM] with x hx; linarith only [neg_abs_le (h x), hx])
  filter_upwards [h1, h2] with x hx1 hx2
  exact abs_le.2 ⟨hx2, hx1⟩

end SuperdiffusionCLT.Section8
