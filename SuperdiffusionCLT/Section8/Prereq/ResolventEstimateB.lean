/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimate

/-!
# The resolvent comparison on a bounded open set

Let `a'` be a field for which the homogenization estimate holds at fixed scale: every pair of
Dirichlet solutions of `-∇·(a'∇w) = F` and `-Δũ = F` with the same data satisfies
`‖w - ũ‖_∞ ≤ E (‖∇g‖_∞ + ‖F‖_∞)`.  Then the solutions of the resolvent problems
`λ u - ½ ∇·(a'∇u) = f` and `λ uhom - ½ Δuhom = f` (written weakly as the Dirichlet problems with
right-hand sides `2 (f - λ u)` and `2 (f - λ uhom)`) satisfy
`‖u - uhom‖_∞ ≤ 2 E (‖∇g‖_∞ + ‖2 (f - λ u)‖_∞)`.

* `resEst_weak_sub`: the difference of two weak solutions with `L²` right-hand sides;
* `resEst_compare`: the comparison, proved by the decomposition `uhom = ũ + u₂`, with `ũ` the
  solution of `-Δũ = 2 (f - λ u)` and `u₂` solving the shifted Laplace problem with zero data.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

open SuperdiffusionCLT.Section7 in
/-- The difference of two weak solutions with `L²` right-hand sides. -/
theorem resEst_weak_sub {U : Set (Vec d)} {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {w₁ w₂ : H1Function U} {f₁ f₂ : Vec d → ℝ}
    (hf₁ : MemLp f₁ 2 (volume.restrict U)) (hf₂ : MemLp f₂ 2 (volume.restrict U))
    (h1 : IsWeakSolutionOn a U w₁ f₁ (fun _ => 0))
    (h2 : IsWeakSolutionOn a U w₂ f₂ (fun _ => 0)) :
    IsWeakSolutionOn a U (w₁ - w₂) (fun x => f₁ x - f₂ x) (fun _ => 0) := by
  intro φ
  have hint : ∀ w : H1Function U, IntegrableOn
      (fun x => vecDot (matVecMul (a x) (w.grad x)) (φ.toH1Function.grad x)) U :=
    fun w => integrableOn_vecDot_of_memVectorL2
      (memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.grad_memVectorL2)
      φ.toH1Function.grad_memVectorL2
  have hsplit : (fun x => vecDot (matVecMul (a x) ((w₁ - w₂).grad x)) (φ.toH1Function.grad x)) =
      fun x => vecDot (matVecMul (a x) (w₁.grad x)) (φ.toH1Function.grad x) -
        vecDot (matVecMul (a x) (w₂.grad x)) (φ.toH1Function.grad x) := by
    funext x
    simp only [H1Function.sub_grad, Pi.sub_apply, vecDot, matVecMul, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  have i1 : Integrable (fun x => f₁ x * φ.toH1Function.toFun x) (volume.restrict U) :=
    hf₁.integrable_mul φ.toH1Function.memL2
  have i2 : Integrable (fun x => f₂ x * φ.toH1Function.toFun x) (volume.restrict U) :=
    hf₂.integrable_mul φ.toH1Function.memL2
  have e1 := h1 φ
  have e2 := h2 φ
  have z : (∫ x in U, vecDot ((fun _ => (0 : Vec d)) x) (φ.toH1Function.grad x)) = 0 := by
    simp [vecDot]
  rw [z, add_zero] at e1 e2 ⊢
  rw [hsplit, integral_sub (hint w₁) (hint w₂), e1, e2]
  simp only [sub_mul]
  rw [integral_sub i1 i2]

/-- Bound the real size of a function by its essential supremum. -/
theorem resEst_ae_abs_le {U : Set (Vec d)} {w : Vec d → ℝ}
    (hm : eLpNorm w ⊤ (volume.restrict U) ≠ ⊤) :
    ∀ᵐ x ∂(volume.restrict U), |w x| ≤ (eLpNorm w ⊤ (volume.restrict U)).toReal := by
  filter_upwards [enorm_ae_le_eLpNormEssSup w (volume.restrict U)] with x hx
  have h1 : ‖w x‖ₑ ≤ eLpNorm w ⊤ (volume.restrict U) := hx.trans eLpNormEssSup_le_eLpNorm_top
  rw [← ofReal_norm] at h1
  have := (ENNReal.ofReal_le_iff_le_toReal hm).1 h1
  simpa using this

open SuperdiffusionCLT.Section7 in
/-- **Comparison of resolvent solutions.**  `hErr` is the homogenization estimate for the field
`a'` at fixed scale (the root theorem with the sample and scale fixed).  A solution `u` of
`-∇·(a'∇u) = 2 (f - λ u)` and a solution `uhom` of `-Δ uhom = 2 (f - λ uhom)`, both with the datum
`g`, satisfy `‖u - uhom‖_∞ ≤ 2 E (‖∇g‖_∞ + ‖2 (f - λ u)‖_∞)`. -/
theorem resEst_compare [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {a' : CoeffField d} {E : ℝ} (hE : 0 < E)
    (hErr : ∀ (F : Vec d → ℝ) (g w wt : H1Function U),
      IsDirichletSolution a' U F g w → IsDirichletSolution (fun _ => (1 : Mat d)) U F g wt →
        eLpNorm (fun x => w.toFun x - wt.toFun x) ⊤ (volume.restrict U) ≤
          ENNReal.ofReal E * (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) +
            eLpNorm F ⊤ (volume.restrict U)))
    {lam : ℝ} (hlam : 0 ≤ lam) (f : Vec d → ℝ) (g u uhom : H1Function U)
    (hu : IsDirichletSolution a' U (fun x => 2 * (f x - lam * u.toFun x)) g u)
    (huh : IsDirichletSolution (fun _ => (1 : Mat d)) U
      (fun x => 2 * (f x - lam * uhom.toFun x)) g uhom) :
    eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict U) ≤
      ENNReal.ofReal (2 * E) *
        (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) +
          eLpNorm (fun x => 2 * (f x - lam * u.toFun x)) ⊤ (volume.restrict U)) := by
  set F : Vec d → ℝ := fun x => 2 * (f x - lam * u.toFun x) with hFdef
  set s := eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) + eLpNorm F ⊤
    (volume.restrict U) with hs
  have h2E : ENNReal.ofReal (2 * E) ≠ 0 := by
    simpa using (show (0 : ℝ) < 2 * E by linarith only [hE])
  by_cases hstop : s = ⊤
  · rw [hstop, ENNReal.mul_top h2E]
    exact le_top
  have hFfin : eLpNorm F ⊤ (volume.restrict U) ≠ ⊤ := fun h => hstop (by rw [hs, h, add_top])
  have hfinU : IsFiniteMeasure (volume.restrict U) := by
    have hbd := Homogenization.Bornology.IsBounded.isBoundedDomain hUb
    exact ⟨by
      simpa [Measure.restrict_apply_univ] using
        (lt_top_iff_ne_top.2 (volume_ne_top_of_isBoundedDomain hbd))⟩
  have hF2 : MemLp F 2 (volume.restrict U) :=
    MemLp.mono_exponent (show MemLp F ⊤ (volume.restrict U) from hFfin.lt_top)
      le_top
  have hEll1 : IsEllipticFieldOn 1 1 U (fun _ => (1 : Mat d)) := by
    simpa using rc_isEllipticFieldOn_smul_one (d := d) one_pos hU.measurableSet
  have hwp := rc_dirichlet_wellPosed_of_elliptic hU hUb hEll1 hF2 g
  obtain ⟨wt, hwt⟩ := hwp.1
  have hbound := hErr F g u wt hu hwt
  have hmfin : eLpNorm (fun x => u.toFun x - wt.toFun x) ⊤ (volume.restrict U) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hbound
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hstop
  set m := eLpNorm (fun x => u.toFun x - wt.toFun x) ⊤ (volume.restrict U) with hm
  have hmle : m ≤ ENNReal.ofReal (2 * E) * s := by
    refine hbound.trans (mul_le_mul_left ?_ _)
    exact ENNReal.ofReal_le_ofReal (by linarith only [hE])
  have hum : AEStronglyMeasurable (fun x => u.toFun x - uhom.toFun x) (volume.restrict U) :=
    (u.memL2.sub uhom.memL2).aestronglyMeasurable
  rcases hlam.eq_or_lt with h0 | hpos
  · -- λ = 0: both solve the same problem
    subst h0
    have huh' : IsDirichletSolution (fun _ => (1 : Mat d)) U F g uhom := by
      have : (fun x => 2 * (f x - 0 * uhom.toFun x)) = F := by
        funext x
        simp [hFdef]
      rwa [this] at huh
    have hae := (hwp.2 uhom wt huh' hwt).1
    have : eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict U) = m := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    rw [this]
    exact hmle
  · -- λ > 0
    set mu : ℝ := 2 * lam with hmu
    have hmupos : 0 < mu := by linarith only [hpos]
    have hFh2 : MemLp (fun x => 2 * (f x - lam * uhom.toFun x)) 2 (volume.restrict U) := by
      have : (fun x => 2 * (f x - lam * uhom.toFun x)) =
          fun x => F x + mu * (u.toFun x - uhom.toFun x) := by
        funext x
        simp only [hFdef, hmu]
        ring
      rw [this]
      exact hF2.add ((u.memL2.sub uhom.memL2).const_mul mu)
    have hsub := resEst_weak_sub hEll1 hFh2 hF2 huh.1 hwt.1
    set u₂ : H1Function U := uhom - wt with hu₂
    have hu₂fun : ∀ x, u₂.toFun x = uhom.toFun x - wt.toFun x := fun x => by
      simp [hu₂]
    have hsol : IsWeakSolutionOn (fun _ => (1 : Mat d)) U u₂
        (fun x => mu * (u.toFun x - wt.toFun x) - mu * u₂.toFun x) (fun _ => 0) := by
      refine rc_isWeakSolutionOn_congr (fun _ => rfl) (fun x => ?_) (fun _ => rfl) hsub
      rw [hu₂fun x]
      simp only [hFdef, hmu]
      ring
    have hw0 : MemH10 U u₂.toFun := by
      have := memH10_sub huh.2 hwt.2
      have e : (fun x => (uhom.toFun x - g.toFun x) - (wt.toFun x - g.toFun x)) = u₂.toFun := by
        funext x
        rw [hu₂fun x]
        ring
      rwa [e] at this
    have hhL2 : MemLp (fun x => mu * (u.toFun x - wt.toFun x)) 2 (volume.restrict U) :=
      (u.memL2.sub wt.memL2).const_mul mu
    have habs := resEst_ae_abs_le (U := U) hmfin
    have hmax := resEst_shift_max_abs hU hUb hEll1 u₂ hw0 hmupos hhL2 hsol
      (M := m.toReal) ENNReal.toReal_nonneg
      (by
        filter_upwards [habs] with x hx
        rw [abs_mul, abs_of_pos hmupos]
        exact mul_le_mul_of_nonneg_left hx hmupos.le)
    have hfin : eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict U) ≤
        ENNReal.ofReal (2 * m.toReal) := by
      have := eLpNorm_le_of_ae_bound (p := ⊤) hum (C := 2 * m.toReal) (by
        filter_upwards [habs, hmax] with x hx1 hx2
        rw [Real.norm_eq_abs]
        have : u.toFun x - uhom.toFun x =
            (u.toFun x - wt.toFun x) - u₂.toFun x := by
          rw [hu₂fun x]
          ring
        rw [this]
        refine (abs_sub _ _).trans ?_
        linarith only [hx1, hx2])
      simpa using this
    refine hfin.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hmfin]
    calc ENNReal.ofReal 2 * m ≤ ENNReal.ofReal 2 * (ENNReal.ofReal E * s) :=
          mul_le_mul_right hbound _
      _ = ENNReal.ofReal (2 * E) * s := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]

/-! ### Scaling lemmas -/

theorem resEst_isEllipticMatrix_smul {lam Lam c : ℝ} {A : Mat d} (hc : 0 < c)
    (hA : IsEllipticMatrix lam Lam A) : IsEllipticMatrix (c * lam) (c * Lam) (c • A) := by
  rcases hA with ⟨hlam, hlamLam, hlower, hupper⟩
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hdet : IsUnit A.det :=
    isUnit_det_of_isEllipticMatrix ⟨hlam, hlamLam, hlower, hupper⟩
  refine ⟨mul_pos hc hlam, mul_le_mul_of_nonneg_left hlamLam hc.le, ?_, ?_⟩
  · intro ξ
    rw [smul_matVecMul, vecDot_smul_right, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlower ξ) hc.le
  · intro ξ
    have hcne : c ≠ 0 := hc.ne'
    have hinv : ((c • A)⁻¹ : Mat d) = c⁻¹ • A⁻¹ := by
      rw [nonsing_inv_smul c hcne hdet]
    rw [hinv, smul_matVecMul, vecDot_smul_right]
    have hmul := mul_le_mul_of_nonneg_left (hupper ξ) (inv_nonneg.2 hc.le)
    have hleft : (c * Lam)⁻¹ * vecNormSq ξ = c⁻¹ * (Lam⁻¹ * vecNormSq ξ) := by
      field_simp [hcne, hLam.ne']
    rw [hleft]
    exact hmul

/-- A positive multiple of an elliptic field is elliptic. -/
theorem resEst_isEllipticFieldOn_smul {lam Lam c : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hc : 0 < c) (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn (c * lam) (c * Lam) U (fun x => c • a x) := by
  classical
  refine ⟨?_, fun x hx => resEst_isEllipticMatrix_smul hc (hEll.2 x hx)⟩
  have hmeas := hEll.1.const_smul c
  convert hmeas using 1
  funext x i j
  by_cases hx : x ∈ U <;> simp [hx]

open SuperdiffusionCLT.Section7 in
/-- The factor one half of the generator, for a general field. -/
theorem resEst_dirichlet_half {A : CoeffField d} (s : ℝ) {U : Set (Vec d)} {f : Vec d → ℝ}
    {g u : H1Function U} :
    IsDirichletSolution (fun x => ((1 / 2 : ℝ) * s) • A x) U f g u ↔
      IsDirichletSolution (fun x => s • A x) U (fun x => 2 * f x) g u := by
  have h := rc_isDirichletSolution_smul_iff (a := fun x => ((1 / 2 : ℝ) * s) • A x) (U := U)
    (u := u) (g := g) (f := f) (c := 2) two_ne_zero
  have e : (fun x => (2 : ℝ) • ((1 / 2 : ℝ) * s) • A x) = fun x => s • A x := by
    funext x
    rw [smul_smul]
    congr 1
    ring
  rw [e] at h
  exact h.symm

open SuperdiffusionCLT.Section7 in
/-- The factor one half for the Laplacian. -/
theorem resEst_dirichlet_half_laplace {U : Set (Vec d)} {f : Vec d → ℝ} {g u : H1Function U} :
    IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) U f g u ↔
      IsDirichletSolution (fun _ => (1 : Mat d)) U (fun x => 2 * f x) g u := by
  have h := resEst_dirichlet_half (A := fun _ => (1 : Mat d)) 1 (U := U) (f := f) (g := g)
    (u := u)
  simpa using h

theorem resEst_eLpNorm_two_mul (h : Vec d → ℝ) (μ : Measure (Vec d)) :
    eLpNorm (fun x => 2 * h x) ⊤ μ = 2 * eLpNorm h ⊤ μ := by
  have := eLpNorm_const_smul (p := (⊤ : ℝ≥0∞)) (μ := μ) (2 : ℝ) h
  have h2 : ‖(2 : ℝ)‖ₑ = 2 := by
    rw [Real.enorm_eq_ofReal (by norm_num)]
    simp
  rw [h2] at this
  simpa [Pi.smul_def, smul_eq_mul] using this

/-- A smooth bounded domain is open and bounded. -/
theorem resEst_open_bounded {U : Set (Vec d)}
    (hU : SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U) :
    IsOpen U ∧ Bornology.IsBounded U := by
  refine ⟨hU.1, ?_⟩
  obtain ⟨R, -, hUB⟩ := SuperdiffusionCLT.Section7.exists_ball_superset_of_isBoundedDomain
    hU.2.2.1
  exact Metric.isBounded_ball.subset hUB

open SuperdiffusionCLT.Section7 in
/-- **Exit-time comparison.**  For `λ > 0`, a solution `v` of `λ v - ½ ∇·(a∇v) = 1` and a
solution `vbar` of `λ vbar - ½Δ vbar = 1` with zero data (written as the Dirichlet problems with
right-hand sides `2 (1 - λ v)` and `2 (1 - λ vbar)`) satisfy `‖v - vbar‖_∞ ≤ 4 E`, when the field
`a'` is elliptic and `hErr` holds with constant `E`. -/
theorem resEst_exit_compare [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {lam' Lam' : ℝ} {a' : CoeffField d}
    (hEll : IsEllipticFieldOn lam' Lam' U a') {E : ℝ} (hE : 0 < E)
    (hErr : ∀ (F : Vec d → ℝ) (g w wt : H1Function U),
      IsDirichletSolution a' U F g w → IsDirichletSolution (fun _ => (1 : Mat d)) U F g wt →
        eLpNorm (fun x => w.toFun x - wt.toFun x) ⊤ (volume.restrict U) ≤
          ENNReal.ofReal E * (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) +
            eLpNorm F ⊤ (volume.restrict U)))
    {lam : ℝ} (hlam : 0 < lam) (v vb : H1Function U)
    (hv : IsDirichletSolution a' U (fun x => 2 * (1 - lam * v.toFun x)) 0 v)
    (hvb : IsDirichletSolution (fun _ => (1 : Mat d)) U
      (fun x => 2 * (1 - lam * vb.toFun x)) 0 vb) :
    eLpNorm (fun x => v.toFun x - vb.toFun x) ⊤ (volume.restrict U) ≤ ENNReal.ofReal (4 * E) := by
  have hbd := Homogenization.Bornology.IsBounded.isBoundedDomain hUb
  have hfinU : IsFiniteMeasure (volume.restrict U) :=
    ⟨by
      simpa [Measure.restrict_apply_univ] using
        (lt_top_iff_ne_top.2 (volume_ne_top_of_isBoundedDomain hbd))⟩
  have hmain := resEst_compare hU hUb hE hErr hlam.le (fun _ => (1 : ℝ)) 0 v vb
    (by simpa using hv) (by simpa using hvb)
  have hg0 : eLpNorm (fun x => eucNorm ((0 : H1Function U).grad x)) ⊤ (volume.restrict U) = 0 := by
    have : (fun x => eucNorm ((0 : H1Function U).grad x)) = fun _ => 0 := by
      funext x
      have h0 : (0 : H1Function U).grad x = 0 := rfl
      simp [eucNorm, h0, vecNormSq, vecDot]
    rw [this]
    exact eLpNorm_zero
  have hh2 : MemLp (fun _ : Vec d => (2 : ℝ)) 2 (volume.restrict U) := memLp_const 2
  have hw0 : MemH10 U v.toFun := by simpa using hv.2
  have hsol : IsWeakSolutionOn a' U v (fun x => (fun _ : Vec d => (2 : ℝ)) x - (2 * lam) *
      v.toFun x) (fun _ => 0) := by
    refine rc_isWeakSolutionOn_congr (fun _ => rfl) (fun x => ?_) (fun _ => rfl) hv.1
    ring
  have hmu : 0 < 2 * lam := by linarith only [hlam]
  have hup := resEst_shift_max_upper hU hUb hEll v hw0 hmu hh2 hsol (M := 1 / lam)
    (by positivity) (by
      refine Filter.Eventually.of_forall fun x => ?_
      have : 2 * lam * (1 / lam) = 2 := by field_simp
      exact le_of_eq this.symm)
  have hlo := resEst_shift_max_lower hU hUb hEll v hw0 hmu hh2 hsol (M := 0) le_rfl
    (Filter.Eventually.of_forall fun x => by simp)
  have hFm : AEStronglyMeasurable (fun x => 2 * (1 - lam * v.toFun x)) (volume.restrict U) :=
    (((memLp_const (1 : ℝ)).sub (v.memL2.const_mul lam)).const_mul 2).aestronglyMeasurable
  have hF : eLpNorm (fun x => 2 * (1 - lam * v.toFun x)) ⊤ (volume.restrict U) ≤
      ENNReal.ofReal 2 := by
    have := eLpNorm_le_of_ae_bound (p := ⊤) hFm (C := 2) (by
      filter_upwards [hup, hlo] with x h1 h2
      rw [Real.norm_eq_abs, abs_le]
      have h3 : lam * v.toFun x ≤ 1 := by
        have := mul_le_mul_of_nonneg_left h1 hlam.le
        rwa [mul_one_div_cancel hlam.ne'] at this
      have h4 : 0 ≤ lam * v.toFun x := mul_nonneg hlam.le (by simpa using h2)
      constructor <;> linarith only [h3, h4])
    simpa using this
  refine hmain.trans ?_
  rw [hg0, zero_add]
  calc ENNReal.ofReal (2 * E) * eLpNorm (fun x => 2 * (1 - lam * v.toFun x)) ⊤
        (volume.restrict U) ≤ ENNReal.ofReal (2 * E) * ENNReal.ofReal 2 :=
        mul_le_mul_right hF _
    _ = ENNReal.ofReal (4 * E) := by
        rw [← ENNReal.ofReal_mul (by linarith only [hE])]
        congr 1
        ring

open SuperdiffusionCLT.Section7 in
/-- **A change of the prefactor is a change of the shift.**  If `v` solves
`λ v - s₁ ∇·(A∇v) = 1` weakly with zero data, then `(s₁/s₂) v` solves
`(λ s₂/s₁) w - s₂ ∇·(A∇w) = 1` with zero data.  In the exit-time problem on a rescaled ball this
turns the prefactor `opScale c⋆ ε` into `opScale c⋆ (ε/ρ)` at the shift `λ s₂/s₁`, with no further
error. -/
theorem resEst_prefactor_shift {A : CoeffField d} {U : Set (Vec d)} {s₁ s₂ lam : ℝ}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) {v : H1Function U}
    (hv : IsDirichletSolution (fun x => s₁ • A x) U (fun x => 1 - lam * v.toFun x) 0 v) :
    IsDirichletSolution (fun x => s₂ • A x) U
      (fun x => 1 - (lam * (s₂ / s₁)) * ((s₁ / s₂) • v).toFun x) 0 ((s₁ / s₂) • v) := by
  refine ⟨fun φ => ?_, ?_⟩
  · have h := hv.1 φ
    have z : (∫ x in U, vecDot ((fun _ => (0 : Vec d)) x) (φ.toH1Function.grad x)) = 0 := by
      simp [vecDot]
    rw [z, add_zero] at h ⊢
    have hc : s₂ * (s₁ / s₂) = s₁ := by field_simp
    have e1 : (fun x => vecDot (matVecMul (s₂ • A x) (((s₁ / s₂) • v).grad x))
        (φ.toH1Function.grad x)) =
        fun x => vecDot (matVecMul (s₁ • A x) (v.grad x)) (φ.toH1Function.grad x) := by
      funext x
      have : matVecMul (s₂ • A x) (((s₁ / s₂) • v).grad x) =
          matVecMul (s₁ • A x) (v.grad x) := by
        simp only [H1Function.smul_grad, smul_matVecMul, matVecMul_smul, smul_smul]
        rw [mul_comm, hc]
      rw [this]
    have e2 : (fun x => (1 - lam * (s₂ / s₁) * ((s₁ / s₂) • v).toFun x) *
        φ.toH1Function.toFun x) =
        fun x => (1 - lam * v.toFun x) * φ.toH1Function.toFun x := by
      funext x
      have : lam * (s₂ / s₁) * ((s₁ / s₂) • v).toFun x = lam * v.toFun x := by
        simp only [H1Function.smul_toFun]
        field_simp
      rw [this]
    rw [e1, e2]
    exact h
  · have h := memH10_smul (s₁ / s₂) (by simpa using hv.2)
    convert h using 1
    funext x
    simp

end SuperdiffusionCLT.Section8
