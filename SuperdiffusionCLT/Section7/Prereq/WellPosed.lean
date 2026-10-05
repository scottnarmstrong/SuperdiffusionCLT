/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Prereq.DirichletExistence
public import Homogenization.Sobolev.Foundations.CoerciveH1

/-!
# The Dirichlet problem with `H¹` boundary data

For a bounded open set `U`, a field `a` elliptic on `U`, `f ∈ L²(U)` and `g ∈ H¹(U)`, there is
`u ∈ H¹(U)` with `-∇·(a∇u) = f` weakly in `U` and `u - g ∈ H¹₀(U)`; it is unique up to almost
everywhere equality of values and gradients, and `∇(u - g)` obeys the energy bound.
The solution is `u = g + w` where `w ∈ H¹₀(U)` solves the zero-trace problem with flux datum
`-a∇g`.

## Main results

* `Section7.w0_dirichlet_exists`, `Section7.w0_dirichlet_unique`, `Section7.w0_dirichlet_energy`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- Gradients of `H¹` functions with equal values agree almost everywhere on an open set. -/
theorem w0_grad_ae_of_toFun_eq (hU : IsOpen U) (v z : H1Function U) (h : v.toFun = z.toFun) :
    v.grad =ᵐ[volumeMeasureOn U] z.grad := by
  have hloc : ∀ (y : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => y.grad x i) U volume := fun y i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((y.gradMemL2 i).locallyIntegrable (by norm_num))
  have hcoord : ∀ i : Fin d, (fun x => v.grad x i) =ᵐ[volumeMeasureOn U] (fun x => z.grad x i) := by
    intro i
    have hw := v.hasWeakGradient i
    rw [h] at hw
    exact HasWeakPartialDerivOn.ae_eq hU (hloc _ i) (hloc _ i) hw (z.hasWeakGradient i)
  have hall := ae_all_iff.2 hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

/-- The Hilbert gradient class depends on the gradient only up to almost everywhere equality. -/
theorem w0_gradToHilbert_congr {z z' : H1Function U}
    (h : z.grad =ᵐ[volumeMeasureOn U] z'.grad) :
    z.gradToHilbertVectorL2 = z'.gradToHilbertVectorL2 := by
  unfold H1Function.gradToHilbertVectorL2 toHilbertVectorL2OfVecField toHilbertVectorL2
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [h] with x hx
  simp only [hilbertifyVecField, hx]

/-- Equal Hilbert gradient classes give almost everywhere equal gradients. -/
theorem w0_grad_ae_of_gradToHilbert_eq {z z' : H1Function U}
    (h : z.gradToHilbertVectorL2 = z'.gradToHilbertVectorL2) :
    z.grad =ᵐ[volumeMeasureOn U] z'.grad := by
  have h1 := H1Function.coeFn_gradToHilbertVectorL2 z
  have h2 := H1Function.coeFn_gradToHilbertVectorL2 z'
  have h3 : (⇑z.gradToHilbertVectorL2 : Vec d → HilbertVec d) =ᵐ[volumeMeasureOn U]
      ⇑z'.gradToHilbertVectorL2 := by rw [h]
  have h4 := (h1.symm.trans h3).trans h2
  filter_upwards [h4] with x hx
  have := congrArg HilbertVec.toVec hx
  simpa only [hilbertifyVecField, HilbertVec.toVec_ofVec] using this

/-- The flux datum `-a∇g` is square integrable. -/
theorem w0_memVectorL2_flux {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (g : H1Function U) :
    MemVectorL2 U (fun x => -(matVecMul (a x) (g.grad x))) :=
  (memVectorL2_matVecMul_of_isEllipticFieldOn hEll g.grad_memVectorL2).neg

theorem w0_integrableOn_flux {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (z : H1Function U) (φ : H10Function U) :
    IntegrableOn (fun x => vecDot (matVecMul (a x) (z.grad x)) (φ.toH1Function.grad x)) U :=
  integrableOn_vecDot_of_memVectorL2
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll z.grad_memVectorL2)
    φ.toH1Function.grad_memVectorL2

/-- An `H¹₀` function with the values of `u - g` has gradient `∇u - ∇g` almost everywhere. -/
theorem w0_h10_grad_ae (hU : IsOpen U) (g u : H1Function U) (v : H10Function U)
    (hv : v.toH1Function.toFun = fun x => u.toFun x - g.toFun x) :
    v.toH1Function.grad =ᵐ[volumeMeasureOn U] fun x => u.grad x - g.grad x := by
  have := w0_grad_ae_of_toFun_eq hU v.toH1Function (u - g) (by rw [hv, H1Function.sub_toFun])
  simpa only [H1Function.sub_grad] using this

/-- **Reduction to the zero-trace problem.** If `v ∈ H¹₀(U)` has the values of `u - g`, then `u`
solves the problem with datum `f` exactly when `v` solves the `H¹₀` problem with flux datum
`-a∇g`. -/
theorem w0_isWeakSolutionOn_iff_h10 (hU : IsOpen U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ} (g u : H1Function U)
    (v : H10Function U) (hv : v.toH1Function.toFun = fun x => u.toFun x - g.toFun x) :
    IsWeakSolutionOn a U u f (fun _ => 0) ↔
      IsH10WeakSolution a U f (fun x => -(matVecMul (a x) (g.grad x))) v := by
  have hgrad := w0_h10_grad_ae hU g u v hv
  have key : ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x) =
        (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)) -
          ∫ x in U, vecDot (matVecMul (a x) (g.grad x)) (φ.toH1Function.grad x) := by
    intro φ
    rw [← integral_sub (w0_integrableOn_flux hEll u φ) (w0_integrableOn_flux hEll g φ)]
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx, sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left, vecDot_neg_left,
      ← sub_eq_add_neg]
  have hneg : ∀ φ : H10Function U,
      ∫ x in U, vecDot (-(matVecMul (a x) (g.grad x))) (φ.toH1Function.grad x) =
        -∫ x in U, vecDot (matVecMul (a x) (g.grad x)) (φ.toH1Function.grad x) := by
    intro φ
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot_neg_left]
  have hzero : ∀ φ : H10Function U,
      ∫ x in U, vecDot ((fun _ : Vec d => (0 : Vec d)) x) (φ.toH1Function.grad x) = 0 := by
    intro φ
    simp only [vecDot_zero_left, integral_zero]
  constructor
  · intro h φ
    have h1 := h φ
    rw [hzero φ, add_zero] at h1
    rw [key φ, hneg φ, h1]
    ring
  · intro h φ
    have h1 := h φ
    rw [key φ, hneg φ] at h1
    rw [hzero φ, add_zero]
    linarith only [h1]

/-- **Existence for the Dirichlet problem with `H¹` data.** -/
theorem w0_dirichlet_exists [NeZero d] (hUo : IsOpen U) (hUb : IsBoundedDomain U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ}
    (hf : MemScalarL2 U f) (g : H1Function U) :
    ∃ u : H1Function U, IsWeakSolutionOn a U u f (fun _ => 0) ∧
      MemH10 U (fun x => u.toFun x - g.toFun x) := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · refine ⟨g, fun φ => by simp, ?_⟩
    have h0 : (fun x => g.toFun x - g.toFun x) = (0 : Vec d → ℝ) := by
      funext x
      simp
    rw [h0]
    exact memH10_zero
  · obtain ⟨C, -, hC⟩ := h10_dirichlet_wellPosed hUo hUb hne
    obtain ⟨w, hw⟩ := (hC hEll hf (w0_memVectorL2_flux hEll g)).1
    have hwv : w.toH1Function.toFun = fun x => (w.toH1Function + g).toFun x - g.toFun x := by
      funext x
      simp
    refine ⟨w.toH1Function + g, ?_, ⟨w, hwv⟩⟩
    exact (w0_isWeakSolutionOn_iff_h10 hUo hEll g _ w hwv).2 hw

/-- **Uniqueness for the Dirichlet problem with `H¹` data**, as almost everywhere equality of
values and of gradients. -/
theorem w0_dirichlet_unique [NeZero d] (hUo : IsOpen U) (hUb : IsBoundedDomain U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ}
    (hf : MemScalarL2 U f) (g : H1Function U) {u₁ u₂ : H1Function U}
    (h₁ : IsWeakSolutionOn a U u₁ f (fun _ => 0))
    (m₁ : MemH10 U (fun x => u₁.toFun x - g.toFun x))
    (h₂ : IsWeakSolutionOn a U u₂ f (fun _ => 0))
    (m₂ : MemH10 U (fun x => u₂.toFun x - g.toFun x)) :
    u₁.toFun =ᵐ[volumeMeasureOn U] u₂.toFun ∧ u₁.grad =ᵐ[volumeMeasureOn U] u₂.grad := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · have h0 : volumeMeasureOn (∅ : Set (Vec d)) = 0 := Measure.restrict_empty
    rw [h0]
    exact ⟨by simp [Filter.EventuallyEq], by simp [Filter.EventuallyEq]⟩
  · obtain ⟨v₁, hv₁⟩ := m₁
    obtain ⟨v₂, hv₂⟩ := m₂
    obtain ⟨C, -, hC⟩ := h10_dirichlet_wellPosed hUo hUb hne
    obtain ⟨hs, hg⟩ := (hC hEll hf (w0_memVectorL2_flux hEll g)).2.1 v₁ v₂
      ((w0_isWeakSolutionOn_iff_h10 hUo hEll g u₁ v₁ hv₁).1 h₁)
      ((w0_isWeakSolutionOn_iff_h10 hUo hEll g u₂ v₂ hv₂).1 h₂)
    have hval : v₁.toH1Function.toFun =ᵐ[volumeMeasureOn U] v₂.toH1Function.toFun :=
      (toScalarL2_eq_toScalarL2_iff v₁.toH1Function.memL2 v₂.toH1Function.memL2).1 hs
    have hgr := w0_grad_ae_of_gradToHilbert_eq hg
    have hd₁ := w0_h10_grad_ae hUo g u₁ v₁ hv₁
    have hd₂ := w0_h10_grad_ae hUo g u₂ v₂ hv₂
    refine ⟨?_, ?_⟩
    · filter_upwards [hval] with x hx
      have e₁ := congrFun hv₁ x
      have e₂ := congrFun hv₂ x
      linarith only [hx, e₁, e₂]
    · filter_upwards [hgr, hd₁, hd₂] with x hx e₁ e₂
      have : u₁.grad x - g.grad x = u₂.grad x - g.grad x := by rw [← e₁, ← e₂, hx]
      exact sub_left_injective this

/-- **Energy bound for the Dirichlet problem with `H¹` data**, with a constant depending only on
`U`: `λ ‖∇(u - g)‖ ≤ ‖a∇g‖ + C ‖f‖` in `L²(U)`. -/
theorem w0_dirichlet_energy [NeZero d] (hUo : IsOpen U) (hUb : IsBoundedDomain U)
    (hne : U.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {lam Lam : ℝ} {a : CoeffField d}
      (hEll : IsEllipticFieldOn lam Lam U a) {f : Vec d → ℝ} (hf : MemScalarL2 U f)
      (g : H1Function U) {u : H1Function U},
      IsWeakSolutionOn a U u f (fun _ => 0) →
      MemH10 U (fun x => u.toFun x - g.toFun x) →
        lam * ‖(u - g).gradToHilbertVectorL2‖ ≤
          ‖toHilbertVectorL2OfVecField (w0_memVectorL2_flux hEll g)‖ +
            C * ‖toScalarL2 hf‖ := by
  obtain ⟨C, hC0, hC⟩ := h10_dirichlet_wellPosed hUo hUb hne
  refine ⟨C, hC0, fun {lam Lam a} hEll {f} hf g {u} hu hm => ?_⟩
  obtain ⟨v, hv⟩ := hm
  have hbound := (hC hEll hf (w0_memVectorL2_flux hEll g)).2.2 v
    ((w0_isWeakSolutionOn_iff_h10 hUo hEll g u v hv).1 hu)
  have hgr : v.toH1Function.grad =ᵐ[volumeMeasureOn U] (u - g).grad := by
    simpa only [H1Function.sub_grad] using w0_h10_grad_ae hUo g u v hv
  rw [← w0_gradToHilbert_congr hgr]
  exact hbound

/-! ### Witness: the unit Euclidean ball, `a = Id`, `f = 1`, `g = 0` -/

example [NeZero d] : ∃ u : H1Function (Section6.euclidBall (d := d) 1),
    IsWeakSolutionOn (fun _ => (1 : Mat d)) (Section6.euclidBall 1) u (fun _ => 1) (fun _ => 0) ∧
      MemH10 (Section6.euclidBall (d := d) 1)
        (fun x => u.toFun x - (0 : H1Function (Section6.euclidBall (d := d) 1)).toFun x) := by
  have : IsFiniteMeasure (volumeMeasureOn (Section6.euclidBall (d := d) 1)) :=
    ⟨by simpa [volumeMeasureOn, Measure.restrict_apply_univ] using
      Section6.volume_euclidBall_lt_top (d := d) one_pos⟩
  exact w0_dirichlet_exists (Section6.isOpen_euclidBall (d := d) 1)
    (isBoundedDomain_euclidBall one_pos) isEllipticFieldOn_one_euclidBall
    (f := fun _ => (1 : ℝ)) (memLp_const 1) 0

/-- Witness for uniqueness and the energy bound on the same data. -/
example [NeZero d] : True := by
  have : IsFiniteMeasure (volumeMeasureOn (Section6.euclidBall (d := d) 1)) :=
    ⟨by simpa [volumeMeasureOn, Measure.restrict_apply_univ] using
      Section6.volume_euclidBall_lt_top (d := d) one_pos⟩
  obtain ⟨u, hu, hm⟩ := w0_dirichlet_exists (Section6.isOpen_euclidBall (d := d) 1)
    (isBoundedDomain_euclidBall one_pos) isEllipticFieldOn_one_euclidBall
    (f := fun _ => (1 : ℝ)) (memLp_const 1) 0
  have hU := w0_dirichlet_unique (Section6.isOpen_euclidBall (d := d) 1)
    (isBoundedDomain_euclidBall one_pos) isEllipticFieldOn_one_euclidBall
    (f := fun _ => (1 : ℝ)) (memLp_const 1) 0 hu hm hu hm
  have hE := w0_dirichlet_energy (Section6.isOpen_euclidBall (d := d) 1)
    (isBoundedDomain_euclidBall one_pos) (Section6.euclidBall_nonempty one_pos)
  trivial

end SuperdiffusionCLT.Section7
