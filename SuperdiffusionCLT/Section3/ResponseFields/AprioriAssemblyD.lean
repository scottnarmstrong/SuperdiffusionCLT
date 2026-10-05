/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.JunkBranchB

/-!
# Test functions, local integrability and the honest weak Jacobian

The estimate `e.abstract.response.W28` of the paper, read for the Dirichlet summand
universally over weak-Hessian witnesses, is the second conjunct of the statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero`.

`Section3/ResponseFields/AprioriAssembly.lean` produces that conjunct from a
single explicit hypothesis, whose case split is analysed in `JunkBranchB.lean`
and is not a junk branch: it demands the estimate *with constant one* on a
branch where the weak-Jacobian witness, and not the flux, is the non-measurable
datum. `AprioriAssemblyE.lean` repairs the case split; this module is the
toolkit it uses.

## The three tools

Write `U = cu_M` for the open cube.

* **Test functions.** `exists_h10Function_grad_eq_basisVec_ball` puts, on every
  ball whose closed double lies in `U`, an `H¹₀(U)` function whose gradient is
  the constant field `e_i` there. It is `χ(x)(x_i − z_i)` for a bump `χ`, the
  free-centre form of `JunkBranch.lean`'s
  `exists_h10Function_grad_eq_basisVec`.
* **Local integrability.** A flux whose pairing with every `H¹₀(U)` gradient is
  integrable is locally integrable on `U`
  (`locallyIntegrableOn_of_forall_integrableOn_vecDot_grad`), because those test
  functions read off one coordinate of the flux on a ball around any point. This
  is what makes `∫_U F_i ∂_jψ` an honest integral for every smooth compactly
  supported test function.
* **The honest weak Jacobian.** `HasWeakGradientOn` constrains its witness only
  through the by-parts identity, whose right-hand side is Bochner's `0` against
  a non-measurable witness coordinate, so a witness may carry arbitrary
  non-measurable coordinates. On such a coordinate the honest weak partial
  derivative is `0` (`hasWeakPartialDerivOn_zero_of_not_aestronglyMeasurable`:
  the test functions with an integrable pairing form a linear subspace, and one
  bad test function outside it makes both sides of the identity vanish for every
  test function), so zeroing those coordinates — `honestJacobian` — keeps a weak
  Jacobian of the same field, is measurable, and is dominated entry by entry.

## The junk branch, sharpened

`grad_ae_eq_zero_of_exists_bad_test` is `JunkBranch.lean`'s Dirichlet junk
branch with the non-measurability of the flux replaced by the weaker datum it
produces: one `H¹₀(U)` test function whose pairing with the flux is not
integrable. `cubeLpENorm_hess_eq_zero_of_grad_ae_eq_zero` is its Hessian form.

## Main results

* `exists_h10Function_grad_eq_basisVec_ball`;
* `locallyIntegrableOn_of_forall_integrableOn_vecDot_grad`,
  `integrableOn_mul_of_locallyIntegrableOn`;
* `aestronglyMeasurable_of_forall_integrableOn_mul_test`,
  `exists_test_not_integrableOn_mul`,
  `hasWeakPartialDerivOn_zero_of_not_aestronglyMeasurable`;
* `honestJacobian`, `hasWeakJacobianOn_honestJacobian`,
  `aestronglyMeasurable_honestJacobianHilbertMat`,
  `cubeLpENorm_honestJacobian_le`;
* `grad_ae_eq_zero_of_exists_bad_test`,
  `cubeLpENorm_hess_eq_zero_of_grad_ae_eq_zero`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-! ## `H¹₀` test functions with a prescribed constant gradient -/

/-- **Test functions with a prescribed constant gradient on an interior ball.**
On every ball whose closed double lies in the open cube there is an `H¹₀(Q)`
function whose gradient is the `i`-th coordinate direction throughout the ball.
It is `χ(x)(x_i − z_i)` for a bump `χ` equal to `1` on the ball and supported in
the closed ball of the larger radius.

This is `exists_h10Function_grad_eq_basisVec` with the centre and the two radii
free, the form the local integrability argument needs. -/
theorem exists_h10Function_grad_eq_basisVec_ball (Q : TriadicCube d) (z : Vec d)
    (r r' : ℝ) (hr : 0 < r) (hrr' : r < r')
    (hsub : Metric.closedBall z r' ⊆ openCubeSet Q) (i : Fin d) :
    ∃ φ : H10Function (openCubeSet Q),
      ∀ x ∈ Metric.ball z r, φ.toH1Function.grad x = basisVec i := by
  classical
  set f : ContDiffBump z := ⟨r, r', hr, hrr'⟩ with hf
  set g : Vec d → ℝ := fun x => (f : Vec d → ℝ) x * (x i - z i) with hg
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => x i - z i) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff).sub contDiff_const
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := f.contDiff.mul hproj
  have hsupp : HasCompactSupport g := f.hasCompactSupport.mul_right
  have hsubg : tsupport g ⊆ openCubeSet Q := by
    refine (closure_mono (Function.support_mul_subset_left _ _)).trans ?_
    rw [show closure (Function.support (f : Vec d → ℝ)) = tsupport (f : Vec d → ℝ) from rfl,
      f.tsupport_eq]
    exact hsub
  refine ⟨H10Function.ofContDiff (isOpen_openCubeSet Q) hsmooth hsupp hsubg, ?_⟩
  intro x hx
  have hx' : x ∈ Metric.ball z f.rIn := by simpa [hf] using hx
  have heq : g =ᶠ[nhds x] fun y : Vec d => y i - z i := by
    filter_upwards [f.eventuallyEq_one_of_mem_ball hx'] with y hy
    simp [hg, hy]
  have hfd : fderiv ℝ g x = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i := by
    rw [heq.fderiv_eq]
    exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt).sub_const
      (z i)).fderiv
  funext j
  show (fderiv ℝ g x) (basisVec j) = basisVec i j
  rw [hfd]
  simp [basisVec_apply, eq_comm]

/-! ## Local integrability of a flux with integrable test pairings -/

/-- **A flux whose pairing with every `H¹₀(Q)` gradient is integrable is locally
integrable on the cube.** Around a point of the cube the test function of
`exists_h10Function_grad_eq_basisVec_ball` reads off one coordinate of the flux
on a ball, and the pairing is integrable there. -/
theorem locallyIntegrableOn_of_forall_integrableOn_vecDot_grad {Q : TriadicCube d}
    {F : Vec d → Vec d}
    (h : ∀ φ : H10Function (openCubeSet Q),
      IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) (openCubeSet Q))
    (i : Fin d) :
    LocallyIntegrableOn (fun x => F x i) (openCubeSet Q) volume := by
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_openCubeSet Q) z hz
  have hr : 0 < ε / 3 := by linarith only [hε]
  have hrr' : ε / 3 < ε / 2 := by linarith only [hε]
  have hsub : Metric.closedBall z (ε / 2) ⊆ openCubeSet Q :=
    (Metric.closedBall_subset_ball (by linarith only [hε])).trans hball
  obtain ⟨φ, hφ⟩ := exists_h10Function_grad_eq_basisVec_ball Q z (ε / 3) (ε / 2) hr hrr' hsub i
  have hballsub : Metric.ball z (ε / 3) ⊆ openCubeSet Q :=
    (Metric.ball_subset_ball (by linarith only [hε])).trans hball
  have hpair : IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x))
      (Metric.ball z (ε / 3)) := (h φ).mono_set hballsub
  refine ⟨Metric.ball z (ε / 3),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr), hpair.congr ?_⟩
  refine Filter.Eventually.mono (ae_restrict_mem Metric.isOpen_ball.measurableSet) ?_
  intro x hx
  show vecDot (F x) (φ.toH1Function.grad x) = F x i
  rw [hφ x hx, vecDot_basisVec_right]

/-! ## Multiplying a locally integrable function by a test function -/

/-- **A locally integrable function times a continuous function of compact
support inside the set is integrable there.** The product is supported in the
compact support of the second factor, where the first is integrable and the
second is bounded. -/
theorem integrableOn_mul_of_locallyIntegrableOn {U : Set (Vec d)} (hU : MeasurableSet U)
    {f g : Vec d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ U) :
    IntegrableOn (fun x => f x * g x) U volume := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hfK : IntegrableOn f (tsupport g) volume :=
    hf.integrableOn_compact_subset hgs hgc
  have hmulK : IntegrableOn (fun x => f x * g x) (tsupport g) volume := by
    have := (hfK.bdd_mul hg.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hC))
    have h2 : IntegrableOn (fun x => g x * f x) (tsupport g) volume := this
    simpa only [mul_comm] using h2
  have hmulC : IntegrableOn (fun x => f x * g x) (U \ tsupport g) volume := by
    refine (integrable_zero (Vec d) ℝ _).congr ?_
    filter_upwards [ae_restrict_mem (hU.diff (isClosed_tsupport g).measurableSet)] with x hx
    exact (mul_eq_zero_of_right (f x) (image_eq_zero_of_notMem_tsupport hx.2)).symm
  refine (integrableOn_union.2 ⟨hmulK, hmulC⟩).mono_set ?_
  intro x hx
  by_cases hxs : x ∈ tsupport g
  · exact Or.inl hxs
  · exact Or.inr ⟨hx, hxs⟩

/-! ## The bad test function of a non-measurable weak derivative -/

/-- **A function whose product with every smooth compactly supported test
function is integrable is measurable.** A bump equal to `1` on a small ball
around a point of the open set reads off the function there, so it is locally
integrable, hence measurable. -/
theorem aestronglyMeasurable_of_forall_integrableOn_mul_test {U : Set (Vec d)}
    (hU : IsOpen U) {g : Vec d → ℝ}
    (h : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      IntegrableOn (fun x => g x * ψ x) U volume) :
    AEStronglyMeasurable g (volume.restrict U) := by
  refine LocallyIntegrableOn.aestronglyMeasurable ?_
  intro z hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
  have hr : 0 < ε / 3 := by linarith only [hε]
  have hrr' : ε / 3 < ε / 2 := by linarith only [hε]
  set f : ContDiffBump z := ⟨ε / 3, ε / 2, hr, hrr'⟩ with hf
  have hsupp : tsupport (f : Vec d → ℝ) ⊆ U := by
    rw [f.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by simpa [hf] using (by linarith only [hε] :
      ε / 2 < ε))).trans hball
  have hint := h (f : Vec d → ℝ) f.contDiff f.hasCompactSupport hsupp
  have hballsub : Metric.ball z (ε / 3) ⊆ U :=
    (Metric.ball_subset_ball (by linarith only [hε])).trans hball
  refine ⟨Metric.ball z (ε / 3),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr),
    (hint.mono_set hballsub).congr ?_⟩
  refine Filter.Eventually.mono (ae_restrict_mem Metric.isOpen_ball.measurableSet) ?_
  intro x hx
  have hx' : x ∈ Metric.closedBall z f.rIn :=
    Metric.ball_subset_closedBall (by simpa [hf] using hx)
  show g x * (f : Vec d → ℝ) x = g x
  rw [f.one_of_mem_closedBall hx', mul_one]

/-- The contrapositive: a function that is not measurable on an open set has a
smooth compactly supported test function whose product with it is not
integrable there. -/
theorem exists_test_not_integrableOn_mul {U : Set (Vec d)} (hU : IsOpen U)
    {g : Vec d → ℝ} (hg : ¬ AEStronglyMeasurable g (volume.restrict U)) :
    ∃ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      ¬ IntegrableOn (fun x => g x * ψ x) U volume := by
  by_contra hcon
  push Not at hcon
  exact hg (aestronglyMeasurable_of_forall_integrableOn_mul_test hU
    (fun ψ h1 h2 h3 => hcon ψ h1 h2 h3))

/-- **A non-measurable weak partial derivative of a locally integrable function
is the zero one.** The test functions whose product with the witness is
integrable form a linear subspace; adding to one of them a test function outside
it keeps the product non-integrable, so the right-hand side of the weak
derivative identity is Bochner's `0` there and at the bad test function itself,
and the left-hand side splits because the function is locally integrable. -/
theorem hasWeakPartialDerivOn_zero_of_not_aestronglyMeasurable {U : Set (Vec d)}
    (hU : IsOpen U) {j : Fin d} {u g : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hg : ¬ AEStronglyMeasurable g (volume.restrict U))
    (hw : HasWeakPartialDerivOn U j u g) :
    HasWeakPartialDerivOn U j u (fun _ => 0) := by
  obtain ⟨ψ₀, hψ₀s, hψ₀c, hψ₀u, hψ₀⟩ := exists_test_not_integrableOn_mul hU hg
  have hleftInt : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      IntegrableOn (fun x => u x * (fderiv ℝ ψ x) (basisVec j)) U volume := by
    intro ψ hψs hψc hψu
    refine integrableOn_mul_of_locallyIntegrableOn hU.measurableSet hu ?_ ?_ ?_
    · exact (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
    · exact (hψc.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec j)) (by simp)
    · refine (closure_mono ?_).trans ((closure_minimal (support_fderiv_subset ℝ)
        (isClosed_tsupport ψ)).trans hψu)
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro hzero
      exact hx (by rw [hzero]; simp)
  have hzero : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ¬ IntegrableOn (fun x => g x * ψ x) U volume →
      ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec j) = 0 := by
    intro ψ hψs hψc hψu hψ
    rw [hw ψ hψs hψc hψu, integral_undef hψ, neg_zero]
  intro ψ hψs hψc hψu
  have hmain : ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec j) = 0 := by
    by_cases hψ : IntegrableOn (fun x => g x * ψ x) U volume
    · have hsum : ¬ IntegrableOn (fun x => g x * (ψ + ψ₀) x) U volume := by
        intro hc
        refine hψ₀ ?_
        have hsplit : (fun x => g x * ψ₀ x)
            = fun x => g x * (ψ + ψ₀) x - g x * ψ x := by
          funext x
          simp only [Pi.add_apply]
          ring
        rw [hsplit]
        exact hc.sub hψ
      have h1 := hzero (ψ + ψ₀) (hψs.add hψ₀s) (hψc.add hψ₀c)
        ((closure_mono (Function.support_add ψ ψ₀)).trans
          (by rw [closure_union]; exact Set.union_subset hψu hψ₀u)) hsum
      have hfd : ∀ x : Vec d, (fderiv ℝ (ψ + ψ₀) x) (basisVec j)
          = (fderiv ℝ ψ x) (basisVec j) + (fderiv ℝ ψ₀ x) (basisVec j) := by
        intro x
        rw [fderiv_add ((hψs.differentiable (by simp)).differentiableAt)
          ((hψ₀s.differentiable (by simp)).differentiableAt)]
        rfl
      have hsplit2 : ∫ x in U, u x * (fderiv ℝ (ψ + ψ₀) x) (basisVec j)
          = (∫ x in U, u x * (fderiv ℝ ψ x) (basisVec j)) +
            ∫ x in U, u x * (fderiv ℝ ψ₀ x) (basisVec j) := by
        rw [← integral_add (hleftInt ψ hψs hψc hψu) (hleftInt ψ₀ hψ₀s hψ₀c hψ₀u)]
        refine setIntegral_congr_fun hU.measurableSet fun x _ => ?_
        rw [hfd x]
        ring
      rw [hsplit2, hzero ψ₀ hψ₀s hψ₀c hψ₀u hψ₀, add_zero] at h1
      exact h1
    · exact hzero ψ hψs hψc hψu hψ
  rw [hmain]
  simp

/-! ## The honest weak Jacobian -/

open Classical in
/-- **The honest weak Jacobian of a weak-Jacobian witness**: the coordinates
whose witness is not measurable on `U` are replaced by `0`.

`HasWeakGradientOn` constrains the witness only through the by-parts identity,
whose right-hand side is Bochner's `0` on a non-measurable coordinate, so a
witness may carry arbitrary non-measurable coordinates. Zeroing them keeps a
weak Jacobian of the same field, is measurable, and is dominated by the original
witness entry by entry. -/
def honestJacobian (U : Set (Vec d)) (DF : Fin d → Vec d → Vec d) :
    Fin d → Vec d → Vec d :=
  fun i x j =>
    if AEStronglyMeasurable (fun y => DF i y j) (volume.restrict U) then DF i x j else 0

theorem honestJacobian_apply_of_aestronglyMeasurable {U : Set (Vec d)}
    {DF : Fin d → Vec d → Vec d} {i j : Fin d}
    (hm : AEStronglyMeasurable (fun y => DF i y j) (volume.restrict U)) (x : Vec d) :
    honestJacobian U DF i x j = DF i x j := by
  simp only [honestJacobian, ite_eq_left hm]

theorem honestJacobian_apply_of_not_aestronglyMeasurable {U : Set (Vec d)}
    {DF : Fin d → Vec d → Vec d} {i j : Fin d}
    (hm : ¬ AEStronglyMeasurable (fun y => DF i y j) (volume.restrict U)) (x : Vec d) :
    honestJacobian U DF i x j = 0 := by
  simp only [honestJacobian, ite_eq_right hm]

theorem abs_honestJacobian_le (U : Set (Vec d)) (DF : Fin d → Vec d → Vec d)
    (i j : Fin d) (x : Vec d) : |honestJacobian U DF i x j| ≤ |DF i x j| := by
  by_cases hm : AEStronglyMeasurable (fun y => DF i y j) (volume.restrict U)
  · exact le_of_eq (congrArg _ (honestJacobian_apply_of_aestronglyMeasurable hm x))
  · rw [honestJacobian_apply_of_not_aestronglyMeasurable hm x, abs_zero]
    exact abs_nonneg _

/-- **The honest witness is again a weak Jacobian of the same field.** On a
coordinate whose witness is not measurable the honest weak partial derivative is
`0` by `hasWeakPartialDerivOn_zero_of_not_aestronglyMeasurable`. -/
theorem hasWeakJacobianOn_honestJacobian {U : Set (Vec d)} (hU : IsOpen U)
    {F : Vec d → Vec d} {DF : Fin d → Vec d → Vec d}
    (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) U volume)
    (hweak : ∀ i, HasWeakGradientOn U (fun x => F x i) (DF i)) :
    ∀ i, HasWeakGradientOn U (fun x => F x i) (honestJacobian U DF i) := by
  intro i j
  by_cases hm : AEStronglyMeasurable (fun y => DF i y j) (volume.restrict U)
  · have hfun : (fun x => honestJacobian U DF i x j) = fun x => DF i x j :=
      funext (honestJacobian_apply_of_aestronglyMeasurable hm)
    rw [hfun]
    exact hweak i j
  · have hfun : (fun x => honestJacobian U DF i x j) = fun _ => (0 : ℝ) :=
      funext (honestJacobian_apply_of_not_aestronglyMeasurable hm)
    rw [hfun]
    exact hasWeakPartialDerivOn_zero_of_not_aestronglyMeasurable hU (hF i) hm (hweak i j)

/-- **The honest witness is measurable**: every entry is either a measurable
entry of the original witness or the constant `0`. -/
theorem aestronglyMeasurable_honestJacobianHilbertMat (U : Set (Vec d))
    (DF : Fin d → Vec d → Vec d) :
    AEStronglyMeasurable
      (fun x => HilbertMat.ofMat (fun i j => honestJacobian U DF i x j))
      (volume.restrict U) := by
  have hentry : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x => honestJacobian U DF i x j) (volume.restrict U) := by
    intro i j
    by_cases hm : AEStronglyMeasurable (fun y => DF i y j) (volume.restrict U)
    · exact hm.congr (Filter.Eventually.of_forall
        fun x => (honestJacobian_apply_of_aestronglyMeasurable hm x).symm)
    · exact aestronglyMeasurable_const.congr (Filter.Eventually.of_forall
        fun x => (honestJacobian_apply_of_not_aestronglyMeasurable hm x).symm)
  have hmat : AEStronglyMeasurable
      (fun x => (fun i j => honestJacobian U DF i x j : Mat d)) (volume.restrict U) := by
    rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
    intro i
    rw [aemeasurable_pi_iff]
    intro j
    exact (hentry i j).aemeasurable
  exact (HilbertMat.continuousLinearEquivMat d).symm.continuous.comp_aestronglyMeasurable hmat

/-! ## Entrywise domination of the Hilbert matrix norm -/

private theorem hilbertMat_ofMat_apply (A : Mat d) (i j : Fin d) :
    (HilbertMat.ofMat A) i j = A i j :=
  (HilbertMat.entryL_apply i j (HilbertMat.ofMat A)).symm.trans (HilbertMat.entryL_ofMat i j A)

private theorem norm_sq_hilbertMat (A : HilbertMat d) :
    ‖A‖ ^ 2 = ∑ i : Fin d, ∑ j : Fin d, (A i j) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, HilbertMat.inner_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (sq (A i j)).symm

/-- **The Frobenius norm is monotone entry by entry.** -/
theorem norm_hilbertMat_ofMat_le_of_abs_le {A B : Mat d}
    (h : ∀ i j, |A i j| ≤ |B i j|) :
    ‖HilbertMat.ofMat A‖ ≤ ‖HilbertMat.ofMat B‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sq_hilbertMat, norm_sq_hilbertMat]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  rw [hilbertMat_ofMat_apply, hilbertMat_ofMat_apply, ← sq_abs (A i j), ← sq_abs (B i j)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2

/-- The `L̲^q(Q)` size of the honest witness is at most that of the original
witness: `eLpNorm` is monotone under a pointwise bound on the norms. -/
theorem cubeLpENorm_honestJacobian_le (Q : TriadicCube d) (q : ℝ≥0∞)
    (DF : Fin d → Vec d → Vec d) :
    Section2.Norms.cubeLpENorm Q q
        (fun x => HilbertMat.ofMat
          (fun i j => honestJacobian (openCubeSet Q) DF i x j)) ≤
      Section2.Norms.cubeLpENorm Q q (fun x => HilbertMat.ofMat (fun i j => DF i x j)) := by
  refine eLpNorm_mono_enorm ?_ fun x => enorm_le_iff_norm_le.2 ?_
  · rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (aestronglyMeasurable_honestJacobianHilbertMat (openCubeSet Q) DF).smul_measure _
  exact norm_hilbertMat_ofMat_le_of_abs_le
    (fun i j => abs_honestJacobian_le (openCubeSet Q) DF i j x)

/-! ## The junk branch carried by a bad test function -/

/-- **The junk branch of the Dirichlet equation, carried by a bad test
function.** This is `grad_ae_eq_zero_of_isCubeDirichletResponse` with the
non-measurability of the flux replaced by the weaker datum it produces: one
`H¹₀(Q)` test function whose pairing with the flux is not integrable. The
pairings that are integrable form a linear subspace, so adding the bad test
function to a good one keeps the pairing non-integrable, the equation forces
`∫_Q ∇w·∇ψ = 0` for every test function, and `ψ = w` gives a vanishing energy. -/
theorem grad_ae_eq_zero_of_exists_bad_test {Q : TriadicCube d} {F : Vec d → Vec d}
    {w : H10Function (openCubeSet Q)}
    (hbad : ∃ φ₀ : H10Function (openCubeSet Q),
      ¬ IntegrableOn (fun x => vecDot (F x) (φ₀.toH1Function.grad x)) (openCubeSet Q))
    (hw : IsCubeDirichletResponse Q F w) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), w.toH1Function.grad x = 0 := by
  obtain ⟨φ₀, hφ₀⟩ := hbad
  have hzero : ∀ ψ : H10Function (openCubeSet Q),
      ¬ IntegrableOn (fun x => vecDot (F x) (ψ.toH1Function.grad x)) (openCubeSet Q) →
      ∫ x in openCubeSet Q,
          vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) = 0 := by
    intro ψ hψ
    rw [hw ψ, integral_undef hψ, neg_zero]
  have key : ∀ ψ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) = 0 := by
    intro ψ
    by_cases hψ : IntegrableOn (fun x => vecDot (F x) (ψ.toH1Function.grad x)) (openCubeSet Q)
    · have hgradsum : (ψ + φ₀).toH1Function.grad
          = fun x => ψ.toH1Function.grad x + φ₀.toH1Function.grad x := rfl
      have hsum : ¬ IntegrableOn
          (fun x => vecDot (F x) ((ψ + φ₀).toH1Function.grad x)) (openCubeSet Q) := by
        intro hc
        refine hφ₀ ?_
        have hsplit : (fun x => vecDot (F x) (φ₀.toH1Function.grad x))
            = fun x => vecDot (F x) ((ψ + φ₀).toH1Function.grad x)
                - vecDot (F x) (ψ.toH1Function.grad x) := by
          funext x
          rw [hgradsum]
          simp only [vecDot, Pi.add_apply, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hsplit]
        exact hc.sub hψ
      have h1 := hzero _ hsum
      have hintψ : IntegrableOn
          (fun x => vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x)) (openCubeSet Q) :=
        integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2
          ψ.toH1Function.grad_memVectorL2
      have hintφ : IntegrableOn
          (fun x => vecDot (w.toH1Function.grad x) (φ₀.toH1Function.grad x)) (openCubeSet Q) :=
        integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2
          φ₀.toH1Function.grad_memVectorL2
      have hsplit2 : ∫ x in openCubeSet Q,
            vecDot (w.toH1Function.grad x) ((ψ + φ₀).toH1Function.grad x)
          = (∫ x in openCubeSet Q,
              vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x)) +
            ∫ x in openCubeSet Q,
              vecDot (w.toH1Function.grad x) (φ₀.toH1Function.grad x) := by
        rw [← integral_add hintψ hintφ]
        refine setIntegral_congr_fun (measurableSet_openCubeSet Q) fun x _ => ?_
        rw [hgradsum]
        simp only [vecDot, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit2, hzero φ₀ hφ₀, add_zero] at h1
      exact h1
    · exact hzero ψ hψ
  have hE := key w
  have hint : IntegrableOn
      (fun x => vecDot (w.toH1Function.grad x) (w.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2
      w.toH1Function.grad_memVectorL2
  have hnn : (0 : Vec d → ℝ) ≤ fun x => vecDot (w.toH1Function.grad x) (w.toH1Function.grad x) :=
    fun x => vecNormSq_nonneg (w.toH1Function.grad x)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 hE
  filter_upwards [hae] with x hx
  refine vecNormSq_eq_zero ?_
  simpa [vecNormSq] using hx

/-- **The `L̲^q(Q)` form of the vanishing weak Hessian**: if the gradient of an
`H¹` function vanishes almost everywhere on the open cube, so does every weak
Hessian witness of it. -/
theorem cubeLpENorm_hess_eq_zero_of_grad_ae_eq_zero {Q : TriadicCube d} {q : ℝ≥0∞}
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u)
    (hu : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), u.grad x = 0) :
    Section2.Norms.cubeLpENorm Q q
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) = 0 := by
  have hcoord : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      ∀ p : Fin d × Fin d, H.hess p.1 p.2 x = 0 :=
    ae_all_iff.2 fun p => hess_ae_eq_zero_of_grad_ae_eq_zero H hu p.1 p.2
  have hae : (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
      =ᵐ[normalizedCubeMeasure Q] 0 := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    refine Measure.ae_smul_measure ?_ _
    filter_upwards [hcoord] with x hx
    refine HilbertMat.ext fun i j => ?_
    show H.hess i j x = (0 : HilbertMat d) i j
    rw [hx (i, j)]
    rfl
  rw [Section2.Norms.cubeLpENorm, eLpNorm_congr_ae hae, eLpNorm_zero]

end

end ResponseFields
end Section3
end SuperdiffusionCLT
