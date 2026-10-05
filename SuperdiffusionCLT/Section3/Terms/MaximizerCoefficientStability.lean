/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.GluedFieldL2Class
public import SuperdiffusionCLT.Section2.Localization.CutoffComparison

/-!
# Stability of the Chapter 2 response maximizer under perturbation of the coefficient

`GluedFieldL2Class.lean` needs the sample measurability
of the `L²` class of the Chapter 2 cube maximizer gradient.  The sample enters
that maximizer only through the coefficient field, so what is needed is a
modulus of continuity of the maximizer gradient in the coefficient.  This
module proves that the modulus is **Lipschitz in the `L∞(U)` operator norm of
the coefficient difference**, at the exact carriers of the paper, whenever
both coefficients have symmetric part `ν Id`:

`ν² ‖∇v(a₁) − ∇v(a₂)‖_{L²(U)} ≤ 3 ‖a₁ − a₂‖_{L∞(U)} ‖F‖_{L²(U)}`.

## Why an energy argument applies

`Book.Ch02.IsResponseMaximizer U a p q v` says that `v` maximizes

`(-½ ∇v · a_s ∇v − p · a ∇v + q · ∇v)_U`

over the admissible class `A(U; a)` of `a`-harmonic functions.  The quadratic
part is `−½ ⟨∇v, a_s ∇v⟩` with `a_s ≥ λ`, so the problem is a genuine concave
maximization, not a saddle, and the first-variation theorem
`Book.Ch02.firstVariationValue_eq_zero` is an honest Euler-Lagrange identity.
At the loading `(p, q) = (0, F)` of the cube problem of `e.u.k.y.def`, and for
a coefficient with `a_s = ν Id`, it reads

`ν ⟨∇v, ∇w⟩_{L²(U)} = ⟨F, ∇w⟩_{L²(U)}` for every `w ∈ A(U; a)`,

that is, `ν ∇v` is the `L²(U)` projection of the constant field `F` on the
closed subspace of `a`-harmonic gradients.

## Why the two admissible classes can be compared

Two coefficients give two different admissible classes, so neither maximizer
can be tested against the other's equation directly.  The bridge is the
`b`-Dirichlet problem with boundary data `u`, treated in
`Section2/Localization/CutoffComparison.lean`:
`exists_isAHarmonicGradient_add_zeroTraceGrad` transfers any `u ∈ H¹(U)` into
`A(U; b)` by a zero-trace correction, and
`dirichlet_comparison_of_skew_perturbation` bounds the correction,
`ν ‖∇u − ∇u_b‖_{L²(U)} ≤ M ‖∇u‖_{L²(U)}` with `M` an `L∞(U)` bound for the
operator norm of `a − b`.  So each admissible class lies within relative
distance `M/ν` of the other, and the two projections of `F` are close.

The naive estimate — expand `‖∇v₁ − ∇v₂‖²` and test each equation against the
transfer of the other maximizer — only gives the square root of `M`.  The sharp
step, carried out in `norm_sub_le_of_variational_transfer`, is to bound instead
the `A(U; a₂)` element `z − ∇v₂`, where `z` is the transfer of `∇v₁`: testing
the `a₂`-equation against *that difference*, and the `a₁`-equation against its
transfer back, is what turns the estimate linear in `M`.

## Main results

* `norm_sub_le_of_variational_transfer`: the abstract Hilbert-space estimate.
* `inner_gradToHilbertVectorL2_eq_of_isResponseMaximizer`: the Euler-Lagrange
  identity of the cube problem in `L²(U)` class form.
* `subSolution`, `exists_solution_mul_norm_gradToHilbertVectorL2_sub_le`: the
  admissible class is closed under differences, and the transfer estimate.
* `norm_gradToHilbertVectorL2_sub_le_of_isResponseMaximizer`: the coefficient
  stability estimate itself.

## References

* The paper: the comparison of two coefficients on a bounded domain, and
  `e.u.k.y.def` (the cube maximizer).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The abstract variational estimate

Two elements of a Hilbert space, each the `ν`-scaled projection of the same
datum `f` on its own subspace, are close when the two subspaces approximate
each other.  Only the four variational identities and the two transfer bounds
below are used; no closedness, no projection operator, and no subspace appears
in the statement. -/

section Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Comparison of nonnegative reals through their squares. -/
private theorem le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have hroot := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at hroot

/-- **The energy bound.**  A solution of the variational identity at its own
value has `ν`-scaled norm bounded by the norm of the datum. -/
theorem mul_norm_le_of_inner_self_eq {nu : ℝ} {f u : H}
    (hu : nu * inner ℝ u u = inner ℝ f u) : nu * ‖u‖ ≤ ‖f‖ := by
  rcases (norm_nonneg u).lt_or_eq with hpos | hzero
  · have h1 : nu * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ := by
      rw [← real_inner_self_eq_norm_sq, hu]
      exact real_inner_le_norm f u
    have h2 : nu * ‖u‖ * ‖u‖ ≤ ‖f‖ * ‖u‖ := by
      have hrw : nu * ‖u‖ * ‖u‖ = nu * ‖u‖ ^ 2 := by ring
      rw [hrw]
      exact h1
    exact le_of_mul_le_mul_right h2 hpos
  · rw [← hzero, mul_zero]
    exact norm_nonneg f

/-- **The residual bound.**  The residual `ν u − f` of a solution of the
variational identity is no larger than the datum itself: the Pythagoras
identity of the projection. -/
theorem norm_smul_sub_le_of_inner_self_eq {nu : ℝ} {f u : H}
    (hu : nu * inner ℝ u u = inner ℝ f u) : ‖nu • u - f‖ ≤ ‖f‖ := by
  rw [norm_sub_rev]
  refine le_of_sq_le_sq (norm_nonneg _) (norm_nonneg _) ?_
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul]
  have hu' : inner ℝ f u = nu * ‖u‖ ^ 2 := by
    rw [← hu, real_inner_self_eq_norm_sq]
  have habs : (‖(nu : ℝ)‖ * ‖u‖) ^ 2 = nu ^ 2 * ‖u‖ ^ 2 := by
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hu', habs]
  have hnn : 0 ≤ nu ^ 2 * ‖u‖ ^ 2 := by positivity
  linarith only [hnn]

/-- The energy of the difference `z − w` inside the second subspace, split into
the transfer error of `u` and the residual of `u` tested against the transfer
error of `z − w`.  This identity is the whole point: the second subspace is
tested against `z − w`, not against `z` and `w` separately. -/
theorem inner_sub_self_eq_of_inner_eq {nu : ℝ} {f u w z g : H}
    (hug : nu * inner ℝ u g = inner ℝ f g)
    (hw : nu * inner ℝ w w = inner ℝ f w)
    (hwz : nu * inner ℝ w z = inner ℝ f z) :
    nu * inner ℝ (z - w) (z - w)
      = nu * inner ℝ (z - u) (z - w) + inner ℝ (nu • u - f) (z - w - g) := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left]
  linarith only [hw, hwz, hug]

/-- **The abstract coefficient-stability estimate.**  Let `u` and `w` each
solve the variational identity `ν ⟨·, ξ⟩ = ⟨f, ξ⟩` on its own subspace, let `z`
be a transfer of `u` into the subspace of `w` with error `M/ν` relative, and
let `g` be a transfer of `z − w` back into the subspace of `u` with the same
relative error.  Then

`ν² ‖u − w‖ ≤ 3 M ‖f‖`,

linear in `M`. -/
theorem norm_sub_le_of_variational_transfer {nu M : ℝ} (hnu : 0 < nu) (hM : 0 ≤ M)
    {f u w z g : H}
    (hu : nu * inner ℝ u u = inner ℝ f u)
    (hug : nu * inner ℝ u g = inner ℝ f g)
    (hw : nu * inner ℝ w w = inner ℝ f w)
    (hwz : nu * inner ℝ w z = inner ℝ f z)
    (huz : nu * ‖u - z‖ ≤ M * ‖u‖)
    (hzwg : nu * ‖z - w - g‖ ≤ M * ‖z - w‖) :
    nu ^ 2 * ‖u - w‖ ≤ 3 * M * ‖f‖ := by
  have hfu : nu * ‖u‖ ≤ ‖f‖ := mul_norm_le_of_inner_self_eq hu
  have hres : ‖nu • u - f‖ ≤ ‖f‖ := norm_smul_sub_le_of_inner_self_eq hu
  have hzu : nu * ‖z - u‖ ≤ M * ‖u‖ := by rwa [norm_sub_rev]
  have hb1 : nu * (nu * inner ℝ (z - u) (z - w)) ≤ M * ‖f‖ * ‖z - w‖ :=
    calc nu * (nu * inner ℝ (z - u) (z - w))
        ≤ nu * (nu * (‖z - u‖ * ‖z - w‖)) := by
          gcongr
          exact real_inner_le_norm _ _
      _ = nu * ((nu * ‖z - u‖) * ‖z - w‖) := by ring
      _ ≤ nu * ((M * ‖u‖) * ‖z - w‖) := by gcongr
      _ = M * ((nu * ‖u‖) * ‖z - w‖) := by ring
      _ ≤ M * (‖f‖ * ‖z - w‖) := by gcongr
      _ = M * ‖f‖ * ‖z - w‖ := by ring
  have hb2 : nu * inner ℝ (nu • u - f) (z - w - g) ≤ M * ‖f‖ * ‖z - w‖ :=
    calc nu * inner ℝ (nu • u - f) (z - w - g)
        ≤ nu * (‖nu • u - f‖ * ‖z - w - g‖) := by
          gcongr
          exact real_inner_le_norm _ _
      _ ≤ nu * (‖f‖ * ‖z - w - g‖) := by gcongr
      _ = ‖f‖ * (nu * ‖z - w - g‖) := by ring
      _ ≤ ‖f‖ * (M * ‖z - w‖) := by gcongr
      _ = M * ‖f‖ * ‖z - w‖ := by ring
  have hsq : nu ^ 2 * ‖z - w‖ ^ 2 ≤ 2 * (M * ‖f‖) * ‖z - w‖ := by
    have hid := inner_sub_self_eq_of_inner_eq (nu := nu) (f := f) (u := u) hug hw hwz
    have hnorm : inner ℝ (z - w) (z - w) = ‖z - w‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hmul : nu * (nu * inner ℝ (z - w) (z - w))
        = nu * (nu * inner ℝ (z - u) (z - w))
          + nu * inner ℝ (nu • u - f) (z - w - g) := by
      rw [hid]; ring
    rw [hnorm] at hmul
    have hgoal : nu ^ 2 * ‖z - w‖ ^ 2 = nu * (nu * ‖z - w‖ ^ 2) := by ring
    rw [hgoal, hmul]
    linarith only [hb1, hb2]
  have hzwbound : nu ^ 2 * ‖z - w‖ ≤ 2 * (M * ‖f‖) := by
    rcases (norm_nonneg (z - w)).lt_or_eq with hpos | hzero
    · refine le_of_mul_le_mul_right ?_ hpos
      have hrw : nu ^ 2 * ‖z - w‖ * ‖z - w‖ = nu ^ 2 * ‖z - w‖ ^ 2 := by ring
      rw [hrw]
      exact hsq
    · rw [← hzero, mul_zero]
      positivity
  calc nu ^ 2 * ‖u - w‖
      ≤ nu ^ 2 * (‖u - z‖ + ‖z - w‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub u z w
    _ = nu * (nu * ‖u - z‖) + nu ^ 2 * ‖z - w‖ := by ring
    _ ≤ nu * (M * ‖u‖) + 2 * (M * ‖f‖) := by gcongr
    _ = M * (nu * ‖u‖) + 2 * (M * ‖f‖) := by ring
    _ ≤ M * ‖f‖ + 2 * (M * ‖f‖) := by gcongr
    _ = 3 * M * ‖f‖ := by ring

end Variational

/-! ## Gradient classes -/

section GradientClasses

variable {U : Set (Vec d)}

/-- The `L²(U)` norm of a gradient class is the square root of the Dirichlet
energy. -/
theorem norm_gradToHilbertVectorL2_eq_sqrt (u : H1Function U) :
    ‖u.gradToHilbertVectorL2‖ =
      Real.sqrt (∫ x in U, vecNormSq (u.grad x) ∂MeasureTheory.volume) := by
  have h : u.gradToHilbertVectorL2 = toHilbertVectorL2OfVecField u.grad_memVectorL2 := rfl
  rw [h, norm_toHilbertVectorL2OfVecField_eq_sqrt]
  rfl

/-- The `L²(U)` distance of two gradient classes is the square root of the
Dirichlet energy of the difference. -/
theorem norm_gradToHilbertVectorL2_sub_eq_sqrt (u v : H1Function U) :
    ‖u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2‖ =
      Real.sqrt (∫ x in U, vecNormSq (u.grad x - v.grad x) ∂MeasureTheory.volume) := by
  have h : u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField (u.grad_memVectorL2.sub v.grad_memVectorL2) :=
    (toHilbertVectorL2OfVecField_sub u.grad_memVectorL2 v.grad_memVectorL2).symm
  rw [h, norm_toHilbertVectorL2OfVecField_eq_sqrt]
  rfl

/-- The gradient class of a difference of `H¹(U)` functions is the difference of
the gradient classes. -/
theorem gradToHilbertVectorL2_sub (u v : H1Function U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  have h : (u - v).gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField (u.grad_memVectorL2.sub v.grad_memVectorL2) := by
    refine toHilbertVectorL2OfVecField_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    simp [sub_eq_add_neg]
  rw [h, toHilbertVectorL2OfVecField_sub u.grad_memVectorL2 v.grad_memVectorL2]
  rfl

end GradientClasses

/-! ## The Euler-Lagrange identity of the pure-flux problem -/

section EulerLagrange

/-- Multiplication by a scalar multiple of the identity matrix. -/
private theorem matVecMul_smul_one (nu : ℝ) (y : Vec d) :
    matVecMul (nu • (1 : Mat d)) y = nu • y := by
  ext i
  simp [matVecMul, Matrix.one_apply]

/-- The pairing is homogeneous in its second argument. -/
private theorem vecDot_smul_right (nu : ℝ) (x y : Vec d) :
    vecDot x (nu • y) = nu * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A Chapter 2 domain has finite nonzero volume, so a vanishing normalized
average is a vanishing integral. -/
theorem setIntegral_eq_zero_of_average_eq_zero {U : Book.Ch02.Domain d}
    {f : Vec d → ℝ} (h : Book.Ch02.average U f = 0) :
    ∫ x in (U : Set (Vec d)), f x ∂MeasureTheory.volume = 0 := by
  have hpos : MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
    (IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty).ne'
  have hfin : MeasureTheory.volume (U : Set (Vec d)) ≠ ⊤ := by
    have h2 := MeasureTheory.measure_lt_top (volumeMeasureOn (U : Set (Vec d))) Set.univ
    rw [volumeMeasureOn, MeasureTheory.Measure.restrict_apply_univ] at h2
    exact h2.ne
  have hne : (MeasureTheory.volume (U : Set (Vec d))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩
  unfold Book.Ch02.average at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd (inv_eq_zero.1 h1) hne
  · exact h1

/-- **The Euler-Lagrange identity of the cube problem, in `L²(U)` class form.**
For a coefficient with symmetric part `ν Id` and the loading `(0, F)` of
`e.u.k.y.def`, a response maximizer `v` satisfies
`ν ⟨∇v, ∇w⟩ = ⟨F, ∇w⟩` for every admissible `w`; that is, `ν ∇v` is the
`L²(U)` projection of the constant field `F` on the `a`-harmonic gradients. -/
theorem inner_gradToHilbertVectorL2_eq_of_isResponseMaximizer
    {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U} {nu : ℝ}
    (hsymm : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      symmPart (a.toCoeffField x) = nu • (1 : Mat d))
    {F : Vec d} {v : Book.Ch02.Solution U a}
    (hv : Book.Ch02.IsResponseMaximizer U a 0 F v) (w : Book.Ch02.Solution U a) :
    nu * inner ℝ v.toH1.gradToHilbertVectorL2 w.toH1.gradToHilbertVectorL2 =
      inner ℝ (toHilbertVectorL2OfVecField
          (memVectorL2_const (U := (U : Set (Vec d))) F))
        w.toH1.gradToHilbertVectorL2 := by
  have hzero := setIntegral_eq_zero_of_average_eq_zero
    (Book.Ch02.firstVariationValue_eq_zero hv w)
  have hae : (Book.Ch02.firstVariationIntegrand U a 0 F v w)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => vecDot F (w.toH1.grad x) - nu * vecDot (w.toH1.grad x) (v.toH1.grad x) := by
    filter_upwards [hsymm] with x hx
    simp only [Book.Ch02.firstVariationIntegrand, hx, matVecMul_smul_one,
      vecDot_smul_right]
    have h0 : vecDot (0 : Vec d) (matVecMul (a.toCoeffField x) (w.toH1.grad x)) = 0 := by
      simp [vecDot]
    rw [h0]
    ring
  rw [MeasureTheory.integral_congr_ae hae] at hzero
  have hF : MemVectorL2 (U : Set (Vec d)) (fun _ : Vec d => F) :=
    memVectorL2_const (U := (U : Set (Vec d))) F
  have hI1 : MeasureTheory.IntegrableOn
      (fun x => vecDot F (w.toH1.grad x)) (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 hF w.toH1.grad_memVectorL2
  have hI2 : MeasureTheory.IntegrableOn
      (fun x => nu * vecDot (w.toH1.grad x) (v.toH1.grad x)) (U : Set (Vec d)) :=
    (integrableOn_vecDot_of_memVectorL2 w.toH1.grad_memVectorL2
      v.toH1.grad_memVectorL2).const_mul nu
  rw [MeasureTheory.integral_sub hI1 hI2, MeasureTheory.integral_const_mul,
    sub_eq_zero] at hzero
  have hinnerF : inner ℝ (toHilbertVectorL2OfVecField hF) w.toH1.gradToHilbertVectorL2 =
      ∫ x in (U : Set (Vec d)), vecDot F (w.toH1.grad x) ∂MeasureTheory.volume :=
    inner_toHilbertVectorL2OfVecField_eq_integral hF w.toH1.grad_memVectorL2
  have hinnerv : inner ℝ v.toH1.gradToHilbertVectorL2 w.toH1.gradToHilbertVectorL2 =
      ∫ x in (U : Set (Vec d)), vecDot (v.toH1.grad x) (w.toH1.grad x)
        ∂MeasureTheory.volume :=
    inner_toHilbertVectorL2OfVecField_eq_integral v.toH1.grad_memVectorL2
      w.toH1.grad_memVectorL2
  have hcomm : (∫ x in (U : Set (Vec d)), vecDot (w.toH1.grad x) (v.toH1.grad x)
        ∂MeasureTheory.volume) =
      ∫ x in (U : Set (Vec d)), vecDot (v.toH1.grad x) (w.toH1.grad x)
        ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact vecDot_comm _ _
  rw [hinnerF, hinnerv, ← hcomm]
  exact hzero.symm

end EulerLagrange

/-! ## Transfer between the two admissible classes -/

section Transfer

/-- The admissible class `A(U; a)` is closed under differences: the difference
of two `a`-harmonic functions is `a`-harmonic. -/
def subSolution {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U}
    (v w : Book.Ch02.Solution U a) : Book.Ch02.Solution U a where
  toH1 := v.toH1 - w.toH1
  isHarmonic := by
    have hflux : ∀ {f : Vec d → Vec d}, MemVectorL2 (U : Set (Vec d)) f →
        h10FluxIntegrable (U : Set (Vec d))
          (fun x => matVecMul (a.toCoeffField x) (f x)) := by
      intro f hf φ
      exact integrableOn_vecDot_of_memVectorL2
        (memVectorL2_matVecMul_coeffOn a hf) φ.toH1Function.grad_memVectorL2
    have hneg : IsAHarmonicGradient a.toCoeffField (U : Set (Vec d))
        ((-1 : ℝ) • w.toH1.grad) := isAHarmonicGradient_smul w.isHarmonic (-1)
    have hnegmem : MemVectorL2 (U : Set (Vec d)) ((-1 : ℝ) • w.toH1.grad) :=
      w.toH1.grad_memVectorL2.const_smul (-1 : ℝ)
    have hsum := isAHarmonicGradient_add_of_integrable v.isHarmonic hneg
      (hflux v.toH1.grad_memVectorL2) (hflux hnegmem)
    have hrw : (v.toH1 - w.toH1).grad = v.toH1.grad + (-1 : ℝ) • w.toH1.grad := by
      funext x
      simp [sub_eq_add_neg]
    rw [hrw]
    exact hsum

@[simp] theorem subSolution_toH1 {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U}
    (v w : Book.Ch02.Solution U a) :
    (subSolution v w).toH1 = v.toH1 - w.toH1 :=
  rfl

/-- **The transfer estimate.**  Every admissible function of the coefficient `a`
is, up to a zero-trace correction of relative size `M/ν`, an admissible function
of the coefficient `b`, whenever `b` has symmetric part `ν Id` and `M` bounds
the operator norm of `a − b` on `U`.  This is the cutoff comparison of
`Section2/Localization/CutoffComparison.lean`, read on `L²(U)` classes. -/
theorem exists_solution_mul_norm_gradToHilbertVectorL2_sub_le [NeZero d]
    {U : Book.Ch02.Domain d} {a b : Book.Ch02.CoeffOn U} {nu M : ℝ} (hnu : 0 < nu)
    (hbsymm : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      symmPart (b.toCoeffField x) = nu • (1 : Mat d))
    (hM : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      Book.Ch02.matrixOperatorNorm (a.toCoeffField x - b.toCoeffField x) ≤ M)
    (v : Book.Ch02.Solution U a) :
    ∃ z : Book.Ch02.Solution U b,
      nu * ‖v.toH1.gradToHilbertVectorL2 - z.toH1.gradToHilbertVectorL2‖ ≤
        M * ‖v.toH1.gradToHilbertVectorL2‖ := by
  obtain ⟨w, hw⟩ := exists_isAHarmonicGradient_add_zeroTraceGrad U b v.toH1
  refine ⟨⟨v.toH1 + w.toH1Function, hw⟩, ?_⟩
  show nu * ‖v.toH1.gradToHilbertVectorL2 -
      (v.toH1 + w.toH1Function).gradToHilbertVectorL2‖ ≤
    M * ‖v.toH1.gradToHilbertVectorL2‖
  rw [norm_gradToHilbertVectorL2_sub_eq_sqrt, norm_gradToHilbertVectorL2_eq_sqrt]
  exact dirichlet_comparison_of_skew_perturbation hnu hbsymm hM
    (u := v.toH1) (ub := v.toH1 + w.toH1Function) (w := w) rfl v.isHarmonic hw

end Transfer

/-! ## The coefficient stability estimate -/

section Stability

/-- The operator norm of a matrix difference is symmetric in its arguments. -/
theorem matrixOperatorNorm_sub_comm (A B : Mat d) :
    Book.Ch02.matrixOperatorNorm (A - B) = Book.Ch02.matrixOperatorNorm (B - A) := by
  simp only [Book.Ch02.matrixOperatorNorm, map_sub]
  exact norm_sub_rev _ _

/-- An almost-everywhere bound for a nonnegative quantity on a Chapter 2 domain
forces the bound to be nonnegative. -/
theorem nonneg_of_ae_matrixOperatorNorm_le {U : Book.Ch02.Domain d} {M : ℝ}
    {K : Vec d → Mat d}
    (hM : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      Book.Ch02.matrixOperatorNorm (K x) ≤ M) : 0 ≤ M := by
  have hpos : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty
  have hne : volumeMeasureOn (U : Set (Vec d)) ≠ 0 := by
    intro hzero
    have hUzero : MeasureTheory.volume (U : Set (Vec d)) = 0 := by
      have := congrArg (fun mu : MeasureTheory.Measure (Vec d) =>
        mu (U : Set (Vec d))) hzero
      simpa [volumeMeasureOn, MeasureTheory.Measure.restrict_apply_self] using this
    exact absurd hUzero hpos.ne'
  have : (MeasureTheory.ae (volumeMeasureOn (U : Set (Vec d)))).NeBot :=
    MeasureTheory.ae_neBot.2 hne
  obtain ⟨x, hx⟩ := hM.exists
  exact le_trans (Book.Ch02.matrixOperatorNorm_nonneg (K x)) hx

/-- **The coefficient stability of the Chapter 2 response maximizer.**

For two coefficient fields on the same Chapter 2 domain, both with symmetric
part `ν Id`, and for the pure-flux loading `(0, F)` of `e.u.k.y.def`, the
gradients of any two response maximizers satisfy

`ν² ‖∇v(a₁) − ∇v(a₂)‖_{L²(U)} ≤ 3 M ‖F‖_{L²(U)}`,

where `M` is any almost-everywhere bound for the operator norm of `a₁ − a₂` on
`U`.  The dependence on the coefficient is Lipschitz in `L∞(U)`, with constant
`3 ν^{-2} ‖F‖_{L²(U)}`.  No selection appears: the estimate holds for every
realization of `IsResponseMaximizer` at either coefficient. -/
theorem norm_gradToHilbertVectorL2_sub_le_of_isResponseMaximizer [NeZero d]
    {U : Book.Ch02.Domain d} {a₁ a₂ : Book.Ch02.CoeffOn U} {nu M : ℝ} (hnu : 0 < nu)
    (h₁ : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      symmPart (a₁.toCoeffField x) = nu • (1 : Mat d))
    (h₂ : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      symmPart (a₂.toCoeffField x) = nu • (1 : Mat d))
    (hM : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      Book.Ch02.matrixOperatorNorm (a₁.toCoeffField x - a₂.toCoeffField x) ≤ M)
    {F : Vec d} {v₁ : Book.Ch02.Solution U a₁} {v₂ : Book.Ch02.Solution U a₂}
    (hv₁ : Book.Ch02.IsResponseMaximizer U a₁ 0 F v₁)
    (hv₂ : Book.Ch02.IsResponseMaximizer U a₂ 0 F v₂) :
    nu ^ 2 * ‖v₁.toH1.gradToHilbertVectorL2 - v₂.toH1.gradToHilbertVectorL2‖ ≤
      3 * M * ‖toHilbertVectorL2OfVecField
        (memVectorL2_const (U := (U : Set (Vec d))) F)‖ := by
  have hM0 : 0 ≤ M := nonneg_of_ae_matrixOperatorNorm_le hM
  have hMswap : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      Book.Ch02.matrixOperatorNorm (a₂.toCoeffField x - a₁.toCoeffField x) ≤ M := by
    filter_upwards [hM] with x hx
    rwa [matrixOperatorNorm_sub_comm]
  obtain ⟨z, hz⟩ :=
    exists_solution_mul_norm_gradToHilbertVectorL2_sub_le hnu h₂ hM v₁
  obtain ⟨g, hg⟩ :=
    exists_solution_mul_norm_gradToHilbertVectorL2_sub_le hnu h₁ hMswap
      (subSolution z v₂)
  rw [subSolution_toH1, gradToHilbertVectorL2_sub] at hg
  exact norm_sub_le_of_variational_transfer hnu hM0
    (inner_gradToHilbertVectorL2_eq_of_isResponseMaximizer h₁ hv₁ v₁)
    (inner_gradToHilbertVectorL2_eq_of_isResponseMaximizer h₁ hv₁ g)
    (inner_gradToHilbertVectorL2_eq_of_isResponseMaximizer h₂ hv₂ v₂)
    (inner_gradToHilbertVectorL2_eq_of_isResponseMaximizer h₂ hv₂ z)
    hz hg

end Stability

end

end SuperdiffusionCLT.Section3.Terms
