/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates
public import SuperdiffusionCLT.Section3.ResponseFields.Norms

/-!
# The junk branch of `e.abstract.response.equations`

The paper states the two response problems (`e.abstract.response.equations`) with no
integrability hypothesis on the flux field `F`, so the two
weak formulations `IsCubeDirichletResponse` and `IsCubeNeumannResponse` are
meaningful for an arbitrary field `F : Vec d → Vec d`. On the branch where `F`
is not measurable on the cube, Bochner's convention makes every pairing
`∫_Q F·∇φ` of a non-integrable integrand equal to `0`, and the two equations
degenerate. This file proves that the degeneration is total: **a response of a
non-measurable flux has a vanishing gradient**.

## The mechanism

Testing the equation with the response itself gives `∫_Q |∇w|² = −∫_Q F·∇w`,
so it is enough to know that some pairing is a Bochner integral of a
non-integrable integrand. The set of test functions whose pairing with `F` is
integrable is a linear subspace: if it is not everything, then a translate
argument makes the left-hand side vanish for *every* test function, and the
energy `∫_Q |∇w|²` is one of those values; and if it is everything, then `F`
is measurable, because the cube carries enough `H¹₀` test functions with a
prescribed constant gradient.

## Main results

* `exists_h10Function_grad_eq_basisVec`: on every concentric ball compactly
  inside the cube there is an `H¹₀` function whose gradient is the constant
  field `e_i` there. The function is `χ(x)(x_i − c_i)` for a bump `χ` that is
  `1` on the ball.
* `aestronglyMeasurable_of_forall_integrableOn_vecDot_grad`: a field whose
  pairing with every `H¹₀` gradient is integrable is measurable on the cube.
* `grad_ae_eq_zero_of_isCubeDirichletResponse`,
  `grad_ae_eq_zero_of_isCubeNeumannResponse`: the junk-branch statements.
* `vecCubeLpENorm_grad_eq_zero_of_isCubeDirichletResponse`,
  `vecCubeLpENorm_grad_eq_zero_of_isCubeNeumannResponse`: their `L̲^q(Q)`
  form, the one the a priori clauses consume.
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

/-! ## An exhaustion of the open cube by concentric balls -/

/-- The radius of the `n`-th ball of the exhaustion of the open cube. -/
noncomputable def junkInnerRadius (Q : TriadicCube d) (n : ℕ) : ℝ :=
  cubeRadius Q * (1 - 1 / ((n : ℝ) + 2))

/-- The support radius of the `n`-th bump of the exhaustion. -/
private noncomputable def junkOuterRadius (Q : TriadicCube d) (n : ℕ) : ℝ :=
  cubeRadius Q * (1 - 1 / (2 * (n : ℝ) + 4))

private theorem junkInnerRadius_pos (Q : TriadicCube d) (n : ℕ) :
    0 < junkInnerRadius Q n := by
  have hR : 0 < cubeRadius Q := cubeRadius_pos Q
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h1 : 1 / ((n : ℝ) + 2) < 1 := by
    rw [div_lt_one hn]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [this]
  have : 0 < 1 - 1 / ((n : ℝ) + 2) := by linarith only [h1]
  exact mul_pos hR this

private theorem junkInnerRadius_lt_junkOuterRadius (Q : TriadicCube d) (n : ℕ) :
    junkInnerRadius Q n < junkOuterRadius Q n := by
  have hR : 0 < cubeRadius Q := cubeRadius_pos Q
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn' : (0 : ℝ) < 2 * (n : ℝ) + 4 := by positivity
  have hlt : 1 / (2 * (n : ℝ) + 4) < 1 / ((n : ℝ) + 2) := by
    rw [div_lt_div_iff₀ hn' hn]
    linarith only [hn]
  unfold junkInnerRadius junkOuterRadius
  have hlt' : 1 - 1 / ((n : ℝ) + 2) < 1 - 1 / (2 * (n : ℝ) + 4) := by linarith only [hlt]
  exact mul_lt_mul_of_pos_left hlt' hR

private theorem junkOuterRadius_lt_cubeRadius (Q : TriadicCube d) (n : ℕ) :
    junkOuterRadius Q n < cubeRadius Q := by
  have hR : 0 < cubeRadius Q := cubeRadius_pos Q
  have hn' : (0 : ℝ) < 2 * (n : ℝ) + 4 := by positivity
  have hpos : 0 < 1 / (2 * (n : ℝ) + 4) := by positivity
  unfold junkOuterRadius
  have h1 : 1 - 1 / (2 * (n : ℝ) + 4) < 1 := by linarith only [hpos]
  calc cubeRadius Q * (1 - 1 / (2 * (n : ℝ) + 4)) < cubeRadius Q * 1 :=
        mul_lt_mul_of_pos_left h1 hR
    _ = cubeRadius Q := mul_one _

private theorem openCubeSet_eq_iUnion_junkBall (Q : TriadicCube d) :
    openCubeSet Q = ⋃ n : ℕ, Metric.ball (cubeCenter Q) (junkInnerRadius Q n) := by
  rw [← ball_cubeCenter_eq_openCubeSet Q]
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun n => ?_)
  · rw [Metric.mem_ball] at hx
    obtain ⟨n, hn⟩ := exists_nat_gt (cubeRadius Q / (cubeRadius Q - dist x (cubeCenter Q)))
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [Metric.mem_ball]
    have hpos : 0 < cubeRadius Q - dist x (cubeCenter Q) := by linarith only [hx]
    have hnpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hkey : cubeRadius Q / ((n : ℝ) + 2) < cubeRadius Q - dist x (cubeCenter Q) := by
      rw [div_lt_iff₀ hnpos]
      have h1 : cubeRadius Q / (cubeRadius Q - dist x (cubeCenter Q)) < (n : ℝ) + 2 := by
        linarith only [hn]
      rw [div_lt_iff₀ hpos] at h1
      linarith only [h1]
    have hsplit : junkInnerRadius Q n = cubeRadius Q - cubeRadius Q / ((n : ℝ) + 2) := by
      unfold junkInnerRadius
      field_simp
    rw [hsplit]
    linarith only [hkey]
  · refine Metric.ball_subset_ball ?_
    have hnpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hR : 0 < cubeRadius Q := cubeRadius_pos Q
    have hpos : 0 < cubeRadius Q / ((n : ℝ) + 2) := by positivity
    have hsplit : junkInnerRadius Q n = cubeRadius Q - cubeRadius Q / ((n : ℝ) + 2) := by
      unfold junkInnerRadius
      field_simp
    rw [hsplit]
    linarith only [hpos]

/-! ## `H¹₀` test functions with a prescribed constant gradient -/

/-- **The cube carries enough test functions**: on the `n`-th ball of the
exhaustion there is an `H¹₀(Q)` function whose gradient is the `i`-th
coordinate direction. It is `χ(x)(x_i − c_i)` for a bump `χ` supported in the
cube and equal to `1` on the ball. -/
theorem exists_h10Function_grad_eq_basisVec (Q : TriadicCube d) (n : ℕ) (i : Fin d) :
    ∃ φ : H10Function (openCubeSet Q),
      ∀ x ∈ Metric.ball (cubeCenter Q) (junkInnerRadius Q n),
        φ.toH1Function.grad x = basisVec i := by
  classical
  set f : ContDiffBump (cubeCenter Q) :=
    ⟨junkInnerRadius Q n, junkOuterRadius Q n, junkInnerRadius_pos Q n,
      junkInnerRadius_lt_junkOuterRadius Q n⟩ with hf
  set g : Vec d → ℝ := fun x => (f : Vec d → ℝ) x * (x i - cubeCenter Q i) with hg
  have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => x i - cubeCenter Q i) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff).sub contDiff_const
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) g := f.contDiff.mul hproj
  have hsupp : HasCompactSupport g := f.hasCompactSupport.mul_right
  have hsub : tsupport g ⊆ openCubeSet Q := by
    refine (closure_mono (Function.support_mul_subset_left _ _)).trans ?_
    rw [show closure (Function.support (f : Vec d → ℝ)) = tsupport (f : Vec d → ℝ) from rfl,
      f.tsupport_eq, ← ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.closedBall_subset_ball (by simpa [hf] using junkOuterRadius_lt_cubeRadius Q n)
  refine ⟨H10Function.ofContDiff (isOpen_openCubeSet Q) hsmooth hsupp hsub, ?_⟩
  intro x hx
  have hx' : x ∈ Metric.ball (cubeCenter Q) f.rIn := by simpa [hf] using hx
  have heq : g =ᶠ[nhds x] fun y : Vec d => y i - cubeCenter Q i := by
    filter_upwards [f.eventuallyEq_one_of_mem_ball hx'] with y hy
    simp [hg, hy]
  have hfd : fderiv ℝ g x = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i := by
    rw [heq.fderiv_eq]
    exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).hasFDerivAt).sub_const
      (cubeCenter Q i)).fderiv
  funext j
  show (fderiv ℝ g x) (basisVec j) = basisVec i j
  rw [hfd]
  simp [basisVec_apply, eq_comm]

/-! ## Measurability from integrable pairings -/

/-- **A field whose pairing with every `H¹₀(Q)` gradient is integrable is
measurable on the cube.** Testing against `exists_h10Function_grad_eq_basisVec`
reads off one coordinate of the field on one ball of the exhaustion, and the
balls exhaust the cube. -/
theorem aestronglyMeasurable_of_forall_integrableOn_vecDot_grad {Q : TriadicCube d}
    {F : Vec d → Vec d}
    (h : ∀ φ : H10Function (openCubeSet Q),
      IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) (openCubeSet Q)) :
    AEStronglyMeasurable F (volume.restrict (openCubeSet Q)) := by
  rw [openCubeSet_eq_iUnion_junkBall Q, aestronglyMeasurable_iUnion_iff]
  intro n
  have hball : Metric.ball (cubeCenter Q) (junkInnerRadius Q n) ⊆ openCubeSet Q := by
    rw [openCubeSet_eq_iUnion_junkBall Q]
    exact Set.subset_iUnion (fun m : ℕ => Metric.ball (cubeCenter Q) (junkInnerRadius Q m)) n
  have hcoord : ∀ i : Fin d,
      AEStronglyMeasurable (fun x => F x i)
        (volume.restrict (Metric.ball (cubeCenter Q) (junkInnerRadius Q n))) := by
    intro i
    obtain ⟨φ, hφ⟩ := exists_h10Function_grad_eq_basisVec Q n i
    have hres : IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x))
        (Metric.ball (cubeCenter Q) (junkInnerRadius Q n)) :=
      (h φ).mono_set hball
    refine (hres.congr ?_).aestronglyMeasurable
    refine Filter.Eventually.mono (ae_restrict_mem Metric.isOpen_ball.measurableSet) ?_
    intro x hx
    show vecDot (F x) (φ.toH1Function.grad x) = F x i
    rw [hφ x hx, vecDot_basisVec_right]
  rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
  exact fun i => (hcoord i).aemeasurable

/-- The contrapositive form: a field that is not measurable on the cube has an
`H¹₀(Q)` test function whose pairing with it is not integrable. -/
theorem exists_h10Function_not_integrableOn_vecDot_grad {Q : TriadicCube d}
    {F : Vec d → Vec d}
    (hF : ¬ AEStronglyMeasurable F (volume.restrict (openCubeSet Q))) :
    ∃ φ : H10Function (openCubeSet Q),
      ¬ IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) (openCubeSet Q) := by
  by_contra hcon
  push Not at hcon
  exact hF (aestronglyMeasurable_of_forall_integrableOn_vecDot_grad hcon)

/-! ## The junk branch of the two response equations -/

/-- A vanishing Dirichlet energy on the cube forces the gradient to vanish
almost everywhere there. -/
private theorem grad_ae_eq_zero_of_setIntegral_vecDot_self_eq_zero {Q : TriadicCube d}
    {v : H1Function (openCubeSet Q)}
    (hE : ∫ x in openCubeSet Q, vecDot (v.grad x) (v.grad x) = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), v.grad x = 0 := by
  have hint : IntegrableOn (fun x => vecDot (v.grad x) (v.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2 v.grad_memVectorL2
  have hnn : (0 : Vec d → ℝ) ≤ fun x => vecDot (v.grad x) (v.grad x) := by
    intro x
    exact vecNormSq_nonneg (v.grad x)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 hE
  filter_upwards [hae] with x hx
  refine vecNormSq_eq_zero ?_
  simpa [vecNormSq] using hx

/-- **The junk branch of the Dirichlet equation**: a
Dirichlet response of a flux field that is not measurable on the cube has a
gradient vanishing almost everywhere.

On that branch some pairing `∫_Q F·∇φ` is the Bochner integral of a
non-integrable integrand, hence `0`; the pairings that are integrable form a
linear subspace, so adding the bad test function to a good one keeps the
pairing non-integrable and the equation forces `∫_Q ∇w·∇φ = 0` for *every*
test function, in particular for `φ = w`. -/
theorem grad_ae_eq_zero_of_isCubeDirichletResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {w : H10Function (openCubeSet Q)}
    (hF : ¬ AEStronglyMeasurable F (volume.restrict (openCubeSet Q)))
    (hw : IsCubeDirichletResponse Q F w) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), w.toH1Function.grad x = 0 := by
  obtain ⟨φ₀, hφ₀⟩ := exists_h10Function_not_integrableOn_vecDot_grad hF
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
  exact grad_ae_eq_zero_of_setIntegral_vecDot_self_eq_zero (key w)

/-- **The junk branch of the prescribed-flux Neumann equation**, the companion of
`grad_ae_eq_zero_of_isCubeDirichletResponse`. The
bad test function of the Dirichlet class is admissible here after subtracting
its average, which does not change its gradient. -/
theorem grad_ae_eq_zero_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {w : H1MeanZeroFunction (openCubeSet Q)}
    (hF : ¬ AEStronglyMeasurable F (volume.restrict (openCubeSet Q)))
    (hw : IsCubeNeumannResponse Q F w) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), w.toH1Function.grad x = 0 := by
  obtain ⟨φ₁, hφ₁⟩ := exists_h10Function_not_integrableOn_vecDot_grad hF
  set φ₀ : H1MeanZeroFunction (openCubeSet Q) :=
    H1Function.toMeanZero φ₁.toH1Function with hφ₀def
  have hgradφ₀ : φ₀.toH1Function.grad = φ₁.toH1Function.grad := by
    funext x
    exact H1Function.grad_subAverage φ₁.toH1Function x
  have hφ₀ : ¬ IntegrableOn
      (fun x => vecDot (F x) (φ₀.toH1Function.grad x)) (openCubeSet Q) := by
    rw [hgradφ₀]
    exact hφ₁
  have hzero : ∀ ψ : H1MeanZeroFunction (openCubeSet Q),
      ¬ IntegrableOn (fun x => vecDot (F x) (ψ.toH1Function.grad x)) (openCubeSet Q) →
      ∫ x in openCubeSet Q,
          vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) = 0 := by
    intro ψ hψ
    rw [hw ψ, integral_undef hψ, neg_zero]
  have key : ∀ ψ : H1MeanZeroFunction (openCubeSet Q),
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
  exact grad_ae_eq_zero_of_setIntegral_vecDot_self_eq_zero (key w)

/-! ## The junk branch in the normalized norms -/

/-- Measurability on the open cube transports to the normalized cube measure
and to the Euclidean carrier. -/
theorem aestronglyMeasurable_hilbertifyVecField_normalizedCubeMeasure {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : AEStronglyMeasurable F (volume.restrict (openCubeSet Q))) :
    AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact ((HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable hF).smul_measure _

/-- **The junk branch is exactly non-measurability**: a flux field of finite
`L̲^q(Q)` size which is not an `L̲^q(Q)` field is not measurable on the cube. -/
theorem not_aestronglyMeasurable_of_not_memLp {Q : TriadicCube d} {q : ℝ≥0∞}
    {F : Vec d → Vec d} (hfin : vecCubeLpENorm Q q F < ⊤)
    (hmem : ¬ MemLp (hilbertifyVecField F) q (normalizedCubeMeasure Q)) :
    ¬ AEStronglyMeasurable F (volume.restrict (openCubeSet Q)) := fun _ =>
  hmem (MeasureTheory.memLp_iff.mpr hfin)

/-- A field vanishing almost everywhere on the open cube has vanishing
`L̲^q(Q)` size. -/
theorem vecCubeLpENorm_eq_zero_of_ae_eq_zero {Q : TriadicCube d} {q : ℝ≥0∞}
    {G : Vec d → Vec d} (hG : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), G x = 0) :
    vecCubeLpENorm Q q G = 0 := by
  have hae : hilbertifyVecField G =ᵐ[normalizedCubeMeasure Q] 0 := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    refine Measure.ae_smul_measure ?_ _
    filter_upwards [hG] with x hx
    simp [hilbertifyVecField, hx]
  rw [vecCubeLpENorm, Section2.Norms.cubeLpENorm, eLpNorm_congr_ae hae, eLpNorm_zero]

/-- **The `L̲^q(Q)` form of the Dirichlet junk branch.** -/
theorem vecCubeLpENorm_grad_eq_zero_of_isCubeDirichletResponse {Q : TriadicCube d} {q : ℝ≥0∞}
    {F : Vec d → Vec d} {w : H10Function (openCubeSet Q)}
    (hF : ¬ AEStronglyMeasurable F (volume.restrict (openCubeSet Q)))
    (hw : IsCubeDirichletResponse Q F w) :
    vecCubeLpENorm Q q w.toH1Function.grad = 0 :=
  vecCubeLpENorm_eq_zero_of_ae_eq_zero
    (grad_ae_eq_zero_of_isCubeDirichletResponse hF hw)

/-- **The `L̲^q(Q)` form of the Neumann junk branch.** -/
theorem vecCubeLpENorm_grad_eq_zero_of_isCubeNeumannResponse {Q : TriadicCube d} {q : ℝ≥0∞}
    {F : Vec d → Vec d} {w : H1MeanZeroFunction (openCubeSet Q)}
    (hF : ¬ AEStronglyMeasurable F (volume.restrict (openCubeSet Q)))
    (hw : IsCubeNeumannResponse Q F w) :
    vecCubeLpENorm Q q w.toH1Function.grad = 0 :=
  vecCubeLpENorm_eq_zero_of_ae_eq_zero
    (grad_ae_eq_zero_of_isCubeNeumannResponse hF hw)

end

end ResponseFields
end Section3
end SuperdiffusionCLT
