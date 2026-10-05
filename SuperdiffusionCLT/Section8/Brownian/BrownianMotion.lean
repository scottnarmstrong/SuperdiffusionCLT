/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.HeatSemigroup
public import MarkovProcess.Main
public import MarkovProcess.Trajectory.Equivariance

/-!
# Standard `d`-dimensional Brownian motion on `Vec d`

The continuous-path process of the `d`-dimensional heat semigroup: the unique Markov kernel from
a starting point `x : Vec d` to continuous paths in `Vec d` whose finite-dimensional
distributions are the iterated product-Gaussian transition laws.  It is the limit object of the
quenched invariance principle.

Main results:

* `brownianMotion`, `existsUnique_continuousProcess_heatSemigroup`: the process and the exact
  sense in which it is unique.
* `brownianMotion_map_eval`: the one-time marginal is the `d`-dimensional heat kernel, that is,
  the product of the real Gaussian laws with means the coordinates of `x` and variance `t`.
* `brownianMotion_map_eval_coord`, `iIndepFun_coord_brownianMotion`: the coordinates of the
  position at a fixed time are independent real Gaussians.
* `brownianMotion_map_finsetEvaluation`, `eq_brownianMotion_of_map_finsetEvaluation`: the
  finite-dimensional distributions and uniqueness from them.
* `brownianMotion_map_prodMk_shift`: the simple Markov property in joint-law form.
* `brownianMotion_map_sub`: every increment is a centred `d`-dimensional Gaussian vector of
  variance the elapsed time.
* `isRescaledConjugate_heatSemigroup`, `brownianMotion_apply_smul`: Brownian scaling, the
  invariance of the law under a dilation of space by `a` and of time by `a ^ (-2)`.

Many names of this namespace and of its two companion modules -- `heatKernel`, `heatSemigroup`,
`brownianMotion` and their `_apply`/`_map` variants among them -- repeat the names `MarkovProcess`
uses for the one-dimensional objects, so a file that opens both `MarkovProcess` and
`SuperdiffusionCLT.Section8.Brownian` will see ambiguous terms; open only one of the two
namespaces, and write the other's names in full.

Nothing here identifies the generator: half the Laplacian on `Vec d` requires a quantitative
second-order Taylor estimate for functions of `d` real variables, which the pinned Mathlib
provides only for functions of one real variable.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Homogenization MeasureTheory ProbabilityTheory
open MarkovProcess
open scoped ENNReal NNReal

noncomputable section

section MarkovProperty

/-- A joint law factorizes through a kernel as soon as the law of the second variable, after
restriction to every event determined by the first, is the kernel composed with that
restriction. -/
private theorem map_prodMk_eq_compProd_of_restrict_map
    {Omega beta gamma : Type*} {mOmega : MeasurableSpace Omega}
    {mBeta : MeasurableSpace beta} {mGamma : MeasurableSpace gamma}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → beta) (hX : Measurable X)
    (Y : Omega → gamma) (hY : Measurable Y)
    (kappa : Kernel beta gamma) [IsMarkovKernel kappa]
    (hrestrict : ∀ C : Set beta, MeasurableSet C →
      (mu.restrict (X ⁻¹' C)).map Y = kappa.comap X hX ∘ₘ (mu.restrict (X ⁻¹' C))) :
    mu.map (fun omega ↦ (X omega, Y omega)) = (mu.map X) ⊗ₘ kappa := by
  have : IsProbabilityMeasure (mu.map fun omega ↦ (X omega, Y omega)) := inferInstance
  have : IsProbabilityMeasure (mu.map X) := inferInstance
  refine MeasureTheory.ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨C, hC, B, hB, rfl⟩
    have hleft : mu.map (fun omega ↦ (X omega, Y omega)) (C ×ˢ B)
        = ∫⁻ omega in X ⁻¹' C, kappa (X omega) B ∂mu := by
      rw [Measure.map_apply (hX.prodMk hY) (hC.prod hB), Set.mk_preimage_prod, Set.inter_comm,
        ← Measure.restrict_apply (hY hB), ← Measure.map_apply hY hB, hrestrict C hC,
        Measure.bind_apply hB (Kernel.aemeasurable _)]
      simp_rw [Kernel.comap_apply]
    rw [hleft, Measure.compProd_apply_prod hC hB, setLIntegral_map hC (kappa.measurable_coe hB) hX]
  · rw [measure_univ, measure_univ]

end MarkovProperty

section Process

variable {d : ℕ}

/-- **Existence and uniqueness for the `d`-dimensional heat semigroup.**  There is exactly one
Markov kernel from `Vec d` to continuous paths in `Vec d` whose finite-dimensional distributions
are the product-Gaussian transition laws of the heat semigroup. -/
theorem existsUnique_continuousProcess_heatSemigroup (d : ℕ) :
    ∃! Q : Kernel (Vec d) (ContinuousPath (Vec d)), IsMarkovKernel Q ∧
      ∀ I : Finset ℝ≥0,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (heatSemigroup d) I :=
  (isFellerKernelSemigroup_heatSemigroup
      d).existsUnique_continuousProcess_of_hasKolmogorovMoments (heatSemigroup d)
    (isConservative_heatSemigroup d) (hasKolmogorovMoments_heatSemigroup d)

/-- **Standard `d`-dimensional Brownian motion**, as a Markov kernel from the starting point to
continuous paths in `Vec d`: the continuous-path process of the `d`-dimensional heat
semigroup. -/
def brownianMotion (d : ℕ) : Kernel (Vec d) (ContinuousPath (Vec d)) :=
  SubMarkovKernelSemigroup.IsConservative.continuousProcess (heatSemigroup d)
    (isConservative_heatSemigroup d)

instance isMarkovKernel_brownianMotion (d : ℕ) : IsMarkovKernel (brownianMotion d) := by
  unfold brownianMotion
  infer_instance

/-- **Every one-time marginal of `d`-dimensional Brownian motion is the heat kernel**: from `x`
at time `t` it is the product of the real Gaussian laws with means the coordinates of `x` and
common variance `t`. -/
theorem brownianMotion_map_eval (t : ℝ≥0) (x : Vec d) :
    (brownianMotion d x).map (fun omega ↦ omega t) = Measure.pi fun i ↦ gaussianReal (x i) t := by
  have hmeas : Measurable fun omega : ContinuousPath (Vec d) ↦ omega t :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t
  rw [brownianMotion, ← Kernel.map_apply _ hmeas,
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
      (heatSemigroup d) (isConservative_heatSemigroup d) (isFellerKernelSemigroup_heatSemigroup d)
      (kolmogorovRegular_heatSemigroup d) t, heatSemigroup_apply]

/-- Each coordinate of the position at a fixed time is a real Gaussian of variance the elapsed
time. -/
theorem brownianMotion_map_eval_coord (t : ℝ≥0) (x : Vec d) (i : Fin d) :
    (brownianMotion d x).map (fun omega ↦ omega t i) = gaussianReal (x i) t := by
  have hmeas : Measurable fun omega : ContinuousPath (Vec d) ↦ omega t :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t
  rw [show (fun omega : ContinuousPath (Vec d) ↦ omega t i)
      = Function.eval i ∘ fun omega : ContinuousPath (Vec d) ↦ omega t from rfl,
    ← Measure.map_map (measurable_pi_apply i) hmeas, brownianMotion_map_eval]
  exact (MeasureTheory.measurePreserving_eval (μ := fun j : Fin d ↦ gaussianReal (x j) t) i).map_eq

/-- **The coordinates of the position at a fixed time are independent.** -/
theorem iIndepFun_coord_brownianMotion (t : ℝ≥0) (x : Vec d) :
    iIndepFun (fun (i : Fin d) (omega : ContinuousPath (Vec d)) ↦ omega t i)
      (brownianMotion d x) := by
  have hmeas : ∀ i : Fin d,
      AEMeasurable (fun omega : ContinuousPath (Vec d) ↦ omega t i) (brownianMotion d x) :=
    fun i ↦ ((measurable_pi_apply i).comp
      (ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t)).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  have hfun : (fun (omega : ContinuousPath (Vec d)) (i : Fin d) ↦ omega t i)
      = fun omega : ContinuousPath (Vec d) ↦ omega t := rfl
  rw [hfun, brownianMotion_map_eval]
  exact congrArg Measure.pi (funext fun i ↦ (brownianMotion_map_eval_coord t x i).symm)

/-- Every finite-dimensional distribution of `d`-dimensional Brownian motion is the corresponding
finite-set kernel of the heat semigroup. -/
theorem brownianMotion_map_finsetEvaluation (d : ℕ) (I : Finset ℝ≥0) :
    (brownianMotion d).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel (heatSemigroup d) I :=
  (isFellerKernelSemigroup_heatSemigroup d).continuousProcess_map_finiteEvaluation
    (heatSemigroup d) (isConservative_heatSemigroup d) (kolmogorovRegular_heatSemigroup d) I

/-- `d`-dimensional Brownian motion is the only Markov kernel into continuous paths with the
finite-dimensional distributions of the heat semigroup. -/
theorem eq_brownianMotion_of_map_finsetEvaluation (d : ℕ)
    (Q : Kernel (Vec d) (ContinuousPath (Vec d))) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel (heatSemigroup d) I) :
    Q = brownianMotion d :=
  SubMarkovKernelSemigroup.IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    (heatSemigroup d) (isConservative_heatSemigroup d) (kolmogorovRegular_heatSemigroup d) Q hQ

/-- **The simple Markov property of `d`-dimensional Brownian motion, in joint-law form.**  The
joint law of the position at time `s` and the path shifted by `s` is the composition-product of
the heat kernel at time `s` with the process. -/
theorem brownianMotion_map_prodMk_shift (x : Vec d) (s : ℝ≥0) :
    (brownianMotion d x).map (fun omega ↦ (omega s, ContinuousPath.shift s omega)) =
      (Measure.pi fun i ↦ gaussianReal (x i) s) ⊗ₘ brownianMotion d := by
  have hX : Measurable fun omega : ContinuousPath (Vec d) ↦ omega s :=
    ContinuousPath.measurable_coordinateProcess s
  have hY : Measurable (ContinuousPath.shift (alpha := Vec d) s) :=
    ContinuousPath.measurable_shift_fixed s
  rw [← brownianMotion_map_eval s x]
  refine map_prodMk_eq_compProd_of_restrict_map (brownianMotion d x) _ hX _ hY
    (brownianMotion d) fun C hC ↦ ?_
  have hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := Vec d) s]
      ((fun omega : ContinuousPath (Vec d) ↦ omega s) ⁻¹' C) :=
    ContinuousPath.measurable_coordinateProcess_canonicalFiltration s hC
  exact SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
    (heatSemigroup d) (isConservative_heatSemigroup d) (isFellerKernelSemigroup_heatSemigroup d)
    (kolmogorovRegular_heatSemigroup d) x s _ hA

/-- The heat kernel started at `y` and recentred at `y` is the heat kernel started at the
origin. -/
theorem map_sub_heatKernel (t : ℝ≥0) (y : Vec d) :
    (heatKernel d t y).map (fun z ↦ z - y) = heatKernel d t 0 := by
  have hy : heatKernel d t y = (heatKernel d t 0).map fun z ↦ z + y := by
    rw [← heatKernel_add_right t 0 y, zero_add]
  rw [hy, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : ((fun z : Vec d ↦ z - y) ∘ fun z : Vec d ↦ z + y) = id :=
    funext fun z ↦ add_sub_cancel_right z y
  rw [hcomp, Measure.map_id]

/-- **Every increment of `d`-dimensional Brownian motion is a centred Gaussian vector** of
variance the elapsed time, independently of the starting point and of the initial time. -/
theorem brownianMotion_map_sub (x : Vec d) (s t : ℝ≥0) :
    (brownianMotion d x).map (fun omega ↦ omega (s + t) - omega s) = heatKernel d t 0 := by
  have hPhi : Measurable fun p : Vec d × ContinuousPath (Vec d) ↦ p.2 t - p.1 :=
    ((ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t).comp
      measurable_snd).sub measurable_fst
  have hpair : Measurable fun omega : ContinuousPath (Vec d) ↦
      (omega s, ContinuousPath.shift s omega) :=
    (ContinuousPath.measurable_coordinateProcess s).prodMk
      (ContinuousPath.measurable_shift_fixed s)
  have hfac : (fun omega : ContinuousPath (Vec d) ↦ omega (s + t) - omega s)
      = (fun p : Vec d × ContinuousPath (Vec d) ↦ p.2 t - p.1) ∘
        fun omega ↦ (omega s, ContinuousPath.shift s omega) := rfl
  rw [hfac, ← Measure.map_map hPhi hpair, brownianMotion_map_prodMk_shift]
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply hPhi hA, Measure.compProd_apply (hPhi hA)]
  have hsub : ∀ y : Vec d, Measurable fun z : Vec d ↦ z - y := fun _ ↦ by fun_prop
  have hev : Measurable fun eta : ContinuousPath (Vec d) ↦ eta t :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t
  have hfiber : ∀ y : Vec d,
      brownianMotion d y (Prod.mk y ⁻¹'
          ((fun p : Vec d × ContinuousPath (Vec d) ↦ p.2 t - p.1) ⁻¹' A))
        = heatKernel d t 0 A := by
    intro y
    have hset : (Prod.mk y ⁻¹'
        ((fun p : Vec d × ContinuousPath (Vec d) ↦ p.2 t - p.1) ⁻¹' A))
          = (fun eta : ContinuousPath (Vec d) ↦ eta t) ⁻¹' ((fun z : Vec d ↦ z - y) ⁻¹' A) := rfl
    rw [hset, ← Measure.map_apply hev (hsub y hA),
      brownianMotion_map_eval, ← heatKernel_apply t y,
      ← Measure.map_apply (hsub y) hA, map_sub_heatKernel]
  simp_rw [hfiber]
  rw [lintegral_const, measure_univ, mul_one]

end Process

section Scaling

variable {d : ℕ}

/-- The dilation of `Vec d` by a nonzero real factor, as a homeomorphism. -/
def dilation (a : ℝ) (ha : a ≠ 0) : Vec d ≃ₜ Vec d :=
  Homeomorph.smulOfNeZero a ha

@[simp]
theorem dilation_apply (a : ℝ) (ha : a ≠ 0) (x : Vec d) : dilation a ha x = a • x := rfl

@[simp]
theorem dilation_symm_apply (a : ℝ) (ha : a ≠ 0) (x : Vec d) :
    (dilation a ha).symm x = a⁻¹ • x := by
  simp [dilation, Homeomorph.smulOfNeZero, Units.smul_def]

/-- **The heat semigroup is its own rescaled conjugate** under the dilation of space by `a` and
of time by `a ^ (-2)`. -/
theorem isRescaledConjugate_heatSemigroup (a : ℝ≥0) (ha : a ≠ 0) :
    SubMarkovKernelSemigroup.IsRescaledConjugate (heatSemigroup d) (heatSemigroup d)
      (dilation (d := d) (a : ℝ) (NNReal.coe_ne_zero.mpr ha)) (a ^ 2)⁻¹ := by
  have hane : (a : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr ha
  have hsq : (a : ℝ≥0) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  intro t x
  have hscale := heatKernel_smul (d := d) a ((a ^ 2)⁻¹ * t) ((a : ℝ)⁻¹ • x)
  rw [← mul_assoc, mul_inv_cancel₀ hsq, one_mul, smul_smul, mul_inv_cancel₀ hane,
    one_smul] at hscale
  exact hscale

/-- **Brownian scaling.**  Dilating space by `a` and time by `a ^ (-2)` maps `d`-dimensional
Brownian motion started at `x` to `d`-dimensional Brownian motion started at `a • x`. -/
theorem brownianMotion_apply_smul (a : ℝ≥0) (ha : a ≠ 0) (x : Vec d) :
    brownianMotion d ((a : ℝ) • x) =
      (brownianMotion d x).map
        (ContinuousPath.rescale (dilation (d := d) (a : ℝ) (NNReal.coe_ne_zero.mpr ha))
          (a ^ 2)⁻¹) := by
  have hane : (a : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr ha
  have hc : 0 < ((a : ℝ≥0) ^ 2)⁻¹ := pos_iff_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 ha))
  have hrescale := SubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale
    (heatSemigroup d) (isConservative_heatSemigroup d) (heatSemigroup d)
    (isConservative_heatSemigroup d) (isFellerKernelSemigroup_heatSemigroup d)
    (kolmogorovRegular_heatSemigroup d) (kolmogorovRegular_heatSemigroup d) hc
    (isRescaledConjugate_heatSemigroup a ha) ((a : ℝ) • x)
  rw [dilation_symm_apply, smul_smul, inv_mul_cancel₀ hane, one_smul] at hrescale
  exact hrescale

/-- The path map of Brownian scaling read pointwise: it dilates the value by `a` and slows the
clock by `a ^ 2`. -/
theorem rescale_dilation_apply (a : ℝ≥0) (ha : a ≠ 0) (omega : ContinuousPath (Vec d))
    (t : ℝ≥0) :
    ContinuousPath.rescale (dilation (d := d) (a : ℝ) (NNReal.coe_ne_zero.mpr ha))
        (a ^ 2)⁻¹ omega t = (a : ℝ) • omega ((a ^ 2)⁻¹ * t) :=
  rfl

end Scaling

end

end SuperdiffusionCLT.Section8.Brownian
