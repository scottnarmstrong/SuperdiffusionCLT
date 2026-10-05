/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.Basic
public import MarkovProcess.Examples.HeatSemigroup
public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# The `d`-dimensional heat kernel on `Vec d`

The transition kernel of `d`-dimensional Brownian motion: at time `t` from the
starting point `x : Vec d` it is the product over the coordinates of the real
Gaussian laws with means `x i` and common variance `t`.  Because `Vec d` is the
plain function space `Fin d → ℝ`, the product measure `Measure.pi` is literally
the law of `d` independent one-dimensional heat kernels.

Everything is built from the affine representation
`heatKernel d t x = (stdGaussian d).map (fun z ↦ x + Real.sqrt t • z)`, which
makes joint measurability in `(t, x)` automatic and reduces every algebraic
identity to the one-dimensional Gaussian lemmas of Mathlib.

Main results:

* `lintegral_pi_prod`: the lower Fubini identity for a product of functions of
  separate coordinates against a product measure.
* `stdGaussian`, `map_add_smul_stdGaussian`: the standard Gaussian vector and
  the affine representation of the heat kernel.
* `heatKernel`, `heatKernel_apply`: the kernel and its product-Gaussian law.
* `heatKernel_zero`: at time zero it is the identity kernel.
* `heatKernel_comp`, `bind_heatKernel`: the Chapman--Kolmogorov identity.
* `heatKernel_add_right`: translation covariance.
* `heatKernel_smul`: the diffusive scaling covariance.

No process is constructed here; that is the subject of
`SuperdiffusionCLT.Section8.Brownian.BrownianMotion`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Homogenization MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

section ProductIntegral

variable {iota : Type*} [Fintype iota] [DecidableEq iota] {X : iota → Type*}
  [∀ i, MeasurableSpace (X i)] {mu : ∀ i, Measure (X i)} [∀ i, SigmaFinite (mu i)]

omit [DecidableEq iota] in
/-- A product of measurable functions of separate coordinates is measurable. -/
theorem measurable_pi_prod {g : ∀ i, X i → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) :
    Measurable (fun y : ∀ i, X i ↦ ∏ i, g i (y i)) :=
  Finset.measurable_prod _ fun i _ ↦ (hg i).comp (measurable_pi_apply i)

/-- Integrating a product of functions of separate coordinates over the coordinates in a finite
set `s` replaces exactly those factors by their one-dimensional integrals. -/
theorem lmarginal_pi_prod {g : ∀ i, X i → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (s : Finset iota) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y : ∀ i, X i ↦ ∏ i, g i (y i)) ∂mu) x
      = (∏ i ∈ s, ∫⁻ u, g i u ∂(mu i)) * ∏ i ∈ Finset.univ \ s, g i (x i) := by
  classical
  induction s using Finset.induction generalizing x with
  | empty => simp [MeasureTheory.lmarginal_empty]
  | insert i s hi ih =>
    rw [MeasureTheory.lmarginal_insert _ (measurable_pi_prod hg) hi]
    have hsplit : ∀ u : X i,
        (∏ j ∈ Finset.univ \ s, g j (Function.update x i u j))
          = g i u * ∏ j ∈ Finset.univ \ insert i s, g j (x j) := by
      intro u
      have hmem : i ∈ Finset.univ \ s := by simp [hi]
      rw [← Finset.mul_prod_erase _ _ hmem, Function.update_self]
      congr 1
      rw [Finset.sdiff_insert]
      exact Finset.prod_congr rfl fun j hj ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hrearrange : ∀ u : X i,
        (∏ j ∈ s, ∫⁻ v, g j v ∂(mu j)) *
            (g i u * ∏ j ∈ Finset.univ \ insert i s, g j (x j))
          = ((∏ j ∈ s, ∫⁻ v, g j v ∂(mu j)) *
              ∏ j ∈ Finset.univ \ insert i s, g j (x j)) * g i u := fun _ ↦ by ring
    simp_rw [ih, hsplit, hrearrange]
    rw [lintegral_const_mul _ (hg i), Finset.prod_insert hi]
    ring

/-- **Lower Fubini for a product measure.**  The integral of a product of functions of separate
coordinates against `Measure.pi mu` is the product of the one-dimensional integrals.  If the
product space is empty then some factor space is, and both sides are `0`. -/
theorem lintegral_pi_prod {g : ∀ i, X i → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) :
    ∫⁻ y, (∏ i, g i (y i)) ∂(Measure.pi mu) = ∏ i, ∫⁻ u, g i u ∂(mu i) := by
  classical
  rcases isEmpty_or_nonempty (∀ i, X i) with hempty | hne
  · obtain ⟨i, hi⟩ := isEmpty_pi.mp hempty
    have := hi
    rw [lintegral_of_isEmpty]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (lintegral_of_isEmpty _ _)).symm
  · have h := lmarginal_pi_prod (mu := mu) hg Finset.univ (Classical.arbitrary (∀ i, X i))
    rw [MeasureTheory.lmarginal_univ] at h
    simpa using h

end ProductIntegral

section StandardGaussian

variable {d : ℕ}

/-- The standard Gaussian vector on `Vec d`: the product of `d` independent standard normal
laws on the coordinates. -/
def stdGaussian (d : ℕ) : Measure (Vec d) :=
  Measure.pi fun _ : Fin d ↦ gaussianReal 0 1

instance isProbabilityMeasure_stdGaussian (d : ℕ) : IsProbabilityMeasure (stdGaussian d) := by
  rw [stdGaussian]
  infer_instance

/-- **The affine representation of the `d`-dimensional Gaussian law.**  The product of the real
Gaussians with means `x i` and common variance `t` is the image of the standard Gaussian vector
under the affine map `z ↦ x + √t • z`. -/
theorem map_add_smul_stdGaussian (x : Vec d) (t : ℝ≥0) :
    (stdGaussian d).map (fun z ↦ x + Real.sqrt t • z)
      = Measure.pi fun i ↦ gaussianReal (x i) t := by
  have hfun : (fun z : Vec d ↦ x + Real.sqrt (t : ℝ) • z)
      = fun (z : Vec d) (i : Fin d) ↦ x i + Real.sqrt (t : ℝ) * z i := rfl
  rw [stdGaussian, hfun,
    Measure.pi_map_pi (f := fun (i : Fin d) (u : ℝ) ↦ x i + Real.sqrt (t : ℝ) * u)
      (fun _ ↦ (by fun_prop : Measurable _).aemeasurable)]
  exact congrArg Measure.pi
    (funext fun i ↦ (MarkovProcess.gaussianReal_eq_map_add_sqrt_mul (x i) t).symm)

end StandardGaussian

section Definition

variable {d : ℕ}

/-- The `d`-dimensional Gaussian transition kernel, jointly in the time and the starting point.
It is the image of the standard Gaussian vector under the jointly measurable affine map
`(t, x, z) ↦ x + √t • z`. -/
def heatKernelJoint (d : ℕ) : Kernel (ℝ≥0 × Vec d) (Vec d) :=
  (Kernel.id ×ₖ Kernel.const (ℝ≥0 × Vec d) (stdGaussian d)).map
    (fun q : (ℝ≥0 × Vec d) × Vec d ↦ q.1.2 + Real.sqrt q.1.1 • q.2)

private theorem measurable_affine (d : ℕ) :
    Measurable (fun q : (ℝ≥0 × Vec d) × Vec d ↦ q.1.2 + Real.sqrt q.1.1 • q.2) := by
  refine Measurable.of_eval fun i ↦ ?_
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).add
    (((NNReal.continuous_coe.comp continuous_fst).sqrt.measurable.comp
      measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd))

theorem heatKernelJoint_apply (p : ℝ≥0 × Vec d) :
    heatKernelJoint d p = Measure.pi fun i ↦ gaussianReal (p.2 i) p.1 := by
  rw [heatKernelJoint, Kernel.map_apply _ (measurable_affine d), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_affine d) (by fun_prop), ← map_add_smul_stdGaussian p.2 p.1]
  rfl

/-- **The `d`-dimensional heat kernel at time `t`**: from `x : Vec d` it is the product of the
real Gaussian laws with means the coordinates of `x` and common variance `t`. -/
def heatKernel (d : ℕ) (t : ℝ≥0) : Kernel (Vec d) (Vec d) :=
  Kernel.comap (heatKernelJoint d) (fun x : Vec d ↦ (t, x)) (by fun_prop)

@[simp]
theorem heatKernel_apply (t : ℝ≥0) (x : Vec d) :
    heatKernel d t x = Measure.pi fun i ↦ gaussianReal (x i) t := by
  rw [heatKernel, Kernel.comap_apply, heatKernelJoint_apply]

theorem heatKernel_apply_eq_map (t : ℝ≥0) (x : Vec d) :
    heatKernel d t x = (stdGaussian d).map (fun z ↦ x + Real.sqrt t • z) := by
  rw [heatKernel_apply, map_add_smul_stdGaussian]

instance isMarkovKernel_heatKernel (t : ℝ≥0) : IsMarkovKernel (heatKernel (d := d) t) :=
  ⟨fun x ↦ by rw [heatKernel_apply]; infer_instance⟩

theorem measurable_heatKernelJoint (d : ℕ) :
    Measurable fun p : ℝ≥0 × Vec d ↦ heatKernel d p.1 p.2 := by
  have hfun : (fun p : ℝ≥0 × Vec d ↦ heatKernel d p.1 p.2) = fun p ↦ heatKernelJoint d p := by
    funext p
    rw [heatKernel, Kernel.comap_apply]
  rw [hfun]
  exact (heatKernelJoint d).measurable

/-- At time zero the heat kernel is the identity kernel. -/
theorem heatKernel_zero (d : ℕ) : heatKernel d 0 = Kernel.id := by
  refine Kernel.ext fun x ↦ ?_
  rw [heatKernel_apply_eq_map, Kernel.id_apply]
  have hfun : (fun z : Vec d ↦ x + Real.sqrt ((0 : ℝ≥0) : ℝ) • z) = fun _ ↦ x := by
    funext z
    rw [NNReal.coe_zero, Real.sqrt_zero, zero_smul, add_zero]
  rw [hfun, Measure.map_const, measure_univ, one_smul]

/-- At time zero the heat kernel is the Dirac mass at the starting point. -/
theorem heatKernel_zero_apply (x : Vec d) : heatKernel d 0 x = Measure.dirac x := by
  rw [heatKernel_zero, Kernel.id_apply]

end Definition

section ChapmanKolmogorov

variable {d : ℕ}

private theorem measurable_gaussianReal_measure (t : ℝ≥0) {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable fun u : ℝ ↦ gaussianReal u t A := by
  have hfun : (fun u : ℝ ↦ gaussianReal u t A) = fun u ↦ MarkovProcess.heatKernel t u A :=
    funext fun u ↦ by rw [MarkovProcess.heatKernel_apply]
  rw [hfun]
  exact (MarkovProcess.heatKernel t).measurable_coe hA

/-- **The Chapman--Kolmogorov identity for the `d`-dimensional heat kernel.**  Sampling the
kernel at time `s` from `x` and then the kernel at time `t` from the value obtained gives the
kernel at time `s + t` from `x`. -/
theorem bind_heatKernel (s t : ℝ≥0) (x : Vec d) :
    (heatKernel d s x).bind (heatKernel d t) = heatKernel d (s + t) x := by
  rw [heatKernel_apply (s + t)]
  refine (Measure.pi_eq fun A hA ↦ ?_).symm
  have hpi : MeasurableSet (Set.univ.pi A) := MeasurableSet.univ_pi hA
  rw [Measure.bind_apply hpi (heatKernel d t).aemeasurable]
  have hinner : ∀ y : Vec d, heatKernel d t y (Set.univ.pi A) = ∏ i, gaussianReal (y i) t (A i) :=
    fun y ↦ by rw [heatKernel_apply, Measure.pi_pi]
  simp_rw [hinner, heatKernel_apply]
  rw [lintegral_pi_prod (mu := fun i : Fin d ↦ gaussianReal (x i) s)
    (g := fun i u ↦ gaussianReal u t (A i))
    fun i ↦ measurable_gaussianReal_measure t (hA i)]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← Measure.bind_apply (hA i) (MarkovProcess.measurable_gaussianReal_left t).aemeasurable,
    MarkovProcess.bind_gaussianReal]

/-- The Chapman--Kolmogorov identity in Mathlib's kernel-composition orientation. -/
theorem heatKernel_comp (s t : ℝ≥0) :
    (heatKernel d t).comp (heatKernel d s) = heatKernel d (s + t) :=
  Kernel.ext fun x ↦ by rw [Kernel.comp_apply, bind_heatKernel]

end ChapmanKolmogorov

section Covariance

variable {d : ℕ}

/-- **Translation covariance.**  Shifting the starting point shifts the heat kernel. -/
theorem heatKernel_add_right (t : ℝ≥0) (x y : Vec d) :
    heatKernel d t (x + y) = (heatKernel d t x).map fun z ↦ z + y := by
  have hfun : (fun z : Vec d ↦ z + y) = fun (z : Vec d) (i : Fin d) ↦ z i + y i := rfl
  rw [heatKernel_apply, heatKernel_apply, hfun,
    Measure.pi_map_pi (f := fun (i : Fin d) (u : ℝ) ↦ u + y i)
      fun _ ↦ (by fun_prop : Measurable _).aemeasurable]
  exact congrArg Measure.pi (funext fun i ↦ (gaussianReal_map_add_const (y i)).symm)

private theorem nnreal_sq_coe (c : ℝ≥0) : NNReal.mk ((c : ℝ) ^ 2) (sq_nonneg _) = c ^ 2 :=
  NNReal.coe_injective (by rw [NNReal.coe_pow]; rfl)

/-- **Diffusive scaling covariance.**  Dilating space by `c` and time by `c ^ 2` maps the heat
kernel to itself. -/
theorem heatKernel_smul (c t : ℝ≥0) (x : Vec d) :
    heatKernel d (c ^ 2 * t) ((c : ℝ) • x) = (heatKernel d t x).map fun z ↦ (c : ℝ) • z := by
  have hfun : (fun z : Vec d ↦ (c : ℝ) • z) = fun (z : Vec d) (i : Fin d) ↦ (c : ℝ) * z i := rfl
  rw [heatKernel_apply, heatKernel_apply, hfun,
    Measure.pi_map_pi (f := fun (_ : Fin d) (u : ℝ) ↦ (c : ℝ) * u)
      fun _ ↦ (by fun_prop : Measurable _).aemeasurable]
  refine congrArg Measure.pi (funext fun i ↦ ?_)
  rw [gaussianReal_map_const_mul (c : ℝ), nnreal_sq_coe]
  rfl

end Covariance

end

end SuperdiffusionCLT.Section8.Brownian
