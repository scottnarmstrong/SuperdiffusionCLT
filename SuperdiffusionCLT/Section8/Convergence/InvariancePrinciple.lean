/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.HeatGenerator
public import SuperdiffusionCLT.Section8.Convergence.CoreResolvent
public import SuperdiffusionCLT.Section8.Rescaling.DilationMoments

/-!
# The heat semigroup and the differentiable class of its generator

The Brownian limit object of the manuscript's Theorem A: a family of conservative Feller
transition semigroups on `Vec d` whose generators converge to half the Laplacian has the heat
semigroup as its limit, and this module provides that semigroup on `C₀(Vec d, ℝ)` together with
the class of functions on which its generator is computed as half the Laplacian.

## What is a hypothesis and what is proved

The generator convergence is a **hypothesis** of the downstream assembly.  Its verification for
the marginal rescaled process is the manuscript's Proposition `p.generators`, which is Section 8
homogenization material and is not touched here.  What is proved here is the bookkeeping of the
limit semigroup: the heat semigroup of `Section8.Brownian` as a strongly continuous contraction
semigroup, and half the Laplacian, identified there by `generator_heatSemigroup`, as its
generator on the differentiable class.

## The core hypothesis

The class `heatCore d` -- the `C₀` functions that are twice continuously differentiable with
second derivative vanishing at infinity -- is the class on which `generator_heatSemigroup`
computes the generator as half the Laplacian.  The manuscript's Proposition `p.generators`
supplies approximants only for `C_c^∞(ℝ^d)`, a proper subclass of `heatCore d`, and the
manuscript asserts in the proof of `p.generators` that `C_c^∞(ℝ^d)` is a standard core for the
Brownian generator `½Δ` on `C₀(ℝ^d)`.  A core in the range-density sense of `CoreResolvent` is
reduced below to a smoothing statement about the heat resolvent.

Main results:

* `heatC0Semigroup`: the heat semigroup as a strongly continuous contraction semigroup on
  `C₀(Vec d, ℝ)`.
* `heatCore`, `heatCoreLaplacian`, `mem_generatorDomain_heatCore`, `generator_heatCore`: the
  differentiable class, its Laplacian read as a `C₀` function, and the generator on it.
* `dense_smul_sub_heatCoreLaplacian_of_resolvent_mem`: the core hypothesis holds as soon as the
  heat resolvent maps some dense set of `C₀(Vec d, ℝ)` into the differentiable class.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence

open Filter Homogenization MeasureTheory Topology
open MarkovProcess
open MarkovProcess.Semigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

section Limit

variable {d : ℕ}

/-- **The `C₀` semigroup of `d`-dimensional Brownian motion**: the strongly continuous
contraction semigroup of Gaussian averages on `C₀(Vec d, ℝ)`, whose generator is half the
Laplacian. -/
def heatC0Semigroup (d : ℕ) : StronglyContinuousContractionSemigroup C₀(Vec d, ℝ) :=
  (Brownian.isFellerKernelSemigroup_heatSemigroup d).c0Semigroup

end Limit

section Core

variable {d : ℕ}

/-- **The differentiable class of the heat generator**: the `C₀` functions on `Vec d` that are
twice continuously differentiable and whose second derivative vanishes at infinity.  On this
class the generator of the heat semigroup is half the Laplacian
(`Brownian.generator_heatSemigroup`). -/
def heatCore (d : ℕ) : Set C₀(Vec d, ℝ) :=
  {f | ContDiff ℝ 2 (f : Vec d → ℝ) ∧
    Tendsto (iteratedFDeriv ℝ 2 (f : Vec d → ℝ)) (cocompact (Vec d)) (𝓝 0)}

/-- The Laplacian of a twice continuously differentiable function is continuous. -/
theorem continuous_vecLaplacian {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Brownian.vecLaplacian f) := by
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (continuous_eval_const _).comp (hf.continuous_iteratedFDeriv (by norm_num))

/-- The Laplacian is dominated by the dimension times the norm of the second derivative: the
metric of `Vec d` is the coordinatewise supremum metric, so each coordinate direction is a unit
vector. -/
theorem abs_vecLaplacian_le (f : Vec d → ℝ) (x : Vec d) :
    |Brownian.vecLaplacian f x| ≤ (d : ℝ) * ‖iteratedFDeriv ℝ 2 f x‖ := by
  have hterm : ∀ i : Fin d,
      |iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single i 1]|
        ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
    intro i
    have h := (iteratedFDeriv ℝ 2 f x).le_opNorm
      ![(Pi.single i 1 : Vec d), (Pi.single i 1 : Vec d)]
    rw [Real.norm_eq_abs] at h
    refine le_trans h (le_of_eq ?_)
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.norm_single, norm_one, mul_one]
  calc |Brownian.vecLaplacian f x|
      ≤ ∑ i : Fin d, |iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single i 1]| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖iteratedFDeriv ℝ 2 f x‖ := Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (d : ℝ) * ‖iteratedFDeriv ℝ 2 f x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- If the second derivative vanishes at infinity then so does the Laplacian. -/
theorem tendsto_vecLaplacian_cocompact {f : Vec d → ℝ}
    (hf2 : Tendsto (iteratedFDeriv ℝ 2 f) (cocompact (Vec d)) (𝓝 0)) :
    Tendsto (Brownian.vecLaplacian f) (cocompact (Vec d)) (𝓝 0) := by
  refine squeeze_zero_norm (a := fun x ↦ (d : ℝ) * ‖iteratedFDeriv ℝ 2 f x‖) (fun x ↦ ?_) ?_
  · rw [Real.norm_eq_abs]
    exact abs_vecLaplacian_le f x
  · simpa only [mul_zero] using
      Filter.Tendsto.const_mul (d : ℝ) (tendsto_zero_iff_norm_tendsto_zero.mp hf2)

/-- **The Laplacian of a function of the differentiable class, as a `C₀` function.** -/
def heatCoreLaplacian (f : heatCore d) : C₀(Vec d, ℝ) :=
  ⟨⟨Brownian.vecLaplacian ((f : C₀(Vec d, ℝ)) : Vec d → ℝ), continuous_vecLaplacian f.2.1⟩,
    tendsto_vecLaplacian_cocompact f.2.2⟩

@[simp]
theorem heatCoreLaplacian_apply (f : heatCore d) (x : Vec d) :
    heatCoreLaplacian f x = Brownian.vecLaplacian ((f : C₀(Vec d, ℝ)) : Vec d → ℝ) x :=
  rfl

/-- **The differentiable class lies in the generator domain of the heat semigroup.** -/
theorem mem_generatorDomain_heatCore (f : heatCore d) :
    (f : C₀(Vec d, ℝ)) ∈ (heatC0Semigroup d).generatorDomain :=
  Brownian.mem_generatorDomain_heatSemigroup _ (heatCoreLaplacian f) f.2.1 f.2.2 fun _ ↦ rfl

/-- **The generator of the heat semigroup on the differentiable class is half the
Laplacian.** -/
theorem generator_heatCore (f : heatCore d) :
    (heatC0Semigroup d).generator ⟨(f : C₀(Vec d, ℝ)), mem_generatorDomain_heatCore f⟩
      = (2 : ℝ)⁻¹ • heatCoreLaplacian f :=
  Brownian.generator_heatSemigroup _ (heatCoreLaplacian f) f.2.1 f.2.2 fun _ ↦ rfl

/-- **A sufficient condition for the differentiable class to be a core.**  If the resolvent at
the shift `mu` maps a dense set `G` of `C₀(Vec d, ℝ)` into the class, then the functions
`mu * f - ½ Δ f`, for `f` in the class, are dense: they already contain `G`, because
`mu * R_mu g - L (R_mu g) = g` and the generator on the class is half the Laplacian.

This is the reduction of the core hypothesis for the differentiable class to a smoothing
statement about the heat resolvent, which is not proved here.  The hypothesis is genuinely
restrictive: the resolvent of an arbitrary `C₀` function need not be twice differentiable, so `G`
has to be a class of functions whose potentials are smooth. -/
theorem dense_smul_sub_heatCoreLaplacian_of_resolvent_mem (mu : PositiveShift)
    {G : Set C₀(Vec d, ℝ)} (hG : Dense G)
    (hres : ∀ g ∈ G, (heatC0Semigroup d).resolvent mu g ∈ heatCore d) :
    Dense {h : C₀(Vec d, ℝ) | ∃ f : heatCore d,
      (mu : ℝ) • (f : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f = h} := by
  refine hG.mono fun g hg ↦ ?_
  refine ⟨⟨(heatC0Semigroup d).resolvent mu g, hres g hg⟩, ?_⟩
  have hgen : (heatC0Semigroup d).generator
      ⟨((⟨_, hres g hg⟩ : heatCore d) : C₀(Vec d, ℝ)),
        mem_generatorDomain_heatCore ⟨_, hres g hg⟩⟩
      = (mu : ℝ) • (heatC0Semigroup d).resolvent mu g - g :=
    (heatC0Semigroup d).generator_eq_of_resolvent_eq mu _ rfl
  rw [← generator_heatCore, hgen]
  abel

end Core

section Abstract

variable {d : ℕ} {iota : Type*} {l : Filter iota} {P : iota → SubMarkovKernelSemigroup (Vec d)}

end Abstract

section Marginal

variable {d : ℕ} {iota : Type*} {l : Filter iota} {P : SubMarkovKernelSemigroup (Vec d)}
  {cStar : ℝ} {ep : iota → ℝ}

end Marginal

end

end SuperdiffusionCLT.Section8.Convergence
