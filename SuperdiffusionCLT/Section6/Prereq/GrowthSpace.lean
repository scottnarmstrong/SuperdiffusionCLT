/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.EuclidBall
public import Homogenization.PDE.Harmonic

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The volume-normalized `L²` norm `‖f‖_{L̲²(B_r)}` on the Euclidean ball `B_r`. -/
noncomputable def ballL2 (r : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f 2 (ballMeasure r)

/-- The volume-normalized `L²` norm `‖F‖_{L̲²(B_r)}` of a vector field (Euclidean length). -/
noncomputable def ballGradL2 (r : ℝ) (F : Vec d → Vec d) : ℝ≥0∞ :=
  eLpNorm (fun x => Real.sqrt (vecNormSq (F x))) 2 (ballMeasure r)

/-- `u ∈ 𝒜(B_R; a)` with weak gradient `g`: `u` and `g` agree a.e. on `B_R` with an
`a`-harmonic `H¹(B_R)` function and its gradient. -/
def IsBallSolution (a : CoeffField d) (R : ℝ) (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  ∃ v : AHarmonicFunction a (euclidBall R),
    v.toH1.toFun =ᵐ[volume.restrict (euclidBall R)] u ∧
      v.toH1.grad =ᵐ[volume.restrict (euclidBall R)] g

/-- `u ∈ 𝒜(ℝ^d; a)` with weak gradient `g`: a solution on every ball. -/
def IsEntireSolution (a : CoeffField d) (u : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  ∀ R : ℝ, 0 < R → IsBallSolution a R u g

/-- `𝒜^{1+γ}(ℝ^d; a)` (`e.harmonic.coordinates`), as a set of a.e.-classes: entire
solutions with `limsup_{r→∞} r^{-(1+γ)} ‖u‖_{L̲²(B_r)} < ∞`. -/
def growthSpace (a : CoeffField d) (γ : ℝ) : Set (Vec d →ₘ[volume] ℝ) :=
  {u | (∃ g : Vec d → Vec d, IsEntireSolution a u g) ∧
    Filter.limsup (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r u)
      Filter.atTop < ⊤}

/-- The zero function is a solution on every ball. -/
theorem isBallSolution_zero (a : CoeffField d) (R : ℝ) :
    IsBallSolution a R (fun _ => 0) (fun _ => 0) :=
  ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩

/-- The zero function is an entire solution. -/
theorem isEntireSolution_zero (a : CoeffField d) :
    IsEntireSolution a (fun _ => 0) (fun _ => 0) :=
  fun R _ => isBallSolution_zero a R

theorem growth_ballL2_zero (r : ℝ) : ballL2 r (0 : Vec d → ℝ) = 0 := by
  simp [ballL2]

theorem growth_ballL2_coe_zero (r : ℝ) :
    ballL2 r (⇑(0 : Vec d →ₘ[volume] ℝ)) = 0 := by
  have h0 : (⇑(0 : Vec d →ₘ[volume] ℝ)) =ᵐ[volume] (fun _ => (0 : ℝ)) := AEEqFun.coeFn_zero
  unfold ballL2
  rw [eLpNorm_congr_ae ((ballMeasure_absolutelyContinuous r).ae_eq h0)]
  simp

/-- The zero class lies in every growth space. -/
theorem zero_mem_growthSpace (a : CoeffField d) (γ : ℝ) :
    (0 : Vec d →ₘ[volume] ℝ) ∈ growthSpace a γ := by
  have h0 : (⇑(0 : Vec d →ₘ[volume] ℝ)) =ᵐ[volume] (fun _ => (0 : ℝ)) := AEEqFun.coeFn_zero
  refine ⟨⟨fun _ => 0, fun R hR => ?_⟩, ?_⟩
  · obtain ⟨v, hv1, hv2⟩ := isBallSolution_zero a R
    exact ⟨v, hv1.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae h0)), hv2⟩
  · simp [growth_ballL2_coe_zero]

/-- Monotonicity in the growth exponent. -/
theorem growthSpace_mono (a : CoeffField d) {γ γ' : ℝ} (h : γ ≤ γ') :
    growthSpace a γ ⊆ growthSpace a γ' := by
  rintro u ⟨hsol, hlim⟩
  refine ⟨hsol, lt_of_le_of_lt ?_ hlim⟩
  refine Filter.limsup_le_limsup ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  gcongr

/-- Uniform ellipticity on every ball: the hypothesis under which solutions form a vector space. -/
def GrowthElliptic (a : CoeffField d) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (euclidBall R) a

private theorem growth_memVectorL2_grad {U : Set (Vec d)} (v : H1Function U) :
    MemVectorL2 U v.grad :=
  MeasureTheory.MemLp.of_eval fun i => v.gradMemL2 i

private theorem growth_fluxIntegrable {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : h10FluxIntegrable U F := by
  intro φ
  have hcoord : ∀ i : Fin d,
      MeasureTheory.IntegrableOn (fun x => F x i * φ.toH1Function.grad x i) U :=
    fun i => (hF.eval i).integrable_mul (φ.toH1Function.gradMemL2 i)
  have hsum : (fun x => vecDot (F x) (φ.toH1Function.grad x)) =
      fun x => ∑ i : Fin d, F x i * φ.toH1Function.grad x i := rfl
  rw [hsum]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => hcoord i

/-- Sum of `a`-harmonic functions on a ball, for elliptic `a`. -/
theorem growth_aHarmonic_add {a : CoeffField d} {R : ℝ}
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (euclidBall R) a)
    (v w : AHarmonicFunction a (euclidBall R)) :
    IsAHarmonicGradient a (euclidBall R) (v.toH1 + w.toH1).grad := by
  obtain ⟨lam, Lam, hEll⟩ := hell
  have hv := growth_fluxIntegrable
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll (growth_memVectorL2_grad v.toH1))
  have hw := growth_fluxIntegrable
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll (growth_memVectorL2_grad w.toH1))
  exact isAHarmonicGradient_add_of_integrable v.isHarmonic w.isHarmonic hv hw

theorem IsBallSolution.add {a : CoeffField d} {R : ℝ}
    (hell : ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (euclidBall R) a)
    {u₁ u₂ : Vec d → ℝ} {g₁ g₂ : Vec d → Vec d}
    (h₁ : IsBallSolution a R u₁ g₁) (h₂ : IsBallSolution a R u₂ g₂) :
    IsBallSolution a R (u₁ + u₂) (g₁ + g₂) := by
  obtain ⟨v, hv1, hv2⟩ := h₁
  obtain ⟨w, hw1, hw2⟩ := h₂
  refine ⟨⟨v.toH1 + w.toH1, growth_aHarmonic_add hell v w⟩, ?_, ?_⟩
  · filter_upwards [hv1, hw1] with x hx hy
    simp [hx, hy]
  · filter_upwards [hv2, hw2] with x hx hy
    simp [hx, hy]

theorem IsBallSolution.smul {a : CoeffField d} {R : ℝ} (c : ℝ)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : IsBallSolution a R u g) :
    IsBallSolution a R (c • u) (c • g) := by
  obtain ⟨v, hv1, hv2⟩ := h
  refine ⟨⟨c • v.toH1, isAHarmonicGradient_smul v.isHarmonic c⟩, ?_, ?_⟩
  · filter_upwards [hv1] with x hx
    simp [hx]
  · filter_upwards [hv2] with x hx
    simp [hx]

theorem IsEntireSolution.add {a : CoeffField d} (hell : GrowthElliptic a)
    {u₁ u₂ : Vec d → ℝ} {g₁ g₂ : Vec d → Vec d}
    (h₁ : IsEntireSolution a u₁ g₁) (h₂ : IsEntireSolution a u₂ g₂) :
    IsEntireSolution a (u₁ + u₂) (g₁ + g₂) :=
  fun R hR => (h₁ R hR).add (hell R hR) (h₂ R hR)

theorem IsEntireSolution.smul {a : CoeffField d} (c : ℝ)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : IsEntireSolution a u g) :
    IsEntireSolution a (c • u) (c • g) :=
  fun R hR => (h R hR).smul c

theorem growth_ballL2_add_le (r : ℝ) (u w : Vec d →ₘ[volume] ℝ) :
    ballL2 r (⇑(u + w)) ≤ ballL2 r (⇑u) + ballL2 r (⇑w) := by
  unfold ballL2
  rw [eLpNorm_congr_ae ((ballMeasure_absolutelyContinuous r).ae_eq (AEEqFun.coeFn_add u w))]
  exact eLpNorm_add_le (by norm_num)

theorem growth_ballL2_smul (r : ℝ) (c : ℝ) (u : Vec d →ₘ[volume] ℝ) :
    ballL2 r (⇑(c • u)) = ‖c‖ₑ * ballL2 r (⇑u) := by
  unfold ballL2
  rw [eLpNorm_congr_ae ((ballMeasure_absolutelyContinuous r).ae_eq (AEEqFun.coeFn_smul c u))]
  exact eLpNorm_const_smul c _ _ _

theorem growth_bound_of_limsup {f : ℝ → ℝ≥0∞}
    (h : Filter.limsup f Filter.atTop < ⊤) : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ᶠ r in Filter.atTop, f r ≤ C := by
  obtain ⟨C, hlt, hC⟩ := exists_between h
  exact ⟨C, hC, (Filter.eventually_lt_of_limsup_lt hlt).mono fun r hr => hr.le⟩

/-- The growth space is a submodule of `L⁰`, for elliptic `a`. -/
def growthSubmodule (a : CoeffField d) (γ : ℝ) (hell : GrowthElliptic a) :
    Submodule ℝ (Vec d →ₘ[volume] ℝ) where
  carrier := growthSpace a γ
  zero_mem' := zero_mem_growthSpace a γ
  add_mem' := by
    rintro u w ⟨⟨g₁, hg₁⟩, hu⟩ ⟨⟨g₂, hg₂⟩, hw⟩
    refine ⟨⟨g₁ + g₂, ?_⟩, ?_⟩
    · intro R hR
      obtain ⟨v, hv1, hv2⟩ := (hg₁.add hell hg₂) R hR
      refine ⟨v, ?_, hv2⟩
      exact hv1.trans (ae_restrict_of_ae (AEEqFun.coeFn_add u w).symm)
    · obtain ⟨C₁, hC₁, h₁⟩ := growth_bound_of_limsup hu
      obtain ⟨C₂, hC₂, h₂⟩ := growth_bound_of_limsup hw
      refine lt_of_le_of_lt (Filter.limsup_le_of_le (by isBoundedDefault)
        (a := C₁ + C₂) ?_) (ENNReal.add_lt_top.2 ⟨hC₁, hC₂⟩)
      filter_upwards [h₁, h₂] with r hr₁ hr₂
      calc ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r (⇑(u + w))
          ≤ ENNReal.ofReal (r ^ (-(1 + γ))) * (ballL2 r (⇑u) + ballL2 r (⇑w)) :=
            mul_le_mul' le_rfl (growth_ballL2_add_le r u w)
        _ = _ := mul_add _ _ _
        _ ≤ C₁ + C₂ := add_le_add hr₁ hr₂
  smul_mem' := by
    rintro c u ⟨⟨g, hg⟩, hu⟩
    refine ⟨⟨c • g, ?_⟩, ?_⟩
    · intro R hR
      obtain ⟨v, hv1, hv2⟩ := (hg.smul c) R hR
      exact ⟨v, hv1.trans (ae_restrict_of_ae (AEEqFun.coeFn_smul c u).symm), hv2⟩
    · obtain ⟨C, hC, h⟩ := growth_bound_of_limsup hu
      refine lt_of_le_of_lt (Filter.limsup_le_of_le (by isBoundedDefault)
        (a := ‖c‖ₑ * C) ?_) (ENNReal.mul_lt_top (by simp) hC)
      filter_upwards [h] with r hr
      calc ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r (⇑(c • u))
          = ‖c‖ₑ * (ENNReal.ofReal (r ^ (-(1 + γ))) * ballL2 r (⇑u)) := by
            rw [growth_ballL2_smul]; ring
        _ ≤ ‖c‖ₑ * C := mul_le_mul' le_rfl hr

@[simp] theorem mem_growthSubmodule {a : CoeffField d} {γ : ℝ} {hell : GrowthElliptic a}
    {u : Vec d →ₘ[volume] ℝ} : u ∈ growthSubmodule a γ hell ↔ u ∈ growthSpace a γ :=
  Iff.rfl

end SuperdiffusionCLT.Section6
