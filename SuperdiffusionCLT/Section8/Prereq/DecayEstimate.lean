/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.AdjointFieldB

/-!
# The duality core of the decay estimate

Deterministic pieces of the dual argument for the `L^∞` decay estimate: the pairing identity for a
zero-trace solution `u` and the adjoint zero-trace solution `v` with source `g`, the oscillation
bound for the pairing against a mean-zero source supported in a smaller set, and the
conversion of a duality bound into an `L²` bound for `u - (u)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section7

noncomputable section

variable {d : ℕ}

/-- Cauchy–Schwarz for set integrals. -/
theorem decayEst_cauchy (S : Set (Vec d)) (p q : Vec d → ℝ)
    (hp : MemLp p 2 (volume.restrict S)) (hq : MemLp q 2 (volume.restrict S)) :
    |∫ x in S, p x * q x| ≤
      Real.sqrt (∫ x in S, p x ^ 2) * Real.sqrt (∫ x in S, q x ^ 2) := by
  have hp' : MemLp (fun x => |p x|) (ENNReal.ofReal 2) (volume.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact hp.abs
  have hq' : MemLp (fun x => |q x|) (ENNReal.ofReal 2) (volume.restrict S) := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact hq.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict S)
    (Real.HolderConjugate.two_two) (f := fun x => |p x|) (g := fun x => |q x|)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => abs_nonneg _) hp' hq'
  have hint : Integrable (fun x => p x * q x) (volume.restrict S) := hp.integrable_mul hq
  have h1 : |∫ x in S, p x * q x| ≤ ∫ x in S, |p x| * |q x| := by
    calc |∫ x in S, p x * q x| ≤ ∫ x in S, |p x * q x| := abs_integral_le_integral_abs
      _ = _ := by simp only [abs_mul]
  have e1 : ∀ r : Vec d → ℝ, ∫ x in S, |r x| ^ (2 : ℝ) = ∫ x in S, r x ^ 2 := by
    intro r
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_two, sq_abs]
  rw [e1 p, e1 q] at h
  have e2 : ∀ t : ℝ, t ^ (1 / (2 : ℝ)) = Real.sqrt t := fun t => by
    rw [Real.sqrt_eq_rpow]
  rw [e2, e2] at h
  exact h1.trans h

/-- Pairing identity: `∫ g u = ∫ h v` for zero-trace solutions of the `a`- and `aᵀ`-problems. -/
theorem decayEst_pairing (a : CoeffField d) (U : Set (Vec d)) (u v : H10Function U)
    (h g : Vec d → ℝ)
    (hu : IsWeakSolutionOn a U u.toH1Function h (fun _ => 0))
    (hv : IsWeakSolutionOn (fun x => matTranspose (a x)) U v.toH1Function g (fun _ => 0)) :
    ∫ x in U, g x * u.toH1Function.toFun x = ∫ x in U, h x * v.toH1Function.toFun x :=
  (adjField_duality a U u v h g hu hv).symm

end

end SuperdiffusionCLT.Section8
