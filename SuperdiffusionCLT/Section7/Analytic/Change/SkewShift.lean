/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShift
public import SuperdiffusionCLT.Section6.Root.CenteredRecenteredBridge

/-!
# Skew-shift invariance of weak solutions with a right-hand side

For a constant anti-symmetric matrix `S`, `IsWeakSolutionOn (a + S) U u f g` and
`IsWeakSolutionOn a U u f g` are equivalent on an open set of finite measure, as soon as the flux
`a ∇u` is square integrable (so that the two flux pairings can be split). The reason is the null
Lagrangian identity `∫ S∇u · ∇φ = 0` for `H¹₀` tests (`isSolenoidalOn_matVecMul_const_skew`).
The corollary transfers this to the centred versus the recentred field of the stream coefficient
(used throughout Section 7).

## Main results

* `SuperdiffusionCLT.Section7.isWeakSolutionOn_add_const_skew_iff`
* `SuperdiffusionCLT.Section7.isWeakSolutionOn_congr_const_skew`
* `SuperdiffusionCLT.Section7.ae_isWeakSolutionOn_centered_iff_recentered`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers

variable {d : ℕ}

/-- **Skew-shift invariance.** -/
theorem isWeakSolutionOn_add_const_skew_iff {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U)
    {S : Mat d} (hS : matTranspose S = -S) {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.grad x))) :
    IsWeakSolutionOn (fun x => a x + S) U u f g ↔ IsWeakSolutionOn a U u f g := by
  have hnull : ∀ φ : H10Function U,
      ∫ x in U, vecDot (matVecMul S (u.grad x)) (φ.toH1Function.grad x) = 0 :=
    Section2.CoarseGraining.isSolenoidalOn_matVecMul_const_skew hU hS u.isPotentialOn
  have hsplit : ∀ φ : H10Function U,
      (∫ x in U, vecDot (matVecMul (a x + S) (u.grad x)) (φ.toH1Function.grad x)) =
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) := by
    intro φ
    have h1 := Section2.CoarseGraining.h10FluxIntegrable_of_memVectorL2 hflux φ
    have h2 := Section2.CoarseGraining.h10FluxIntegrable_of_memVectorL2
      (Section2.CoarseGraining.memVectorL2_matVecMul_const S u.grad_memVectorL2) φ
    have hfun : (fun x => vecDot (matVecMul (a x + S) (u.grad x)) (φ.toH1Function.grad x)) =
        fun x => vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) +
          vecDot (matVecMul S (u.grad x)) (φ.toH1Function.grad x) := by
      funext x
      rw [add_matVecMul, vecDot_add_left]
    rw [hfun, integral_add h1 h2, hnull φ, add_zero]
  constructor
  · intro h φ
    rw [← hsplit φ]
    exact h φ
  · intro h φ
    rw [hsplit φ]
    exact h φ

/-- Skew-shift invariance for a field known to be `a + S` pointwise. -/
theorem isWeakSolutionOn_congr_const_skew {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U)
    {S : Mat d} (hS : matTranspose S = -S) {a b : CoeffField d} (hab : ∀ x, b x = a x + S)
    {u : H1Function U} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.grad x))) :
    IsWeakSolutionOn b U u f g ↔ IsWeakSolutionOn a U u f g := by
  have hb : b = fun x => a x + S := funext hab
  rw [hb]
  exact isWeakSolutionOn_add_const_skew_iff hU hS hflux

/-- **Centred versus recentred field.** Almost surely, for every `m`, a weak solution (with any
right-hand side) for the field `ν Id + centeredStreamField ω □_m` is the same as one for the
recentred field `fullCoefficientRecentered ν ω`, on every open set of finite measure and for every
`H¹` function with square-integrable recentred flux. -/
theorem ae_isWeakSolutionOn_centered_iff_recentered
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) (nu : ℝ) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ m : ℕ, ∀ {U : Set (Vec d)},
      IsOpen U → IsFiniteMeasure (volumeMeasureOn U) → ∀ (u : H1Function U) (f : Vec d → ℝ)
        (g : Vec d → Vec d),
      MemVectorL2 U (fun x => matVecMul
        (Section6.fullCoefficientRecentered nu omega x) (u.grad x)) →
      (IsWeakSolutionOn (fun x => nu • (1 : Mat d) +
          centeredStreamField omega (cubeSet (originCube d (m : ℤ))) x) U u f g ↔
        IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) U u f g) := by
  filter_upwards [Section6.ae_centered_eq_recentered_add_skew hJ3 nu] with omega hω m U hU hfin u f g hflux
  obtain ⟨K, hK, hx⟩ := hω m
  exact isWeakSolutionOn_congr_const_skew hU hK hx hflux

/-- Witness: for `S = 0` and the zero function on any open set of finite measure with the identity
coefficient, the hypotheses hold and the equivalence is the identity. -/
example (U : Set (Vec d)) [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U) :
    IsWeakSolutionOn (fun _ => (1 : Mat d) + 0) U (0 : H10Function U).toH1Function 0 0 ↔
      IsWeakSolutionOn (fun _ => (1 : Mat d)) U (0 : H10Function U).toH1Function 0 0 := by
  refine isWeakSolutionOn_add_const_skew_iff (a := fun _ => (1 : Mat d)) hU ?_ ?_
  · ext i j; simp [matTranspose]
  · have h0 : ∀ x, (0 : H10Function U).toH1Function.grad x = 0 := fun _ => rfl
    have h1 : ∀ v : Vec d, matVecMul (1 : Mat d) v = v := fun v => Matrix.one_mulVec v
    have : MemVectorL2 U (fun _ : Vec d => (0 : Vec d)) := MeasureTheory.MemLp.zero
    simpa only [h0, h1] using this

end SuperdiffusionCLT.Section7
