/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment

/-!
# The `k_L - k_ell` `L²(cu_m)` moment bound (`l.new.mixing.parameterized#kL-kell-L2-bound`)

The printed statement (`l.new.mixing.parameterized#kL-kell-L2-bound`) is:
"By `e.kmn.bounds` with `p=2`
and the bound `L-ell≤(L-m)_++CKlogL`, `‖k_L-k_ell‖²_{L2(cu_m)} ≤
O_{Gamma_1}(C((L-m)_++KlogL))`."

This file proves the RAW form (`newMixParam_kLkEllMomentBoundRaw`), before the
scale-construction gap comparison `L - ell ≤ (L-m)_+ + CK log L` (from the scale construction)
converts the amplitude `L - ell` to the printed `(L-m)_+ + K log L`
shape: `e.kmn.bounds` at `p = 2` (`isBigO_gammaSigma_finiteShellIncrementPthMoment`
from the stream estimates of `Section2`, applied with its own
`n := ell`, `m := L`) directly gives the `Γ₁` tail bound on
`⨍_{cu_m}|(k_L-k_ell)(x)|² dx` at amplitude `C² (L-ell)`. The `ell = L` case
(the `ℓ = L` branch of the scale construction) is handled by the trivial zero
witness, since `finiteShellIncrement omega ell ell = 0` (an empty `Finset.Ioc`
sum).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- Abstract measurability transport for `Measurable.comp measurable_swap`,
kept generic in `f` so the elaborator never has to unfold a concrete
`matrixOperatorNorm (finiteShellIncrement ⋯)` term while checking the
composite's type (a bare inline `.comp measurable_swap` at the concrete type
times out at `whnf`). -/
private theorem newMixParam_swapHelper {Omega : Type*} [MeasurableSpace Omega]
    {f : Vec d → Omega → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun q : Omega × Vec d => f q.2 q.1) :=
  hf.comp measurable_swap

/-- Abstract measurability of a normalized volume average of a jointly
measurable family, kept generic in `f` for the same elaboration reason as
`newMixParam_swapHelper`. -/
private theorem newMixParam_volumeAverageMeasurableHelper {Omega : Type*}
    [MeasurableSpace Omega] {U : Set (Vec d)} {f : Vec d → Omega → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun omega : Omega => Homogenization.volumeAverage U (fun x => f x omega)) := by
  have hswap := newMixParam_swapHelper hf
  have hZ0m : Measurable (fun omega : Omega => ∫ x, f x omega ∂(volume.restrict U)) :=
    hswap.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun omega : Omega => Homogenization.volumeAverage U (fun x => f x omega)) =
      fun omega => (MeasureTheory.volume U).toReal⁻¹ * ∫ x, f x omega ∂(volume.restrict U) := by
    funext omega
    rfl
  rw [heq]
  exact hZ0m.const_mul _

/-- The raw `k_L - k_ell` `L²(cu_m)` moment bound, `e.kmn.bounds` at `p = 2`
(applied with `n := ell`, `m := L`), read over the domain
`cu_m` (`Q := originCube d (m : ℤ)`), in the amplitude `L - ell` (before the
scale-construction gap comparison converts it to `(L-m)_+ + K log L`).
Covers `ell = L` (the `ℓ = L` scale-construction branch) with the trivial
zero witness. -/
theorem newMixParam_kLkEllMomentBoundRaw
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (ell L m : ℕ) (hellL : ell ≤ L) :
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1) X
        (finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) * ((L : ℝ) - (ell : ℝ))) ∧
      ∀ omega : ShellSeq d,
        Homogenization.volumeAverage (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
            (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ)) ≤
          X omega := by
  have hYmeas : Measurable (Function.uncurry
      (fun (x : Vec d) (omega : ShellSeq d) =>
        matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))) :=
    measurable_uncurry_matrixOperatorNorm_rpow_finiteShellIncrement ell L
      (by norm_num : (0 : ℝ) ≤ 2)
  have hXmeas : Measurable (fun omega =>
      Homogenization.volumeAverage (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2 : ℝ))) :=
    newMixParam_volumeAverageMeasurableHelper hYmeas
  rcases eq_or_lt_of_le hellL with heqEll | hlt
  · refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
    · have hzero : finiteShellIncrementPthMomentConst d 2 ^ (2 : ℝ) * ((L : ℝ) - (ell : ℝ)) = 0 := by
        have hLE : (L : ℝ) - (ell : ℝ) = 0 := by rw [heqEll]; ring
        rw [hLE]; ring
      rw [hzero]
      intro t ht
      have hset : Homogenization.IndependentSums.upperTailEvent
          (fun omega : ShellSeq d => |(fun (_ : ShellSeq d) => (0:ℝ)) omega|) (0 * t) =
          (∅ : Set (ShellSeq d)) := by
        ext omega
        simp [Homogenization.IndependentSums.upperTailEvent]
      show P.toMeasure.real (Homogenization.IndependentSums.upperTailEvent
          (fun omega => |(fun (_ : ShellSeq d) => (0:ℝ)) omega|) (0 * t)) ≤
        (Homogenization.IndependentSums.gammaSigma 1 t)⁻¹
      rw [hset]
      simp only [measureReal_empty]
      exact inv_nonneg.mpr (Real.exp_pos _).le
    · intro omega
      have hzeroInc : finiteShellIncrement omega ell L = 0 := by
        have hLeqEll : L = ell := heqEll.symm
        rw [hLeqEll]
        unfold finiteShellIncrement
        simp
      have hquant : Homogenization.volumeAverage
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2:ℝ)) = 0 := by
        have hfun : (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2:ℝ)) =
            fun (_ : Vec d) => (0:ℝ) := by
          funext x
          rw [hzeroInc]
          simp
        rw [hfun]
        simp [Homogenization.volumeAverage]
      rw [hquant]
  · refine ⟨fun omega =>
        Homogenization.volumeAverage (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
          (fun x => matrixOperatorNorm (finiteShellIncrement omega ell L x) ^ (2:ℝ)),
        hXmeas, ?_, ?_⟩
    · have hraw := isBigO_gammaSigma_finiteShellIncrementPthMoment (P := P) hPrefix hJ2 hJ3 hJ4
        (p := 2) (by norm_num : (1:ℝ) ≤ 2) hlt (Homogenization.originCube d (m : ℤ))
      have hgamma : (2:ℝ) / 2 = 1 := by norm_num
      rw [hgamma] at hraw
      have hsqrt : Real.sqrt ((L - ell : ℕ) : ℝ) ^ (2:ℝ) = ((L - ell : ℕ) : ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
          Real.sq_sqrt (Nat.cast_nonneg _)]
      have hcast : ((L - ell : ℕ) : ℝ) = (L:ℝ) - (ell:ℝ) := by
        have hh := Nat.cast_sub hellL (R := ℝ)
        simpa using hh
      rw [hsqrt, hcast] at hraw
      exact hraw
    · intro omega
      exact le_refl _

end
end SuperdiffusionCLT.Section4.NewMixing
