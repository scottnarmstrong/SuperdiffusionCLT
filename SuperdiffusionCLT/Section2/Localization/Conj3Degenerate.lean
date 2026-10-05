/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3Hgrad
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain

/-!
# The minimizers clause at the degenerate scale `m = L`

`Frozen.Section2.cutoff_localization` quantifies its third conjunct
`e.localization.minimizers` over every `m ≤ L` with `n ≤ m ≤ L`, so the
degenerate scale `m = L` is admissible.  At `m = L` the finite shell increment
over the empty interval `Finset.Ioc L L` vanishes, so its volume average
vanishes and the two coefficient fields compared by the clause coincide: the
volume-average-centered level-`L` field `â = a_L - (k_L - k_L)_U` is the
level-`L` cutoff field `a_L` (`centeredPairField_selfCoincident`).

The clause is nevertheless true there.  Its two maximizer premises are then two
maximizer statements for one response functional, so the Chapter 2 almost
everywhere gradient uniqueness
`Book.Ch02.sameGradientAE_of_isResponseMaximizer` makes `∇u = ∇v` almost
everywhere on `U` and the left side `⨍_U ‖∇u − ∇v‖²` is zero.  The right side
is zero as well: the `L^∞(cu_n)` window is the supremum of
`matrixDerivativeNorm` over the empty shell interval `(L, L]`, whose only value
is `matrixDerivativeNorm 0 = 0`.  The inequality is therefore `0 ≤ 0`
at `m = L`, and it holds for every constant `C`, with no hypothesis beyond the
binders of the statement and the degenerate-scale equation `m = L`.

## Main results

* `cutoffLocalizationConjunct3_selfCoincident`: the conjunct 3
  conclusion at `m = L`, verbatim, with the binders of the statement and `m = L` as the
  only hypotheses.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Auxiliary facts at the degenerate scale -/

/-- The exact Euclidean induced norm of the zero matrix derivative vanishes:
the zero element is the value of the explicit `none` branch of the defining
supremum, and every other value is `matrixOperatorNorm (0 v) = 0`. -/
private theorem matrixDerivativeNorm_zero (d : ℕ) :
    ShellField.matrixDerivativeNorm
        (0 : ShellField.MatrixDerivative (d := d)) = 0 := by
  refine le_antisymm ?_ (ShellField.matrixDerivativeNorm_nonneg 0)
  rw [ShellField.matrixDerivativeNorm]
  refine csSup_le ⟨0, ⟨none, rfl⟩⟩ ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_refl 0
  | some v =>
      show Book.Ch02.matrixOperatorNorm
        ((0 : Vec d →L[ℝ] Mat d) v.1) ≤ 0
      rw [zero_apply, Book.Ch02.matrixOperatorNorm_zero]

/-- A maximizer statement is insensitive to replacing the coefficient field by
an equal one: the response integrand depends on the field pointwise. -/
private theorem isResponseMaximizer_congr_field {U : Set (Vec d)} {a b : CoeffField d}
    (hab : a = b) {p q : Vec d} {u : AHarmonicFunction a U}
    (h : Homogenization.IsResponseMaximizer U p q a u) :
    Homogenization.IsResponseMaximizer U p q b
      (⟨u.toH1, hab ▸ u.isHarmonic⟩ : AHarmonicFunction b U) := by
  subst hab
  simpa using h

/-! ## The third conjunct at `m = L` -/

/-- **The conjunct 3 conclusion at the degenerate scale `m = L`.**  The
statement is the third conjunct of `Frozen.Section2.cutoff_localization`
(`e.localization.minimizers`), copied verbatim, extended by the equation
`hmL' : m = L`.  Its hypothesis list is exactly that of the statement: the standing range
`0 < nu ≤ 1`,
the scales with `n ≤ m ≤ L`, the domain with its cube inclusion, the constant
`C`, the shell sequence `omega`, the loading `(p, q)`, the two maximizers `u`
and `v` with their maximizer premises.  The binders the degenerate argument
does not consume are named with a leading underscore and carry the same
types.

The proof exhibits both sides as zero.  On the left, the two coefficient fields
coincide at `m = L` (`centeredPairField_selfCoincident`), the maximizer
premises are transported across that equality, and a.e. gradient uniqueness
makes the integrand vanish a.e.; on the right, the window is the supremum of
`matrixDerivativeNorm` over the empty shell interval, hence zero, so the whole
product vanishes whatever the values of `C` and of the response scale. -/
theorem cutoffLocalizationConjunct3_selfCoincident
    (d : ℕ) (C : ℝ) (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
    (m n L : ℕ) (_hnm : n ≤ m) (_hmL : m ≤ L) (hmL' : m = L)
    (U : Homogenization.Book.Ch02.Domain d)
    (_hU : (U : Set (Homogenization.Vec d)) ⊆
        Homogenization.openCubeSet
          (Homogenization.originCube d (n : ℤ)))
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (p q : Homogenization.Vec d)
    (u : Homogenization.AHarmonicFunction
      (fun x : Homogenization.Vec d =>
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
              nu omega L).toCoeffField x -
          Homogenization.volumeAverageMat
            (U : Set (Homogenization.Vec d))
            (fun y =>
              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                omega m L y))
      (U : Set (Homogenization.Vec d)))
    (v : Homogenization.AHarmonicFunction
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
          nu omega m).toCoeffField
      (U : Set (Homogenization.Vec d)))
    (hu : ∀ w : Homogenization.AHarmonicFunction
        (fun x : Homogenization.Vec d =>
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                nu omega L).toCoeffField x -
            Homogenization.volumeAverageMat
              (U : Set (Homogenization.Vec d))
              (fun y =>
                SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                  omega m L y))
        (U : Set (Homogenization.Vec d)),
        Homogenization.volumeAverage
            (U : Set (Homogenization.Vec d))
            (Homogenization.scalarResponseIntegrand
              (U : Set (Homogenization.Vec d))
              (fun x : Homogenization.Vec d =>
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                      nu omega L).toCoeffField x -
                  Homogenization.volumeAverageMat
                    (U : Set (Homogenization.Vec d))
                    (fun y =>
                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                        omega m L y))
              p q w) ≤
          Homogenization.volumeAverage
            (U : Set (Homogenization.Vec d))
            (Homogenization.scalarResponseIntegrand
              (U : Set (Homogenization.Vec d))
              (fun x : Homogenization.Vec d =>
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                      nu omega L).toCoeffField x -
                  Homogenization.volumeAverageMat
                    (U : Set (Homogenization.Vec d))
                    (fun y =>
                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                        omega m L y))
              p q u))
    (hv : ∀ w : Homogenization.AHarmonicFunction
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
            nu omega m).toCoeffField
        (U : Set (Homogenization.Vec d)),
        Homogenization.volumeAverage
            (U : Set (Homogenization.Vec d))
            (Homogenization.scalarResponseIntegrand
              (U : Set (Homogenization.Vec d))
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                  nu omega m).toCoeffField p q w) ≤
          Homogenization.volumeAverage
            (U : Set (Homogenization.Vec d))
            (Homogenization.scalarResponseIntegrand
              (U : Set (Homogenization.Vec d))
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                  nu omega m).toCoeffField p q v)) :
    Homogenization.volumeAverage
        (U : Set (Homogenization.Vec d))
        (fun x =>
          Homogenization.vecNormSq
            (u.toH1.grad x - v.toH1.grad x)) ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          sSup
            (Set.range fun o :
                Option {x : Homogenization.Vec d //
                  x ∈ Homogenization.openCubeSet
                    (Homogenization.originCube d (n : ℤ))} =>
              match o with
              | none => 0
              | some x =>
                  SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixDerivativeNorm
                    (∑ k ∈ Finset.Ioc m L,
                      SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv
                        (omega k) x.1)) *
        (Homogenization.ResponseJ
            (U : Set (Homogenization.Vec d)) p q
            (fun x : Homogenization.Vec d =>
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                    nu omega L).toCoeffField x -
                Homogenization.volumeAverageMat
                  (U : Set (Homogenization.Vec d))
                  (fun y =>
                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                      omega m L y)) +
          Homogenization.ResponseJ
            (U : Set (Homogenization.Vec d)) p q
            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                nu omega m).toCoeffField +
          2 * Homogenization.vecDot p q) := by
  obtain rfl : L = m := hmL'.symm
  -- at `m = L` the centered field is the level-`L` cutoff field
  have hcoin : centeredPairField nu omega L L (U : Set (Vec d)) =
      (coefficientCutoff nu omega L).toCoeffField :=
    centeredPairField_selfCoincident nu omega L (U : Set (Vec d))
  -- both maximizer premises therefore live at the level-`L` cutoff field
  have huH : Homogenization.IsAHarmonicGradient
      (coefficientCutoff nu omega L).toCoeffField (U : Set (Vec d)) u.toH1.grad :=
    Eq.mp (congrArg (fun a : CoeffField d =>
      Homogenization.IsAHarmonicGradient a (U : Set (Vec d)) u.toH1.grad) hcoin)
      u.isHarmonic
  let uL : AHarmonicFunction (coefficientCutoff nu omega L).toCoeffField
      (U : Set (Vec d)) :=
    ⟨u.toH1, huH⟩
  have huL : Homogenization.IsResponseMaximizer (U : Set (Vec d)) p q
      (coefficientCutoff nu omega L).toCoeffField uL :=
    isResponseMaximizer_congr_field hcoin hu
  have huC : Book.Ch02.IsResponseMaximizer U
      (SuperdiffusionCLT.Section2.Annealed.cutoffDomainCoeffOn U hnu omega L)
      p q uL := huL
  have hvC : Book.Ch02.IsResponseMaximizer U
      (SuperdiffusionCLT.Section2.Annealed.cutoffDomainCoeffOn U hnu omega L)
      p q v := hv
  -- a.e. gradient uniqueness of the two maximizers of one functional
  have hgrad : u.toH1.grad =ᵐ[volumeMeasureOn (U : Set (Vec d))] v.toH1.grad :=
    Book.Ch02.sameGradientAE_of_isResponseMaximizer huC hvC
  have hzero : (fun x : Vec d => vecNormSq (u.toH1.grad x - v.toH1.grad x))
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] 0 := by
    filter_upwards [hgrad] with x hx
    rw [hx, sub_self]
    simp [vecNormSq, vecDot]
  have hLHS : Homogenization.volumeAverage
      (U : Set (Homogenization.Vec d))
      (fun x => Homogenization.vecNormSq (u.toH1.grad x - v.toH1.grad x)) = 0 := by
    rw [volumeAverage, MeasureTheory.integral_eq_zero_of_ae hzero, mul_zero]
  -- the `L^∞(cu_n)` window is the supremum over the empty shell interval
  have hsum : ∀ x : Homogenization.Vec d,
      (∑ k ∈ Finset.Ioc L L,
        SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv (omega k) x) = 0 := by
    intro x
    simp
  have hval : ∀ o : Option {x : Homogenization.Vec d //
        x ∈ Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))},
      (match o with
        | none => 0
        | some x =>
            SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixDerivativeNorm
              (∑ k ∈ Finset.Ioc L L,
                SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv
                  (omega k) x.1)) = 0 := by
    intro o
    cases o with
    | none => rfl
    | some x =>
        show SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixDerivativeNorm
          (∑ k ∈ Finset.Ioc L L,
            SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv
              (omega k) x.1) = 0
        rw [hsum x.1, matrixDerivativeNorm_zero]
  have hW : sSup
        (Set.range fun o :
            Option {x : Homogenization.Vec d //
              x ∈ Homogenization.openCubeSet
                (Homogenization.originCube d (n : ℤ))} =>
          match o with
          | none => 0
          | some x =>
              SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixDerivativeNorm
                (∑ k ∈ Finset.Ioc L L,
                  SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv
                    (omega k) x.1)) = 0 := by
    have hbdd : BddAbove
        (Set.range fun o :
            Option {x : Homogenization.Vec d //
              x ∈ Homogenization.openCubeSet
                (Homogenization.originCube d (n : ℤ))} =>
          match o with
          | none => 0
          | some x =>
              SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixDerivativeNorm
                (∑ k ∈ Finset.Ioc L L,
                  SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv
                    (omega k) x.1)) :=
      ⟨0, by rintro r ⟨o, rfl⟩; exact le_of_eq (hval o)⟩
    refine le_antisymm ?_ (le_csSup hbdd ⟨none, rfl⟩)
    exact csSup_le ⟨0, ⟨none, rfl⟩⟩ (by rintro r ⟨o, rfl⟩; exact le_of_eq (hval o))
  rw [hLHS, hW]
  simp

end

end SuperdiffusionCLT.Section2.Localization
