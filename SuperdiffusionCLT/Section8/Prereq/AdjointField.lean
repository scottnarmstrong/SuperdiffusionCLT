/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.FullFieldB
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# The adjoint field: sample negation transposes the coefficient field

`ShellField.negateSequence` negates every shell, hence the stream matrix `k`; since `k` is
skew, `ν Id - k = (ν Id + k)ᵀ`. Together with `ShellLawJ4.negation` (the law is invariant under
the negation map) every almost-sure statement for `a = ν Id + k` transfers to `aᵀ`.

Every identity here holds for EVERY sample (the `tsum` junk value `0` is skew).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section6

noncomputable section

variable {d : ℕ}

theorem adjField_shellReg_negate (omega : ShellSeq d) (n : ℕ) (x : Vec d) :
    shellReg (ShellField.negateSequence omega) n x = -shellReg omega n x := by
  simp only [shellReg, ShellField.forgetShell_apply, ShellField.negateSequence_apply,
    ShellField.negate_apply]

theorem adjField_fullStreamRecentered_negate (omega : ShellSeq d) (x : Vec d) :
    fullStreamRecentered (ShellField.negateSequence omega) x =
      -fullStreamRecentered omega x := by
  simp only [fullStreamRecentered, adjField_shellReg_negate, ← tsum_neg]
  exact tsum_congr fun n => by abel

/-- The transpose of the recentered stream is its negative. -/
theorem adjField_fullStreamRecentered_transpose (omega : ShellSeq d) (x : Vec d) :
    matTranspose (fullStreamRecentered omega x) = -fullStreamRecentered omega x := by
  ext i k
  exact fullStreamRecentered_skew_entry omega x k i

/-- **(1)** Negating the sample transposes the recentered coefficient field, for every sample. -/
theorem adjField_fullCoefficientRecentered_negate (nu : ℝ) (omega : ShellSeq d) (x : Vec d) :
    fullCoefficientRecentered nu (ShellField.negateSequence omega) x =
      matTranspose (fullCoefficientRecentered nu omega x) := by
  have h := adjField_fullStreamRecentered_transpose omega x
  simp only [fullCoefficientRecentered, adjField_fullStreamRecentered_negate, matTranspose,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one] at h ⊢
  rw [h]

/-! ## Transfer -/

theorem adjField_negate_measurePreserving {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : Frozen.Assumptions.ShellLawJ4 d P) :
    MeasurePreserving (ShellField.negateSequence (d := d)) P.toMeasure P.toMeasure := by
  refine ⟨ShellField.measurable_negateSequence, ?_⟩
  have h := congrArg ProbabilityMeasure.toMeasure hJ4.negation
  simpa only [ProbabilityMeasure.toMeasure_map] using h

theorem adjField_ae_negate {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : Frozen.Assumptions.ShellLawJ4 d P) {Φ : ShellSeq d → Prop}
    (h : ∀ᵐ omega ∂P.toMeasure, Φ omega) :
    ∀ᵐ omega ∂P.toMeasure, Φ (ShellField.negateSequence omega) :=
  (adjField_negate_measurePreserving hJ4).quasiMeasurePreserving.ae h

theorem adjField_measure_preimage_negate {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : Frozen.Assumptions.ShellLawJ4 d P) {E : Set (ShellSeq d)} (hE : MeasurableSet E) :
    P.toMeasure (ShellField.negateSequence ⁻¹' E) = P.toMeasure E :=
  (adjField_negate_measurePreserving hJ4).measure_preimage hE.nullMeasurableSet

/-- **(4)** A.s. statements about the recentered field hold for its transpose. -/
theorem adjField_ae_transpose {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : Frozen.Assumptions.ShellLawJ4 d P) (nu : ℝ)
    {Ψ : (Vec d → Mat d) → Prop}
    (h : ∀ᵐ omega ∂P.toMeasure, Ψ (fullCoefficientRecentered nu omega)) :
    ∀ᵐ omega ∂P.toMeasure,
      Ψ (fun x => matTranspose (fullCoefficientRecentered nu omega x)) := by
  filter_upwards [adjField_ae_negate hJ4 h] with omega hω
  have : fullCoefficientRecentered nu (ShellField.negateSequence omega) =
      fun x => matTranspose (fullCoefficientRecentered nu omega x) :=
    funext (adjField_fullCoefficientRecentered_negate nu omega)
  rwa [this] at hω

/-- Random-scale version: `X ∘ N` has the same tail bound (same law). -/
theorem adjField_exists_scale_transpose {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : Frozen.Assumptions.ShellLawJ4 d P) (nu : ℝ)
    {Ψ : ℝ → (Vec d → Mat d) → Prop} (T : ℝ → ℝ)
    (h : ∃ X : ShellSeq d → ℝ, Measurable X ∧
      (∀ t, P.toMeasure {omega | t < X omega} ≤ ENNReal.ofReal (T t)) ∧
      ∀ᵐ omega ∂P.toMeasure, Ψ (X omega) (fullCoefficientRecentered nu omega)) :
    ∃ X' : ShellSeq d → ℝ, Measurable X' ∧
      (∀ t, P.toMeasure {omega | t < X' omega} ≤ ENNReal.ofReal (T t)) ∧
      ∀ᵐ omega ∂P.toMeasure,
        Ψ (X' omega) (fun x => matTranspose (fullCoefficientRecentered nu omega x)) := by
  obtain ⟨X, hX, hT, hΨ⟩ := h
  refine ⟨X ∘ ShellField.negateSequence, hX.comp ShellField.measurable_negateSequence, ?_, ?_⟩
  · intro t
    have hm : MeasurableSet {omega | t < X omega} := measurableSet_lt measurable_const hX
    have := adjField_measure_preimage_negate hJ4 hm
    exact (le_of_eq this).trans (hT t)
  · filter_upwards [adjField_ae_negate hJ4 hΨ] with omega hω
    have : fullCoefficientRecentered nu (ShellField.negateSequence omega) =
        fun x => matTranspose (fullCoefficientRecentered nu omega x) :=
      funext (adjField_fullCoefficientRecentered_negate nu omega)
    rwa [this] at hω

/-! ## Commutation with translations -/

/-- Satisfiability: the Dirac zero law satisfies `ShellLawJ4`, so the transfer applies. -/
example (nu : ℝ) {Ψ : (Vec d → Mat d) → Prop}
    (h : ∀ᵐ omega ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure, Ψ (fullCoefficientRecentered nu omega)) :
    ∀ᵐ omega ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      Ψ (fun x => matTranspose (fullCoefficientRecentered nu omega x)) :=
  adjField_ae_transpose (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw (d := d)) nu h

end

end SuperdiffusionCLT.Section8
