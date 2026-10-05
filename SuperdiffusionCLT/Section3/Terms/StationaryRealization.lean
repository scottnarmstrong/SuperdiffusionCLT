/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.LHSSandwichInputs

/-!
# Realization of the stationary potential gradient on the cube

The LHS sandwich of `Section3/Terms/LHSSandwichInputs.lean` carries one
realization hypothesis, `hReal`: the stationary potential gradient on the cube,
together with two joint measurabilities of its sample fields and the interior
weak equation.  This module isolates the part of `hReal` that follows from the
translation structure of the sequence law.

The translation action of `Vec d` on `ShellSeq d` is jointly continuous for the
compact-open topology on shells, hence jointly measurable.  Together with the
invariance of the sequence law under translation, this makes the map
`(omega, x) ↦ ofVec (G (x +ᵥ omega))` strongly measurable on the product for
every square-integrable `G`.  That discharges the two joint measurability
conjuncts of `hReal`, for the potential gradient and for the flux, and leaves a
single analytic statement: the existence of a cube `H¹` function whose weak
gradient is the sample field and whose interior weak equation holds.

That residual statement is the named hypothesis `energyRealization` of
`hReal_of_energyRealization`, so a later module supplies only that.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal

noncomputable section

/-! ## Joint continuity of the translation action on shells -/

/-- The translation `x ↦ x + z` as a continuous self-map of `Vec d`. -/
def stationaryTranslateMap {d : ℕ} (z : Vec d) : C(Vec d, Vec d) :=
  ⟨fun x => x + z, continuous_id.add continuous_const⟩

theorem continuous_stationaryTranslateMap {d : ℕ} :
    Continuous (fun z : Vec d => stationaryTranslateMap z) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_snd.add continuous_fst

/-- The ambient shell data translated by a vector, as the explicit triple of
post-compositions with `x ↦ x + z`. -/
def stationaryAmbientTranslate {d : ℕ} (q : ShellField d × Vec d) : ShellAmbient d :=
  ((q.1.1.1).comp (stationaryTranslateMap q.2),
    ((q.1.1.2.1).comp (stationaryTranslateMap q.2),
      (q.1.1.2.2).comp (stationaryTranslateMap q.2)))

theorem continuous_stationaryAmbientTranslate {d : ℕ} :
    Continuous (fun q : ShellField d × Vec d => stationaryAmbientTranslate q) := by
  have h1 : Continuous (fun q : ShellField d × Vec d =>
      (q.1.1.1).comp (stationaryTranslateMap q.2)) :=
    ContinuousMap.continuous_comp'.comp
      ((continuous_stationaryTranslateMap.comp continuous_snd).prodMk
        ((continuous_subtype_val.comp continuous_fst).fst))
  have h2 : Continuous (fun q : ShellField d × Vec d =>
      (q.1.1.2.1).comp (stationaryTranslateMap q.2)) :=
    ContinuousMap.continuous_comp'.comp
      ((continuous_stationaryTranslateMap.comp continuous_snd).prodMk
        ((continuous_subtype_val.comp continuous_fst).snd.fst))
  have h3 : Continuous (fun q : ShellField d × Vec d =>
      (q.1.1.2.2).comp (stationaryTranslateMap q.2)) :=
    ContinuousMap.continuous_comp'.comp
      ((continuous_stationaryTranslateMap.comp continuous_snd).prodMk
        ((continuous_subtype_val.comp continuous_fst).snd.snd))
  exact h1.prodMk (h2.prodMk h3)

theorem stationaryAmbientTranslate_eq_translate {d : ℕ} (q : ShellField d × Vec d) :
    stationaryAmbientTranslate q = (ShellField.translate q.2 q.1).1 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply ContinuousMap.ext
    intro x
    simp only [stationaryAmbientTranslate, stationaryTranslateMap, ContinuousMap.comp_apply]
    exact (ShellField.translate_apply q.2 q.1 x).symm
  · apply ContinuousMap.ext
    intro x
    simp only [stationaryAmbientTranslate, stationaryTranslateMap, ContinuousMap.comp_apply]
    exact (ShellField.translate_deriv q.2 q.1 x).symm
  · apply ContinuousMap.ext
    intro x
    simp only [stationaryAmbientTranslate, stationaryTranslateMap, ContinuousMap.comp_apply]
    exact (ShellField.translate_secondDeriv q.2 q.1 x).symm

/-- The translation action on a single shell is jointly continuous in the shell
and the translating vector. -/
theorem continuous_translate_shellField_joint {d : ℕ} :
    Continuous (fun q : ShellField d × Vec d => ShellField.translate q.2 q.1) := by
  apply Continuous.subtype_mk
  exact continuous_stationaryAmbientTranslate.congr
    (fun q => (stationaryAmbientTranslate_eq_translate q))

/-! ## Joint measurability of the action on shell sequences -/

/-- The translation action on shell sequences is measurable in the pair. -/
theorem measurable_vadd_shellSeq {d : ℕ} :
    Measurable (fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1) := by
  have hEq : (fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1)
      = fun p : ShellSeq d × Vec d => fun n => ShellField.translate p.2 (p.1 n) := by
    funext p n
    rfl
  rw [hEq]
  apply Measurable.of_eval
  intro n
  have hpair : Measurable (fun p : ShellSeq d × Vec d => (p.1 n, p.2)) :=
    ((measurable_pi_apply n).comp measurable_fst).prodMk
      (measurable_snd : Measurable (fun p : ShellSeq d × Vec d => p.2))
  exact (continuous_translate_shellField_joint (d := d)).measurable.comp hpair

/-- Pushing the product of the sequence law with the normalized cube measure
along the translation action returns the sequence law. -/
theorem map_vadd_prod_eq {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure] {Q : TriadicCube d} :
    (P.toMeasure.prod (normalizedCubeMeasure Q)).map
      (fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1) = P.toMeasure := by
  ext s hs
  rw [Measure.map_apply (measurable_vadd_shellSeq (d := d)) hs]
  have hs' : MeasurableSet
      ((fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1) ⁻¹' s) :=
    hs.preimage (measurable_vadd_shellSeq (d := d))
  rw [Measure.prod_apply_symm hs']
  have hinner : ∀ x : Vec d,
      P.toMeasure ((fun omega : ShellSeq d => (omega, x)) ⁻¹'
          ((fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1) ⁻¹' s)) =
        P.toMeasure s := by
    intro x
    have hset : (fun omega : ShellSeq d => (omega, x)) ⁻¹'
          ((fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1) ⁻¹' s) =
        (fun omega : ShellSeq d => x +ᵥ omega) ⁻¹' s := rfl
    rw [hset]
    exact VAddInvariantMeasure.measure_preimage_vadd x hs
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  simp only [hinner, lintegral_const, measure_univ, mul_one]

/-- If a vector field on shell sequences is square integrable, then its
translated evaluation on the product of the sequence law with the normalized
cube measure is strongly measurable. -/
theorem aestronglyMeasurable_vadd_of_aestronglyMeasurable {d : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {Q : TriadicCube d} {G : ShellSeq d → Vec d}
    (hG : AEStronglyMeasurable (fun omega => HilbertVec.ofVec (G omega)) P.toMeasure) :
    AEStronglyMeasurable (fun p : ShellSeq d × Vec d => HilbertVec.ofVec (G (p.2 +ᵥ p.1)))
      (P.toMeasure.prod (normalizedCubeMeasure Q)) := by
  have hmap := map_vadd_prod_eq (P := P) (Q := Q)
  have hg : AEMeasurable (fun omega => HilbertVec.ofVec (G omega))
      (Measure.map (fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1)
        (P.toMeasure.prod (normalizedCubeMeasure Q))) := by
    rw [hmap]
    exact hG.aemeasurable
  exact (hg.comp_measurable (measurable_vadd_shellSeq (d := d))).aestronglyMeasurable

/-! ## The reduction of `hReal` to its analytic residue -/

/-- The realization block of `hReal` for a fixed field: the two joint
measurabilities are supplied here, so the remaining content is exactly the
existence of the cube `H¹` function with its weak gradient and interior
equation. -/
theorem realizationBlock_of_energyRealization {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure] {Q : TriadicCube d}
    (F : ShellSeq d → Vec d → Vec d) (gradHatW : ShellSeq d → Vec d)
    (hFmemLp : MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
    (hGmemLp : MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (energyRealization : ∃ uReal : ShellSeq d → H1Function (openCubeSet Q),
      (∀ᵐ omega ∂P.toMeasure,
        (uReal omega).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
          fun x => gradHatW (x +ᵥ omega)) ∧
      (∀ᵐ omega ∂P.toMeasure, ∀ phi : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q, vecDot ((uReal omega).grad x) (phi.toH1Function.grad x) =
          -∫ x in openCubeSet Q, vecDot (F omega x) (phi.toH1Function.grad x))) :
    ∃ uReal : ShellSeq d → H1Function (openCubeSet Q),
      (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
          HilbertVec.ofVec (gradHatW (z.2 +ᵥ z.1)))
        (P.toMeasure.prod (normalizedCubeMeasure Q))) ∧
      (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
          HilbertVec.ofVec (F (z.2 +ᵥ z.1) 0))
        (P.toMeasure.prod (normalizedCubeMeasure Q))) ∧
      (∀ᵐ omega ∂P.toMeasure,
        (uReal omega).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
          fun x => gradHatW (x +ᵥ omega)) ∧
      (∀ᵐ omega ∂P.toMeasure, ∀ phi : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q, vecDot ((uReal omega).grad x) (phi.toH1Function.grad x) =
          -∫ x in openCubeSet Q, vecDot (F omega x) (phi.toH1Function.grad x)) := by
  obtain ⟨uReal, hgrad, hueq⟩ := energyRealization
  refine ⟨uReal,
    aestronglyMeasurable_vadd_of_aestronglyMeasurable (P := P) (Q := Q) (G := gradHatW)
      hGmemLp.aestronglyMeasurable,
    aestronglyMeasurable_vadd_of_aestronglyMeasurable (P := P) (Q := Q)
      (G := fun omega => F omega 0) hFmemLp.aestronglyMeasurable,
    hgrad, hueq⟩

/-- `hReal` with its two joint measurability conjuncts discharged: the only
remaining input is the analytic realization statement `energyRealization`,
which produces the cube `H¹` function with its weak gradient identity and its
interior weak equation. -/
theorem hReal_of_energyRealization (d : ℕ) [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d))
    (hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure)
    (S : ScaleSelection) (F : ShellSeq d → Vec d → Vec d)
    (energyRealization : ∀ (gradHatW : ShellSeq d → Vec d)
        (hFmemLp : MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
        (hGmemLp : MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
      (hGmemLp.toLp (fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega))) =
        -@stationaryPotentialProjection d (ShellSeq d) _ P.toMeasure _ _ hInv
          (hFmemLp.toLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0))) →
      ∃ uReal : ShellSeq d → H1Function (openCubeSet (originCube d (S.m : ℤ))),
        (∀ᵐ omega ∂P.toMeasure,
          (uReal omega).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ)))]
            fun x => gradHatW (x +ᵥ omega)) ∧
        (∀ᵐ omega ∂P.toMeasure, ∀ phi : H10Function (openCubeSet (originCube d (S.m : ℤ))),
          ∫ x in openCubeSet (originCube d (S.m : ℤ)),
              vecDot ((uReal omega).grad x) (phi.toH1Function.grad x) =
            -∫ x in openCubeSet (originCube d (S.m : ℤ)),
              vecDot (F omega x) (phi.toH1Function.grad x))) :
    ∀ (gradHatW : ShellSeq d → Vec d)
      (hFmemLp : MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
      (hGmemLp : MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
      (hGmemLp.toLp (fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega))) =
        -@stationaryPotentialProjection d (ShellSeq d) _ P.toMeasure _ _ hInv
          (hFmemLp.toLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0))) →
      ∃ uReal : ShellSeq d → H1Function (openCubeSet (originCube d (S.m : ℤ))),
        (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
            HilbertVec.ofVec (gradHatW (z.2 +ᵥ z.1)))
          (P.toMeasure.prod (normalizedCubeMeasure (originCube d (S.m : ℤ))))) ∧
        (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
            HilbertVec.ofVec (F (z.2 +ᵥ z.1) 0))
          (P.toMeasure.prod (normalizedCubeMeasure (originCube d (S.m : ℤ))))) ∧
        (∀ᵐ omega ∂P.toMeasure,
          (uReal omega).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ)))]
            fun x => gradHatW (x +ᵥ omega)) ∧
        (∀ᵐ omega ∂P.toMeasure, ∀ phi : H10Function (openCubeSet (originCube d (S.m : ℤ))),
          ∫ x in openCubeSet (originCube d (S.m : ℤ)),
              vecDot ((uReal omega).grad x) (phi.toH1Function.grad x) =
            -∫ x in openCubeSet (originCube d (S.m : ℤ)),
              vecDot (F omega x) (phi.toH1Function.grad x)) := by
  intro gradHatW hFmemLp hGmemLp hproj
  have := hInv
  exact realizationBlock_of_energyRealization (P := P) (Q := originCube d (S.m : ℤ))
    F gradHatW hFmemLp hGmemLp (energyRealization gradHatW hFmemLp hGmemLp hproj)

end

end SuperdiffusionCLT.Section3.Terms
