/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellDilationB
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# Per-shell reduction of the stationary response energy

The stationary potential projection of the single-shell forcing on the sequence space has the same
norm as the stationary potential projection of the forcing `j ↦ j(0) e` on the one-shell carrier,
computed for the marginal law of that shell. The coordinate map is measure preserving and
translation equivariant, so the transport identity applies.

* `nv_fieldForcing`: the forcing `j ↦ j(0) e` of one shell field.
* `nv_shellEnergy`: the squared norm of its stationary potential projection for a stationary law.
* `nv_norm_sq_shellProjection_eq`: the sequence-space response energy of shell `l` is the energy
  for the marginal law of shell `l`.
* `nv_norm_sq_blockPotentialResponse_eq`: the block response energy is the sum of the marginal
  energies of the shells of the block.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- The forcing `j ↦ j(0) e` of one shell field. -/
def nv_fieldForcing (e : Vec d) (j : ShellField d) : HilbertVec d :=
  originForcing e (ShellField.forgetShell j)

theorem measurable_nv_fieldForcing (e : Vec d) : Measurable (nv_fieldForcing (d := d) e) :=
  (measurable_originForcing e).comp ShellField.measurable_forgetShell

/-- Invariance of a law under the real translations, as the stationarity class. -/
theorem nv_vaddInvariant_of_stationary (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν) :
    VAddInvariantMeasure (Vec d) (ShellField d) ν where
  measure_preimage_vadd z s hs := by
    change ν ((ShellField.translate z) ⁻¹' s) = ν s
    rw [← Measure.map_apply (ShellField.measurable_translate z) hs]
    exact congrArg (fun m : Measure (ShellField d) ↦ m s) (hν z)

/-- The energy of the stationary potential part of the forcing `j ↦ j(0) e` for a stationary law
`ν` on the one-shell carrier. -/
def nv_shellEnergy (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν) (e : Vec d)
    (hmem : MemLp (nv_fieldForcing e) 2 ν) : ℝ := by
  haveI := nv_vaddInvariant_of_stationary ν hν
  exact ‖stationaryPotentialProjection (μ := ν) (hmem.toLp (nv_fieldForcing e))‖ ^ 2

variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- Under J3 the forcing of one shell is square integrable for the marginal law of that shell. -/
theorem nv_memLp_fieldForcing_marginal (hJ3 : ShellLawJ3 d P) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (l : ℕ) :
    MemLp (nv_fieldForcing e) 2 (ShellField.shellMarginalLaw P l).toMeasure := by
  have h := hJ3.memLp_shellOriginForcing e he l
  have hmap : (ShellField.shellMarginalLaw P l).toMeasure =
      Measure.map (fun omega : ShellSeq d ↦ omega l) P.toMeasure :=
    ProbabilityMeasure.toMeasure_map _
  rw [hmap]
  exact (memLp_map_measure_iff (measurable_nv_fieldForcing e).aestronglyMeasurable
    (ShellField.measurable_shellCoordinate l).aemeasurable).mpr h

/-- The coordinate map pushes the sequence law to the marginal law of the shell. -/
theorem nv_measurePreserving_coordinate (P : ProbabilityMeasure (ℕ → ShellField d)) (l : ℕ) :
    MeasurePreserving (fun omega : ShellSeq d ↦ omega l) P.toMeasure
      (ShellField.shellMarginalLaw P l).toMeasure :=
  ⟨ShellField.measurable_shellCoordinate l, (ProbabilityMeasure.toMeasure_map _).symm⟩

theorem nv_transportL2_toLp_fieldForcing (hJ3 : ShellLawJ3 d P) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (l : ℕ) :
    transportL2 (HilbertVec d) (nv_measurePreserving_coordinate P l)
        ((nv_memLp_fieldForcing_marginal hJ3 e he l).toLp (nv_fieldForcing e)) =
      shellForcingL2 hJ3 e he l := by
  refine Lp.ext ?_
  have h1 := coeFn_transportL2 (μ := P.toMeasure) (nv_measurePreserving_coordinate P l)
    ((nv_memLp_fieldForcing_marginal hJ3 e he l).toLp (nv_fieldForcing e))
  have h2 : (((nv_memLp_fieldForcing_marginal hJ3 e he l).toLp (nv_fieldForcing e) :
        ShellField d → HilbertVec d) ∘ fun omega : ShellSeq d ↦ omega l)
      =ᵐ[P.toMeasure] nv_fieldForcing e ∘ fun omega : ShellSeq d ↦ omega l := by
    refine ae_eq_comp (nv_measurePreserving_coordinate P l).measurable.aemeasurable ?_
    rw [(nv_measurePreserving_coordinate P l).map_eq]
    exact (nv_memLp_fieldForcing_marginal hJ3 e he l).coeFn_toLp
  have h3 := (hJ3.memLp_shellOriginForcing e he l).coeFn_toLp
  filter_upwards [h1, h2, h3] with omega hh1 hh2 hh3
  simp only [Function.comp_apply] at hh1 hh2
  rw [hh1, hh2]
  exact hh3.symm

/-- **Per-shell reduction.** The sequence-space response energy of the forcing of shell `l` is the
response energy of the one-shell forcing for the marginal law of shell `l`. -/
theorem nv_norm_sq_shellProjection_eq (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (e : Vec d) (he : Book.Ch02.vecNorm e = 1) (l : ℕ) :
    letI := ShellField.vaddInvariantMeasure hPrefix hJ2
    ‖stationaryPotentialProjection (μ := P.toMeasure) (shellForcingL2 hJ3 e he l)‖ ^ 2 =
      nv_shellEnergy (ShellField.shellMarginalLaw P l).toMeasure
        (hPrefix.stationary l) e (nv_memLp_fieldForcing_marginal hJ3 e he l) := by
  have := ShellField.vaddInvariantMeasure hPrefix hJ2
  have := nv_vaddInvariant_of_stationary _ (hPrefix.stationary l)
  unfold nv_shellEnergy
  rw [← nv_transportL2_toLp_fieldForcing hJ3 e he l]
  congr 1
  exact norm_stationaryPotentialProjection_transportL2 (nv_measurePreserving_coordinate P l)
    (fun _ _ ↦ rfl) _

/-- **The block response energy is the sum of the marginal shell energies.** -/
theorem nv_norm_sq_blockPotentialResponse_eq (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (n m : ℕ) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) :
    ‖blockPotentialResponse P n m (blockRegLaw_stationary hPrefix hJ2 n m) e
        (memLp_originForcing_blockRegLaw hJ3 n m e he)‖ ^ 2 =
      ∑ l ∈ Finset.Ioc n m, nv_shellEnergy (ShellField.shellMarginalLaw P l).toMeasure
        (hPrefix.stationary l) e (nv_memLp_fieldForcing_marginal hJ3 e he l) := by
  have := ShellField.vaddInvariantMeasure hPrefix hJ2
  rw [norm_blockPotentialResponse_eq hPrefix hJ2 hJ3 n m e he,
    norm_sq_stationaryPotentialProjection_sum hJ2 hJ3 e he]
  exact Finset.sum_congr rfl fun l _ ↦ nv_norm_sq_shellProjection_eq hPrefix hJ2 hJ3 e he l

end

/-! ## Satisfiability witness -/

/-- The hypotheses of the reduction are met by the Dirac zero law in dimension two. -/
example (n m : ℕ) (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) :
    ‖blockPotentialResponse (diracZeroLaw 2) n m
        (blockRegLaw_stationary (shellLawPrefix_diracZeroLaw (by norm_num))
          shellLawJ2_diracZeroLaw n m) e
        (memLp_originForcing_blockRegLaw shellLawJ3_diracZeroLaw n m e he)‖ ^ 2 =
      ∑ l ∈ Finset.Ioc n m, nv_shellEnergy
        (ShellField.shellMarginalLaw (diracZeroLaw 2) l).toMeasure
        ((shellLawPrefix_diracZeroLaw (by norm_num)).stationary l) e
        (nv_memLp_fieldForcing_marginal shellLawJ3_diracZeroLaw e he l) :=
  nv_norm_sq_blockPotentialResponse_eq (shellLawPrefix_diracZeroLaw (by norm_num))
    shellLawJ2_diracZeroLaw shellLawJ3_diracZeroLaw n m e he

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
