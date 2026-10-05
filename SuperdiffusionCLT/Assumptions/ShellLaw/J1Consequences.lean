/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.RegCoeffField.SliceMeasurability
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1

/-!
# Finite-family independence from the marginal J1 range of dependence

The assumption `ShellLawJ1` supplies only *pairwise* independence of the
local integral sigma-fields of two separated read regions. This module upgrades
it to mutual independence of an arbitrary finite family of pairwise separated
read regions, by applying the pairwise statement to one region and the
union of the remaining ones.

## Main definitions

* `ShellField.AreShellSeparated`: the exact J1 separation relation at shell `n`.

## Main results

* `ShellField.lihLocalSigma_mono`: the local integral sigma-field grows with its
  read region.
* `ShellLawJ1.iIndep_lihLocalSigma`: mutual independence of the local integral
  sigma-fields of a pairwise separated family, under the shell-`n` marginal law.
* `ShellLawJ1.iIndepFun_marginal`: the observable form of that statement.
* `ShellLawJ1.iIndepFun_shellCoordinate`: the same family read through the
  shell-`n` coordinate of the canonical sequence law.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

namespace ShellField

/-- The exact separation relation used by the marginal J1 assumption at
shell `n`: every point of `U` and every point of `V` are at Euclidean distance
at least `3 ^ n * sqrt d`, non-strictly. -/
def AreShellSeparated (n : ℕ) (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
    (3 : ℝ) ^ n * Real.sqrt (d : ℝ) ≤ vecNorm (x - y)

/-- The integral-generated local sigma-field, pulled back to shell fields, is
monotone in the read region: enlarging the region adds test observables. -/
theorem lihLocalSigma_mono {U V : Set (Vec d)} (hUV : U ⊆ V) :
    lihLocalSigma U ≤ lihLocalSigma V :=
  MeasurableSpace.comap_mono (Homogenization.localSigmaR_mono hUV)

/-- Separation from every member of a finite family gives separation from the
union of that family. -/
theorem areShellSeparated_biUnion_right {ι : Type*} {n : ℕ} {U : Set (Vec d)}
    {V : ι → Set (Vec d)} {s : Finset ι}
    (h : ∀ i ∈ s, AreShellSeparated n U (V i)) :
    AreShellSeparated n U (⋃ i ∈ s, V i) := by
  intro x y hx hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨i, hi, hyi⟩ := hy
  exact h i hi hx hyi

/-- An event read by finitely many local integral sigma-fields is read by the
local integral sigma-field of the union of their regions. -/
theorem measurableSet_biInter_lihLocalSigma_biUnion {ι : Type*}
    {U : ι → Set (Vec d)} {f : ι → Set (ShellField d)} {s : Finset ι}
    (hf : ∀ i ∈ s, @MeasurableSet (ShellField d) (lihLocalSigma (U i)) (f i)) :
    @MeasurableSet (ShellField d) (lihLocalSigma (⋃ i ∈ s, U i))
      (⋂ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hsubset_i : U i ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp only [Set.mem_iUnion, Finset.mem_insert]
        exact ⟨i, Or.inl rfl, hx⟩
      have hsubset_s : (⋃ j ∈ s, U j) ⊆ ⋃ j ∈ insert i s, U j := by
        intro x hx
        simp only [Set.mem_iUnion, Finset.mem_insert] at hx ⊢
        obtain ⟨j, hj, hxj⟩ := hx
        exact ⟨j, Or.inr hj, hxj⟩
      have hi_meas :
          @MeasurableSet (ShellField d)
            (lihLocalSigma (⋃ j ∈ insert i s, U j)) (f i) :=
        lihLocalSigma_mono hsubset_i (f i) (hf i (Finset.mem_insert_self i s))
      have hs_meas :
          @MeasurableSet (ShellField d)
            (lihLocalSigma (⋃ j ∈ insert i s, U j)) (⋂ j ∈ s, f j) :=
        lihLocalSigma_mono hsubset_s (⋂ j ∈ s, f j)
          (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.set_biInter_insert] using hi_meas.inter hs_meas

end ShellField

end

end SuperdiffusionCLT.Frozen.Assumptions

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- Mutual independence of the local integral sigma-fields of a finite family
of pairwise separated measurable read regions, under the shell-`n` marginal
law. Only the pairwise J1 statement is used. -/
theorem iIndep_lihLocalSigma {ι : Type*} (hJ1 : ShellLawJ1 d P) (n : ℕ)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j ↦ ShellField.AreShellSeparated n (U i) (U j)) :
    iIndep (fun i ↦ ShellField.lihLocalSigma (U i))
      (ShellField.shellMarginalLaw P n).toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ ↦ hU j
      have hsep_union :
          ShellField.AreShellSeparated n (U i) (⋃ j ∈ s, U j) := by
        refine ShellField.areShellSeparated_biUnion_right
          (U := U i) (V := U) ?_
        intro j hj
        exact hsep (by
          intro hij
          exact hi (hij ▸ hj))
      have hs_meas :
          @MeasurableSet (ShellField d)
            (ShellField.lihLocalSigma (⋃ j ∈ s, U j)) (⋂ j ∈ s, f j) :=
        ShellField.measurableSet_biInter_lihLocalSigma_biUnion (U := U)
          (f := f) (s := s) fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
      have h_inter :
          (ShellField.shellMarginalLaw P n).toMeasure (f i ∩ ⋂ j ∈ s, f j) =
            (ShellField.shellMarginalLaw P n).toMeasure (f i) *
              (ShellField.shellMarginalLaw P n).toMeasure (⋂ j ∈ s, f j) :=
        (Indep_iff _ _ _).1
          (hJ1.range_dependence n (U i) (⋃ j ∈ s, U j) (hU i) hUnion
            hsep_union)
          (f i) (⋂ j ∈ s, f j) (hf i (Finset.mem_insert_self i s)) hs_meas
      calc
        (ShellField.shellMarginalLaw P n).toMeasure (⋂ j ∈ insert i s, f j) =
            (ShellField.shellMarginalLaw P n).toMeasure
              (f i ∩ ⋂ j ∈ s, f j) := by
          rw [Finset.set_biInter_insert]
        _ = (ShellField.shellMarginalLaw P n).toMeasure (f i) *
              (ShellField.shellMarginalLaw P n).toMeasure (⋂ j ∈ s, f j) :=
          h_inter
        _ = (ShellField.shellMarginalLaw P n).toMeasure (f i) *
              ∏ j ∈ s, (ShellField.shellMarginalLaw P n).toMeasure (f j) := by
          rw [ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]
        _ = ∏ j ∈ insert i s,
              (ShellField.shellMarginalLaw P n).toMeasure (f j) := by
          rw [Finset.prod_insert hi]

/-- Observables that are measurable for the local integral sigma-fields of a
pairwise separated family are mutually independent under the shell-`n` marginal
law. -/
theorem iIndepFun_marginal {ι : Type*} {beta : ι → Type*}
    [∀ i, MeasurableSpace (beta i)] (hJ1 : ShellLawJ1 d P) (n : ℕ)
    {U : ι → Set (Vec d)} {X : ∀ i, ShellField d → beta i}
    (hU : ∀ i, MeasurableSet (U i))
    (hX : ∀ i, @Measurable (ShellField d) (beta i)
      (ShellField.lihLocalSigma (U i)) inferInstance (X i))
    (hsep : Pairwise fun i j ↦ ShellField.AreShellSeparated n (U i) (U j)) :
    iIndepFun X (ShellField.shellMarginalLaw P n).toMeasure := by
  classical
  rw [iIndepFun_iff_iIndep, iIndep_iff]
  intro s f hf
  exact (iIndep_iff (fun i ↦ ShellField.lihLocalSigma (U i)) _).1
    (iIndep_lihLocalSigma hJ1 n hU hsep) s
    fun i hi ↦ (Measurable.comap_le (hX i)) (f i) (hf i hi)

/-- The same finite family read through the shell-`n` coordinate of the
canonical sequence law. -/
theorem iIndepFun_shellCoordinate {ι : Type*} {beta : ι → Type*}
    [∀ i, MeasurableSpace (beta i)] (hJ1 : ShellLawJ1 d P) (n : ℕ)
    {U : ι → Set (Vec d)} {X : ∀ i, ShellField d → beta i}
    (hU : ∀ i, MeasurableSet (U i))
    (hX : ∀ i, @Measurable (ShellField d) (beta i)
      (ShellField.lihLocalSigma (U i)) inferInstance (X i))
    (hsep : Pairwise fun i j ↦ ShellField.AreShellSeparated n (U i) (U j)) :
    iIndepFun (fun (i : ι) (omega : ℕ → ShellField d) ↦ X i (omega n))
      P.toMeasure := by
  classical
  have hXmeas : ∀ i, Measurable (X i) := fun i ↦
    (hX i).mono (ShellField.lihLocalSigma_le_borel (U i)) le_rfl
  have hmarginal := iIndepFun_marginal hJ1 n hU hX hsep
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hmarginal ⊢
  intro S sets hsets
  have hcoord : Measurable (fun omega : ℕ → ShellField d ↦ omega n) :=
    ShellField.measurable_shellCoordinate n
  have hmap : (ShellField.shellMarginalLaw P n).toMeasure =
      Measure.map (fun omega : ℕ → ShellField d ↦ omega n) P.toMeasure := rfl
  have hpre : ∀ i, (fun omega : ℕ → ShellField d ↦ X i (omega n)) ⁻¹' sets i =
      (fun omega : ℕ → ShellField d ↦ omega n) ⁻¹' (X i ⁻¹' sets i) := fun _ ↦ rfl
  have hmeasInter : MeasurableSet (⋂ i ∈ S, X i ⁻¹' sets i) :=
    S.measurableSet_biInter fun i hi ↦ (hXmeas i) (hsets i hi)
  have hleft : P.toMeasure (⋂ i ∈ S,
        (fun omega : ℕ → ShellField d ↦ X i (omega n)) ⁻¹' sets i) =
      (ShellField.shellMarginalLaw P n).toMeasure (⋂ i ∈ S, X i ⁻¹' sets i) := by
    rw [hmap, Measure.map_apply hcoord hmeasInter]
    simp only [hpre, Set.preimage_iInter]
  have hright : ∀ i ∈ S, P.toMeasure
        ((fun omega : ℕ → ShellField d ↦ X i (omega n)) ⁻¹' sets i) =
      (ShellField.shellMarginalLaw P n).toMeasure (X i ⁻¹' sets i) := by
    intro i hi
    rw [hmap, Measure.map_apply hcoord ((hXmeas i) (hsets i hi)), hpre i]
  rw [hleft, hmarginal S hsets]
  exact Finset.prod_congr rfl fun i hi ↦ (hright i hi).symm

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1
