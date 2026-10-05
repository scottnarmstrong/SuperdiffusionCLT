/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.RestrictionSigma
public import SuperdiffusionCLT.Assumptions.ShellLaw.J1Consequences
public import SuperdiffusionCLT.Section3.HighContrast.StructuralLaw

/-!
# The range of dependence of the infrared cutoff field

The paper (Section 3, the high-contrast reduction) records the property that the
high-contrast entry theorem consumes:

> By (J1), the fields `a_m`, `k_m`, `A_m` and `f_m` are `R^d`-stationary and
> have range of dependence `sqrt d 3^m`.

The two assumptions behind it are (J1), the shell
`j_n` has range of dependence `3^n sqrt d`, and (J2), disjoint subcollections
of the shells are independent. This module turns that one-line deduction into
Lean.

## The two halves

The deduction splits into a *product-structure* half and a *lane* half.

The product-structure half is unconditional. The cutoff `a_m = nu Id + k_m`
reads only the shells `j_0, ..., j_m`, each of which has range `3^n sqrt d`
at most `3^m sqrt d`; so the two observation sets are separated at the range
of each individual shell, (J1) makes the two lanes of one shell independent,
and (J2) makes the shells independent of one another. The join over `n <= m`
of the two families of lanes is then independent. This is `indep_blockLane`,
and its consequence for the cutoff law is `indep_restrictionSigmaR_cutoffLaw`.

The lane half is the question of *which* sigma-field on shell fields plays the
role of the observation lane. The stated (J1) uses
`ShellField.lihLocalSigma U`, the pullback of `CoarseGraining`'s
integral-generated `LocalSigmaR U`; the entry theorem's
`IsRestrictionUnitRangeDependentR` uses `RestrictionSigmaR U hU`, the comap of
the canonical carrier sigma-algebra along the pointwise restriction
`a |-> 1_U a`. The two differ exactly by the point evaluations `a |-> a x` for
`x` in `U`, and the only comparison `CoarseGraining` supplies,
`localSigmaR_le_restrictionSigmaR`, runs the wrong way.

For a field with continuous values -- every shell of the shell-field carrier stores
a continuous value map -- the point evaluation at `x` is recovered from integral
tests: `j x` is the limit of the averages of `j` over the balls `B(x, s)`, and
each such average is an entry test against a test function supported in `B(x, s)`. A
transfer of the restriction lane to the integral lane therefore needs the
test functions to fit inside the observation set. Such a transfer holds for an open
observation set and fails for a set with empty interior: for a singleton no
nonzero test function is supported in it, so the integral lane is trivial while the
restriction lane still reads the point evaluation. Enlarging the observation set
to an open neighbourhood repairs the transfer but moves the two observation sets
closer, which costs separation; the shells `n < m` have the factor of three of
room that pays for this, and the top shell `n = m` does not. The transfer is
thus not available at the exactly printed range, and the way out is to change
the lane rather than the range:

* `cutoffRangeDependence_of_shellRestrictionRangeDependence` derives the exact
  obligation `CutoffRangeDependence` of
  `SuperdiffusionCLT.Section3.HighContrast.StructuralLaw` from the
  restriction-lane form of (J1), `ShellRestrictionRangeDependence`, together
  with (J2). Nothing else is missing on that route.
* `shellLawJ1_of_shellRestrictionRangeDependence` records that the
  restriction-lane assumption implies the stated (J1), so the restriction-lane
  form is the stronger of the two assumptions.

## Main definitions

* `shellLane`, `blockLane`: one shell lane on the sequence carrier and the join
  of the lanes of the shells `0, ..., m`.
  The lane carrier `shellRestrictionSigma`, its domination
  `shellRestrictionSigma_le` and the comparison
  `lihLocalSigma_le_shellRestrictionSigma` live in
  `SuperdiffusionCLT.Assumptions.ShellField.RestrictionSigma`.
* `ShellRestrictionRangeDependence`: the restriction-lane form of (J1).

## Main results

* `indep_blockLane`: the product-structure step, from (J2) and one independent
  pair of lanes per shell.
* `measurable_restrictReg_coefficientCutoff`: the restricted cutoff field is
  read by the join of the lanes of the shells `0, ..., m`.
* `indep_restrictionSigmaR_cutoffLaw`: independence of the restriction
  sigma-algebras of the cutoff law, given lanes for the shells.
* `cutoffRangeDependence_of_shellRestrictionRangeDependence`: route one, the
  only route stated.
* `shellLawJ1_of_shellRestrictionRangeDependence`: the restriction-lane
  assumption implies the stated (J1).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
  (shellRestrictionSigma shellRestrictionSigma_le
    lihLocalSigma_le_shellRestrictionSigma)
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- The canonical sigma-algebra of the shell-sequence carrier, written out so
that it cannot be captured by a lane variable in scope. -/
abbrev seqSigma (d : ℕ) : MeasurableSpace (ShellSeq d) :=
  @MeasurableSpace.pi ℕ (fun _ ↦ ShellField d) (fun _ ↦ (shellFieldMeasurableSpace d))

/-! ## Independence of two joins

The elementary lattice step: two independent blocks, each split into two
independent lanes, recombine into two independent joins. -/

/-- The pi-system of intersections of an event of `m1` with an event of `m2`. -/
private def interSystem {Omega : Type*} (m1 m2 : MeasurableSpace Omega) : Set (Set Omega) :=
  {s | ∃ a, MeasurableSet[m1] a ∧ ∃ b, MeasurableSet[m2] b ∧ s = a ∩ b}

private theorem isPiSystem_interSystem {Omega : Type*} (m1 m2 : MeasurableSpace Omega) :
    IsPiSystem (interSystem m1 m2) := by
  rintro s ⟨a, ha, b, hb, rfl⟩ t ⟨a', ha', b', hb', rfl⟩ -
  refine ⟨a ∩ a', ha.inter ha', b ∩ b', hb.inter hb', ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

private theorem generateFrom_interSystem {Omega : Type*} (m1 m2 : MeasurableSpace Omega) :
    MeasurableSpace.generateFrom (interSystem m1 m2) = m1 ⊔ m2 := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (sup_le ?_ ?_)
  · rintro s ⟨a, ha, b, hb, rfl⟩
    exact MeasurableSet.inter (le_sup_left (a := m1) (b := m2) a ha)
      (le_sup_right (a := m1) (b := m2) b hb)
  · intro s hs
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨s, hs, Set.univ, MeasurableSet.univ, (Set.inter_univ s).symm⟩
  · intro s hs
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨Set.univ, MeasurableSet.univ, s, hs, (Set.univ_inter s).symm⟩

/-- **Recombination of two independent blocks.** If the block `A1 ⊔ B1` is
independent of the block `A2 ⊔ B2`, and inside each block the two lanes are
independent, then the two joined lanes `A1 ⊔ A2` and `B1 ⊔ B2` are
independent. -/
private theorem indep_sup_sup {Omega : Type*} {m0 : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {A1 A2 B1 B2 : MeasurableSpace Omega}
    (hA1 : A1 ≤ m0) (hA2 : A2 ≤ m0) (hB1 : B1 ≤ m0) (hB2 : B2 ≤ m0)
    (hblock : Indep (A1 ⊔ B1) (A2 ⊔ B2) mu)
    (h1 : Indep A1 B1 mu) (h2 : Indep A2 B2 mu) :
    Indep (A1 ⊔ A2) (B1 ⊔ B2) mu := by
  refine IndepSets.indep (sup_le hA1 hA2) (sup_le hB1 hB2)
    (isPiSystem_interSystem A1 A2) (isPiSystem_interSystem B1 B2)
    (generateFrom_interSystem A1 A2).symm (generateFrom_interSystem B1 B2).symm ?_
  rw [IndepSets_iff]
  rintro s t ⟨a1, ha1, a2, ha2, rfl⟩ ⟨b1, hb1, b2, hb2, rfl⟩
  have hblock' := (Indep_iff _ _ mu).1 hblock
  have hrw : a1 ∩ a2 ∩ (b1 ∩ b2) = a1 ∩ b1 ∩ (a2 ∩ b2) := by
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  have hA1B1 : MeasurableSet[A1 ⊔ B1] (a1 ∩ b1) :=
    MeasurableSet.inter (le_sup_left (a := A1) (b := B1) a1 ha1)
      (le_sup_right (a := A1) (b := B1) b1 hb1)
  have hA2B2 : MeasurableSet[A2 ⊔ B2] (a2 ∩ b2) :=
    MeasurableSet.inter (le_sup_left (a := A2) (b := B2) a2 ha2)
      (le_sup_right (a := A2) (b := B2) b2 hb2)
  rw [hrw, hblock' _ _ hA1B1 hA2B2, (Indep_iff _ _ mu).1 h1 _ _ ha1 hb1,
    (Indep_iff _ _ mu).1 h2 _ _ ha2 hb2,
    hblock' _ _ (le_sup_left (a := A1) (b := B1) a1 ha1)
      (le_sup_left (a := A2) (b := B2) a2 ha2),
    hblock' _ _ (le_sup_right (a := A1) (b := B1) b1 hb1)
      (le_sup_right (a := A2) (b := B2) b2 hb2)]
  ring

/-! ## The shell lanes of the sequence carrier -/

/-- A sigma-field of shell fields, read through the shell-`n` coordinate of the
sequence carrier. -/
@[instance_reducible]
def shellLane (n : ℕ) (S : MeasurableSpace (ShellField d)) : MeasurableSpace (ShellSeq d) :=
  MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega n) S

/-- The join of the shell lanes of the shells `0, ..., m`: the information the
infrared cutoff at scale `3 ^ m` can read. -/
@[instance_reducible]
def blockLane (m : ℕ) (S : MeasurableSpace (ShellField d)) : MeasurableSpace (ShellSeq d) :=
  ⨆ n ∈ Set.Iic m, shellLane n S

theorem shellLane_le {n : ℕ} {S : MeasurableSpace (ShellField d)}
    (hS : S ≤ (shellFieldMeasurableSpace d)) :
    shellLane n S ≤ seqSigma d :=
  le_trans (MeasurableSpace.comap_mono hS)
    (ShellField.measurable_shellCoordinate (d := d) n).comap_le

theorem shellLane_le_blockLane {m n : ℕ} (hn : n ≤ m) (S : MeasurableSpace (ShellField d)) :
    shellLane n S ≤ blockLane m S :=
  le_iSup₂ (f := fun k (_ : k ∈ Set.Iic m) ↦ shellLane k S) n (Set.mem_Iic.2 hn)

theorem blockLane_le {m : ℕ} {S : MeasurableSpace (ShellField d)}
    (hS : S ≤ (shellFieldMeasurableSpace d)) :
    blockLane m S ≤ seqSigma d :=
  iSup₂_le fun _ _ ↦ shellLane_le hS

private theorem blockLane_zero (S : MeasurableSpace (ShellField d)) :
    blockLane 0 S = shellLane 0 S := by
  refine le_antisymm (iSup₂_le fun n hn ↦ ?_) (shellLane_le_blockLane (le_refl 0) S)
  have hn0 : n = 0 := Nat.le_zero.1 (Set.mem_Iic.1 hn)
  subst hn0
  exact le_rfl

private theorem blockLane_succ (m : ℕ) (S : MeasurableSpace (ShellField d)) :
    blockLane (m + 1) S = blockLane m S ⊔ shellLane (m + 1) S := by
  refine le_antisymm (iSup₂_le fun n hn ↦ ?_)
    (sup_le (iSup₂_le fun n hn ↦ shellLane_le_blockLane
      (le_trans (Set.mem_Iic.1 hn) (Nat.le_succ m)) S)
      (shellLane_le_blockLane (le_refl (m + 1)) S))
  rcases eq_or_lt_of_le (Set.mem_Iic.1 hn) with hn' | hn'
  · subst hn'
    exact le_sup_right
  · exact le_sup_of_le_left (shellLane_le_blockLane (Nat.lt_succ_iff.1 hn') S)

/-! ## The product-structure step

The lanes are supplied as an assignment `L` of a sigma-field of shell fields to
each measurable observation set; the two instances used below are the
integral lane `ShellField.lihLocalSigma` and the pointwise-restriction lane
`shellRestrictionSigma`. -/

/-- Independence of the lanes of two observation sets in one shell, read on the
sequence carrier. -/
theorem indep_shellLane_of_marginal {P : ProbabilityMeasure (ShellSeq d)}
    (L : ∀ W : Set (Vec d), MeasurableSet W → MeasurableSpace (ShellField d))
    (hL : ∀ (W : Set (Vec d)) (hW : MeasurableSet W), L W hW ≤ (shellFieldMeasurableSpace d))
    {U V : Set (Vec d)} (hU : MeasurableSet U) (hV : MeasurableSet V) (n : ℕ)
    (h : Indep (L U hU) (L V hV) (ShellField.shellMarginalLaw P n).toMeasure) :
    Indep (shellLane n (L U hU)) (shellLane n (L V hV)) P.toMeasure := by
  rw [Indep_iff]
  rintro s t ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have hcoord : Measurable (fun omega : ShellSeq d ↦ omega n) :=
    ShellField.measurable_shellCoordinate n
  have hmap : (ShellField.shellMarginalLaw P n).toMeasure =
      Measure.map (fun omega : ShellSeq d ↦ omega n) P.toMeasure := rfl
  have h' := (Indep_iff _ _ _).1 h a b ha hb
  rw [hmap, Measure.map_apply hcoord ((hL U hU a ha).inter (hL V hV b hb)),
    Measure.map_apply hcoord (hL U hU a ha), Measure.map_apply hcoord (hL V hV b hb),
    Set.preimage_inter] at h'
  exact h'

/-- **The product-structure step.** Under (J2) the shells are independent, so
lanes that are independent in every shell `n <= m` have independent joins over
`n <= m`. -/
theorem indep_blockLane {P : ProbabilityMeasure (ShellSeq d)} (hJ2 : ShellLawJ2 d P)
    (L : ∀ W : Set (Vec d), MeasurableSet W → MeasurableSpace (ShellField d))
    (hL : ∀ (W : Set (Vec d)) (hW : MeasurableSet W), L W hW ≤ (shellFieldMeasurableSpace d))
    {U V : Set (Vec d)} (hU : MeasurableSet U) (hV : MeasurableSet V) (m : ℕ)
    (hindep : ∀ n ≤ m, Indep (L U hU) (L V hV) (ShellField.shellMarginalLaw P n).toMeasure) :
    Indep (blockLane m (L U hU)) (blockLane m (L V hV)) P.toMeasure := by
  have hJ2' : iIndep (fun n : ℕ ↦ MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega n)
      (shellFieldMeasurableSpace d)) P.toMeasure :=
    (iIndepFun_iff_iIndep _ _ _).1 hJ2.independent
  have hcoordLe : ∀ n : ℕ, MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega n)
      (shellFieldMeasurableSpace d) ≤ seqSigma d :=
    fun n ↦ (ShellField.measurable_shellCoordinate (d := d) n).comap_le
  induction m with
  | zero =>
      rw [blockLane_zero, blockLane_zero]
      exact indep_shellLane_of_marginal L hL hU hV 0 (hindep 0 le_rfl)
  | succ m ih =>
      have hIH := ih fun n hn ↦ hindep n (le_trans hn (Nat.le_succ m))
      have hdisj : Disjoint (Set.Iic m) (Set.Ici (m + 1)) := by
        rw [Set.disjoint_left]
        intro n hn hn'
        have hle := le_trans (Set.mem_Ici.1 hn') (Set.mem_Iic.1 hn)
        omega
      have hsplit := indep_iSup_of_disjoint hcoordLe hJ2' hdisj
      have hleft : ∀ W : Set (Vec d), ∀ hW : MeasurableSet W, blockLane m (L W hW) ≤
          ⨆ n ∈ Set.Iic m, MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega n)
            (shellFieldMeasurableSpace d) := by
        intro W hW
        refine iSup₂_le fun n hn ↦ le_trans (MeasurableSpace.comap_mono (hL W hW)) ?_
        exact le_iSup₂ (f := fun k (_ : k ∈ Set.Iic m) ↦
          MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega k)
            (shellFieldMeasurableSpace d)) n hn
      have hright : ∀ W : Set (Vec d), ∀ hW : MeasurableSet W,
          shellLane (m + 1) (L W hW) ≤
            ⨆ n ∈ Set.Ici (m + 1), MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega n)
              (shellFieldMeasurableSpace d) := by
        intro W hW
        refine le_trans (MeasurableSpace.comap_mono (hL W hW)) ?_
        exact le_iSup₂ (f := fun k (_ : k ∈ Set.Ici (m + 1)) ↦
          MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega k)
            (shellFieldMeasurableSpace d)) (m + 1) (Set.mem_Ici.2 le_rfl)
      rw [blockLane_succ, blockLane_succ]
      exact indep_sup_sup (blockLane_le (hL U hU)) (shellLane_le (hL U hU))
        (blockLane_le (hL V hV)) (shellLane_le (hL V hV))
        (indep_of_indep_of_le_right
          (indep_of_indep_of_le_left hsplit (sup_le (hleft U hU) (hleft V hV)))
          (sup_le (hright U hU) (hright V hV)))
        hIH (indep_shellLane_of_marginal L hL hU hV (m + 1) (hindep (m + 1) le_rfl))

/-! ## The cutoff field reads only the lanes of the shells it sums -/

private theorem restrictReg_add (U : Set (Vec d)) (hU : MeasurableSet U)
    (a b : RegCoeffField d) :
    restrictReg U hU (a + b) = restrictReg U hU a + restrictReg U hU b := by
  refine RegCoeffField.ext fun x ↦ ?_
  by_cases hx : x ∈ U
  · simp only [restrictReg_apply, Set.indicator_of_mem hx, RegCoeffField.add_apply]
  · simp only [restrictReg_apply, Set.indicator_of_notMem hx, RegCoeffField.add_apply, add_zero]

private theorem restrictReg_zero (U : Set (Vec d)) (hU : MeasurableSet U) :
    restrictReg U hU (0 : RegCoeffField d) = 0 := by
  refine RegCoeffField.ext fun x ↦ ?_
  by_cases hx : x ∈ U
  · simp only [restrictReg_apply, Set.indicator_of_mem hx, RegCoeffField.zero_apply]
  · simp only [restrictReg_apply, Set.indicator_of_notMem hx, RegCoeffField.zero_apply]

private theorem restrictReg_finsetSum {iota : Type*} (U : Set (Vec d)) (hU : MeasurableSet U)
    (s : Finset iota) (g : iota → RegCoeffField d) :
    restrictReg U hU (∑ i ∈ s, g i) = ∑ i ∈ s, restrictReg U hU (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using restrictReg_zero U hU
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, restrictReg_add, ih]

/-- The restriction of the infrared cutoff `a_m = nu Id + k_m` to an observation
set is read by the join of the lanes of the shells `0, ..., m`, provided each
shell's restriction is read by the lane. -/
theorem measurable_restrictReg_coefficientCutoff {U : Set (Vec d)} (hU : MeasurableSet U)
    (nu : ℝ) (m : ℕ) {S : MeasurableSpace (ShellField d)}
    (hS : Measurable[S] fun j : ShellField d ↦ restrictReg U hU (ShellField.forgetShell j)) :
    Measurable[blockLane m S]
      fun omega : ShellSeq d ↦ restrictReg U hU (coefficientCutoff nu omega m) := by
  have hEq : (fun omega : ShellSeq d ↦ restrictReg U hU (coefficientCutoff nu omega m))
      = fun omega : ShellSeq d ↦
        restrictReg U hU (RegCoeffField.constRegCoeffField (nu • (1 : Mat d)))
          + ∑ n ∈ Finset.range (m + 1), restrictReg U hU (shellReg omega n) := by
    funext omega
    have hsplit : coefficientCutoff nu omega m
        = RegCoeffField.constRegCoeffField (nu • (1 : Mat d))
          + ∑ n ∈ Finset.range (m + 1), shellReg omega n := rfl
    rw [hsplit, restrictReg_add, restrictReg_finsetSum]
  rw [hEq]
  refine Measurable.add measurable_const (Finset.measurable_sum _ fun n hn ↦ ?_)
  have hn' : n ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have hcoord : Measurable[blockLane m S, S] fun omega : ShellSeq d ↦ omega n :=
    Measurable.of_comap_le (shellLane_le_blockLane hn' S)
  exact hS.comp hcoord

/-- Independence of two sub-sigma-algebras transfers to a pushforward law along
a measurable map, provided both are below the ambient sigma-algebra of the
target. -/
private theorem indep_map_of_comap {alpha beta : Type*} [malpha : MeasurableSpace alpha]
    [mbeta : MeasurableSpace beta] {mu : Measure alpha} {f : alpha → beta}
    (hf : Measurable f) {m₁ m₂ : MeasurableSpace beta}
    (h₁ : m₁ ≤ mbeta) (h₂ : m₂ ≤ mbeta)
    (h : @Indep alpha (m₁.comap f) (m₂.comap f) malpha mu) :
    @Indep beta m₁ m₂ mbeta (@Measure.map alpha beta malpha mbeta f mu) := by
  refine (@Indep_iff beta m₁ m₂ mbeta (@Measure.map alpha beta malpha mbeta f mu)).2 ?_
  intro s t hs ht
  have hs' : @MeasurableSet beta mbeta s := h₁ s hs
  have ht' : @MeasurableSet beta mbeta t := h₂ t ht
  have hst' : @MeasurableSet beta mbeta (s ∩ t) := hs'.inter ht'
  rw [@Measure.map_apply alpha beta malpha mbeta mu f hf (s ∩ t) hst',
    @Measure.map_apply alpha beta malpha mbeta mu f hf s hs',
    @Measure.map_apply alpha beta malpha mbeta mu f hf t ht', Set.preimage_inter]
  exact (@Indep_iff alpha (m₁.comap f) (m₂.comap f) malpha mu).1 h _ _
    ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩

/-- **The restriction sigma-algebras of the cutoff law are independent** as soon
as the shells supply independent lanes that read the restriction of a shell to
the observation set. The pointwise-restriction lane takes its hypothesis from
the restriction-lane form of (J1); the integral lane would need a lane
transfer, which is not available at the exactly printed range (see the module
header). -/
theorem indep_restrictionSigmaR_cutoffLaw {P : ProbabilityMeasure (ShellSeq d)}
    (hJ2 : ShellLawJ2 d P)
    (L : ∀ W : Set (Vec d), MeasurableSet W → MeasurableSpace (ShellField d))
    (hL : ∀ (W : Set (Vec d)) (hW : MeasurableSet W), L W hW ≤ (shellFieldMeasurableSpace d))
    {U V : Set (Vec d)} (hU : MeasurableSet U) (hV : MeasurableSet V) (nu : ℝ) (m : ℕ)
    (hLU : Measurable[L U hU] fun j : ShellField d ↦ restrictReg U hU (ShellField.forgetShell j))
    (hLV : Measurable[L V hV] fun j : ShellField d ↦ restrictReg V hV (ShellField.forgetShell j))
    (hindep : ∀ n ≤ m, Indep (L U hU) (L V hV) (ShellField.shellMarginalLaw P n).toMeasure) :
    Indep (RestrictionSigmaR U hU) (RestrictionSigmaR V hV) (cutoffLaw (d := d) nu m P) := by
  have hcomap : ∀ (W : Set (Vec d)) (hW : MeasurableSet W),
      Measurable[L W hW] (fun j : ShellField d ↦ restrictReg W hW (ShellField.forgetShell j)) →
      MeasurableSpace.comap (fun omega : ShellSeq d ↦ coefficientCutoff nu omega m)
        (RestrictionSigmaR W hW) ≤ blockLane m (L W hW) := by
    intro W hW hmeas
    have hstep := (measurable_restrictReg_coefficientCutoff hW nu m hmeas).comap_le
    rw [RestrictionSigmaR, MeasurableSpace.comap_comp]
    exact hstep
  exact indep_map_of_comap (measurable_coefficientCutoff nu m)
    (restrictionSigmaR_le U hU) (restrictionSigmaR_le V hV)
    (indep_of_indep_of_le_left
      (indep_of_indep_of_le_right (indep_blockLane hJ2 L hL hU hV m hindep)
        (hcomap V hV hLV)) (hcomap U hU hLU))

/-! ## Route one: the restriction lane at shell level

The stated (J1) is for the integral lane `ShellField.lihLocalSigma`. Its
pointwise-restriction counterpart is the following predicate, identical to the
stated assumption except for the lane; with it, the obligation
`CutoffRangeDependence` of `StructuralLaw` closes outright. -/

theorem measurable_restrictReg_forgetShell (U : Set (Vec d)) (hU : MeasurableSet U) :
    Measurable[shellRestrictionSigma U hU]
      fun j : ShellField d ↦ restrictReg U hU (ShellField.forgetShell j) :=
  Measurable.of_comap_le le_rfl

/-- **The restriction-lane form of (J1)**: the shell
`j_n` has range of dependence `3 ^ n sqrt d` for the pointwise-restriction
sigma-fields. It differs from `ShellLawJ1` only in the lane: the
separation relation, the range, and the marginal law are the same, and
`shellRestrictionSigma` replaces `ShellField.lihLocalSigma`.

The integral lane is the weaker of the two: `LocalSigmaR U` is generated by the
entry tests against test functions supported in `U`, and
`Homogenization.localSigmaR_le_restrictionSigmaR` puts it below the restriction
lane. What separates them is the point evaluations `a |-> a x` at points `x` of
`U`. On a *continuous* field those are limits of averages over balls around `x`,
hence limits of entry tests, so the two lanes carry the same information as soon
as the balls fit inside `U`. The residue is the boundary case: for `U` with
empty interior, a singleton say, the integral lane is trivial while the
restriction lane still sees `a |-> a x`, and no thickening of `U` is available
at the exactly printed range. The assumption is stronger than the
stated (J1): `shellLawJ1_of_shellRestrictionRangeDependence` below recovers
`ShellLawJ1` from it. -/
def ShellRestrictionRangeDependence (d : ℕ) (P : ProbabilityMeasure (ShellSeq d)) : Prop :=
  ∀ (n : ℕ) (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V),
    (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      (3 : ℝ) ^ n * Real.sqrt (d : ℝ) ≤ Book.Ch02.vecNorm (x - y)) →
      Indep (shellRestrictionSigma U hU) (shellRestrictionSigma V hV)
        (ShellField.shellMarginalLaw P n).toMeasure

/-- The sup metric of `Vec d` is dominated by the Euclidean norm, so sup
separation at a radius implies the Euclidean separation of (J1) at the same
radius. -/
private theorem dist_le_vecNorm (x y : Vec d) : dist x y ≤ Book.Ch02.vecNorm (x - y) := by
  have hnn : (0 : ℝ) ≤ Book.Ch02.vecNorm (x - y) := Book.Ch02.vecNorm_nonneg _
  have hsqrt : Book.Ch02.vecNorm (x - y) = Real.sqrt (vecNormSq (x - y)) := by
    rw [← Book.Ch02.vecNorm_sq_eq_vecNormSq, Real.sqrt_sq hnn]
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hnn]
  intro i
  rw [Real.norm_eq_abs, hsqrt, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  show (x - y) i ^ 2 ≤ ∑ j : Fin d, (x - y) j * (x - y) j
  calc (x - y) i ^ 2 = (x - y) i * (x - y) i := by ring
    _ ≤ ∑ j : Fin d, (x - y) j * (x - y) j :=
        Finset.single_le_sum (f := fun j : Fin d ↦ (x - y) j * (x - y) j)
          (fun j _ ↦ mul_self_nonneg ((x - y) j)) (Finset.mem_univ i)

/-- **Route one.** With the restriction-lane form of (J1) and with (J2), the
infrared cutoff has the range of dependence recorded in the module header, in the
pointwise-restriction lane that `CoarseGraining`'s high-contrast entry theorem
consumes. This is the obligation `CutoffRangeDependence` of `StructuralLaw`. -/
theorem cutoffRangeDependence_of_shellRestrictionRangeDependence
    {P : ProbabilityMeasure (ShellSeq d)} (hJ2 : ShellLawJ2 d P)
    (hJ1R : ShellRestrictionRangeDependence d P) (nu : ℝ) (m : ℕ) :
    CutoffRangeDependence nu m P := by
  intro U V hU hV hsep
  refine indep_restrictionSigmaR_cutoffLaw hJ2 shellRestrictionSigma
    (fun W hW ↦ shellRestrictionSigma_le W hW) hU hV nu m
    (measurable_restrictReg_forgetShell U hU) (measurable_restrictReg_forgetShell V hV)
    fun n hn ↦ hJ1R n U V hU hV fun x y hx hy ↦ ?_
  calc (3 : ℝ) ^ n * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ m * Real.sqrt (d : ℝ) := by
        gcongr; norm_num
    _ ≤ dist x y := hsep hx hy
    _ ≤ Book.Ch02.vecNorm (x - y) := dist_le_vecNorm x y

/-- **The restriction-lane assumption implies the stated (J1).** The
integral lane is below the restriction lane
(`lihLocalSigma_le_shellRestrictionSigma`), so independence of the restriction
lanes of two separated sets gives independence of their integral lanes. -/
theorem shellLawJ1_of_shellRestrictionRangeDependence
    {P : ProbabilityMeasure (ShellSeq d)}
    (h : ShellRestrictionRangeDependence d P) : ShellLawJ1 d P where
  range_dependence := fun n U V hU hV hsep =>
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (h n U V hU hV hsep)
        (lihLocalSigma_le_shellRestrictionSigma U hU))
      (lihLocalSigma_le_shellRestrictionSigma V hV)

end

end SuperdiffusionCLT.Section3.HighContrast
