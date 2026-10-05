/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergy

/-!
# The `hproj` binder of `l.abstract.response.fields` supplied for the flux

The paper defines the stationary potential gradient `∇ŵ_F` of a flux `F` as the
potential part of `-F`; the `hproj` binder of
`l_LHS_term1_constFirst_of_shellData` (`WholeSpaceEnergyOrderOneB.lean`) and of
`l_LHS_term1_of_apriori` (`WholeSpaceEnergyApriori.lean`) is exactly that
definition read in the `L²` carrier `VectorL2 d P.toMeasure`.  This file
supplies the binder.

* `exists_gradHatW_neg_stationaryPotentialProjection`: the definitional core.  A
  square-integrable flux admits a representative `gradHatW` of the potential
  part of `-F`, namely `gradHatW omega = (−Π F)ᵛ` read coordinatewise as a
  `Vec d`, together with both typing binders `hGmemLp` and the projection
  equation `hproj`, each in the exact shape of the binder block of `l_LHS_term1_of_apriori`.  No
  potential theory is re-proved: the representative is *defined* to be the
  potential part, as the print does.
* `ofVec_originFlux_streamCutoff_sub_eq_sum_shellOriginForcing` and
  `memLp_originFlux_streamCutoff_sub`: the concrete flux
  `F ω = fun x => matVecMul (streamCutoff ω L' x − streamCutoff ω ℓ' x) p` with
  `p = lam • e` a scalar multiple of a unit direction is square integrable at
  the spatial origin, by the increment identity
  `finiteShellIncrement_apply_eq_streamCutoff_sub`, the finset form
  `originForcing_finiteShellIncrement` and the J3 square integrability of the
  single-shell forcings.
* `stationary_projection_bridge`: the two together, for the flux of
  `l.LHS.term1`, i.e. the complete supply of the `hproj` binder together with its
  two typing binders.

The projection is a continuous linear map, so linearity in the flux is free and
no per-shell decomposition of the response is performed here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The representative of the stationary potential projection -/

section Representative

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable [AddAction (Vec d) Omega] [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

/-- **The `hproj` binder is realized by the representative choice
`∇ŵ_F(ω) = (−Π F)(ω)ᵛ`.**  For a square-integrable flux there is a function
`gradHatW` — the coordinatewise read-out of the `L²` element
`−stationaryPotentialProjection (Fᵛ)` — that carries both neighbouring typing
binders of `l_LHS_term1_of_apriori`: `fun omega => HilbertVec.ofVec (gradHatW
omega)` is square integrable, and its `MemLp.toLp` representative equals the
negative stationary potential projection of the flux representative.

This is the direction in which the `hproj`-shaped statements all take it as a
hypothesis: they consume `gradHatW` with its projection equation, and this
theorem produces both by construction.  It is definitional, matching the
print's construction of `∇ŵ_F` as the potential part of `−F`;
the orthogonal-projection theory itself is not re-proved. -/
theorem exists_gradHatW_neg_stationaryPotentialProjection {F : Omega → Vec d}
    (hFmemLp : MemLp (fun omega => HilbertVec.ofVec (F omega)) 2 mu) :
    ∃ (gradHatW : Omega → Vec d)
      (hGmemLp : MemLp (fun omega => HilbertVec.ofVec (gradHatW omega)) 2 mu),
      (hGmemLp.toLp fun omega => HilbertVec.ofVec (gradHatW omega)) =
        -stationaryPotentialProjection (μ := mu)
          (hFmemLp.toLp fun omega => HilbertVec.ofVec (F omega)) := by
  set y : VectorL2 d mu :=
    -stationaryPotentialProjection (μ := mu)
      (hFmemLp.toLp fun omega => HilbertVec.ofVec (F omega)) with hy
  have hae : (fun omega : Omega => HilbertVec.ofVec
        (HilbertVec.toVec ((y : Omega → HilbertVec d) omega)))
      =ᵐ[mu] (fun omega : Omega => (y : Omega → HilbertVec d) omega) :=
    Filter.Eventually.of_forall fun _ => HilbertVec.ofVec_toVec _
  have hGmem : MemLp (fun omega : Omega =>
      HilbertVec.ofVec (HilbertVec.toVec ((y : Omega → HilbertVec d) omega)))
      2 mu := MemLp.ae_eq hae (Lp.memLp y)
  have hproj : MemLp.toLp (fun omega : Omega =>
      HilbertVec.ofVec (HilbertVec.toVec ((y : Omega → HilbertVec d) omega)))
      hGmem = y := by
    rw [MemLp.toLp_congr hGmem (Lp.memLp y) hae, Lp.toLp_coeFn y (Lp.memLp y)]
  exact ⟨fun omega => HilbertVec.toVec ((y : Omega → HilbertVec d) omega),
    hGmem, hproj⟩

end Representative

/-! ## The concrete flux at the spatial origin -/

section ConcreteFlux

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- The origin value of the flux `(k_{L'} − k_{ℓ'}) p` with `p = lam • e` is,
as a `HilbertVec`, `lam` times the sum of the single-shell forcings of the block
`(ℓ', L']`.  This is the pointwise form behind
`toLp_originFlux_eq_smul_sum_shellForcingL2`, with the increment identity
`finiteShellIncrement_apply_eq_streamCutoff_sub` and the finset form
`originForcing_finiteShellIncrement`. -/
theorem ofVec_originFlux_streamCutoff_sub_eq_sum_shellOriginForcing
    (S : ScaleSelection) (hnm : S.ellPrime ≤ S.LPrime)
    (e : Vec d)
    (lam : ℝ) (p : Vec d) (hp : p = lam • e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
    (omega : ShellSeq d) :
    HilbertVec.ofVec (F omega 0) =
      ∑ l ∈ Finset.Ioc S.ellPrime S.LPrime, lam • shellOriginForcing e l omega := by
  rw [hF omega]
  simp only [hp, matVecMul_smul_right, ofVec_smul, originForcing,
    ← finiteShellIncrement_apply_eq_streamCutoff_sub omega hnm 0,
    ← originForcing_finiteShellIncrement, ← Finset.smul_sum]

/-- **The concrete flux is square integrable at the spatial origin.**  For the
flux `F = (k_{L'} − k_{ℓ'}) p` of the paper with `p = lam • e` a scalar multiple
of a unit direction, the origin value `F ω 0` is, pointwise, `lam` times the sum
of the single-shell forcings `j_l e` over the block `(ℓ', L']`; each of those is
square integrable by `ShellLawJ3`, so the finite sum is.  This is the
sequence-law twin of `memLp_originForcing_blockRegLaw`, which does the same
`memLp_finsetSum` argument on the block law. -/
theorem memLp_originFlux_streamCutoff_sub (S : ScaleSelection)
    (hSorder : ScalesOrdering S) (hJ3 : ShellLawJ3 d P)
    (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1)
    (lam : ℝ) (p : Vec d) (hp : p = lam • e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p) :
    MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) 2 P.toMeasure := by
  have hnm : S.ellPrime ≤ S.LPrime := by
    have h1 := hSorder.ellPrime_lt_m
    have h2 := hSorder.m_lt_LPrime
    omega
  have hfun : (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0))
      = fun omega : ShellSeq d => ∑ l ∈ Finset.Ioc S.ellPrime S.LPrime,
        lam • shellOriginForcing e l omega := by
    funext omega
    exact ofVec_originFlux_streamCutoff_sub_eq_sum_shellOriginForcing S hnm e
      lam p hp F hF omega
  have hmem : MemLp (fun omega : ShellSeq d =>
      ∑ l ∈ Finset.Ioc S.ellPrime S.LPrime, lam • shellOriginForcing e l omega)
      2 P.toMeasure :=
    memLp_finsetSum (μ := P.toMeasure) (p := 2) (Finset.Ioc S.ellPrime S.LPrime)
      (f := fun l : ℕ => lam • shellOriginForcing e l)
      (fun l _ => (hJ3.memLp_shellOriginForcing e hunit l).const_smul lam)
  exact MemLp.ae_eq (Filter.Eventually.of_forall (congrFun hfun.symm)) hmem

end ConcreteFlux

/-! ## The `hproj` binder for the flux of `l.LHS.term1` -/

/-- **The `hproj` binder, supplied.**  For the flux
`F = (k_{L'} − k_{ℓ'}) p` of the paper with `p = lam • e` a scalar multiple of a unit
direction, the two typing binders `hFmemLp`, `hGmemLp` and the projection
equation `hproj` of the binder block of
`l_LHS_term1_constFirst_of_shellData` (`WholeSpaceEnergyOrderOneB.lean`) and of the
third `∀`-clause of `l_LHS_term1_of_apriori` (`WholeSpaceEnergyApriori.lean`) are
all realized: the flux is
square integrable at the origin by `memLp_originFlux_streamCutoff_sub`, and
`gradHatW` is the coordinatewise read-out of the negative stationary potential
projection of its representative.

The binder equation is verbatim the one of that block, and `hFmemLp` is
produced rather than consumed, so a caller of
`l_LHS_term1_constFirst_of_shellData` or `l_LHS_term1_of_apriori` can read all
three binders off this theorem.  The shell-law input is `ShellLawJ3`; the
translation invariance of the sequence law enters only through the instance
argument of `stationaryPotentialProjection`. -/
theorem stationary_projection_bridge {P : ProbabilityMeasure (ShellSeq d)}
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (hJ3 : ShellLawJ3 d P)
    (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1)
    (lam : ℝ) (p : Vec d) (hp : p = lam • e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
    [hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure] :
    ∃ (hFmemLp : MemLp (fun omega : ShellSeq d =>
          HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
      (gradHatW : ShellSeq d → Vec d)
      (hGmemLp : MemLp (fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
      (hGmemLp.toLp fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) =
        -stationaryPotentialProjection (μ := P.toMeasure)
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)) := by
  have hFmem := memLp_originFlux_streamCutoff_sub (P := P) S hSorder hJ3 e hunit
    lam p hp F hF
  obtain ⟨gradHatW, hGmemLp, hproj⟩ :=
    exists_gradHatW_neg_stationaryPotentialProjection (Omega := ShellSeq d)
      (mu := P.toMeasure) (F := fun omega => F omega 0) hFmem
  exact ⟨hFmem, gradHatW, hGmemLp, hproj⟩

end