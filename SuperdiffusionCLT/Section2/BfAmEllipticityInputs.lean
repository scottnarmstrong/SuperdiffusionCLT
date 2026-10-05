/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import Homogenization.Sobolev.PotentialSolenoidalL2Realization
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery
public import Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily
public import Homogenization.Probability.RegCoeffField.SliceMeasurability

/-!
# Inputs for the ellipticity bounds of `bfA_m`

Lemma `l.bfAm.ellip` asserts in its first clause (`e.Enaught.vs.A.and.Ahom`) that
for every bounded domain `U` the rescaled coarse block matrix
`bfE_m^{-1/2} bfA_m(U) bfE_m^{-1/2}` is measurable in the sample and has
Γ₁-bounded operator norm. The second half of that clause is
`isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale`; the
measurability half needs `Homogenization.Mu` to be measurable on the bounded
domain `U`, and `CoarseGraining` supplies that only on triadic cubes.

This module supplies the general-domain inputs:

* `measurableSet_localSigmaR_aeeQuantitativeEllipticSlice_of_isOpen`: the AEE
  quantitative-slice event is `LocalSigmaR U`-measurable on every **open** `U`,
  the general-open-domain form of `CoarseGraining`'s cube-only
  `measurableSet_localSigmaR_aeeSlice`;
* `measurable_Mu_of_aeeSlice_measurable_entryTest`: `Homogenization.Mu U P a` is
  measurable in a sample of locally a.e.-uniformly elliptic fields for every
  bounded open `U` of finite volume whose localized entry-test generators are
  measurable, which is the hypothesis `hMu` of
  `measurable_blockMatrixOperatorNorm_envelopeRescale_of_measurable_Mu` on the domains of
  `Homogenization.Book.Ch02.Domain`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The AEE quantitative-slice event on an open domain -/

/-- **The AEE quantitative-slice event is `LocalSigmaR U`-measurable on every
open `U`.** `CoarseGraining` proves this only for the half-open triadic cubes
(`measurableSet_localSigmaR_aeeSlice`), reducing the slice predicate to the
a.e.-ellipticity event on the open core and then to the rational-ball
intersection `slicePart`. On an open `U` the open core is `U` itself, so the
same reduction applies verbatim; `aeeQuantitativeEllipticSlice_carrier_iff`
removes the two free measurability conjuncts of the carrier predicate. -/
theorem measurableSet_localSigmaR_aeeQuantitativeEllipticSlice_of_isOpen
    {U : Set (Vec d)} (hU : IsOpen U) (k : ℕ) :
    MeasurableSet[LocalSigmaR U]
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice U k a.toFun} := by
  set lam : ℝ := (k + 1 : ℝ)⁻¹
  set Lam : ℝ := (k + 1 : ℝ)
  have hEvent :
      {a : RegCoeffField d | AEEQuantitativeEllipticSlice U k a.toFun} =
        {a : RegCoeffField d |
          ∀ᵐ x ∂(MeasureTheory.volume.restrict U), IsEllipticMatrix lam Lam (a x)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    rw [aeeQuantitativeEllipticSlice_carrier_iff U hU.measurableSet k a]
  rw [hEvent, setOf_aeRestrict_isEllipticMatrix_eq_slicePart hU lam Lam]
  exact measurableSet_slicePart lam Lam

/-! ## The canonical AEE operator system on a general open set

`CoarseGraining` builds the canonical operator-system data only on the half-open
triadic cubes (`canonicalAEEMuOperatorSystemData`). The construction is however
independent of the cube: the correction space is always
`MuCorrectionSpaceData.ofSubmoduleClosures U`, and the coefficient operator is
the a.e.-representative operator of the slice predicate
(`AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn`), which needs only positive
`toReal` volume. We repeat the same construction on an arbitrary `U`. -/

section GeneralOpenSet

variable {d : ℕ} {U : Set (Vec d)}

/-- The canonical AEE operator-system data on one quantitative AEE slice of an
open set of positive finite volume: the closed predicate-generated correction
space together with the a.e.-representative coefficient operator of the slice. -/
noncomputable def aeemuOperatorSystemDataOfAEESlice {k : ℕ}
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    AEEMuOperatorSystemData U a.1 where
  correctionSpace := MuCorrectionSpaceData.ofSubmoduleClosures U
  coeffOperatorData :=
    AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn (U := U) (a := a.1) a.2 hvol

@[simp] theorem correctionSpace_aeemuOperatorSystemDataOfAEESlice {k : ℕ}
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (aeemuOperatorSystemDataOfAEESlice (U := U) hvol a).correctionSpace =
      MuCorrectionSpaceData.ofSubmoduleClosures U :=
  rfl

/-- **The variational `Mu` on a quantitative AEE slice is the canonical AEE
Hilbert-operator candidate.**  This is the general-open-set form of
`Homogenization.mu_eq_canonicalAEEMuCandidate`, whose proof uses no property of
the cube beyond the identification of the correction space with
`ofSubmoduleClosures`. -/
theorem mu_eq_aeemuOperatorSystemData_muCandidate
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {k : ℕ} (hvol : 0 < (MeasureTheory.volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    (P0 : BlockVec d) :
    Mu U P0 a.1 =
      ((aeemuOperatorSystemDataOfAEESlice (U := U) hvol a).toMuHilbertRealization).muCandidate
        P0 := by
  let system : AEEMuOperatorSystemData U a.1 :=
    aeemuOperatorSystemDataOfAEESlice (U := U) hvol a
  let H : MuHilbertRealization U a.1 := system.toMuHilbertRealization
  let gen : canonicalMuBlockCorrectionGeneratorSubmodule U →
      H.correctionSpace.correctionSpace.toSubmodule := fun Y =>
    canonicalMuCorrectionGeneratorEmbedding U Y
  let s : Set ℝ := Set.range fun Y : canonicalMuBlockCorrectionGeneratorSubmodule U =>
    quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U))
  have hgen_dense : DenseRange gen := by
    dsimp [gen, H, system]
    simp only [aeemuOperatorSystemDataOfAEESlice, MuCorrectionSpaceData.ofSubmoduleClosures,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
    exact denseRange_canonicalMuCorrectionGeneratorEmbedding U
  have hCandidate_sInf : H.muCandidate P0 = sInf s := by
    simpa [s] using
      H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
  have hCandidateLe :
      ∀ X : BlockState d, IsBlockMuAdmissible U P0 X →
        H.muCandidate P0 ≤ blockEnergyAverage U a.1 X := by
    intro X hX
    have hXmem : MemBlockL2 U X.eval := hX.memBlockL2_eval
    have hcorr_mem :
        toHilbertBlockL2OfBlockField (U := U) hXmem - H.constantField P0 ∈
          H.correctionSpace.correctionSpace := by
      have hsplit := hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
      rw [hsplit]
      have hcorr := hX.toCorrectionFieldData_mem_correctionSpace
      simpa [H, system, aeemuOperatorSystemDataOfAEESlice,
        MuCorrectionSpaceData.ofSubmoduleClosures,
        AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_comm] using hcorr
    have hmin :
        H.muCandidate P0 ≤
          quadraticEnergy H.energyBilin (toHilbertBlockL2OfBlockField (U := U) hXmem) :=
      H.muCandidate_le_quadraticEnergy P0
        (toHilbertBlockL2OfBlockField (U := U) hXmem) hcorr_mem
    calc
      H.muCandidate P0 ≤
          quadraticEnergy H.energyBilin (toHilbertBlockL2OfBlockField (U := U) hXmem) := hmin
      _ = blockEnergyAverage U a.1 X := by
        simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
          MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
          system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
            (X := X) hXmem
  have hBddBelow : BddBelow (muValueSet U P0 a.1) := by
    refine ⟨H.muCandidate P0, ?_⟩
    intro m hm
    rcases hm with ⟨X, hX, rfl⟩
    simpa [blockEnergyAverage] using hCandidateLe X hX
  have hCandidate_le_Mu : H.muCandidate P0 ≤ Mu U P0 a.1 := by
    apply le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    simpa [blockEnergyAverage] using hCandidateLe X hX
  have hs_subset_mu : s ⊆ muValueSet U P0 a.1 := by
    intro m hm
    rcases hm with ⟨Y, rfl⟩
    rcases Y.property with ⟨f, g, hf, hg, hY, hpot, hsol⟩
    let X : BlockState d :=
      { potential := fun x => P0.1 + f x
        flux := fun x => P0.2 + g x }
    have hAdm : IsBlockMuAdmissible U P0 X := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hf
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hpot
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hg
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hsol
    have hGen_comp :
        (gen Y : HilbertBlockL2 U) = toHilbertBlockL2OfComponents hf hg := by
      have hblock_to_hilbert :
          blockL2ToHilbertBlockL2 (U := U) (Y : BlockL2 U) =
            toHilbertBlockL2OfComponents hf hg := by
        rw [← hY]
        simp only [toBlockL2OfComponents, toHilbertBlockL2OfComponents]
        exact
          (blockL2ToHilbertBlockL2_toBlockL2
            (U := U)
            (F := blockField f g)
            (memBlockL2_blockField hf hg))
      dsimp [gen, canonicalMuCorrectionGeneratorEmbedding,
        PotentialSolenoidalL2Data.submoduleClosureToMuCorrectionSpace]
      exact hblock_to_hilbert
    have hAdmCorr :
        (hAdm.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 =
          toHilbertBlockL2OfComponents hf hg := by
      change toHilbertBlockL2OfComponents
          hAdm.potentialCorrection_memL2 hAdm.fluxCorrection_memL2 =
        toHilbertBlockL2OfComponents hf hg
      apply MeasureTheory.Lp.ext
      filter_upwards
          [coeFn_toHilbertBlockL2OfComponents (U := U)
            (f := fun x => X.potential x - P0.1)
            (g := fun x => X.flux x - P0.2)
            hAdm.potentialCorrection_memL2 hAdm.fluxCorrection_memL2,
           coeFn_toHilbertBlockL2OfComponents (U := U) (f := f) (g := g) hf hg]
        with x hleft hright
      rw [hleft, hright]
      apply HilbertBlockVec.ext
      · ext i
        simp [X, hilbertBlockField]
      · ext i
        simp [X, hilbertBlockField]
    have hsplit :
        toHilbertBlockL2OfBlockField (U := U) hAdm.memBlockL2_eval =
          H.constantField P0 + (gen Y : HilbertBlockL2 U) := by
      calc
        toHilbertBlockL2OfBlockField (U := U) hAdm.memBlockL2_eval
            = blockVecToHilbertBlockL2Const (U := U) P0 +
                (hAdm.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 :=
              hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
        _ = H.constantField P0 + (gen Y : HilbertBlockL2 U) := by
              rw [hAdmCorr, ← hGen_comp]
              simp [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
                MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
    have hEnergy :
        quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U)) =
          blockEnergyAverage U a.1 X := by
      rw [← hsplit]
      simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
          (X := X) hAdm.memBlockL2_eval
    refine ⟨X, hAdm, ?_⟩
    simpa [blockEnergyAverage] using hEnergy
  have hs_nonempty : s.Nonempty := by
    refine ⟨quadraticEnergy H.energyBilin (H.constantField P0 + (gen 0 : HilbertBlockL2 U)), ?_⟩
    exact ⟨0, rfl⟩
  have hMu_le_sInf : Mu U P0 a.1 ≤ sInf s := by
    apply le_csInf hs_nonempty
    intro m hm
    exact csInf_le hBddBelow (hs_subset_mu hm)
  have hMu_le_candidate : Mu U P0 a.1 ≤ H.muCandidate P0 := by
    calc
      Mu U P0 a.1 ≤ sInf s := hMu_le_sInf
      _ = H.muCandidate P0 := hCandidate_sInf.symm
  have hEq : Mu U P0 a.1 = H.muCandidate P0 :=
    le_antisymm hMu_le_candidate hCandidate_le_Mu
  simpa [H, system, aeemuOperatorSystemDataOfAEESlice] using hEq

/-- **The variational `Mu` is the infimum of the fixed-competitor block energies
along any dense sequence in the canonical generator submodule**, on a general
open set.  This is the general-open-set form of
`Homogenization.mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator_denseSeq`
used by the carrier measurability engine. -/
theorem mu_eq_iInf_blockEnergyAverage_aeemuGenerator_denseSeq
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {k : ℕ} (hvol : 0 < (MeasureTheory.volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    (P0 : BlockVec d)
    (ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U)
    (hξ : DenseRange ξ) :
    Mu U P0 a.1 =
      ⨅ n : ℕ,
        blockEnergyAverage U a.1
          (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
  let system : AEEMuOperatorSystemData U a.1 :=
    aeemuOperatorSystemDataOfAEESlice (U := U) hvol a
  let H : MuHilbertRealization U a.1 := system.toMuHilbertRealization
  let gen : ℕ → H.correctionSpace.correctionSpace.toSubmodule := fun n =>
    canonicalMuCorrectionGeneratorEmbedding U (ξ n)
  have hgen_dense : DenseRange gen := by
    have hEmbDense :
        DenseRange (canonicalMuCorrectionGeneratorEmbedding U) :=
      denseRange_canonicalMuCorrectionGeneratorEmbedding U
    have hEmbCont :
        Continuous (canonicalMuCorrectionGeneratorEmbedding U) :=
      continuous_canonicalMuCorrectionGeneratorEmbedding U
    have hcomp : DenseRange ((canonicalMuCorrectionGeneratorEmbedding U) ∘ ξ) :=
      DenseRange.comp hEmbDense hξ hEmbCont
    dsimp [gen, H, system]
    simp only [aeemuOperatorSystemDataOfAEESlice, MuCorrectionSpaceData.ofSubmoduleClosures,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
    exact hcomp
  have hCandidate :
      H.muCandidate P0 =
        sInf (Set.range fun n : ℕ =>
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U))) := by
    simpa using H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
  have hEnergy :
      ∀ n : ℕ,
        quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) =
          blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
    intro n
    have hsplit :
        toHilbertBlockL2OfBlockField (U := U)
            (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n)) =
          H.constantField P0 + (gen n : HilbertBlockL2 U) := by
      simpa [gen, H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 (ξ n)
    calc
      quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U))
          = quadraticEnergy H.energyBilin
              (toHilbertBlockL2OfBlockField (U := U)
                (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))) := by
            rw [hsplit]
      _ = blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
            simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
              MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
              system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                (X := canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
                (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))
  calc
    Mu U P0 a.1 = H.muCandidate P0 := by
      simpa [H, system] using mu_eq_aeemuOperatorSystemData_muCandidate (U := U) hvol a P0
    _ = ⨅ n : ℕ,
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) := by
      rw [hCandidate, sInf_range]
    _ = ⨅ n : ℕ,
          blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) :=
      iInf_congr hEnergy

/-- The dense-sequence form with `TopologicalSpace.denseSeq` on the canonical
generator submodule. -/
theorem mu_eq_iInf_blockEnergyAverage_aeemuGenerator
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {k : ℕ} (hvol : 0 < (MeasureTheory.volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a})
    (P0 : BlockVec d) :
    Mu U P0 a.1 =
      ⨅ n : ℕ,
        blockEnergyAverage U a.1
          (canonicalMuGeneratorAffineField (U := U) P0
            (TopologicalSpace.denseSeq
              (canonicalMuBlockCorrectionGeneratorSubmodule U) n)) := by
  exact mu_eq_iInf_blockEnergyAverage_aeemuGenerator_denseSeq (U := U) hvol a P0
    (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U))
    (TopologicalSpace.denseRange_denseSeq
      (canonicalMuBlockCorrectionGeneratorSubmodule U))

end GeneralOpenSet

/-! ## The general-domain carrier measurability engine -/

section CarrierEngine

/-- A nonempty open bounded convex set has strictly positive `toReal` volume. -/
theorem volume_toReal_pos_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    0 < (MeasureTheory.volume U).toReal :=
  ENNReal.toReal_pos
    (IsOpen.measure_pos MeasureTheory.volume hU.isOpen hne).ne' hU.volume_lt_top.ne

/-- **The carrier `Mu` measurability engine on a general open set.**  Given a
carrier source `A` taking values pointwise in the AEE quantitative `k`-slice of an
open set `U` of finite volume, whose localized entry-test generators are
measurable, the coarse-grained energy `ω ↦ Mu U P (A ω).toFun` is measurable.
This is the general-open-set form of
`Homogenization.measurable_Mu_comp_aeeSlice_of_measurable_entryTest`; the only
cube-specific input there is the variational identity
`Homogenization.mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator`, replaced
here by `mu_eq_iInf_blockEnergyAverage_aeemuGenerator`. -/
theorem measurable_Mu_of_aeeSlice_measurable_entryTest
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    {A : Ω → RegCoeffField d}
    (hSlice : ∀ ω, AEEQuantitativeEllipticSlice U k (A ω).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      @Measurable Ω ℝ _ _ (fun ω => entryTestR i j φ (A ω)))
    (P : BlockVec d) :
    Measurable (fun ω => Mu U P (A ω).toFun) := by
  have hF := measurable_toHilbertMatrixL2_carrier (U := U) (k := k) (A := A)
    (hSlice := hSlice) hUopen.measurableSet hEntry hUopen hUfinite
  have hRewrite :
      (fun ω => Mu U P (A ω).toFun) = fun ω =>
        ⨅ n : ℕ, blockEnergyAverage U (A ω).toFun
          (canonicalMuGeneratorAffineField (U := U) P
            (TopologicalSpace.denseSeq
              (canonicalMuBlockCorrectionGeneratorSubmodule U) n)) := by
    funext ω
    exact mu_eq_iInf_blockEnergyAverage_aeemuGenerator (U := U) hvol ⟨(A ω).toFun, hSlice ω⟩ P
  rw [hRewrite]
  refine Measurable.iInf (fun n => ?_)
  exact measurable_blockEnergyAverage_carrier (U := U) (k := k) (A := A)
    (hSlice := hSlice) hF _
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P _)

end CarrierEngine

end

end SuperdiffusionCLT.Section2.Annealed
