/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Tails.CFS
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.Basic

/-!
# Package C2: translation transport of `(P3′)` from the origin to every lattice cube

Finding 1 of `CFS.lean` records that the `(P3′)` clause of
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3` (copied verbatim below)
quantifies its bilinear average bound only at the **origin** cube `cu_j`, while the
tail union bound needs it at every translate `z + cu_j`. This file supplies that
transport, from stationarity of the cutoff law alone (`ShellLawPrefix`,
`ShellLawJ2`) — no `ShellLawJ4` (dihedral/negation symmetry) is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Tails

open Homogenization MeasureTheory
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-! ## Transport of `IsBigO` along a measure-preserving self-map -/

/-- **`IsBigO` transports along precomposition with a measure-preserving
self-map.** If `f` is measurable and `Measure.map f mu = mu`, then a witness
`X` for `IsBigO mu Psi X A` gives a witness `X ∘ f` for the same bound: the
tail event of `X ∘ f` is the `f`-preimage of the tail event of `X`, and `f`
being measure-preserving makes the two events have equal measure. -/
theorem akhcCfsT_isBigO_comp_of_measurePreserving {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {f : Omega → Omega}
    (hf : Measurable f) (hmap : Measure.map f mu = mu)
    {Psi : ℝ → ℝ} {X : Omega → ℝ} (hXmeas : Measurable X) {A : ℝ}
    (hXbigO : IsBigO mu Psi X A) :
    IsBigO mu Psi (fun omega => X (f omega)) A := by
  intro t ht
  have hset : upperTailEvent (fun omega => |X (f omega)|) (A * t) =
      f ⁻¹' (upperTailEvent (fun omega => |X omega|) (A * t)) := by
    ext omega
    simp only [upperTailEvent, Set.mem_ofPred_eq, Set.mem_preimage]
  have hXabs : Measurable (fun omega => |X omega|) :=
    continuous_abs.measurable.comp hXmeas
  have hSmeas' : MeasurableSet (upperTailEvent (fun omega => |X omega|) (A * t)) :=
    measurableSet_lt measurable_const hXabs
  have heq : mu (f ⁻¹' (upperTailEvent (fun omega => |X omega|) (A * t))) =
      mu (upperTailEvent (fun omega => |X omega|) (A * t)) := by
    rw [← Measure.map_apply hf hSmeas', hmap]
  have := hXbigO ht
  rw [Measure.real_def] at this ⊢
  rw [hset, heq]
  exact this

/-! ## Geometric covariance: descendants of a translated origin cube -/

/-- **The real shift matching an integer lattice translate of a scale-`j`
origin cube.** -/
def akhcCfsT_realShift {d : ℕ} (j : ℕ) (zshift : Fin d → ℤ) : Vec d :=
  fun i => (zshift i : ℝ) * (3 : ℝ) ^ (j : ℤ)

/-- **A depth-`kdep` descendant of a translated origin cube is the same real
shift of the corresponding descendant of the origin cube.** Combines
`descendantsAtDepth_translateCube`'s combinatorial reindexing with the scale
computation `scale_eq_sub_of_mem_descendantsAtDepth` and the cube-translation
geometry `mem_cubeSet_translateCube_iff`. -/
theorem akhcCfsT_cubeSet_translateCube_descendant {d : ℕ} (j kdep : ℕ)
    (zshift : Fin d → ℤ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (j : ℤ)) kdep) :
    cubeSet (translateCube (descendantTranslationShift kdep zshift) R) =
      translateSet (akhcCfsT_realShift j zshift) (cubeSet R) := by
  have hscaleR : R.scale = (j : ℤ) - (kdep : ℤ) := by
    simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hR
  ext x
  rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem]
  have hvec :
      (fun i => ((descendantTranslationShift kdep zshift i : ℤ) : ℝ) *
          cubeScaleFactor R) = akhcCfsT_realShift j zshift := by
    have hpow : (3 : ℝ) ^ kdep * (3 : ℝ) ^ ((j : ℤ) - (kdep : ℤ)) =
        (3 : ℝ) ^ (j : ℤ) := by
      rw [← zpow_natCast (3 : ℝ) kdep, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    funext i
    simp only [descendantTranslationShift, cubeScaleFactor, hscaleR,
      akhcCfsT_realShift]
    push_cast
    calc (3 : ℝ) ^ kdep * (zshift i : ℝ) * (3 : ℝ) ^ ((j : ℤ) - (kdep : ℤ))
        = (zshift i : ℝ) * ((3 : ℝ) ^ kdep * (3 : ℝ) ^ ((j : ℤ) - (kdep : ℤ))) := by
          ring
      _ = (zshift i : ℝ) * (3 : ℝ) ^ (j : ℤ) := by rw [hpow]
  rw [hvec]

/-! ## Covariance of the coarse block matrix under the cutoff field -/

/-- **The coarse block matrix at a translated descendant cube, for a fixed
sample `omega`, equals the coarse block matrix at the original descendant
cube for the shifted sample `ShellField.translateSequence Z omega`.** This is
the pointwise (sample-by-sample, no law typing) covariance step: it combines
the geometric covariance above with `coefficientCutoff`'s covariance under
`translateReg`/`translateSequence`
(`translateReg_coefficientCutoff`) and `CoarseGraining`'s covariance of
`coarseBlockMatrix` under `translateSet`/`translateCoeffField`. -/
theorem akhcCfsT_coarseBlockMatrix_translateCube_descendant {d : ℕ} (nu : ℝ)
    (L j kdep : ℕ) (zshift : Fin d → ℤ) (omega : ShellSeq d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (j : ℤ)) kdep) :
    coarseBlockMatrix
        (cubeSet (translateCube (descendantTranslationShift kdep zshift) R))
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega
            L).toCoeffField =
      coarseBlockMatrix (cubeSet R)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
            (ShellField.translateSequence (akhcCfsT_realShift j zshift) omega)
            L).toCoeffField := by
  rw [akhcCfsT_cubeSet_translateCube_descendant j kdep zshift hR,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  congr 1
  exact congrArg RegCoeffField.toCoeffField
    (SuperdiffusionCLT.Section2.Annealed.translateReg_coefficientCutoff nu
      (akhcCfsT_realShift j zshift) omega L)

/-! ## Reindexing the depth average over a translated origin cube -/

/-- **The cardinality of the depth-`kdep` descendant set is translation
invariant.** -/
theorem akhcCfsT_card_descendantsAtDepth_translateCube {d : ℕ} (Q : TriadicCube d)
    (kdep : ℕ) (shift : Fin d → ℤ) :
    (descendantsAtDepth (translateCube shift Q) kdep).card =
      (descendantsAtDepth Q kdep).card := by
  rw [descendantsAtDepth_translateCube,
    Finset.card_image_of_injective _ (Homogenization.Book.Ch02.translateCube_injective _)]

/-- **The depth-`kdep` sum over a translated origin cube reindexes to the sum
over the original descendants, each argument post-composed with the matching
per-descendant translate.** -/
theorem akhcCfsT_sum_descendantsAtDepth_translateCube {d : ℕ} {β : Type*}
    [AddCommMonoid β] (Q : TriadicCube d) (kdep : ℕ) (shift : Fin d → ℤ)
    (F : TriadicCube d → β) :
    ∑ R' ∈ descendantsAtDepth (translateCube shift Q) kdep, F R' =
      ∑ R ∈ descendantsAtDepth Q kdep,
        F (translateCube (descendantTranslationShift kdep shift) R) := by
  rw [descendantsAtDepth_translateCube]
  exact Finset.sum_image fun x _ y _ h => Homogenization.Book.Ch02.translateCube_injective _ h

/-! ## The main transport theorem -/

/-- **Transport of V3's origin-only `(P3′)` witness to every integer lattice
translate of the origin cube**, from stationarity of the cutoff law alone
(`ShellLawPrefix`, `ShellLawJ2`; no `ShellLawJ4`). The hypothesis `hBilinear`
is exactly the origin-cube conclusion of V3's `(P3′)` clause
(`Frozen.Section4.akhc_weakerP3`, copied verbatim, never imported) at
depth `j - n` (`j n : ℕ`, `n ≤ j`); the conclusion is the same shape at the
translated cube `translateCube zshift (originCube d j)`, against the
**same** (deterministic, translation-independent) reference matrix
`annealedBlockMatrix nu L P (cubeSet (originCube d n))` — the source's own
`bfAhom(cu_h)` is never translated, only the sample cube is. No `n ≤ j` side
condition is needed: the depth-`(j - n)` bookkeeping (natural subtraction)
carries the whole argument through uniformly, including the degenerate
`n ≥ j` case where the (Nat-truncated) depth is `0`. -/
theorem akhcCfsT_translate_bilinear {d : ℕ} (nu : ℝ) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    {Psi : ℝ → ℝ} {j n : ℕ} {A : ℝ} (zshift : Fin d → ℤ)
    {X : ShellSeq d → ℝ} (hXmeas : Measurable X)
    (hXbigO : IsBigO P.toMeasure Psi X A)
    (hBilinear : ∀ (omega : ShellSeq d) (p q : BlockVec d),
        2 * (((descendantsAtDepth (originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (j : ℤ)) (j - n),
              blockVecDot p (blockMatVecMul (ofFullBlockMat
                  (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                          omega L).toCoeffField) -
                    toFullBlockMat (annealedBlockMatrix nu L P
                      (cubeSet (originCube d (n : ℤ)))))) q)) ≤
          X omega * (blockVecDot p (blockMatVecMul
                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q (blockMatVecMul
                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q))) :
    ∃ X' : ShellSeq d → ℝ, Measurable X' ∧ IsBigO P.toMeasure Psi X' A ∧
      ∀ (omega : ShellSeq d) (p q : BlockVec d),
        2 * (((descendantsAtDepth
                (translateCube zshift (originCube d (j : ℤ))) (j - n)).card : ℝ)⁻¹ *
            ∑ R' ∈ descendantsAtDepth
                (translateCube zshift (originCube d (j : ℤ))) (j - n),
              blockVecDot p (blockMatVecMul (ofFullBlockMat
                  (toFullBlockMat (coarseBlockMatrix (cubeSet R')
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                          omega L).toCoeffField) -
                    toFullBlockMat (annealedBlockMatrix nu L P
                      (cubeSet (originCube d (n : ℤ)))))) q)) ≤
          X' omega * (blockVecDot p (blockMatVecMul
                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q (blockMatVecMul
                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) := by
  set Z : Vec d := akhcCfsT_realShift j zshift with hZ
  refine ⟨fun omega => X (ShellField.translateSequence Z omega), ?_, ?_, ?_⟩
  · exact hXmeas.comp (ShellField.measurable_translateSequence Z)
  · exact akhcCfsT_isBigO_comp_of_measurePreserving
      (ShellField.measurable_translateSequence Z)
      (ShellField.map_translateSequence_eq hPrefix hJ2 Z) hXmeas hXbigO
  · intro omega p q
    rw [akhcCfsT_card_descendantsAtDepth_translateCube,
      akhcCfsT_sum_descendantsAtDepth_translateCube]
    have hpointwise : ∀ R ∈ descendantsAtDepth (originCube d (j : ℤ)) (j - n),
        blockVecDot p (blockMatVecMul (ofFullBlockMat
            (toFullBlockMat (coarseBlockMatrix
                (cubeSet (translateCube (descendantTranslationShift (j - n) zshift) R))
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                    omega L).toCoeffField) -
              toFullBlockMat (annealedBlockMatrix nu L P
                (cubeSet (originCube d (n : ℤ)))))) q) =
        blockVecDot p (blockMatVecMul (ofFullBlockMat
            (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                    (ShellField.translateSequence Z omega) L).toCoeffField) -
              toFullBlockMat (annealedBlockMatrix nu L P
                (cubeSet (originCube d (n : ℤ)))))) q) := by
      intro R hR
      rw [akhcCfsT_coarseBlockMatrix_translateCube_descendant nu L j (j - n) zshift
        omega hR]
    rw [Finset.sum_congr rfl hpointwise]
    exact hBilinear (ShellField.translateSequence Z omega) p q

/-! ## Bridging facts for the corollary -/

/-- `descendantsAverage` unfolds definitionally to the explicit card/sum
form that V3's `(P3′)` clause and `akhcCfsT_translate_bilinear` are stated
with. -/
private theorem akhcCfsT_descendantsAverage_eq {d : ℕ} (Q : TriadicCube d)
    (kdep : ℕ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q kdep F =
      ((descendantsAtDepth Q kdep).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q kdep, F R :=
  rfl

/-- The integer-to-`Nat` truncated depth `(Q.scale - h).toNat` used by
`CFS.lean`'s subadditivity chain matches the `Nat`-truncated depth `j - n`
used by V3's `(P3′)` clause, for every `j n : ℕ` (no `n ≤ j` side condition:
both sides truncate to `0` in the degenerate case). -/
private theorem akhcCfsT_toNat_sub_eq (j n : ℕ) :
    ((j : ℤ) - (n : ℤ)).toNat = j - n := by
  omega

/-! ## The corollary: the Loewner excess bound at every translate -/

/-- **Package C2's node-13 target, discharged from V3's origin `(P3′)` clause
alone.** Given the origin `(P3′)` bilinear witness at `(j, n)` and
`ShellLawPrefix`/`ShellLawJ2` (stationarity; no `ShellLawJ4`), there is a
single translate-indexed witness `X'` — `Measurable`, `IsBigO`-bounded by the
same amplitude `A` — such that, at every integer lattice translate `zshift`
and every sample `omega` with an a.e.-locally-uniformly-elliptic cutoff field,
`CFS.lean`'s algebraic core
(`akhcCfs_blockMatLoewnerLE_coarseBlockMatrix_of_subadditivity_and_bilinear`)
gives the one-sided Loewner excess bound
`bfA(z + cu_j) ⪯ (1 + X'(omega)) • bfAhom(cu_n)`, against the **same** fixed
origin reference `bfAhom(cu_n)` for every translate. This is exactly the
translate-indexed family that node 13's union bound (`CFSB.lean`) ranges
over: `CFSB.lean`'s own theorems (`akhcCfs_perScale_secondMoment_le`,
`akhcCfs_scaleSum_secondMoment_le`) already take that family as a generic
hypothesis `hX : ∀ i ∈ S, IsBigO Pm Psi (X i) ωh`, so no change to `CFSB.lean`
is needed: this corollary is exactly the missing derivation of that
hypothesis at the intended instantiation `S k := descendantsAtScale
(originCube d n) k`'s translate-indexed sibling for the coarser scale `j`,
using `X i := fun omega => X' omega` for `i` ranging over the finitely many
admissible `zshift`. -/
theorem akhcCfsT_blockMatLoewnerLE_translateCube_of_P3prime {d : ℕ} [NeZero d]
    (nu : ℝ) (L : ℕ) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    {Psi : ℝ → ℝ} {j n : ℕ} (hnj : n ≤ j) {A : ℝ} (zshift : Fin d → ℤ)
    {X : ShellSeq d → ℝ} (hXmeas : Measurable X)
    (hXbigO : IsBigO P.toMeasure Psi X A)
    (hBilinear : ∀ (omega : ShellSeq d) (p q : BlockVec d),
        2 * (((descendantsAtDepth (originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (j : ℤ)) (j - n),
              blockVecDot p (blockMatVecMul (ofFullBlockMat
                  (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                          omega L).toCoeffField) -
                    toFullBlockMat (annealedBlockMatrix nu L P
                      (cubeSet (originCube d (n : ℤ)))))) q)) ≤
          X omega * (blockVecDot p (blockMatVecMul
                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q (blockMatVecMul
                (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q))) :
    ∃ X' : ShellSeq d → ℝ, Measurable X' ∧ IsBigO P.toMeasure Psi X' A ∧
      ∀ omega : ShellSeq d,
        Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L) →
        Homogenization.BlockMatLoewnerLE
          (coarseBlockMatrix (cubeSet (translateCube zshift (originCube d (j : ℤ))))
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega
                  L).toCoeffField)
          ((1 + X' omega) •
            annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) := by
  obtain ⟨X', hX'meas, hX'bigO, hX'bilinear⟩ :=
    akhcCfsT_translate_bilinear nu L hPrefix hJ2 zshift hXmeas hXbigO hBilinear
  refine ⟨X', hX'meas, hX'bigO, fun omega ha => ?_⟩
  have hh : (n : ℤ) ≤ (translateCube zshift (originCube d (j : ℤ))).scale := by
    show (n : ℤ) ≤ (j : ℤ)
    exact_mod_cast hnj
  have hdepth : (((translateCube zshift (originCube d (j : ℤ))).scale : ℤ) -
      (n : ℤ)).toNat = j - n := by
    show ((j : ℤ) - (n : ℤ)).toNat = j - n
    exact akhcCfsT_toNat_sub_eq j n
  have hBil' :
      ∀ p q : BlockVec d,
        2 * descendantsAverage (translateCube zshift (originCube d (j : ℤ)))
            (((translateCube zshift (originCube d (j : ℤ))).scale - (n : ℤ)).toNat)
            (fun R => blockVecDot p
              (blockMatVecMul
                (ofFullBlockMat
                  (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                          omega L).toCoeffField) -
                    toFullBlockMat (annealedBlockMatrix nu L P
                      (cubeSet (originCube d (n : ℤ)))))) q)) ≤
          X' omega *
            (blockVecDot p (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) := by
    intro p q
    rw [akhcCfsT_descendantsAverage_eq, hdepth]
    exact hX'bilinear omega p q
  exact akhcCfs_blockMatLoewnerLE_coarseBlockMatrix_of_subadditivity_and_bilinear
    (a := SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L) ha hh hBil'

end

end SuperdiffusionCLT.AKHC61.Tails
