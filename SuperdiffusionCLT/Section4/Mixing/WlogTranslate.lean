/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.WlogReduction
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# `p.mixing.P.three.prime#wlog-reduction`, the translated-block step

`Section4/Mixing/WlogReduction.lean`'s `mixMain_wlogInductionStep` assembles
the WLOG reassembly from, for *every* scale-`mtilde` block `R`
inside `cu_m`, the "already proved smaller-gap statement" holding at `R` with
a *common* amplitude witness. That file leaves the translation-covariance step
supplying those per-`R` witnesses from the single statement at the origin
cube untouched (its own docstring: "wiring (1) and (2) into the actual
induction ... is not proved in this file").

This file supplies that step. `mixFin_wlogTranslate` takes the "smaller-gap
statement" `h0` at the origin cube `cu_{m̃}` (an arbitrary translation-
covariant bilinear form `F`, together with the hypothesis `hFcov` that it
*is* translation covariant: for every discrete cube translation `translateCube
w Q` realized as the real-space translate `translateSet zreal (cubeSet Q)`,
`F` reads the same value on the translate as `F` reads on `Q` for the
correspondingly shell-translated field) and produces the same statement, with
the same amplitude, at every scale-`mtilde` descendant `R` of `cu_m` — exactly
the `hXm`, `hXO`, `hbound` hypotheses of `mixMain_wlogInductionStep`.

The mechanism: `R` (scale `mtilde`) is `translateCube R.index (originCube d
mtilde)`; by `Homogenization.descendantsAtDepth_translateCube`, its own
scale-`n` descendants are exactly the images, under the *same* discrete shift
`descendantTranslationShift (mtilde-n) R.index`, of the scale-`n` descendants
`S` of `cu_{m̃}`. The elementary identity
`triadicCubeShift (translateCube (descendantTranslationShift k z) S) =
triadicCubeShift S + triadicCubeShift (translateCube z (originCube d mtilde))`
(`mixFin_triadicCubeShift_descendant_eq`) turns this into the *real-space*
translate identity `cubeSet (translateCube (descendantTranslationShift k z) S)
= translateSet (triadicCubeShift R) (cubeSet S)` (`mixFin_cubeSet_descendant_eq`,
using `Homogenization.cubeSet_eq_translateSet_originCube_of_triadicCube` twice
and `translateSet_translateSet` once — no translation-composition law on the
shell field itself is needed), which `hFcov` then reads off directly against
the single shift `triadicCubeShift R`, matching exactly the shift
`Section3/Terms/TranslatedBlocks.lean`'s `translateObservable` uses. The
witness produced is `translateObservable X0 R`, and `measurable_translateObservable`
/ `isBigO_gammaSigma_translateObservable` (both in that file) give `hXm`,
`hXO` for it directly — "the law of the translated field equals the law of
the field, so an `O_Γ` statement at the origin cube holds at every translate
with the same constant."
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)
open SuperdiffusionCLT.Section2.Annealed (translateReg_coefficientCutoff)
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The elementary shift algebra -/

/-- **The key shift identity.** For a scale-`n` cube `S` sitting `k` levels
below scale `mtilde` (`S.scale + k = mtilde`), translating its depth-`k`
descendant-indexing shift `descendantTranslationShift k z` gives a cube whose
`triadicCubeShift` is `S`'s own shift plus the shift of the scale-`mtilde`
translate `translateCube z (originCube d mtilde)`. -/
private theorem mixFin_triadicCubeShift_descendant_eq {mtilde : ℤ} {k : ℕ} {z : Fin d → ℤ}
    {S : TriadicCube d} (hS : S.scale + (k : ℤ) = mtilde) :
    triadicCubeShift (translateCube (descendantTranslationShift k z) S) =
      triadicCubeShift S + triadicCubeShift (translateCube z (originCube d mtilde)) := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have hpow : (3 : ℝ) ^ k * (3 : ℝ) ^ S.scale = (3 : ℝ) ^ mtilde := by
    rw [← zpow_natCast (3 : ℝ) k, ← zpow_add₀ h3ne, add_comm (k : ℤ) S.scale, hS]
  funext i
  simp only [triadicCubeShift, translateCube, originCube, descendantTranslationShift,
    cubeScaleFactor, Pi.add_apply, Pi.zero_apply, zero_add]
  push_cast
  rw [← hpow]
  ring

/-- **The real-space translate identity for a nested descendant.** -/
private theorem mixFin_cubeSet_descendant_eq {mtilde : ℤ} {k : ℕ} {z : Fin d → ℤ}
    {S : TriadicCube d} (hS : S.scale + (k : ℤ) = mtilde) :
    cubeSet (translateCube (descendantTranslationShift k z) S) =
      translateSet (triadicCubeShift (translateCube z (originCube d mtilde))) (cubeSet S) := by
  have hshift := mixFin_triadicCubeShift_descendant_eq (z := z) hS
  calc cubeSet (translateCube (descendantTranslationShift k z) S)
      = translateSet (triadicCubeShift (translateCube (descendantTranslationShift k z) S))
          (cubeSet (originCube d S.scale)) :=
        cubeSet_eq_translateSet_originCube_of_triadicCube
          (translateCube (descendantTranslationShift k z) S)
    _ = translateSet (triadicCubeShift S + triadicCubeShift (translateCube z (originCube d mtilde)))
          (cubeSet (originCube d S.scale)) := by rw [hshift]
    _ = translateSet (triadicCubeShift (translateCube z (originCube d mtilde)))
          (translateSet (triadicCubeShift S) (cubeSet (originCube d S.scale))) :=
        (translateSet_translateSet (triadicCubeShift S)
          (triadicCubeShift (translateCube z (originCube d mtilde))) (cubeSet (originCube d S.scale))).symm
    _ = translateSet (triadicCubeShift (translateCube z (originCube d mtilde))) (cubeSet S) := by
        rw [← cubeSet_eq_translateSet_originCube_of_triadicCube S]

/-! ## The descendant combinatorics -/

/-- Every scale-`(m'-n')`-depth descendant of `cu_{m'}` has scale `n'`. -/
private theorem mixFin_scale_eq_of_mem_descendantsAtDepth' {n' m' : ℕ} (hnm : n' ≤ m')
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (m' : ℤ)) (m' - n')) :
    R.scale = (n' : ℤ) := by
  have h := scale_eq_sub_of_mem_descendantsAtDepth hR
  have hoscale : (originCube d (m' : ℤ)).scale = (m' : ℤ) := rfl
  rw [hoscale] at h
  omega

/-- Every cube of scale `s` is a discrete translate of the origin cube of the
same scale, by its own index. -/
private theorem mixFin_eq_translateCube_index_originCube {Q : TriadicCube d} {s : ℤ}
    (hQ : Q.scale = s) : Q = translateCube Q.index (originCube d s) := by
  cases Q with
  | mk qs qi =>
      simp only at hQ
      subst hQ
      simp [translateCube, originCube]

/-- Translating triadic cube indices by a fixed shift is injective. -/
private theorem mixFin_translateCube_injective (w : Fin d → ℤ) :
    Function.Injective (translateCube w : TriadicCube d → TriadicCube d) := by
  intro Q1 Q2 hQ
  have hs0 := congrArg (fun R : TriadicCube d => R.scale) hQ
  have hs : Q1.scale = Q2.scale := hs0
  have hi : Q1.index = Q2.index := by
    funext j
    have h0 := congrArg (fun R : TriadicCube d => R.index j) hQ
    have h : Q1.index j + w j = Q2.index j + w j := h0
    exact add_right_cancel h
  cases Q1 with
  | mk s1 i1 =>
      cases Q2 with
      | mk s2 i2 =>
          simp only at hs hi
          subst hs
          subst hi
          rfl

/-! ## The main translation step -/

/-- **The WLOG translation step**, `p.mixing.P.three.prime#wlog-reduction`
Given the "already proved smaller-gap statement" `h0` at the
origin cube `cu_{m̃}` and the translation covariance `hFcov` of the bilinear
form `F` (every discrete cube translation `translateCube w Q`, realized as the
real-space translate `translateSet zreal (cubeSet Q)`, reads on `F` as `Q`
does for the correspondingly shell-translated field), produces the same
statement, with the same amplitude (via `translateObservable X0`), at every
scale-`mtilde` descendant `R` of `cu_m` — exactly `mixMain_wlogInductionStep`'s
three hypotheses `hXm`, `hXO`, `hbound`. -/
theorem mixFin_wlogTranslate {PQ : Type*} [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P)
    {n mtilde m : ℕ} (hnmt : n ≤ mtilde) (hmtm : mtilde ≤ m)
    {G : PQ → PQ → ℝ} {a σ : ℝ}
    {F : TriadicCube d → ShellSeq d → PQ → PQ → ℝ}
    (hFcov : ∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d) (p q : PQ),
        cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
          F (translateCube w Q) omega p q = F Q (ShellField.translateSequence zreal omega) p q)
    {X0 : ShellSeq d → ℝ} (hX0m : Measurable X0) (hX0O : IsBigO P.toMeasure (gammaSigma σ) X0 a)
    (h0 : ∀ (omega : ShellSeq d) (p q : PQ),
        2 * descendantsAverage (originCube d (mtilde : ℤ)) (mtilde - n) (fun R' => F R' omega p q) ≤
          X0 omega * G p q) :
    (∀ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - mtilde),
        Measurable (translateObservable X0 R)) ∧
      (∀ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - mtilde),
        IsBigO P.toMeasure (gammaSigma σ) (translateObservable X0 R) a) ∧
      ∀ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - mtilde),
        ∀ (omega : ShellSeq d) (p q : PQ),
          2 * descendantsAverage R (mtilde - n) (fun R' => F R' omega p q) ≤
            translateObservable X0 R omega * G p q := by
  refine ⟨fun R _ => measurable_translateObservable hX0m R,
    fun R _ => isBigO_gammaSigma_translateObservable hPrefix hJ2 hX0m hX0O R, ?_⟩
  intro R hR omega p q
  have hRscale : R.scale = (mtilde : ℤ) := mixFin_scale_eq_of_mem_descendantsAtDepth' hmtm hR
  have hReq : R = translateCube R.index (originCube d (mtilde : ℤ)) :=
    mixFin_eq_translateCube_index_originCube hRscale
  set w : Fin d → ℤ := descendantTranslationShift (mtilde - n) R.index with hw_def
  have hSscale : ∀ S ∈ descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n),
      S.scale + ((mtilde - n : ℕ) : ℤ) = (mtilde : ℤ) := by
    intro S hS
    have := mixFin_scale_eq_of_mem_descendantsAtDepth' hnmt hS
    omega
  have himg : descendantsAtDepth R (mtilde - n) =
      (descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n)).image (translateCube w) := by
    conv_lhs => rw [hReq]
    exact descendantsAtDepth_translateCube R.index (originCube d (mtilde : ℤ)) (mtilde - n)
  have hcov : ∀ S ∈ descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n),
      F (translateCube w S) omega p q =
        F S (ShellField.translateSequence (triadicCubeShift R) omega) p q := by
    intro S hS
    have hSseq : S.scale + ((mtilde - n : ℕ) : ℤ) = (mtilde : ℤ) := hSscale S hS
    have hset : cubeSet (translateCube w S) = translateSet (triadicCubeShift R) (cubeSet S) := by
      have hraw := mixFin_cubeSet_descendant_eq (z := R.index) hSseq
      rwa [← hReq] at hraw
    exact hFcov (triadicCubeShift R) w S omega p q hset
  have hinj : Set.InjOn (translateCube w)
      (descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n) : Set (TriadicCube d)) :=
    (mixFin_translateCube_injective w).injOn
  have hcard_nat : (descendantsAtDepth R (mtilde - n)).card =
      (descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n)).card := by
    rw [himg, Finset.card_image_of_injOn hinj]
  have hcard : ((descendantsAtDepth R (mtilde - n)).card : ℝ) =
      ((descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n)).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hsum : ∑ R' ∈ descendantsAtDepth R (mtilde - n), F R' omega p q =
      ∑ S ∈ descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n),
        F S (ShellField.translateSequence (triadicCubeShift R) omega) p q := by
    rw [himg, Finset.sum_image hinj]
    exact Finset.sum_congr rfl hcov
  have hdesc : descendantsAverage R (mtilde - n) (fun R' => F R' omega p q) =
      descendantsAverage (originCube d (mtilde : ℤ)) (mtilde - n)
        (fun S => F S (ShellField.translateSequence (triadicCubeShift R) omega) p q) := by
    show ((descendantsAtDepth R (mtilde - n)).card : ℝ)⁻¹ *
          ∑ R' ∈ descendantsAtDepth R (mtilde - n), F R' omega p q =
        ((descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n)).card : ℝ)⁻¹ *
          ∑ S ∈ descendantsAtDepth (originCube d (mtilde : ℤ)) (mtilde - n),
            F S (ShellField.translateSequence (triadicCubeShift R) omega) p q
    rw [hcard, hsum]
  rw [hdesc]
  have hbase := h0 (ShellField.translateSequence (triadicCubeShift R) omega) p q
  simpa only [translateObservable, ge_iff_le] using hbase

/-! ## Satisfiability: a concrete `F` that discharges `hFcov`

`mixFin_wlogTranslate`'s covariance hypothesis `hFcov` is not vacuous: the
actual coarse-block quenched bilinear form this development's induction is
over — `blockVecDot p (blockMatVecMul (coarseBlockMatrix (cubeSet Q)
(coefficientCutoff nu omega L).toCoeffField) q)`, the summand underlying
`mixTerms_reassembled` (`Section4/Mixing/TermsCombined.lean`) and the
stationarity target of `Section4/Mixing/AnnealedFinal.lean` — satisfies it,
by exactly the argument `Section3/Terms/TranslatedBlocks.lean`'s
`translatedBlockMat_eq_originCube` already uses for the single-cube case:
`coarseBlockMatrix_translateSet_eq_translateCoeffField` and
`translateReg_coefficientCutoff`. -/
theorem mixFin_coarseBlockMatrix_hFcov [NeZero d] (nu : ℝ) (L : ℕ) :
    ∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d) (p q : BlockVec d),
      cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
        blockVecDot p (blockMatVecMul
            (coarseBlockMatrix (cubeSet (translateCube w Q))
              (coefficientCutoff nu omega L).toCoeffField) q) =
          blockVecDot p (blockMatVecMul
              (coarseBlockMatrix (cubeSet Q)
                (coefficientCutoff nu (ShellField.translateSequence zreal omega) L).toCoeffField) q) := by
  intro zreal w Q omega p q hset
  have hraw : coarseBlockMatrix (cubeSet (translateCube w Q))
      (coefficientCutoff nu omega L).toCoeffField =
      coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu (ShellField.translateSequence zreal omega) L).toCoeffField := by
    rw [hset, coarseBlockMatrix_translateSet_eq_translateCoeffField,
      ← translateReg_coefficientCutoff nu zreal omega L]
    rfl
  rw [hraw]

end

end SuperdiffusionCLT.Section4.Mixing
