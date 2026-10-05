/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.EnvelopeEllipticity

/-!
# The weighted sub-cube union bound of `e.bfAm.ellip`

The proof of lemma `l.bfAm.ellip` obtains its third assertion `e.Smgamma.integ` from a union bound
over the triadic sub-cubes of `cu_n`: for `t ≥ 1`, `gamma ∈ (0,1)` and `n ∈ ℕ` it sums the local
square bound `e.km.square.bound` over all scales `l ∈ ℤ ∩ (-∞, n]` and, at each scale, over the
`3^{d(n-l)}` cubes `z + cu_l` with `z ∈ 3^l ℤ^d ∩ cu_n`.

This module supplies that sum. Its input is the Γ₁ tail of the
random factor `envelopeRatio` of `Envelope`,
`isBigOWith_gammaSigma_envelopeRatio`, which holds at amplitude `1` uniformly
in the cube and in `m`, and its output is the printed amplitude
`C exp(C |log gamma| / gamma)` of `e.Smgamma.integ`. That amplitude is exactly
the value of the geometric sum: the term of scale `n - l = k` is at most
`3^{d(k+1)} exp(-2 t 3^{gamma k})`, and

`sup_{k ≥ 0} (d k log 3 - 3^{gamma k}) ≤ (d/gamma) log(d/gamma)`

by the Legendre bound `a u - e^u ≤ a log a - a`, which is where the factor
`exp(C |log gamma| / gamma)` is produced.

## Main results

* `measureReal_envelopeRatio_gt_le`: the tail of one cube, read as
  `P[envelopeRatio > s] ≤ exp(-s)` for `s ≥ 1`.
* `subCubeUnionConst`: the dimension-only amplitude constant.
* `measureReal_exists_subCube_gt_le_of_scaleTail`: the union bound from an
  arbitrary per-scale tail of `envelopeRatio`, with the counting of the
  sub-cubes of one scale.
* `envelopeRatio_weighted_le_of_not_mem`: off the event that some triadic sub-cube of `cu_n` of
  scale `l ≤ n` violates `envelopeRatio ≤ 2 t 3^{gamma(n-l)}`, at `t = 1`, every triadic sub-cube
  of `cu_n` satisfies the scalar form of the printed conclusion
  `3^{-gamma(n-l)} bfE_m^{-1/2} bfA_m(z + cu_l) bfE_m^{-1/2} ≤ 2 I_{2d}` of `e.bfAm.ellip`.

## What the random minimal scale needs beyond this bound

Two things separate the union bound proved here from the random scale
`S_{m,gamma}` of `e.Smgamma.integ`.

* **Decay in the level `n`.** The printed union bound is
  `exp(C |log gamma| / gamma) exp(-c t 3^{gamma(n-m)})`, and its decay in `n`
  comes from the printed square bound `e.km.square.bound`, whose
  amplitude improves to `1 + O_{Γ₁}(C 3^{-((d/2)(l-m) ∨ 0)})` on
  cubes larger than the cutoff scale. Only the unimproved amplitude `1` is
  used here, so the bound proved here is uniform in `n`: the scale-`n` term of the
  sum contributes `exp(-t)` at every `n`. Without decay in `n` the events
  `{some sub-cube of cu_n fails at t = 1}` are not summable in `n`, so no
  Borel-Cantelli step is available and the set of failing levels `n` cannot be
  shown to be finite.
* **The shape of the conclusion.** A minimal scale with values in `ℝ` and the
  implication `S omega ≤ 3^n → (every sub-cube of cu_n is good)` required for
  *every* `omega` forces the set of failing levels to be bounded at every sample
  point, not merely almost surely. The sample carrier
  `ShellSeq d = ℕ → ShellField d` contains sample points whose shells are
  arbitrarily large constant skew matrices; for such a point the coefficient
  field `nu Id + k_m` is constant, so the normalized coarse block matrix on
  `cu_n` does not depend on `n` and exceeds `2 I_{2d}` at every level. For such
  a sample point no real value of `S` can satisfy the implication, so the
  quantifier over `omega` has to be almost-sure.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-! ## Two elementary exponential inequalities -/

/-! ## The geometric sum over the scales -/

/-- The dimension-only amplitude produced by the sum over the scales `l ≤ n`. -/
def subCubeUnionConst (d : ℕ) : ℝ :=
  max ((3 : ℝ) ^ (d + 1) * Real.exp (((d : ℝ) + 1) * Real.log ((d : ℝ) + 1)) *
      (3 / Real.log 3))
    (((d : ℝ) + 1) * Real.log ((d : ℝ) + 1) + ((d : ℝ) + 1) + 1)

/-! ## The triadic sub-cubes of `cu_n` at one scale -/

variable {d : ℕ}

/-- The triadic cubes of scale `n - k` whose centre can lie in `cu_n`. -/
private def subCubeFinset (d n k : ℕ) : Finset (TriadicCube d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(3 ^ k : ℤ)) (3 ^ k)).image
    fun idx => ⟨(n : ℤ) - (k : ℤ), idx⟩

private theorem card_subCubeFinset_le (d n k : ℕ) :
    (subCubeFinset d n k).card ≤ 3 ^ ((d + 1) * (k + 1)) := by
  have hIcc : ∀ _i : Fin d, (Finset.Icc (-(3 ^ k : ℤ)) (3 ^ k)).card = 2 * 3 ^ k + 1 := by
    intro _i
    rw [Int.card_Icc]
    have hcast : ((3 : ℤ) ^ k + 1 - -(3 ^ k)) = ((2 * 3 ^ k + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast, Int.toNat_natCast]
  have hcard : (Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-(3 ^ k : ℤ)) (3 ^ k)).card = (2 * 3 ^ k + 1) ^ d := by
    rw [Fintype.card_piFinset, Finset.prod_congr rfl fun i _ => hIcc i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  refine le_trans Finset.card_image_le ?_
  rw [hcard]
  have hbase : 2 * 3 ^ k + 1 ≤ 3 ^ (k + 1) := by
    have h1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
    omega
  calc (2 * 3 ^ k + 1) ^ d ≤ (3 ^ (k + 1)) ^ d := Nat.pow_le_pow_left hbase d
    _ = 3 ^ ((k + 1) * d) := by rw [← pow_mul]
    _ ≤ 3 ^ ((d + 1) * (k + 1)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        have : (k + 1) * d = d * (k + 1) := Nat.mul_comm _ _
        rw [this]
        exact Nat.mul_le_mul_right _ (Nat.le_succ d)

private theorem mem_subCubeFinset (n k : ℕ) {Q : TriadicCube d}
    (hscale : Q.scale = (n : ℤ) - (k : ℤ))
    (hmem : cubeCenter Q ∈ cubeSet (originCube d (n : ℤ))) :
    Q ∈ subCubeFinset d n k := by
  have hA : (0 : ℝ) < (3 : ℝ) ^ (n : ℤ) := by positivity
  have hB : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := by positivity
  have hidx : ∀ i, Q.index i ∈ Finset.Icc (-(3 ^ k : ℤ)) (3 ^ k) := by
    intro i
    have h := (mem_cubeSet_originCube_iff.1 hmem) i
    have hcc : cubeCenter Q i =
        (Q.index i : ℝ) / (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (n : ℤ) := by
      show (Q.index i : ℝ) * cubeScaleFactor Q = _
      rw [cubeScaleFactor, hscale, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    rw [hcc] at h
    have hlow : -(1 / 2 : ℝ) ≤ (Q.index i : ℝ) / (3 : ℝ) ^ (k : ℤ) := by
      have := h.1
      exact le_of_mul_le_mul_right (by linarith only [this]) hA
    have hhigh : (Q.index i : ℝ) / (3 : ℝ) ^ (k : ℤ) < 1 / 2 := by
      have := h.2
      exact lt_of_mul_lt_mul_right (by linarith only [this]) hA.le
    have hlow' : -(1 / 2 : ℝ) * (3 : ℝ) ^ (k : ℤ) ≤ (Q.index i : ℝ) :=
      (le_div_iff₀ hB).1 hlow
    have hhigh' : (Q.index i : ℝ) < 1 / 2 * (3 : ℝ) ^ (k : ℤ) :=
      (div_lt_iff₀ hB).1 hhigh
    have hcast : ((3 : ℝ) ^ (k : ℤ)) = (((3 ^ k : ℤ) : ℝ)) := by
      push_cast
      rw [zpow_natCast]
    rw [Finset.mem_Icc]
    constructor
    · have : (-((3 ^ k : ℤ) : ℝ)) ≤ (Q.index i : ℝ) := by
        rw [← hcast]
        linarith only [hlow', hB]
      exact_mod_cast this
    · have : (Q.index i : ℝ) ≤ (((3 ^ k : ℤ) : ℝ)) := by
        rw [← hcast]
        linarith only [hhigh', hB]
      exact_mod_cast this
  have hQ : (⟨(n : ℤ) - (k : ℤ), Q.index⟩ : TriadicCube d) = Q := by
    rw [← hscale]
  exact Finset.mem_image.2 ⟨Q.index, Fintype.mem_piFinset.2 hidx, hQ⟩

/-! ## The per-cube tail -/

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- The Γ₁ tail of `envelopeRatio`, read as an exponential bound on
the upper-tail event of one triadic cube. -/
theorem measureReal_envelopeRatio_gt_le (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m : ℕ)
    (Q : TriadicCube d) {s : ℝ} (hs : 1 ≤ s) :
    P.toMeasure.real {omega | s < envelopeRatio m Q omega} ≤ Real.exp (-s) := by
  have h := isBigOWith_gammaSigma_envelopeRatio hPrefix hJ2 hJ3 hJ4 m Q hs
  have hset : IndependentSums.upperTailEvent (fun omega => envelopeRatio m Q omega) (1 * s)
      = {omega | s < envelopeRatio m Q omega} := by
    rw [one_mul]
    rfl
  rw [hset] at h
  refine h.trans (le_of_eq ?_)
  rw [IndependentSums.gammaSigma_apply, Real.rpow_one, ← Real.exp_neg]

/-! ## The weighted union bound over all sub-cubes of `cu_n` -/

private theorem scale_of_mem_subCubeFinset {n k : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ subCubeFinset d n k) : Q.scale = (n : ℤ) - (k : ℤ) := by
  obtain ⟨idx, -, rfl⟩ := Finset.mem_image.1 hQ
  rfl

/-- **The union bound over the triadic sub-cubes of `cu_n`**,
from an arbitrary per-scale tail of the random factor: the scale `l = n - k` carries the
threshold `thr k`, the tail bound `tail k`, and at most `3^{(d+1)(k+1)}` cubes
whose centre lies in `cu_n`. -/
theorem measureReal_exists_subCube_gt_le_of_scaleTail (m n : ℕ) (thr tail : ℕ → ℝ)
    (htail : ∀ (k : ℕ) (Q : TriadicCube d), Q.scale = (n : ℤ) - (k : ℤ) →
      P.toMeasure.real {omega : ShellSeq d | thr k < envelopeRatio m Q omega} ≤ tail k)
    (htail0 : ∀ k : ℕ, 0 ≤ tail k)
    (hsum : Summable fun k : ℕ => (3 : ℝ) ^ ((d + 1) * (k + 1)) * tail k) :
    P.toMeasure.real {omega : ShellSeq d | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧
        thr (((n : ℤ) - Q.scale).toNat) < envelopeRatio m Q omega} ≤
      ∑' k : ℕ, (3 : ℝ) ^ ((d + 1) * (k + 1)) * tail k := by
  classical
  have hbnn : ∀ k : ℕ, 0 ≤ (3 : ℝ) ^ ((d + 1) * (k + 1)) * tail k := by
    intro k
    exact mul_nonneg (by positivity) (htail0 k)
  have hsub : {omega : ShellSeq d | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧
      thr (((n : ℤ) - Q.scale).toNat) < envelopeRatio m Q omega} ⊆
      ⋃ k : ℕ, ⋃ Q ∈ subCubeFinset d n k,
        {omega : ShellSeq d | thr k < envelopeRatio m Q omega} := by
    intro omega homega
    obtain ⟨Q, hQscale, hQmem, hQgt⟩ := homega
    have hk : ((((n : ℤ) - Q.scale).toNat : ℤ)) = (n : ℤ) - Q.scale :=
      Int.toNat_of_nonneg (by omega)
    have hscale : Q.scale = (n : ℤ) - ((((n : ℤ) - Q.scale).toNat : ℕ) : ℤ) := by omega
    exact Set.mem_iUnion.2 ⟨((n : ℤ) - Q.scale).toNat,
      Set.mem_iUnion₂.2 ⟨Q, mem_subCubeFinset n _ hscale hQmem, hQgt⟩⟩
  have hlevel : ∀ k : ℕ, P.toMeasure (⋃ Q ∈ subCubeFinset d n k,
      {omega : ShellSeq d | thr k < envelopeRatio m Q omega}) ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((d + 1) * (k + 1)) * tail k) := by
    intro k
    have hone : ∀ Q ∈ subCubeFinset d n k,
        P.toMeasure {omega : ShellSeq d | thr k < envelopeRatio m Q omega} ≤
          ENNReal.ofReal (tail k) := by
      intro Q hQ
      have hreal := htail k Q (scale_of_mem_subCubeFinset hQ)
      have hfin : P.toMeasure {omega : ShellSeq d | thr k < envelopeRatio m Q omega} ≠ ⊤ :=
        measure_ne_top _ _
      calc P.toMeasure {omega : ShellSeq d | thr k < envelopeRatio m Q omega}
          = ENNReal.ofReal
              (P.toMeasure.real {omega : ShellSeq d | thr k < envelopeRatio m Q omega}) := by
            rw [measureReal_def, ENNReal.ofReal_toReal hfin]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hone) ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : (((subCubeFinset d n k).card : ℕ) : ℝ) ≤ (3 : ℝ) ^ ((d + 1) * (k + 1)) := by
      have hle : (((subCubeFinset d n k).card : ℕ) : ℝ) ≤
          ((3 ^ ((d + 1) * (k + 1)) : ℕ) : ℝ) :=
        Nat.cast_le.2 (card_subCubeFinset_le d n k)
      refine hle.trans (le_of_eq ?_)
      push_cast
      ring
    exact mul_le_mul_of_nonneg_right hcard (htail0 k)
  have hmeasure : P.toMeasure {omega : ShellSeq d | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧
      thr (((n : ℤ) - Q.scale).toNat) < envelopeRatio m Q omega} ≤
      ENNReal.ofReal (∑' k : ℕ, (3 : ℝ) ^ ((d + 1) * (k + 1)) * tail k) := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_iUnion_le _) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hbnn hsum]
    exact ENNReal.tsum_le_tsum hlevel
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rw [ENNReal.toReal_ofReal (tsum_nonneg hbnn)] at htoReal
  rw [measureReal_def]
  exact htoReal

/-! ## The printed conclusion off the union-bound event -/

/-- Off the union-bound event at level `t = 1`, every triadic sub-cube of `cu_n`
of scale `l ≤ n` satisfies the scalar bound `3^{-gamma(n-l)} envelopeRatio ≤ 2`
of `e.bfAm.ellip`. -/
theorem envelopeRatio_weighted_le_of_not_mem (m n : ℕ) {gamma : ℝ} (omega : ShellSeq d)
    (hgood : omega ∉ {omega : ShellSeq d | ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧
      2 * 1 * (3 : ℝ) ^ (gamma * ((n : ℝ) - (Q.scale : ℝ))) < envelopeRatio m Q omega})
    (Q : TriadicCube d) (hQ : Q.scale ≤ (n : ℤ))
    (hmem : cubeCenter Q ∈ cubeSet (originCube d (n : ℤ))) :
    (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) * envelopeRatio m Q omega ≤ 2 := by
  have hle : envelopeRatio m Q omega ≤
      2 * 1 * (3 : ℝ) ^ (gamma * ((n : ℝ) - (Q.scale : ℝ))) := by
    by_contra hcon
    exact hgood ⟨Q, hQ, hmem, not_le.1 hcon⟩
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (gamma * ((n : ℝ) - (Q.scale : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnegpos : (0 : ℝ) ≤ (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  refine (mul_le_mul_of_nonneg_left hle hnegpos).trans (le_of_eq ?_)
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  field_simp

end

end SuperdiffusionCLT.Section2.Annealed
