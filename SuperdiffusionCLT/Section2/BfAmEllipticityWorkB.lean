/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.BfAmEllipticityWork

/-!
# The random minimal scale `S_{m,γ}` of `e.Smgamma.integ`

The third assertion of lemma `l.bfAm.ellip`, quoted:

> Moreover, for each `m ∈ N` and `γ ∈ (0,1)`, there exists a random minimal
> scale `S_{m,γ}` satisfying
> `S_{m,γ} = O_{Γ_γ}(C exp(C |log γ| / γ) 3^m)` such that, for every `n ∈ N`,
> `3^n ≥ S_{m,γ} ⟹ 3^{-γ(n-l)} bfE_m^{-1/2} bfA_m(z + cu_l) bfE_m^{-1/2} ≤ 2 I_{2d}`,
> `∀ l ∈ Z ∩ (-∞,n], z ∈ 3^l Z^d ∩ cu_n`.

The printed construction of `S_{m,γ}` is as follows: for every level
`n ∈ N` the probability that some triadic sub-cube `z + cu_l` of `cu_n` violates
the weighted bound at threshold `2` is at most
`exp(C |log γ| / γ) exp(-c 3^{γ(n-m)})`, the level tail `e.km.square.bound`
being summed over the `3^{d(n-l)}` sub-cubes of each scale `l ≤ n`; then `S_{m,γ}`
is the least scale above `3^m` past which no level is bad, and the amplitude of
`S_{m,γ}` follows from summing the level tail over the levels.

## What is assembled here

* `badLevel`: the level-`n` failure event, in the exact shape of the event
  of `measureReal_exists_subCube_gt_le_of_scaleTail` (the threshold `2` of the
  printed weighted bound at `t = 1`, over the triadic sub-cubes of `cu_n`).
* `measurable_envelopeRatio`, `measurableSet_badLevel`: the observables
  are measurable in the sample. The second is a countable union over
  `TriadicCube d`, which is a countable type
  (`Homogenization.instCountableTriadicCube`).
* `minScale`, `measurable_minScale`, `measureReal_minScale_gt_le`: the minimal scale built
  from the bad levels, its measurability and its tail, from the level tail.

The level tail is the single missing ingredient of `hScale`. The union bound over the sub-cubes
(`measureReal_exists_subCube_gt_le_of_scaleTail`) has an amplitude that does **not depend on the
level `n`**, because the per-cube tail `measureReal_envelopeRatio_gt_le` holds at amplitude `1`
uniformly in the cube and in `m`; the printed level tail carries the decay
`exp(-c 3^{γ(n-m)})`, which is the printed improvement of `e.km.square.bound`.

* `tsum_exp_neg_three_shift_le`: the sum over the levels of the level tail,
  `∑_j exp(-c 3^{γ(K+j)}) ≤ 2 exp(-c 3^{γK})`, from the Bernoulli bound
  `1 + γ k log 3 ≤ 3^{γ k}`.
* `hScale_of_levelTail`: **the random minimal scale**, from the level tail
  alone: `S_{m,γ}` built as the supremum of the bad levels, its measurability,
  its `Γ_γ` tail at the printed amplitude `C exp(C |log γ|/γ) 3^m` (Borel--Cantelli
  is not needed for the tail: the amplitude truncates the sum over the levels),
  and the almost-sure sub-cube clause (Borel--Cantelli over the levels).
* `bfAmEllipticity_of_levelTail`: the printed ellipticity conclusion, with the level tail as
  its only hypothesis, obtained by applying `bfAmEllipticity_of_minimalScale` to
  `hScale_of_levelTail`.

DIMENSION ONE IS OUT OF SCOPE. `NeZero d` is never assumed; where the block
statement needs it, it is derived from `ShellLawPrefix.dimension`, exactly as in
the statement.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

variable {d : ℕ}

/-! ## The bad-level event of `e.Smgamma.integ` -/

/-- **The level-`n` failure event of `e.Smgamma.integ`** (the proof of `l.bfAm.ellip`): some
triadic sub-cube `z + cu_l` of `cu_n`, of any scale `l ≤ n`, satisfies
`3^{-γ(n-l)} bfE_m^{-1/2} bfA_m(z + cu_l) bfE_m^{-1/2} ≰ 2 I_{2d}`, read through
the scalar factor `envelopeRatio` at the printed threshold `2 t 3^{γ(n-l)}`
with `t = 1`. The displayed `2 * 1 * ...` is the normalisation of that
threshold. -/
def badLevel (d : ℕ) (m : ℕ) (gamma : ℝ) (n : ℕ) (omega : ShellSeq d) : Prop :=
  ∃ Q : TriadicCube d, Q.scale ≤ (n : ℤ) ∧
    cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) ∧
    2 * 1 * (3 : ℝ) ^ (gamma * ((n : ℝ) - (Q.scale : ℝ))) < envelopeRatio m Q omega

/-- The scalar factor `envelopeRatio` is measurable in the shell
sequence, for every cube and every cutoff scale. -/
theorem measurable_envelopeRatio (m : ℕ) (Q : TriadicCube d) :
    Measurable (fun omega : ShellSeq d ↦ envelopeRatio m Q omega) :=
  measurable_const.max
    ((measurable_volumeAverage_sq_streamCutoff (d := d) m (openCubeSet Q)).div_const
      (cutoffEnvelopeConst d * max 1 (m : ℝ)))

/-- The level-`n` failure event is measurable in the sample: it is a countable
union over the triadic cubes. -/
theorem measurableSet_badLevel (m n : ℕ) (gamma : ℝ) :
    MeasurableSet {omega : ShellSeq d | badLevel d m gamma n omega} := by
  have hset : {omega : ShellSeq d | badLevel d m gamma n omega} =
      ⋃ Q ∈ {Q : TriadicCube d |
          Q.scale ≤ (n : ℤ) ∧ cubeCenter Q ∈ cubeSet (originCube d (n : ℤ))},
        {omega : ShellSeq d |
          2 * 1 * (3 : ℝ) ^ (gamma * ((n : ℝ) - (Q.scale : ℝ))) <
            envelopeRatio m Q omega} := by
    ext omega
    constructor
    · rintro ⟨Q, hQscale, hQmem, hQgt⟩
      exact Set.mem_iUnion.2 ⟨Q, Set.mem_iUnion.2 ⟨⟨hQscale, hQmem⟩, hQgt⟩⟩
    · intro h
      obtain ⟨Q, hQmem⟩ := Set.mem_iUnion.1 h
      obtain ⟨hQs, hgt⟩ := Set.mem_iUnion.1 hQmem
      exact ⟨Q, hQs.1, hQs.2, hgt⟩
  rw [hset]
  refine MeasurableSet.biUnion (Set.Countable.mono (Set.subset_univ _) Set.countable_univ) ?_
  intro Q _
  exact measurableSet_lt measurable_const (measurable_envelopeRatio m Q)

/-! ## The union bound, read as a level tail -/

/-! ## The level sums -/

/-- **The Bernoulli bound for the level decay**: `1 + γ k log 3 ≤ 3^{γ k}`. It is
what turns the printed level decay `exp(-c 3^{γ(n-m)})` into a geometric series
in the level difference `n - m`. -/
theorem one_add_mul_log_three_le_rpow {gamma : ℝ} (hg0 : 0 < gamma) (k : ℕ) :
    1 + gamma * (k : ℝ) * Real.log 3 ≤ (3 : ℝ) ^ (gamma * (k : ℝ)) := by
  have h3g : (1 : ℝ) < (3 : ℝ) ^ gamma := Real.one_lt_rpow (by norm_num) hg0
  have hbern : 1 + (k : ℝ) * ((3 : ℝ) ^ gamma - 1) ≤
      (1 + ((3 : ℝ) ^ gamma - 1)) ^ k :=
    one_add_mul_le_pow (a := (3 : ℝ) ^ gamma - 1) (by linarith only [h3g]) k
  have hpow : 1 + (k : ℝ) * ((3 : ℝ) ^ gamma - 1) ≤ ((3 : ℝ) ^ gamma) ^ k := by
    have hbase : 1 + ((3 : ℝ) ^ gamma - 1) = (3 : ℝ) ^ gamma := by ring
    simpa only [hbase] using hbern
  have hexp : gamma * Real.log 3 ≤ (3 : ℝ) ^ gamma - 1 := by
    have h := Real.add_one_le_exp (gamma * Real.log 3)
    have h2 : (3 : ℝ) ^ gamma = Real.exp (gamma * Real.log 3) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), mul_comm]
    rw [h2]
    linarith only [h]
  have hrpow : (3 : ℝ) ^ (gamma * (k : ℝ)) = ((3 : ℝ) ^ gamma) ^ k := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) gamma (k : ℝ), Real.rpow_natCast]
  rw [hrpow]
  calc 1 + gamma * (k : ℝ) * Real.log 3 = 1 + (k : ℝ) * (gamma * Real.log 3) := by ring
    _ ≤ 1 + (k : ℝ) * ((3 : ℝ) ^ gamma - 1) := by
        have hmul := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg k)
        linarith only [hmul]
    _ ≤ ((3 : ℝ) ^ gamma) ^ k := hpow

/-- The level tails `exp(-c 3^{γ k})` are summable in the level difference: the
printed decay dominates the geometric sequence with ratio `exp(-c γ log 3)`. -/
theorem summable_exp_neg_three_mul {c gamma : ℝ} (hc : 0 < c) (hg0 : 0 < gamma) :
    Summable fun k : ℕ ↦ Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ)))) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hρ0 : 0 ≤ Real.exp (-(c * gamma * Real.log 3)) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-(c * gamma * Real.log 3)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_lt_zero.2 (mul_pos (mul_pos hc hg0) hlog3)
  have hgeo : Summable fun k : ℕ ↦ Real.exp (-c) * Real.exp (-(c * gamma * Real.log 3)) ^ k :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  refine Summable.of_nonneg_of_le (fun k ↦ (Real.exp_pos _).le) (fun k ↦ ?_) hgeo
  have hbase := one_add_mul_log_three_le_rpow hg0 k
  have h1 : c * (1 + gamma * (k : ℝ) * Real.log 3) ≤ c * (3 : ℝ) ^ (gamma * (k : ℝ)) :=
    mul_le_mul_of_nonneg_left hbase hc.le
  have h2 : -(c * (3 : ℝ) ^ (gamma * (k : ℝ))) ≤
      -(c * (1 + gamma * (k : ℝ) * Real.log 3)) := neg_le_neg h1
  have h3 : -(c * (1 + gamma * (k : ℝ) * Real.log 3)) =
      -c + (k : ℝ) * -(c * gamma * Real.log 3) := by ring
  calc Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ))))
      ≤ Real.exp (-c + (k : ℝ) * -(c * gamma * Real.log 3)) := by
        rw [h3] at h2
        exact Real.exp_le_exp.2 h2
    _ = Real.exp (-c) * Real.exp (-(c * gamma * Real.log 3)) ^ k := by
        rw [Real.exp_add, Real.exp_nat_mul]

/-- **The sum of the level tail from a threshold on**: for `A ≥ 0` with
`1 ≤ c A γ log 3`, the decay `exp(-c A 3^{γ j})` sums to at most
`2 exp(-c A)`. This is the printed sum over the levels, in the shape in which
`e.Smgamma.integ` consumes it. -/
theorem tsum_exp_neg_three_mul_le {c gamma A : ℝ} (hc : 0 < c) (hg0 : 0 < gamma)
    (hA : 0 ≤ A) (hgood : 1 ≤ c * A * gamma * Real.log 3) :
    ∑' j : ℕ, Real.exp (-(c * A * (3 : ℝ) ^ (gamma * (j : ℝ)))) ≤
      2 * Real.exp (-(c * A)) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hcAγ : 0 < c * A * gamma * Real.log 3 :=
    lt_of_lt_of_le zero_lt_one hgood
  have hρ0 : 0 ≤ Real.exp (-(c * A * gamma * Real.log 3)) := (Real.exp_pos _).le
  have hρhalf : Real.exp (-(c * A * gamma * Real.log 3)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(c * A * gamma * Real.log 3)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 (by linarith only [hgood])
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      have hthree : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        linarith only [h]
      rw [Real.exp_neg]
      calc (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hthree
        _ = 1 / 2 := by norm_num
    linarith only [h1, h2]
  have hρ1 : Real.exp (-(c * A * gamma * Real.log 3)) < 1 :=
    lt_of_le_of_lt hρhalf (by norm_num)
  have hgeo : Summable fun j : ℕ ↦ Real.exp (-(c * A)) *
      Real.exp (-(c * A * gamma * Real.log 3)) ^ j :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hmaj : ∀ j : ℕ, Real.exp (-(c * A * (3 : ℝ) ^ (gamma * (j : ℝ)))) ≤
      Real.exp (-(c * A)) * Real.exp (-(c * A * gamma * Real.log 3)) ^ j := by
    intro j
    have hbase := one_add_mul_log_three_le_rpow hg0 j
    have h1 : c * A * (1 + gamma * (j : ℝ) * Real.log 3) ≤
        c * A * (3 : ℝ) ^ (gamma * (j : ℝ)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    have h2 : -(c * A * (3 : ℝ) ^ (gamma * (j : ℝ))) ≤
        -(c * A * (1 + gamma * (j : ℝ) * Real.log 3)) := neg_le_neg h1
    have h3 : -(c * A * (1 + gamma * (j : ℝ) * Real.log 3)) =
        -c * A + (j : ℝ) * -(c * A * gamma * Real.log 3) := by ring
    calc Real.exp (-(c * A * (3 : ℝ) ^ (gamma * (j : ℝ))))
        ≤ Real.exp (-c * A + (j : ℝ) * -(c * A * gamma * Real.log 3)) := by
          rw [h3] at h2
          exact Real.exp_le_exp.2 h2
      _ = Real.exp (-(c * A)) * Real.exp (-(c * A * gamma * Real.log 3)) ^ j := by
          rw [Real.exp_add, Real.exp_nat_mul]
          congr 2
          ring
  calc ∑' j : ℕ, Real.exp (-(c * A * (3 : ℝ) ^ (gamma * (j : ℝ))))
      ≤ ∑' j : ℕ, Real.exp (-(c * A)) *
          Real.exp (-(c * A * gamma * Real.log 3)) ^ j :=
        Summable.tsum_le_tsum hmaj
          (Summable.of_nonneg_of_le (fun j ↦ (Real.exp_pos _).le) hmaj hgeo) hgeo
    _ = Real.exp (-(c * A)) *
          (1 - Real.exp (-(c * A * gamma * Real.log 3)))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ ≤ Real.exp (-(c * A)) * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have hhalf : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(c * A * gamma * Real.log 3)) := by
          linarith only [hρhalf]
        calc (1 - Real.exp (-(c * A * gamma * Real.log 3)))⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ :=
              inv_anti₀ (by norm_num) hhalf
          _ = 2 := by norm_num
    _ = 2 * Real.exp (-(c * A)) := by ring

/-- **The sum of the level tail over the levels beyond a threshold**:
`∑_j exp(-c 3^{γ(K+j)}) ≤ 2 exp(-c 3^{γ K})`. -/
theorem tsum_exp_neg_three_shift_le {c gamma : ℝ} (hc : 0 < c) (hg0 : 0 < gamma) (K : ℕ)
    (hgood : 1 ≤ c * (3 : ℝ) ^ (gamma * (K : ℝ)) * gamma * Real.log 3) :
    ∑' j : ℕ, Real.exp (-(c * (3 : ℝ) ^ (gamma * ((K + j : ℕ) : ℝ)))) ≤
      2 * Real.exp (-(c * (3 : ℝ) ^ (gamma * (K : ℝ)))) := by
  have hA : 0 ≤ (3 : ℝ) ^ (gamma * (K : ℝ)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  refine le_trans (le_of_eq (tsum_congr fun j ↦ ?_))
    (tsum_exp_neg_three_mul_le (A := (3 : ℝ) ^ (gamma * (K : ℝ))) hc hg0 hA hgood)
  rw [show gamma * ((K + j : ℕ) : ℝ) = gamma * (K : ℝ) + gamma * (j : ℝ) by
        push_cast
        ring, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring_nf

/-! ## The amplitude constant -/

/-! ## The random minimal scale -/

/-- **The random minimal scale `S_{m,γ}` of `e.Smgamma.integ`** (the proof of
`l.bfAm.ellip`): the largest of `3^m` and of the scales `3^{n+1}` over the failing
levels `n = m + k` above the cutoff. On the exceptional sample where the failing
levels are unbounded there is no finite minimal scale; there the function is set
to `0`, which can only shrink the tail `{S_{m,γ} > t}` and leaves the almost-sure
sub-cube clause intact because that sample has measure zero
(`ae_eventually_not_badLevel`). -/
def minScale (d : ℕ) (m : ℕ) (gamma : ℝ) (omega : ShellSeq d) : ℝ := by
  classical
  exact
    if ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega then
      max ((3 : ℝ) ^ m)
        (⨆ k : ℕ, if badLevel d m gamma (m + k) omega then (3 : ℝ) ^ (m + k + 1) else 0)
    else 0

/-- The sample where the failing levels are eventually absent is measurable: it
is a countable union over `N` of countable intersections over `n ≥ N`. -/
theorem measurableSet_eventually_not_badLevel (m : ℕ) (gamma : ℝ) :
    MeasurableSet {omega : ShellSeq d |
      ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega} := by
  have hset : {omega : ShellSeq d |
        ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega} =
      ⋃ N : ℕ, ⋂ n : {n : ℕ // N ≤ n},
        {omega : ShellSeq d | ¬ badLevel d m gamma (n : ℕ) omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Filter.eventually_atTop]
    constructor
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n => hN (n : ℕ) n.2⟩
    · rintro ⟨N, hN⟩
      exact ⟨N, fun n hn => hN ⟨n, hn⟩⟩
  rw [hset]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    (measurableSet_badLevel m (n : ℕ) gamma).compl

/-- **The random minimal scale is measurable in the sample**: the supremum of a
countable family of measurable step functions, cut off on a measurable set. -/
theorem measurable_minScale (m : ℕ) (gamma : ℝ) :
    Measurable (fun omega : ShellSeq d => minScale d m gamma omega) := by
  classical
  have hsup : Measurable fun omega : ShellSeq d =>
      ⨆ k : ℕ, if badLevel d m gamma (m + k) omega then (3 : ℝ) ^ (m + k + 1) else 0 :=
    Measurable.iSup fun k =>
      Measurable.ite (measurableSet_badLevel m (m + k) gamma) measurable_const
        measurable_const
  unfold minScale
  exact Measurable.ite (measurableSet_eventually_not_badLevel m gamma)
    (measurable_const.max hsup) measurable_const

/-! ## Borel--Cantelli for the levels -/

/-- **The level tails are summable.** The printed decay `exp(-c 3^{γ k})` of the
probability that the level `m + k` fails dominates a summable geometric
sequence, so `k ↦ P{level m + k fails}` is summable. -/
theorem summable_measureReal_badLevel {P : ProbabilityMeasure (ShellSeq d)} (m : ℕ) {gamma : ℝ}
    (hg0 : 0 < gamma) {Kamp C₀ c : ℝ} (hc : 0 < c) (hKamp : 0 ≤ Kamp)
    (hLevel : ∀ k : ℕ,
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} ≤
        Kamp * Real.exp (C₀ * |Real.log gamma| / gamma) *
          Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ))))) :
    Summable fun k : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} := by
  have hmaj : Summable fun k : ℕ => Kamp * Real.exp (C₀ * |Real.log gamma| / gamma) *
      Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ)))) :=
    (summable_exp_neg_three_mul hc hg0).mul_left _
  refine Summable.of_nonneg_of_le (fun k => measureReal_nonneg) (fun k => ?_) hmaj
  refine le_trans (hLevel k) ?_
  refine mul_le_mul_of_nonneg_left (le_refl _) (mul_nonneg hKamp (Real.exp_pos _).le)

/-- **The Borel--Cantelli input in `ℝ≥0∞`**: the sum of the failure probabilities
over the levels is finite, because each of them is the `ofReal` of the real
failure probability. -/
theorem tsum_measure_badLevel_ne_top {P : ProbabilityMeasure (ShellSeq d)} (m : ℕ) (gamma : ℝ)
    (hsum : Summable fun k : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega}) :
    (∑' k : ℕ, P.toMeasure {omega : ShellSeq d | badLevel d m gamma (m + k) omega}) ≠ ⊤ := by
  have hcongr : (∑' k : ℕ, P.toMeasure {omega : ShellSeq d | badLevel d m gamma (m + k) omega}) =
      ENNReal.ofReal (∑' k : ℕ,
        P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega}) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => measureReal_nonneg) hsum]
    exact tsum_congr fun k => by
      rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hcongr]
  exact ENNReal.ofReal_ne_top

/-- **Borel--Cantelli along the levels**: almost surely the levels `m + k` fail
only finitely often, i.e. the sample is in `{∀ᶠ k, ¬ badLevel (m+k)}`. -/
theorem ae_eventually_not_badLevel {P : ProbabilityMeasure (ShellSeq d)} (m : ℕ) (gamma : ℝ)
    (hsum : Summable fun k : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega}) :
    ∀ᵐ omega ∂P.toMeasure,
      ∀ᶠ k : ℕ in Filter.atTop, ¬ badLevel d m gamma (m + k) omega :=
  MeasureTheory.ae_eventually_notMem (tsum_measure_badLevel_ne_top m gamma hsum)

/-! ## The good sample and the bounds of the minimal scale -/

/-- The sample on which the failing levels are eventually absent, in the shifted
form in which the level Borel--Cantelli statement delivers it. -/
def goodShift (d : ℕ) (m : ℕ) (gamma : ℝ) : Set (ShellSeq d) :=
  {omega | ∀ᶠ k : ℕ in Filter.atTop, ¬ badLevel d m gamma (m + k) omega}

/-- The shifted form of eventual goodness is the form in which the minimal scale
is defined: the levels `m + k` from the cutoff onwards are the same levels. -/
theorem goodShift_eq_eventually_not_badLevel (m : ℕ) (gamma : ℝ) :
    goodShift d m gamma =
      {omega : ShellSeq d | ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega} := by
  ext omega
  rw [goodShift]
  simp only [Set.mem_ofPred_eq]
  rw [Filter.eventually_atTop, Filter.eventually_atTop]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨m + K, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa only [Nat.add_assoc] using hK (K + j) (Nat.le_add_right K j)
  · rintro ⟨N, hN⟩
    refine ⟨N - m, fun k hk => hN (m + k) ?_⟩
    have hbase : N ≤ m + (N - m) := by
      rcases le_or_gt m N with h | h
      · rw [Nat.add_sub_of_le h]
      · rw [Nat.sub_eq_zero_of_le h.le]
        exact h.le
    exact le_trans hbase (Nat.add_le_add_left hk m)

/-- Membership in the good sample is the unshifted eventual statement. -/
theorem mem_goodShift_iff (m : ℕ) (gamma : ℝ) (omega : ShellSeq d) :
    (omega ∈ goodShift d m gamma) ↔
      ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega := by
  rw [goodShift_eq_eventually_not_badLevel]
  simp only [Set.mem_ofPred_eq]

/-- **The good sample has full measure**, from the level Borel--Cantelli
statement. -/
theorem ae_goodShift {P : ProbabilityMeasure (ShellSeq d)} (m : ℕ) (gamma : ℝ)
    (hsum : Summable fun k : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega}) :
    ∀ᵐ omega ∂P.toMeasure, omega ∈ goodShift d m gamma :=
  ae_eventually_not_badLevel m gamma hsum

/-- **The exceptional sample is null**, in the form consumed by the union bound:
the complement of the good sample has measure zero. -/
theorem measure_compl_goodShift {P : ProbabilityMeasure (ShellSeq d)} (m : ℕ) (gamma : ℝ)
    (hsum : Summable fun k : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega}) :
    P.toMeasure (goodShift d m gamma)ᶜ = 0 := by
  have h := MeasureTheory.ae_iff.mp (ae_goodShift m gamma hsum)
  simpa only [goodShift, Set.compl_ofPred, Set.mem_ofPred_eq] using h

/-- **The minimal scale is nonnegative**, in every sample: it is a supremum of
powers of `3` cut off at `0`. -/
theorem minScale_nonneg (m : ℕ) (gamma : ℝ) (omega : ShellSeq d) :
    0 ≤ minScale d m gamma omega := by
  classical
  rw [minScale]
  split_ifs with h
  · exact le_trans (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) m) (le_max_left _ _)
  · exact le_refl 0

/-- **The minimal scale is at least `3^m`**, on the good sample. -/
theorem pow_le_minScale_of_mem_goodShift (m : ℕ) (gamma : ℝ) {omega : ShellSeq d}
    (hgood : omega ∈ goodShift d m gamma) :
    (3 : ℝ) ^ m ≤ minScale d m gamma omega := by
  classical
  have hf : ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega :=
    (mem_goodShift_iff m gamma omega).1 hgood
  rw [minScale, ite_eq_left hf]
  exact le_max_left _ _

/-- **A level above the minimal scale is a failing level.** On the good sample,
if a scale `A ≥ 3^m` lies strictly below the minimal scale then some level
`m + k` fails, and its recorded scale `3^{m+k+1}` lies strictly above `A`. -/
theorem exists_badLevel_of_lt_minScale (m N : ℕ) (gamma : ℝ) {omega : ShellSeq d}
    (hgood : omega ∈ goodShift d m gamma)
    (hN : ∀ n : ℕ, N ≤ n → ¬ badLevel d m gamma n omega)
    {A : ℝ} (hA : (3 : ℝ) ^ m ≤ A) (hlt : A < minScale d m gamma omega) :
    ∃ k : ℕ, badLevel d m gamma (m + k) omega ∧ A < (3 : ℝ) ^ (m + k + 1) := by
  classical
  have hf : ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega :=
    (mem_goodShift_iff m gamma omega).1 hgood
  rw [minScale, ite_eq_left hf] at hlt
  have hBdd : BddAbove (Set.range fun k : ℕ =>
      if badLevel d m gamma (m + k) omega then (3 : ℝ) ^ (m + k + 1) else 0) := by
    refine ⟨(3 : ℝ) ^ N, ?_⟩
    rintro _ ⟨k, rfl⟩
    dsimp only
    split_ifs with hk
    · have hltN : m + k < N := by
        by_contra hcon
        exact (hN (m + k) (not_lt.1 hcon)) hk
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
    · exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) N
  rcases lt_max_iff.1 hlt with h | h
  · exact absurd h (not_lt.2 hA)
  · obtain ⟨k, hk⟩ := (lt_ciSup_iff hBdd).1 h
    have hbad : badLevel d m gamma (m + k) omega := by
      by_contra hnb
      rw [ite_eq_right hnb] at hk
      exact absurd hk
        (not_lt.2 (le_trans (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) m) hA))
    refine ⟨k, hbad, ?_⟩
    rwa [ite_eq_left hbad] at hk

/-! ## The level sum at the printed amplitude -/

/-- **The union bound in `ℝ`, for a summable family.** For a finite measure the
sum of the real measures of a countable family dominates the real measure of its
union, provided the family is summable: that hypothesis is what keeps the right
side finite, so that the `toReal` conversion is monotone. -/
theorem measureReal_iUnion_le_of_summable {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} [IsFiniteMeasure mu] (s : ℕ → Set alpha)
    (hsum : Summable fun j : ℕ => mu.real (s j)) :
    mu.real (⋃ j, s j) ≤ ∑' j, mu.real (s j) := by
  have hfin : ∀ j : ℕ, mu (s j) ≠ ⊤ := fun j => measure_ne_top _ _
  have h1 : mu (⋃ j, s j) ≤ ∑' j, mu (s j) := measure_iUnion_le s
  have h2 : (∑' j, mu (s j)) = ENNReal.ofReal (∑' j, mu.real (s j)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => measureReal_nonneg) hsum]
    exact tsum_congr fun j => by
      rw [MeasureTheory.measureReal_def]
      exact (ENNReal.ofReal_toReal (hfin j)).symm
  have h3 : (∑' j, mu (s j)) ≠ ⊤ := by
    rw [h2]
    exact ENNReal.ofReal_ne_top
  rw [MeasureTheory.measureReal_def]
  calc (mu (⋃ j, s j)).toReal
      ≤ (∑' j, mu (s j)).toReal := ENNReal.toReal_mono h3 h1
    _ = ∑' j, mu.real (s j) := by
        rw [h2, ENNReal.toReal_ofReal (tsum_nonneg fun j => measureReal_nonneg)]

/-- **The level tail summed beyond a threshold**, at the printed amplitude. If
the level probabilities decay at the printed rate `exp(-c 3^{γ k})`, then the sum
of the shifted level probabilities is at most twice the first term. -/
theorem tsum_measureReal_badLevel_shift_le {P : ProbabilityMeasure (ShellSeq d)} (m : ℕ)
    {gamma : ℝ} (hg0 : 0 < gamma) {Kamp C₀ c : ℝ} (hc : 0 < c) (hKamp : 0 ≤ Kamp)
    (hLevel : ∀ k : ℕ,
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} ≤
        Kamp * Real.exp (C₀ * |Real.log gamma| / gamma) *
          Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ)))))
    (K : ℕ) (hgeo : 1 ≤ c * (3 : ℝ) ^ (gamma * (K : ℝ)) * gamma * Real.log 3) :
    ∑' j : ℕ,
        P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + (K + j)) omega} ≤
      Kamp * Real.exp (C₀ * |Real.log gamma| / gamma) *
        (2 * Real.exp (-(c * (3 : ℝ) ^ (gamma * (K : ℝ))))) := by
  have hmaj : Summable fun j : ℕ =>
      Real.exp (-(c * (3 : ℝ) ^ (gamma * ((K + j : ℕ) : ℝ)))) :=
    (summable_exp_neg_three_mul hc hg0).comp_injective fun a b hab => Nat.add_left_cancel hab
  have hg : Summable fun j : ℕ => Kamp * Real.exp (C₀ * |Real.log gamma| / gamma) *
      Real.exp (-(c * (3 : ℝ) ^ (gamma * ((K + j : ℕ) : ℝ)))) := hmaj.mul_left _
  have hf : Summable fun j : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + (K + j)) omega} :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg)
      (fun j => le_trans (hLevel (K + j)) (le_refl _)) hg
  calc ∑' j : ℕ,
        P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + (K + j)) omega}
      ≤ ∑' j : ℕ, Kamp * Real.exp (C₀ * |Real.log gamma| / gamma) *
          Real.exp (-(c * (3 : ℝ) ^ (gamma * ((K + j : ℕ) : ℝ)))) :=
        Summable.tsum_le_tsum (fun j => hLevel (K + j)) hf hg
    _ = (Kamp * Real.exp (C₀ * |Real.log gamma| / gamma)) *
          ∑' j : ℕ, Real.exp (-(c * (3 : ℝ) ^ (gamma * ((K + j : ℕ) : ℝ)))) :=
        tsum_mul_left
    _ ≤ (Kamp * Real.exp (C₀ * |Real.log gamma| / gamma)) *
          (2 * Real.exp (-(c * (3 : ℝ) ^ (gamma * (K : ℝ))))) :=
        mul_le_mul_of_nonneg_left (tsum_exp_neg_three_shift_le hc hg0 K hgeo)
          (mul_nonneg hKamp (Real.exp_pos _).le)

/-- **The printed amplitude to the power `γ`**: with `A = C exp(C |log γ|/γ) 3^m`
the factor `exp(C |log γ|/γ)` contributes exactly `γ^{-C}`, so
`A^γ = C^γ γ^{-C} 3^{γm} = 3^γ ((C/3)^γ γ^{-C}) 3^{γm}`. -/
theorem rpow_of_scaleAmp {Cscale gamma : ℝ} (hCs : 0 < Cscale) (hg0 : 0 < gamma)
    (hg1 : gamma ≤ 1) (m : ℕ) :
    (Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m) ^ gamma =
      ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * (3 : ℝ) ^ (gamma * (m : ℝ)) *
        (3 : ℝ) ^ gamma := by
  have hX0 : (0 : ℝ) ≤ Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) := by positivity
  have h3m0 : (0 : ℝ) ≤ (3 : ℝ) ^ m := (pow_pos (by norm_num) m).le
  rw [Real.mul_rpow hX0 h3m0, Real.mul_rpow (le_of_lt hCs) (Real.exp_pos _).le]
  have hCsplit : Cscale ^ gamma = (3 : ℝ) ^ gamma * (Cscale / 3) ^ gamma := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity : (0 : ℝ) ≤ Cscale / 3)]
    congr 1
    ring
  have hE : (Real.exp (Cscale * |Real.log gamma| / gamma)) ^ gamma = gamma ^ (-Cscale) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.rpow_def_of_pos hg0]
    congr 1
    rw [abs_of_nonpos (Real.log_nonpos hg0.le hg1)]
    field_simp
  have h3m : ((3 : ℝ) ^ m) ^ gamma = (3 : ℝ) ^ (gamma * (m : ℝ)) := by
    rw [← Real.rpow_natCast (3 : ℝ) m,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) ((m : ℕ) : ℝ) gamma, mul_comm]
  rw [hCsplit, hE, h3m]
  ring

/-- **The threshold of the minimal scale.** From `A t < 3^{m+k+1}` with the
printed amplitude `A` it follows that `(C/3)^γ γ^{-C} t^γ < 3^{γ k}`: raising to
the power `γ` and cancelling `3^γ 3^{γm}` on both sides. -/
theorem rpow_scaleAmp_mul_lt {Cscale gamma t : ℝ} (hCs : 0 < Cscale) (hg0 : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < t) {m k : ℕ}
    (hs : Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
      (3 : ℝ) ^ (m + k + 1)) :
    (Cscale / 3) ^ gamma * gamma ^ (-Cscale) * t ^ gamma <
      (3 : ℝ) ^ (gamma * (k : ℝ)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hA0 : 0 < Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m := by
    positivity
  have hAt0 : 0 < Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t :=
    mul_pos hA0 ht
  have hstep : (Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t) ^ gamma <
      ((3 : ℝ) ^ (m + k + 1)) ^ gamma := Real.rpow_lt_rpow hAt0.le hs hg0
  have hlhs : (Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t) ^ gamma =
      ((Cscale / 3) ^ gamma * gamma ^ (-Cscale) * t ^ gamma) *
        ((3 : ℝ) ^ (gamma * (m : ℝ)) * (3 : ℝ) ^ gamma) := by
    rw [Real.mul_rpow hA0.le ht.le, rpow_of_scaleAmp hCs hg0 hg1 m]
    ring
  have hrhs : ((3 : ℝ) ^ (m + k + 1)) ^ gamma =
      (3 : ℝ) ^ (gamma * (k : ℝ)) * ((3 : ℝ) ^ (gamma * (m : ℝ)) * (3 : ℝ) ^ gamma) := by
    rw [← Real.rpow_natCast (3 : ℝ) (m + k + 1),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (((m + k + 1 : ℕ) : ℝ)) gamma,
      show (((m + k + 1 : ℕ) : ℝ)) * gamma = gamma * (m : ℝ) + gamma * (k : ℝ) + gamma by
        push_cast
        ring,
      Real.rpow_add h3, Real.rpow_add h3]
    ring
  have hG0 : 0 < (3 : ℝ) ^ (gamma * (m : ℝ)) * (3 : ℝ) ^ gamma :=
    mul_pos (Real.rpow_pos_of_pos h3 _) (Real.rpow_pos_of_pos h3 _)
  rw [hlhs, hrhs] at hstep
  exact lt_of_mul_lt_mul_right hstep hG0.le

/-! ## The tail of the random minimal scale -/

/-- **The tail of the random minimal scale**, from the level tail alone. For
`γ ∈ (0,1)`, if the level probabilities decay at the printed rate with the
constant `Cscale` — the same constant that appears in the printed amplitude
`Cscale exp(Cscale |log γ|/γ) 3^m` — and if `Cscale` satisfies the two arithmetic
thresholds `hAbs` and `hGeo`, then the minimal scale exceeds
`Cscale exp(Cscale |log γ|/γ) 3^m t` with probability at most `exp(-t^γ)`.

No Borel--Cantelli is used here: the threshold `t` determines a first level above
the truncated amplitude, and the sum over the levels is truncated there, which is
exactly the printed amplitude of `S_{m,γ}`. -/
theorem measureReal_minScale_gt_le {P : ProbabilityMeasure (ShellSeq d)} (m : ℕ) {gamma : ℝ}
    (hg0 : 0 < gamma) (hg1 : gamma < 1) {Cscale c : ℝ} (hc : 0 < c) (hCscale : 3 ≤ Cscale)
    (hLevel : ∀ k : ℕ,
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} ≤
        Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
          Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ)))))
    (hAbs : 1 + Real.log 2 + Real.log Cscale + Cscale * |Real.log gamma| / gamma ≤
      c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)))
    (hGeo : 1 ≤ c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * gamma * Real.log 3) :
    ∀ t : ℝ, 1 ≤ t →
      P.toMeasure.real {omega : ShellSeq d |
        Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
          minScale d m gamma omega} ≤ Real.exp (-(t ^ gamma)) := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hCspos : 0 < Cscale := by linarith only [hCscale]
  have hsum : Summable fun k : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} :=
    summable_measureReal_badLevel (d := d) m hg0 hc (by linarith only [hCscale]) hLevel
  have hG0 : P.toMeasure (goodShift d m gamma)ᶜ = 0 := measure_compl_goodShift m gamma hsum
  have hGre : P.toMeasure.real (goodShift d m gamma)ᶜ = 0 := by
    rw [MeasureTheory.measureReal_def, hG0]
    simp
  have hApos : 0 < Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m := by
    positivity
  have hA : (3 : ℝ) ^ m ≤
      Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t := by
    have hCs1 : 1 ≤ Cscale := by linarith only [hCscale]
    have hexp1 : 1 ≤ Real.exp (Cscale * |Real.log gamma| / gamma) :=
      Real.one_le_exp (by positivity)
    have hmul : 1 ≤ Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) :=
            mul_le_mul hCs1 hexp1 zero_le_one (by linarith only [hCs1])
    calc (3 : ℝ) ^ m = 1 * (3 : ℝ) ^ m := by ring
      _ ≤ Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right hmul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) m)
      _ ≤ Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t :=
          le_mul_of_one_le_right hApos.le ht
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ,
      Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
        (3 : ℝ) ^ N₀ :=
    pow_unbounded_of_one_lt _ (by norm_num : (1 : ℝ) < 3)
  have hex : ∃ k : ℕ,
      Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
        (3 : ℝ) ^ (m + k + 1) :=
    ⟨N₀, lt_of_lt_of_le hN₀ (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega))⟩
  set K : ℕ := Nat.find hex with hKdef
  have hk₀ : Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
      (3 : ℝ) ^ (m + K + 1) := by
    rw [hKdef]
    exact Nat.find_spec hex
  have hk₀min : ∀ k : ℕ,
      Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
        (3 : ℝ) ^ (m + k + 1) → K ≤ k := by
    intro k hk
    rw [hKdef]
    exact Nat.find_min' hex hk
  have hsumK : Summable fun j : ℕ =>
      P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + (K + j)) omega} :=
    Summable.comp_injective
      (f := fun k : ℕ => P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega})
      (i := fun j : ℕ => K + j) hsum (fun a b hab => Nat.add_left_cancel hab)
  have hsubset : {omega : ShellSeq d |
        Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
          minScale d m gamma omega} ⊆
      (goodShift d m gamma)ᶜ ∪ ⋃ j : ℕ, {omega : ShellSeq d |
        badLevel d m gamma (m + (K + j)) omega} := by
    intro omega homega
    by_cases hgood : omega ∈ goodShift d m gamma
    · right
      have hf : ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega :=
        (mem_goodShift_iff m gamma omega).1 hgood
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hf
      obtain ⟨k, hbad, hlt⟩ :=
        exists_badLevel_of_lt_minScale (d := d) m N gamma hgood hN hA homega
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (hk₀min k hlt)
      exact Set.mem_iUnion.2 ⟨j, by rwa [hj] at hbad⟩
    · exact Or.inl hgood
  have hgeoK : 1 ≤ c * (3 : ℝ) ^ (gamma * (K : ℝ)) * gamma * Real.log 3 := by
    have hFlt : (Cscale / 3) ^ gamma * gamma ^ (-Cscale) <
        (3 : ℝ) ^ (gamma * (K : ℝ)) := by
      have hFA := rpow_scaleAmp_mul_lt hCspos hg0 hg1.le ht0 hk₀
      have htr : 1 ≤ t ^ gamma := Real.one_le_rpow ht hg0.le
      have hF0 : 0 ≤ (Cscale / 3) ^ gamma * gamma ^ (-Cscale) := by positivity
      calc (Cscale / 3) ^ gamma * gamma ^ (-Cscale)
          = (Cscale / 3) ^ gamma * gamma ^ (-Cscale) * 1 := by ring
        _ ≤ (Cscale / 3) ^ gamma * gamma ^ (-Cscale) * t ^ gamma :=
            mul_le_mul_of_nonneg_left htr hF0
        _ < (3 : ℝ) ^ (gamma * (K : ℝ)) := hFA
    have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hstep : c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * gamma * Real.log 3 ≤
        c * (3 : ℝ) ^ (gamma * (K : ℝ)) * gamma * Real.log 3 := by
      have h1 : c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) ≤
          c * (3 : ℝ) ^ (gamma * (K : ℝ)) := (mul_lt_mul_of_pos_left hFlt hc).le
      have h2 : c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * gamma ≤
          c * (3 : ℝ) ^ (gamma * (K : ℝ)) * gamma := mul_le_mul_of_nonneg_right h1 hg0.le
      exact mul_le_mul_of_nonneg_right h2 hlog3.le
    linarith only [hGeo, hstep]
  have hfinal : Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
      (2 * Real.exp (-(c * (3 : ℝ) ^ (gamma * (K : ℝ))))) ≤ Real.exp (-(t ^ gamma)) := by
    have hkey : t ^ gamma +
        (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2) ≤
        c * (3 : ℝ) ^ (gamma * (K : ℝ)) := by
      have h1 : 1 + (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2) ≤
          c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) := by linarith only [hAbs]
      have hstuff0 : 0 ≤ Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2 := by
        have ha : 0 ≤ Real.log Cscale := Real.log_nonneg (by linarith only [hCscale])
        have hb : 0 ≤ Cscale * |Real.log gamma| / gamma := by positivity
        have hd : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith only [ha, hb, hd]
      have htr : 1 ≤ t ^ gamma := Real.one_le_rpow ht hg0.le
      have h2 : (1 + (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2)) *
            t ^ gamma ≤
          c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * t ^ gamma :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le gamma)
      have h3 : t ^ gamma +
            (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2) ≤
          (1 + (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2)) *
            t ^ gamma := by
        have h4 : (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2) ≤
            (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2) * t ^ gamma := by
          calc (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2)
              = (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2) * 1 := by ring
            _ ≤ (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2) * t ^ gamma :=
                mul_le_mul_of_nonneg_left htr hstuff0
        linarith only [h4]
      have h5 : c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * t ^ gamma <
          c * (3 : ℝ) ^ (gamma * (K : ℝ)) := by
        have hFA := rpow_scaleAmp_mul_lt hCspos hg0 hg1.le ht0 hk₀
        have hassoc : c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale) * t ^ gamma) =
            c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * t ^ gamma := by ring
        have h6 : c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale) * t ^ gamma) <
            c * (3 : ℝ) ^ (gamma * (K : ℝ)) := mul_lt_mul_of_pos_left hFA hc
        linarith only [h6, hassoc]
      linarith only [h2, h3, h5]
    have hexpand : Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
        (2 * Real.exp (-(c * (3 : ℝ) ^ (gamma * (K : ℝ))))) =
        Real.exp (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2 +
          -(c * (3 : ℝ) ^ (gamma * (K : ℝ)))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add,
        Real.exp_log hCspos, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
          (2 * Real.exp (-(c * (3 : ℝ) ^ (gamma * (K : ℝ)))))
        = Real.exp (Real.log Cscale + Cscale * |Real.log gamma| / gamma + Real.log 2 +
            -(c * (3 : ℝ) ^ (gamma * (K : ℝ)))) := hexpand
      _ ≤ Real.exp (-(t ^ gamma)) := by
          refine Real.exp_le_exp.2 ?_
          linarith only [hkey]
  calc P.toMeasure.real {omega : ShellSeq d |
        Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
          minScale d m gamma omega}
      ≤ P.toMeasure.real ((goodShift d m gamma)ᶜ ∪ ⋃ j : ℕ, {omega : ShellSeq d |
          badLevel d m gamma (m + (K + j)) omega}) :=
        MeasureTheory.measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ P.toMeasure.real (goodShift d m gamma)ᶜ +
        P.toMeasure.real (⋃ j : ℕ, {omega : ShellSeq d |
          badLevel d m gamma (m + (K + j)) omega}) :=
        MeasureTheory.measureReal_union_le _ _
    _ = P.toMeasure.real (⋃ j : ℕ, {omega : ShellSeq d |
          badLevel d m gamma (m + (K + j)) omega}) := by rw [hGre, zero_add]
    _ ≤ ∑' j : ℕ, P.toMeasure.real {omega : ShellSeq d |
          badLevel d m gamma (m + (K + j)) omega} :=
        measureReal_iUnion_le_of_summable
          (fun j : ℕ => {omega : ShellSeq d | badLevel d m gamma (m + (K + j)) omega}) hsumK
    _ ≤ Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
          (2 * Real.exp (-(c * (3 : ℝ) ^ (gamma * (K : ℝ))))) :=
        tsum_measureReal_badLevel_shift_le m hg0 hc (by linarith only [hCscale]) hLevel K hgeoK
    _ ≤ Real.exp (-(t ^ gamma)) := hfinal

/-! ## The random minimal scale from the level tail -/

/-- **A failing level forces the minimal scale above it** on the good sample: the
recorded scale `3^{m+k+1}` is dominated by the supremum and hence by the minimal
scale. The family is bounded above by `3^N` for any level `N` past which the
levels stop failing. -/
theorem pow_le_minScale_of_badLevel (m k N : ℕ) (gamma : ℝ) {omega : ShellSeq d}
    (hgood : omega ∈ goodShift d m gamma)
    (hN : ∀ n : ℕ, N ≤ n → ¬ badLevel d m gamma n omega)
    (hbad : badLevel d m gamma (m + k) omega) :
    (3 : ℝ) ^ (m + k + 1) ≤ minScale d m gamma omega := by
  classical
  have hf : ∀ᶠ n : ℕ in Filter.atTop, ¬ badLevel d m gamma n omega :=
    (mem_goodShift_iff m gamma omega).1 hgood
  have hbdd : BddAbove (Set.range fun j : ℕ =>
      if badLevel d m gamma (m + j) omega then (3 : ℝ) ^ (m + j + 1) else 0) := by
    refine ⟨(3 : ℝ) ^ N, ?_⟩
    rintro _ ⟨j, rfl⟩
    dsimp only
    split_ifs with hj
    · have hltN : m + j < N := by
        by_contra hcon
        exact (hN (m + j) (not_lt.1 hcon)) hj
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
    · exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) N
  have hle : (3 : ℝ) ^ (m + k + 1) ≤
      ⨆ j : ℕ, (if badLevel d m gamma (m + j) omega then (3 : ℝ) ^ (m + j + 1) else 0) := by
    have h := le_ciSup hbdd k
    rwa [ite_eq_left hbad] at h
  rw [minScale, ite_eq_left hf]
  exact le_trans hle (le_max_right _ _)

/-- **Off the failing event at the threshold `2`**, every triadic sub-cube of
`cu_n` satisfies the printed weighted bound. This is
`envelopeRatio_weighted_le_of_not_mem`, read through the failing event
`badLevel`. -/
theorem subCube_bound_of_not_badLevel (m n : ℕ) (gamma : ℝ) (omega : ShellSeq d)
    (h : ¬ badLevel d m gamma n omega) :
    ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
      cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
        (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) * envelopeRatio m Q omega ≤ 2 :=
  fun Q hQ hmem =>
    SuperdiffusionCLT.Section2.Annealed.envelopeRatio_weighted_le_of_not_mem
      m n omega (by simpa only [badLevel, Set.mem_ofPred_eq] using h) Q hQ hmem

/-- **On the good sample the sub-cube clause holds at every level above the
minimal scale.** If `minScale ≤ 3^n` then the level `n` does not fail: either
`n < m`, where `minScale ≥ 3^m > 3^n` contradicts the hypothesis, or `n = m + k`,
where a failing level would force `minScale ≥ 3^{m+k+1} > 3^n`. -/
theorem goodShift_implies_subCube_bound (m : ℕ) (gamma : ℝ) {omega : ShellSeq d}
    (hgood : omega ∈ goodShift d m gamma) :
    ∀ n : ℕ, minScale d m gamma omega ≤ (3 : ℝ) ^ n →
      ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
          (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) * envelopeRatio m Q omega ≤ 2 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((mem_goodShift_iff m gamma omega).1 hgood)
  intro n hn
  have hnb : ¬ badLevel d m gamma n omega := by
    intro hbad
    rcases lt_or_ge n m with hnm | hmn
    · have h1 : (3 : ℝ) ^ n < (3 : ℝ) ^ m :=
        pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 3) hnm
      have h2 : (3 : ℝ) ^ m ≤ minScale d m gamma omega :=
        pow_le_minScale_of_mem_goodShift m gamma hgood
      linarith only [hn, h1, h2]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have h1 : (3 : ℝ) ^ (m + k + 1) ≤ minScale d m gamma omega :=
        pow_le_minScale_of_badLevel m k N gamma hgood hN hbad
      have h2 : (3 : ℝ) ^ (m + k) < (3 : ℝ) ^ (m + k + 1) :=
        pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 3) (Nat.lt_succ_self _)
      linarith only [hn, h1, h2]
  exact subCube_bound_of_not_badLevel m n gamma omega hnb

/-- **The random minimal scale `S_{m,γ}`, from the level tail alone.** This is the
statement `hScale` of `BfAmEllipticityWork.lean` verbatim, with one further
hypothesis: the printed level tail `e.km.square.bound` at the constant `Cscale`,
whose absence is the single missing ingredient of `hScale`. The witness is the
random minimal scale `minScale d m gamma` of `e.Smgamma.integ`.

The amplitude clause is `measureReal_minScale_gt_le`, which exhibits `Cscale` as
the amplitude constant; the almost-sure clause is Borel--Cantelli over the levels
(`ae_goodShift`) together with `goodShift_implies_subCube_bound`. -/
theorem hScale_of_levelTail (d : ℕ) (Cscale c : ℝ) (hCscale : 3 ≤ Cscale) (hc : 0 < c)
    (hAbs : ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      1 + Real.log 2 + Real.log Cscale + Cscale * |Real.log gamma| / gamma ≤
        c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)))
    (hGeo : ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      1 ≤ c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * gamma * Real.log 3)
    (hLevel : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ (m : ℕ) (gamma : ℝ), 0 < gamma → gamma < 1 →
          ∀ k : ℕ,
            P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} ≤
              Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
                Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ))))) :
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ (m : ℕ) (gamma : ℝ), 0 < gamma → gamma < 1 →
          ∃ S : ShellSeq d → ℝ,
            Measurable S ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma gamma) S
                (Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
                  (3 : ℝ) ^ m) ∧
              ∀ᵐ omega ∂P.toMeasure, ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
                  cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
                    (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) *
                      envelopeRatio m Q omega ≤ 2 := by
  intro nu hnu0 hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m gamma hg0 hg1
  have htail := hLevel nu hnu0 hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m gamma hg0 hg1
  refine ⟨minScale d m gamma, measurable_minScale m gamma, ?_, ?_⟩
  · unfold IndependentSums.IsBigO IndependentSums.IsBigOWith
    intro t ht
    have h := measureReal_minScale_gt_le (P := P) m hg0 hg1 hc hCscale htail
      (hAbs gamma hg0 hg1) (hGeo gamma hg0 hg1) t ht
    have hset : {omega : ShellSeq d |
          Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
            |minScale d m gamma omega|} =
        {omega : ShellSeq d |
          Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) * (3 : ℝ) ^ m * t <
            minScale d m gamma omega} := by
      ext omega
      simp only [Set.mem_ofPred_eq]
      rw [abs_of_nonneg (minScale_nonneg m gamma omega)]
    simp only [IndependentSums.upperTailEvent, hset, IndependentSums.gammaSigma,
      ← Real.exp_neg]
    exact h
  · have hsum : Summable fun k : ℕ =>
        P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} :=
      summable_measureReal_badLevel (d := d) m hg0 hc (by linarith only [hCscale]) htail
    exact (ae_goodShift (P := P) m gamma hsum).mono fun omega hgood =>
      goodShift_implies_subCube_bound (d := d) m gamma hgood

/-- **The printed ellipticity conclusion, from the level tail
alone**: `bfAmEllipticity_of_minimalScale` applied to
`hScale_of_levelTail`, so the level tail is the only hypothesis and `Cscale` is
the exhibited amplitude constant. -/
theorem bfAmEllipticity_of_levelTail (d : ℕ) (Cscale c : ℝ) (hCscale : 3 ≤ Cscale)
    (hc : 0 < c)
    (hAbs : ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      1 + Real.log 2 + Real.log Cscale + Cscale * |Real.log gamma| / gamma ≤
        c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)))
    (hGeo : ∀ gamma : ℝ, 0 < gamma → gamma < 1 →
      1 ≤ c * ((Cscale / 3) ^ gamma * gamma ^ (-Cscale)) * gamma * Real.log 3)
    (hLevel : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ (m : ℕ) (gamma : ℝ), 0 < gamma → gamma < 1 →
          ∀ k : ℕ,
            P.toMeasure.real {omega : ShellSeq d | badLevel d m gamma (m + k) omega} ≤
              Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
                Real.exp (-(c * (3 : ℝ) ^ (gamma * (k : ℝ))))) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m : ℕ,
            (∀ U : Homogenization.Book.Ch02.Domain d,
                Measurable
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                      SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                        (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                          (Homogenization.coarseBlockMatrix
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                omega m).toCoeffField))) ∧
                Homogenization.IndependentSums.IsBigOWith P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma 1)
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                    SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (Homogenization.coarseBlockMatrix
                          (U : Set (Homogenization.Vec d))
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                              omega m).toCoeffField)))
                  1) ∧
              (∀ n : ℕ,
                  Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Carriers.annealedBlockMatInfinite
                          nu m P))
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ))))) ∧
                    Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ)))))
                      (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (∀ gamma : ℝ, 0 < gamma → gamma < 1 →
                  ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable S ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma gamma) S
                        (C * Real.exp (C * |Real.log gamma| / gamma) *
                          (3 : ℝ) ^ m) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                        ∀ Q : Homogenization.TriadicCube d, Q.scale ≤ (n : ℤ) →
                          Homogenization.cubeCenter Q ∈
                              Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ)) →
                            Homogenization.BlockMatLoewnerLE
                              (((3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ))))) •
                                SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                                  (Homogenization.coarseBlockMatrix
                                    (Homogenization.cubeSet Q)
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                        omega m).toCoeffField))
                              ((2 : ℝ) • Homogenization.Book.Ch02.blockIdentity d)) :=
  bfAmEllipticity_of_minimalScale d Cscale
    (hScale_of_levelTail d Cscale c hCscale hc hAbs hGeo hLevel)
