/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Homogenization.Probability.IndependentSums.Triangle
public import Homogenization.Besov.Poincare.Projection
public import Homogenization.Geometry.TriadicPartition

/-!
# The WLOG reduction of `p.mixing.P.three.prime`

The paper reduces the case of a large scale gap
`n < m - 10K log(ν⁻¹L)` to the bounded-gap case by "splitting
the sum into smaller subcubes ... induction on `m-n` ... and averaging", but
does not display or bound the error this reassembly accumulates from averaging
`O(3^{d(m-m̃)})` subcube `O_{Γ_σ}` bounds back up to scale `m`.

This file proves the two facts the reassembly needs.

1. **The averaging-of-Orlicz-variables lemma.** This already exists in the
   `CoarseGraining` dependency: `Homogenization.IndependentSums.
   isBigO_finsetAverage_of_isBigO_gammaSigma` is exactly a bound on the
   *average* of finitely many `O_{Γ_σ}(a)}`-controlled variables by
   `O_{Γ_σ}(C(σ) a)`, with a constant `C(σ) = gammaTriangleConst σ`
   independent of how many variables are averaged (in particular independent
   of the subcube count `3^{d(m-m̃)}`). `mixMain_wlogReassembly_bilinear` below repackages this
   fact at the level of the bilinear-form sandwich shape used throughout this
   development (`e.decompose.AL.minus.Aell` and the statement of `p.mixing.P.three.prime`), combined
   with the elementary observation that a pointwise average of bilinear
   inequalities with a *common* right-hand quadratic form is again such an
   inequality with the averaged left-hand coefficient.
2. **The scale comparability that makes the reassembled bound have the right
   polynomial order.** The subcube scale is `m̃ = n + q` for the excluded-gap
   threshold `q := ⌈10K log(ν⁻¹L)⌉`; the "smaller-gap" statement applied on
   the subcubes therefore only supplies decay `O(m̃^{-3000})`, not `O(m^{-3000})`.
   The paper's claim that "averaging gives the original estimate" is only
   true because the *standing* hypothesis `m < 2n` (part of `e.mixing.gaps`,
   carried through every recursive application) forces `m < 2 m̃`, so
   `m̃^{-p} ≤ 2^p m^{-p}` for every `p ≥ 0`: the reassembled amplitude is
   `O(m^{-3000})` after all, with the fixed absolute constant `2^3000`
   absorbed into `C(d)`. `mixMain_wlogAuxScale_rpow_le` records this.

**Scope.** This file does not carry out the induction on `m - n` over the concrete lattice
partition of `cu_m` into `Homogenization.descendantsAtDepth`-subcubes of scale
`m̃`; it supplies only facts (1) and (2). The identity between the
nested averages `avg_{z ∈ cu_m}` and `avg_R avg_{z ∈ R}` is the combinatorial fact about the
cube lattice quoted below.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open scoped BigOperators

/-! ## Fact 2: the auxiliary splitting scale is comparable to `m` -/

/-- The polynomial-decay consequence of comparability: whenever `m < 2 mtilde`
and `0 ≤ p`, the decay rate `mtilde^{-p}` obtained by applying the
already-proved statement at the smaller scale `mtilde` is bounded by
`2^p` times the decay rate `m^{-p}` needed at the true scale `m`. This is the
fact that turns "the averaged bound has amplitude `O(mtilde^{-p})}`" into
"the averaged bound has amplitude `O(m^{-p})}`" with an absolute (`m`-, `n`-,
`L`-, `ν`-independent) constant. -/
theorem mixMain_wlogAuxScale_rpow_le {m mtilde : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hm : 1 ≤ m) (hlt : m < 2 * mtilde) :
    (mtilde : ℝ) ^ (-p) ≤ (2 : ℝ) ^ p * (m : ℝ) ^ (-p) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmt_pos : (0 : ℝ) < (mtilde : ℝ) := by
    have hmtnat : 0 < mtilde := by omega
    exact_mod_cast hmtnat
  have hcast : (m : ℝ) ≤ 2 * (mtilde : ℝ) := by
    have : m ≤ 2 * mtilde := le_of_lt hlt
    exact_mod_cast this
  have hpow : (m : ℝ) ^ p ≤ (2 : ℝ) ^ p * (mtilde : ℝ) ^ p := by
    calc (m : ℝ) ^ p ≤ (2 * (mtilde : ℝ)) ^ p :=
          Real.rpow_le_rpow hm_pos.le hcast hp
      _ = (2 : ℝ) ^ p * (mtilde : ℝ) ^ p := Real.mul_rpow (by norm_num) hmt_pos.le
  have hmtp_pos : 0 < (mtilde : ℝ) ^ p := Real.rpow_pos_of_pos hmt_pos p
  have hmp_pos : 0 < (m : ℝ) ^ p := Real.rpow_pos_of_pos hm_pos p
  rw [Real.rpow_neg hmt_pos.le, Real.rpow_neg hm_pos.le, inv_eq_one_div,
    show (2 : ℝ) ^ p * ((m : ℝ) ^ p)⁻¹ = (2 : ℝ) ^ p / (m : ℝ) ^ p from
      (div_eq_mul_inv _ _).symm,
    div_le_div_iff₀ hmtp_pos hmp_pos, one_mul]
  exact hpow

/-! ## Fact 1: averaging finitely many bilinear `O_{Γ_σ}` bounds with a
common right-hand quadratic form -/

/-- The generic reassembly step. If `s` is a nonempty finite index set of
"subcubes", `G p q` is a bilinear form value that does **not** depend on the
subcube (as in this development, where it is a fixed pair of annealed
quadratic forms evaluated at the parent scale `L, n`), and for every subcube
`i ∈ s` there is a measurable `X i : Ω → ℝ` with `X i = O_{Γ_σ}(a)` (the
*same* amplitude `a` for every subcube, matching the fact that every subcube
statement is obtained from the same already-proved statement at the same
parameters `m̃, n, L, ν`) satisfying the subcube-level bilinear bound
`2 * F i ω p q ≤ X i ω * G p q`, then the *averaged* coefficient
`X' ω := (s.card)⁻¹ * ∑ i ∈ s, X i ω` is measurable, is
`O_{Γ_σ}(gammaTriangleConst σ * a)` (a constant **independent of `s.card`**,
directly answering the graph's concern about the `O(3^{d(m-m̃)})` subcube
count), and the averaged bilinear bound
`2 * ((s.card)⁻¹ * ∑ i ∈ s, F i ω p q) ≤ X' ω * G p q` holds for every `ω`,
`p`, `q`. -/
theorem mixMain_wlogReassembly_bilinear {Ω ι PQ : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    (s : Finset ι) {X : ι → Ω → ℝ} {F : ι → Ω → PQ → PQ → ℝ} {G : PQ → PQ → ℝ}
    {a σ : ℝ} (hσ : 0 < σ) (hs : s.Nonempty) (ha : 0 < a)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) a)
    (hXm : ∀ i ∈ s, Measurable (X i))
    (hbound : ∀ i ∈ s, ∀ ω : Ω, ∀ p q : PQ, 2 * F i ω p q ≤ X i ω * G p q) :
    ∃ X' : Ω → ℝ, Measurable X' ∧
      IsBigO μ (gammaSigma σ) X' (gammaTriangleConst σ * a) ∧
      ∀ ω : Ω, ∀ p q : PQ,
        2 * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, F i ω p q) ≤ X' ω * G p q := by
  refine ⟨fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, X i ω, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum s hXm |>.const_mul _
  · have ha' : ∀ i ∈ s, (0:ℝ) < (fun _ : ι => a) i := fun i _ => ha
    have hraw :=
      isBigO_finsetAverage_of_isBigO_gammaSigma (μ := μ) (s := s)
        (X := X) (a := fun _ : ι => a) (σ := σ) hσ hs ha' hX hXm
    have hcard_ne : (s.card : ℝ) ≠ 0 := by
      have : 0 < s.card := Finset.card_pos.mpr hs
      exact_mod_cast this.ne'
    have hamp : gammaTriangleConst σ * ((s.card : ℝ)⁻¹ * ∑ _i ∈ s, a) =
        gammaTriangleConst σ * a := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    rwa [hamp] at hraw
  · intro ω p q
    have hcard_inv_nonneg : (0:ℝ) ≤ (s.card : ℝ)⁻¹ := by positivity
    have e1 : (s.card : ℝ)⁻¹ * ∑ i ∈ s, F i ω p q =
        ∑ i ∈ s, (s.card : ℝ)⁻¹ * F i ω p q :=
      Finset.mul_sum s (fun i => F i ω p q) (s.card : ℝ)⁻¹
    have e2 : ((s.card : ℝ)⁻¹ * ∑ i ∈ s, X i ω) * G p q =
        ∑ i ∈ s, (s.card : ℝ)⁻¹ * X i ω * G p q := by
      rw [Finset.mul_sum s (fun i => X i ω) (s.card : ℝ)⁻¹, Finset.sum_mul]
    have hstep : ∀ i ∈ s, 2 * ((s.card:ℝ)⁻¹ * F i ω p q) ≤
        (s.card:ℝ)⁻¹ * X i ω * G p q := by
      intro i hi
      have h := hbound i hi ω p q
      have h2 := mul_le_mul_of_nonneg_left h hcard_inv_nonneg
      nlinarith only [h2]
    have hsum : ∑ i ∈ s, 2 * ((s.card:ℝ)⁻¹ * F i ω p q) ≤
        ∑ i ∈ s, (s.card:ℝ)⁻¹ * X i ω * G p q :=
      Finset.sum_le_sum hstep
    have efinal : 2 * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, F i ω p q) =
        ∑ i ∈ s, 2 * ((s.card:ℝ)⁻¹ * F i ω p q) := by
      rw [e1, Finset.mul_sum]
    rw [efinal, e2]
    exact hsum

/-! ## Fact 3: the nested-average identity (the other missing ingredient)

The dependency graph's source-gap note also implicitly needs the combinatorial fact
that the outer average `avg_{z∈3^nℤ^d∩cu_m}` decomposes as the average, over
scale-`m̃` subcube blocks `R`, of the inner averages `avg_{z∈3^nℤ^d∩R}` — this
is what "splitting into smaller subcubes ... and averaging" means at the
Finset level. This is *already proved* in the `CoarseGraining` dependency as
`Homogenization.descendantsAverage_add_eq_descendantsAverage_descendantsAverage`
(`Homogenization/Besov/Poincare/Projection.lean`): for `Q : TriadicCube d` and
`j n : ℕ`, `descendantsAverage Q (j+n) F = descendantsAverage Q j (fun R =>
descendantsAverage R n F)`, where `descendantsAverage Q k F := (card
(descendantsAtDepth Q k))⁻¹ * ∑_{R ∈ descendantsAtDepth Q k} F R` is
definitionally the same average used throughout this development (matching
`Section4/Mixing/TermsCombined.lean`'s `mixTerms_reassembled_avg_eq_add` and
the average `avg_{z∈3^nℤ^d∩cu_m}` of the printed statement). -/

/-- **The WLOG induction step, combinatorics and Orlicz-averaging combined.**
Fix `n ≤ m̃ ≤ m`. If, for *every* scale-`m̃` block `R` in
`descendantsAtDepth (originCube d m) (m - m̃)` (the "already proved
smaller-gap statement applied on the subcubes of scale `m̃`"), the
inner average of a bilinear form `F` is controlled by a measurable,
`O_{Γ_σ}(a)`-bounded coefficient `X R` against a *block-independent* right
side `G p q`, then the *outer* average (at the true, possibly much larger,
gap `m - n`) is controlled the same way, by the block average `X' :=
avg_R (X R)`, which is `O_{Γ_σ}(C(σ) a)` with `C(σ) = gammaTriangleConst σ`
**independent of the number of blocks** `card (descendantsAtDepth
(originCube d m) (m - m̃))` — directly answering the graph's concern. This
combines `mixMain_wlogReassembly_bilinear` (the averaging-of-Orlicz-variables
step) with the nested-average identity above (the reassembly-of-subcubes
step); together they are the two facts the paper leaves undisplayed. -/
theorem mixMain_wlogInductionStep {d : ℕ} {Ω PQ : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {n mtilde m : ℕ} (hnmt : n ≤ mtilde) (hmtm : mtilde ≤ m)
    {G : PQ → PQ → ℝ} {a σ : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    {F : Homogenization.TriadicCube d → Ω → PQ → PQ → ℝ}
    {X : Homogenization.TriadicCube d → Ω → ℝ}
    (hXm : ∀ R ∈ Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ)) (m - mtilde),
        Measurable (X R))
    (hXO : ∀ R ∈ Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ)) (m - mtilde),
        IsBigO μ (gammaSigma σ) (X R) a)
    (hbound : ∀ R ∈ Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ)) (m - mtilde),
        ∀ ω : Ω, ∀ p q : PQ,
          2 * Homogenization.descendantsAverage R (mtilde - n) (fun R' => F R' ω p q) ≤
            X R ω * G p q) :
    ∃ X' : Ω → ℝ, Measurable X' ∧ IsBigO μ (gammaSigma σ) X' (gammaTriangleConst σ * a) ∧
      ∀ ω : Ω, ∀ p q : PQ,
        2 * Homogenization.descendantsAverage (Homogenization.originCube d (m : ℤ)) (m - n)
            (fun R' => F R' ω p q) ≤
          X' ω * G p q := by
  set s := Homogenization.descendantsAtDepth (Homogenization.originCube d (m : ℤ)) (m - mtilde) with hs_def
  have hs : s.Nonempty := Homogenization.descendantsAtDepth_nonempty _ _
  obtain ⟨X', hX'm, hX'O, hX'bd⟩ :=
    mixMain_wlogReassembly_bilinear (Ω := Ω) (μ := μ) (s := s)
      (X := X) (F := fun R ω p q => Homogenization.descendantsAverage R (mtilde - n) (fun R' => F R' ω p q))
      (G := G) (a := a) (σ := σ) hσ hs ha hXO hXm hbound
  refine ⟨X', hX'm, hX'O, fun ω p q => ?_⟩
  have hcomp :
      Homogenization.descendantsAverage (Homogenization.originCube d (m : ℤ)) (m - n)
          (fun R' => F R' ω p q) =
        Homogenization.descendantsAverage (Homogenization.originCube d (m : ℤ)) (m - mtilde)
          (fun R => Homogenization.descendantsAverage R (mtilde - n) (fun R' => F R' ω p q)) := by
    rw [← Homogenization.descendantsAverage_add_eq_descendantsAverage_descendantsAverage]
    congr 1
    omega
  rw [hcomp]
  have hunfold :
      Homogenization.descendantsAverage (Homogenization.originCube d (m : ℤ)) (m - mtilde)
          (fun R => Homogenization.descendantsAverage R (mtilde - n) (fun R' => F R' ω p q)) =
        (s.card : ℝ)⁻¹ * ∑ R ∈ s, Homogenization.descendantsAverage R (mtilde - n)
          (fun R' => F R' ω p q) := rfl
  rw [hunfold]
  exact hX'bd ω p q

end SuperdiffusionCLT.Section4.Mixing
