/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsC
public import Homogenization.Probability.IndependentSums.Rosenthal.Corollaries
public import Mathlib.Algebra.Order.Chebyshev

/-!
# `l.RHS.term3`, fourth block: block concentration and the averaged quadratic tail

The last two of the four
displays that Step 3 of the proof of `l.RHS.term3` combines into
`e.bL.to.bhomell`.

* `block_concentration` is `l.RHS.term3#block-concentration`: the centered coarse blocks
  `Y_z^{(i)}` on the fine lattice have
  range of dependence `C3^ℓ`, so the lattice splits into `O(3^{d(ℓ-n)})`
  sublattices on each of which the family is independent; Rosenthal's
  polynomial-moment inequality on each sublattice and a Cauchy-Schwarz sum over
  the sublattices give the `3^{-d(k-ℓ)/2}` decay of the second moment of the
  lattice average.
* `averaged_quadratic_tail` is `l.RHS.term3#averaged-quadratic-tail`: the one-sided part
  of `l.mixing.minscale` on each translate
  bounds `σ_{L',*}^{-1}(z+cu_n)` by `σ̄_{L',*}^{-1}(cu_{m-2h})Id` plus a `Γ₂`
  error, the balanced part of the same lemma bounds the averaged stream tail,
  and `e.nablaw.Lt`, `|p|² = σ̄_{L',*}^{-1}(cu_n)`, `e.p-bound-crude` and the
  pigeonhole comparability close the display.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-! ## Elementary real inequalities -/

/-- Subadditivity of the square root, `√(x+y) ≤ √x + √y` for nonnegative
arguments: the elementary step that splits the square root of
`e.bL.to.bhomell` into its `σ̄` part and its polynomial part. -/
theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hx' : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hy' : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hxy : 0 ≤ Real.sqrt x * Real.sqrt y :=
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  have hexp : (Real.sqrt x + Real.sqrt y) ^ 2 = x + y + 2 * (Real.sqrt x * Real.sqrt y) := by
    rw [add_sq, hx', hy']; ring
  have hle : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by linarith only [hexp, hxy]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (by positivity)

/-- The scaled arithmetic-geometric mean inequality `2uv ≤ λu² + λ⁻¹v²`. -/
private theorem two_mul_le_scaled_add_sq {lam u v : ℝ} (hlam : 0 < lam) :
    2 * (u * v) ≤ lam * u ^ 2 + lam⁻¹ * v ^ 2 := by
  have hkey : lam * u ^ 2 + lam⁻¹ * v ^ 2 - 2 * (u * v) = lam⁻¹ * (lam * u - v) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ lam⁻¹ * (lam * u - v) ^ 2 :=
    mul_nonneg (inv_nonneg.2 hlam.le) (sq_nonneg _)
  linarith only [hkey, hnn]

/-! ## Moments of a `Γ_σ`-tailed observable -/

/-- The `p`-th absolute moment of a `Γ_σ`-tailed observable, in the
Chapter 4 form `∫|X|^p ≤ (gammaMomentConst σ · p^{1/σ} · A)^p`, with the
integrand written as a natural power. -/
private theorem integral_abs_pow_le_of_isBigO_gammaSigma {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {A sigma : ℝ} {p : ℕ} (hsigma : 0 < sigma) (hA : 0 < A)
    (hp : 1 ≤ p) (hXm : Measurable X)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X A) :
    ∫ omega, |X omega| ^ p ∂mu ≤
      (IndependentSums.gammaMomentConst sigma * ((p : ℝ)) ^ sigma⁻¹ * A) ^ p := by
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h := IndependentSums.integral_abs_rpow_le_of_isBigO_gammaSigma
    (μ := mu) (X := X) (K := A) (σ := sigma) (p := (p : ℝ)) hsigma hA hp'
    hXm.aemeasurable hX
  have hfun : (fun omega => |X omega| ^ ((p : ℕ) : ℝ)) = fun omega => |X omega| ^ p := by
    funext omega
    exact Real.rpow_natCast _ p
  have hconst : (IndependentSums.gammaMomentConst sigma * ((p : ℝ)) ^ sigma⁻¹ * A) ^ ((p : ℕ) : ℝ) =
      (IndependentSums.gammaMomentConst sigma * ((p : ℝ)) ^ sigma⁻¹ * A) ^ p :=
    Real.rpow_natCast _ p
  rw [hfun, hconst] at h
  exact h

/-- Integrability of the `p`-th absolute power of a `Γ_σ`-tailed observable. -/
private theorem integrable_abs_pow_of_isBigO_gammaSigma {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {A sigma : ℝ} {p : ℕ} (hsigma : 0 < sigma) (hA : 0 < A)
    (hp : 1 ≤ p) (hXm : Measurable X)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X A) :
    Integrable (fun omega => |X omega| ^ p) mu := by
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hXabs : Measurable fun omega => |X omega| :=
    continuous_abs.measurable.comp hXm
  have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (μ := mu) (Y := fun omega => |X omega|) (K := A) (σ := sigma) (p := (p : ℝ))
    hsigma hA hp' (fun omega => abs_nonneg _)
    hXabs.aemeasurable hX
  have hfun : (fun omega => |X omega| ^ ((p : ℕ) : ℝ)) = fun omega => |X omega| ^ p := by
    funext omega
    exact Real.rpow_natCast _ p
  rwa [hfun] at h

/-- The square root of the second moment of a `Γ_σ`-tailed observable. -/
private theorem sqrt_integral_sq_le_of_isBigO_gammaSigma {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {A sigma : ℝ} (hsigma : 0 < sigma) (hA : 0 < A)
    (hXm : Measurable X)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X A) :
    Real.sqrt (∫ omega, |X omega| ^ (2 : ℕ) ∂mu) ≤
      IndependentSums.gammaMomentConst sigma * (2 : ℝ) ^ sigma⁻¹ * A := by
  have h := integral_abs_pow_le_of_isBigO_gammaSigma (p := 2) hsigma hA (by norm_num) hXm hX
  have hMnn : 0 ≤ IndependentSums.gammaMomentConst sigma * (2 : ℝ) ^ sigma⁻¹ * A := by
    have h1 : 0 < IndependentSums.gammaMomentConst sigma :=
      IndependentSums.gammaMomentConst_pos hsigma
    have h2 : (0 : ℝ) < (2 : ℝ) ^ sigma⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at h
  calc Real.sqrt (∫ omega, |X omega| ^ (2 : ℕ) ∂mu)
      ≤ Real.sqrt ((IndependentSums.gammaMomentConst sigma * (2 : ℝ) ^ sigma⁻¹ * A) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq hMnn

/-! ## `l.RHS.term3#block-concentration` -/

/-- The constant of `l.RHS.term3#block-concentration`: the `p = 2` case of the
Rosenthal polynomial-moment corollary times the `Γ₁` second-moment
constant of the Chapter 4 moment calculus. -/
noncomputable def blockConcentrationConst : ℝ :=
  (4 + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt 2) *
    (2 * IndependentSums.gammaMomentConst 1)

theorem blockConcentrationConst_nonneg : (0 : ℝ) ≤ blockConcentrationConst := by
  have h1 : (0 : ℝ) < IndependentSums.rosenthalBennettIntegralConst := by
    rw [IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have h2 : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
    IndependentSums.gammaMomentConst_pos one_pos
  have h3 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have : (0 : ℝ) ≤ 4 + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt 2 := by
    positivity
  exact mul_nonneg this (by positivity)

private theorem inv_sq_mul_self_aux {x : ℝ} (hx : x ≠ 0) : x⁻¹ ^ 2 * x = x⁻¹ := by
  rw [sq, mul_assoc, inv_mul_cancel₀ hx, mul_one]

/-- **`l.RHS.term3#block-concentration`**.  For a coordinate direction `e_i` the centered
coarse blocks
`Y_z = e_i·(b_ℓ(z+cu_n) − σ̄_ℓ(cu_n))e_i`, `z ∈ 3^nℤ^d ∩ cu_k`, satisfy
`Y_z = O_{Γ₁}(Cℓν⁻¹)` and depend only on the cutoff-`ℓ` environment in a
`C3^ℓ` neighbourhood of `z + cu_n`, so the fine lattice `D` splits into
`O(3^{d(ℓ−n)})` sublattices `part j`, `j ∈ J`, on each of which the family is
independent; the conclusion is

`E[|avsum_{z∈D} Y_z|²]^{1/2} ≤ C·ℓν⁻¹·3^{−d(k−ℓ)/2}`.

The printed proof is realized as written: the Rosenthal
polynomial-moment corollary
`integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero`
(the Lean form of the paper's `p.concentration`) is applied on each sublattice
at `p = 2`, and the sublattices are summed by the Cauchy-Schwarz inequality
`(∑_j S_j)² ≤ |J|∑_j S_j²` (a sharper form of the "triangle inequality" the
paper names, with the same final rate).  The `Γ₁`-tail-to-second-moment
passage, which the paper performs silently, is
`integral_abs_rpow_le_of_isBigO_gammaSigma` and is proved here.

The hypotheses carry the printed data of the step and nothing else:

* `hUnion`, `hDisj` are the sublattice partition;
* `hIndep` is the independence *within* each sublattice, which the paper
  deduces from the range of dependence `C3^ℓ` of the family and `a.j.frd`
  (the `ShellLawJ1Restriction` restriction lane); the coarse blocks on the translated
  cubes `z + cu_n` have no carrier here, so `Y` is a free binder and the
  measurability statement of the paper's "each `Y_z` is a function only of the
  cutoff-`ℓ` environment in a `C3^ℓ` neighborhood of `z+cu_n`" reaches this
  theorem only through `hIndep`;
* `hYmean` is the centering `E[Y_z] = 0`, which the paper leaves implicit
  (`E[b_ℓ(z+cu_n)] = σ̄_ℓ(cu_n)Id` on translated cubes, i.e.
  stationarity plus the scalar reduction);
* `hYtail` is the per-variable envelope `Y_z = O_{Γ₁}(K)`, `K = Cℓν⁻¹`, which
  `l.bfAm.ellip` (`envelopeRescale_ellipticity`) and `e.Enaught.mixing`
  supply;
* `hDcard`, `hJcard` are the cardinalities `|D| = 3^{d(k−n)}` and
  `|J| ≤ C3^{d(ℓ−n)}` of the printed partition. -/
theorem block_concentration {kappa : Type*}
    (P : ProbabilityMeasure (ShellSeq d))
    (D : Finset (TriadicCube d)) (J : Finset kappa)
    (part : kappa → Finset (TriadicCube d))
    (Y : ShellSeq d → TriadicCube d → ℝ) {K CJ : ℝ} {nn ell kk : ℕ}
    (hK : 0 < K) (hCJ : 0 ≤ CJ) (hDne : D.Nonempty)
    (hUnion : D = J.biUnion part)
    (hDisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (part j) (part j'))
    (hYmeas : ∀ z, Measurable fun omega => Y omega z)
    (hYmean : ∀ z ∈ D, ∫ omega, Y omega z ∂P.toMeasure = 0)
    (hYtail : ∀ z ∈ D, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 1) (fun omega => Y omega z) K)
    (hIndep : ∀ j ∈ J, ProbabilityTheory.iIndepFun
      (fun z : {z // z ∈ part j} => fun omega : ShellSeq d => Y omega (z : TriadicCube d))
      P.toMeasure)
    (hnl : nn ≤ ell) (hlk : ell ≤ kk)
    (hDcard : (D.card : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((kk - nn : ℕ) : ℝ)))
    (hJcard : (J.card : ℝ) ≤ CJ * (3 : ℝ) ^ ((d : ℝ) * ((ell - nn : ℕ) : ℝ))) :
    Real.sqrt (∫ omega, |((D.card : ℝ))⁻¹ * ∑ z ∈ D, Y omega z| ^ (2 : ℕ) ∂P.toMeasure) ≤
      blockConcentrationConst * Real.sqrt CJ * K *
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by
  classical
  have hNpos : (0 : ℝ) < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hDne
  have hg1pos : (0 : ℝ) < IndependentSums.gammaMomentConst 1 :=
    IndependentSums.gammaMomentConst_pos one_pos
  set Kp : ℝ := 2 * IndependentSums.gammaMomentConst 1 * K with hKpdef
  have hKpnn : (0 : ℝ) ≤ Kp := by positivity
  set Cros : ℝ := 4 + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt 2
    with hCrosdef
  have hCrosnn : (0 : ℝ) ≤ Cros := by
    have h1 : (0 : ℝ) < IndependentSums.rosenthalBennettIntegralConst := by
      rw [IndependentSums.rosenthalBennettIntegralConst]; positivity
    have h3 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    rw [hCrosdef]; positivity
  have hsub : ∀ j ∈ J, part j ⊆ D := by
    intro j hj z hz
    rw [hUnion]
    exact Finset.mem_biUnion.2 ⟨j, hj, hz⟩
  -- the per-variable second moment, from the `Γ₁` envelope
  have hsqrt_eq : ∀ x : ℝ, 0 ≤ x → x ^ (1 / ((2 : ℕ) : ℝ)) = Real.sqrt x := by
    intro x _
    rw [Real.sqrt_eq_rpow]
    norm_num
  have hmom : ∀ z ∈ D,
      (∫ omega, |Y omega z| ^ (2 : ℕ) ∂P.toMeasure) ^ (1 / ((2 : ℕ) : ℝ)) ≤ Kp := by
    intro z hz
    have hnn : (0 : ℝ) ≤ ∫ omega, |Y omega z| ^ (2 : ℕ) ∂P.toMeasure :=
      MeasureTheory.integral_nonneg fun omega => by positivity
    rw [hsqrt_eq _ hnn]
    have h := sqrt_integral_sq_le_of_isBigO_gammaSigma (sigma := 1) (A := K)
      one_pos hK (hYmeas z) (hYtail z hz)
    have hrw : IndependentSums.gammaMomentConst 1 * (2 : ℝ) ^ (1 : ℝ)⁻¹ * K = Kp := by
      rw [hKpdef, inv_one, Real.rpow_one]; ring
    rwa [hrw] at h
  have hIntY : ∀ z ∈ D, Integrable (fun omega => |Y omega z| ^ (2 : ℕ)) P.toMeasure := by
    intro z hz
    exact integrable_abs_pow_of_isBigO_gammaSigma (sigma := 1) (A := K) (p := 2)
      one_pos hK (by norm_num) (hYmeas z) (hYtail z hz)
  -- Rosenthal on each sublattice
  have hpart : ∀ j ∈ J,
      Real.sqrt (∫ omega, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) ∂P.toMeasure) ≤
        Cros * Real.sqrt ((part j).card : ℝ) * Kp := by
    intro j hj
    rcases Finset.eq_empty_or_nonempty (part j) with hempty | hne
    · simp only [hempty, Finset.sum_empty, abs_zero]
      have : ((0 : ℝ)) ^ (2 : ℕ) = 0 := by norm_num
      rw [this]
      simp only [MeasureTheory.integral_zero, Real.sqrt_zero]
      have : (0 : ℝ) ≤ Real.sqrt (((part j).card : ℝ)) := Real.sqrt_nonneg _
      positivity
    obtain ⟨z0, hz0⟩ := hne
    have : Nonempty {z // z ∈ part j} := ⟨⟨z0, hz0⟩⟩
    have hs : (Finset.univ : Finset {z // z ∈ part j}).Nonempty := Finset.univ_nonempty
    have hros :=
      IndependentSums.integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
        (μ := P.toMeasure)
        (X := fun (z : {z // z ∈ part j}) (omega : ShellSeq d) => Y omega (z : TriadicCube d))
        (s := Finset.univ) (p := 2) (K := Kp) hs (by norm_num) hKpnn (hIndep j hj)
        (fun z => hYmeas _) (fun z _ => hIntY _ (hsub j hj z.2))
        (fun z _ => hYmean _ (hsub j hj z.2)) (fun z _ => hmom _ (hsub j hj z.2))
    have hsumcoe : ∀ omega : ShellSeq d,
        ∑ i ∈ (Finset.univ : Finset {z // z ∈ part j}), Y omega (i : TriadicCube d) =
          ∑ z ∈ part j, Y omega z := fun omega =>
      Finset.sum_coe_sort (part j) (fun z => Y omega z)
    have hcard : ((Finset.univ : Finset {z // z ∈ part j}).card : ℝ) = ((part j).card : ℝ) := by
      rw [Finset.card_univ, Fintype.card_coe]
    simp only [hsumcoe, hcard] at hros
    have hnn : (0 : ℝ) ≤ ∫ omega, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) ∂P.toMeasure :=
      MeasureTheory.integral_nonneg fun omega => by positivity
    rw [hsqrt_eq _ hnn] at hros
    refine hros.trans (le_of_eq ?_)
    rw [hsqrt_eq _ (by positivity : (0 : ℝ) ≤ ((part j).card : ℝ))]
    have h2 : Real.sqrt (((2 : ℕ) : ℝ)) = Real.sqrt 2 := by norm_num
    rw [h2, hCrosdef]
    push_cast
    ring
  -- integrability of the squared sublattice sums
  have hIntS : ∀ j ∈ J,
      Integrable (fun omega => |∑ z ∈ part j, Y omega z| ^ (2 : ℕ)) P.toMeasure := by
    intro j hj
    have hgi : Integrable (fun omega : ShellSeq d =>
        ((part j).card : ℝ) * ∑ z ∈ part j, |Y omega z| ^ (2 : ℕ)) P.toMeasure :=
      (MeasureTheory.integrable_finsetSum _ (fun z hz => hIntY z (hsub j hj hz))).const_mul _
    have h1 : Measurable fun omega : ShellSeq d => ∑ z ∈ part j, Y omega z :=
      Finset.measurable_sum _ (fun z _ => hYmeas z)
    have hmeas : Measurable fun omega : ShellSeq d => |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) :=
      (continuous_abs.measurable.comp h1).pow_const 2
    refine hgi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun omega => ?_)
    have hcs : (∑ z ∈ part j, Y omega z) ^ 2 ≤
        ((part j).card : ℝ) * ∑ z ∈ part j, Y omega z ^ 2 := sq_sum_le_card_mul_sum_sq
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [sq_abs]
    exact hcs
  -- the partition of the fine lattice
  have hsplit : ∀ omega : ShellSeq d,
      ∑ z ∈ D, Y omega z = ∑ j ∈ J, ∑ z ∈ part j, Y omega z := by
    intro omega
    rw [hUnion]
    exact Finset.sum_biUnion (fun j hj j' hj' hne => hDisj j hj j' hj' hne)
  have hcardsum : ∑ j ∈ J, ((part j).card : ℝ) = (D.card : ℝ) := by
    rw [hUnion, Finset.card_biUnion hDisj]
    push_cast
    rfl
  -- Cauchy-Schwarz over the sublattices
  have hchain : ∫ omega, |∑ z ∈ D, Y omega z| ^ (2 : ℕ) ∂P.toMeasure ≤
      (J.card : ℝ) * ∑ j ∈ J,
        ∫ omega, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) ∂P.toMeasure := by
    have hgi : Integrable (fun omega : ShellSeq d =>
        (J.card : ℝ) * ∑ j ∈ J, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ)) P.toMeasure :=
      (MeasureTheory.integrable_finsetSum _ (fun j hj => hIntS j hj)).const_mul _
    have hpt : ∀ omega : ShellSeq d,
        |∑ z ∈ D, Y omega z| ^ (2 : ℕ) ≤
          (J.card : ℝ) * ∑ j ∈ J, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) := by
      intro omega
      have hcs : (∑ j ∈ J, ∑ z ∈ part j, Y omega z) ^ 2 ≤
          (J.card : ℝ) * ∑ j ∈ J, (∑ z ∈ part j, Y omega z) ^ 2 := sq_sum_le_card_mul_sum_sq
      rw [hsplit omega]
      simp only [sq_abs]
      exact hcs
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun omega : ShellSeq d =>
        (by positivity : (0 : ℝ) ≤ |∑ z ∈ D, Y omega z| ^ (2 : ℕ)))
      hgi (Filter.Eventually.of_forall hpt)
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ (fun j hj => hIntS j hj)]
  -- the sublattice bounds, summed
  have hsum_le : ∑ j ∈ J, ∫ omega, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) ∂P.toMeasure ≤
      (Cros * Kp) ^ 2 * (D.card : ℝ) := by
    have hb : ∀ j ∈ J, ∫ omega, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) ∂P.toMeasure ≤
        (Cros * Kp) ^ 2 * ((part j).card : ℝ) := by
      intro j hj
      have hnn : (0 : ℝ) ≤ ∫ omega, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) ∂P.toMeasure :=
        MeasureTheory.integral_nonneg fun omega => by positivity
      have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpart j hj) 2
      rw [Real.sq_sqrt hnn] at hsq
      refine hsq.trans (le_of_eq ?_)
      have hcard : Real.sqrt ((part j).card : ℝ) ^ 2 = ((part j).card : ℝ) :=
        Real.sq_sqrt (by positivity)
      calc (Cros * Real.sqrt ((part j).card : ℝ) * Kp) ^ 2
          = (Cros * Kp) ^ 2 * Real.sqrt ((part j).card : ℝ) ^ 2 := by ring
        _ = (Cros * Kp) ^ 2 * ((part j).card : ℝ) := by rw [hcard]
    calc ∑ j ∈ J, ∫ omega, |∑ z ∈ part j, Y omega z| ^ (2 : ℕ) ∂P.toMeasure
        ≤ ∑ j ∈ J, (Cros * Kp) ^ 2 * ((part j).card : ℝ) := Finset.sum_le_sum hb
      _ = (Cros * Kp) ^ 2 * ∑ j ∈ J, ((part j).card : ℝ) := by rw [Finset.mul_sum]
      _ = (Cros * Kp) ^ 2 * (D.card : ℝ) := by rw [hcardsum]
  -- pull the normalization out of the integral
  have hpull : ∫ omega, |((D.card : ℝ))⁻¹ * ∑ z ∈ D, Y omega z| ^ (2 : ℕ) ∂P.toMeasure =
      ((D.card : ℝ))⁻¹ ^ 2 * ∫ omega, |∑ z ∈ D, Y omega z| ^ (2 : ℕ) ∂P.toMeasure := by
    have hpt : ∀ omega : ShellSeq d,
        |((D.card : ℝ))⁻¹ * ∑ z ∈ D, Y omega z| ^ (2 : ℕ) =
          ((D.card : ℝ))⁻¹ ^ 2 * |∑ z ∈ D, Y omega z| ^ (2 : ℕ) := by
      intro omega
      rw [abs_mul, mul_pow, abs_of_nonneg (le_of_lt (inv_pos.2 hNpos))]
    simp only [hpt]
    exact MeasureTheory.integral_const_mul _ _
  have hAnn : (0 : ℝ) ≤ ∫ omega, |∑ z ∈ D, Y omega z| ^ (2 : ℕ) ∂P.toMeasure :=
    MeasureTheory.integral_nonneg fun omega => by positivity
  rw [hpull, Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt (inv_pos.2 hNpos))]
  -- the cardinality ratio
  have hratio : ((D.card : ℝ))⁻¹ ^ 2 * ((J.card : ℝ) * (Cros * Kp) ^ 2 * (D.card : ℝ)) ≤
      (Cros * Kp) ^ 2 * (CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) := by
    have hE : (d : ℝ) * ((ell - nn : ℕ) : ℝ) - (d : ℝ) * ((kk - nn : ℕ) : ℝ) =
        -((d : ℝ) * ((kk - ell : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hnl, Nat.cast_sub (hnl.trans hlk), Nat.cast_sub hlk]
      ring
    have hNval : ((D.card : ℝ))⁻¹ = (3 : ℝ) ^ (-((d : ℝ) * ((kk - nn : ℕ) : ℝ))) := by
      rw [hDcard, ← Real.rpow_neg (by norm_num)]
    have hJle : (J.card : ℝ) * ((D.card : ℝ))⁻¹ ≤
        CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ))) := by
      have hposinv : (0 : ℝ) < ((D.card : ℝ))⁻¹ := inv_pos.2 hNpos
      calc (J.card : ℝ) * ((D.card : ℝ))⁻¹
          ≤ (CJ * (3 : ℝ) ^ ((d : ℝ) * ((ell - nn : ℕ) : ℝ))) * ((D.card : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hJcard hposinv.le
        _ = CJ * ((3 : ℝ) ^ ((d : ℝ) * ((ell - nn : ℕ) : ℝ)) *
              (3 : ℝ) ^ (-((d : ℝ) * ((kk - nn : ℕ) : ℝ)))) := by rw [hNval]; ring
        _ = CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ))) := by
            have hadd : (d : ℝ) * ((ell - nn : ℕ) : ℝ) + -((d : ℝ) * ((kk - nn : ℕ) : ℝ)) =
                -((d : ℝ) * ((kk - ell : ℕ) : ℝ)) := by linarith only [hE]
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hadd]
    have hCKnn : (0 : ℝ) ≤ (Cros * Kp) ^ 2 := sq_nonneg _
    have heq : ((D.card : ℝ))⁻¹ ^ 2 * ((J.card : ℝ) * (Cros * Kp) ^ 2 * (D.card : ℝ)) =
        (Cros * Kp) ^ 2 * ((J.card : ℝ) * ((D.card : ℝ))⁻¹) := by
      linear_combination ((Cros * Kp) ^ 2 * (J.card : ℝ)) * inv_sq_mul_self_aux hNpos.ne'
    rw [heq]
    exact mul_le_mul_of_nonneg_left hJle hCKnn
  have hstep : ((D.card : ℝ))⁻¹ *
      Real.sqrt (∫ omega, |∑ z ∈ D, Y omega z| ^ (2 : ℕ) ∂P.toMeasure) ≤
      ((D.card : ℝ))⁻¹ * Real.sqrt ((J.card : ℝ) * ((Cros * Kp) ^ 2 * (D.card : ℝ))) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hchain.trans
      (mul_le_mul_of_nonneg_left hsum_le (by positivity)))) (le_of_lt (inv_pos.2 hNpos))
  refine hstep.trans ?_
  have hrw : ((D.card : ℝ))⁻¹ * Real.sqrt ((J.card : ℝ) * ((Cros * Kp) ^ 2 * (D.card : ℝ))) =
      Real.sqrt (((D.card : ℝ))⁻¹ ^ 2 * ((J.card : ℝ) * (Cros * Kp) ^ 2 * (D.card : ℝ))) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ ((D.card : ℝ))⁻¹ ^ 2 by positivity)
        ((J.card : ℝ) * (Cros * Kp) ^ 2 * (D.card : ℝ)),
      Real.sqrt_sq (le_of_lt (inv_pos.2 hNpos))]
    congr 2
    ring
  rw [hrw]
  have hfinal : Real.sqrt ((Cros * Kp) ^ 2 *
      (CJ * (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ))))) =
      blockConcentrationConst * Real.sqrt CJ * K *
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by
    have h3 : Real.sqrt ((3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)))) =
        (3 : ℝ) ^ (-((d : ℝ) * ((kk - ell : ℕ) : ℝ)) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
      ring_nf
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
      Real.sqrt_mul hCJ, h3, blockConcentrationConst, hCrosdef, hKpdef]
    ring
  rw [← hfinal]
  exact Real.sqrt_le_sqrt hratio


/-! ## `l.RHS.term3#averaged-quadratic-tail` -/

/-- The pointwise square bound behind the averaged quadratic tail: a
nonnegative quantity dominated by `(a + X)S` has square dominated by
`2a²S² + λX⁴ + λ⁻¹S⁴` for every `λ > 0`. -/
private theorem quad_sq_le {a lam q X Sv : ℝ} (hlam : 0 < lam) (hq : 0 ≤ q) (hS : 0 ≤ Sv)
    (hle : q ≤ (a + X) * Sv) :
    q ^ 2 ≤ 2 * a ^ 2 * |Sv| ^ 2 + lam * |X| ^ 4 + lam⁻¹ * |Sv| ^ 4 := by
  have habs : |Sv| = Sv := abs_of_nonneg hS
  have hXle : (a + X) * Sv ≤ (a + |X|) * Sv :=
    mul_le_mul_of_nonneg_right (by linarith only [le_abs_self X]) hS
  have h2 : q ^ 2 ≤ ((a + |X|) * Sv) ^ 2 := pow_le_pow_left₀ hq (hle.trans hXle) 2
  have hring : (a + |X|) ^ 2 + (a - |X|) ^ 2 = 2 * a ^ 2 + 2 * |X| ^ 2 := by ring
  have h4 : (a + |X|) ^ 2 ≤ 2 * a ^ 2 + 2 * |X| ^ 2 := by
    linarith only [hring, sq_nonneg (a - |X|)]
  have h5 : ((a + |X|) * Sv) ^ 2 ≤ (2 * a ^ 2 + 2 * |X| ^ 2) * Sv ^ 2 := by
    have := mul_le_mul_of_nonneg_right h4 (sq_nonneg Sv)
    calc ((a + |X|) * Sv) ^ 2 = (a + |X|) ^ 2 * Sv ^ 2 := by ring
      _ ≤ (2 * a ^ 2 + 2 * |X| ^ 2) * Sv ^ 2 := this
  have h6 : 2 * (|X| ^ 2 * Sv ^ 2) ≤ lam * (|X| ^ 2) ^ 2 + lam⁻¹ * (Sv ^ 2) ^ 2 :=
    two_mul_le_scaled_add_sq hlam
  have e1 : (|X| ^ 2) ^ 2 = |X| ^ 4 := by ring
  have e2 : (Sv ^ 2) ^ 2 = Sv ^ 4 := by ring
  rw [habs]
  rw [e1, e2] at h6
  linarith only [h2, h5, h6]

/-- The main constant of `l.RHS.term3#averaged-quadratic-tail`, carrying the
`Γ₁` second-moment constant, the balanced-part amplitude `Cb` of
`l.mixing.minscale`, the `e.nablaw.Lt` constant `Cw` and the pigeonhole
comparability constant `Cpig` of `e.pigeon.scalar`. -/
noncomputable def quadTailConstMain (Cb Cw Cpig : ℝ) : ℝ :=
  2 * Real.sqrt 2 * IndependentSums.gammaMomentConst 1 * Cb * Cw * Cpig

/-- The error constant of `l.RHS.term3#averaged-quadratic-tail`, carrying in
addition the `Γ₂` fourth-moment constant and the one-sided amplitude `Cms` of
`l.mixing.minscale`. -/
noncomputable def quadTailConstError (Cms Cb Cw : ℝ) : ℝ :=
  8 * Real.sqrt 2 * IndependentSums.gammaMomentConst 1 *
    IndependentSums.gammaMomentConst 2 * Cms * Cb * Cw

/-- **`l.RHS.term3#averaged-quadratic-tail`**.

The one-sided part of `l.mixing.minscale` (the statement
`sigmaStarInv_mixing_minscale`, conjunct `e.sstarL.quenched.lb`), applied on
each translate `z + cu_n` with local lower scale `m − 2h` and local cube scale
`n`, gives
`σ_{L',*}^{-1}(z+cu_n) ≤ σ̄_{L',*}^{-1}(cu_{m−2h})Id + O_{Γ₂}(Cν⁻²3^{−(n−(m−2h))/4}Id)`;
the balanced part `e.refined.localization.twoo` of the same lemma controls the
averaged stream tail `(k_ℓ−k_{L'})_{z+cu_n}` in the `σ_{L',*}^{-1}` metric.
Testing the first against the second gives, for `z ∈ D`, the pointwise
domination `hOneSided` of the printed per-cube quadratic form by
`(σ̄_{L',*}^{-1}(cu_{m−2h}) + X_z)·streamSq_z`; `hXtail` and `hStreamTail` are
the two anchors' `Γ₂` and `Γ₁` envelopes in their exact amplitudes.  The
conclusion is the printed display

`E[|avsum_z (k_ℓ−k_{L'})ᵗσ_{L',*}^{-1}(k_ℓ−k_{L'})|²]^{1/2}E[‖∇w‖⁴_{L̲⁴(cu_m)}]^{1/2}
   ≤ C(L'−ℓ)²σ̄_{L',*}^{-1}(cu_n)² + Cν⁻³(L'−ℓ)²3^{−h/8}`.

Everything between the two is proved here: the Jensen step
`(avsum_z q_z)² ≤ avsum_z q_z²`, the pointwise square bound with the scaled
arithmetic-geometric mean inequality, the `Γ_σ`-tail-to-moment passages
(`integral_abs_rpow_le_of_isBigO_gammaSigma`), and the closing
arithmetic — `E[‖∇w‖⁴]^{1/2} ≤ Ch|p|² ≤ C(L'−ℓ)|p|²` (`hWL4`),
`|p|² = σ̄_{L',*}^{-1}(cu_n)` (`vecNormSq_testVector`, entering through
`hWL4`), `|p|² ≤ ν⁻¹` (`e.p-bound-crude`, `hcrude`) and the pigeonhole
comparability (`hPigeon`).

Three points that the paper leaves implicit are visible in the hypotheses:

* `l.mixing.minscale` is printed on `cu_n`, so its use "on each translate" is
  the translated-localization bridge; it reaches this theorem only through
  `hOneSided`, `hXtail`, `hStreamTail`, which are stated *per cube of `D`*;
* the coarsening `3^{−(h−2⌈K log(ν⁻¹L)⌉)/4} ≤ 3^{−h/8}` requires
  `h ≥ 4⌈K log(ν⁻¹L)⌉`, which the paper never states; it is the explicit
  hypothesis `hKlog` together with the scale identity `hScaleId`
  (`n − (m−2h) = h − 2⌈K log(ν⁻¹L)⌉`);
* `|p|² ≤ σ̄_{L',*}^{-1}(cu_n)` is an equality, and the passage from
  `σ̄^{-1}(cu_n)|p|²` to `σ̄^{-1}(cu_n)²` uses that identity: both are absorbed
  into `hWL4`. -/
theorem averaged_quadratic_tail [NeZero d]
    {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (D : Finset (TriadicCube d)) (hDne : D.Nonempty)
    (quad streamSq Xdev : ShellSeq d → TriadicCube d → ℝ)
    {WL4 Klog Cms Cb Cw Cpig : ℝ}
    (hCms : 0 < Cms) (hCb : 0 < Cb) (hCw : 0 ≤ Cw)
    (hell : S.ell < S.LPrime)
    (hquadNonneg : ∀ (omega : ShellSeq d) (z : TriadicCube d), 0 ≤ quad omega z)
    (hstreamNonneg : ∀ (omega : ShellSeq d) (z : TriadicCube d), 0 ≤ streamSq omega z)
    (hquadMeas : ∀ z, Measurable fun omega => quad omega z)
    (hstreamMeas : ∀ z, Measurable fun omega => streamSq omega z)
    (hXmeas : ∀ z, Measurable fun omega => Xdev omega z)
    (hOneSided : ∀ (omega : ShellSeq d), ∀ z ∈ D,
      quad omega z ≤
        (sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h) + Xdev omega z) * streamSq omega z)
    (hXtail : ∀ z ∈ D, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 2) (fun omega => Xdev omega z)
      (Cms * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4)))
    (hStreamTail : ∀ z ∈ D, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 1) (fun omega => streamSq omega z)
      (Cb * ((S.LPrime - S.ell : ℕ) : ℝ)))
    (hWL4nonneg : 0 ≤ WL4)
    (hWL4 : WL4 ^ ((1 : ℝ) / 2) ≤
      Cw * ((S.LPrime - S.ell : ℕ) : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n)
    (hsigmaNonneg : 0 ≤ sigmaBarStarInvSeq nu S.LPrime P S.n)
    (hsigmaMinus : 0 ≤ sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h))
    (hcrude : sigmaBarStarInvSeq nu S.LPrime P S.n ≤ nu⁻¹)
    (hPigeon : sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h) ≤
      Cpig * sigmaBarStarInvSeq nu S.LPrime P S.n)
    (hScaleId : (((S.n - (S.m - 2 * S.h) : ℕ)) : ℝ) = ((S.h : ℕ) : ℝ) - 2 * Klog)
    (hKlog : 4 * Klog ≤ ((S.h : ℕ) : ℝ)) :
    Real.sqrt (∫ omega, |((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z| ^ 2 ∂P.toMeasure) *
        WL4 ^ ((1 : ℝ) / 2) ≤
      quadTailConstMain Cb Cw Cpig * ((S.LPrime - S.ell : ℕ) : ℝ) ^ 2 *
          sigmaBarStarInvSeq nu S.LPrime P S.n ^ 2 +
        quadTailConstError Cms Cb Cw * nu ^ (-(3 : ℝ)) *
          ((S.LPrime - S.ell : ℕ) : ℝ) ^ 2 * (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8) := by
  classical
  have hNpos : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hDne
  have hNne : ((D.card : ℝ)) ≠ 0 := ne_of_gt hNpos
  have hLLpos : (0 : ℝ) < ((S.LPrime - S.ell : ℕ) : ℝ) := by
    have : 0 < S.LPrime - S.ell := by omega
    exact_mod_cast this
  set g1 : ℝ := IndependentSums.gammaMomentConst 1 with hg1def
  set g2 : ℝ := IndependentSums.gammaMomentConst 2 with hg2def
  have hg1pos : (0 : ℝ) < g1 := IndependentSums.gammaMomentConst_pos one_pos
  have hg2pos : (0 : ℝ) < g2 := IndependentSums.gammaMomentConst_pos two_pos
  set a : ℝ := sigmaBarStarInvSeq nu S.LPrime P (S.m - 2 * S.h) with hadef
  set AS : ℝ := Cb * ((S.LPrime - S.ell : ℕ) : ℝ) with hASdef
  set AX : ℝ := Cms * nu ^ (-(2 : ℝ)) *
    (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) with hAXdef
  have hASpos : (0 : ℝ) < AS := mul_pos hCb hLLpos
  have hAXpos : (0 : ℝ) < AX := by
    have h1 : (0 : ℝ) < nu ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hnu _
    have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact mul_pos (mul_pos hCms h1) h2
  set MX : ℝ := 2 * g2 * AX with hMXdef
  set MS4 : ℝ := 4 * g1 * AS with hMS4def
  set MS2 : ℝ := 2 * g1 * AS with hMS2def
  have hMXpos : (0 : ℝ) < MX := mul_pos (mul_pos two_pos hg2pos) hAXpos
  have hMS4pos : (0 : ℝ) < MS4 := mul_pos (mul_pos four_pos hg1pos) hASpos
  have hMS2pos : (0 : ℝ) < MS2 := mul_pos (mul_pos two_pos hg1pos) hASpos
  set lam : ℝ := MS4 ^ 2 / MX ^ 2 with hlamdef
  have hlampos : (0 : ℝ) < lam := div_pos (pow_pos hMS4pos 2) (pow_pos hMXpos 2)
  -- the three moment bounds
  have hX4 : ∀ z ∈ D, ∫ omega, |Xdev omega z| ^ 4 ∂P.toMeasure ≤ MX ^ 4 := by
    intro z hz
    have h := integral_abs_pow_le_of_isBigO_gammaSigma (sigma := 2) (A := AX) (p := 4)
      two_pos hAXpos (by norm_num) (hXmeas z) (hXtail z hz)
    have hc : g2 * (((4 : ℕ) : ℝ)) ^ (2 : ℝ)⁻¹ * AX = MX := by
      have h4 : (((4 : ℕ) : ℝ)) ^ (2 : ℝ)⁻¹ = 2 := by
        rw [show (((4 : ℕ) : ℝ)) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
          ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h4, hMXdef]; ring
    rwa [hc] at h
  have hS4 : ∀ z ∈ D, ∫ omega, |streamSq omega z| ^ 4 ∂P.toMeasure ≤ MS4 ^ 4 := by
    intro z hz
    have h := integral_abs_pow_le_of_isBigO_gammaSigma (sigma := 1) (A := AS) (p := 4)
      one_pos hASpos (by norm_num) (hstreamMeas z) (hStreamTail z hz)
    have hc : g1 * (((4 : ℕ) : ℝ)) ^ (1 : ℝ)⁻¹ * AS = MS4 := by
      have h4 : (((4 : ℕ) : ℝ)) ^ (1 : ℝ)⁻¹ = (4 : ℝ) := by
        rw [inv_one, Real.rpow_one]; norm_num
      rw [h4, hMS4def]; ring
    rwa [hc] at h
  have hS2 : ∀ z ∈ D, ∫ omega, |streamSq omega z| ^ 2 ∂P.toMeasure ≤ MS2 ^ 2 := by
    intro z hz
    have h := integral_abs_pow_le_of_isBigO_gammaSigma (sigma := 1) (A := AS) (p := 2)
      one_pos hASpos (by norm_num) (hstreamMeas z) (hStreamTail z hz)
    have hc : g1 * (((2 : ℕ) : ℝ)) ^ (1 : ℝ)⁻¹ * AS = MS2 := by
      have h2 : (((2 : ℕ) : ℝ)) ^ (1 : ℝ)⁻¹ = (2 : ℝ) := by
        rw [inv_one, Real.rpow_one]; norm_num
      rw [h2, hMS2def]; ring
    rwa [hc] at h
  have hIX4 : ∀ z ∈ D, Integrable (fun omega => |Xdev omega z| ^ 4) P.toMeasure := fun z hz =>
    integrable_abs_pow_of_isBigO_gammaSigma (sigma := 2) (A := AX) (p := 4)
      two_pos hAXpos (by norm_num) (hXmeas z) (hXtail z hz)
  have hIS4 : ∀ z ∈ D, Integrable (fun omega => |streamSq omega z| ^ 4) P.toMeasure :=
    fun z hz =>
      integrable_abs_pow_of_isBigO_gammaSigma (sigma := 1) (A := AS) (p := 4)
        one_pos hASpos (by norm_num) (hstreamMeas z) (hStreamTail z hz)
  have hIS2 : ∀ z ∈ D, Integrable (fun omega => |streamSq omega z| ^ 2) P.toMeasure :=
    fun z hz =>
      integrable_abs_pow_of_isBigO_gammaSigma (sigma := 1) (A := AS) (p := 2)
        one_pos hASpos (by norm_num) (hstreamMeas z) (hStreamTail z hz)
  -- the per-cube square bound
  set B : ℝ := 2 * a ^ 2 * MS2 ^ 2 + 2 * (MS4 ^ 2 * MX ^ 2) with hBdef
  have hdom : ∀ z ∈ D, ∀ omega : ShellSeq d,
      quad omega z ^ 2 ≤ 2 * a ^ 2 * |streamSq omega z| ^ 2 +
        lam * |Xdev omega z| ^ 4 + lam⁻¹ * |streamSq omega z| ^ 4 := fun z hz omega =>
    quad_sq_le hlampos (hquadNonneg omega z) (hstreamNonneg omega z) (hOneSided omega z hz)
  have hI1 : ∀ z ∈ D, Integrable
      (fun omega : ShellSeq d => 2 * a ^ 2 * |streamSq omega z| ^ 2) P.toMeasure :=
    fun z hz => (hIS2 z hz).const_mul _
  have hI2 : ∀ z ∈ D, Integrable
      (fun omega : ShellSeq d => lam * |Xdev omega z| ^ 4) P.toMeasure :=
    fun z hz => (hIX4 z hz).const_mul _
  have hI3 : ∀ z ∈ D, Integrable
      (fun omega : ShellSeq d => lam⁻¹ * |streamSq omega z| ^ 4) P.toMeasure :=
    fun z hz => (hIS4 z hz).const_mul _
  have hI12 : ∀ z ∈ D, Integrable (fun omega : ShellSeq d =>
      2 * a ^ 2 * |streamSq omega z| ^ 2 + lam * |Xdev omega z| ^ 4) P.toMeasure :=
    fun z hz => (hI1 z hz).add (hI2 z hz)
  have hdomInt : ∀ z ∈ D, Integrable (fun omega : ShellSeq d =>
      2 * a ^ 2 * |streamSq omega z| ^ 2 + lam * |Xdev omega z| ^ 4 +
        lam⁻¹ * |streamSq omega z| ^ 4) P.toMeasure :=
    fun z hz => (hI12 z hz).add (hI3 z hz)
  have hquadInt : ∀ z ∈ D, Integrable (fun omega => quad omega z ^ 2) P.toMeasure := by
    intro z hz
    refine (hdomInt z hz).mono' ((hquadMeas z).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom z hz omega
  have hquadBound : ∀ z ∈ D, ∫ omega, quad omega z ^ 2 ∂P.toMeasure ≤ B := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun omega : ShellSeq d =>
        sq_nonneg (quad omega z))
      (hdomInt z hz) (Filter.Eventually.of_forall (hdom z hz))
    refine hmono.trans ?_
    rw [MeasureTheory.integral_add (hI12 z hz) (hI3 z hz),
      MeasureTheory.integral_add (hI1 z hz) (hI2 z hz),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    have h1 : 2 * a ^ 2 * ∫ omega, |streamSq omega z| ^ 2 ∂P.toMeasure ≤
        2 * a ^ 2 * MS2 ^ 2 :=
      mul_le_mul_of_nonneg_left (hS2 z hz) (mul_nonneg zero_le_two (sq_nonneg _))
    have h2 : lam * ∫ omega, |Xdev omega z| ^ 4 ∂P.toMeasure ≤ lam * MX ^ 4 :=
      mul_le_mul_of_nonneg_left (hX4 z hz) hlampos.le
    have h3 : lam⁻¹ * ∫ omega, |streamSq omega z| ^ 4 ∂P.toMeasure ≤ lam⁻¹ * MS4 ^ 4 :=
      mul_le_mul_of_nonneg_left (hS4 z hz) (inv_nonneg.2 hlampos.le)
    have h4 : lam * MX ^ 4 + lam⁻¹ * MS4 ^ 4 = 2 * (MS4 ^ 2 * MX ^ 2) := by
      have e1 : MS4 ^ 2 / MX ^ 2 * MX ^ 4 = MS4 ^ 2 * MX ^ 2 := by
        rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hMXpos.ne')]; ring
      have e2 : (MS4 ^ 2 / MX ^ 2)⁻¹ * MS4 ^ 4 = MX ^ 2 * MS4 ^ 2 := by
        rw [inv_div, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hMS4pos.ne')]; ring
      rw [hlamdef, e1, e2]; ring
    rw [hBdef]
    linarith only [h1, h2, h3, h4]
  -- the Jensen step over the lattice average
  have hJensen : ∀ omega : ShellSeq d,
      |((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z| ^ 2 ≤
        ((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z ^ 2 := by
    intro omega
    have hcs : (∑ z ∈ D, quad omega z) ^ 2 ≤ (D.card : ℝ) * ∑ z ∈ D, quad omega z ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hcnn : (0 : ℝ) ≤ ((D.card : ℝ))⁻¹ := le_of_lt (inv_pos.2 hNpos)
    rw [abs_mul, mul_pow, abs_of_nonneg hcnn, sq_abs]
    have h := mul_le_mul_of_nonneg_left hcs (sq_nonneg (((D.card : ℝ))⁻¹))
    refine h.trans (le_of_eq ?_)
    linear_combination (∑ z ∈ D, quad omega z ^ 2) * inv_sq_mul_self_aux hNne
  have hIntRHS : Integrable
      (fun omega : ShellSeq d => ((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z ^ 2) P.toMeasure :=
    (MeasureTheory.integrable_finsetSum _ fun z hz => hquadInt z hz).const_mul _
  have hInt2 : ∫ omega, |((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z| ^ 2 ∂P.toMeasure ≤ B := by
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun omega : ShellSeq d =>
        sq_nonneg |((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z|)
      hIntRHS (Filter.Eventually.of_forall hJensen)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ fun z hz => hquadInt z hz]
    have hsum : ∑ z ∈ D, ∫ omega, quad omega z ^ 2 ∂P.toMeasure ≤ ∑ _z ∈ D, B :=
      Finset.sum_le_sum hquadBound
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    calc ((D.card : ℝ))⁻¹ * ∑ z ∈ D, ∫ omega, quad omega z ^ 2 ∂P.toMeasure
        ≤ ((D.card : ℝ))⁻¹ * ((D.card : ℝ) * B) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.2 hNpos))
      _ = B := inv_mul_cancel_left₀ hNne B
  have hsplitB : B = 2 * (a * MS2) ^ 2 + 2 * (MS4 * MX) ^ 2 := by rw [hBdef]; ring
  have hsqrtB : Real.sqrt B ≤ Real.sqrt 2 * (a * MS2) + Real.sqrt 2 * (MS4 * MX) := by
    rw [hsplitB]
    refine (sqrt_add_le_add_sqrt (mul_nonneg zero_le_two (sq_nonneg _))
      (mul_nonneg zero_le_two (sq_nonneg _))).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ((a * MS2) ^ 2),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ((MS4 * MX) ^ 2),
      Real.sqrt_sq (mul_nonneg hsigmaMinus hMS2pos.le),
      Real.sqrt_sq (mul_nonneg hMS4pos.le hMXpos.le)]
  have hLHS : Real.sqrt (∫ omega, |((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z| ^ 2 ∂P.toMeasure) ≤
      Real.sqrt 2 * (a * MS2) + Real.sqrt 2 * (MS4 * MX) :=
    (Real.sqrt_le_sqrt hInt2).trans hsqrtB
  set sg : ℝ := sigmaBarStarInvSeq nu S.LPrime P S.n with hsgdef
  set LL : ℝ := ((S.LPrime - S.ell : ℕ) : ℝ) with hLLdef
  have hWnn : (0 : ℝ) ≤ WL4 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hWL4nonneg _
  have hCnn : (0 : ℝ) ≤ Real.sqrt 2 * (a * MS2) + Real.sqrt 2 * (MS4 * MX) :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hsigmaMinus hMS2pos.le))
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hMS4pos.le hMXpos.le))
  have hmul : Real.sqrt (∫ omega, |((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z| ^ 2 ∂P.toMeasure) *
      WL4 ^ ((1 : ℝ) / 2) ≤
      (Real.sqrt 2 * (a * MS2) + Real.sqrt 2 * (MS4 * MX)) * (Cw * LL * sg) := by
    calc Real.sqrt (∫ omega, |((D.card : ℝ))⁻¹ * ∑ z ∈ D, quad omega z| ^ 2 ∂P.toMeasure) *
          WL4 ^ ((1 : ℝ) / 2)
        ≤ (Real.sqrt 2 * (a * MS2) + Real.sqrt 2 * (MS4 * MX)) * WL4 ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hLHS hWnn
      _ ≤ _ := mul_le_mul_of_nonneg_left hWL4 hCnn
  have hT1 : Real.sqrt 2 * (a * MS2) * (Cw * LL * sg) ≤
      quadTailConstMain Cb Cw Cpig * LL ^ 2 * sg ^ 2 := by
    have hfac : (0 : ℝ) ≤ Real.sqrt 2 * (2 * g1 * Cb) * Cw * LL ^ 2 * sg :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg
        (mul_nonneg zero_le_two hg1pos.le) hCb.le)) hCw) (sq_nonneg _)) hsigmaNonneg
    have hstep := mul_le_mul_of_nonneg_left hPigeon hfac
    have heq1 : Real.sqrt 2 * (a * MS2) * (Cw * LL * sg) =
        Real.sqrt 2 * (2 * g1 * Cb) * Cw * LL ^ 2 * sg * a := by
      rw [hMS2def, hASdef]; ring
    have heq2 : Real.sqrt 2 * (2 * g1 * Cb) * Cw * LL ^ 2 * sg * (Cpig * sg) =
        quadTailConstMain Cb Cw Cpig * LL ^ 2 * sg ^ 2 := by
      rw [quadTailConstMain, ← hg1def]; ring
    rw [heq1, ← heq2]
    exact hstep
  have hT2 : Real.sqrt 2 * (MS4 * MX) * (Cw * LL * sg) ≤
      quadTailConstError Cms Cb Cw * nu ^ (-(3 : ℝ)) * LL ^ 2 *
        (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8) := by
    have hKcnn : (0 : ℝ) ≤ quadTailConstError Cms Cb Cw := by
      rw [quadTailConstError, ← hg1def, ← hg2def]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (Real.sqrt_nonneg _)) hg1pos.le) hg2pos.le) hCms.le) hCb.le) hCw
    have hEle : -(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4 ≤ -((S.h : ℕ) : ℝ) / 8 := by
      rw [hScaleId]; linarith only [hKlog]
    have h3le : (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) ≤
        (3 : ℝ) ^ (-((S.h : ℕ) : ℝ) / 8) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hEle
    have hnuprod : nu ^ (-(2 : ℝ)) * nu⁻¹ = nu ^ (-(3 : ℝ)) := by
      rw [show nu⁻¹ = nu ^ (-(1 : ℝ)) from (Real.rpow_neg_one nu).symm, ← Real.rpow_add hnu]
      norm_num
    have hfac : (0 : ℝ) ≤ quadTailConstError Cms Cb Cw * LL ^ 2 * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) := by
      have h1 : (0 : ℝ) < nu ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hnu _
      have h2 : (0 : ℝ) < (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) :=
        Real.rpow_pos_of_pos (by norm_num) _
      exact mul_nonneg (mul_nonneg (mul_nonneg hKcnn (sq_nonneg _)) h1.le) h2.le
    have heq1 : Real.sqrt 2 * (MS4 * MX) * (Cw * LL * sg) =
        quadTailConstError Cms Cb Cw * LL ^ 2 * nu ^ (-(2 : ℝ)) *
          (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) * sg := by
      rw [hMS4def, hMXdef, hASdef, hAXdef, quadTailConstError, ← hg1def, ← hg2def]; ring
    have hstep1 := mul_le_mul_of_nonneg_left hcrude hfac
    rw [heq1]
    refine hstep1.trans ?_
    have heq2 : quadTailConstError Cms Cb Cw * LL ^ 2 * nu ^ (-(2 : ℝ)) *
        (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) * nu⁻¹ =
        quadTailConstError Cms Cb Cw * nu ^ (-(3 : ℝ)) * LL ^ 2 *
          (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4) := by
      rw [← hnuprod]; ring
    rw [heq2]
    have hfac2 : (0 : ℝ) ≤ quadTailConstError Cms Cb Cw * nu ^ (-(3 : ℝ)) * LL ^ 2 := by
      have h1 : (0 : ℝ) < nu ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hnu _
      exact mul_nonneg (mul_nonneg hKcnn h1.le) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left h3le hfac2
  refine hmul.trans ?_
  have hdist : (Real.sqrt 2 * (a * MS2) + Real.sqrt 2 * (MS4 * MX)) * (Cw * LL * sg) =
      Real.sqrt 2 * (a * MS2) * (Cw * LL * sg) +
        Real.sqrt 2 * (MS4 * MX) * (Cw * LL * sg) := by ring
  rw [hdist]
  exact add_le_add hT1 hT2


end

end SuperdiffusionCLT.Section3.Terms
