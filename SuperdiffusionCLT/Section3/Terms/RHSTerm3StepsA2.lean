/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsA
public import Mathlib.Analysis.MeanInequalities

/-!
# `l.RHS.term3`, Step 1: the small-cube oscillation term `e.RHS.term3.B`

The first step of the proof of `l.RHS.term3`.
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

/-! ## Averaged Hölder and Jensen inequalities over the sub-cube family -/

/-- Jensen's inequality for the plain average over a finite family, at a
concave power `t ↦ t^r`, `0 < r ≤ 1`. -/
private theorem avsum_rpow_le {iota : Type*} (s : Finset iota) (hs : s.Nonempty)
    (x : iota → ℝ) (hx : ∀ i, 0 ≤ x i) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ((s.card : ℝ))⁻¹ * ∑ i ∈ s, x i ^ r ≤ (((s.card : ℝ))⁻¹ * ∑ i ∈ s, x i) ^ r := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hp : (1 : ℝ) ≤ r⁻¹ := by
    have h := one_div_le_one_div_of_le hr0 hr1
    simpa using h
  have hmain := Real.inner_le_weight_mul_Lp_of_nonneg s (p := r⁻¹) hp
    (fun _ => (1 : ℝ)) (fun i => x i ^ r) (fun _ => zero_le_one)
    (fun i => Real.rpow_nonneg (hx i) r)
  have hxx : ∀ i : iota, (x i ^ r) ^ r⁻¹ = x i := by
    intro i
    rw [← Real.rpow_mul (hx i), mul_inv_cancel₀ (ne_of_gt hr0), Real.rpow_one]
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, inv_inv, hxx] at hmain
  have hsumnn : (0 : ℝ) ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
  have hstep := mul_le_mul_of_nonneg_left hmain (le_of_lt (inv_pos.2 hcard))
  refine hstep.trans_eq ?_
  have hinv : ((s.card : ℝ))⁻¹ = (s.card : ℝ) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg hcard.le, Real.rpow_one]
  have hL : ((s.card : ℝ))⁻¹ * ((s.card : ℝ) ^ (1 - r) * (∑ i ∈ s, x i) ^ r) =
      (s.card : ℝ) ^ (-r) * (∑ i ∈ s, x i) ^ r := by
    rw [hinv, ← mul_assoc, ← Real.rpow_add hcard]
    ring_nf
  have hR : (((s.card : ℝ))⁻¹ * ∑ i ∈ s, x i) ^ r =
      (s.card : ℝ) ^ (-r) * (∑ i ∈ s, x i) ^ r := by
    rw [Real.mul_rpow (le_of_lt (inv_pos.2 hcard)) hsumnn, hinv, ← Real.rpow_mul hcard.le]
    ring_nf
  rw [hL, hR]

/-- Hölder's inequality with the conjugate pair `(3, 3/2)` for the plain
average over a finite family. -/
private theorem avsum_mul_le_holder_third {iota : Type*} (s : Finset iota) (hs : s.Nonempty)
    (a b : iota → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ((s.card : ℝ))⁻¹ * ∑ i ∈ s, a i ^ ((1 : ℝ) / 3) * b i ^ ((2 : ℝ) / 3) ≤
      (((s.card : ℝ))⁻¹ * ∑ i ∈ s, a i) ^ ((1 : ℝ) / 3) *
        (((s.card : ℝ))⁻¹ * ∑ i ∈ s, b i) ^ ((2 : ℝ) / 3) := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hs
  have hconj : Real.HolderConjugate (3 : ℝ) ((3 : ℝ) / 2) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hmain := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun i => a i ^ ((1 : ℝ) / 3)) (g := fun i => b i ^ ((2 : ℝ) / 3)) hconj
    (fun i _ => Real.rpow_nonneg (ha i) _) (fun i _ => Real.rpow_nonneg (hb i) _)
  have hA : ∀ i : iota, (a i ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = a i := by
    intro i
    rw [← Real.rpow_mul (ha i)]
    norm_num
  have hB : ∀ i : iota, (b i ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = b i := by
    intro i
    rw [← Real.rpow_mul (hb i)]
    norm_num
  simp only [hA, hB] at hmain
  have hexp1 : (1 : ℝ) / (3 : ℝ) = (1 : ℝ) / 3 := rfl
  have hexp2 : (1 : ℝ) / ((3 : ℝ) / 2) = (2 : ℝ) / 3 := by norm_num
  rw [hexp1, hexp2] at hmain
  have hsa : (0 : ℝ) ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
  have hsb : (0 : ℝ) ≤ ∑ i ∈ s, b i := Finset.sum_nonneg fun i _ => hb i
  have hinvnn : (0 : ℝ) ≤ ((s.card : ℝ))⁻¹ := le_of_lt (inv_pos.2 hcard)
  have hstep := mul_le_mul_of_nonneg_left hmain hinvnn
  refine hstep.trans_eq ?_
  rw [Real.mul_rpow hinvnn hsa, Real.mul_rpow hinvnn hsb]
  have hsplit : ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 3) * ((s.card : ℝ))⁻¹ ^ ((2 : ℝ) / 3) =
      ((s.card : ℝ))⁻¹ := by
    rw [← Real.rpow_add (inv_pos.2 hcard)]
    norm_num
  calc ((s.card : ℝ))⁻¹ * ((∑ i ∈ s, a i) ^ ((1 : ℝ) / 3) * (∑ i ∈ s, b i) ^ ((2 : ℝ) / 3))
      = (((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 3) * ((s.card : ℝ))⁻¹ ^ ((2 : ℝ) / 3)) *
        ((∑ i ∈ s, a i) ^ ((1 : ℝ) / 3) * (∑ i ∈ s, b i) ^ ((2 : ℝ) / 3)) := by
        rw [hsplit]
    _ = ((s.card : ℝ))⁻¹ ^ ((1 : ℝ) / 3) * (∑ i ∈ s, a i) ^ ((1 : ℝ) / 3) *
        (((s.card : ℝ))⁻¹ ^ ((2 : ℝ) / 3) * (∑ i ∈ s, b i) ^ ((2 : ℝ) / 3)) := by ring

/-- Monotonicity of `(A, B) ↦ A^{1/3} B^{2/3}` on the nonnegative quadrant. -/
private theorem rpow_third_mul_rpow_two_thirds_le {A B a b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAa : A ≤ a) (hBb : B ≤ b) :
    A ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) ≤ a ^ ((1 : ℝ) / 3) * b ^ ((2 : ℝ) / 3) :=
  mul_le_mul (Real.rpow_le_rpow hA hAa (by norm_num))
    (Real.rpow_le_rpow hB hBb (by norm_num)) (Real.rpow_nonneg hB _)
    (Real.rpow_nonneg (hA.trans hAa) _)

/-- The exponent bookkeeping of the final Hölder step of `e.RHS.term3.B`:
`(C_wν^{-3/2}3^{-3ℓ'})^{1/3}` times
`(C_3 3^{3n/2}(L'ν⁻¹)^{3/4}(δ+η_L)^{3/4})^{2/3}` is
`C_w^{1/3}C_3^{2/3}ν^{-1}(δ+η_L)^{1/2}(L')^{1/2}3^{-(ℓ'-n)}`, which the
standing range `ν ≤ 1` turns into the printed `ν^{-3/2}` form. -/
private theorem rhs_term3_B_arith {nu Cw C3 delta etaL : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {S : ScaleSelection} (hSorder : ScalesOrdering S)
    (hCw : 0 ≤ Cw) (hC3 : 0 ≤ C3) (hde : 0 ≤ delta + etaL) :
    (Cw * nu ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ)))) ^ ((1 : ℝ) / 3) *
        (C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
            (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
            (delta + etaL) ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) ≤
      Cw ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3) * nu ^ (-(3 / 2 : ℝ)) *
        (delta + etaL) ^ ((1 : ℝ) / 2) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hLnn : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnuinv : (0 : ℝ) ≤ nu⁻¹ := le_of_lt (inv_pos.2 hnu)
  have hLnu : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) * nu⁻¹ := mul_nonneg hLnn hnuinv
  -- the first factor
  have ea : (-(3 / 2 : ℝ)) * ((1 : ℝ) / 3) = -(1 / 2 : ℝ) := by norm_num
  have eb : (-(3 * (S.ellPrime : ℝ))) * ((1 : ℝ) / 3) = -(S.ellPrime : ℝ) := by ring
  have e1 : (Cw * nu ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ)))) ^ ((1 : ℝ) / 3) =
      Cw ^ ((1 : ℝ) / 3) * nu ^ (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)) := by
    rw [Real.mul_rpow (mul_nonneg hCw (Real.rpow_nonneg hnu.le _)) (Real.rpow_nonneg h3 _),
      Real.mul_rpow hCw (Real.rpow_nonneg hnu.le _), ← Real.rpow_mul hnu.le,
      ← Real.rpow_mul h3, ea, eb]
  -- the second factor
  have ec : ((3 * (S.n : ℝ)) / 2) * ((2 : ℝ) / 3) = (S.n : ℝ) := by ring
  have ed : ((3 : ℝ) / 4) * ((2 : ℝ) / 3) = (1 : ℝ) / 2 := by norm_num
  have hnuhalf : (nu⁻¹) ^ ((1 : ℝ) / 2) = nu ^ (-(1 / 2 : ℝ)) := by
    rw [Real.inv_rpow hnu.le, Real.rpow_neg hnu.le]
  have e2 : (C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
        (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
        (delta + etaL) ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) =
      C3 ^ ((2 : ℝ) / 3) * (3 : ℝ) ^ (S.n : ℝ) *
        (((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * nu ^ (-(1 / 2 : ℝ))) *
        (delta + etaL) ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg hC3 (Real.rpow_nonneg h3 _))
        (Real.rpow_nonneg hLnu _)) (Real.rpow_nonneg hde _),
      Real.mul_rpow (mul_nonneg hC3 (Real.rpow_nonneg h3 _)) (Real.rpow_nonneg hLnu _),
      Real.mul_rpow hC3 (Real.rpow_nonneg h3 _), ← Real.rpow_mul h3,
      ← Real.rpow_mul hLnu, ← Real.rpow_mul hde, ec, ed,
      Real.mul_rpow hLnn hnuinv, hnuhalf]
  rw [e1, e2]
  -- combine the powers of `ν` and of `3`
  have hnucomb : nu ^ (-(1 / 2 : ℝ)) * nu ^ (-(1 / 2 : ℝ)) = nu ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hnu]
    norm_num
  have h3comb : (3 : ℝ) ^ (-(S.ellPrime : ℝ)) * (3 : ℝ) ^ (S.n : ℝ) =
      (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) := by
    have hle : S.n ≤ S.ellPrime :=
      le_of_lt (lt_trans hSorder.n_lt_ell hSorder.ell_lt_ellPrime)
    rw [← Real.rpow_add h3pos, Nat.cast_sub hle]
    ring_nf
  have hcombine : Cw ^ ((1 : ℝ) / 3) * nu ^ (-(1 / 2 : ℝ)) * (3 : ℝ) ^ (-(S.ellPrime : ℝ)) *
        (C3 ^ ((2 : ℝ) / 3) * (3 : ℝ) ^ (S.n : ℝ) *
          (((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * nu ^ (-(1 / 2 : ℝ))) *
          (delta + etaL) ^ ((1 : ℝ) / 2)) =
      Cw ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3) * nu ^ (-(1 : ℝ)) *
        (delta + etaL) ^ ((1 : ℝ) / 2) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) := by
    rw [← hnucomb, ← h3comb]
    ring
  rw [hcombine]
  have hmono : nu ^ (-(1 : ℝ)) ≤ nu ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)
  have hc12 : (0 : ℝ) ≤ Cw ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3) :=
    mul_nonneg (Real.rpow_nonneg hCw _) (Real.rpow_nonneg hC3 _)
  have htail : (0 : ℝ) ≤ (delta + etaL) ^ ((1 : ℝ) / 2) *
      ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hde _) (Real.rpow_nonneg hLnn _))
      (Real.rpow_nonneg h3 _)
  have hexpand : ∀ t : ℝ, Cw ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3) * t *
        (delta + etaL) ^ ((1 : ℝ) / 2) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) =
      (Cw ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3)) * t *
        ((delta + etaL) ^ ((1 : ℝ) / 2) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ))) := fun t => by ring
  rw [hexpand, hexpand]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmono hc12) htail

/-! ## `e.RHS.term3.B` -/

/-- **`e.RHS.term3.B`**, proved from the four displays of the proof of `l.RHS.term3`:

`E[avsum_z ⨍_{z+cu_n}(∇w − (∇w)_{z+cu_n})·a_{L'}(∇u_m − ∇u_{n,z})]
   ≤ C ν^{-3/2}(δ + η_L)^{1/2}(L')^{1/2} 3^{-(ℓ'−n)}`, `C = C_w^{1/3} C_3^{2/3}`.

The three per-cube quantities are free binders, as in
`multiscale_poincare_flux`: `oscH1 ω z` is the `H̲¹(z+cu_n)` seminorm
`[∇w − (∇w)_{z+cu_n}]`, `fluxNegNorm ω z` is
`‖a_{L'}(∇u_m − ∇u_{n,z})‖_{H̲^{-1}(z+cu_n)}` and `energyL2 ω z` is
`‖σ^{1/2}(∇u_m − ∇u_{n,z})‖²_{L̲²(z+cu_n)}`.

The inputs from the paper enter as explicit hypotheses in their printed shapes:

* `hCS` is the first display of the proof, the `H̲¹`/`H̲^{-1}`
  duality pairing on `z + cu_n`.  The paper compresses this step; the
  fractional/negative-norm duality it needs has no carrier in the development, so it
  is a hypothesis.
* `hOsc` is the second display: `e.nablaw.Lt` of
  `l.w.basic.regbounds` composed with the per-cube Poincaré inequality for the
  centered gradient, in the printed form
  `avsum_z E[[∇w − (∇w)_{z+cu_n}]³_{H̲¹}] ≤ Cν^{-3/2}3^{-3ℓ'}`.
* `hFlux` is `l.RHS.term3#multiscale-poincare-flux`, i.e. the conclusion of
  `multiscale_poincare_flux`, applied on each small cube.
* `hEnergy` is `e.additivity.error.superdiff`, i.e. the conclusion of
  `additivity_error_superdiff`.

The two Hölder steps that the paper names but does not display — the pairing
`avsum_z E[a_z b_z] ≤ (avsum_z E[a_z³])^{1/3}(avsum_z E[b_z^{3/2}])^{2/3}` and
the concavity step `avsum_z E[·]^{3/4} ≤ (avsum_z E[·])^{3/4}` — are proved
here (`avsum_mul_le_holder_third`, `avsum_rpow_le`).

The computation produces the factor `ν⁻¹`; the printed `ν^{-3/2}` follows from
the standing range `ν ≤ 1` of `e.sde.intro`, which is the hypothesis
`hnu1`. -/
theorem rhs_term3_B {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d)) {S : ScaleSelection} (hSorder : ScalesOrdering S)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (oscH1 fluxNegNorm energyL2 : ShellSeq d → TriadicCube d → ℝ)
    {Cw C3 delta etaL : ℝ} (hCw : 0 ≤ Cw) (hC3 : 0 ≤ C3)
    (hde : 0 ≤ delta + etaL)
    (hOscNonneg : ∀ (omega : ShellSeq d) (R : TriadicCube d), 0 ≤ oscH1 omega R)
    (hFluxNonneg : ∀ (omega : ShellSeq d) (R : TriadicCube d), 0 ≤ fluxNegNorm omega R)
    (hEnergyNonneg : ∀ (omega : ShellSeq d) (R : TriadicCube d), 0 ≤ energyL2 omega R)
    (hCS : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      volumeAverage (openCubeSet R)
          (fun y => vecDot ((w omega).toH1Function.grad y -
              volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) ≤
        oscH1 omega R * fluxNegNorm omega R)
    (hOsc : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, oscH1 omega R ^ (3 : ℝ) ∂P.toMeasure ≤
      Cw * nu ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ))))
    (hFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d, fluxNegNorm omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure ≤
        C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
          (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) *
          (∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure) ^ ((3 : ℝ) / 4))
    (hEnergy : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure ≤ delta + etaL)
    (hXint : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d S.n S.m,
          volumeAverage (openCubeSet R)
            (fun y => vecDot ((w omega).toH1Function.grad y -
                volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hOFint : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => oscH1 omega R * fluxNegNorm omega R) P.toMeasure)
    (hMemOsc : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d => oscH1 omega R) (ENNReal.ofReal (3 : ℝ)) P.toMeasure)
    (hMemFlux : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      MemLp (fun omega : ShellSeq d => fluxNegNorm omega R)
        (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            volumeAverage (openCubeSet R)
              (fun y => vecDot ((w omega).toH1Function.grad y -
                  volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y)))
        ∂P.toMeasure ≤
      Cw ^ ((1 : ℝ) / 3) * C3 ^ ((2 : ℝ) / 3) * nu ^ (-(3 / 2 : ℝ)) *
        (delta + etaL) ^ ((1 : ℝ) / 2) * ((S.LPrime : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) := by
  classical
  set D : Finset (TriadicCube d) := largeCubeSubcubes d S.n S.m with hD
  set c : ℝ := ((D.card : ℝ))⁻¹ with hc
  have hDne : D.Nonempty := largeCubeSubcubes_nonempty d S.n S.m
  have hcard : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hDne
  have hcnn : (0 : ℝ) ≤ c := le_of_lt (inv_pos.2 hcard)
  set A : TriadicCube d → ℝ :=
    fun R => ∫ omega : ShellSeq d, oscH1 omega R ^ (3 : ℝ) ∂P.toMeasure with hA
  set B : TriadicCube d → ℝ :=
    fun R => ∫ omega : ShellSeq d, fluxNegNorm omega R ^ ((3 : ℝ) / 2) ∂P.toMeasure with hB
  set E : TriadicCube d → ℝ :=
    fun R => ∫ omega : ShellSeq d, energyL2 omega R ∂P.toMeasure with hE
  have hAnn : ∀ R : TriadicCube d, 0 ≤ A R := fun R =>
    MeasureTheory.integral_nonneg fun omega => Real.rpow_nonneg (hOscNonneg omega R) _
  have hBnn : ∀ R : TriadicCube d, 0 ≤ B R := fun R =>
    MeasureTheory.integral_nonneg fun omega => Real.rpow_nonneg (hFluxNonneg omega R) _
  have hEnn : ∀ R : TriadicCube d, 0 ≤ E R := fun R =>
    MeasureTheory.integral_nonneg fun omega => hEnergyNonneg omega R
  -- Step 1: the pointwise duality bound, integrated
  have hYint : Integrable (fun omega : ShellSeq d =>
      c * ∑ R ∈ D, oscH1 omega R * fluxNegNorm omega R) P.toMeasure :=
    (MeasureTheory.integrable_finsetSum D hOFint).const_mul c
  have hstep1 : ∫ omega : ShellSeq d,
        c * ∑ R ∈ D,
          volumeAverage (openCubeSet R)
            (fun y => vecDot ((w omega).toH1Function.grad y -
                volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
      c * ∑ R ∈ D, A R ^ ((1 : ℝ) / 3) * B R ^ ((2 : ℝ) / 3) := by
    have hmono : ∀ omega : ShellSeq d,
        c * ∑ R ∈ D,
            volumeAverage (openCubeSet R)
              (fun y => vecDot ((w omega).toH1Function.grad y -
                  volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
                (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) ≤
          c * ∑ R ∈ D, oscH1 omega R * fluxNegNorm omega R := by
      intro omega
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun R hR => hCS omega R hR) hcnn
    have hint := MeasureTheory.integral_mono hXint hYint hmono
    refine hint.trans ?_
    have hswap : ∫ omega : ShellSeq d,
        c * ∑ R ∈ D, oscH1 omega R * fluxNegNorm omega R ∂P.toMeasure =
        c * ∑ R ∈ D, ∫ omega : ShellSeq d,
          oscH1 omega R * fluxNegNorm omega R ∂P.toMeasure := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finsetSum _ (fun R hR => hOFint R hR)]
    rw [hswap]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => ?_) hcnn
    have hconj : Real.HolderConjugate (3 : ℝ) ((3 : ℝ) / 2) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P.toMeasure) hconj
      (f := fun omega : ShellSeq d => oscH1 omega R)
      (g := fun omega : ShellSeq d => fluxNegNorm omega R)
      (Filter.Eventually.of_forall fun omega => hOscNonneg omega R)
      (Filter.Eventually.of_forall fun omega => hFluxNonneg omega R)
      (hMemOsc R hR) (hMemFlux R hR)
    rw [show (1 : ℝ) / ((3 : ℝ) / 2) = (2 : ℝ) / 3 by norm_num] at h
    exact h
  -- Step 2: the averaged Hölder pairing
  have hstep2 : c * ∑ R ∈ D, A R ^ ((1 : ℝ) / 3) * B R ^ ((2 : ℝ) / 3) ≤
      (c * ∑ R ∈ D, A R) ^ ((1 : ℝ) / 3) * (c * ∑ R ∈ D, B R) ^ ((2 : ℝ) / 3) :=
    avsum_mul_le_holder_third D hDne A B hAnn hBnn
  -- Step 3: the two averaged bounds
  set K : ℝ := C3 * (3 : ℝ) ^ ((3 * (S.n : ℝ)) / 2) *
    (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((3 : ℝ) / 4) with hK
  have hKnn : (0 : ℝ) ≤ K := by
    have h1 : (0 : ℝ) ≤ ((S.LPrime : ℕ) : ℝ) * nu⁻¹ :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (inv_pos.2 hnu))
    exact mul_nonneg (mul_nonneg hC3 (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg h1 _)
  have hBavg : c * ∑ R ∈ D, B R ≤ K * (delta + etaL) ^ ((3 : ℝ) / 4) := by
    have h1 : c * ∑ R ∈ D, B R ≤ c * ∑ R ∈ D, K * E R ^ ((3 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => hFlux R hR) hcnn
    have h2 : c * ∑ R ∈ D, K * E R ^ ((3 : ℝ) / 4) =
        K * (c * ∑ R ∈ D, E R ^ ((3 : ℝ) / 4)) := by
      rw [← Finset.mul_sum]
      ring
    have h3 : c * ∑ R ∈ D, E R ^ ((3 : ℝ) / 4) ≤ (c * ∑ R ∈ D, E R) ^ ((3 : ℝ) / 4) :=
      avsum_rpow_le D hDne E hEnn (by norm_num) (by norm_num)
    have h4 : (c * ∑ R ∈ D, E R) ^ ((3 : ℝ) / 4) ≤ (delta + etaL) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (mul_nonneg hcnn (Finset.sum_nonneg fun R _ => hEnn R))
        hEnergy (by norm_num)
    calc c * ∑ R ∈ D, B R ≤ c * ∑ R ∈ D, K * E R ^ ((3 : ℝ) / 4) := h1
      _ = K * (c * ∑ R ∈ D, E R ^ ((3 : ℝ) / 4)) := h2
      _ ≤ K * (delta + etaL) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hKnn
  have hstep3 : (c * ∑ R ∈ D, A R) ^ ((1 : ℝ) / 3) * (c * ∑ R ∈ D, B R) ^ ((2 : ℝ) / 3) ≤
      (Cw * nu ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (-(3 * (S.ellPrime : ℝ)))) ^ ((1 : ℝ) / 3) *
        (K * (delta + etaL) ^ ((3 : ℝ) / 4)) ^ ((2 : ℝ) / 3) :=
    rpow_third_mul_rpow_two_thirds_le
      (mul_nonneg hcnn (Finset.sum_nonneg fun R _ => hAnn R))
      (mul_nonneg hcnn (Finset.sum_nonneg fun R _ => hBnn R)) hOsc hBavg
  refine le_trans (le_trans (le_trans hstep1 hstep2) hstep3) ?_
  rw [hK]
  exact rhs_term3_B_arith hnu hnu1 hSorder hCw hC3 hde

end

end SuperdiffusionCLT.Section3.Terms
