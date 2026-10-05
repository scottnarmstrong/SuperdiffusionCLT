/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2B
public import SuperdiffusionCLT.Probability.OrliczPower

/-!
# The first summand `T1` of the averaged gauged comparison

The single Orlicz premise of the localization statement splits into the two printed summands
`T1 + T2`, and `localizationAverageEnvelope_eq_T1_add_T2` shows that the printed envelope is
the sum of the two amplitudes.  This module addresses the *first* summand, whose printed
amplitude is `localizationAverageEnvelopeT1`.

## What the printed proof does for `T1`

With `h_z := (k_L − k_ℓ)_{z+cu_n}` and `D_z` the deterministic comparison

* `D_z ≤ Cν⁻¹3^n‖∇(k_L − k_ℓ)‖_{L^∞(z+cu_n)} + Cν⁻²3^{2n}‖∇(k_L − k_ℓ)‖²_{L^∞(z+cu_n)}`
  (`e.localization.average.Dz`), obtained from `l.localization.A` at perturbation
  `k_L − k_ℓ − h_z` (available as `coarseBlockMatrix_localization_scalar_two_sided`), the
  pointwise localization comparison and `e.commute.coarse.grained.k0`;

the first summand is

`T_1 := avsum_{z} D_z |bfA_ℓ^{1/2}(z+cu_n) G_{-h_z}P|²`.

The printed proof then supplies two averages.

* `D_z ≤ O_{Γ_1}(Cν⁻²3^{-(ℓ-n)})` for each fixed `z`
  (stationarity together with `e.nabla.kmn.Linfty`), hence by the power rule
  and the generalized triangle inequality the *second-moment average*
  `avsum_z D_z² ≤ 1_{L>ℓ} O_{Γ_{1/2}}(Cν⁻⁴3^{-2(ℓ-n)})`.
* With `Y_z := |bfE_ℓ^{-1/2}bfA_ℓ(z+cu_n)bfE_ℓ^{-1/2}|` and
  `R_z := |bfE_ℓ^{1/2}G_{-h_z}P|⁴`, and using
  `e.Enaught.vs.A.and.Ahom`, `e.jk.spatialavg`, `e.Enaught.mixing`, the finite
  maximum and the multiplication property, the *fourth-moment average*
  `avsum_z |bfA_ℓ^{1/2}(z+cu_n)G_{-h_z}P|⁴ ≤ O_{Γ_{1/4}}(Cν⁻²((1∨ℓ)²+(L-ℓ)²)|P|⁴)`.

Cauchy--Schwarz over the grid then gives
`T_1 ≤ (avsum_z D_z²)^{1/2}(avsum_z |…|⁴)^{1/2}`, whose two factors are `Γ_1`
and `Γ_{1/2}` at the square roots of those amplitudes; the printed
multiplication property `e.multGammasig` at `σ₁ = 1`, `σ₂ = 1/2` returns
`Γ_{1/3}` at `Cν⁻³3^{-(ℓ-n)}√((1∨ℓ)²+(L-ℓ)²)|P|²`, which after enlarging
`C(d)` is the printed `1_{L>ℓ}Cν⁻³L3^{-(ℓ-n)}|P|²`.

## The `ν` power of the printed amplitude

`localizationAverageEnvelopeT1` carries `ν⁻³`.  That agrees with both places where the paper
states `T1`: the first summand of `e.localization.average.oneshot` and the conclusion of the
Cauchy--Schwarz step both read `Cν⁻³…`.  The two intermediate amplitudes
carry `ν⁻⁴` and `ν⁻²`; their geometric mean is `ν⁻³`,
which is what makes the printed `T1` amplitude consistent.

## Main results

* `isBigO_gammaSigma_sqrt_of_sq`: the power rule `e.powerofGammasigma` read
  backwards at `p = 2` --- the square root of a `Γ_{σ/2}` quantity is `Γ_σ`.
* `isBigO_gammaSigma_mul_of_abs_le_mul`: Cauchy--Schwarz followed by the
  printed multiplication property `e.multGammasig`.
* `localizationAverageT1SecondAmplitude`, `localizationAverageT1FourthAmplitude`
  and their square-root forms: the amplitudes of the two printed averages,
  with `localizationAverageT1Const` the enlarged constant.
* `localizationAverageT1_amplitude_le`: the printed amplitude bookkeeping.
* `localizationAverage_T1`: the `Γ_{1/3}` bound for the first summand at
  `localizationAverageEnvelopeT1`, with the square-root step, the index
  bookkeeping and the constant enlargement discharged.

The two averages themselves, and the vanishing of the localization error at
`L = ℓ`, enter as the named hypotheses `hD2`, `hB2`, `hD2_zero`:
their carriers (`D_z`, `bfE_ℓ`, `h_z`, `bfA_ℓ`) are not formalized here, exactly as the
cutoff-`ℓ` summand `V_z` of `T2` is not.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The Orlicz toolbox of the first summand -/

section OrliczToolbox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random variable that vanishes pointwise obeys every `Γ_σ` tail bound at
amplitude `0`: its absolute upper-tail event is empty.  This is the degenerate
branch `L = ℓ` of the first summand, where the localization error vanishes
identically. -/
private theorem isBigO_gammaSigma_of_eq_zero {mu : MeasureTheory.Measure Ω} {X : Ω → ℝ}
    {σ : ℝ} (hX : ∀ omega, X omega = 0) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ) X 0 := by
  intro t _ht
  have hset : IndependentSums.upperTailEvent (fun omega : Ω => |X omega|) (0 * t) = (∅ : Set Ω) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, Set.mem_empty_iff_false, zero_mul, hX omega,
      abs_zero, lt_self_iff_false]
  rw [hset]
  rw [MeasureTheory.Measure.real, measure_empty, ENNReal.toReal_zero]
  exact inv_nonneg.mpr (by
    simpa only [IndependentSums.gammaSigma_apply] using (Real.exp_pos (t ^ σ)).le)

/-- **The power rule `e.powerofGammasigma` read as a square root.**  For a
pointwise nonnegative `D` and `0 ≤ A`, if `D` is `O_{Γ_{σ/2}}(A²)` then its
pointwise square root is `O_{Γ_σ}(A)`.

This is the backward direction of the equivalence
`isBigO_gammaSigma_rpow_iff` at `p = 2`
(`SuperdiffusionCLT.Probability.OrliczIndexWeakening`): squaring raises
the amplitude to `A² = A^(2:ℝ)` and divides the index by `2`, so inverting it
doubles the index.  It is the step by which the printed proof turns the
second-moment average (`Γ_{1/2}`) into the `Γ_1` factor of
Cauchy--Schwarz, and the fourth-moment average (`Γ_{1/4}`) into the
`Γ_{1/2}` factor. -/
theorem isBigO_gammaSigma_sqrt_of_sq {mu : MeasureTheory.Measure Ω} [IsFiniteMeasure mu]
    {D : Ω → ℝ} {A σ : ℝ} (hA : 0 ≤ A) (hD : ∀ omega, 0 ≤ D omega)
    (h : IndependentSums.IsBigO mu (IndependentSums.gammaSigma (σ / 2)) D (A ^ 2)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ)
      (fun omega => Real.sqrt (D omega)) A := by
  have hrev : IndependentSums.IsBigO mu (IndependentSums.gammaSigma (σ / 2))
      (fun omega => Real.sqrt (D omega) ^ (2 : ℝ)) (A ^ (2 : ℝ)) := by
    have hfun : (fun omega => Real.sqrt (D omega) ^ (2 : ℝ)) = D :=
      funext fun omega => by rw [Real.rpow_two, Real.sq_sqrt (hD omega)]
    rw [hfun]
    rw [Real.rpow_two]
    exact h
  exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_rev
    (X := fun omega => Real.sqrt (D omega)) (K := A) (σ := σ) (p := 2)
    (by norm_num) hA (fun _ => Real.sqrt_nonneg _) hrev

/-- **Cauchy--Schwarz followed by the printed multiplication property**
(`e.multGammasig`).  If `|T| ≤ X · Y` pointwise with `X, Y` nonnegative and
`X`, `Y` are `O_{Γ_{σ₁}}(A)` and `O_{Γ_{σ₂}}(B)`, then `T` is
`O_{Γ_{σ₁σ₂/(σ₁+σ₂)}}(orliczProductConst σ₁ σ₂ * (A B))`.

The pointwise Cauchy--Schwarz inequality is what turns the two moment averages
of the printed proof into a product of two square roots; the multiplication
property is applied to that product, the nonnegativity of the two factors
being what lets the absolute value of the product be read as the product. -/
theorem isBigO_gammaSigma_mul_of_abs_le_mul {mu : MeasureTheory.Measure Ω} [IsFiniteMeasure mu]
    {T X Y : Ω → ℝ} {A B σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hXnn : ∀ omega, 0 ≤ X omega) (hYnn : ∀ omega, 0 ≤ Y omega)
    (hT : ∀ omega, |T omega| ≤ X omega * Y omega)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ₁) X A)
    (hY : IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ₂) Y B) :
    IndependentSums.IsBigO mu
      (IndependentSums.gammaSigma (σ₁ * σ₂ / (σ₁ + σ₂))) T
      (SuperdiffusionCLT.Probability.orliczProductConst σ₁ σ₂ * (A * B)) :=
  (SuperdiffusionCLT.Probability.isBigO_gammaSigma_mul (mu := mu) (X₁ := X) (X₂ := Y)
    (A₁ := A) (A₂ := B) (σ₁ := σ₁) (σ₂ := σ₂) hσ₁ hσ₂ hA hB hX hY).of_abs_le
    (fun omega => by
      rw [abs_mul, abs_of_nonneg (hXnn omega), abs_of_nonneg (hYnn omega)]
      exact hT omega)

end OrliczToolbox

/-! ## The printed amplitudes of the two moment averages -/

/-- The printed amplitude of the second-moment average of the localization
error: `Cν⁻⁴3^{-2(ℓ-n)}`. -/
noncomputable def localizationAverageT1SecondAmplitude (C nu : ℝ) (l n : ℕ) : ℝ :=
  C * nu ^ (-(4 : ℝ)) * (3 : ℝ) ^ (-(2 * ((l - n : ℕ) : ℝ)))

/-- The printed amplitude of the fourth-moment average:
`Cν⁻²((1∨ℓ)² + (L-ℓ)²)|P|⁴`. -/
noncomputable def localizationAverageT1FourthAmplitude (C nu : ℝ) (l L : ℕ)
    (Pvec : BlockVec d) : ℝ :=
  C * nu ^ (-(2 : ℝ)) * ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
    blockVecDot Pvec Pvec ^ 2

/-- The square root of the second-moment amplitude:
`√C ν⁻² 3^{-(ℓ-n)}`.  This is the amplitude of the `Γ_1` factor produced by
`isBigO_gammaSigma_sqrt_of_sq`; its square is
`localizationAverageT1SecondAmplitude`. -/
noncomputable def localizationAverageT1SecondSqrtAmplitude (C nu : ℝ) (l n : ℕ) : ℝ :=
  Real.sqrt C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ))

/-- The square root of the fourth-moment amplitude:
`√C ν⁻¹ √((1∨ℓ)² + (L-ℓ)²) |P|²`.  This is the amplitude of the `Γ_{1/2}`
factor produced by `isBigO_gammaSigma_sqrt_of_sq`; its square is
`localizationAverageT1FourthAmplitude`. -/
noncomputable def localizationAverageT1FourthSqrtAmplitude (C nu : ℝ) (l L : ℕ)
    (Pvec : BlockVec d) : ℝ :=
  Real.sqrt C * nu ^ (-(1 : ℝ)) *
    Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) * blockVecDot Pvec Pvec

/-! ## Positivity of the amplitudes -/

/-- The second-moment amplitude is nonnegative. -/
theorem localizationAverageT1SecondAmplitude_nonneg {C nu : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (l n : ℕ) : 0 ≤ localizationAverageT1SecondAmplitude C nu l n := by
  unfold localizationAverageT1SecondAmplitude
  exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hnu _)) (Real.rpow_nonneg (by norm_num) _)

/-- The fourth-moment amplitude is nonnegative. -/
theorem localizationAverageT1FourthAmplitude_nonneg {C nu : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (l L : ℕ) (Pvec : BlockVec d) :
    0 ≤ localizationAverageT1FourthAmplitude C nu l L Pvec := by
  unfold localizationAverageT1FourthAmplitude
  exact mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hnu _))
    (add_nonneg (sq_nonneg _) (sq_nonneg _))) (sq_nonneg _)

/-- The square root of the second-moment amplitude is nonnegative. -/
theorem localizationAverageT1SecondSqrtAmplitude_nonneg {C nu : ℝ}
    (hnu : 0 ≤ nu) (l n : ℕ) : 0 ≤ localizationAverageT1SecondSqrtAmplitude C nu l n := by
  unfold localizationAverageT1SecondSqrtAmplitude
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hnu _))
    (Real.rpow_nonneg (by norm_num) _)

/-- The square root of the fourth-moment amplitude is nonnegative. -/
theorem localizationAverageT1FourthSqrtAmplitude_nonneg {C nu : ℝ}
    (hnu : 0 ≤ nu) (l L : ℕ) (Pvec : BlockVec d) :
    0 ≤ localizationAverageT1FourthSqrtAmplitude C nu l L Pvec := by
  unfold localizationAverageT1FourthSqrtAmplitude
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hnu _))
    (Real.sqrt_nonneg _)) (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)

/-! ## The two amplitudes are the squares of their square roots -/

/-- `(x^(-2))² = x^(-4)` for `x > 0`. -/
private theorem rpow_neg_two_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-(2 : ℝ))) ^ 2 = x ^ (-(4 : ℝ)) := by
  rw [sq, ← Real.rpow_add hx, show -(2 : ℝ) + -(2 : ℝ) = -(4 : ℝ) by norm_num]

/-- `(x^(-1))² = x^(-2)` for `x > 0`. -/
private theorem rpow_neg_one_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (-(1 : ℝ))) ^ 2 = x ^ (-(2 : ℝ)) := by
  rw [sq, ← Real.rpow_add hx, show -(1 : ℝ) + -(1 : ℝ) = -(2 : ℝ) by norm_num]

/-- `(x^(-a))² = x^(-(2a))` for `x > 0`. -/
private theorem rpow_neg_sq {x : ℝ} (hx : 0 < x) (a : ℝ) :
    (x ^ (-a)) ^ 2 = x ^ (-(2 * a)) := by
  rw [sq, ← Real.rpow_add hx, show -a + -a = -(2 * a) by ring]

/-- The square of the second-moment square root amplitude is the printed
second-moment amplitude. -/
theorem localizationAverageT1SecondSqrtAmplitude_sq {C nu : ℝ} (hC : 0 ≤ C) (hnu : 0 < nu)
    (l n : ℕ) :
    localizationAverageT1SecondSqrtAmplitude C nu l n ^ 2 =
      localizationAverageT1SecondAmplitude C nu l n := by
  unfold localizationAverageT1SecondSqrtAmplitude localizationAverageT1SecondAmplitude
  rw [mul_pow, mul_pow, Real.sq_sqrt hC, rpow_neg_two_sq hnu,
    rpow_neg_sq (by norm_num : (0 : ℝ) < 3)]

/-- The square of the fourth-moment square root amplitude is the printed
fourth-moment amplitude. -/
theorem localizationAverageT1FourthSqrtAmplitude_sq {C nu : ℝ} (hC : 0 ≤ C) (hnu : 0 < nu)
    (l L : ℕ) (Pvec : BlockVec d) :
    localizationAverageT1FourthSqrtAmplitude C nu l L Pvec ^ 2 =
      localizationAverageT1FourthAmplitude C nu l L Pvec := by
  unfold localizationAverageT1FourthSqrtAmplitude localizationAverageT1FourthAmplitude
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hC, rpow_neg_one_sq hnu,
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]

/-! ## The enlarged constant -/

/-- The enlarged constant `C(d)` of the first summand: twice the
multiplication constant `orliczProductConst 1 (1/2)`, absorbing the factor `2`
of `√((1∨ℓ)² + (L-ℓ)²) ≤ 2L` on the branch `ℓ < L`. -/
noncomputable def localizationAverageT1Const : ℝ :=
  2 * SuperdiffusionCLT.Probability.orliczProductConst 1 ((1 : ℝ) / 2)

/-- The enlarged constant is positive. -/
theorem localizationAverageT1Const_pos : 0 < localizationAverageT1Const :=
  mul_pos (by norm_num)
    (SuperdiffusionCLT.Probability.orliczProductConst_pos 1 ((1 : ℝ) / 2))

/-- **The printed bound `L` for the square root of the fourth-moment
amplitude.**  On the branch `ℓ < L` one has `(1∨ℓ) ≤ L` and `L - ℓ ≤ L`, hence
`√((1∨ℓ)² + (L-ℓ)²) ≤ √(2L²) ≤ 2L`. -/
theorem sqrt_maxSq_add_sq_le {l L : ℕ} (hlL : l < L) :
    Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) ≤ 2 * (L : ℝ) := by
  have hL1 : 1 ≤ L := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le l) hlL)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have ha : max 1 (l : ℝ) ≤ (L : ℝ) :=
    max_le (by exact_mod_cast hL1) (by exact_mod_cast le_of_lt hlL)
  have hb : ((L - l : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L l
  have hann : 0 ≤ max 1 (l : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have hbnn : 0 ≤ ((L - l : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsq : (max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2 ≤ (2 * (L : ℝ)) ^ 2 := by
    have h1 : (max 1 (l : ℝ)) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hann ha 2
    have h2 : ((L - l : ℕ) : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hbnn hb 2
    nlinarith only [h1, h2, hLnn]
  calc Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2)
      ≤ Real.sqrt ((2 * (L : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * (L : ℝ) := Real.sqrt_sq (by positivity)

/-! ## The printed amplitude bookkeeping -/

/-- **The amplitude of the Cauchy--Schwarz combine is dominated by the printed
first summand amplitude.**  On the branch `ℓ < L`, the product of the `Γ_1`
and `Γ_{1/2}` square-root amplitudes multiplied by the multiplication constant
`orliczProductConst 1 (1/2)` is at most
`localizationAverageEnvelopeT1 (localizationAverageT1Const * C) ν ℓ L n Pvec`;
the enlarged constant is the printed enlargement of `C(d)`. -/
theorem localizationAverageT1_amplitude_le {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    {l L n : ℕ} (hlL : l < L) (Pvec : BlockVec d) :
    SuperdiffusionCLT.Probability.orliczProductConst 1 ((1 : ℝ) / 2) *
        (localizationAverageT1SecondSqrtAmplitude C nu l n *
          localizationAverageT1FourthSqrtAmplitude C nu l L Pvec) ≤
      localizationAverageEnvelopeT1 (localizationAverageT1Const * C) nu l L n Pvec := by
  have hM : Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) ≤ 2 * (L : ℝ) :=
    sqrt_maxSq_add_sq_le hlL
  have hp : 0 ≤ blockVecDot Pvec Pvec :=
    SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec
  have hX : 0 ≤ C * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
      blockVecDot Pvec Pvec :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hnu.le _))
      (Real.rpow_nonneg (by norm_num) _)) hp
  have hOP : 0 ≤ SuperdiffusionCLT.Probability.orliczProductConst 1 ((1 : ℝ) / 2) :=
    (SuperdiffusionCLT.Probability.orliczProductConst_pos 1 ((1 : ℝ) / 2)).le
  have hS2S4 : localizationAverageT1SecondSqrtAmplitude C nu l n *
        localizationAverageT1FourthSqrtAmplitude C nu l L Pvec =
      Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
        (C * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
          blockVecDot Pvec Pvec) := by
    unfold localizationAverageT1SecondSqrtAmplitude localizationAverageT1FourthSqrtAmplitude
    calc (Real.sqrt C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ))) *
          (Real.sqrt C * nu ^ (-(1 : ℝ)) *
            Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
            blockVecDot Pvec Pvec)
        = (Real.sqrt C * Real.sqrt C) * (nu ^ (-(2 : ℝ)) * nu ^ (-(1 : ℝ))) *
            ((3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
              Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
              blockVecDot Pvec Pvec) := by ring
      _ = C * (nu ^ (-(2 : ℝ)) * nu ^ (-(1 : ℝ))) *
            ((3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
              Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
              blockVecDot Pvec Pvec) := by rw [Real.mul_self_sqrt hC.le]
      _ = C * nu ^ (-(3 : ℝ)) *
            ((3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
              Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
              blockVecDot Pvec Pvec) := by
        rw [← Real.rpow_add hnu, show -(2 : ℝ) + -(1 : ℝ) = -(3 : ℝ) by norm_num]
      _ = Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
            (C * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
              blockVecDot Pvec Pvec) := by ring
  calc SuperdiffusionCLT.Probability.orliczProductConst 1 ((1 : ℝ) / 2) *
        (localizationAverageT1SecondSqrtAmplitude C nu l n *
          localizationAverageT1FourthSqrtAmplitude C nu l L Pvec)
      = SuperdiffusionCLT.Probability.orliczProductConst 1 ((1 : ℝ) / 2) *
          (Real.sqrt ((max 1 (l : ℝ)) ^ 2 + ((L - l : ℕ) : ℝ) ^ 2) *
            (C * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
              blockVecDot Pvec Pvec)) := by rw [hS2S4]
    _ ≤ SuperdiffusionCLT.Probability.orliczProductConst 1 ((1 : ℝ) / 2) *
          ((2 * (L : ℝ)) *
            (C * nu ^ (-(3 : ℝ)) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) *
              blockVecDot Pvec Pvec)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hX) hOP
    _ = localizationAverageEnvelopeT1 (localizationAverageT1Const * C) nu l L n Pvec := by
        unfold localizationAverageEnvelopeT1 localizationAverageT1Const
        rw [ite_eq_left hlL]
        ring

/-! ## The first summand at the printed envelope -/

/-- **The first printed summand of `e.localization.average.oneshot`.**
Let `T1` be pointwise dominated by the Cauchy--Schwarz product of the second-moment average
`D2` of the localization error and the fourth-moment average `B2` of the perturbed gauge
vectors.  If

1. `D2 = O_{Γ_{1/2}}(Cν⁻⁴3^{-2(ℓ-n)})` (the second-moment average),
2. `B2 = O_{Γ_{1/4}}(Cν⁻²((1∨ℓ)² + (L-ℓ)²)|P|⁴)` (the fourth-moment average), and
3. the localization error vanishes identically when `L = ℓ`,

then `T1 = O_{Γ_{1/3}}(1_{L>ℓ}Cν⁻³L3^{-(ℓ-n)}|P|²)` at the enlarged constant
`localizationAverageT1Const * C`.

The two square-root steps (`isBigO_gammaSigma_sqrt_of_sq`: `Γ_{1/2} ↝ Γ_1` and
`Γ_{1/4} ↝ Γ_{1/2}`), the multiplication property at `σ₁ = 1`, `σ₂ = 1/2`
(index `1/3`), the amplitude bookkeeping and the degenerate branch are all
discharged.  What remains named is the printed input: the two averages, the
pointwise Cauchy--Schwarz domination, the nonnegativity of the two averages,
and the vanishing of the localization error at `L = ℓ`. -/
theorem localizationAverage_T1 {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (l L n : ℕ) (Pvec : BlockVec d)
    (T1 D2 B2 : ShellSeq d → ℝ)
    (hcs : ∀ omega, |T1 omega| ≤ Real.sqrt (D2 omega) * Real.sqrt (B2 omega))
    (hD2nn : ∀ omega, 0 ≤ D2 omega) (hB2nn : ∀ omega, 0 ≤ B2 omega)
    (hD2zero : ¬ l < L → ∀ omega, D2 omega = 0)
    (hD2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2)) D2
      (localizationAverageT1SecondAmplitude C nu l n))
    (hB2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 4)) B2
      (localizationAverageT1FourthAmplitude C nu l L Pvec)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1 (localizationAverageT1Const * C) nu l L n Pvec) := by
  by_cases hlL : l < L
  · have hS2nn := localizationAverageT1SecondSqrtAmplitude_nonneg (C := C) hnu.le l n
    have hS4nn := localizationAverageT1FourthSqrtAmplitude_nonneg (C := C) hnu.le l L Pvec
    have hd2 : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 2)) D2
        (localizationAverageT1SecondSqrtAmplitude C nu l n ^ 2) := by
      rw [localizationAverageT1SecondSqrtAmplitude_sq hC.le hnu]
      exact hD2
    have hb2 : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma (((1 : ℝ) / 2) / 2)) B2
        (localizationAverageT1FourthSqrtAmplitude C nu l L Pvec ^ 2) := by
      rw [show ((1 : ℝ) / 2) / 2 = (1 : ℝ) / 4 by norm_num,
        localizationAverageT1FourthSqrtAmplitude_sq hC.le hnu]
      exact hB2
    have hsqrtD2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
        (fun omega => Real.sqrt (D2 omega))
        (localizationAverageT1SecondSqrtAmplitude C nu l n) :=
      isBigO_gammaSigma_sqrt_of_sq (σ := 1) hS2nn hD2nn hd2
    have hsqrtB2 : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) / 2))
        (fun omega => Real.sqrt (B2 omega))
        (localizationAverageT1FourthSqrtAmplitude C nu l L Pvec) :=
      isBigO_gammaSigma_sqrt_of_sq (σ := (1 : ℝ) / 2) hS4nn hB2nn hb2
    have hprod : IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma ((1 : ℝ) * ((1 : ℝ) / 2) / (1 + (1 : ℝ) / 2))) T1
        (SuperdiffusionCLT.Probability.orliczProductConst 1 ((1 : ℝ) / 2) *
          (localizationAverageT1SecondSqrtAmplitude C nu l n *
            localizationAverageT1FourthSqrtAmplitude C nu l L Pvec)) :=
      isBigO_gammaSigma_mul_of_abs_le_mul (σ₁ := 1) (σ₂ := (1 : ℝ) / 2)
        (by norm_num) (by norm_num) hS2nn hS4nn
        (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
        hcs hsqrtD2 hsqrtB2
    rw [show (1 : ℝ) * ((1 : ℝ) / 2) / (1 + (1 : ℝ) / 2) = (1 : ℝ) / 3 by norm_num] at hprod
    exact hprod.mono_scale (localizationAverageT1_amplitude_le hC hnu hlL Pvec)
  · have hzero : ∀ omega, T1 omega = 0 := by
      intro omega
      have h1 : |T1 omega| ≤ Real.sqrt (D2 omega) * Real.sqrt (B2 omega) := hcs omega
      rw [hD2zero hlL omega, Real.sqrt_zero, zero_mul] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have henv : localizationAverageEnvelopeT1 (localizationAverageT1Const * C) nu l L n Pvec
        = 0 := by
      unfold localizationAverageEnvelopeT1
      rw [ite_eq_right hlL]
      ring
    rw [henv]
    exact isBigO_gammaSigma_of_eq_zero (mu := P.toMeasure) (σ := (1 : ℝ) / 3) hzero

/-! ## The lattice average form of the first summand -/

/-- **Cauchy--Schwarz over a finite grid with the printed normalisation.**
For a nonempty grid and the normalised average `N⁻¹ ∑_i f_i g_i`, the printed
Cauchy--Schwarz step reads

`N⁻¹∑ f_i g_i ≤ (N⁻¹∑ f_i²)^{1/2}(N⁻¹∑ g_i²)^{1/2}`.

The normalisation is what makes this an identity of amplitudes rather than a
sum over the grid: `N⁻¹ = (N^{-1/2})²` is what splits the single factor
`N⁻¹` into the two square roots. -/
private theorem cardInv_mul_sum_le_sqrt_mul_sqrt {ι : Type*} (grid : Finset ι)
    (hne : grid.Nonempty) (f g : ι → ℝ) :
    (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, f i * g i ≤
      Real.sqrt ((grid.card : ℝ)⁻¹ * ∑ i ∈ grid, f i ^ 2) *
        Real.sqrt ((grid.card : ℝ)⁻¹ * ∑ i ∈ grid, g i ^ 2) := by
  have hNpos : 0 < (grid.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hNin : 0 ≤ (grid.card : ℝ)⁻¹ := inv_nonneg.mpr hNpos.le
  refine (mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt grid f g) hNin).trans
    (le_of_eq ?_)
  rw [Real.sqrt_mul hNin (∑ i ∈ grid, f i ^ 2), Real.sqrt_mul hNin (∑ i ∈ grid, g i ^ 2)]
  rw [show Real.sqrt ((grid.card : ℝ)⁻¹) * Real.sqrt (∑ i ∈ grid, f i ^ 2) *
        (Real.sqrt ((grid.card : ℝ)⁻¹) * Real.sqrt (∑ i ∈ grid, g i ^ 2)) =
      (Real.sqrt ((grid.card : ℝ)⁻¹) * Real.sqrt ((grid.card : ℝ)⁻¹)) *
        (Real.sqrt (∑ i ∈ grid, f i ^ 2) * Real.sqrt (∑ i ∈ grid, g i ^ 2)) by ring,
    Real.mul_self_sqrt hNin]

/-- **The first summand at the printed envelope, in its lattice-average form.**
The observable is the printed average
`T1 = N⁻¹∑_i D_i B_i` of the per-cube product of the localization error `D_i`
and the squared perturbed gauge vector `B_i`, and the two moment averages are
`D2 = N⁻¹∑_i D_i²` and `B2 = N⁻¹∑_i B_i²`.

The pointwise Cauchy--Schwarz step (`cardInv_mul_sum_le_sqrt_mul_sqrt`), the
nonnegativity of the two averages and the vanishing of the localization error
when `L = ℓ` (through `hDdzero`) are discharged from the carrier
data; surviving hypotheses are the carriers `hT1`, `hD2def`, `hB2def`, the
nonnegativity `hDdnn`, `hBdnn`, the vanishing `hDdzero`, and `hD2bound`, `hB2bound`. -/
theorem localizationAverage_T1_of_grid {C nu : ℝ} (hC : 0 < C) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (l L n : ℕ) (Pvec : BlockVec d)
    {ι : Type*} (grid : Finset ι) (hne : grid.Nonempty)
    (Dd Bd : ι → ShellSeq d → ℝ) (T1 D2 B2 : ShellSeq d → ℝ)
    (hT1 : ∀ omega, T1 omega = (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Dd i omega * Bd i omega)
    (hD2def : ∀ omega, D2 omega = (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Dd i omega ^ 2)
    (hB2def : ∀ omega, B2 omega = (grid.card : ℝ)⁻¹ * ∑ i ∈ grid, Bd i omega ^ 2)
    (hDdnn : ∀ i ∈ grid, ∀ omega, 0 ≤ Dd i omega)
    (hBdnn : ∀ i ∈ grid, ∀ omega, 0 ≤ Bd i omega)
    (hDdzero : ¬ l < L → ∀ i ∈ grid, ∀ omega, Dd i omega = 0)
    (hD2bound : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2))
      D2 (localizationAverageT1SecondAmplitude C nu l n))
    (hB2bound : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 4))
      B2 (localizationAverageT1FourthAmplitude C nu l L Pvec)) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1 (localizationAverageT1Const * C) nu l L n Pvec) := by
  have hNin : 0 ≤ (grid.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcs : ∀ omega, |T1 omega| ≤ Real.sqrt (D2 omega) * Real.sqrt (B2 omega) := by
    intro omega
    have hstep := cardInv_mul_sum_le_sqrt_mul_sqrt grid hne
      (fun i => Dd i omega) (fun i => Bd i omega)
    rw [← hD2def omega, ← hB2def omega] at hstep
    have hnn : 0 ≤ T1 omega := by
      rw [hT1 omega]
      exact mul_nonneg hNin (Finset.sum_nonneg fun i hi =>
        mul_nonneg (hDdnn i hi omega) (hBdnn i hi omega))
    rwa [abs_of_nonneg hnn, hT1 omega]
  have hD2nn : ∀ omega, 0 ≤ D2 omega := by
    intro omega
    rw [hD2def omega]
    exact mul_nonneg hNin (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hB2nn : ∀ omega, 0 ≤ B2 omega := by
    intro omega
    rw [hB2def omega]
    exact mul_nonneg hNin (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hD2zero : ¬ l < L → ∀ omega, D2 omega = 0 := by
    intro hnot omega
    rw [hD2def omega, Finset.sum_eq_zero (fun i hi => by rw [hDdzero hnot i hi omega]; simp),
      mul_zero]
  exact localizationAverage_T1 hC hnu P l L n Pvec T1 D2 B2 hcs hD2nn hB2nn hD2zero
    hD2bound hB2bound

end SuperdiffusionCLT.Section2.Localization
