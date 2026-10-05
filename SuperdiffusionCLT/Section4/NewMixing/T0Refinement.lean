/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.T3Algebra
public import SuperdiffusionCLT.Section4.NewMixing.BranchBAbsorption
public import SuperdiffusionCLT.Section4.NewMixing.Nu4Threshold
public import SuperdiffusionCLT.Section4.SigmaBarComparison.Growth
public import SuperdiffusionCLT.Section4.NewMixing.Splitting

/-!
# `l.new.mixing.parameterized#T0-refinement`

Refines the general `T₀(P)` bound of `newMixAsm_localizationError_uniform`
(`AssemblyLocErr.lean`) to the specific vectors `P_e^σ`, reaching the
printed envelope `O_{Γ_{1/3}}(C m^{-3000}(1+shom_r^{-1}|h₀|²))`.

Two purely numeric ingredients, proved elsewhere and consumed here:
`newMixParam_threeNegH_le_mNeg12000` (`LogGrowth.lean`, the `m ≤ L+h` branch)
and `newMixParam_threeNeg_halfd_mMinusL_le_mNeg12000` (`BranchBAbsorption.lean`,
the `m > L+h` branch), together with `Nu4Threshold.lean`'s linear-in-`L` bound
on `ν⁻⁴` and `SigmaBarComparison.Growth`'s crude growth bound on `σ̄_r`.

This file supplies the pure quadratic-form / real-number algebra; the
`IsBigO.mono_scale` wiring into the full `T₀(P_e^σ)` statement is left to a
consuming file (see the module docstring's final remark).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

/-- **The `G_{-h₀}P_e^σ` quadratic form, exactly**: `|G_{-h₀}P_e^σ|² =
shom_r⁻¹|e|² + shom_r|e|² + shom_r⁻¹|h₀e|²`, as printed ("since `h₀` is skew,
`e·h₀e=0`, so `|G_{-h₀}P_e^σ|² = |P_e^σ|² + shom_r^{-1}|h₀e|²`"). Proved via
`newMixParam_blockQuad_expand` at `a = b = 1`. -/
theorem newMixParam_G_h0_PeSigma_eq (d : ℕ) [NeZero d]
    {nu : ℝ} {r : ℕ} {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {e : Vec d} {sigma : ℝ} (hsigma2 : sigma ^ 2 = 1)
    {h0 : Mat d} (hh0 : matTranspose h0 = -h0) :
    blockVecDot
        (blockMatVecMul (blockG (-h0))
          ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
            Real.sqrt (sigmaBarInfinite nu r P) • e))
        (blockMatVecMul (blockG (-h0))
          ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
            Real.sqrt (sigmaBarInfinite nu r P) • e)) =
      (sigmaBarInfinite nu r P)⁻¹ * vecNormSq e + (sigmaBarInfinite nu r P) * vecNormSq e +
        (sigmaBarInfinite nu r P)⁻¹ * vecNormSq (matVecMul h0 e) := by
  set shomr := sigmaBarInfinite nu r P with hshomrdef
  have hshomr : 0 < shomr := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  set c := sigma * Real.sqrt shomr⁻¹ with hcdef
  set s := Real.sqrt shomr with hsdef
  have hc2 : c ^ 2 = shomr⁻¹ := by
    rw [hcdef, mul_pow, hsigma2, one_mul, Real.sq_sqrt (inv_nonneg.mpr hshomr.le)]
  have hs2 : s ^ 2 = shomr := by rw [hsdef, Real.sq_sqrt hshomr.le]
  have hexpand := newMixParam_blockQuad_expand (a := (1 : ℝ)) (b := (1 : ℝ))
    (c := c) (s := s) (e := e) (hSum := h0) hh0
  have hblockeq : Book.Ch02.blockDiag ((1 : ℝ) • (1 : Mat d)) ((1 : ℝ) • (1 : Mat d)) =
      Book.Ch02.blockIdentity d := by
    simp [Book.Ch02.blockIdentity]
  rw [hblockeq, Homogenization.blockMatVecMul_blockIdentity] at hexpand
  rw [hexpand, hc2, hs2]
  ring

/-- **The `P_e^σ` quadratic form is polynomially bounded**: `shom_r⁻¹|e|² +
shom_r|e|² ≤ C(d) ν⁻¹ (1+r)`, from the crude growth bound
`sbAsm_crude_growth_bound` (`shom_r ≤ C ν⁻¹(1+r)`) and the envelope bound
`shom_r⁻¹ ≤ 2 cutoffEnvelopeConst(d) ν⁻¹` (`sigmaBarStarInvLimit_le` at `n=0`
composed with `sigmaBarStarInvSeq_le_envelopeLowerScalar`), as in the paper
("the crude upper bound on `σ̄_r`... imply that `|P_e^σ|²` is bounded by a
polynomial in `L`"; here bounded in terms of `ν⁻¹(1+r)`, converted to a
polynomial in `L` downstream via `r ≤ 2L`). -/
theorem newMixParam_PeSigma_normSq_le (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (r : ℕ) (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (_hPrefix : ShellLawPrefix d P) (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P)
          (_hJ4 : ShellLawJ4 d P) (e : Vec d), vecNormSq e ≤ 1 →
          (sigmaBarInfinite nu r P)⁻¹ * vecNormSq e + (sigmaBarInfinite nu r P) * vecNormSq e ≤
            C * nu⁻¹ * (1 + (r : ℝ)) := by
  obtain ⟨Ccrude, hCcrude1, hCrude⟩ := SuperdiffusionCLT.Section4.SigmaBarComparison.sbAsm_crude_growth_bound d
  refine ⟨2 * cutoffEnvelopeConst d + Ccrude, ?_, ?_⟩
  · have h1 := one_le_cutoffEnvelopeConst d
    linarith only [h1, hCcrude1]
  intro nu hnu hnu1 r P hPrefix hJ2 hJ3 hJ4 e he
  set shomr := sigmaBarInfinite nu r P with hshomrdef
  have hshomr : 0 < shomr := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  have hnuinv : (0 : ℝ) < nu⁻¹ := inv_pos.mpr hnu
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have h1r : (1 : ℝ) ≤ 1 + (r : ℝ) := by linarith only [hrnn]
  -- `shom_r⁻¹ ≤ 2 cutoffEnvelopeConst(d) ν⁻¹`.
  have hSinvle : shomr⁻¹ ≤ envelopeLowerScalar d nu := by
    have h1 : sigmaBarStarInvLimit nu r P ≤ sigmaBarStarInvSeq nu r P 0 :=
      sigmaBarStarInvLimit_le hnu r hPrefix hJ2 hJ3 hJ4 0
    have h2 : sigmaBarStarInvSeq nu r P 0 ≤ envelopeLowerScalar d nu :=
      sigmaBarStarInvSeq_le_envelopeLowerScalar hnu r hPrefix hJ2 hJ3 hJ4 0
    have heq : shomr⁻¹ = sigmaBarStarInvLimit nu r P := by
      rw [hshomrdef, sigmaBarInfinite, inv_inv]
    rw [heq]
    exact le_trans h1 h2
  have hSinvle' : shomr⁻¹ ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ := by
    rw [envelopeLowerScalar] at hSinvle; exact hSinvle
  -- `shom_r ≤ Ccrude ν⁻¹(1+r)`.
  have hSle : shomr ≤ Ccrude * nu⁻¹ * (1 + (r : ℝ)) := hCrude nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 r
  have hSinvpos : (0 : ℝ) ≤ shomr⁻¹ := (inv_pos.mpr hshomr).le
  have hSpos : (0 : ℝ) ≤ shomr := hshomr.le
  have hCcrudenn : (0 : ℝ) ≤ Ccrude := le_trans zero_le_one hCcrude1
  have hCcrude_nu_nn : (0 : ℝ) ≤ Ccrude * nu⁻¹ := mul_nonneg hCcrudenn hnuinv.le
  have hCEpos : (0 : ℝ) < cutoffEnvelopeConst d := cutoffEnvelopeConst_pos d
  have hCEnn : (0 : ℝ) ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ := by
    have := mul_nonneg (by linarith only [hCEpos] : (0:ℝ) ≤ 2 * cutoffEnvelopeConst d) hnuinv.le
    linarith only [this]
  have hSinv1r : shomr⁻¹ ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ * (1 + (r : ℝ)) := by
    calc shomr⁻¹ ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ := hSinvle'
      _ = 2 * cutoffEnvelopeConst d * nu⁻¹ * 1 := (mul_one _).symm
      _ ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ * (1 + (r : ℝ)) :=
          mul_le_mul_of_nonneg_left h1r hCEnn
  have hstep1 : shomr⁻¹ * vecNormSq e ≤ shomr⁻¹ := by nlinarith only [he, hSinvpos]
  have hstep2 : shomr * vecNormSq e ≤ shomr := by nlinarith only [he, hSpos]
  have hsum : shomr⁻¹ + shomr ≤
      2 * cutoffEnvelopeConst d * nu⁻¹ * (1 + (r : ℝ)) + Ccrude * nu⁻¹ * (1 + (r : ℝ)) := by
    linarith only [hSinv1r, hSle]
  have heq2 : 2 * cutoffEnvelopeConst d * nu⁻¹ * (1 + (r : ℝ)) + Ccrude * nu⁻¹ * (1 + (r : ℝ)) =
      (2 * cutoffEnvelopeConst d + Ccrude) * nu⁻¹ * (1 + (r : ℝ)) := by ring
  linarith only [hstep1, hstep2, hsum, heq2.le, heq2.ge]

/-- **The combined `|G_{-h₀}P_e^σ|²` bound**: `|G_{-h₀}P_e^σ|² ≤
C(d) ν⁻¹(1+r) + shom_r⁻¹|h₀|²`. Combines `newMixParam_G_h0_PeSigma_eq`,
`newMixParam_PeSigma_normSq_le`, and the operator-norm bound
`newMixParam_vecNormSq_matVecMul_le` on the surviving `shom_r⁻¹|h₀e|²` term
(kept as the *exact* factor `shom_r⁻¹`, matching the target `l.new.mixing.
parameterized#T0-refinement` envelope `1+shom_r^{-1}|h₀|²` verbatim). -/
theorem newMixParam_G_h0_PeSigma_le (d : ℕ) [NeZero d] :
    ∃ Cv : ℝ, 1 ≤ Cv ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (r : ℕ) (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ (e : Vec d), vecNormSq e ≤ 1 →
            ∀ (sigma : ℝ), sigma ^ 2 = 1 →
              ∀ (h0 : Mat d), matTranspose h0 = -h0 →
                blockVecDot
                    (blockMatVecMul (blockG (-h0))
                      ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                        Real.sqrt (sigmaBarInfinite nu r P) • e))
                    (blockMatVecMul (blockG (-h0))
                      ((sigma * Real.sqrt (sigmaBarInfinite nu r P)⁻¹) • e,
                        Real.sqrt (sigmaBarInfinite nu r P) • e)) ≤
                  Cv * nu⁻¹ * (1 + (r : ℝ)) +
                    (sigmaBarInfinite nu r P)⁻¹ * matrixOperatorNorm h0 ^ 2 := by
  obtain ⟨Cv, hCv1, hCv⟩ := newMixParam_PeSigma_normSq_le d
  refine ⟨Cv, hCv1, ?_⟩
  intro nu hnu hnu1 r P hPrefix hJ2 hJ3 hJ4 e he sigma hsigma2 h0 hh0
  have heq := newMixParam_G_h0_PeSigma_eq d (r := r) hnu hPrefix hJ2 hJ3 hJ4 (e := e)
    (sigma := sigma) hsigma2 (h0 := h0) hh0
  have hbound := hCv nu hnu hnu1 r P hPrefix hJ2 hJ3 hJ4 e he
  have hshomr : 0 < sigmaBarInfinite nu r P := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  have hop : vecNormSq (matVecMul h0 e) ≤ matrixOperatorNorm h0 ^ 2 * vecNormSq e :=
    newMixParam_vecNormSq_matVecMul_le h0 e
  have hopnn : (0 : ℝ) ≤ matrixOperatorNorm h0 ^ 2 := by positivity
  have hop2 : matrixOperatorNorm h0 ^ 2 * vecNormSq e ≤ matrixOperatorNorm h0 ^ 2 := by
    nlinarith only [he, hopnn]
  have hop3 : vecNormSq (matVecMul h0 e) ≤ matrixOperatorNorm h0 ^ 2 := le_trans hop hop2
  have hshomrinvnn : (0 : ℝ) ≤ (sigmaBarInfinite nu r P)⁻¹ := (inv_pos.mpr hshomr).le
  have hop4 : (sigmaBarInfinite nu r P)⁻¹ * vecNormSq (matVecMul h0 e) ≤
      (sigmaBarInfinite nu r P)⁻¹ * matrixOperatorNorm h0 ^ 2 :=
    mul_le_mul_of_nonneg_left hop3 hshomrinvnn
  rw [heq]
  linarith only [hbound, hop4]

/-- **The localization-error bracket, branch `m ≤ L+h`** (`ell - n = h`,
`m - ell = h`): both summands of the bracket
are dominated by `L² m^{-12000}` up to the polynomial prefactor `1+ell(m-n)`.
The second summand's exponent `(d/2)(m-ell) = (d/2)h` is bounded via `3^{-(d/2)h}
≤ 3^{-h}` (`d ≥ 2` gives `d/2 ≥ 1`) and then `newMixParam_threeNegH_le_mNeg12000`'s
`3^{-h} ≤ m^{-12000}`. -/
theorem newMixParam_bracket_branchA (d : ℕ) (hd : 2 ≤ d)
    {L m ell n h : ℕ} (hell_n : ell - n = h) (hm_ell : m - ell = h)
    (hfact : (3 : ℝ) ^ (-(h : ℝ)) ≤ (m : ℝ) ^ (-(12000 : ℝ))) :
    (if ell < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
        (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) ≤
      (1 + (ell : ℝ) * ((m - n : ℕ) : ℝ)) * (L : ℝ) ^ 2 * (m : ℝ) ^ (-(12000 : ℝ)) := by
  have hLsqnn : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hmpownn : (0 : ℝ) ≤ (m : ℝ) ^ (-(12000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hellnn : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hmnnn : (0 : ℝ) ≤ ((m - n : ℕ) : ℝ) := Nat.cast_nonneg _
  -- First (indicator) term: `≤ L² m^{-12000}` in either case of the `if`.
  have hterm1 : (if ell < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) ≤
      (L : ℝ) ^ 2 * (m : ℝ) ^ (-(12000 : ℝ)) := by
    split_ifs with hcase
    · rw [hell_n]; exact mul_le_mul_of_nonneg_left hfact hLsqnn
    · positivity
  -- Second term's exponent: `(d/2)(m-ell) = (d/2)h`.
  have hdhalf : (1 : ℝ) ≤ (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [this]
  have hhnn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  have hmell_eq : ((m - ell : ℕ) : ℝ) = (h : ℝ) := by rw [hm_ell]
  have hexp_le : -((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ)) ≤ -(h : ℝ) := by
    rw [hmell_eq]
    have : (h : ℝ) ≤ (d : ℝ) / 2 * (h : ℝ) := by nlinarith only [hdhalf, hhnn]
    linarith only [this]
  have hterm2exp : (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) ≤ (3 : ℝ) ^ (-(h : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
  have hterm2exp' : (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) ≤ (m : ℝ) ^ (-(12000 : ℝ)) :=
    le_trans hterm2exp hfact
  have hcoefnn : (0 : ℝ) ≤ (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) := by positivity
  have hterm2 : (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) ≤
      (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) * (m : ℝ) ^ (-(12000 : ℝ)) :=
    mul_le_mul_of_nonneg_left hterm2exp' hcoefnn
  have heq : (1 + (ell : ℝ) * ((m - n : ℕ) : ℝ)) * (L : ℝ) ^ 2 * (m : ℝ) ^ (-(12000 : ℝ)) =
      (L : ℝ) ^ 2 * (m : ℝ) ^ (-(12000 : ℝ)) +
        (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) * (m : ℝ) ^ (-(12000 : ℝ)) := by ring
  linarith only [hterm1, hterm2, heq.le, heq.ge]

/-- **The localization-error bracket, branch `m > L+h`** (`ell = L`):
the indicator term vanishes (`ell = L` is not
`< L`), and the surviving term `L³(m-n)3^{-(d/2)(m-L)}` is dominated by
`newMixParam_threeNeg_halfd_mMinusL_le_mNeg12000`'s `3^{-(d/2)(m-L)} ≤
m^{-12000}` directly. -/
theorem newMixParam_bracket_branchB (d : ℕ) {L m ell n : ℕ} (hell_eq : ell = L)
    (hfact : (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - L : ℕ) : ℝ))) ≤ (m : ℝ) ^ (-(12000 : ℝ))) :
    (if ell < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) +
        (ell : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - ell : ℕ) : ℝ))) ≤
      (L : ℝ) ^ 3 * ((m - n : ℕ) : ℝ) * (m : ℝ) ^ (-(12000 : ℝ)) := by
  have hmnnn : (0 : ℝ) ≤ ((m - n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hite : (if ell < L then (L : ℝ) ^ 2 * (3 : ℝ) ^ (-((ell - n : ℕ) : ℝ)) else 0) = 0 := by
    simp only [hell_eq, lt_self_iff_false, ↓reduceIte]
  rw [hite, zero_add, hell_eq]
  have hcoefnn : (0 : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) := by positivity
  have hstep : (L : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2 * ((m - L : ℕ) : ℝ))) ≤
      (L : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) * (m : ℝ) ^ (-(12000 : ℝ)) :=
    mul_le_mul_of_nonneg_left hfact hcoefnn
  have heq : (L : ℝ) * (L : ℝ) ^ 2 * ((m - n : ℕ) : ℝ) * (m : ℝ) ^ (-(12000 : ℝ)) =
      (L : ℝ) ^ 3 * ((m - n : ℕ) : ℝ) * (m : ℝ) ^ (-(12000 : ℝ)) := by ring
  linarith only [hstep, heq.le, heq.ge]

/-- **`L ≤ 2m` and `r ≤ 2L`**, from the standing hypotheses `m ≥ L - M L^α
log³L` and `|L-r| ≤ K log L` together with `newMixParam_absorbSlack`'s slack
bounds, applied at the caller's own shared `C` (`1 ≤ C`, so `1/(2C) ≤ 1/2`);
the caller supplies `newMixParam_absorbSlack`'s witness `C0` and `C0 ≤ C`
directly (from having chosen `C := max C0 (...)`). Reusable by both
`T0-refinement` branches for the `L`-to-`m` polynomial-degree conversion. -/
theorem newMixParam_t0_L_le_2m_r_le_2L {C0 C M K alpha cStar nu nondeg : ℝ}
    (_hC0 : 1 ≤ C0)
    (hslack : ∀ C : ℝ, C0 ≤ C →
      ∀ M K alpha cStar nu nondeg : ℝ,
        1 ≤ M → 1 ≤ K → 0 ≤ alpha → alpha < 1 → 0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 →
        0 ≤ nondeg →
        ∀ L : ℕ,
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
              (L : ℝ) →
          (8 : ℝ) < (L : ℝ) ∧
          M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / (2 * C) ∧
          K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / (2 * C))
    (hC0' : C0 ≤ C) (hC1 : 1 ≤ C) (hM : 1 ≤ M) (hK : 1 ≤ K) (hα0 : 0 ≤ alpha) (hα1 : alpha < 1)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hnondeg : 0 ≤ nondeg)
    {L m r : ℕ}
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
      (L : ℝ))
    (hLm : (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ))
    (hLr : |(L : ℝ) - (r : ℝ)| ≤ K * Real.log (L : ℝ)) :
    (L : ℝ) ≤ 2 * (m : ℝ) ∧ (r : ℝ) ≤ 2 * (L : ℝ) := by
  obtain ⟨hL8, hMslack, hKslack⟩ :=
    hslack C hC0' M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by linarith only [hL8]
  have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have hlogL1 : (1 : ℝ) < Real.log (L : ℝ) := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h9 : (3 : ℝ) ≤ (L : ℝ) := by linarith only [hL8]
    have h1 : Real.exp 1 < (L : ℝ) := lt_of_lt_of_le he3 h9
    have h2 := Real.log_lt_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  -- `M L^α log³L ≤ L/2`, hence `m ≥ L/2`.
  have hMhalf : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2 := by
    have h2C : (L : ℝ) / (2 * C) ≤ (L : ℝ) / 2 := by
      apply div_le_div_of_nonneg_left (by linarith only [hL1]) (by norm_num)
      nlinarith only [hC1]
    linarith only [hMslack, h2C]
  have hmL2 : (L : ℝ) ≤ 2 * (m : ℝ) := by linarith only [hLm, hMhalf]
  -- `K log L ≤ L/2`, hence `r ≤ 2L`.
  have hLalpha1 : (1 : ℝ) ≤ (L : ℝ) ^ alpha := newMixParam_one_le_rpow hL1 hα0
  have hlog3geLog : Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
    newMixParam_le_rpow_three hlogL1.le
  have hlog3nn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := le_trans hlogLnn hlog3geLog
  have hKlog_le : K * Real.log (L : ℝ) ≤ K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
    have hstepLE : Real.log (L : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      calc Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := hlog3geLog
        _ = 1 * Real.log (L : ℝ) ^ (3 : ℝ) := (one_mul _).symm
        _ ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right hLalpha1 hlog3nn
    exact mul_le_mul_of_nonneg_left hstepLE (by linarith only [hK])
  have hKhalf : K * Real.log (L : ℝ) ≤ (L : ℝ) / 2 := by
    have heq : K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) =
        K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
    have h2C : (L : ℝ) / (2 * C) ≤ (L : ℝ) / 2 := by
      apply div_le_div_of_nonneg_left (by linarith only [hL1]) (by norm_num)
      nlinarith only [hC1]
    linarith only [hKlog_le, heq.le, heq.ge, hKslack, h2C]
  have hrL2 : (r : ℝ) ≤ 2 * (L : ℝ) := by
    have habs := (abs_le.mp hLr).1
    linarith only [habs, hKhalf]
  exact ⟨hmL2, hrL2⟩

/-- **`h ≤ L/4`**, the tighter companion of `newMixParam_t0_L_le_2m_r_le_2L`
needed to keep `ell := m - h ≥ 1` (branch A): with `C ≥ 100000` (not merely
`C ≥ 1`), `K log L ≤ L/(2C) ≤ L/200000`, so `h ≤ 24000·(K log L) ≤ L/4`
(`newMixParam_h_le`, `newMixParam_h_le_L_div_4`'s public reproduction). -/
theorem newMixParam_t0_h_le_L_div_4 {C0 C M K alpha cStar nu nondeg : ℝ}
    (_hC0 : 1 ≤ C0)
    (hslack : ∀ C : ℝ, C0 ≤ C →
      ∀ M K alpha cStar nu nondeg : ℝ,
        1 ≤ M → 1 ≤ K → 0 ≤ alpha → alpha < 1 → 0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 →
        0 ≤ nondeg →
        ∀ L : ℕ,
          SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
              (L : ℝ) →
          (8 : ℝ) < (L : ℝ) ∧
          M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / (2 * C) ∧
          K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / (2 * C))
    (hC0' : C0 ≤ C) (hC100000 : (100000 : ℝ) ≤ C) (hM : 1 ≤ M) (hK : 1 ≤ K) (hα0 : 0 ≤ alpha)
    (hα1 : alpha < 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hnondeg : 0 ≤ nondeg)
    {L : ℕ}
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C (C * (M + K)) alpha cStar nu nondeg ≤
      (L : ℝ)) :
    (newMixParam_h K (Real.log (L : ℝ)) : ℝ) ≤ (L : ℝ) / 4 := by
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC100000
  obtain ⟨hL8, _, hKslack⟩ :=
    hslack C hC0' M K alpha cStar nu nondeg hM hK hα0 hα1 hcStar hcStar2 hnu hnu1 hnondeg L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by linarith only [hL8]
  have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have hlogL1 : (1 : ℝ) < Real.log (L : ℝ) := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h9 : (3 : ℝ) ≤ (L : ℝ) := by linarith only [hL8]
    have h1 : Real.exp 1 < (L : ℝ) := lt_of_lt_of_le he3 h9
    have h2 := Real.log_lt_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hLalpha1 : (1 : ℝ) ≤ (L : ℝ) ^ alpha := newMixParam_one_le_rpow hL1 hα0
  have hlog3geLog : Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
    newMixParam_le_rpow_three hlogL1.le
  have hlog3nn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := le_trans hlogLnn hlog3geLog
  have hKlogL_le_slack : K * Real.log (L : ℝ) ≤ (L : ℝ) / (2 * C) := by
    have hstepLE : Real.log (L : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      calc Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := hlog3geLog
        _ = 1 * Real.log (L : ℝ) ^ (3 : ℝ) := (one_mul _).symm
        _ ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right hLalpha1 hlog3nn
    have h1 : K * Real.log (L : ℝ) ≤ K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hstepLE (by linarith only [hK])
    have h2 : K * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) =
        K * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
    rw [h2] at h1
    exact le_trans h1 hKslack
  have hx1 : (1 : ℝ) ≤ newMixParam_K0 * K * Real.log (L : ℝ) := by
    unfold newMixParam_K0
    nlinarith only [hK, hlogL1]
  have hhle := newMixParam_h_le hx1
  have hK0eq : newMixParam_K0 = 12000 := rfl
  have h1 : (newMixParam_h K (Real.log (L : ℝ)) : ℝ) ≤ 24000 * (K * Real.log (L : ℝ)) := by
    have heqassoc : newMixParam_K0 * K * Real.log (L : ℝ) =
        newMixParam_K0 * (K * Real.log (L : ℝ)) := by ring
    rw [heqassoc, hK0eq] at hhle
    linarith only [hhle]
  have h2 : (24000 : ℝ) * (K * Real.log (L : ℝ)) ≤ 24000 * ((L : ℝ) / (2 * C)) :=
    mul_le_mul_of_nonneg_left hKlogL_le_slack (by norm_num)
  have h3 : (L : ℝ) / (2 * C) ≤ (L : ℝ) / 200000 := by
    apply div_le_div_of_nonneg_left (by linarith only [hL1]) (by norm_num)
    linarith only [hC100000]
  have h4 : (24000 : ℝ) * ((L : ℝ) / 200000) ≤ (L : ℝ) / 4 := by
    have heq : (24000 : ℝ) * ((L : ℝ) / 200000) = (L : ℝ) * (24000 / 200000) := by ring
    rw [heq]
    have heq2 : (L : ℝ) / 4 = (L : ℝ) * (1 / 4) := by ring
    rw [heq2]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg L)
    norm_num
  linarith only [h1, h2, h3, h4]

end
end SuperdiffusionCLT.Section4.NewMixing
