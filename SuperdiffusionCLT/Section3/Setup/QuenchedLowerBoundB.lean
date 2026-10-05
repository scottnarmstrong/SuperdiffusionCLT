/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.QuenchedLowerBound

/-!
# The quenched conjunct `e.sstar.lower.bound.quenched`

The paper closes the proof of
Proposition `p.sstar.lower.bound`: with `n₀ = ⌊m/2⌋` and the deterministic
bound on `σ̄_{L,*}^{-1}(cu_{n₀})` of `QuenchedLowerBound` in hand, the
print applies `e.sstarL.quenched.lb` (Lemma `l.mixing.minscale`) with
`h = n₀` and `n = m`, which gives

`s_{L,*}^{-1}(cu_m) ≤ σ̄_{L,*}^{-1}(cu_{n₀}) + O_{Γ₂}(C ν^{-2} 3^{-(m-n₀)/4} Id)`,

and observes that `m - n₀ ≥ m/2`, so that the Orlicz amplitude is at most
`C ν^{-2} 3^{-m/8}`.  Since `σ̄_{L,*}^{-1}(cu_{n₀})` is a scalar matrix, the sum
is the scalar matrix of the conclusion.

## What is proved here

* `matLoewnerLE_smul_one_add` — the Loewner comparison of two scalar matrices
  perturbed by the same scalar matrix.
* `quenched_error_amplitude_le` — `m - n₀ ≥ m/2`, i.e.
  `C ν^{-2} 3^{-(m-n₀)/4} ≤ C ν^{-2} 3^{-m/8}`.
* `sstar_lower_bound_quenched` — the quenched conjunct of the root theorem
  `Frozen.Section3.sigmaBarStar_lower_bound`, in its exact conclusion
  shape.

## What is not proved here

`e.sstarL.quenched.lb` itself.  It is the statement
`Frozen.Section2.sigmaStarInv_mixing_minscale`; its
first conjunct is carried here as the single explicit hypothesis
`hMix`, copied verbatim from that conclusion (the
constant renamed `CM` and the inner cutoff binder renamed `l` to avoid
shadowing).  The two annealed inputs `hAnn` and `hLocal` are those of
`QuenchedLowerBound`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2

/-! ## Scalar matrices in the Loewner order -/

private theorem vecDot_matVecMul_smul_one {d : ℕ} (a : ℝ) (x : Vec d) :
    vecDot x (matVecMul (a • (1 : Mat d)) x) = a * vecNormSq x := by
  rw [show (a • (1 : Mat d)) = scalarMatrix (d := d) a from rfl,
    matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]

/-- The Loewner order between scalar matrices is the order of their scalars,
and it is stable under adding a common scalar matrix.  This is the step that
turns the additive comparison of `e.sstarL.quenched.lb` into the root theorem's
one-sided matrix inequality. -/
theorem matLoewnerLE_smul_one_add {d : ℕ} {a b y : ℝ} (hab : a ≤ b) :
    MatLoewnerLE (a • (1 : Mat d) + y • (1 : Mat d))
      (b • (1 : Mat d) + y • (1 : Mat d)) := by
  rw [← add_smul, ← add_smul]
  intro x
  have hx : (0 : ℝ) ≤ vecNormSq x := vecNormSq_nonneg x
  rw [vecDot_matVecMul_smul_one, vecDot_matVecMul_smul_one]
  have hmul := mul_le_mul_of_nonneg_right (add_le_add_right hab y) hx
  linarith only [hmul]

/-! ## The Orlicz amplitude -/

/-- **The rate**: `m - n₀ ≥ m/2`, so the amplitude
`C ν^{-2} 3^{-(m-n₀)/4}` of `e.sstarL.quenched.lb` is below the printed
`C ν^{-2} 3^{-m/8}`. -/
theorem quenched_error_amplitude_le {CM C nu : ℝ} {m n0 : ℕ}
    (hCM : 0 ≤ CM) (hC : CM ≤ C) (hnu : 0 < nu) (hm : m ≤ 2 * (m - n0)) :
    CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - n0 : ℕ) : ℝ) / 4)) ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8)) := by
  have hnu2 : (0 : ℝ) < nu ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hnu _
  have hmR : (m : ℝ) ≤ 2 * ((m - n0 : ℕ) : ℝ) := by exact_mod_cast hm
  have hexp : -(((m - n0 : ℕ) : ℝ) / 4) ≤ -((m : ℝ) / 8) := by
    linarith only [hmR]
  have hpow : (3 : ℝ) ^ (-(((m - n0 : ℕ) : ℝ) / 4)) ≤ (3 : ℝ) ^ (-((m : ℝ) / 8)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hpownn : (0 : ℝ) ≤ (3 : ℝ) ^ (-((m : ℝ) / 8)) :=
    Real.rpow_nonneg (by norm_num) _
  have h1 : CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - n0 : ℕ) : ℝ) / 4)) ≤
      CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8)) :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg hCM hnu2.le)
  have h2 : CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8)) ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC hnu2.le) hpownn
  exact le_trans h1 h2

/-! ## The quenched conjunct of `p.sstar.lower.bound` -/

/-- **The quenched estimate `e.sstar.lower.bound.quenched`**,
in the exact conclusion
shape of the second bracket of the root theorem
`Frozen.Section3.sigmaBarStar_lower_bound`.

The proof is the print's: `e.sstarL.quenched.lb` at `h = n₀ = ⌊m/2⌋`, `n = m`
and cutoff `L` bounds `s_{L,*}^{-1}(cu_m)` by `σ̄_{L,*}^{-1}(cu_{n₀})` plus an
`O_{Γ₂}(C ν^{-2} 3^{-(m-n₀)/4})` scalar; `m - n₀ ≥ m/2` turns the rate into the
printed `3^{-m/8}`; and `sigmaBarStarInvScalar_le_quenchedConst` replaces the
annealed matrix, which is scalar on an origin cube, by the printed
`C ν^{-2} c⋆^{-3/2} m^{-1/2} log^{9/2}(ν^{-1}m)`.

Explicit hypotheses beyond the standing data.

* `hAnn` — the annealed lower bound `e.sstar.lower.bound` at cutoff
  `R = 2⌊m/2⌋` and spatial scale `n₀`, i.e. the annealed lower bound of
  `Frozen.Section3.sigmaBarStar_lower_bound` read at `L := R`, `m̄ := n₀`.
* `hLocal`, `hEta` — `e.localization.s.star.annealed.applied` at
  the cutoff pair `(R, L)` on `cu_{n₀}`, and the absorption of its error;
  `localization_error_le_one` gives a sufficient threshold for `hEta`.
* `hMix` — the first conjunct of the conclusion of
  `Frozen.Section2.sigmaStarInv_mixing_minscale`, verbatim. -/
theorem sstar_lower_bound_quenched {d : ℕ} [NeZero d]
    {nu cStar c Ceta CM C : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L m : ℕ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hc : 0 < c) (hCM : 0 ≤ CM)
    (hCMC : CM ≤ C) (hquench : quenchedConst c ≤ C)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hm : 2 ≤ m) (hmL : m ≤ L)
    (hlog : 0 < Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)))
    (hAnn : c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
          ((quenchedInnerScale m : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
        sigmaBarStarScalar nu (quenchedCutoffScale m) P
          (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))))
    (hLocal : |sigmaBarStarScalar nu (quenchedCutoffScale m) P
            (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) *
          sigmaBarStarInvScalar nu L P
            (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))) - 1| ≤
        Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) *
          (3 : ℝ) ^ (-((quenchedInnerScale m : ℕ) : ℝ)))
    (hEta : Ceta * nu ^ (-(5 : ℝ)) * (L : ℝ) *
        (3 : ℝ) ^ (-((quenchedInnerScale m : ℕ) : ℝ)) ≤ 1)
    (hMix : ∀ h n l : ℕ, h < n → n ≤ l →
        ∃ X : ShellSeq d → ℝ,
          Measurable X ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
              (CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                (sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
                  (coefficientCutoff nu omega l).toCoeffField)
                (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                  X omega • (1 : Mat d))) :
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
          (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8))) ∧
        ∀ omega : ShellSeq d,
          MatLoewnerLE
            (sigmaStarInvCoarse (cubeSet (originCube d (m : ℤ)))
              (coefficientCutoff nu omega L).toCoeffField)
            ((C * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
                  (m : ℝ) ^ (-((1 : ℝ) / 2)) *
                  Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) • (1 : Mat d) +
              X omega • (1 : Mat d)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have h1 : 1 ≤ m := by omega
    exact_mod_cast h1
  have hn0le : ((quenchedInnerScale m : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast quenchedInnerScale_le m
  have hlogm : 0 < Real.log (nu⁻¹ * (m : ℝ)) := by
    have hn0R : (0 : ℝ) < ((quenchedInnerScale m : ℕ) : ℝ) := by
      have h1 : 1 ≤ quenchedInnerScale m := one_le_quenchedInnerScale hm
      exact_mod_cast h1
    have hmono := Real.log_le_log (mul_pos (inv_pos.2 hnu) hn0R)
      (mul_le_mul_of_nonneg_left hn0le (inv_pos.2 hnu).le)
    linarith only [hlog, hmono]
  -- the deterministic bound on the annealed scalar at `cu_{n₀}`
  have hscalar := sigmaBarStarInvScalar_le_quenchedConst (Ceta := Ceta) (L := L)
    hnu hcStar hc hPrefix hJ2 hJ3 hJ4 hm hlog hAnn hLocal hEta
  have hfacnn : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
      (m : ℝ) ^ (-((1 : ℝ) / 2)) * Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hnu.le _)
      (Real.rpow_nonneg hcStar.le _)) (Real.rpow_nonneg hmR.le _))
      (Real.rpow_nonneg hlogm.le _)
  have hconst : quenchedConst c * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
      (m : ℝ) ^ (-((1 : ℝ) / 2)) * Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) ≤
      C * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (m : ℝ) ^ (-((1 : ℝ) / 2)) * Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) := by
    have h := mul_le_mul_of_nonneg_right hquench hfacnn
    have e1 : quenchedConst c * (nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (m : ℝ) ^ (-((1 : ℝ) / 2)) * Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) =
        quenchedConst c * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
          (m : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) := by ring
    have e2 : C * (nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
        (m : ℝ) ^ (-((1 : ℝ) / 2)) * Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) =
        C * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
          (m : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2) := by ring
    rw [e1, e2] at h
    exact h
  -- the anchor at `(n₀, m, L)`
  obtain ⟨X, hXmeas, hXO, hXLoewner⟩ :=
    hMix (quenchedInnerScale m) m L (quenchedInnerScale_lt (by omega)) hmL
  refine ⟨X, hXmeas, hXO.mono_scale (quenched_error_amplitude_le hCM hCMC hnu
    (le_two_mul_sub_quenchedInnerScale m)), ?_⟩
  intro omega
  refine (hXLoewner omega).trans ?_
  rw [sigmaBarStarInv_originCube_eq_smul_one hnu L hJ4
    ((quenchedInnerScale m : ℕ) : ℤ)]
  exact matLoewnerLE_smul_one_add (le_trans hscalar hconst)

end SuperdiffusionCLT.Section3.Setup
