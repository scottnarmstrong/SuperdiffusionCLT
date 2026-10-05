/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.Reductions
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolumeBelow

/-!
# The two crude ingredients for `e.sL.growth`

Lemma `l.shomm.vs.shomell` states a growth display
`e.sL.growth`; its proof uses two
separate ingredients: the crude linear bound `e.Enaught.vs.A.and.Ahom`
(`shom_r ≤ C nu⁻¹(1+r)`, used to seed and to bound the telescoping
construction) and the root lower bound `p.sstar.lower.bound`
(`sbComp_root_lower_bound_infinite`, `Reductions.lean`), which alone already
gives the *lower* half of `e.sL.growth` once the deterministic scale `L_g` is
chosen large enough (depending on `d, ν, c⋆, K`, per the statement of
`sigmaBar_cutoff_comparison`) to both clear the root bound's own threshold and to convert its
`log(ν⁻¹ L)` normalization to the printed `log L`.

This file proves both pieces unconditionally (no hypothesis beyond the
standing shell laws): `sbAsm_crude_growth_bound` and `sbAsm_growth_lower`.
The upper half of `e.sL.growth` needs the telescoping construction of
`l.shomm.vs.shomell#growth-construction`/`#growth-telescoping`, which reapplies
`e.sL.vs.sell` at `alpha = 0` recursively; that
construction is carried out in `GrowthUpper.lean`.
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-- **`e.Enaught.vs.A.and.Ahom`, crude form** (`p.homog.below`'s proof also cites this):
the infinite-volume running diffusivity is dominated by a dimension-only constant times
`nu⁻¹ (1 + r)`. Proved directly from the envelope `bfE_m`'s explicit upper-left
scalar (`envelopeUpperScalar`, `Section2/Annealed/Envelope.lean`), via the chain
`shom_r ≤ shom_r(cu_0) ≤ envelopeUpperScalar d nu r`: the first step inverts the
uniform lower bound on the lower-block sequence at `n = 0`, the second is the
envelope sandwich `sigmaBarSeq_le_envelopeUpperScalar`. -/
theorem sbAsm_crude_growth_bound (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (_hPrefix : ShellLawPrefix d P) (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P)
          (_hJ4 : ShellLawJ4 d P),
          ∀ r : ℕ,
            sigmaBarInfinite nu r P ≤ C * nu⁻¹ * (1 + (r : ℝ)) := by
  refine ⟨1 + 2 * cutoffEnvelopeConst d, ?_, ?_⟩
  · have hCge : 1 ≤ cutoffEnvelopeConst d := one_le_cutoffEnvelopeConst d
    linarith only [hCge]
  intro nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 r
  have hstep1 : sigmaBarInfinite nu r P ≤ sigmaBarSeq nu r P 0 := by
    have hkey : (sigmaBarSeq nu r P 0)⁻¹ ≤ sigmaBarStarInvLimit nu r P :=
      le_ciInf fun n ↦
        inv_sigmaBarSeq_zero_le_sigmaBarStarInvSeq hnu r hPrefix hJ2 hJ3 hJ4 n
    have h0pos := sigmaBarSeq_pos hnu r hPrefix hJ2 hJ3 hJ4 0
    have hinvpos : (0 : ℝ) < (sigmaBarSeq nu r P 0)⁻¹ := inv_pos.mpr h0pos
    have hanti := inv_anti₀ hinvpos hkey
    rw [inv_inv] at hanti
    show (sigmaBarStarInvLimit nu r P)⁻¹ ≤ sigmaBarSeq nu r P 0
    exact hanti
  have hstep2 : sigmaBarSeq nu r P 0 ≤ envelopeUpperScalar d nu r :=
    sigmaBarSeq_le_envelopeUpperScalar hnu r hPrefix hJ2 hJ3 hJ4 0
  have hCpos : (0 : ℝ) < cutoffEnvelopeConst d :=
    cutoffEnvelopeConst_pos d
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := by
    have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hnu).2 hnu1
    simpa only [inv_one] using h
  have hmaxle : max 1 (r : ℝ) ≤ 1 + (r : ℝ) := by
    apply max_le
    · linarith only [Nat.cast_nonneg (α := ℝ) r]
    · linarith only [Nat.cast_nonneg (α := ℝ) r]
  have hnu_le_nuinv : nu ≤ nu⁻¹ := le_trans hnu1 hnuinv1
  have h1mr_nonneg : (0 : ℝ) ≤ 1 + (r : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) r; linarith only [this]
  have hstep3 : envelopeUpperScalar d nu r ≤
      (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (1 + (r : ℝ)) := by
    unfold envelopeUpperScalar
    have ha : nu ≤ nu⁻¹ * (1 + (r : ℝ)) := by
      calc nu ≤ nu⁻¹ := hnu_le_nuinv
        _ = nu⁻¹ * 1 := by ring
        _ ≤ nu⁻¹ * (1 + (r : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith only [Nat.cast_nonneg (α := ℝ) r])
            (by positivity)
    have hb : 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (r : ℝ) ≤
        2 * cutoffEnvelopeConst d * nu⁻¹ * (1 + (r : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hmaxle
      positivity
    have hsum := add_le_add ha hb
    calc nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (r : ℝ) ≤
        nu⁻¹ * (1 + (r : ℝ)) + 2 * cutoffEnvelopeConst d * nu⁻¹ * (1 + (r : ℝ)) := hsum
      _ = (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * (1 + (r : ℝ)) := by ring
  exact le_trans hstep1 (le_trans hstep2 hstep3)

/-- **The lower half of `e.sL.growth`** (the right end of the display). The deterministic scale `Lg`
depends on `d, ν, c⋆, K` (it packages both the root bound's own threshold and
the conversion of that root's `log(ν⁻¹ L)` normalization to the printed
`log L`, which needs `L ≥ ν⁻¹`). -/
theorem sbAsm_growth_lower (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ Lg : ℕ,
              ∀ (P : ProbabilityMeasure (ShellSeq d))
                (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
                (hJ3 : ShellLawJ3 d P),
                ShellLawJ1Restriction d P → ShellLawJ4 d P →
                ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
                  ∀ L : ℕ, Lg ≤ L →
                    C⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2) *
                        Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) ≤
                      sigmaBarInfinite nu L P := by
  obtain ⟨Croot, hCroot, croot, hcroot, hcrootHalf, hRoot⟩ :=
    sbComp_root_lower_bound_infinite d hd
  have hcrootpos : (0 : ℝ) < croot := hcroot
  refine ⟨(2 : ℝ) ^ ((9 : ℝ) / 2) / croot, ?_, ?_⟩
  · have h2raw : (2 : ℝ) ≤ 1 / croot := by
      rw [le_div_iff₀ hcrootpos]
      linarith only [hcrootHalf]
    have h2 : (1 : ℝ) ≤ 1 / croot := by linarith only [h2raw]
    have h9 : (1 : ℝ) ≤ (2 : ℝ) ^ ((9 : ℝ) / 2) := by
      have : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ ((9 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using this
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ ((9 : ℝ) / 2) * (1 / croot) :=
        mul_le_mul h9 h2 (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ ((9 : ℝ) / 2) / croot := by ring
  intro nu hnu hnu1 cStar hcStar K
  set T : ℝ := Croot * cStar ^ (-(3 : ℝ)) *
      (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
        (1 + K) * Real.log (3 + nu⁻¹ + cStar⁻¹ + K)) with hTdef
  refine ⟨max (Nat.ceil T) (max (Nat.ceil nu⁻¹) 3), ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L hLg
  have hLg1 : Nat.ceil T ≤ L := le_trans (le_max_left _ _) hLg
  have hLg2 : Nat.ceil nu⁻¹ ≤ L := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLg)
  have hLg3 : 3 ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLg)
  have hthr : T ≤ (L : ℝ) := le_trans (Nat.le_ceil T) (by exact_mod_cast hLg1)
  have hnuinvL : nu⁻¹ ≤ (L : ℝ) := le_trans (Nat.le_ceil nu⁻¹) (by exact_mod_cast hLg2)
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLg3
  have hrootL := hRoot nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 L L le_rfl
    (by omega) (hTdef ▸ hthr)
  -- Convert `log(nu⁻¹ L)` to `log L`.
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL3]
  have hlogLpos : (0 : ℝ) < Real.log (L : ℝ) := Real.log_pos (by linarith only [hL3])
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := by
    have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1) hnu).2 hnu1
    simpa only [inv_one] using h
  have hprodL2 : nu⁻¹ * (L : ℝ) ≤ (L : ℝ) * (L : ℝ) :=
    mul_le_mul_of_nonneg_right hnuinvL hLpos.le
  have hprodpos : (0 : ℝ) < nu⁻¹ * (L : ℝ) := mul_pos (by linarith only [hnuinv1]) hLpos
  have hlogprod_le : Real.log (nu⁻¹ * (L : ℝ)) ≤ Real.log ((L : ℝ) * (L : ℝ)) :=
    Real.log_le_log hprodpos hprodL2
  have hlogsq : Real.log ((L : ℝ) * (L : ℝ)) = 2 * Real.log (L : ℝ) := by
    rw [← sq, Real.log_pow]
    push_cast; ring
  have hlogprod_le2 : Real.log (nu⁻¹ * (L : ℝ)) ≤ 2 * Real.log (L : ℝ) := by
    rw [hlogsq] at hlogprod_le; exact hlogprod_le
  have hlogprodpos : (0 : ℝ) < Real.log (nu⁻¹ * (L : ℝ)) := by
    apply Real.log_pos
    have h1 : (3 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
      calc (3 : ℝ) = 1 * 3 := by ring
        _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul hnuinv1 hL3 (by norm_num) (by linarith only [hnuinv1])
    linarith only [h1]
  have hrpow_le : ((2 : ℝ) * Real.log (L : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
      Real.log (nu⁻¹ * (L : ℝ)) ^ (-((9 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hlogprodpos hlogprod_le2 (by norm_num)
  have hmulrpow : ((2 : ℝ) * Real.log (L : ℝ)) ^ (-((9 : ℝ) / 2)) =
      (2 : ℝ) ^ (-((9 : ℝ) / 2)) * Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) :=
    Real.mul_rpow (by norm_num) hlogLpos.le
  have hcoeffnonneg : (0 : ℝ) ≤ croot * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
      (L : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have hstepmul :
      (croot * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) *
          (((2 : ℝ) * Real.log (L : ℝ)) ^ (-((9 : ℝ) / 2))) ≤
        (croot * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) *
          (Real.log (nu⁻¹ * (L : ℝ)) ^ (-((9 : ℝ) / 2))) :=
    mul_le_mul_of_nonneg_left hrpow_le hcoeffnonneg
  rw [hmulrpow] at hstepmul
  have hfinal :
      (croot * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) *
          ((2 : ℝ) ^ (-((9 : ℝ) / 2)) * Real.log (L : ℝ) ^ (-((9 : ℝ) / 2))) ≤
        sigmaBarInfinite nu L P := by
    calc (croot * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) *
        ((2 : ℝ) ^ (-((9 : ℝ) / 2)) * Real.log (L : ℝ) ^ (-((9 : ℝ) / 2))) ≤
          (croot * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) *
            (Real.log (nu⁻¹ * (L : ℝ)) ^ (-((9 : ℝ) / 2))) := hstepmul
      _ ≤ sigmaBarInfinite nu L P := hrootL
  have hCeq : ((2 : ℝ) ^ ((9 : ℝ) / 2) / croot)⁻¹ =
      croot * (2 : ℝ) ^ (-((9 : ℝ) / 2)) := by
    rw [div_eq_mul_inv, mul_inv, inv_inv, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hlhs_eq :
      ((2 : ℝ) ^ ((9 : ℝ) / 2) / croot)⁻¹ * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
          (L : ℝ) ^ ((1 : ℝ) / 2) * Real.log (L : ℝ) ^ (-((9 : ℝ) / 2)) =
        (croot * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (L : ℝ) ^ ((1 : ℝ) / 2)) *
          ((2 : ℝ) ^ (-((9 : ℝ) / 2)) * Real.log (L : ℝ) ^ (-((9 : ℝ) / 2))) := by
    rw [hCeq]; ring
  rw [hlhs_eq]
  exact hfinal

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
