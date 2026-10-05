/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.RootChainComposedB
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

/-- The dimension-only logarithmic part of absorption follows from the threshold.
Only the mixed term involving the J5 error parameter remains. -/
theorem rootChainAbsorptionB_log_square {CM Ks A : ℝ}
    (hCM : 0 < CM) (hKs : 0 < Ks) (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K : ℝ,
      0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < K →
      ∀ L m : ℕ, m ≤ L →
      C*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) →
      8*CM*Ks*Real.log (nu⁻¹*(L : ℝ))^2 ≤ A*cStar^3*(L : ℝ) := by
  have hden : 0 < 8*CM*Ks := by positivity
  obtain ⟨C, hC, hc⟩ := rootChainComposedB_log_cube (div_pos hA hden)
  refine ⟨max C 100000000, le_trans hC (le_max_left _ _), ?_⟩
  intro nu cStar K hnu hnu1 hcs hcs2 hK L m hm hthr
  have ht : C*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) := by
    apply le_trans _ hthr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hcs.le _))
      (eLvsNuTerm_pos hnu hcs hK.le).le
  have hg := SuperdiffusionCLT.Section3.Terms.sstarCloseB_eleven_le_log
    hnu hnu1 hcs hcs2 hK (le_max_right C 100000000) hthr hm
  have hg1 : 1 ≤ Real.log (nu⁻¹*(L : ℝ)) := by linarith only [hg]
  have hpow : Real.log (nu⁻¹*(L : ℝ))^2 ≤ Real.log (nu⁻¹*(L : ℝ))^3 := by
    calc
      _ = Real.log (nu⁻¹*(L : ℝ))^2 * 1 := (mul_one _).symm
      _ ≤ Real.log (nu⁻¹*(L : ℝ))^2 * Real.log (nu⁻¹*(L : ℝ)) :=
        mul_le_mul_of_nonneg_left hg1 (sq_nonneg _)
      _ = _ := (pow_succ _ 2).symm
  have hh := mul_le_mul_of_nonneg_left
    (hpow.trans (hc nu cStar K hnu hnu1 hcs hK.le L m hm ht)) hden.le
  calc
    _ ≤ (8*CM*Ks)*(A/(8*CM*Ks)*(cStar^3*(L : ℝ))) := hh
    _ = _ := by
      rw [← mul_assoc, mul_div_cancel₀ _ hden.ne']
      ring

/-- Two half-budget estimates give the full lower-order absorption bound. -/
theorem rootChainAbsorptionB_split {CM Ks A cStar K g L : ℝ}
    (hMixed : 8*CM*(1+K)*g ≤ A*cStar^3*L)
    (hSquare : 8*CM*Ks*g^2 ≤ A*cStar^3*L) :
    4*CM*(1+K+Ks*g)*g ≤ A*cStar^3*L := by
  have he : 2*(4*CM*(1+K+Ks*g)*g) =
      8*CM*(1+K)*g + 8*CM*Ks*g^2 := by ring
  linarith only [hMixed, hSquare, he]

/-- Above a uniform threshold, it suffices to control only the mixed error term.
The remaining premise is displayed explicitly and is not asserted to follow from J5. -/
theorem rootChainAbsorptionB_mixed_reduction {CM Ks A : ℝ}
    (hCM : 0 < CM) (hKs : 0 < Ks) (hA : 0 < A) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu cStar K : ℝ,
      0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < K →
      ∀ L m : ℕ, m ≤ L →
      C*cStar ^ (-(3 : ℝ))*eLvsNuTerm nu cStar K ≤ (m : ℝ) →
      8*CM*(1+K)*Real.log (nu⁻¹*(L : ℝ)) ≤ A*cStar^3*(L : ℝ) →
      4*CM*(1+K+Ks*Real.log (nu⁻¹*(L : ℝ)))*Real.log (nu⁻¹*(L : ℝ)) ≤
        A*cStar^3*(L : ℝ) := by
  obtain ⟨C, hC, hs⟩ := rootChainAbsorptionB_log_square hCM hKs hA
  refine ⟨C, hC, ?_⟩
  intro nu cStar K hnu hnu1 hc hc2 hK L m hm hthr hMixed
  exact rootChainAbsorptionB_split hMixed
    (hs nu cStar K hnu hnu1 hc hc2 hK L m hm hthr)

end SuperdiffusionCLT.Section3.Setup
