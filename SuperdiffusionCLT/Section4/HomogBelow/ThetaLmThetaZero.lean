/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Pigeonhole
public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff

/-!
**`Θ_{L,0} ≤ C(d) ν^{-2} L`**
(the display `e.Enaught.mixing` of the paper),
the fact feeding the `m₀` startup-scale threshold in the proof of `p.homog.below`.

The content of `e.Enaught.mixing` is available as `envelopeUpperScalar`
`/` `envelopeLowerScalar` (`Section2/Annealed/Envelope.lean`), and the
scale-independent bound
`sigmaBarSeq nu L P n * sigmaBarStarInvSeq nu L P n ≤
  envelopeScalarProduct d nu L`
is `sigmaBarSeq_mul_le_envelopeScalarProduct`
(`Section3/Setup/Pigeonhole.lean`) for *every* `n`, in particular `n = 0`;
since `thetaCutoff nu L P n` is definitionally that same product
(`Frozen/Section4/ThetaCutoff.lean`), this gives `Θ_{L,0} ≤
envelopeScalarProduct d nu L` immediately. What remains — bounding
`envelopeScalarProduct d nu L` itself by `C(d) ν⁻² L` — is done here
from the public definitions (`envelopeUpperScalar`, `envelopeLowerScalar`,
`cutoffEnvelopeConst`) directly, since the existing occurrence of this exact
computation is a private `have` inside the differently-shaped
`ellipBelow_crude_comparison` (`Section4/Ellipticity/
EllipticityBelowCutoff.lean`), not a directly reusable lemma. The constant
obtained, `2 C(d) + 4 C(d)²` with `C(d) := cutoffEnvelopeConst d`, matches
`ellipBelow_crudeConst d` there exactly. -/

@[expose] public section

/-- **`Θ_{L,0} ≤ (2C(d) + 4C(d)²) ν⁻² L`**, `C(d) := cutoffEnvelopeConst d`. -/
theorem SuperdiffusionCLT.Section4.HomogBelow.homogBelow_thetaCutoff_zero_le
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (L : ℕ) (hL1 : 1 ≤ L) :
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 ≤
      (2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
          4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2) *
        nu⁻¹ ^ 2 * (L : ℝ) := by
  have hstep1 :
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 ≤
        SuperdiffusionCLT.Section3.Setup.envelopeScalarProduct d nu L :=
    SuperdiffusionCLT.Section3.Setup.sigmaBarSeq_mul_le_envelopeScalarProduct
      hnu L hPrefix hJ2 hJ3 hJ4 0
  set Cd := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d with hCddef
  have hCdpos : 0 < Cd := by
    rw [hCddef]; exact SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst_pos d
  have hLge1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hmaxL : max (1 : ℝ) (L : ℝ) = (L : ℝ) := max_eq_right hLge1
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
  have hnuinv2ge1 : (1 : ℝ) ≤ nu⁻¹ ^ 2 := by
    calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ nu⁻¹ ^ 2 := pow_le_pow_left₀ (by norm_num) hnuinv1 2
  have hLnuinv2ge1 : (1 : ℝ) ≤ nu⁻¹ ^ 2 * (L : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ nu⁻¹ ^ 2 * (L : ℝ) :=
        mul_le_mul hnuinv2ge1 hLge1 (by norm_num) (by linarith only [hnuinv2ge1])
  have hexpand :
      SuperdiffusionCLT.Section3.Setup.envelopeScalarProduct d nu L =
        2 * Cd + 4 * Cd ^ 2 * nu⁻¹ ^ 2 * (L : ℝ) := by
    show SuperdiffusionCLT.Section2.Annealed.envelopeUpperScalar d nu L *
        SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar d nu =
        2 * Cd + 4 * Cd ^ 2 * nu⁻¹ ^ 2 * (L : ℝ)
    unfold SuperdiffusionCLT.Section2.Annealed.envelopeUpperScalar
      SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar
    rw [hmaxL]
    have hnu_ne : nu ≠ 0 := hnu.ne'
    field_simp
    ring
  have hfinal : 2 * Cd + 4 * Cd ^ 2 * nu⁻¹ ^ 2 * (L : ℝ) ≤
      (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) := by
    have hrhs_eq : (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) =
        2 * Cd * (nu⁻¹ ^ 2 * (L : ℝ)) + 4 * Cd ^ 2 * nu⁻¹ ^ 2 * (L : ℝ) := by ring
    rw [hrhs_eq]
    have h2C : 2 * Cd ≤ 2 * Cd * (nu⁻¹ ^ 2 * (L : ℝ)) := by
      calc 2 * Cd = 2 * Cd * 1 := (mul_one _).symm
        _ ≤ 2 * Cd * (nu⁻¹ ^ 2 * (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hLnuinv2ge1 (by linarith only [hCdpos])
    linarith only [h2C]
  rw [hexpand] at hstep1
  linarith only [hstep1, hfinal]
