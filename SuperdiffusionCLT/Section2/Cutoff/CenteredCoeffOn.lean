/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff

/-!
# The centered marginal cutoff as a Chapter 2 coefficient object

The level-`L` centered representative of the infrared cutoff,
`ν Id + k_L - (k_L)_U` — the operator of the manuscript's `u_L`-equation in the
proof of `l.cutoff.approximation` — is given by `centeredCoefficientCutoff`.
The manuscript's `a^U` itself is the *infinite* recentered
series `ν Id + ∑ (j_k - (j_k)_U)`, of which the bundled field is the level-`L`
truncation; the ellipticity of `a^U` additionally needs the `L^∞`-convergence
bridge of `Carriers.CenteredStreamField`, which is not supplied here.

The Chapter 2 theorems are stated for a `Book.Ch02.CoeffOn U`, which bundles
quantitative ellipticity constants, a.e. strong measurability and a.e.
ellipticity; supplying those constants is the step carried out here.

The lower constant is again the molecular diffusivity `ν`: the constant
anti-symmetric average `(k_L)_U` that the recentering subtracts leaves the
symmetric part `ν Id` untouched (`symmPart_centeredCoefficientCutoff`). The
upper constant is the `L^∞` bound of the centered field on `U` converted to the
inverse-side bound of `IsEllipticMatrix` (a quantitative two-sided strengthening
of the paper's qualitative notion), exactly as in
`coefficientCutoffCoeffOn` for the un-centered field.

No hypothesis is needed: the bundled field is a finite sum of shells
(`streamCutoff omega L x i j = ∑_{n ≤ L} omega n x i j`), every shell entry is
continuous because the `ShellField` carrier stores a `ContinuousMap`, so every
entry of the finite sum is bounded on the bounded domain `U` for *every* shell
sequence. The explicit constants are `streamCutoffEntryBound` (per entry of
`k_L`) and `centeredEntryBound` (`ν + 2 * ∑ p, |streamCutoffEntryBound … p.1 p.2|`,
via `abs_centeredCoefficientCutoff_entry_le`). The remark in the proof of
`l.cutoff.approximation` derives the almost-sure *summability* of the shell derivative suprema
(with the `3^{-L}` tail) that is what upgrades the truncation to the infinite `a^U`; in
the manuscript, the `L^∞` entry bound itself comes from the printed proof's
Lipschitz and averaging steps.

## Main results

* `abs_volumeAverageMat_streamCutoff_entry_le`: the entrywise volume average
  `(k_L)_U` inherits the uniform entry bound of `k_L` on `U`.
* `abs_centeredCoefficientCutoff_entry_le`: the entry bound of `k_L` on a
  bounded domain gives an entry bound `ν + 2 C` for the centered field.
* `shellReg_entry_continuous`, `shellReg_entry_bounded`: every entry of every
  shell is continuous, hence bounded on a bounded set.
* `abs_streamCutoffEntryBound`, `abs_centeredEntryBound`: the explicit entry
  bounds `streamCutoffEntryBound` and `centeredEntryBound` hold for every shell
  sequence, with no hypothesis.
* `centeredCoefficientCutoffCoeffOn`: the Chapter 2 coefficient object of
  `ν Id + (k_L - (k_L)_U)`, with `lam = ν` and
  `Lam = (d^2 * (centeredEntryBound …)^2 + ν^2)/ν`, hypothesis-free.
* `centeredCoefficientCutoffCoeffOn_toCoeffField`: the raw coefficient field of the
  bundle is the centered field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.CoarseGraining
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The entrywise average bound -/

/-- The entrywise volume average of the cutoff stream matrix inherits the
uniform entry bound of the stream matrix: on a bounded measurable set of
positive volume, each entry of `(k_L)_U` is bounded by the same constant as the
entries of `k_L` on `U`. -/
theorem abs_volumeAverageMat_streamCutoff_entry_le {omega : ShellSeq d} {L : ℕ}
    {U : Set (Vec d)} {C : ℝ}
    (hUb : Bornology.IsBounded U) (hUmeas : MeasurableSet U)
    (hvol : 0 < (volume U).toReal)
    (hstream : ∀ x ∈ U, ∀ i j : Fin d, |streamCutoff omega L x i j| ≤ C)
    (i j : Fin d) : |volumeAverageMat U (streamCutoff omega L) i j| ≤ C := by
  have hfin : volume U ≠ ⊤ := volume_ne_top_of_isBounded hUb
  have hint : IntegrableOn (fun x ↦ streamCutoff omega L x i j) U volume :=
    integrableOn_entry_of_isBounded (streamCutoff omega L) hUb i j
  have hintabs : IntegrableOn (fun x ↦ |streamCutoff omega L x i j|) U volume :=
    hint.abs
  have hintneg : IntegrableOn (fun x ↦ (-(C : ℝ))) U volume :=
    integrableOn_const (C := (-(C : ℝ))) hfin
  have hintC : IntegrableOn (fun x ↦ (C : ℝ)) U volume :=
    integrableOn_const (C := C) hfin
  have hconst : ∫ x in U, (C : ℝ) ∂volume = (volume U).toReal * C := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, smul_eq_mul]
  have hconstneg : ∫ x in U, (-(C : ℝ)) ∂volume = -((volume U).toReal * C) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real, smul_eq_mul,
      mul_neg]
  have hun : NullMeasurableSet U volume := hUmeas.nullMeasurableSet
  have habs : |∫ x in U, streamCutoff omega L x i j ∂volume| ≤
      (volume U).toReal * C := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have hlow : ∫ x in U, (-(C : ℝ)) ∂volume ≤
          ∫ x in U, streamCutoff omega L x i j ∂volume :=
        MeasureTheory.setIntegral_mono_on₀ hintneg hint hun
          fun x hx => (abs_le.mp (hstream x hx i j)).1
      rwa [hconstneg] at hlow
    · have hhigh : ∫ x in U, streamCutoff omega L x i j ∂volume ≤
          ∫ x in U, (C : ℝ) ∂volume :=
        le_trans
          (MeasureTheory.setIntegral_mono_on₀ hint hintabs hun
            fun x hx => le_abs_self _)
          (MeasureTheory.setIntegral_mono_on₀ hintabs hintC hun
            fun x hx => hstream x hx i j)
      rwa [hconst] at hhigh
  have hval : volumeAverageMat U (streamCutoff omega L) i j =
      (volume U).toReal⁻¹ * ∫ x in U, streamCutoff omega L x i j ∂volume := by
    simp only [volumeAverageMat, volumeAverage]
  rw [hval, abs_mul, abs_of_pos (inv_pos.mpr hvol)]
  calc (volume U).toReal⁻¹ * |∫ x in U, streamCutoff omega L x i j ∂volume| ≤
      (volume U).toReal⁻¹ * ((volume U).toReal * C) :=
        mul_le_mul_of_nonneg_left habs (inv_nonneg.2 hvol.le)
    _ = C := by field_simp

/-- On a Chapter 2 domain, the entrywise volume average of the cutoff stream
matrix inherits the uniform entry bound of the stream matrix on `U`. -/
theorem abs_volumeAverageMat_streamCutoff_entry_le_domain (U : Book.Ch02.Domain d)
    {omega : ShellSeq d} {L : ℕ} {C : ℝ}
    (hstream : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |streamCutoff omega L x i j| ≤ C)
    (i j : Fin d) :
    |volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L) i j| ≤ C := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hvol : 0 < MeasureTheory.volume (U : Set (Vec d)) :=
    IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty
  refine abs_volumeAverageMat_streamCutoff_entry_le hUb U.measurableSet ?_ hstream i j
  exact ENNReal.toReal_pos (ne_of_gt hvol) (volume_ne_top_of_isBounded hUb)

/-- The entry bound of the cutoff stream matrix `k_L` on a Chapter 2 domain is
an entry bound for the centered field `a^U = ν Id + (k_L - (k_L)_U)`, with the
constant enlarged from `C` to `ν + 2 C`: one `C` for the entries of
`ν Id + k_L`, one for the entrywise average. -/
theorem abs_centeredCoefficientCutoff_entry_le (U : Book.Ch02.Domain d)
    {nu : ℝ} {omega : ShellSeq d} {C : ℝ} (L : ℕ) (hnu : 0 < nu)
    (hstream : ∀ x ∈ (U : Set (Vec d)), ∀ i j : Fin d,
      |streamCutoff omega L x i j| ≤ C)
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) (i j : Fin d) :
    |(centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField x i j| ≤
      nu + 2 * C := by
  have havg := abs_volumeAverageMat_streamCutoff_entry_le_domain U hstream i j
  have haL : |(coefficientCutoff nu omega L).toCoeffField x i j| ≤ nu + C :=
    abs_coefficientCutoff_entry_le (le_of_lt hnu) omega L x (hstream x hx) i j
  have hstep :
      |(centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField x i j| ≤
        |(coefficientCutoff nu omega L).toCoeffField x i j| +
          |volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L) i j| := by
    show |(centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toFun x i j| ≤
      |(coefficientCutoff nu omega L).toFun x i j| +
        |volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L) i j|
    rw [centeredCoefficientCutoff_eq_coefficientCutoff_sub nu omega L
      (U : Set (Vec d)) x]
    exact abs_sub _ _
  calc
    |(centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField x i j| ≤
        |(coefficientCutoff nu omega L).toCoeffField x i j| +
          |volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L) i j| := hstep
    _ ≤ nu + 2 * C := by linarith only [haL, havg]

/-! ## The unconditional entry bounds of the finite centered field -/

/-- Each entry of each shell is continuous: the `ShellField` carrier stores a
`ContinuousMap`. -/
theorem shellReg_entry_continuous (omega : ShellSeq d) (n : ℕ) (i j : Fin d) :
    Continuous (fun x : Vec d => shellReg omega n x i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp (omega n).1.1.continuous)

/-- Each entry of each shell is bounded on a bounded set. -/
theorem shellReg_entry_bounded {U : Set (Vec d)} (hUb : Bornology.IsBounded U)
    (omega : ShellSeq d) (n : ℕ) (i j : Fin d) :
    ∃ M : ℝ, ∀ x ∈ U, |shellReg omega n x i j| ≤ M := by
  obtain ⟨M, hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn
    (shellReg_entry_continuous omega n i j).continuousOn
  refine ⟨M, fun x hx => ?_⟩
  have h := hM x (subset_closure hx)
  rwa [Real.norm_eq_abs] at h

/-- An explicit uniform entry bound for the finite cutoff stream matrix on a
bounded set, indexed by the entry pair: the sum over the shells `n ≤ L` of the
chosen per-shell entry bounds. -/
noncomputable def streamCutoffEntryBound {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (omega : ShellSeq d) (L : ℕ) :
    Fin d × Fin d → ℝ :=
  fun p => ∑ n ∈ Finset.range (L + 1),
    Classical.choose (shellReg_entry_bounded hUb omega n p.1 p.2)

/-- The explicit entry bound `streamCutoffEntryBound` works: the finite cutoff
stream matrix is bounded on a bounded set with no hypothesis beyond
boundedness. -/
theorem abs_streamCutoffEntryBound {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (omega : ShellSeq d) (L : ℕ)
    (p : Fin d × Fin d) (x : Vec d) (hx : x ∈ U) :
    |streamCutoff omega L x p.1 p.2| ≤ streamCutoffEntryBound hUb omega L p := by
  calc |streamCutoff omega L x p.1 p.2|
      = |∑ n ∈ Finset.range (L + 1), omega n x p.1 p.2| := by
        rw [streamCutoff_apply_entry]
    _ ≤ ∑ n ∈ Finset.range (L + 1), |omega n x p.1 p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ streamCutoffEntryBound hUb omega L p := by
        show ∑ n ∈ Finset.range (L + 1), |omega n x p.1 p.2| ≤
          ∑ n ∈ Finset.range (L + 1),
            Classical.choose (shellReg_entry_bounded hUb omega n p.1 p.2)
        exact Finset.sum_le_sum fun n _ =>
          Classical.choose_spec (shellReg_entry_bounded hUb omega n p.1 p.2) x hx

/-- An explicit uniform entry bound for the level-`L` centered field on a
Chapter 2 domain: `ν + 2 * ∑ p, |streamCutoffEntryBound … p|`, obtained from
`abs_centeredCoefficientCutoff_entry_le` with the unconditional bound
`abs_streamCutoffEntryBound` of the finite stream matrix. The definition itself
is hypothesis-free; the bound theorem `abs_centeredEntryBound` needs
`hnu : 0 < nu`, which is genuinely required (at the diagonal the centered entry
is exactly `ν`). -/
noncomputable def centeredEntryBound (U : Book.Ch02.Domain d) (nu : ℝ)
    (omega : ShellSeq d) (L : ℕ) : ℝ :=
  nu + 2 * ∑ p : Fin d × Fin d,
    |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p|

/-- The explicit entry bound `centeredEntryBound` holds for every shell
sequence, with no hypothesis. -/
theorem abs_centeredEntryBound (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (x : Vec d) (hx : x ∈ (U : Set (Vec d)))
    (i j : Fin d) :
    |(centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField x i j| ≤
      centeredEntryBound U nu omega L := by
  have hC : ∀ y ∈ (U : Set (Vec d)), ∀ p q : Fin d,
      |streamCutoff omega L y p q| ≤ ∑ p : Fin d × Fin d,
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| := by
    intro y hy p q
    calc |streamCutoff omega L y p q| ≤
        |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L (p, q)| :=
          (abs_streamCutoffEntryBound _ omega L (p, q) y hy).trans (le_abs_self _)
      _ ≤ ∑ p : Fin d × Fin d,
          |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded omega L p| :=
          Finset.single_le_sum
            (f := fun p => |streamCutoffEntryBound U.isDomain.isBoundedDomain.isBounded
              omega L p|)
            (fun p _ => abs_nonneg _) (Finset.mem_univ _)
  unfold centeredEntryBound
  exact abs_centeredCoefficientCutoff_entry_le U L hnu hC x hx i j

/-! ## The Chapter 2 coefficient object of the centered field -/

/-- The Chapter 2 coefficient object of the level-`L` centered representative
`ν Id + (k_L - (k_L)_U)` of the infrared cutoff — the operator of the
manuscript's printed `u_L`-equation — on a domain `U`, with no hypothesis: the
bundled field is a finite sum of `C^2` shells, so the entry bound
`centeredEntryBound U nu omega L` holds on the bounded domain `U` for every
shell sequence (`abs_centeredEntryBound`).

The lower ellipticity constant is the molecular diffusivity `ν`, which the
recentering does not touch because the subtracted average is anti-symmetric;
the upper one is the explicit entry bound `centeredEntryBound U nu omega L` of
the centered field on `U` converted to the inverse-side bound of
`IsEllipticMatrix`.

This is not the manuscript's `a^U`: the printed `k^U` is the
infinite recentered series `∑ (j_k - (j_k)_U)`, of which the bundled field is
the level-`L` truncation; the ellipticity of `a^U` itself additionally needs
the `L^∞`-convergence bridge of `Carriers.CenteredStreamField`. -/
noncomputable def centeredCoefficientCutoffCoeffOn (U : Book.Ch02.Domain d)
    {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) :
    Book.Ch02.CoeffOn U where
  toCoeffField := (centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField
  lam := nu
  Lam := ((d : ℝ) * (d : ℝ) * (centeredEntryBound U nu omega L) ^ 2 + nu ^ 2) / nu
  lam_pos := hnu
  lam_le_Lam := by
    rw [le_div_iff₀ hnu, ← pow_two]
    linarith only [show (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) *
      (centeredEntryBound U nu omega L) ^ 2 by positivity]
  aeStronglyMeasurable := by
    classical
    intro i j
    have hEq : (fun x : Vec d =>
        restrictCoeffField (U : Set (Vec d))
          (centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField
            x i j) =
        fun x : Vec d => if x ∈ (U : Set (Vec d))
          then (centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField
            x i j else 0 := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hx]
    rw [hEq]
    exact (((centeredCoefficientCutoff nu omega L
      (U : Set (Vec d))).entry_measurable i j).ite
      U.measurableSet measurable_const).aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    exact isEllipticMatrix_of_symmPart_eq_smul_one hnu
      (symmPart_centeredCoefficientCutoff nu omega L (U : Set (Vec d)) x)
      (abs_centeredEntryBound U nu hnu omega L x hx)

@[simp] theorem centeredCoefficientCutoffCoeffOn_toCoeffField
    (U : Book.Ch02.Domain d) {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    (L : ℕ) :
    (centeredCoefficientCutoffCoeffOn U hnu omega L).toCoeffField =
      (centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField :=
  rfl

end

end SuperdiffusionCLT.Section2.Cutoff
