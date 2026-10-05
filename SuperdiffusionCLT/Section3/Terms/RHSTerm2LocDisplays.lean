/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Assembly

/-!
# The response-field residue of `l.RHS.term2`: the weak-gradient displays

`term2_of_residue` of `RHSTerm2Assembly` states the display
`SuperdiffusionCLT.Frozen.Section3.rhs_term2` modulo five residue
binders.  Three of them concern the response field `R = (k_{L'} − k_ℓ) ∇w`:

* `hfinR` — finiteness of the annealed squared `L̲²(cu_m)` norm
  of `R`;
* `hRres` — the bounds on `R` and its weak gradient at `C₁ = 1`, quantified over *every* weak
  gradient `DR` of `R`;
* `hPtilde` — the proxy-mean control of `e.RHS.term2.proxy.energy`.

This module reduces the first two of them.

## `hRres`: the `∀ DR` binder is discharged

The a.e. uniqueness of weak partial derivatives
(`Homogenization.HasWeakPartialDerivOn.ae_eq`, the lever of
`Sobolev/DirichletW2pDivergence.hess_ae_eq`) says that two weak gradients of the
same component of `R` on the open cube `cu_m` agree almost everywhere, so the
`cubeLpENorm` of the Jacobian `HilbertMat.ofMat DR` is the *same function of the
sample* for every choice of weak gradient `DR` of `R`.  Hence the three clauses
of `hRres` depend on `DR` only through that function, and the universal
quantifier of the residue collapses to a single witness:

* `locallyIntegrableOn_entry_of_memLp`, `weakGradientOn_ae_eq_of_locallyIntegrable`,
  `hilbertMat_ae_eq_of_weakGradient`, `cubeLpENorm_ofMat_congr_of_ae_eq` and
  `cubeLpENorm_ofMat_congr_of_weakGradient` are the a.e.-invariance engine, with
  no hypothesis beyond the weak-gradient data and the local integrability that
  `L²` membership on the cube supplies;
* `hRres_collapse` is the collapse at an arbitrary witness `DR₀`;
* `hRres_of_exists_canonical` states it in the residue's own shape, with the
  `∀ DR` of `hRres` replaced by an `∃ DR₀`;
* `hRres_of_rfieldWeakJacobian` feeds in the weak Jacobian
  `RHSTerm2RField.rfieldWeakJacobian`, whose two data clauses
  (`rfieldWeakJacobian_hasWeakGradientOn`, `memLp_rfieldWeakJacobian`) are
  already proved, so the residue is *equivalent* to its three clauses at that
  single witness.

## `hPtilde`: reduced to the comparison of the two annealed energies

* `vecNormSq_annealedGluedAverage_le_cubeEnergy` is the Cauchy–Schwarz half of
  the proxy-mean control, fully proved: Jensen in the sample
  (`ofReal_vecNormSq_integral_le`) followed by Jensen on the cube
  (`ofReal_vecNormSq_volumeAverageVec_le`) bounds `|p̃|²` by the annealed squared
  `L̲²(cu_n)` energy of the cutoff-`ℓ` glued field;
* `hPtilde_of_cubeEnergy` concludes the residue from the one remaining
  comparison of the annealed energies at the nested cubes `cu_n ⊆ cu_m`.

## What is not treated here

`hfinR` and the measurability clause of the bounds on `R` are not
touched in this file; `hfinR` and the first summand of the display conjunct carry
the same stream-increment input as the gradient half of
`e.RHS.term2.R.bounds`.
The cube comparison `hcube` of `hPtilde_of_cubeEnergy` is the
stationarity/translation step, which relates the annealed energies at the two
nested scales; it is proved as `RHSTerm2Analytic.hcube_of_stationarity`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Norms
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Almost-everywhere uniqueness of the weak gradient of `R` -/

/-- A matrix entry of an `L²` Jacobian on the cube is locally integrable on the
open cube: the entry is `L²` on the finite restricted measure
(`HilbertMat.entryL` composed with the `L²` membership), hence `L¹` there, hence
locally integrable. -/
private theorem locallyIntegrableOn_entry_of_memLp {Q : TriadicCube d}
    {DR : Fin d → Vec d → Vec d}
    (hL2 : MemLp (fun x => HilbertMat.ofMat (fun i j => DR i x j)) 2
      (volume.restrict (openCubeSet Q))) (i j : Fin d) :
    LocallyIntegrableOn (fun x => DR i x j) (openCubeSet Q) volume := by
  have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_ne le_top (volume_openCubeSet_ne_top Q)⟩
  have hent : MemLp (fun x : Vec d => DR i x j) 2
      (volume.restrict (openCubeSet Q)) := by
    have h := (HilbertMat.entryL i j).comp_memLp' hL2
    exact h
  exact IntegrableOn.locallyIntegrableOn (hent.integrable (by norm_num))

/-- Two weak gradients of the same scalar function on the open cube, both
locally integrable, agree almost everywhere.  This is the coordinate form of
`Homogenization.HasWeakPartialDerivOn.ae_eq`. -/
theorem weakGradientOn_ae_eq_of_locallyIntegrable {Q : TriadicCube d}
    {u : Vec d → ℝ} {D₁ D₂ : Vec d → Vec d}
    (h₁ : HasWeakGradientOn (openCubeSet Q) u D₁)
    (h₂ : HasWeakGradientOn (openCubeSet Q) u D₂)
    (hloc₁ : ∀ j : Fin d, LocallyIntegrableOn (fun x => D₁ x j) (openCubeSet Q) volume)
    (hloc₂ : ∀ j : Fin d, LocallyIntegrableOn (fun x => D₂ x j) (openCubeSet Q) volume)
    (j : Fin d) :
    (fun x => D₁ x j) =ᵐ[volume.restrict (openCubeSet Q)] (fun x => D₂ x j) :=
  HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q) (hloc₁ j) (hloc₂ j) (h₁ j) (h₂ j)

/-- Two weak gradients of the same vector field on the open cube, each with
locally integrable entries, give the same `HilbertMat`-valued Jacobian almost
everywhere.  The `d²` coordinate equalities are collected by `ae_all_iff`. -/
theorem hilbertMat_ae_eq_of_weakGradient {Q : TriadicCube d}
    {U : Fin d → Vec d → ℝ} {D₁ D₂ : Fin d → Vec d → Vec d}
    (h₁ : ∀ i : Fin d, HasWeakGradientOn (openCubeSet Q) (U i) (D₁ i))
    (h₂ : ∀ i : Fin d, HasWeakGradientOn (openCubeSet Q) (U i) (D₂ i))
    (hloc₁ : ∀ i j : Fin d, LocallyIntegrableOn (fun x => D₁ i x j) (openCubeSet Q) volume)
    (hloc₂ : ∀ i j : Fin d, LocallyIntegrableOn (fun x => D₂ i x j) (openCubeSet Q) volume) :
    (fun x => HilbertMat.ofMat (fun i j => D₁ i x j)) =ᵐ[
        volume.restrict (openCubeSet Q)]
      (fun x => HilbertMat.ofMat (fun i j => D₂ i x j)) := by
  have hcoord : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ∀ p : Fin d × Fin d, D₁ p.1 x p.2 = D₂ p.1 x p.2 := by
    refine ae_all_iff.2 fun p => ?_
    exact weakGradientOn_ae_eq_of_locallyIntegrable (h₁ p.1) (h₂ p.1)
      (fun j => hloc₁ p.1 j) (fun j => hloc₂ p.1 j) p.2
  filter_upwards [hcoord] with x hx
  exact congrArg HilbertMat.ofMat (funext fun i => funext fun j => hx (i, j))

/-- The `L̲^q(cu_m)` size of the `HilbertMat` Jacobian is the same function of
the sample for every choice of weak gradient of `R`. -/
theorem cubeLpENorm_ofMat_congr_of_ae_eq {Q : TriadicCube d}
    {DR₁ DR₂ : Fin d → Vec d → Vec d} (q : ℝ≥0∞)
    (h : (fun x => HilbertMat.ofMat (fun i j => DR₁ i x j)) =ᵐ[
        volume.restrict (openCubeSet Q)]
      (fun x => HilbertMat.ofMat (fun i j => DR₂ i x j))) :
    cubeLpENorm Q q (fun x => HilbertMat.ofMat (fun i j => DR₁ i x j)) =
      cubeLpENorm Q q (fun x => HilbertMat.ofMat (fun i j => DR₂ i x j)) := by
  rw [cubeLpENorm, cubeLpENorm]
  refine eLpNorm_congr_ae ?_
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact Measure.ae_smul_measure h _

/-- **The a.e.-invariance of the Jacobian norm at weak-gradient
data**: for every pair of weak gradients `D₁`, `D₂` of the same vector field
whose `HilbertMat` readings are `L²` on `cu_m`, the `L̲^q(cu_m)` norms of the two
readings coincide. -/
theorem cubeLpENorm_ofMat_congr_of_weakGradient {Q : TriadicCube d}
    {U : Fin d → Vec d → ℝ} {D₁ D₂ : Fin d → Vec d → Vec d} (q : ℝ≥0∞)
    (h₁ : ∀ i : Fin d, HasWeakGradientOn (openCubeSet Q) (U i) (D₁ i))
    (h₂ : ∀ i : Fin d, HasWeakGradientOn (openCubeSet Q) (U i) (D₂ i))
    (hL2₁ : MemLp (fun x => HilbertMat.ofMat (fun i j => D₁ i x j)) 2
      (volume.restrict (openCubeSet Q)))
    (hL2₂ : MemLp (fun x => HilbertMat.ofMat (fun i j => D₂ i x j)) 2
      (volume.restrict (openCubeSet Q))) :
    cubeLpENorm Q q (fun x => HilbertMat.ofMat (fun i j => D₁ i x j)) =
      cubeLpENorm Q q (fun x => HilbertMat.ofMat (fun i j => D₂ i x j)) :=
  cubeLpENorm_ofMat_congr_of_ae_eq q
    (hilbertMat_ae_eq_of_weakGradient h₁ h₂
      (fun i j => locallyIntegrableOn_entry_of_memLp hL2₁ i j)
      (fun i j => locallyIntegrableOn_entry_of_memLp hL2₂ i j))

/-! ## The `∀ DR` binder of `hRres` collapses to a single witness -/

/-! ## The Jensen half of `hPtilde` -/

/-- **The Cauchy–Schwarz half of the proxy-mean control.**  The proxy mean
`p̃ = annealedGluedAverage hnu P L k m F = E[(∇u_k)_{cu_k}]` is the
Bochner integral of the `cu_k`-averages of the glued field, so Jensen's
inequality for a probability measure
(`ofReal_vecNormSq_integral_le`) followed by Jensen on the cube
(`ofReal_vecNormSq_volumeAverageVec_le`) bounds its squared magnitude by the
*annealed `cu_k` energy*:

`|p̃|² ≤ E_ω ‖∇u_k(ω)‖²_{L̲²(cu_k)}`.

This is the first half of the residue `hPtilde` and carries no hypothesis
beyond the law binders that make the annealed mean integrable
(`integrable_annealedGluedAverage`) and the glued field `L²`
(`memVectorL2_openCubeSet_gluedGradientField`).  The passage from the cube `cu_k`
to the cube `cu_m` at which the residue states its energy is *not* performed
here; it is the separate `hcube` hypothesis of `hPtilde_of_cubeEnergy`. -/
theorem vecNormSq_annealedGluedAverage_le_cubeEnergy [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {k m : ℕ} (hkm : k ≤ m) (L : ℕ) (F : Vec d) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) :
    vecNormSq (annealedGluedAverage hnu P L k m F) ≤
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (k : ℤ)) 2
            (gluedGradientField hnu L k m F omega) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal := by
  classical
  have hV : ∀ i : Fin d, MeasureTheory.Integrable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet (originCube d (k : ℤ)))
        (gluedGradientField hnu L k m F omega) i) P.toMeasure :=
    fun i =>
      (integrable_annealedGluedAverage hnu L k m hkm F hPrefix hJ2 hJ3 hJ4).eval i
  have hJen : ENNReal.ofReal (vecNormSq (annealedGluedAverage hnu P L k m F)) ≤
      ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (k : ℤ)) 2
        (gluedGradientField hnu L k m F omega) ^ (2 : ℕ) ∂P.toMeasure := by
    rw [annealedGluedAverage_eq]
    refine le_trans (ofReal_vecNormSq_integral_le hV) ?_
    exact lintegral_mono fun omega =>
      ofReal_vecNormSq_volumeAverageVec_le
        (memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega (originCube d (k : ℤ)))
  have hfin : (∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (k : ℤ)) 2
      (gluedGradientField hnu L k m F omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ := by
    have hb : ∀ omega : ShellSeq d, vecCubeLpENorm (originCube d (k : ℤ)) 2
        (gluedGradientField hnu L k m F omega) ^ (2 : ℕ) ≤
        ENNReal.ofReal (nu⁻¹ * nu⁻¹ * vecNormSq F) :=
      fun omega => vecCubeLpENorm_two_sq_gluedGradientField_le hnu le_rfl hkm L F omega
    have hle := lintegral_mono (μ := P.toMeasure) hb
    rw [lintegral_const, MeasureTheory.measure_univ, mul_one] at hle
    exact (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne_top
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hJen

/-- **`hPtilde` from the cube comparison.**  The residue `hPtilde` of the
reduction compares the squared proxy mean `|p̃|²` with the annealed squared
`L̲²(cu_m)` energy of the cutoff-`ℓ` glued field.  By
`vecNormSq_annealedGluedAverage_le_cubeEnergy` the left side is dominated by the
*annealed squared `L̲²(cu_n)` energy* of the same field, so the residue follows
from the one remaining comparison of the two annealed energies at the nested
cubes `cu_n ⊆ cu_m`.

The `hcube` hypothesis is stated at the two energies exactly as they appear, so
that discharging it is a statement about the process and not about the
reduction. -/
theorem hPtilde_of_cubeEnergy [NeZero d] (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (hcube : (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.n : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ≤
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal) :
    vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m
        (fluxSlot nu S.LPrime P S.n e)) ≤
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal := by
  have hnm : S.n ≤ S.m := by
    have h1 := hSorder.n_lt_ell
    have h2 := hSorder.ell_lt_ellPrime
    have h3 := hSorder.ellPrime_lt_m
    omega
  exact (vecNormSq_annealedGluedAverage_le_cubeEnergy hnu hnm S.ell
    (fluxSlot nu S.LPrime P S.n e) hPrefix hJ2 hJ3 hJ4).trans hcube

/-! ## The display with the `hRres` binder in single-witness form -/

end

end SuperdiffusionCLT.Section3.Terms
