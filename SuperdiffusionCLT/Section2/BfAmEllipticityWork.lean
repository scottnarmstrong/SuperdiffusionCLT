/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.EnvelopeMinimalScale
public import SuperdiffusionCLT.Section2.Annealed.MuDomainMeasurability

/-!
# The ellipticity bounds of `bfA_m`: assembly of the ellipticity conclusion

## The printed statement

lemma `l.bfAm.ellip`, quoted verbatim:

> **Lemma (Ellipticity bounds for `bfA_m`).** For every `m ∈ N` and every bounded
> Lipschitz domain `U`,
> `|bfE_m^{-1/2} bfA_m(U) bfE_m^{-1/2}| ≤ O_{Γ₁}(1)`.
> Moreover, for every `n ∈ N`,
> `bfE_m^{-1/2} bfAhom_m bfE_m^{-1/2} ≤ bfE_m^{-1/2} bfAhom_m(cu_n) bfE_m^{-1/2}
> ≤ I_{2d}`.
> Moreover, for each `m ∈ N` and `γ ∈ (0,1)`, there exists a random minimal scale
> `S_{m,γ}` satisfying
> `S_{m,γ} = O_{Γ_γ}(C exp(C |log γ| / γ) 3^m)`
> such that, for every `n ∈ N`,
> `3^n ≥ S_{m,γ} ⟹ 3^{-γ(n-l)} bfE_m^{-1/2} bfA_m(z + cu_l) bfE_m^{-1/2} ≤ 2 I_{2d}`,
> `∀ l ∈ Z ∩ (-∞,n], z ∈ 3^l Z^d ∩ cu_n`.

The formal statement is the `∃ C` conclusion of `bfAmEllipticity_of_inputs`, whose third
clause is
quantified almost surely in the sample. Here it is reduced to one named
hypothesis, `hScale`.

## What is supplied here

* `eventually_blockMatLoewnerLE_of_eventually_weighted_ratio_le`: the
  almost-sure scalar-to-Loewner passage of the third assertion. The printed
  union bound (`EnvelopeMinimalScale.lean`,
  `measureReal_exists_subCube_gt_le_of_scaleTail`) produces the scalar bound
  `3^{-γ(n-l)} envelopeRatio ≤ 2` off an event; this lemma turns that eventwise
  scalar statement into the eventwise matrix statement
  `3^{-γ(n-l)} bfE_m^{-1/2} bfA_m(z + cu_l) bfE_m^{-1/2} ≤ 2 I_{2d}` through the
  deterministic Loewner bound `blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix`
  and the scaling `blockMatLoewnerLE_two_smul_blockIdentity_of_mul_le`.
* `bfAmEllipticity_of_inputs`: the conclusion verbatim as the goal,
  with two ingredients taken as named hypotheses `hMu` and `hScale`.
  The first two assertions are *discharged* here:
  the second is
  `blockMatLoewnerLE_envelopeRescale_annealed_sandwich`, and the first is
  `isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale`
  together with the measurability half taken from `hMu`.
* `exists_openCubeSet_originCube_of_isBounded`,
  `exists_aeeQuantitativeEllipticSlice_of_isBounded`,
  `measurable_Mu_domain_coefficientCutoff`: **the hypothesis
  `hMu` is discharged.** A bounded set lies in one centred triadic cube, so a
  locally a.e.-uniformly elliptic field lies in a quantitative `AEE` slice on
  every bounded measurable set; the countable family of slice events therefore
  covers the sample space, and the fixed-slice-level carrier engine of
  `BfAmEllipticityInputs` (`measurable_Mu_of_aeeSlice_measurable_entryTest`,
  `measurable_Mu_of_isOpenBoundedConvexDomain_of_measurable_source`) gives the
  measurability of `Mu` on a bounded convex domain by `Set.liftCover`. The
  measurability half of the first assertion is then unconditional on
  `Homogenization.Book.Ch02.Domain`.
* `bfAmEllipticity_of_minimalScale`: the conclusion verbatim as the
  goal, with `hScale` as its only hypothesis.

## What `Section2/BfAmEllipticityInputs.lean` supplies

That module (with its consumer
`Section2/Annealed/MuDomainMeasurability.lean`) proves the carrier
`Mu`-measurability engine on an arbitrary open set of positive finite volume
(`measurable_Mu_of_aeeSlice_measurable_entryTest`), the `LocalSigmaR U`
measurability of the quantitative-slice event on every open `U`
(`measurableSet_localSigmaR_aeeQuantitativeEllipticSlice_of_isOpen`), the
variational identity identifying `Homogenization.Mu` with the canonical AEE
Hilbert-operator candidate, and the resulting engine on a bounded open convex
domain from a measurable source with the localized entry-test premise removed
(`measurable_Mu_of_isOpenBoundedConvexDomain_of_measurable_source`). Its engine
is indexed by a *fixed* slice level `k`; the countable-slice cover that the
printed observable needs on a general domain is not assembled there. That cover
is assembled here, in `measurable_Mu_domain_coefficientCutoff`, so the
hypothesis `hMu` of `bfAmEllipticity_of_inputs` is available unconditionally
for the cutoff field.

## What remains as a hypothesis

* `hScale`, the random minimal scale
  `e.Smgamma.integ`. Its decay in the level `n` needs the
  printed improvement of the square bound `e.km.square.bound` on cubes larger than the
  cutoff scale, which is not available here: the union bound
  `measureReal_exists_subCube_gt_le_of_scaleTail` is uniform in `n`, so the events
  `{some sub-cube of cu_n fails}` are not summable in `n` and no
  Borel--Cantelli step produces the almost-sure finiteness of the failing
  levels. Everything else in the third assertion is supplied here by
  `eventually_blockMatLoewnerLE_of_eventually_weighted_ratio_le` together with
  the deterministic Loewner bound
  `blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix`.

DIMENSION ONE IS OUT OF SCOPE. The statement itself carries no `NeZero d`
binder: `NeZero d` is derived inside from `ShellLawPrefix.dimension`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2

noncomputable section

variable {d : ℕ}

/-! ## The almost-sure scalar-to-Loewner passage of the third assertion -/

/-- **The third assertion of `l.bfAm.ellip` in its almost-sure
form, from the scalar minimal-scale bound on the random factor
`envelopeRatio`.** The hypothesis is the conclusion of the printed union bound
over all scales `l ≤ n` and all sub-cubes `z + cu_l` of `cu_n`, read almost surely in the sample;
the passage from the scalar bound
to the block Loewner order is supplied here from the deterministic bound
`blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix`. -/
theorem eventually_blockMatLoewnerLE_of_eventually_weighted_ratio_le [NeZero d]
    {nu gamma : ℝ} (hnu : 0 < nu) {m : ℕ} {S : ShellSeq d → ℝ}
    {P : ProbabilityMeasure (ShellSeq d)}
    (h : ∀ᵐ omega ∂P.toMeasure, ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
      ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
          (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) *
            envelopeRatio m Q omega ≤ 2) :
    ∀ᵐ omega ∂P.toMeasure, ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
      ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
        cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
          BlockMatLoewnerLE
            (((3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ))))) •
              envelopeRescale d nu m
                (coarseBlockMatrix (cubeSet Q)
                  (coefficientCutoff nu omega m).toCoeffField))
            ((2 : ℝ) • Book.Ch02.blockIdentity d) := by
  filter_upwards [h] with omega hratio n hn Q hQ hmem
  exact blockMatLoewnerLE_two_smul_blockIdentity_of_mul_le
    (Real.rpow_pos_of_pos (by norm_num) _).le
    (blockMatLoewnerLE_envelopeRescale_coarseBlockMatrix hnu omega m Q)
    (hratio n hn Q hQ hmem)

/-! ## The measurability of `Mu` on a bounded domain, discharged -/

/-- **Every bounded set of `R^d` lies in an open half-scale triadic cube.** A
bounded set lies in some closed ball, and the centred triadic cubes
`openCubeSet (originCube d N) = (-3^N/2, 3^N/2)^d` exhaust the ambient space. -/
theorem exists_openCubeSet_originCube_of_isBounded {U : Set (Vec d)}
    (hbdd : Bornology.IsBounded U) :
    ∃ N : ℤ, U ⊆ openCubeSet (originCube d N) := by
  obtain ⟨r, hr⟩ := hbdd.subset_closedBall (0 : Vec d)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max 1 (2 * r)) (by norm_num : (1 : ℝ) < 3)
  refine ⟨(n : ℤ), fun x hx => ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxr : ‖x‖ ≤ r := by
    simpa using (Metric.mem_closedBall.mp (hr hx))
  have hxi : |x i| ≤ r := by
    have h2 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at h2
    linarith only [h2, hxr]
  have h2r : 2 * r < (3 : ℝ) ^ n :=
    (le_max_right (1 : ℝ) (2 * r)).trans_lt hn
  have hrlt : r < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by linarith only [h2r]
  rw [zpow_natCast]
  constructor
  · have h1 := neg_abs_le (x i)
    linarith only [h1, hxi, hrlt]
  · have h1 := le_abs_self (x i)
    linarith only [h1, hxi, hrlt]

/-- **A locally a.e.-uniformly elliptic field lies in a quantitative `AEE`
slice on every bounded measurable set.** `AELocallyUniformlyEllipticField` is
indexed by triadic cubes; a bounded set lies in one, and the quantitative slice
`AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn` relaxes the constants
obtained there. -/
theorem exists_aeeQuantitativeEllipticSlice_of_isBounded {U : Set (Vec d)}
    (hU : MeasurableSet U) (hbdd : Bornology.IsBounded U) {a : RegCoeffField d}
    (h : Book.Ch04.AELocallyUniformlyEllipticField a) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a.toFun := by
  obtain ⟨N, hN⟩ := exists_openCubeSet_originCube_of_isBounded hbdd
  obtain ⟨lam, _Lam, hlam, _hle, hEll⟩ := h (originCube d N)
  exact AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam
    ((hEll.cubeSet_of_openCubeSet).mono hU (hN.trans (openCubeSet_subset_cubeSet _)))

/-- **The measurability of `Mu` on a bounded domain of
`Homogenization.Book.Ch02.Domain`, for the cutoff field.** This discharges the
hypothesis `hMu` of `bfAmEllipticity_of_inputs`: the countable
family of quantitative-slice events covers the whole sample space
(`exists_aeeQuantitativeEllipticSlice_of_isBounded`), each is measurable
(`measurableSet_localSigmaR_aeeQuantitativeEllipticSlice_of_isOpen`), and on
each slice the fixed-`k` carrier engine of `BfAmEllipticityInputs` applies. -/
theorem measurable_Mu_domain_coefficientCutoff {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    (U : Book.Ch02.Domain d) (P0 : BlockVec d) :
    Measurable fun omega : ShellSeq d =>
      Mu (U : Set (Vec d)) P0 (coefficientCutoff nu omega m).toCoeffField := by
  classical
  set S : ℕ → Set (ShellSeq d) := fun k =>
    {omega | AEEQuantitativeEllipticSlice (U : Set (Vec d)) k
      (coefficientCutoff nu omega m).toFun} with hSdef
  have hSmeas : ∀ k, MeasurableSet (S k) := by
    intro k
    exact measurable_coefficientCutoff (d := d) nu m
      (LocalSigmaR_le (U : Set (Vec d)) _
        (measurableSet_localSigmaR_aeeQuantitativeEllipticSlice_of_isOpen U.isOpen k))
  have hSunion : ⋃ k, S k = Set.univ := by
    ext omega
    refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
    obtain ⟨k, hk⟩ := exists_aeeQuantitativeEllipticSlice_of_isBounded
      U.isOpen.measurableSet U.isDomain.isBoundedDomain.isBounded
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m)
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  set F : (k : ℕ) → S k → ℝ := fun k x =>
    Mu (U : Set (Vec d)) P0 (coefficientCutoff nu (x : ShellSeq d) m).toCoeffField
    with hFdef
  have hFagree : ∀ (i j : ℕ) (x : ShellSeq d) (hxi : x ∈ S i) (hxj : x ∈ S j),
      F i ⟨x, hxi⟩ = F j ⟨x, hxj⟩ := fun _ _ _ _ _ => rfl
  have hFmeas : ∀ k, Measurable (F k) := by
    intro k
    exact measurable_Mu_of_isOpenBoundedConvexDomain_of_measurable_source
      (U := (U : Set (Vec d))) (k := k) U.isDomain U.nonempty
      ((measurable_coefficientCutoff (d := d) nu m).comp measurable_subtype_coe)
      (fun x => x.2) P0
  have hEq : (fun omega : ShellSeq d =>
        Mu (U : Set (Vec d)) P0 (coefficientCutoff nu omega m).toCoeffField) =
      Set.liftCover S F hFagree hSunion := by
    funext omega
    have hmem : omega ∈ ⋃ k, S k := by rw [hSunion]; exact Set.mem_univ _
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    rw [Set.liftCover_coe (S := S) (f := F) (x := (⟨omega, hk⟩ : S k))]
  rw [hEq]
  exact measurable_liftCover S hSmeas F hFmeas hFagree hSunion

/-! ## The conclusion, with two ingredients as hypotheses -/

/-- **`l.bfAm.ellip`, in the shape of the printed
statement**, from two ingredients taken as hypotheses:

* `hMu`: the measurability of `Homogenization.Mu` on a bounded domain of
  `Homogenization.Book.Ch02.Domain`, which `CoarseGraining` supplies only on
  triadic cubes;
* `hScale`: the random minimal scale of `e.Smgamma.integ` for the scalar
  random factor `envelopeRatio`, with the sub-cube clause quantified almost
  surely in the sample.

The witness exhibited
for its `∃ C` is `Cscale`, so the constant is exactly the one carried by
`hScale`. The second assertion and the determinism of the first are discharged
by results proved elsewhere, and the third assertion is the almost-sure passage
`eventually_blockMatLoewnerLE_of_eventually_weighted_ratio_le`. -/
theorem bfAmEllipticity_of_inputs (d : ℕ) (Cscale : ℝ)
    (hMu : ∀ nu : ℝ, 0 < nu → ∀ (m : ℕ) (U : Book.Ch02.Domain d) (P0 : BlockVec d),
      Measurable fun omega : ShellSeq d =>
        Mu (U : Set (Vec d)) P0 (coefficientCutoff nu omega m).toCoeffField)
    (hScale : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ (m : ℕ) (gamma : ℝ), 0 < gamma → gamma < 1 →
          ∃ S : ShellSeq d → ℝ,
            Measurable S ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma gamma) S
                (Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
                  (3 : ℝ) ^ m) ∧
              ∀ᵐ omega ∂P.toMeasure, ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
                  cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
                    (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) *
                      envelopeRatio m Q omega ≤ 2) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m : ℕ,
            (∀ U : Homogenization.Book.Ch02.Domain d,
                Measurable
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                      SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                        (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                          (Homogenization.coarseBlockMatrix
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                omega m).toCoeffField))) ∧
                Homogenization.IndependentSums.IsBigOWith P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma 1)
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                    SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (Homogenization.coarseBlockMatrix
                          (U : Set (Homogenization.Vec d))
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                              omega m).toCoeffField)))
                  1) ∧
              (∀ n : ℕ,
                  Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Carriers.annealedBlockMatInfinite
                          nu m P))
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ))))) ∧
                    Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ)))))
                      (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (∀ gamma : ℝ, 0 < gamma → gamma < 1 →
                  ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable S ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma gamma) S
                        (C * Real.exp (C * |Real.log gamma| / gamma) *
                          (3 : ℝ) ^ m) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                        ∀ Q : Homogenization.TriadicCube d, Q.scale ≤ (n : ℤ) →
                          Homogenization.cubeCenter Q ∈
                              Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ)) →
                            Homogenization.BlockMatLoewnerLE
                              (((3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ))))) •
                                SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                                  (Homogenization.coarseBlockMatrix
                                    (Homogenization.cubeSet Q)
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                        omega m).toCoeffField))
                              ((2 : ℝ) • Homogenization.Book.Ch02.blockIdentity d)) := by
  refine ⟨Cscale, fun nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m => ⟨?_, ?_, ?_⟩⟩
  · intro U
    exact ⟨measurable_blockMatrixOperatorNorm_envelopeRescale_of_measurable_Mu m
        (hMu nu hnu m U),
      isBigOWith_gammaSigma_blockMatrixOperatorNorm_envelopeRescale hnu hPrefix hJ2
        hJ3 hJ4 m U⟩
  · have hne : NeZero d := ⟨by have hd := hPrefix.dimension; omega⟩
    intro n
    exact blockMatLoewnerLE_envelopeRescale_annealed_sandwich hnu hPrefix hJ2 hJ3 hJ4
      m n
  · have hne : NeZero d := ⟨by have hd := hPrefix.dimension; omega⟩
    intro gamma hgamma0 hgamma1
    obtain ⟨S, hSmeas, hStail, hSratio⟩ :=
      hScale nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m gamma hgamma0 hgamma1
    exact ⟨S, hSmeas, hStail,
      eventually_blockMatLoewnerLE_of_eventually_weighted_ratio_le hnu hSratio⟩

/-! ## The conclusion with only the random minimal scale as a hypothesis -/

/-- **`l.bfAm.ellip`, in the shape of the printed
statement, from the random minimal scale alone.** The
hypothesis `hMu` of `bfAmEllipticity_of_inputs` is discharged by
`measurable_Mu_domain_coefficientCutoff`, so the only input left is `hScale`,
the random minimal scale of `e.Smgamma.integ` for the scalar random
factor `envelopeRatio`, with the sub-cube clause quantified almost surely in
the sample. Its `∃ C` is witnessed by `Cscale`. -/
theorem bfAmEllipticity_of_minimalScale (d : ℕ) (Cscale : ℝ)
    (hScale : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ (m : ℕ) (gamma : ℝ), 0 < gamma → gamma < 1 →
          ∃ S : ShellSeq d → ℝ,
            Measurable S ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma gamma) S
                (Cscale * Real.exp (Cscale * |Real.log gamma| / gamma) *
                  (3 : ℝ) ^ m) ∧
              ∀ᵐ omega ∂P.toMeasure, ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                ∀ Q : TriadicCube d, Q.scale ≤ (n : ℤ) →
                  cubeCenter Q ∈ cubeSet (originCube d (n : ℤ)) →
                    (3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ)))) *
                      envelopeRatio m Q omega ≤ 2) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m : ℕ,
            (∀ U : Homogenization.Book.Ch02.Domain d,
                Measurable
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                      SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                        (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                          (Homogenization.coarseBlockMatrix
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                omega m).toCoeffField))) ∧
                Homogenization.IndependentSums.IsBigOWith P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma 1)
                  (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
                    SuperdiffusionCLT.Section2.Carriers.blockMatrixOperatorNorm
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (Homogenization.coarseBlockMatrix
                          (U : Set (Homogenization.Vec d))
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                              omega m).toCoeffField)))
                  1) ∧
              (∀ n : ℕ,
                  Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Carriers.annealedBlockMatInfinite
                          nu m P))
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ))))) ∧
                    Homogenization.BlockMatLoewnerLE
                      (SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu m P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (n : ℤ)))))
                      (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (∀ gamma : ℝ, 0 < gamma → gamma < 1 →
                  ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable S ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma gamma) S
                        (C * Real.exp (C * |Real.log gamma| / gamma) *
                          (3 : ℝ) ^ m) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ n : ℕ, S omega ≤ (3 : ℝ) ^ n →
                        ∀ Q : Homogenization.TriadicCube d, Q.scale ≤ (n : ℤ) →
                          Homogenization.cubeCenter Q ∈
                              Homogenization.cubeSet
                                (Homogenization.originCube d (n : ℤ)) →
                            Homogenization.BlockMatLoewnerLE
                              (((3 : ℝ) ^ (-(gamma * ((n : ℝ) - (Q.scale : ℝ))))) •
                                SuperdiffusionCLT.Section2.Annealed.envelopeRescale d nu m
                                  (Homogenization.coarseBlockMatrix
                                    (Homogenization.cubeSet Q)
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                                        omega m).toCoeffField))
                              ((2 : ℝ) • Homogenization.Book.Ch02.blockIdentity d)) :=
  bfAmEllipticity_of_inputs d Cscale
    (fun _ hnu m U P0 => measurable_Mu_domain_coefficientCutoff hnu m U P0) hScale

end

end SuperdiffusionCLT.Section2
