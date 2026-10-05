/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffComparison
public import SuperdiffusionCLT.Section2.Cutoff.CenteredCoeffOn
public import SuperdiffusionCLT.Section2.Cutoff.CutoffApproximationInputs
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField

/-!
# The cutoff approximation lemma on bounded domains

The lemma `l.cutoff.approximation` of the paper is stated as
`SuperdiffusionCLT.Frozen.Section2.cutoff_approximation`. This module
proves it from the results on the centered stream field and its coarse-grained
matrices.

The first conjunct of the statement -- uniform ellipticity of the limiting
centered field `a^U = nu Id + k^U` -- is
`exists_isEllipticMatrix_smul_one_add_centeredStreamField`
(`Section2/Cutoff/CutoffApproximationInputs.lean`), assembled from the
summability hypothesis alone.

The second conjunct needs a Chapter 2 coefficient object for the limiting
field `a^U`, which is not provided elsewhere: the truncation bundle
`centeredCoefficientCutoffCoeffOn` covers the level-`L` field only. That object
is built here as `centeredStreamCoeffOn`, with `lam = nu` and the upper
constant `(d^2 (nu + C)^2 + nu^2)/nu` for `C` the uniform `L∞(U)` bound of the
recentered series supplied by `norm_centeredStreamField_le`. Its only new input
is the a.e. strong measurability of the recentered series, obtained from
`aestronglyMeasurable_of_tendsto_ae` applied to the partial sums, which are
continuous because every shell entry is continuous.

With that bundle in hand the comparison estimate of the printed proof
is
`dirichlet_comparison_of_skew_perturbation`: the difference `a^U - a^U_L`
between the limiting field and the level-`L` centered cutoff is the tail of
the recentered series, bounded on `U` by
`norm_centeredStreamField_sub_centeredStreamCutoff_le`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Carriers
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The entry of a matrix as a continuous linear map -/

/-- Evaluation of a matrix at one entry, as a continuous linear map. -/
def matEntryCLM (d : ℕ) (i k : Fin d) : Mat d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun A => A i k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun A => by
      show ‖A i k‖ ≤ 1 * ‖A‖
      rw [one_mul]
      exact Matrix.norm_entry_le_entrywise_sup_norm A (i := i) (j := k))

@[simp] theorem matEntryCLM_apply (d : ℕ) (i k : Fin d) (A : Mat d) :
    matEntryCLM d i k A = A i k :=
  rfl

/-! ## Measurability of the recentered series -/

/-- Every entry of every centered shell term is continuous in the space
variable: the shell entry is continuous (`shellReg_entry_continuous`) and the
centering is a constant. -/
theorem centeredShellTerm_entry_continuous (omega : ShellSeq d) (U : Set (Vec d))
    (k : ℕ) (i j : Fin d) :
    Continuous (fun x : Vec d => centeredShellTerm omega U k x i j) := by
  have h : (fun x : Vec d => centeredShellTerm omega U k x i j) =
      fun x : Vec d => shellReg omega k x i j -
        volumeAverageMat U (fun y => shellReg omega k y) i j := by
    funext x
    simp only [centeredShellTerm, Matrix.sub_apply]
  rw [h]
  exact (shellReg_entry_continuous omega k i j).sub continuous_const

/-- **Every entry of the recentered series `k^U` is a.e. strongly measurable**
on a Chapter 2 domain under the summability hypothesis of
`l.cutoff.approximation`. The
partial sums are continuous; on `U` they converge pointwise to the series, whose
summability at every point of `U` is `summable_centeredShellTerm`. -/
theorem centeredStreamField_entry_aeStronglyMeasurable (U : Book.Ch02.Domain d)
    (omega : ShellSeq d)
    (hsum : Summable fun k : ℕ => shellDerivLinftyNorm (U : Set (Vec d)) (omega k))
    (i j : Fin d) :
    AEStronglyMeasurable
      (fun x : Vec d => centeredStreamField omega (U : Set (Vec d)) x i j)
      (volumeMeasureOn (U : Set (Vec d))) := by
  have hUb : Bornology.IsBounded (U : Set (Vec d)) :=
    U.isDomain.isBoundedDomain.isBounded
  have hUconv : Convex ℝ (U : Set (Vec d)) := U.convex
  have hUpos : MeasureTheory.volume (U : Set (Vec d)) ≠ 0 :=
    (IsOpen.measure_pos MeasureTheory.volume U.isOpen U.nonempty).ne'
  have hf : ∀ N : ℕ, AEStronglyMeasurable
      (fun x : Vec d =>
        (∑ k ∈ Finset.range N, centeredShellTerm omega (U : Set (Vec d)) k x) i j)
      (volumeMeasureOn (U : Set (Vec d))) := by
    intro N
    refine Continuous.aestronglyMeasurable ?_
    have hsumN : (fun x : Vec d =>
        (∑ k ∈ Finset.range N, centeredShellTerm omega (U : Set (Vec d)) k x) i j) =
        fun x : Vec d =>
          ∑ k ∈ Finset.range N, centeredShellTerm omega (U : Set (Vec d)) k x i j := by
      funext x
      rw [Matrix.sum_apply]
    rw [hsumN]
    exact continuous_finsetSum _
      (fun k _ => centeredShellTerm_entry_continuous omega (U : Set (Vec d)) k i j)
  refine aestronglyMeasurable_of_tendsto_ae (μ := volumeMeasureOn (U : Set (Vec d)))
    (u := Filter.atTop) hf ?_
  filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
  have hsumx : Summable fun k : ℕ => centeredShellTerm omega (U : Set (Vec d)) k x :=
    summable_centeredShellTerm hUb hUconv hUpos omega hsum hx
  have hhs : HasSum (fun k : ℕ => centeredShellTerm omega (U : Set (Vec d)) k x)
      (centeredStreamField omega (U : Set (Vec d)) x) := by
    rw [centeredStreamField_eq_tsum]
    exact hsumx.hasSum
  have hhs_entry := hhs.map (matEntryCLM d i j) (matEntryCLM d i j).continuous
  have hlim := hhs_entry.tendsto_sum_nat
  have hconv : (fun N : ℕ =>
      (∑ k ∈ Finset.range N, centeredShellTerm omega (U : Set (Vec d)) k x) i j) =
      fun N : ℕ =>
        ∑ k ∈ Finset.range N, centeredShellTerm omega (U : Set (Vec d)) k x i j := by
    funext N
    rw [Matrix.sum_apply]
  rw [hconv]
  simpa only [matEntryCLM_apply, Function.comp_apply] using hlim

/-! ## The Chapter 2 coefficient object of the limiting field `a^U` -/

/-- **The Chapter 2 coefficient object of the limiting recentered field**
`a^U = ν Id + k^U` on a bounded domain, under `0 < ν` and
the printed summability hypothesis. The lower ellipticity constant
is the molecular diffusivity `ν`; the upper one is `(d² (ν + C)² + ν²)/ν` for
the uniform bound `C = √d R ∑_k ‖∇ j_k‖_{L∞(U)}` of `norm_centeredStreamField_le`,
the factor `R` bounding the diameter of `U`.

The only obligation beyond the two inputs above is the a.e. strong
measurability of the recentered series, supplied by
`centeredStreamField_entry_aeStronglyMeasurable`. -/
noncomputable def centeredStreamCoeffOn (U : Book.Ch02.Domain d) {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ (U : Set (Vec d)) → ∀ ⦃b : Vec d⦄,
      b ∈ (U : Set (Vec d)) → dist a b ≤ R)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) :
    Book.Ch02.CoeffOn U where
  toCoeffField := fun x => nu • (1 : Mat d) +
    centeredStreamField omega (U : Set (Vec d)) x
  lam := nu
  Lam := ((d : ℝ) * (d : ℝ) * (nu + Real.sqrt d * R *
      (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec d)) (omega k))) ^ 2 + nu ^ 2) / nu
  lam_pos := hnu
  lam_le_Lam := by
    rw [le_div_iff₀ hnu, ← pow_two]
    linarith only [show (0 : ℝ) ≤ (d : ℝ) * (d : ℝ) *
      (nu + Real.sqrt d * R * (∑' k : ℕ,
        shellDerivLinftyNorm (U : Set (Vec d)) (omega k))) ^ 2 by positivity]
  aeStronglyMeasurable := by
    intro i j
    have hAE : MeasureTheory.AEStronglyMeasurable
        (fun x : Vec d => (nu • (1 : Mat d)) i j +
          centeredStreamField omega (U : Set (Vec d)) x i j)
        (volumeMeasureOn (U : Set (Vec d))) :=
      aestronglyMeasurable_const.add
        (centeredStreamField_entry_aeStronglyMeasurable U omega hsum i j)
    refine hAE.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    simp [restrictCoeffField, hx]
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    exact isEllipticMatrix_smul_one_add_centeredStreamField U hnu omega
      (fun y hy i j => abs_centeredStreamField_entry_le U omega hR hsum hy i j) x hx

/-! ## The operator norm of the perturbation -/

/-- **Operator-norm form of the tail bound.** The difference `k^U - (k_L - (k_L)_U)`
of the limiting recentered field and the level-`L` centered cutoff is bounded
in the Euclidean operator norm on `U` by `d²` times the entry bound
`√d R ∑_{k>L} ‖∇ j_k‖_{L∞(U)}`. This is the constant `M` of the printed energy
comparison: `d²` is the loss of the two elementary norm
conversions on `Mat d`. -/
theorem matrixOperatorNorm_centeredStreamField_sub_centeredStreamCutoff_le
    (U : Book.Ch02.Domain d) (omega : ShellSeq d) {R : ℝ}
    (hR : ∀ ⦃a : Vec d⦄, a ∈ (U : Set (Vec d)) → ∀ ⦃b : Vec d⦄,
      b ∈ (U : Set (Vec d)) → dist a b ≤ R)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (U : Set (Vec d)) (omega k))
    {x : Vec d} (hx : x ∈ (U : Set (Vec d))) (L : ℕ) :
    matrixOperatorNorm (centeredStreamField omega (U : Set (Vec d)) x -
        centeredStreamCutoff omega L (U : Set (Vec d)) x) ≤
      (d : ℝ) * (d : ℝ) * (Real.sqrt d * R *
        (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k)))) := by
  set M : ℝ := Real.sqrt d * R *
    (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k))) with hM
  have hentry : ∀ i j : Fin d,
      |(centeredStreamField omega (U : Set (Vec d)) x -
        centeredStreamCutoff omega L (U : Set (Vec d)) x) i j| ≤ M := by
    intro i j
    calc
      |(centeredStreamField omega (U : Set (Vec d)) x -
          centeredStreamCutoff omega L (U : Set (Vec d)) x) i j|
          = ‖(centeredStreamField omega (U : Set (Vec d)) x -
              centeredStreamCutoff omega L (U : Set (Vec d)) x) i j‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ ‖centeredStreamField omega (U : Set (Vec d)) x -
            centeredStreamCutoff omega L (U : Set (Vec d)) x‖ :=
          Matrix.norm_entry_le_entrywise_sup_norm _
      _ ≤ M := by
          rw [hM]
          exact norm_centeredStreamField_sub_centeredStreamCutoff_le U omega hR hsum hx L
  calc
    matrixOperatorNorm (centeredStreamField omega (U : Set (Vec d)) x -
        centeredStreamCutoff omega L (U : Set (Vec d)) x) ≤
        matrixFrobeniusNorm (centeredStreamField omega (U : Set (Vec d)) x -
          centeredStreamCutoff omega L (U : Set (Vec d)) x) :=
      Homogenization.Book.Ch02.matrixOperatorNorm_le_matrixFrobeniusNorm _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
          |(centeredStreamField omega (U : Set (Vec d)) x -
            centeredStreamCutoff omega L (U : Set (Vec d)) x) i j| :=
      Homogenization.Book.Ch02.matrixFrobeniusNorm_le_sum_abs_entries _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, M :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (d : ℝ) * (d : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-! ## The cutoff approximation lemma -/

/-- **Lemma `l.cutoff.approximation`, `d ≥ 1`.** The conclusion of
`SuperdiffusionCLT.Frozen.Section2.cutoff_approximation` verbatim, with
`[NeZero d]` as the sole extra hypothesis. The witness is the explicit
`C = d² √d R` for `R` a diameter bound of `U`; the whole statement is
hypothesis-free beyond the printed `0 < ν ≤ 1` and summability. -/
theorem cutoff_approximation_of_neZero [NeZero d] (U : Book.Ch02.Domain d) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ omega : ShellSeq d,
          Summable (fun k : ℕ =>
              shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) →
            (∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
                ∀ x ∈ (U : Set (Vec d)),
                  IsEllipticMatrix lam Lam
                    (nu • (1 : Mat d) +
                      centeredStreamField omega (U : Set (Vec d)) x)) ∧
              ∀ (L : ℕ) (u : H1Function (U : Set (Vec d))),
                IsAHarmonicGradient
                    (fun x : Vec d =>
                      nu • (1 : Mat d) +
                        centeredStreamField omega (U : Set (Vec d)) x)
                    (U : Set (Vec d)) u.grad →
                  ∃ uL : H1Function (U : Set (Vec d)),
                    (∃ w : H10Function (U : Set (Vec d)),
                      uL = u + w.toH1Function) ∧
                      IsAHarmonicGradient
                        (coefficientCutoff nu omega L).toCoeffField
                        (U : Set (Vec d)) uL.grad ∧
                      Real.sqrt (∫ x in (U : Set (Vec d)),
                          vecNormSq (u.grad x - uL.grad x)
                          ∂MeasureTheory.volume) ≤
                        C * nu⁻¹ *
                            (∑' k : ℕ,
                              shellDerivLinftyNorm (U : Set (Vec d))
                                (omega (L + 1 + k))) *
                          Real.sqrt (∫ x in (U : Set (Vec d)),
                            vecNormSq (u.grad x)
                            ∂MeasureTheory.volume) := by
  classical
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp U.isDomain.isBoundedDomain.isBounded
  refine ⟨(d : ℝ) * (d : ℝ) * Real.sqrt d * R, ?_⟩
  intro nu hnu _hnu1 omega hsum
  refine ⟨exists_isEllipticMatrix_smul_one_add_centeredStreamField U hnu omega hsum, ?_⟩
  intro L u hu
  set a : Book.Ch02.CoeffOn U := centeredStreamCoeffOn U hnu omega hR hsum with ha
  set b : Book.Ch02.CoeffOn U := centeredCoefficientCutoffCoeffOn U hnu omega L with hb
  have ha_apply : ∀ x : Vec d, a.toCoeffField x = nu • (1 : Mat d) +
      centeredStreamField omega (U : Set (Vec d)) x := fun _ => rfl
  have hb_apply : ∀ x : Vec d, b.toCoeffField x =
      (centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField x :=
    fun _ => rfl
  have hu' : IsAHarmonicGradient a.toCoeffField (U : Set (Vec d)) u.grad := hu
  obtain ⟨w, hw⟩ :=
    SuperdiffusionCLT.Section2.Localization.exists_isAHarmonicGradient_add_zeroTraceGrad
      U b u
  set uL : H1Function (U : Set (Vec d)) := u + w.toH1Function with huL
  have hbc : uL = u + w.toH1Function := huL
  have hgrad : uL.grad = fun x : Vec d => u.grad x + w.toH1Function.grad x := by
    rw [huL]
    rfl
  have hub : IsAHarmonicGradient b.toCoeffField (U : Set (Vec d)) uL.grad := by
    rw [hgrad]
    exact hw
  have hbsymm : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      symmPart (b.toCoeffField x) = nu • (1 : Mat d) :=
    Filter.Eventually.of_forall fun x =>
      symmPart_centeredCoefficientCutoff nu omega L (U : Set (Vec d)) x
  have hM : ∀ᵐ x ∂(volumeMeasureOn (U : Set (Vec d))),
      matrixOperatorNorm (a.toCoeffField x - b.toCoeffField x) ≤
        (d : ℝ) * (d : ℝ) * (Real.sqrt d * R *
          (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k)))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    have hdiff : a.toCoeffField x - b.toCoeffField x =
        centeredStreamField omega (U : Set (Vec d)) x -
          centeredStreamCutoff omega L (U : Set (Vec d)) x := by
      rw [ha_apply x, hb_apply x,
        show (centeredCoefficientCutoff nu omega L (U : Set (Vec d))).toCoeffField x =
            centeredCoefficientCutoff nu omega L (U : Set (Vec d)) x from rfl,
        centeredCoefficientCutoff_apply]
      abel
    rw [hdiff]
    exact matrixOperatorNorm_centeredStreamField_sub_centeredStreamCutoff_le U omega hR hsum hx L
  have hcmp :=
    SuperdiffusionCLT.Section2.Localization.dirichlet_comparison_of_skew_perturbation
      (U := U) (a := a) (b := b) hnu hbsymm hM hbc hu' hub
  have hk0 : matTranspose
      (volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L)) =
      -volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L) := by
    have h : -(matTranspose
        (volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L))) =
        -(-volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L)) := by
      simpa only [matTranspose, Matrix.transpose_neg] using
        SuperdiffusionCLT.Section2.CoarseGraining.matTranspose_neg_volumeAverageMat_streamCutoff
          omega L (U : Set (Vec d))
    exact neg_inj.mp h
  have hflux : MemVectorL2 (U : Set (Vec d))
      (fun x : Vec d => matVecMul (b.toCoeffField x) (uL.grad x)) :=
    SuperdiffusionCLT.Section2.Localization.memVectorL2_matVecMul_coeffOn
      b uL.grad_memVectorL2
  have hcoe : (fun x : Vec d => b.toCoeffField x +
        volumeAverageMat (U : Set (Vec d)) (streamCutoff omega L)) =
      (coefficientCutoff nu omega L).toCoeffField := by
    funext x
    rw [hb_apply x,
      congrFun (SuperdiffusionCLT.Section2.CoarseGraining.centeredCoefficientCutoff_toCoeffField
        nu omega L (U : Set (Vec d))) x]
    abel
  have hub_coeff : IsAHarmonicGradient (coefficientCutoff nu omega L).toCoeffField
      (U : Set (Vec d)) uL.grad := by
    have h :=
      (SuperdiffusionCLT.Section2.CoarseGraining.isAHarmonicGradient_add_const_skew_iff
        (U := (U : Set (Vec d))) U.isOpen hk0 (c := b.toCoeffField) (f := uL.grad) hflux).2 hub
    rwa [hcoe] at h
  refine ⟨uL, ⟨w, hbc⟩, hub_coeff, ?_⟩
  have hSp : Real.sqrt (∫ x in (U : Set (Vec d)),
      vecNormSq (u.grad x - uL.grad x) ∂MeasureTheory.volume) ≤
      nu⁻¹ * ((d : ℝ) * (d : ℝ) * (Real.sqrt d * R *
          (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k)))) *
        Real.sqrt (∫ x in (U : Set (Vec d)),
          vecNormSq (u.grad x) ∂MeasureTheory.volume)) := by
    have h2 := mul_le_mul_of_nonneg_left hcmp (le_of_lt (inv_pos.mpr hnu))
    rw [inv_mul_cancel_left₀ (ne_of_gt hnu)] at h2
    exact h2
  calc Real.sqrt (∫ x in (U : Set (Vec d)),
        vecNormSq (u.grad x - uL.grad x) ∂MeasureTheory.volume)
      ≤ nu⁻¹ * ((d : ℝ) * (d : ℝ) * (Real.sqrt d * R *
          (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k)))) *
        Real.sqrt (∫ x in (U : Set (Vec d)),
          vecNormSq (u.grad x) ∂MeasureTheory.volume)) := hSp
    _ = ((d : ℝ) * (d : ℝ) * Real.sqrt d * R) * nu⁻¹ *
          (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec d)) (omega (L + 1 + k))) *
        Real.sqrt (∫ x in (U : Set (Vec d)),
          vecNormSq (u.grad x) ∂MeasureTheory.volume) := by
      ring

/-! ## The statement -/

/-- **Lemma `l.cutoff.approximation`, the statement verbatim.** The
conclusion of `SuperdiffusionCLT.Frozen.Section2.cutoff_approximation`,
proved with no hypothesis beyond the printed ones: `0 < ν ≤ 1` and the
summability of the `L∞(U)` norms of the shell derivatives.

The witness is `C = d² √d R` for `R` a diameter bound of `U`, so `C` is
constant in `ν`, `omega`, `L` and `u`. The proof splits on `d = 0`: the
degenerate case has `Mat 0` and `Vec 0` subsingletons, so the two coefficient
fields coincide and the estimate is `0 ≤ 0`; for `d ≥ 1` the statement is
`cutoff_approximation_of_neZero`. -/
theorem cutoff_approximation (d : ℕ) (U : Book.Ch02.Domain d) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ omega : ShellSeq d,
          Summable (fun k : ℕ =>
              shellDerivLinftyNorm (U : Set (Vec d)) (omega k)) →
            (∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
                ∀ x ∈ (U : Set (Vec d)),
                  IsEllipticMatrix lam Lam
                    (nu • (1 : Mat d) +
                      centeredStreamField omega (U : Set (Vec d)) x)) ∧
              ∀ (L : ℕ) (u : H1Function (U : Set (Vec d))),
                IsAHarmonicGradient
                    (fun x : Vec d =>
                      nu • (1 : Mat d) +
                        centeredStreamField omega (U : Set (Vec d)) x)
                    (U : Set (Vec d)) u.grad →
                  ∃ uL : H1Function (U : Set (Vec d)),
                    (∃ w : H10Function (U : Set (Vec d)),
                      uL = u + w.toH1Function) ∧
                      IsAHarmonicGradient
                        (coefficientCutoff nu omega L).toCoeffField
                        (U : Set (Vec d)) uL.grad ∧
                      Real.sqrt (∫ x in (U : Set (Vec d)),
                          vecNormSq (u.grad x - uL.grad x)
                          ∂MeasureTheory.volume) ≤
                        C * nu⁻¹ *
                            (∑' k : ℕ,
                              shellDerivLinftyNorm (U : Set (Vec d))
                                (omega (L + 1 + k))) *
                          Real.sqrt (∫ x in (U : Set (Vec d)),
                            vecNormSq (u.grad x)
                            ∂MeasureTheory.volume) := by
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, ?_⟩
    intro nu hnu _hnu1 omega hsum
    refine ⟨exists_isEllipticMatrix_smul_one_add_centeredStreamField U hnu omega hsum, ?_⟩
    intro L u hu
    set w0 : H10Function (U : Set (Vec 0)) := 0 with _hw0
    set uL : H1Function (U : Set (Vec 0)) := u + w0.toH1Function with huL
    have hgrad0 : uL.grad = u.grad := by
      rw [huL, H1Function.add_grad]
      funext x
      exact Subsingleton.elim _ _
    have hcoeff : (coefficientCutoff nu omega L).toCoeffField =
        fun x : Vec 0 => nu • (1 : Mat 0) +
          centeredStreamField omega (U : Set (Vec 0)) x := by
      funext x
      exact Subsingleton.elim _ _
    refine ⟨uL, ⟨w0, huL⟩, ?_, ?_⟩
    · rw [hgrad0, hcoeff]
      exact hu
    · have hint : (∫ x in (U : Set (Vec 0)), vecNormSq (u.grad x - u.grad x)
          ∂MeasureTheory.volume) = 0 := by
        have h : (fun x : Vec 0 => vecNormSq (u.grad x - u.grad x)) = fun _ => 0 := by
          funext x
          rw [sub_self, Homogenization.vecNormSq_eq_zero_iff]
        rw [h, MeasureTheory.integral_zero]
      have hrhs : (0 : ℝ) * nu⁻¹ *
          (∑' k : ℕ, shellDerivLinftyNorm (U : Set (Vec 0)) (omega (L + 1 + k))) *
          Real.sqrt (∫ x in (U : Set (Vec 0)), vecNormSq (u.grad x)
            ∂MeasureTheory.volume) = 0 := by
        ring
      rw [hgrad0, hint, hrhs, Real.sqrt_zero]
  · have : NeZero d := ⟨hd⟩
    exact cutoff_approximation_of_neZero U

end

end SuperdiffusionCLT.Section2.Cutoff
