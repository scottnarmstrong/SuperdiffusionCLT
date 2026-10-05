/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Probability.StationaryProjectionTransport

/-!
# The manuscript bound `c⋆ ≤ 2`

This module proves the display `e.cstar.bound` of the paper: the non-degeneracy constant of
the assumption J5 never exceeds `2`.

The argument is the one printed in the source. Fix a unit direction `e` and a
block `(0, N]` of shells.

1. *Transport.* The block response lives on the law of the block increment on
   the regular coefficient fields of the CoarseGraining library. That law is the pushforward of
   the shell sequence law along the block increment map, which is equivariant for the two
   translation actions, so `Probability/StationaryProjectionTransport.lean`
   identifies the block response energy with the response energy of the
   pulled-back forcing on the sequence space.
2. *Additivity.* The pulled-back forcing is the finite sum of the single-shell
   forcings. Each single-shell forcing is measurable for the coordinate
   sub-sigma-field of its own shell, these sub-sigma-fields are independent by
   J2 and translation invariant, so the response energies add.
3. *Contraction and moments.* The orthogonal projection is a contraction, and by
   J3 the second moment of one shell forcing is at most `1 + e⁻¹`.
4. *Conclusion.* J5 forces `c⋆ (log 3) N ≤ N (1 + e⁻¹) + K` for every `N ≥ 1`,
   hence `c⋆ log 3 ≤ 1 + e⁻¹ ≤ 2 ≤ 2 log 3`, hence `c⋆ ≤ 2`.

## Main results

* `SuperdiffusionCLT.Probability.integral_sq_le_of_gaussian_tail`: the
  layer-cake second-moment bound `E[X²] ≤ 1 + e⁻¹` for a nonnegative variable
  with the J3 tail.
* `SuperdiffusionCLT.Frozen.Assumptions.ShellField.addAction` and
  companions: the translation action of the paper on one shell and on the
  whole shell sequence, with the invariance of the sequence law.
* `SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5.cStar_le_two`: the
  bound `c⋆ ≤ 2`.
-/

@[expose] public section

/-! ## A layer-cake second-moment bound -/

namespace SuperdiffusionCLT.Probability

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A nonnegative measurable variable with the strict Gaussian upper tail above
level one has second moment at most `1 + e⁻¹`.

The layer-cake formula splits the tail integral at level one: below level one
the tail is bounded by the total mass, above level one by `exp (-t)`. -/
theorem integral_sq_le_of_gaussian_tail [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXnonneg : ∀ ω, 0 ≤ X ω)
    (hTail : ∀ t : ℝ, 1 ≤ t →
      μ {ω | t < X ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2)))) :
    ∫ ω, X ω ^ 2 ∂μ ≤ 1 + Real.exp (-1) := by
  have hXsq_meas : Measurable fun ω ↦ X ω ^ 2 := by
    exact hXmeas.pow_const 2
  have hTail_sq : ∀ t : ℝ, 1 ≤ t →
      μ {ω | t < X ω ^ 2} ≤ ENNReal.ofReal (Real.exp (-t)) := by
    intro t ht
    calc
      μ {ω | t < X ω ^ 2} ≤ μ {ω | Real.sqrt t < X ω} := by
        refine measure_mono fun ω hω ↦ ?_
        change t < X ω ^ 2 at hω
        change Real.sqrt t < X ω
        rw [Real.sqrt_lt (by linarith only [ht]) (hXnonneg ω)]
        exact hω
      _ ≤ ENNReal.ofReal (Real.exp (-Real.sqrt t ^ 2)) := by
        refine hTail _ ?_
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt ht
      _ = ENNReal.ofReal (Real.exp (-t)) := by
        rw [Real.sq_sqrt (by linarith only [ht])]
  have hsmall : (∫⁻ t in Ioc (0 : ℝ) 1, μ {ω | t < X ω ^ 2}) ≤ 1 := by
    calc
      (∫⁻ t in Ioc (0 : ℝ) 1, μ {ω | t < X ω ^ 2}) ≤
          ∫⁻ _t in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := by
        refine setLIntegral_mono measurable_const fun t _ ↦ ?_
        exact (measure_mono (Set.subset_univ _)).trans_eq
          (IsProbabilityMeasure.measure_univ (μ := μ))
      _ = 1 := by
        simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ,
          Set.univ_inter, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
  have hlarge : (∫⁻ t in Ioi (1 : ℝ), μ {ω | t < X ω ^ 2}) ≤
      ENNReal.ofReal (Real.exp (-1)) := by
    calc
      (∫⁻ t in Ioi (1 : ℝ), μ {ω | t < X ω ^ 2}) ≤
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
        refine setLIntegral_mono ?_ fun t ht ↦ hTail_sq t ht.le
        exact (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal
      _ = ENNReal.ofReal (∫ t in Ioi (1 : ℝ), Real.exp (-t)) :=
        (ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 1)
          (Filter.Eventually.of_forall fun t ↦ (Real.exp_pos _).le)).symm
      _ = ENNReal.ofReal (Real.exp (-1)) := by rw [integral_exp_neg_Ioi]
  have hlayer : (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ) ≤
      ENNReal.ofReal (1 + Real.exp (-1)) := by
    rw [lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X ω)) hXsq_meas.aemeasurable]
    have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
      (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)).symm
    rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
      ENNReal.ofReal_add (by norm_num) (Real.exp_pos _).le, ENNReal.ofReal_one]
    exact add_le_add hsmall hlarge
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (X ω))
    hXsq_meas.aestronglyMeasurable]
  calc
    (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ).toReal ≤
        (ENNReal.ofReal (1 + Real.exp (-1))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hlayer
    _ = 1 + Real.exp (-1) := ENNReal.toReal_ofReal (by positivity)

end

end SuperdiffusionCLT.Probability

/-! ## The translation action on shells and shell sequences -/

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The manuscript's real spatial translation, as an additive action of `Vec d`
on one marginal shell. -/
noncomputable instance addAction : AddAction (Vec d) (ShellField d) where
  vadd := translate
  zero_vadd j := ShellField.ext fun x ↦ by
    change j (x + 0) = j x
    rw [add_zero]
  add_vadd z w j := ShellField.ext fun x ↦ by
    change j (x + (z + w)) = j (x + z + w)
    rw [add_assoc]

@[simp] theorem vadd_eq_translate (z : Vec d) (j : ShellField d) :
    z +ᵥ j = translate z j := rfl

/-- Fixed-shift measurability of the shell translation action. -/
instance measurableConstVAdd : MeasurableConstVAdd (Vec d) (ShellField d) where
  measurable_const_vadd z := measurable_translate z

/-- Fixed-shift measurability of the simultaneous translation of a whole shell
sequence. -/
instance sequenceMeasurableConstVAdd :
    MeasurableConstVAdd (Vec d) (ℕ → ShellField d) where
  measurable_const_vadd z := measurable_translateSequence z

@[simp] theorem vadd_sequence_eq (z : Vec d) (F : ℕ → ShellField d) :
    z +ᵥ F = translateSequence z F := rfl

/-- Under the shell-law prefix and J2 the canonical shell-sequence law is invariant
under the simultaneous translation of every shell. -/
theorem vaddInvariantMeasure {P : ProbabilityMeasure (ℕ → ShellField d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) :
    VAddInvariantMeasure (Vec d) (ℕ → ShellField d) P.toMeasure where
  measure_preimage_vadd z s hs := by
    change P.toMeasure (translateSequence z ⁻¹' s) = P.toMeasure s
    rw [← Measure.map_apply (measurable_translateSequence z) hs]
    exact congrArg (fun ν : Measure (ℕ → ShellField d) ↦ ν s)
      (map_translateSequence_eq hPrefix hJ2 z)

end SuperdiffusionCLT.Frozen.Assumptions.ShellField

/-! ## Single-shell forcings and the bound on `c⋆` -/

namespace SuperdiffusionCLT.Frozen.Assumptions

open Homogenization MeasureTheory
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ### Elementary auxiliaries -/

private theorem coeFn_finset_sum {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ι : Type*} (s : Finset ι) (f : ι → VectorL2 d μ) :
    ((∑ i ∈ s, f i : VectorL2 d μ) : Ω → HilbertVec d)
      =ᵐ[μ] fun ω ↦ ∑ i ∈ s, (f i : Ω → HilbertVec d) ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero (HilbertVec d) 2 μ
  | insert i s hi ih =>
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with ω h1 h2
      rw [Finset.sum_insert hi, h1]
      simp only [Pi.add_apply, Finset.sum_insert hi, h2]

private theorem norm_sq_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → HilbertVec d} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω, real_inner_self_eq_norm_sq]

private def matVecRight (e : Vec d) : Mat d →ₗ[ℝ] Vec d where
  toFun A := matVecMul A e
  map_add' A B := by
    funext i
    change ∑ j, (A i j + B i j) * e j =
      (∑ j, A i j * e j) + ∑ j, B i j * e j
    simp_rw [add_mul]
    exact Finset.sum_add_distrib
  map_smul' c A := by
    funext i
    change ∑ j, (c * A i j) * e j = c * ∑ j, A i j * e j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [mul_assoc]

private def originForcingLinear (e : Vec d) : Mat d →ₗ[ℝ] HilbertVec d :=
  (HilbertVec.linearEquivVec d).symm.toLinearMap.comp (matVecRight e)

private theorem vecNorm_single_one (i : Fin d) :
    Book.Ch02.vecNorm (Pi.single i 1 : Vec d) = 1 := by
  have hsq : Book.Ch02.vecNorm (Pi.single i 1 : Vec d) ^ 2 = 1 := by
    rw [Book.Ch02.vecNorm_sq_eq_vecNormSq, vecNormSq, vecDot,
      Finset.sum_eq_single i]
    · simp
    · intro j _ hij
      simp [Pi.single_eq_of_ne hij]
    · simp
  calc Book.Ch02.vecNorm (Pi.single i 1 : Vec d)
      = Real.sqrt (Book.Ch02.vecNorm (Pi.single i 1 : Vec d) ^ 2) :=
        (Real.sqrt_sq (Book.Ch02.vecNorm_nonneg _)).symm
    _ = 1 := by rw [hsq, Real.sqrt_one]

/-! ### The single-shell forcing -/

/-- The manuscript's single-shell forcing `j_l e` evaluated at the spatial
origin, as a function of the shell sequence. -/
def shellOriginForcing (e : Vec d) (l : ℕ) (omega : ShellSeq d) : HilbertVec d :=
  originForcing e (shellReg omega l)

theorem measurable_shellOriginForcing (e : Vec d) (l : ℕ) :
    Measurable (shellOriginForcing (d := d) e l) :=
  (measurable_originForcing e).comp (measurable_shellReg l)

/-- The single-shell forcings of a finite block add up to the block forcing. -/
theorem originForcing_finiteShellIncrement (e : Vec d) (n m : ℕ)
    (omega : ShellSeq d) :
    originForcing e (finiteShellIncrement omega n m) =
      ∑ l ∈ Finset.Ioc n m, shellOriginForcing e l omega := by
  have hval : (finiteShellIncrement omega n m) 0 =
      ∑ l ∈ Finset.Ioc n m, (shellReg omega l) 0 :=
    finiteShellIncrement_apply omega n m 0
  change originForcingLinear e ((finiteShellIncrement omega n m) 0) =
    ∑ l ∈ Finset.Ioc n m, originForcingLinear e ((shellReg omega l) 0)
  rw [hval]
  exact map_sum (originForcingLinear e) _ _

/-- The J3 observable of shell `l` dominates the single-shell forcing in a unit
direction. -/
theorem norm_shellOriginForcing_le_j3Observable (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (l : ℕ) (omega : ShellSeq d) :
    ‖shellOriginForcing e l omega‖ ≤ ShellField.j3Observable d l (omega l) := by
  refine (norm_originForcing_le_matrixOperatorNorm e (shellReg omega l) he).trans ?_
  exact ShellField.matrixOperatorNorm_zero_le_j3Observable l (omega l)

/-- Under J3 every single-shell forcing is square integrable for the canonical
sequence law. -/
theorem ShellLawJ3.memLp_shellOriginForcing (hJ3 : ShellLawJ3 d P) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (l : ℕ) :
    MemLp (shellOriginForcing (d := d) e l) 2 P.toMeasure := by
  refine (hJ3.memLp_two_j3Observable_coordinate l).mono'
    (measurable_shellOriginForcing e l).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega ↦ ?_)
  exact norm_shellOriginForcing_le_j3Observable e he l omega

/-- The canonical `L²` element of the single-shell forcing. -/
def shellForcingL2 (hJ3 : ShellLawJ3 d P) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (l : ℕ) : VectorL2 d P.toMeasure :=
  (hJ3.memLp_shellOriginForcing e he l).toLp (shellOriginForcing e l)

/-- **The second moment of one shell forcing is at most `1 + e⁻¹`.** -/
theorem norm_sq_shellForcingL2_le (hJ3 : ShellLawJ3 d P) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (l : ℕ) :
    ‖shellForcingL2 hJ3 e he l‖ ^ 2 ≤ 1 + Real.exp (-1) := by
  rw [shellForcingL2, norm_sq_toLp]
  have hobsLp := hJ3.memLp_two_j3Observable_coordinate l
  have hint₁ : Integrable
      (fun omega : ShellSeq d ↦ ‖shellOriginForcing e l omega‖ ^ 2) P.toMeasure :=
    (memLp_two_iff_integrable_sq_norm
      (measurable_shellOriginForcing e l).aestronglyMeasurable).mp
      (hJ3.memLp_shellOriginForcing e he l)
  have hint₂ : Integrable
      (fun omega : ShellSeq d ↦ ShellField.j3Observable d l (omega l) ^ 2)
      P.toMeasure := hobsLp.integrable_sq
  refine le_trans (integral_mono hint₁ hint₂ fun omega ↦ ?_) ?_
  · exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_shellOriginForcing_le_j3Observable e he l omega) 2
  · refine SuperdiffusionCLT.Probability.integral_sq_le_of_gaussian_tail
      (ShellLawJ3.measurable_j3Observable_coordinate l)
      (fun omega ↦ ShellField.j3Observable_nonneg d l (omega l))
      (hJ3.gaussian_tail l)

/-! ### Transport of the block response to the sequence space -/

/-- The block increment map pushes the shell-sequence law forward to the block
law. -/
theorem measurePreserving_finiteShellIncrement
    (P : ProbabilityMeasure (ℕ → ShellField d)) (n m : ℕ) :
    MeasurePreserving (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m)
      P.toMeasure (blockRegLaw P n m).toMeasure :=
  ⟨measurable_finiteShellIncrement n m, (blockRegLaw_toMeasure P n m).symm⟩

/-- The block increment map is equivariant for the two translation actions. -/
theorem finiteShellIncrement_vadd (z : Vec d) (omega : ShellSeq d) (n m : ℕ) :
    finiteShellIncrement (z +ᵥ omega) n m = z +ᵥ finiteShellIncrement omega n m :=
  (translateReg_finiteShellIncrement z omega n m).symm

/-- The pullback of the block forcing is the sum of the single-shell forcings of
the block. -/
theorem transportL2_blockForcingL2 (hJ3 : ShellLawJ3 d P) (n m : ℕ) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) :
    transportL2 (HilbertVec d) (measurePreserving_finiteShellIncrement P n m)
        (blockForcingL2 P n m e (memLp_originForcing_blockRegLaw hJ3 n m e he))
      = ∑ l ∈ Finset.Ioc n m, shellForcingL2 hJ3 e he l := by
  have hT := measurePreserving_finiteShellIncrement P n m
  have hmem := memLp_originForcing_blockRegLaw hJ3 n m e he
  refine Lp.ext ?_
  have h1 := coeFn_transportL2 (μ := P.toMeasure) hT (blockForcingL2 P n m e hmem)
  have h2 : ((blockForcingL2 P n m e hmem : RegCoeffField d → HilbertVec d) ∘
        fun omega : ShellSeq d ↦ finiteShellIncrement omega n m)
      =ᵐ[P.toMeasure] originForcing e ∘
        fun omega : ShellSeq d ↦ finiteShellIncrement omega n m := by
    refine ae_eq_comp hT.measurable.aemeasurable ?_
    rw [hT.map_eq]
    exact coeFn_blockForcingL2 P n m e hmem
  have h3 := coeFn_finset_sum (μ := P.toMeasure) (Finset.Ioc n m)
    fun l ↦ shellForcingL2 hJ3 e he l
  have h4 : ∀ᵐ omega ∂P.toMeasure, ∀ l ∈ Finset.Ioc n m,
      (shellForcingL2 hJ3 e he l : ShellSeq d → HilbertVec d) omega =
        shellOriginForcing e l omega :=
    (Filter.eventually_all_finset _).2 fun l _ ↦
      (hJ3.memLp_shellOriginForcing e he l).coeFn_toLp
  filter_upwards [h1, h2, h3, h4] with omega hh1 hh2 hh3 hh4
  simp only [Function.comp_apply] at hh1 hh2
  rw [hh1, hh2, hh3, originForcing_finiteShellIncrement]
  exact (Finset.sum_congr rfl fun l hl ↦ hh4 l hl).symm

/-- The block response energy equals the response energy of the sum of the
single-shell forcings on the sequence space.

The translation invariance of the sequence law that makes the right-hand side
meaningful is the one `hPrefix` and `hJ2` already supply, so it is read off from
them rather than assumed again. -/
theorem norm_blockPotentialResponse_eq
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (n m : ℕ) (e : Vec d) (he : Book.Ch02.vecNorm e = 1) :
    letI := ShellField.vaddInvariantMeasure hPrefix hJ2
    ‖blockPotentialResponse P n m (blockRegLaw_stationary hPrefix hJ2 n m) e
        (memLp_originForcing_blockRegLaw hJ3 n m e he)‖ =
      ‖stationaryPotentialProjection (μ := P.toMeasure)
        (∑ l ∈ Finset.Ioc n m, shellForcingL2 hJ3 e he l)‖ := by
  have := ShellField.vaddInvariantMeasure hPrefix hJ2
  have := blockRegLaw_vaddInvariant P n m (blockRegLaw_stationary hPrefix hJ2 n m)
  rw [← transportL2_blockForcingL2 hJ3 n m e he]
  exact (norm_stationaryPotentialProjection_transportL2
    (measurePreserving_finiteShellIncrement P n m)
    (fun z omega ↦ finiteShellIncrement_vadd z omega n m) _).symm

/-! ### Additivity over independent shells -/

/-- Each single-shell forcing is measurable for the coordinate sub-sigma-field of
its own shell. -/
theorem aestronglyMeasurable_shellForcingL2 (hJ3 : ShellLawJ3 d P) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (l : ℕ) :
    AEStronglyMeasurable[MeasurableSpace.comap
        (fun omega : ShellSeq d ↦ omega l) inferInstance]
      (shellForcingL2 hJ3 e he l : ShellSeq d → HilbertVec d) P.toMeasure := by
  refine AEStronglyMeasurable.congr ?_
    ((hJ3.memLp_shellOriginForcing e he l).coeFn_toLp).symm
  refine (Measurable.stronglyMeasurable ?_).aestronglyMeasurable
  exact ((measurable_originForcing e).comp ShellField.measurable_forgetShell).comp
    (comap_measurable fun omega : ShellSeq d ↦ omega l)

/-- **The response energies of distinct shells add.** -/
theorem norm_sq_stationaryPotentialProjection_sum
    [VAddInvariantMeasure (Vec d) (ℕ → ShellField d) P.toMeasure]
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) (s : Finset ℕ) :
    ‖stationaryPotentialProjection (μ := P.toMeasure)
        (∑ l ∈ s, shellForcingL2 hJ3 e he l)‖ ^ 2 =
      ∑ l ∈ s, ‖stationaryPotentialProjection (μ := P.toMeasure)
        (shellForcingL2 hJ3 e he l)‖ ^ 2 :=
  norm_stationaryPotentialProjection_sum_sq s
    (fun l ↦ MeasurableSpace.comap (fun omega : ShellSeq d ↦ omega l) inferInstance)
    (fun l ↦ (ShellField.measurable_shellCoordinate l).comap_le)
    (fun l ↦ isVAddInvariantSubalgebra_comap
      (fun omega : ShellSeq d ↦ omega l) fun _ _ ↦ rfl)
    hJ2.independent.iIndep _
    (aestronglyMeasurable_shellForcingL2 hJ3 e he)

/-! ### The bound on the non-degeneracy constant -/

/-- **The manuscript bound `c⋆ ≤ 2`** (display `e.cstar.bound`).

For a block of `N` shells the J5 estimate forces
`c⋆ (log 3) N ≤ K + Σ ‖response of shell l‖²`. Each shell response energy is at
most the forcing energy, which the J3 Gaussian tail bounds by `1 + e⁻¹`.
Dividing by `N` and letting `N` grow gives `c⋆ log 3 ≤ 1 + e⁻¹ ≤ 2 ≤ 2 log 3`. -/
theorem ShellLawJ5.cStar_le_two {d : ℕ}
    {P : ProbabilityMeasure (ℕ → ShellField d)} {cStar K : ℝ}
    {hPrefix : ShellLawPrefix d P} {hJ2 : ShellLawJ2 d P} {hJ3 : ShellLawJ3 d P}
    (hJ5 : ShellLawJ5 d P cStar K hPrefix hJ2 hJ3) : cStar ≤ 2 := by
  have := ShellField.vaddInvariantMeasure hPrefix hJ2
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  set i : Fin d := ⟨0, hdpos⟩ with hi
  set e : Vec d := Pi.single i 1 with hedef
  have he : Book.Ch02.vecNorm e = 1 := vecNorm_single_one i
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have hlog3pos : (0 : ℝ) < Real.log 3 := lt_trans one_pos hlog3
  have hMle : 1 + Real.exp (-1) ≤ 2 := by
    have hlt : Real.exp (-1) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    linarith only [hlt]
  have hkey : ∀ N : ℕ, 0 < N →
      cStar * Real.log 3 * (N : ℝ) ≤ (N : ℝ) * (1 + Real.exp (-1)) + K := by
    intro N hN
    have hnd := hJ5.nondegenerate 0 N hN e he
    rw [Nat.sub_zero] at hnd
    have hlow : cStar * Real.log 3 * (N : ℝ) - K ≤
        ‖blockPotentialResponse P 0 N (blockRegLaw_stationary hPrefix hJ2 0 N) e
          (memLp_originForcing_blockRegLaw hJ3 0 N e he)‖ ^ 2 := by
      have habs := abs_le.mp hnd
      linarith only [habs.1]
    have hcard : (Finset.Ioc 0 N).card = N := by rw [Nat.card_Ioc, Nat.sub_zero]
    have hup : ‖blockPotentialResponse P 0 N
          (blockRegLaw_stationary hPrefix hJ2 0 N) e
          (memLp_originForcing_blockRegLaw hJ3 0 N e he)‖ ^ 2 ≤
        (N : ℝ) * (1 + Real.exp (-1)) := by
      rw [norm_blockPotentialResponse_eq hPrefix hJ2 hJ3 0 N e he,
        norm_sq_stationaryPotentialProjection_sum hJ2 hJ3 e he]
      calc
        ∑ l ∈ Finset.Ioc 0 N, ‖stationaryPotentialProjection (μ := P.toMeasure)
            (shellForcingL2 hJ3 e he l)‖ ^ 2 ≤
            ∑ _l ∈ Finset.Ioc 0 N, (1 + Real.exp (-1)) := by
          refine Finset.sum_le_sum fun l _ ↦ ?_
          have hcontract : ‖stationaryPotentialProjection (μ := P.toMeasure)
              (shellForcingL2 hJ3 e he l)‖ ≤ ‖shellForcingL2 hJ3 e he l‖ :=
            Submodule.norm_starProjection_apply_le _ _
          refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hcontract 2) ?_
          exact norm_sq_shellForcingL2_le hJ3 e he l
        _ = (N : ℝ) * (1 + Real.exp (-1)) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
    linarith only [hlow, hup]
  have hcl : cStar * Real.log 3 ≤ 1 + Real.exp (-1) := by
    by_contra hcon
    push Not at hcon
    have hδpos : 0 < cStar * Real.log 3 - (1 + Real.exp (-1)) := by
      linarith only [hcon]
    obtain ⟨N, hN⟩ := exists_nat_gt
      (K / (cStar * Real.log 3 - (1 + Real.exp (-1))))
    have hquot : 0 < K / (cStar * Real.log 3 - (1 + Real.exp (-1))) :=
      div_pos hJ5.K_pos hδpos
    have hNposR : (0 : ℝ) < (N : ℝ) := lt_trans hquot hN
    have hNpos : 0 < N := by exact_mod_cast hNposR
    have hbig : K < (cStar * Real.log 3 - (1 + Real.exp (-1))) * (N : ℝ) := by
      rw [div_lt_iff₀ hδpos] at hN
      linarith only [hN]
    have hsmall := hkey N hNpos
    have hexpand : (cStar * Real.log 3 - (1 + Real.exp (-1))) * (N : ℝ) =
        cStar * Real.log 3 * (N : ℝ) - (N : ℝ) * (1 + Real.exp (-1)) := by ring
    rw [hexpand] at hbig
    linarith only [hbig, hsmall]
  have hfinal : cStar * Real.log 3 ≤ 2 * Real.log 3 := by
    linarith only [hcl, hMle, hlog3]
  exact le_of_mul_le_mul_right hfinal hlog3pos

end

end SuperdiffusionCLT.Frozen.Assumptions
