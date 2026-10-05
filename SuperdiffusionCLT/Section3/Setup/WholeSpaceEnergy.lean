/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import SuperdiffusionCLT.Assumptions.ShellField.SpatialAverage
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters

/-!
# The whole-space stationary energy `E[|∇ŵ_F(0)|²]`

The proof of `l.LHS.term1` runs the lower bound
`e.nabla.w.lower.bound` through the scalar

`E0 = E[|∇ŵ_F(0)|²]`,

the second moment at the spatial origin of the stationary potential gradient of
the flux `F = (k_{L'} − k_{ℓ'}) p`. This file supplies that scalar carrier and
the structural facts about it that the proof uses.

* `wholeSpaceEnergy` is the scalar itself, read as the `.toReal` of the
  lower integral of `‖∇ŵ(0)‖²`, which is the shape in which
  `SuperdiffusionCLT.Frozen.Section3.responseFields_stationary`
  sandwiches it between the two response energies.
* `coeFn_finsetSum_vectorL2` is the almost-everywhere formula for a finite sum in
  `VectorL2`, which is what turns the block statement `a.j.nondeg` (`ShellLawJ5`) into a
  statement about the whole space and, downstream, gives `ŵ = Σ_r ŵ_{j_r p}`.

The file also contains the two consequences of the shell laws that
the end of the proof consumes:

* `integral_eq_zero_of_negateSequence_neg` and its two spatial-average
  corollaries: the zero-mean step `E[(j_r p)_{cu_m}] = 0` that
  `e.average.error.energy` needs, from the negation half of J4; and
* `wholeSpaceEnergy_eq_vecNormSq_mul_norm_sq_blockPotentialResponse` together
  with `abs_wholeSpaceEnergy_sub_cStar_mul_le`, which is display
  `e.use.nondeg.ass`: the whole-space energy of the flux
  `(k_{L'} − k_{ℓ'}) p` is `|p|²` times the block response energy of the unit
  direction `e`, so `ShellLawJ5` at the block `(ℓ', L']` bounds
  `|E0 − c⋆ (log 3)(m − n) |p|²|` by `K |p|²`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary algebra of the matrix-vector action -/

theorem matVecMul_smul_right (A : Mat d) (lam : ℝ) (x : Vec d) :
    matVecMul A (lam • x) = lam • matVecMul A x := by
  funext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem matVecMul_neg_left (A : Mat d) (x : Vec d) :
    matVecMul (-A) x = -matVecMul A x := by
  funext i
  simp only [matVecMul, Matrix.neg_apply, Pi.neg_apply, neg_mul,
    Finset.sum_neg_distrib]

theorem ofVec_smul (lam : ℝ) (x : Vec d) :
    HilbertVec.ofVec (lam • x) = lam • HilbertVec.ofVec x := by
  simpa only [HilbertVec.ofVecL_apply] using (HilbertVec.ofVecL d).map_smul lam x

theorem measurable_matVecMul_left {Omega : Type*} [MeasurableSpace Omega]
    {M : Omega → Mat d} (hM : Measurable M) (x : Vec d) :
    Measurable fun a => matVecMul (M a) x := by
  rw [measurable_pi_iff]
  intro i
  simp only [matVecMul]
  exact Finset.univ.measurable_sum fun j _ =>
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)).mul_const (x j)

/-! ## The scalar carrier -/

section Carrier

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **The whole-space stationary energy `E0 = E[|∇ŵ_F(0)|²]`** as a real number: the
`.toReal` of the lower integral of the squared Euclidean length of the
stationary potential gradient at the spatial origin.

This is exactly the middle term of the sandwich that
`responseFields_stationary` produces, so no separate identification theorem
is needed to consume it. -/
def wholeSpaceEnergy (mu : Measure Omega) (gradHatW : Omega → Vec d) : ℝ :=
  (∫⁻ omega, ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂mu).toReal

/-- For a square-integrable stationary gradient the whole-space energy is the
squared `L²` norm of its canonical `L²` representative. -/
theorem wholeSpaceEnergy_eq_norm_sq_toLp {mu : Measure Omega}
    {gradHatW : Omega → Vec d}
    (hG : MemLp (fun omega => HilbertVec.ofVec (gradHatW omega)) 2 mu) :
    wholeSpaceEnergy mu gradHatW =
      ‖hG.toLp fun omega => HilbertVec.ofVec (gradHatW omega)‖ ^ 2 := by
  set f : Omega → HilbertVec d := fun omega => HilbertVec.ofVec (gradHatW omega)
    with hf
  have h1 : ‖hG.toLp f‖ ^ 2 = ∫ omega, ‖f omega‖ ^ 2 ∂mu := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hG.coeFn_toLp] with omega homega
    rw [homega, real_inner_self_eq_norm_sq]
  have hmeas : AEStronglyMeasurable (fun omega => ‖f omega‖ ^ 2) mu :=
    (continuous_pow 2).comp_aestronglyMeasurable hG.aestronglyMeasurable.norm
  have h2 : ∫ omega, ‖f omega‖ ^ 2 ∂mu
      = (∫⁻ omega, ENNReal.ofReal (‖f omega‖ ^ 2) ∂mu).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => by positivity) hmeas
  rw [h1, h2, wholeSpaceEnergy]
  congr 1
  refine lintegral_congr fun omega => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The lower integral defining a square-integrable whole-space energy is
finite, so `.toReal` is faithful on it. -/
theorem lintegral_enorm_sq_ofVec_ne_top {mu : Measure Omega} {gradHatW : Omega → Vec d}
    (hG : MemLp (fun omega => HilbertVec.ofVec (gradHatW omega)) 2 mu) :
    (∫⁻ omega, ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂mu) ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (f := fun omega => HilbertVec.ofVec (gradHatW omega)) (p := 2) (μ := mu)
    (by norm_num) (by norm_num) hG.eLpNorm_lt_top
  have hcast : ∀ omega : Omega, ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ ((2 : ℝ≥0∞).toReal)
      = ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) := by
    intro omega
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [hcast] at h
  exact h.ne

end Carrier

section Invariance

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable [AddAction (Vec d) Omega] [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

end Invariance

/-! ## Finite sums in `VectorL2` -/

section Linearity

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
variable [AddAction (Vec d) Omega] [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

omit [AddAction (Vec d) Omega] [MeasurableConstVAdd (Vec d) Omega]
  [VAddInvariantMeasure (Vec d) Omega mu] in
theorem coeFn_finsetSum_vectorL2 {iota : Type*} (s : Finset iota)
    (f : iota → VectorL2 d mu) :
    ((∑ i ∈ s, f i : VectorL2 d mu) : Omega → HilbertVec d)
      =ᵐ[mu] fun omega => ∑ i ∈ s, (f i : Omega → HilbertVec d) omega := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero (HilbertVec d) 2 mu
  | insert i s hi ih =>
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with omega h1 h2
      rw [Finset.sum_insert hi, h1]
      simp only [Pi.add_apply, Finset.sum_insert hi, h2]

end Linearity

/-! ## The zero-mean step of `e.average.error.energy` -/

section ZeroMean

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- **The J4 zero-mean principle.** Whole-sequence negation preserves the shell
law (the `negation` clause of `ShellLawJ4`), so every Bochner
integrable observable that negation turns into its own negative has vanishing
expectation.

Integrability is not needed: Lean's Bochner integral of a non-integrable
function is zero, and both sides of the symmetry identity are then zero. -/
theorem integral_eq_zero_of_negateSequence_neg (hJ4 : ShellLawJ4 d P)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ShellSeq d → E} (hX : AEStronglyMeasurable X P.toMeasure)
    (hneg : ∀ omega : ShellSeq d, X (ShellField.negateSequence omega) = -X omega) :
    ∫ omega, X omega ∂P.toMeasure = 0 := by
  have hNegLaw : Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hJ4.negation
    change Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure at h
    exact h
  have hEq : (∫ omega, X omega ∂P.toMeasure) = -∫ omega, X omega ∂P.toMeasure := by
    calc
      ∫ omega, X omega ∂P.toMeasure =
          ∫ omega, X omega
            ∂Measure.map (ShellField.negateSequence (d := d)) P.toMeasure := by
        rw [hNegLaw]
      _ = ∫ omega, X (ShellField.negateSequence omega) ∂P.toMeasure :=
        integral_map ShellField.measurable_negateSequence.aemeasurable
          (by rw [hNegLaw]; exact hX)
      _ = ∫ omega, -X omega ∂P.toMeasure := by
        refine integral_congr_ae ?_
        filter_upwards with omega
        rw [hneg omega]
      _ = -∫ omega, X omega ∂P.toMeasure := integral_neg X
  have h2 : (2 : ℝ) • (∫ omega, X omega ∂P.toMeasure) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hEq]
    abel
  simpa only [smul_eq_zero, OfNat.ofNat_ne_zero, false_or] using h2

theorem measurable_matVecMul_shellSpatialAverage (r : ℕ) (h : ℤ) (y p : Vec d) :
    Measurable fun omega : ShellSeq d =>
      matVecMul (ShellField.shellSpatialAverage h y (omega r)) p :=
  measurable_matVecMul_left
    ((ShellField.measurable_shellSpatialAverage h y).comp (measurable_pi_apply r)) p

end ZeroMean

/-! ## The whole-space energy of the block flux `(k_{L'} − k_{ℓ'}) p` -/

section BlockFlux

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- The `L²` representative of the origin value of the manuscript's flux
`F = (k_{L'} − k_{ℓ'}) p` with `p = lam e` is `lam` times the sum of the
single-shell forcings of the block `(n, m]`.

This is the increment identity `finiteShellIncrement_apply_eq_streamCutoff_sub`
combined with `originForcing_finiteShellIncrement`. -/
theorem toLp_originFlux_eq_smul_sum_shellForcingL2 (hJ3 : ShellLawJ3 d P)
    {n m : ℕ} (hnm : n ≤ m) (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1)
    (lam : ℝ) (p : Vec d) (hp : p = lam • e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega m x - streamCutoff omega n x) p)
    (hFmemLp :
      MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) 2 P.toMeasure) :
    (hFmemLp.toLp fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) =
      lam • ∑ l ∈ Finset.Ioc n m, shellForcingL2 hJ3 e hunit l := by
  refine Lp.ext ?_
  have hshell : ∀ᵐ omega ∂P.toMeasure, ∀ l ∈ Finset.Ioc n m,
      (shellForcingL2 hJ3 e hunit l : ShellSeq d → HilbertVec d) omega =
        shellOriginForcing e l omega :=
    (Filter.eventually_all_finset _).2 fun l _ =>
      (hJ3.memLp_shellOriginForcing e hunit l).coeFn_toLp
  filter_upwards [hFmemLp.coeFn_toLp,
    Lp.coeFn_smul lam (∑ l ∈ Finset.Ioc n m, shellForcingL2 hJ3 e hunit l),
    coeFn_finsetSum_vectorL2 (Finset.Ioc n m) fun l => shellForcingL2 hJ3 e hunit l,
    hshell] with omega h1 h2 h3 h4
  rw [h1, h2]
  simp only [Pi.smul_apply]
  rw [h3, Finset.sum_congr rfl fun l hl => h4 l hl]
  simp only [hF omega, hp]
  rw [matVecMul_smul_right, ofVec_smul,
    ← finiteShellIncrement_apply_eq_streamCutoff_sub omega hnm 0]
  congr 1
  exact originForcing_finiteShellIncrement e n m omega

/-- **`E[|∇ŵ_F(0)|²] = |p|² ‖grad Δ⁻¹ div ((k_m − k_n) e)‖²`.** The whole-space
stationary energy of the block flux `F = (k_m − k_n) p` at `p = lam e` is `|p|²`
times the block response energy of the unit direction `e`, which is the scalar
that `ShellLawJ5` constrains.

The hypotheses `hFmemLp`, `hGmemLp` and `hproj` are the ones
`responseFields_stationary` carries, verbatim. -/
theorem wholeSpaceEnergy_eq_vecNormSq_mul_norm_sq_blockPotentialResponse
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {n m : ℕ} (hnm : n ≤ m) (e : Vec d) (hunit : Book.Ch02.vecNorm e = 1)
    (he : vecNormSq e = 1) (lam : ℝ) (p : Vec d) (hp : p = lam • e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega m x - streamCutoff omega n x) p)
    (gradHatW : ShellSeq d → Vec d)
    (hFmemLp :
      MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
    (hGmemLp :
      MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hproj : (hGmemLp.toLp fun omega : ShellSeq d =>
        HilbertVec.ofVec (gradHatW omega)) =
      -stationaryPotentialProjection (μ := P.toMeasure)
        (hFmemLp.toLp fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0))) :
    wholeSpaceEnergy P.toMeasure gradHatW =
      vecNormSq p * ‖blockPotentialResponse P n m
        (blockRegLaw_stationary hPrefix hJ2 n m) e
        (memLp_originForcing_blockRegLaw hJ3 n m e hunit)‖ ^ 2 := by
  have hnorm : vecNormSq p = lam ^ 2 := by
    rw [hp, vecNormSq_smul, he, mul_one]
  have hblk := norm_blockPotentialResponse_eq hPrefix hJ2 hJ3 n m e hunit
  rw [wholeSpaceEnergy_eq_norm_sq_toLp hGmemLp, hproj, norm_neg,
    toLp_originFlux_eq_smul_sum_shellForcingL2 hJ3 hnm e hunit lam p hp F hF hFmemLp,
    map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hblk, hnorm]

/-- **Display `e.use.nondeg.ass`**: the `ShellLawJ5` bound at the
block `(n, m]` and the unit direction `e`, transported to the whole-space energy
of the flux `(k_m − k_n) p`.

The hypothesis `hJ5app` is the `nondegenerate` clause of
`ShellLawJ5` in its applied shape at `(n, m]` and `e`; it is exactly the shape
in which the lower-bound lemma of `l.LHS.term1` receives it. -/
theorem abs_wholeSpaceEnergy_sub_cStar_mul_le
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {cStar K : ℝ} {n m : ℕ} (hnm : n ≤ m) (e : Vec d)
    (hunit : Book.Ch02.vecNorm e = 1) (he : vecNormSq e = 1)
    (lam : ℝ) (p : Vec d) (hp : p = lam • e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega m x - streamCutoff omega n x) p)
    (gradHatW : ShellSeq d → Vec d)
    (hFmemLp :
      MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
    (hGmemLp :
      MemLp (fun omega : ShellSeq d => HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hproj : (hGmemLp.toLp fun omega : ShellSeq d =>
        HilbertVec.ofVec (gradHatW omega)) =
      -stationaryPotentialProjection (μ := P.toMeasure)
        (hFmemLp.toLp fun omega : ShellSeq d => HilbertVec.ofVec (F omega 0)))
    (hJ5app : |‖blockPotentialResponse P n m
          (blockRegLaw_stationary hPrefix hJ2 n m) e
          (memLp_originForcing_blockRegLaw hJ3 n m e hunit)‖ ^ 2 -
        cStar * Real.log 3 * ((m - n : ℕ) : ℝ)| ≤ K) :
    |wholeSpaceEnergy P.toMeasure gradHatW -
        cStar * Real.log 3 * ((m - n : ℕ) : ℝ) * vecNormSq p| ≤ K * vecNormSq p := by
  have hE0 := wholeSpaceEnergy_eq_vecNormSq_mul_norm_sq_blockPotentialResponse
    hPrefix hJ2 hJ3 hnm e hunit he lam p hp F hF gradHatW hFmemLp hGmemLp hproj
  have hpos : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
  have hfactor : wholeSpaceEnergy P.toMeasure gradHatW -
      cStar * Real.log 3 * ((m - n : ℕ) : ℝ) * vecNormSq p =
      vecNormSq p * (‖blockPotentialResponse P n m
          (blockRegLaw_stationary hPrefix hJ2 n m) e
          (memLp_originForcing_blockRegLaw hJ3 n m e hunit)‖ ^ 2 -
        cStar * Real.log 3 * ((m - n : ℕ) : ℝ)) := by
    rw [hE0]; ring
  rw [hfactor, abs_mul, abs_of_nonneg hpos, mul_comm K (vecNormSq p)]
  exact mul_le_mul_of_nonneg_left hJ5app hpos

end BlockFlux

end

end SuperdiffusionCLT.Section3.Setup
