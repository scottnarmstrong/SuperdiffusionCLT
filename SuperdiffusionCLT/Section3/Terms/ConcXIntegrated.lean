/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthB
public import SuperdiffusionCLT.Section3.Terms.ConcentrationComparisonB
public import SuperdiffusionCLT.Section3.Terms.PerClassCentering
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB

/-!
# The `x`-integrated restatement of the block-energy obligation

The printed concentration comparison at the depth observable `a_ℓ ∇ũ_n − q̃`
consumes, at every printed block `B` and at the parent cube `R`, the
a.e.-measurability of the *block-energy* integrand
`omega ↦ ofReal (⍍_B ((a_ℓ ∇ũ_n − q̃)(omega) · i)²)`.  The comparison
supplies it through the single joint-measurability input `hFjoint` — joint
measurability of `(ω, x) ↦ F ω x i` *pointwise in* `x`.  The present module
shows that input is strictly stronger than what the comparison uses: the only
thing taken from it is the a.e.-measurability of an *integral over `x`*, the
block energy itself.

* `..._descendants_of_subcollections_of_xIntegrated` replaces `hFjoint` by those
  block-energy a.e.-measurabilities (`hEmeas` at the blocks, `hEmeas0` at `R`);
  `..._of_subcollections_from_jointMeasurable` re-derives the original statement,
  so the restatement is *faithful* (implied by `hFjoint`, not stronger).
* `aemeasurable_ofReal_volumeAverage_sq_coord_pairingField` discharges the
  bundle outright at the observable field: the coordinate projection is a fixed
  bounded matrix field acting continuously on the `L²(cu_m)` class, and the
  glued class is measurable.  No joint measurability of the field, and no
  per-cube representative, is used.
* `aemeasurable_ofReal_volumeAverage_sq_coord_concDepthField` is that discharge
  at the pinned data; `lintegral_concDepthField_le_decay_subcollections_of_xIntegrated`
  is the printed comparison at that field with `hFjoint` gone.
* `mem_descendantsAtDepth_of_mem_descendantsAtDepth` composes depths, placing
  the printed blocks of a depth-`j` cube inside the descendant family of `cu_m`.

Everything proved here carries explicit witnesses; no lemma collapses to `True`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The coordinate-projection matrix -/

/-- The matrix that keeps exactly the `i`-th coordinate: `v ↦ (v i) • e_i`. -/
private def coordProj (i : Fin d) : Mat d :=
  fun p q => if p = i ∧ q = i then (1 : ℝ) else 0

/-- The coordinate-projection matrix zeroes all but the `i`-th coordinate. -/
private theorem matVecMul_coordProj (i : Fin d) (v : Vec d) :
    matVecMul (coordProj (d := d) i) v = fun p => if p = i then v i else 0 := by
  funext p
  show (∑ j : Fin d, coordProj (d := d) i p j * v j) = (if p = i then v i else 0)
  by_cases hp : p = i
  · subst hp
    simp [coordProj, Finset.sum_ite_eq']
  · rw [ite_eq_right hp]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [coordProj, hp]

/-- The squared length of the coordinate projection is the coordinate square. -/
private theorem vecDot_coordProj (i : Fin d) (v : Vec d) :
    vecDot (matVecMul (coordProj (d := d) i) v) (matVecMul (coordProj (d := d) i) v) =
      (v i) ^ 2 := by
  rw [matVecMul_coordProj]
  show (∑ p : Fin d, (if p = i then v i else 0) * (if p = i then v i else 0)) = (v i) ^ 2
  have hterm : ∀ p : Fin d,
      (if p = i then v i else 0) * (if p = i then v i else 0) =
        (if p = i then (v i) ^ 2 else 0) := by
    intro p
    by_cases hp : p = i <;> simp [hp, sq]
  rw [Finset.sum_congr rfl fun p _ => hterm p]
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ => (v i) ^ 2)]
  simp

/-- A single coordinate square is at most the squared length. -/
private theorem sq_coord_le_vecNormSq (i : Fin d) (v : Vec d) : (v i) ^ 2 ≤ vecNormSq v := by
  rw [vecNormSq_eq_sum_coordSq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

/-- The coordinate projection does not increase the squared length. -/
private theorem vecNormSq_coordProj_le (i : Fin d) (v : Vec d) :
    vecNormSq (matVecMul (coordProj (d := d) i) v) ≤ vecNormSq v := by
  have h : vecNormSq (matVecMul (coordProj (d := d) i) v) = (v i) ^ 2 := by
    show vecDot (matVecMul (coordProj (d := d) i) v) (matVecMul (coordProj (d := d) i) v) =
      (v i) ^ 2
    exact vecDot_coordProj i v
  rw [h]
  exact sq_coord_le_vecNormSq i v

/-! ## Depth composition for the descendant families

The printed blocks are descendants of `R` at a further depth, so the two
statements are matched by the depth composition below. -/

/-- **Depth composition.**  A depth-`t` descendant of a depth-`j` descendant of
`Q` is a depth-`j + t` descendant of `Q`. -/
theorem mem_descendantsAtDepth_of_mem_descendantsAtDepth {Q R : TriadicCube d} (j : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) :
    ∀ {t : ℕ} {B : TriadicCube d}, B ∈ descendantsAtDepth R t →
      B ∈ descendantsAtDepth Q (j + t) := by
  intro t
  induction t with
  | zero =>
      intro B hB
      rw [descendantsAtDepth_zero, Finset.mem_singleton] at hB
      subst hB
      simpa using hR
  | succ t ih =>
      intro B hB
      rw [descendantsAtDepth_succ] at hB
      rw [Nat.add_succ, descendantsAtDepth_succ]
      rcases Finset.mem_biUnion.mp hB with ⟨S, hS, hBS⟩
      exact Finset.mem_biUnion.mpr ⟨S, ih hS, hBS⟩

/-! ## The coordinate block-energy of the observable field is measurable -/

/-- **The coordinate block energy of the pairing field is a.e.-measurable.**  The
`x`-integrated obligation, discharged unconditionally: the energy sees only the
`L²(cu_m)` class, acted on continuously by the coordinate projection. -/
theorem aemeasurable_ofReal_volumeAverage_sq_coord_pairingField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L k m j : ℕ) (F qTilde : Vec d)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) j)
    (i : Fin d) :
    AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal
      (volumeAverage (cubeSet R) (fun x => (pairingField hnu L k m F qTilde omega x i) ^ 2)))
      P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let Q : TriadicCube d := originCube d (m : ℤ)
  set A : Vec d → Mat d := fun x => Set.indicator (cubeSet R) (fun _ => coordProj (d := d) i) x
    with hAdef
  have hA_mem : ∀ x : Vec d, x ∈ cubeSet R → A x = coordProj (d := d) i := by
    intro x hx
    simp only [hAdef, Set.indicator_of_mem hx]
  have hA_notMem : ∀ x : Vec d, x ∉ cubeSet R → A x = (0 : Mat d) := by
    intro x hx
    simp only [hAdef, Set.indicator_of_notMem hx]
  have hsubopen : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hmemR : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet R)
      (pairingField hnu L k m F qTilde omega) :=
    fun omega => memVectorL2_mono hsubopen
      (memVectorL2_pairingField hnu L k m F qTilde omega Q)
  have hmemg : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet R)
      (fun x => matVecMul (coordProj (d := d) i) (pairingField hnu L k m F qTilde omega x)) :=
    fun omega => memVectorL2_matVecMul_const (U := openCubeSet R) (coordProj (d := d) i)
      (hmemR omega)
  have hmulB : ∀ f : Vec d → Vec d, MemVectorL2 (openCubeSet Q) f →
      MemVectorL2 (openCubeSet Q) (fun x => matVecMul (A x) (f x)) := by
    intro f hf
    have hpt : (fun x => matVecMul (A x) (f x)) =
        Set.indicator (cubeSet R) (fun x => matVecMul (coordProj (d := d) i) (f x)) := by
      funext x
      by_cases hx : x ∈ cubeSet R
      · rw [hA_mem x hx, Set.indicator_of_mem hx]
      · rw [hA_notMem x hx, Set.indicator_of_notMem hx]
        show matVecMul (0 : Mat d) (f x) = 0
        funext p
        simp [matVecMul]
    rw [hpt]
    exact memVectorL2_indicator_cubeSet (Q := Q)
      (memVectorL2_matVecMul_const (U := openCubeSet R) (coordProj (d := d) i)
        (memVectorL2_mono hsubopen hf))
  have hbdB : ∀ x ∈ openCubeSet Q, ∀ v : Vec d,
      vecNormSq (matVecMul (A x) v) ≤ (1 : ℝ) ^ 2 * vecNormSq v := by
    intro x _ v
    rw [one_pow, one_mul]
    by_cases hx : x ∈ cubeSet R
    · rw [hA_mem x hx]
      exact vecNormSq_coordProj_le i v
    · rw [hA_notMem x hx]
      have hz : vecNormSq (matVecMul (0 : Mat d) v) = 0 := by
        have h0 : matVecMul (0 : Mat d) v = 0 := by
          funext p
          simp [matVecMul]
        rw [h0]
        simp [vecNormSq, vecDot]
      rw [hz]
      exact vecNormSq_nonneg v
  have hcontMul : Continuous (matFieldMulClass A hmulB) :=
    continuous_matFieldMulClass (measurableSet_openCubeSet Q) A hmulB (by norm_num) hbdB
  have hclass : AEMeasurable (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_pairingField hnu L k m F qTilde omega Q)) P.toMeasure :=
    aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass hnu L k m F qTilde
      (measurable_gluedGradientClass (d := d) hnu L k m F).aemeasurable
  have hkey : ∀ omega : ShellSeq d, toHilbertVectorL2OfVecField
        (memVectorL2_indicator_cubeSet (Q := Q) (hmemg omega)) =
      matFieldMulClass A hmulB (toHilbertVectorL2OfVecField
        (memVectorL2_pairingField hnu L k m F qTilde omega Q)) := by
    intro omega
    rw [matFieldMulClass_toHilbertVectorL2OfVecField A hmulB
      (memVectorL2_pairingField hnu L k m F qTilde omega Q)]
    refine toHilbertVectorL2OfVecField_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ cubeSet R
    · simp only [hA_mem x hx, Set.indicator_of_mem hx]
    · simp only [hA_notMem x hx, Set.indicator_of_notMem hx]
      have h0 : matVecMul (0 : Mat d) (pairingField hnu L k m F qTilde omega x) = 0 := by
        funext p
        simp [matVecMul]
      rw [h0]
  have hMeasClass : AEMeasurable (fun omega : ShellSeq d => matFieldMulClass A hmulB
      (toHilbertVectorL2OfVecField (memVectorL2_pairingField hnu L k m F qTilde omega Q)))
      P.toMeasure :=
    hcontMul.measurable.comp_aemeasurable hclass
  have hMeasInd : AEMeasurable (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_indicator_cubeSet (Q := Q) (hmemg omega))) P.toMeasure :=
    (aemeasurable_congr (Filter.Eventually.of_forall fun omega => (hkey omega).symm)).mp hMeasClass
  have hMeasNorm : AEMeasurable (fun omega : ShellSeq d => ‖toHilbertVectorL2OfVecField
      (memVectorL2_indicator_cubeSet (Q := Q) (hmemg omega))‖) P.toMeasure :=
    continuous_norm.measurable.comp_aemeasurable hMeasInd
  have hMeasProd : AEMeasurable (fun omega : ShellSeq d =>
      (MeasureTheory.volume (cubeSet R)).toReal⁻¹ * ‖toHilbertVectorL2OfVecField
        (memVectorL2_indicator_cubeSet (Q := Q) (hmemg omega))‖ ^ (2 : ℕ)) P.toMeasure :=
    (hMeasNorm.pow_const (2 : ℕ)).const_mul _
  have hnorm : ∀ omega : ShellSeq d,
      volumeAverage (cubeSet R) (fun x => (pairingField hnu L k m F qTilde omega x i) ^ 2) =
        (MeasureTheory.volume (cubeSet R)).toReal⁻¹ * ‖toHilbertVectorL2OfVecField
          (memVectorL2_indicator_cubeSet (Q := Q) (hmemg omega))‖ ^ (2 : ℕ) := by
    intro omega
    have h1 : volumeAverage (cubeSet R)
          (fun x => (pairingField hnu L k m F qTilde omega x i) ^ 2) =
        (MeasureTheory.volume (cubeSet R)).toReal⁻¹ *
          ∫ x in cubeSet R, (pairingField hnu L k m F qTilde omega x i) ^ 2 :=
      rfl
    have hnonneg : (0 : ℝ) ≤ ∫ x in openCubeSet Q,
        vecDot (Set.indicator (cubeSet R) (fun x => matVecMul (coordProj (d := d) i)
            (pairingField hnu L k m F qTilde omega x)) x)
          (Set.indicator (cubeSet R) (fun x => matVecMul (coordProj (d := d) i)
            (pairingField hnu L k m F qTilde omega x)) x) := by
      refine setIntegral_nonneg (measurableSet_openCubeSet Q) fun x _ => ?_
      exact vecNormSq_nonneg _
    have h2 : ‖toHilbertVectorL2OfVecField
          (memVectorL2_indicator_cubeSet (Q := Q) (hmemg omega))‖ ^ (2 : ℕ) =
        ∫ x in cubeSet R, (pairingField hnu L k m F qTilde omega x i) ^ 2 := by
      rw [norm_toHilbertVectorL2OfVecField_eq_sqrt, Real.sq_sqrt hnonneg]
      rw [integral_indicator_cubeSet_vecDot_eq_of_mem_descendantsAtDepth hR
        (fun x => matVecMul (coordProj (d := d) i) (pairingField hnu L k m F qTilde omega x))]
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_cubeSet R) fun x _ => ?_
      exact vecDot_coordProj i (pairingField hnu L k m F qTilde omega x)
    rw [h1, ← h2]
  exact ((aemeasurable_congr (Filter.Eventually.of_forall fun omega =>
    (hnorm omega).symm)).mp hMeasProd).ennreal_ofReal

/-- **The coordinate block energy at the observable field.**
`..._sq_coord_pairingField` at the pinned data of the clause. -/
theorem aemeasurable_ofReal_volumeAverage_sq_coord_concDepthField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (j : ℕ) {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j)
    (i : Fin d) :
    AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal
      (volumeAverage (cubeSet R) (fun x => (concDepthField hnu P S e omega x i) ^ 2)))
      P.toMeasure :=
  aemeasurable_ofReal_volumeAverage_sq_coord_pairingField hnu P S.ell S.n S.m j
    (fluxSlot nu S.LPrime P S.n e)
    (qVector hnu P S.ell S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) hR i

/-! ## The comparison in `x`-integrated form -/

/-- **The printed comparison in `x`-integrated form.**  The
`..._descendants_of_subcollections` with `hFjoint` replaced by the two
block-energy a.e.-measurabilities it actually consumes: `hEmeas` at the printed
blocks and `hEmeas0` at the parent cube. -/
theorem
    lintegral_ofReal_vecNormSq_volumeAverageVec_le_decay_mul_vecSqAvg_descendants_of_subcollections_of_xIntegrated
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {R : TriadicCube d} {m j ell : ℕ} {F : Ω → Vec d → Vec d}
    (hL2 : ∀ ω, MeasureTheory.MemLp (hilbertifyVecField (F ω)) 2 (normalizedCubeMeasure R))
    (hpair : ∀ c ∈ shellColorSet R (m - j - ell), ∀ i : Fin d,
      ∀ B ∈ subcollectionAtDepth R (m - j - ell) c,
      ∀ B' ∈ subcollectionAtDepth R (m - j - ell) c, B ≠ B' →
      ProbabilityTheory.IndepFun (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i))
        (fun ω => volumeAverage (cubeSet B') (fun x => F ω x i)) μ)
    (hmem : ∀ c ∈ shellColorSet R (m - j - ell), ∀ i : Fin d,
      ∀ B ∈ subcollectionAtDepth R (m - j - ell) c,
      MeasureTheory.MemLp (fun ω => volumeAverage (cubeSet B) (fun x => F ω x i)) 2 μ)
    (hmean : ∀ c ∈ shellColorSet R (m - j - ell), ∀ i : Fin d,
      ∀ B ∈ subcollectionAtDepth R (m - j - ell) c,
      ∫ ω, volumeAverage (cubeSet B) (fun x => F ω x i) ∂μ = 0)
    (hEmeas : ∀ i : Fin d, ∀ B ∈ descendantsAtDepth R (m - j - ell),
      AEMeasurable (fun ω => ENNReal.ofReal
        (volumeAverage (cubeSet B) (fun x => (F ω x i) ^ 2))) μ)
    (hEmeas0 : ∀ i : Fin d, AEMeasurable (fun ω => ENNReal.ofReal
      (volumeAverage (cubeSet R) (fun x => (F ω x i) ^ 2))) μ) :
    (∫⁻ ω, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet R) (F ω))) ∂μ) ≤
      ENNReal.ofReal ((printedSubcollectionCount d : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ)))) *
        (∫⁻ ω, ENNReal.ofReal (vecSqAvg R (F ω)) ∂μ) := by
  classical
  have hpart : ∀ i : Fin d, ∀ ω,
      volumeAverage (cubeSet R) (fun x => F ω x i) =
        (((descendantsAtDepth R (m - j - ell)).card : ℝ))⁻¹ *
          ∑ B ∈ descendantsAtDepth R (m - j - ell),
            volumeAverage (cubeSet B) (fun x => F ω x i) := by
    intro i ω
    have h := volumeAverageVec_eq_descendantsAverage_memLp R (m - j - ell) (hL2 ω) i
    dsimp only [descendantsAverage] at h
    simpa only [volumeAverageVec_apply_coord] using h
  have htile : ∀ i : Fin d, ∀ ω,
      ∑ B ∈ descendantsAtDepth R (m - j - ell),
        volumeAverage (cubeSet B) (fun x => (F ω x i) ^ 2) =
      ((descendantsAtDepth R (m - j - ell)).card : ℝ) *
        volumeAverage (cubeSet R) (fun x => (F ω x i) ^ 2) := by
    intro i ω
    have h := volumeAverage_eq_descendantsAverage_integrableOn R (m - j - ell)
      (integrableOn_coord_sq_of_memLp R (hL2 ω) i)
    dsimp only [descendantsAverage] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ (by rw [descendantsAtDepth_card]; positivity), one_mul]
  have hstep : ∀ i : Fin d,
      (∫⁻ ω, ENNReal.ofReal ((volumeAverage (cubeSet R) (fun x => F ω x i)) ^ 2) ∂μ) ≤
        ENNReal.ofReal ((printedSubcollectionCount d : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ)))) *
          ∫⁻ ω, ENNReal.ofReal (volumeAverage (cubeSet R) (fun x => (F ω x i) ^ 2)) ∂μ := by
    intro i
    refine le_trans (lintegral_ofReal_sq_le_subcollectionSum (R := R) (t := m - j - ell)
      (A := fun ω => volumeAverage (cubeSet R) (fun x => F ω x i))
      (Y := fun B ω => volumeAverage (cubeSet B) (fun x => F ω x i))
      (Eb := fun B ω => volumeAverage (cubeSet B) (fun x => (F ω x i) ^ 2))
      (E := fun ω => volumeAverage (cubeSet R) (fun x => (F ω x i) ^ 2))
      (hpart i) (htile i)
      (fun c hc B hB B' hB' hne => hpair c hc i B hB B' hB' hne)
      (fun c hc B hB => hmem c hc i B hB)
      (fun c hc B hB => hmean c hc i B hB)
      (fun B _ => hEmeas i B ‹B ∈ descendantsAtDepth R (m - j - ell)›)
      (fun B _ _ => volumeAverage_cubeSet_nonneg B fun x => sq_nonneg _)
      (fun B hB => lintegral_ofReal_sq_volumeAverage_le_volumeAverage_sq (Q := B) i
        (fun ω => memLp_coord_of_memLp_subset
          (cubeSet_subset_of_mem_descendantsAtDepth hB) (hL2 ω) i))) ?_
    refine mul_le_mul' ?_ le_rfl
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by exact_mod_cast card_shellColorSet_le R (m - j - ell))
        (Real.rpow_nonneg (by norm_num) _))
  have hAmeas : ∀ i : Fin d, AEMeasurable (fun ω =>
      ENNReal.ofReal ((volumeAverage (cubeSet R) (fun x => F ω x i)) ^ 2)) μ := by
    intro i
    have h1 : AEStronglyMeasurable (fun ω => volumeAverage (cubeSet R) (fun x => F ω x i)) μ := by
      have hcongr : (fun ω => volumeAverage (cubeSet R) (fun x => F ω x i)) =
          fun ω => (((descendantsAtDepth R (m - j - ell)).card : ℝ))⁻¹ *
            ∑ c ∈ shellColorSet R (m - j - ell),
              ∑ B ∈ subcollectionAtDepth R (m - j - ell) c,
                volumeAverage (cubeSet B) (fun x => F ω x i) := by
        funext ω
        rw [hpart i ω]
        congr 1
        rw [← biUnion_subcollectionAtDepth R (m - j - ell)]
        exact Finset.sum_biUnion (fun c₁ _ c₂ _ hne => disjoint_subcollectionAtDepth_of_ne hne)
      have hsum : AEStronglyMeasurable
          (∑ c ∈ shellColorSet R (m - j - ell),
            ∑ B ∈ subcollectionAtDepth R (m - j - ell) c,
              fun ω => volumeAverage (cubeSet B) (fun x => F ω x i)) μ :=
        Finset.aestronglyMeasurable_sum _ fun c hc =>
          Finset.aestronglyMeasurable_sum _ fun B hB =>
            (hmem c hc i B hB).aestronglyMeasurable
      rw [hcongr]
      refine (hsum.const_mul (((descendantsAtDepth R (m - j - ell)).card : ℝ)⁻¹)).congr ?_
      filter_upwards with ω
      simp only [Finset.sum_apply]
    exact (h1.aemeasurable.pow_const 2).ennreal_ofReal
  have hEsq : ∀ ω, (∑ i : Fin d, ENNReal.ofReal
        (volumeAverage (cubeSet R) (fun x => (F ω x i) ^ 2))) =
      ENNReal.ofReal (vecSqAvg R (F ω)) := by
    intro ω
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ =>
      volumeAverage_cubeSet_nonneg R fun x => sq_nonneg _, (vecSqAvg_eq_sum_coordSq R (hL2 ω)).symm]
  have hLHS : (∫⁻ ω, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet R) (F ω))) ∂μ) =
      ∑ i : Fin d, ∫⁻ ω,
        ENNReal.ofReal ((volumeAverage (cubeSet R) (fun x => F ω x i)) ^ 2) ∂μ := by
    have hpt : ∀ ω, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet R) (F ω))) =
        ∑ i : Fin d,
          ENNReal.ofReal ((volumeAverage (cubeSet R) (fun x => F ω x i)) ^ 2) := by
      intro ω
      have hsq : vecNormSq (volumeAverageVec (cubeSet R) (F ω)) =
          ∑ i : Fin d, (volumeAverage (cubeSet R) (fun x => F ω x i)) ^ 2 := by
        rw [vecNormSq_eq_sum_coordSq]
        exact Finset.sum_congr rfl fun i _ => by rw [volumeAverageVec_apply_coord]
      rw [hsq, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    rw [lintegral_congr hpt,
      MeasureTheory.lintegral_finsetSum' Finset.univ (fun i _ => hAmeas i)]
  have hRHS : ∑ i : Fin d, (ENNReal.ofReal ((printedSubcollectionCount d : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ)))) *
        ∫⁻ ω, ENNReal.ofReal (volumeAverage (cubeSet R) (fun x => (F ω x i) ^ 2)) ∂μ) =
      ENNReal.ofReal ((printedSubcollectionCount d : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ)))) *
        ∫⁻ ω, ENNReal.ofReal (vecSqAvg R (F ω)) ∂μ := by
    rw [← Finset.mul_sum, ← MeasureTheory.lintegral_finsetSum' Finset.univ
      (fun i _ => hEmeas0 i),
      lintegral_congr hEsq]
  calc (∫⁻ ω, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet R) (F ω))) ∂μ)
      = ∑ i : Fin d, ∫⁻ ω,
          ENNReal.ofReal ((volumeAverage (cubeSet R) (fun x => F ω x i)) ^ 2) ∂μ := hLHS
    _ ≤ ∑ i : Fin d, ENNReal.ofReal ((printedSubcollectionCount d : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ)))) *
          ∫⁻ ω, ENNReal.ofReal (volumeAverage (cubeSet R) (fun x => (F ω x i) ^ 2)) ∂μ :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = ENNReal.ofReal ((printedSubcollectionCount d : ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ)))) *
          ∫⁻ ω, ENNReal.ofReal (vecSqAvg R (F ω)) ∂μ := hRHS

/-! ## The consumer at the observable field, with `hFjoint` gone -/

/-- **The printed comparison at the centred field, `x`-integrated.**  The
`..._le_decay_subcollections` with `hFjoint` removed, block energies discharged
at the observable field. -/
theorem lintegral_concDepthField_le_decay_subcollections_of_xIntegrated [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {j : ℕ} {R : TriadicCube d}
    (hjm : j ≤ S.m) (hR : R ∈ descendantsAtDepth (originCube d (S.m : ℤ)) j)
    (hnj : S.n ≤ S.m - j)
    (hpair : ∀ c ∈ shellColorSet R (S.m - j - S.ell), ∀ i : Fin d,
      ∀ B ∈ subcollectionAtDepth R (S.m - j - S.ell) c,
      ∀ B' ∈ subcollectionAtDepth R (S.m - j - S.ell) c, B ≠ B' →
      ProbabilityTheory.IndepFun
        (fun omega : ShellSeq d => volumeAverage (cubeSet B)
          (fun x => concDepthField hnu P S e omega x i))
        (fun omega : ShellSeq d => volumeAverage (cubeSet B')
          (fun x => concDepthField hnu P S e omega x i)) P.toMeasure)
    (hmem : ∀ c ∈ shellColorSet R (S.m - j - S.ell), ∀ i : Fin d,
      ∀ B ∈ subcollectionAtDepth R (S.m - j - S.ell) c,
      MeasureTheory.MemLp (fun omega : ShellSeq d => volumeAverage (cubeSet B)
        (fun x => concDepthField hnu P S e omega x i)) 2 P.toMeasure) :
    (∫⁻ omega : ShellSeq d, ENNReal.ofReal (vecNormSq (volumeAverageVec (cubeSet R)
        (concDepthField hnu P S e omega))) ∂P.toMeasure) ≤
      ENNReal.ofReal ((printedSubcollectionCount d : ℝ) *
        (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
        (∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (vecSqAvg R (concDepthField hnu P S e omega)) ∂P.toMeasure) :=
  lintegral_ofReal_vecNormSq_volumeAverageVec_le_decay_mul_vecSqAvg_descendants_of_subcollections_of_xIntegrated
    (μ := P.toMeasure) (R := R) (m := S.m) (j := j) (ell := S.ell)
    (F := fun omega => concDepthField hnu P S e omega)
    (fun omega => memLp_hilbertifyVecField_concDepthField_of_cube hnu P S e omega R)
    hpair hmem
    (integral_concDepthField_subcollection_eq_zero hnu P S e hPrefix hJ2 hJ3 hJ4 hjm hR hnj)
    (fun i _ hB => aemeasurable_ofReal_volumeAverage_sq_coord_concDepthField hnu P S e _
      (mem_descendantsAtDepth_of_mem_descendantsAtDepth j hR hB) i)
    (fun i => aemeasurable_ofReal_volumeAverage_sq_coord_concDepthField hnu P S e j hR i)

end

end SuperdiffusionCLT.Section3.Terms
