/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationC
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationD
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Caccioppoli

/-!
# The De Giorgi step on shrinking concentric cubes

The concentric cube `subCube z L s = axisCube (z + s) (L - 2 s)`, the truncated and cut-off test
function `η (u - k)₊ ∈ H¹₀(Q)`, and the localised energy bound for its gradient.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The concentric cube of `axisCube z L` with margin `s`. -/
def subCube (z : Vec d) (L s : ℝ) : Set (Vec d) := axisCube (z + fun _ => s) (L - 2 * s)

theorem subCube_zero (z : Vec d) (L : ℝ) : subCube z L 0 = axisCube z L := by
  unfold subCube
  have : (z + fun _ => (0 : ℝ)) = z := by funext i; simp
  rw [this]
  congr 1
  ring

theorem halfCube_eq_subCube (z : Vec d) (L : ℝ) : halfCube z L = subCube z L (L / 4) := by
  unfold halfCube subCube
  congr 1
  ring

theorem isOpen_subCube (z : Vec d) (L s : ℝ) : IsOpen (subCube z L s) := isOpen_axisCube _ _

theorem subCube_subset {z : Vec d} {L s : ℝ} (hs : 0 ≤ s) : subCube z L s ⊆ axisCube z L := by
  intro x hx j _
  have h := hx j (Set.mem_univ j)
  simp only [Set.mem_Ioo, Pi.add_apply] at h ⊢
  constructor <;> linarith only [h.1, h.2, hs]

theorem subCube_anti {z : Vec d} {L s s' : ℝ} (hs : s ≤ s') : subCube z L s' ⊆ subCube z L s := by
  intro x hx j _
  have h := hx j (Set.mem_univ j)
  simp only [Set.mem_Ioo, Pi.add_apply] at h ⊢
  constructor <;> linarith only [h.1, h.2, hs]

theorem axisCube_add_eq_subCube (z : Vec d) (L s δ : ℝ) :
    axisCube ((z + fun _ => s) + fun _ => δ) (L - 2 * s - 2 * δ) = subCube z L (s + δ) := by
  unfold subCube
  have h1 : (z + fun _ => s) + (fun _ => δ) = z + fun _ => s + δ := by
    funext i; simp [add_assoc]
  rw [h1]
  congr 1
  ring

theorem isEllipticFieldOn_mono {lam Lam : ℝ} {U V : Set (Vec d)} {a : CoeffField d}
    (hV : MeasurableSet V) (hVU : V ⊆ U) (h : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam V a := by
  classical
  refine ⟨?_, fun x hx => h.2 x (hVU hx)⟩
  have h1 := h.1
  have : (fun x i j => if x ∈ V then a x i j else 0) =
      fun x => if x ∈ V then (fun i j => if x ∈ U then a x i j else 0) else 0 := by
    funext x i j
    by_cases hx : x ∈ V
    · simp [hx, hVU hx]
    · simp [hx]
  rw [this]
  exact Measurable.ite hV h1 measurable_const

theorem cutoffGrad_eq_zero {η : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport η) :
    cutoffGrad η x = 0 := by
  funext i
  have : fderiv ℝ η x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset ℝ h)
  simp [cutoffGrad, this]

theorem integral_eq_of_vanish {Q S : Set (Vec d)} (hQ : MeasurableSet Q) (hS : S ⊆ Q)
    {F : Vec d → ℝ} (h : ∀ x, x ∉ S → F x = 0) :
    ∫ x in Q, F x = ∫ x in S, F x :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ hS fun x hx => h x hx.2

/-- The test function `η (u - k)₊` as an `H¹₀` function. -/
theorem exists_cutoff_truncation_h10 {z : Vec d} {L : ℝ} (u : H1Function (axisCube z L)) (k : ℝ)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ axisCube z L) :
    ∃ (W : H1Function (axisCube z L)) (w : H10Function (axisCube z L)),
      W.toFun = (fun x => max (u.toFun x - k) 0) ∧
      (∀ᵐ x ∂(volume.restrict (axisCube z L)),
        W.grad x = {y | k < u.toFun y}.indicator u.grad x) ∧
      w.toH1Function.toFun = (fun x => η x * W.toFun x) ∧
      (∀ᵐ x ∂(volume.restrict (axisCube z L)), ∀ i,
        w.toH1Function.grad x i = η x * W.grad x i + W.toFun x * cutoffGrad η x i) := by
  have hQo : IsOpen (axisCube z L) := isOpen_axisCube z L
  have hconv := isOpenBoundedConvexDomain_axisCube z L
  obtain ⟨W, hWf, hWg⟩ := exists_h1_max_sub_const hconv u k
  set φ1 : H1Function (axisCube z L) := W.mulContDiffHasCompactSupport hη hηc with hφ1
  have hφ1f : φ1.toFun = fun x => η x * W.toFun x := by
    rw [hφ1]; exact H1Function.mulContDiffHasCompactSupport_toFun W hη hηc
  have hφ1g : φ1.grad = fun x i => η x * W.grad x i +
      W.toFun x * (fderiv ℝ η x) (basisVec i) := by
    rw [hφ1]; exact H1Function.mulContDiffHasCompactSupport_grad W hη hηc
  have hmem : MemH10 (axisCube z L) φ1.toFun := by
    refine memH10_of_compactSupport hconv φ1 (K := tsupport η) hηc hηs ?_
    intro x hx
    rw [hφ1f]
    simp [image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨W, φ, hWf, hWg, by rw [hφ, hφ1f], ?_⟩
  have hall : ∀ᵐ x ∂(volume.restrict (axisCube z L)), ∀ i,
      φ.toH1Function.grad x i = φ1.grad x i :=
    ae_all_iff.2 fun i => gradCoord_ae_eq_of_toFun_eq hQo φ.toH1Function φ1 hφ i
  filter_upwards [hall] with x hx i
  rw [hx i, hφ1g]
  rfl

theorem vecNormSq_add_le (a b : Vec d) :
    vecNormSq (a + b) ≤ 2 * vecNormSq a + 2 * vecNormSq b := by
  unfold vecNormSq vecDot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := sq_nonneg (a i - b i)
  simp only [Pi.add_apply]
  linarith only [this]

theorem vecNormSq_smul (c : ℝ) (v : Vec d) : vecNormSq (c • v) = c ^ 2 * vecNormSq v := by
  unfold vecNormSq
  rw [vecDot_smul_left, vecDot_smul_right]
  ring

theorem integrable_vecNormSq_grad {U : Set (Vec d)} (u : H1Function U) :
    Integrable (fun x => vecNormSq (u.grad x)) (volume.restrict U) :=
  caccioppoli_integrable_vecDot_of_memLp u.gradMemL2 u.gradMemL2

theorem vecNormSq_le_of_eucNorm_le {v : Vec d} {G : ℝ} (h : eucNorm v ≤ G) :
    vecNormSq v ≤ G ^ 2 := by
  rw [← eucNorm_sq]
  exact pow_le_pow_left₀ (eucNorm_nonneg v) h 2

/-- Localised energy bound for the gradient of the cut-off truncation `w = η W`. -/
theorem grad_sq_cutoff_bound {z : Vec d} {L : ℝ} {S : Set (Vec d)} (hSQ : S ⊆ axisCube z L)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ S)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {G : ℝ}
    (hG : ∀ x, eucNorm (cutoffGrad η x) ≤ G)
    (W : H1Function (axisCube z L)) (w : H10Function (axisCube z L))
    (hwg : ∀ᵐ x ∂(volume.restrict (axisCube z L)), ∀ i,
      w.toH1Function.grad x i = η x * W.grad x i + W.toFun x * cutoffGrad η x i) :
    ∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x) ≤
      2 * (∫ x in S, η x ^ 2 * vecNormSq (W.grad x)) + 2 * G ^ 2 * ∫ x in S, W.toFun x ^ 2 := by
  have hQm : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  set μ : Measure (Vec d) := volume.restrict (axisCube z L) with hμ
  have hηc : Continuous η := hη.continuous
  have hηb : ∀ x, |η x| ≤ 1 := fun x => by rw [abs_of_nonneg (hη0 x)]; exact hη1 x
  have hG0 : 0 ≤ G := (eucNorm_nonneg _).trans (hG 0)
  have hc : ∀ i, MemLp (fun x => (η x • W.grad x) i) 2 μ := fun i => by
    simpa using memLp_two_mul_bdd (μ := μ) hηc.aestronglyMeasurable
      (Filter.Eventually.of_forall hηb) (W.gradMemL2 i)
  have I1 : Integrable (fun x => η x ^ 2 * vecNormSq (W.grad x)) μ := by
    refine (caccioppoli_integrable_vecDot_of_memLp (F := fun x => η x • W.grad x)
      (G := fun x => η x • W.grad x) hc hc).congr (Filter.Eventually.of_forall fun x => ?_)
    show vecDot (η x • W.grad x) (η x • W.grad x) = _
    have := vecNormSq_smul (η x) (W.grad x)
    unfold vecNormSq at this
    exact this
  have hN2c : Continuous (fun x => vecNormSq (cutoffGrad η x)) := by
    unfold vecNormSq vecDot
    exact continuous_finsetSum _ fun i _ =>
      (cutoffGrad_continuous hη i).mul (cutoffGrad_continuous hη i)
  have hNb : ∀ x, ‖vecNormSq (cutoffGrad η x)‖ ≤ G ^ 2 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _)]
    exact vecNormSq_le_of_eucNorm_le (hG x)
  have I2 : Integrable (fun x => vecNormSq (cutoffGrad η x) * W.toFun x ^ 2) μ :=
    W.memL2.integrable_sq.bdd_mul hN2c.aestronglyMeasurable (Filter.Eventually.of_forall hNb)
  have hpt : ∀ᵐ x ∂μ, vecNormSq (w.toH1Function.grad x) ≤
      2 * (η x ^ 2 * vecNormSq (W.grad x)) + 2 * (vecNormSq (cutoffGrad η x) * W.toFun x ^ 2) := by
    filter_upwards [hwg] with x hx
    have hv : w.toH1Function.grad x = η x • W.grad x + W.toFun x • cutoffGrad η x := by
      funext i; simp [hx i]
    rw [hv]
    refine (vecNormSq_add_le _ _).trans ?_
    rw [vecNormSq_smul, vecNormSq_smul]
    exact le_of_eq (by ring)
  have hI3 := integrable_vecNormSq_grad w.toH1Function
  have hmono : ∫ x, vecNormSq (w.toH1Function.grad x) ∂μ ≤
      ∫ x, (2 * (η x ^ 2 * vecNormSq (W.grad x)) +
        2 * (vecNormSq (cutoffGrad η x) * W.toFun x ^ 2)) ∂μ :=
    integral_mono_ae hI3 ((I1.const_mul 2).add (I2.const_mul 2)) hpt
  rw [integral_add (I1.const_mul 2) (I2.const_mul 2), integral_const_mul, integral_const_mul]
    at hmono
  have hnotS : ∀ x, x ∉ S → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h))
  have e1 : ∫ x in axisCube z L, η x ^ 2 * vecNormSq (W.grad x) =
      ∫ x in S, η x ^ 2 * vecNormSq (W.grad x) :=
    integral_eq_of_vanish hQm hSQ fun x hx => by simp [hnotS x hx]
  have e2 : ∫ x in axisCube z L, vecNormSq (cutoffGrad η x) * W.toFun x ^ 2 =
      ∫ x in S, vecNormSq (cutoffGrad η x) * W.toFun x ^ 2 :=
    integral_eq_of_vanish hQm hSQ fun x hx => by
      have : cutoffGrad η x = 0 := cutoffGrad_eq_zero fun h => hx (hηs h)
      simp [this, vecNormSq, vecDot]
  have hmS : Measure.restrict volume S ≤ μ := Measure.restrict_mono hSQ le_rfl
  have e3 : ∫ x in S, vecNormSq (cutoffGrad η x) * W.toFun x ^ 2 ≤
      ∫ x in S, G ^ 2 * W.toFun x ^ 2 := by
    refine integral_mono (I2.mono_measure hmS)
      ((W.memL2.integrable_sq.const_mul (G ^ 2)).mono_measure hmS) fun x => ?_
    exact mul_le_mul_of_nonneg_right (vecNormSq_le_of_eucNorm_le (hG x)) (sq_nonneg _)
  rw [integral_const_mul] at e3
  rw [e1, e2] at hmono
  linarith only [hmono, e3]

/-- The level inequality and the Caccioppoli bound on the concentric subcube `Q_s`, for the
cut-off `η` supported in `Q_s`. -/
theorem caccioppoli_subcube {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {L : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (axisCube z L) a)
    (u : H1Function (axisCube z L)) (f : Vec d → ℝ) (g : Vec d → Vec d) {Fb Gb : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (axisCube z L)))
    (hgm : AEStronglyMeasurable g (volume.restrict (axisCube z L)))
    (hf : ∀ᵐ x ∂(volume.restrict (axisCube z L)), |f x| ≤ Fb)
    (hg : ∀ᵐ x ∂(volume.restrict (axisCube z L)), eucNorm (g x) ≤ Gb)
    (k : ℝ) {s : ℝ} (hs : 0 ≤ s)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηsupp : tsupport η ⊆ subCube z L s)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {G : ℝ}
    (hG : ∀ x, eucNorm (cutoffGrad η x) ≤ G)
    (hlev : ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
      (∫ x in axisCube z L, f x * (η x ^ 2 * max (u.toFun x - k) 0)) +
        ∫ x in axisCube z L, vecDot (g x) (levelTest u k η x)) :
    ∫ x in subCube z L s, η x ^ 2 * vecNormSq ({y | k < u.toFun y}.indicator u.grad x) ≤
      (8 * d ^ 2 + 4) * ((Lam / lam) ^ 2 * G ^ 2 *
          (∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2) +
        (1 / lam) ^ 2 * (Gb ^ 2 + (L - 2 * s) ^ 2 * Fb ^ 2) *
          (volume ({x | k < u.toFun x} ∩ tsupport η)).toReal) := by
  have hsub : subCube z L s ⊆ axisCube z L := subCube_subset hs
  have hQm : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  have hQsm : MeasurableSet (subCube z L s) := (isOpen_subCube z L s).measurableSet
  have hηsQ : tsupport η ⊆ axisCube z L := hηsupp.trans hsub
  let us : H1Function (subCube z L s) := u.restrict (isOpen_subCube z L s) hsub
  have hnot : ∀ x, x ∉ subCube z L s → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hηsupp h))
  have hLT : ∀ x, x ∉ subCube z L s → levelTest u k η x = 0 := by
    intro x hx
    have hN : cutoffGrad η x = 0 := cutoffGrad_eq_zero fun h => hx (hηsupp h)
    unfold levelTest
    simp [hnot x hx, hN]
  have hlev_s : ∫ x in subCube z L s, vecDot (matVecMul (a x) (us.grad x)) (levelTest us k η x) =
      (∫ x in subCube z L s, f x * (η x ^ 2 * max (us.toFun x - k) 0)) +
        ∫ x in subCube z L s, vecDot (g x) (levelTest us k η x) := by
    have e1 := integral_eq_of_vanish hQm hsub (F := fun x =>
      vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x)) (fun x hx => by
        simp [hLT x hx, vecDot])
    have e2 := integral_eq_of_vanish hQm hsub (F := fun x => f x * (η x ^ 2 * max (u.toFun x - k) 0))
      (fun x hx => by simp [hnot x hx])
    have e3 := integral_eq_of_vanish hQm hsub (F := fun x => vecDot (g x) (levelTest u k η x))
      (fun x hx => by simp [hLT x hx, vecDot])
    show ∫ x in subCube z L s, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
      (∫ x in subCube z L s, f x * (η x ^ 2 * max (u.toFun x - k) 0)) +
        ∫ x in subCube z L s, vecDot (g x) (levelTest u k η x)
    rw [← e1, ← e2, ← e3]
    exact hlev
  have hEll_s : IsEllipticFieldOn lam Lam (axisCube (z + fun _ => s) (L - 2 * s)) a :=
    isEllipticFieldOn_mono hQsm hsub hEll
  have hmono : volume.restrict (subCube z L s) ≤ volume.restrict (axisCube z L) :=
    Measure.restrict_mono hsub le_rfl
  exact caccioppoli_truncation (lam := lam) (Lam := Lam) (a := a) (z + fun _ => s)
    (L := L - 2 * s) hEll_s us k f g (Fb := Fb) (Gb := Gb) (hfm.mono_measure hmono)
    (hgm.mono_measure hmono) (ae_restrict_of_ae_restrict_of_subset hsub hf)
    (ae_restrict_of_ae_restrict_of_subset hsub hg) hη hηsupp hη0 hη1 hG hlev_s

/-- **One De Giorgi step.** For a level `k` and margins `s`, `δ`: the `L²` mass of `(u - k)₊` on
`Q_{s+δ}` is controlled by the mass and the measure of `{u > k}` on `Q_s`, with the Sobolev gain
`|{u > k} ∩ Q_s|^{1 - 2/2^*}`. -/
theorem deGiorgi_step (hd : 2 ≤ d) :
    ∃ Cs c : ℝ, 0 ≤ Cs ∧ 0 ≤ c ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} (z : Vec d) {L : ℝ}, 0 < L →
      IsEllipticFieldOn lam Lam (axisCube z L) a →
      ∀ (u : H1Function (axisCube z L)) (f : Vec d → ℝ) (g : Vec d → Vec d) {Fb Gb : ℝ},
        AEStronglyMeasurable f (volume.restrict (axisCube z L)) →
        AEStronglyMeasurable g (volume.restrict (axisCube z L)) →
        (∀ᵐ x ∂(volume.restrict (axisCube z L)), |f x| ≤ Fb) →
        (∀ᵐ x ∂(volume.restrict (axisCube z L)), eucNorm (g x) ≤ Gb) →
        ∀ (k : ℝ),
        (∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
          tsupport η ⊆ axisCube z L →
          ∫ x in axisCube z L, vecDot (matVecMul (a x) (u.grad x)) (levelTest u k η x) =
            (∫ x in axisCube z L, f x * (η x ^ 2 * max (u.toFun x - k) 0)) +
              ∫ x in axisCube z L, vecDot (g x) (levelTest u k η x)) →
        ∀ (s δ : ℝ), 0 ≤ s → 0 < δ →
        ∫ x in subCube z L (s + δ), max (u.toFun x - k) 0 ^ 2 ≤
          Cs * L ^ (2 * ((d : ℝ) / sobStar d) + 2 - d) *
            (2 * (8 * d ^ 2 + 4) * ((Lam / lam) ^ 2 * (c / δ) ^ 2 *
                (∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2) +
              (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) *
                (volume ({x | k < u.toFun x} ∩ subCube z L s)).toReal) +
              2 * (c / δ) ^ 2 * ∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2) *
            (volume ({x | k < u.toFun x} ∩ subCube z L s)).toReal ^ (1 - 2 / sobStar d) := by
  obtain ⟨c, hc0, hcut⟩ := exists_cube_cutoff d
  obtain ⟨Cs, hCs0, hSH⟩ := sobolev_holder_sq hd
  refine ⟨Cs, c, hCs0, hc0, ?_⟩
  intro lam Lam a z L hL hEll u f g Fb Gb hfm hgm hf hg k hlev s δ hs hδ
  have hp : 2 < sobStar d := two_lt_sobStar hd
  have hβ : 0 ≤ 1 - 2 / sobStar d := by
    have : 2 / sobStar d ≤ 1 := by
      rw [div_le_one (by linarith only [hp])]; exact hp.le
    linarith only [this]
  have hQm : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  have hQsm : MeasurableSet (subCube z L s) := (isOpen_subCube z L s).measurableSet
  have hsub : subCube z L s ⊆ axisCube z L := subCube_subset hs
  have hA0 : 0 ≤ ∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  set A := ∫ x in subCube z L s, max (u.toFun x - k) 0 ^ 2 with hAdef
  set T := (volume ({x | k < u.toFun x} ∩ subCube z L s)).toReal with hTdef
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  by_cases hne : (subCube z L s).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hempty : subCube z L (s + δ) = ∅ :=
      Set.eq_empty_of_subset_empty (hne ▸ subCube_anti (z := z) (L := L) (by linarith only [hδ]))
    rw [hempty]
    simp only [Measure.restrict_empty, integral_zero_measure]
    positivity
  obtain ⟨x0, hx0⟩ := hne
  have hx0Q : x0 ∈ axisCube z L := hsub hx0
  obtain ⟨hlam, hlamLam, -, -⟩ := hEll.2 x0 hx0Q
  have hL' : 0 < L - 2 * s := by
    have := hx0 ⟨0, by omega⟩ (Set.mem_univ _)
    simp only [Set.mem_Ioo, Pi.add_apply] at this
    linarith only [this.1, this.2]
  obtain ⟨η, hη, hηc, hηsupp, hη0, hη1, hηone, hηG⟩ := hcut (z + fun _ => s) (L - 2 * s) δ hδ
  have hηsupp' : tsupport η ⊆ subCube z L s := hηsupp
  have hηsQ : tsupport η ⊆ axisCube z L := hηsupp'.trans hsub
  obtain ⟨W, w, hWf, hWg, hwf, hwg⟩ := exists_cutoff_truncation_h10 u k hη hηc hηsQ
  have hcacc := caccioppoli_subcube z hEll u f g hfm hgm hf hg k hs hη hηsupp' hη0 hη1 hηG
    (hlev hη hηc hηsQ)
  set E : Set (Vec d) := {x | k < u.toFun x} ∩ tsupport η with hE
  have hEQ : E ⊆ axisCube z L := Set.inter_subset_right.trans hηsQ
  have hEsupp : Function.support w.toH1Function.toFun ⊆ E := by
    intro x hx
    rw [Function.mem_support, hwf, hWf] at hx
    have hx' := mul_ne_zero_iff.1 hx
    refine ⟨?_, subset_tsupport η (Function.mem_support.2 hx'.1)⟩
    by_contra h
    exact hx'.2 (max_eq_right (by linarith only [not_lt.1 (show ¬ (k < u.toFun x) from h)]))
  have hsh := hSH z L hL w E hEQ hEsupp
  have hgrad := grad_sq_cutoff_bound hsub hη hηsupp' hη0 hη1 hηG W w hwg
  have hWA : ∫ x in subCube z L s, W.toFun x ^ 2 = A := by
    simp only [hWf, hAdef]
  have hCi : ∫ x in subCube z L s, η x ^ 2 * vecNormSq (W.grad x) =
      ∫ x in subCube z L s, η x ^ 2 * vecNormSq ({y | k < u.toFun y}.indicator u.grad x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hWg] with x hx
    rw [hx]
  have hfinQ : volume (axisCube z L) < ⊤ := by
    have := measure_univ_axisCube z L
    rw [Measure.restrict_apply_univ] at this
    rw [this]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hVT : (volume E).toReal ≤ T := by
    refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_right _ hηsupp'))
    exact ((measure_mono (Set.inter_subset_right.trans hsub)).trans_lt hfinQ).ne
  have hV0 : 0 ≤ (volume E).toReal := ENNReal.toReal_nonneg
  -- left side
  have hwQ : Integrable (fun x => w.toH1Function.toFun x ^ 2) (volume.restrict (axisCube z L)) :=
    w.toH1Function.memL2.integrable_sq
  have hLHS : ∫ x in subCube z L (s + δ), max (u.toFun x - k) 0 ^ 2 ≤
      ∫ x in axisCube z L, w.toH1Function.toFun x ^ 2 := by
    have hsub2 : subCube z L (s + δ) ⊆ axisCube z L :=
      (subCube_anti (z := z) (L := L) (by linarith only [hδ])).trans hsub
    have h1 : ∫ x in subCube z L (s + δ), max (u.toFun x - k) 0 ^ 2 =
        ∫ x in subCube z L (s + δ), w.toH1Function.toFun x ^ 2 := by
      refine setIntegral_congr_fun (isOpen_subCube z L (s + δ)).measurableSet fun x hx => ?_
      have hx' : x ∈ axisCube ((z + fun _ => s) + fun _ => δ) (L - 2 * s - 2 * δ) := by
        rw [axisCube_add_eq_subCube]; exact hx
      simp only [hwf, hWf, hηone x hx', one_mul]
    rw [h1]
    exact setIntegral_mono_set hwQ (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub2 hx)
  -- constants
  have hEd : (1 / lam) ^ 2 * (Gb ^ 2 + (L - 2 * s) ^ 2 * Fb ^ 2) ≤
      (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have : (L - 2 * s) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ hL'.le (by linarith only [hs]) 2
    have := mul_le_mul_of_nonneg_right this (sq_nonneg Fb)
    linarith only [this]
  have hEd0 : 0 ≤ (1 / lam) ^ 2 * (Gb ^ 2 + (L - 2 * s) ^ 2 * Fb ^ 2) := by positivity
  have hCi_le : ∫ x in subCube z L s, η x ^ 2 * vecNormSq (W.grad x) ≤
      (8 * d ^ 2 + 4) * ((Lam / lam) ^ 2 * (c / δ) ^ 2 * A +
        (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * T) := by
    rw [hCi]
    refine hcacc.trans (mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (by positivity))
    exact mul_le_mul hEd hVT hV0 (hEd0.trans hEd)
  have hB2 : ∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x) ≤
      2 * (8 * d ^ 2 + 4) * ((Lam / lam) ^ 2 * (c / δ) ^ 2 * A +
        (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * T) + 2 * (c / δ) ^ 2 * A := by
    rw [hWA] at hgrad
    linarith only [hgrad, hCi_le]
  have hB20 : 0 ≤ ∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x) :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hLe0 : 0 ≤ Cs * L ^ (2 * ((d : ℝ) / sobStar d) + 2 - d) := by positivity
  have hVβ : (volume E).toReal ^ (1 - 2 / sobStar d) ≤ T ^ (1 - 2 / sobStar d) :=
    Real.rpow_le_rpow hV0 hVT hβ
  calc _ ≤ _ := hLHS
    _ ≤ _ := hsh
    _ ≤ Cs * L ^ (2 * ((d : ℝ) / sobStar d) + 2 - d) *
          (2 * (8 * d ^ 2 + 4) * ((Lam / lam) ^ 2 * (c / δ) ^ 2 * A +
            (1 / lam) ^ 2 * (Gb ^ 2 + L ^ 2 * Fb ^ 2) * T) + 2 * (c / δ) ^ 2 * A) *
          T ^ (1 - 2 / sobStar d) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hB2 hLe0) hVβ (by positivity) ?_
        exact mul_nonneg hLe0 ((hB20).trans hB2)

end SuperdiffusionCLT.Section7
