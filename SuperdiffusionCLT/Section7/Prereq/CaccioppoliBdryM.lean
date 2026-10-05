/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryL

/-!
# The sum over the good grid cubes

The per-cube bound `ca2_x_good` is summed over the good cubes with `ca1_sum_abstract`, using the
Harnack comparison `ca2_M_le`, the comparison with the weighted gradient of the larger cutoff
`ca2_e_le`, and the bounds `ca2_sum_sq_le` of the normalized sums of the squared norms.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_cs_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hF := hf.integrable_sq
  have hG := hg.integrable_sq
  have hI : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hquad : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) * t * t + (-2 * ∫ x, f x * g x ∂μ) * t +
      ∫ x, g x ^ 2 ∂μ := by
    intro t
    have h0 : 0 ≤ ∫ x, (t * f x - g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have e : ∫ x, (t * f x - g x) ^ 2 ∂μ =
        (∫ x, f x ^ 2 ∂μ) * t * t + (-2 * ∫ x, f x * g x ∂μ) * t + ∫ x, g x ^ 2 ∂μ := by
      have e1 : (fun x => (t * f x - g x) ^ 2) =
          fun x => (t * t) * f x ^ 2 + (-2 * t) * (f x * g x) + g x ^ 2 := by
        funext x; ring
      have hA : Integrable (fun x => (t * t) * f x ^ 2 + (-2 * t) * (f x * g x)) μ :=
        (hF.const_mul _).add (hI.const_mul _)
      have hB : Integrable (fun x => (t * t) * f x ^ 2) μ := hF.const_mul _
      have hC : Integrable (fun x => (-2 * t) * (f x * g x)) μ := hI.const_mul _
      rw [e1, integral_add hA hG, integral_add hB hC, integral_const_mul, integral_const_mul]
      ring
    nlinarith only [h0, e]
  have hd := discrim_le_zero (a := ∫ x, f x ^ 2 ∂μ) (b := -2 * ∫ x, f x * g x ∂μ)
    (c := ∫ x, g x ^ 2 ∂μ) (fun t => by have := hquad t; nlinarith only [this])
  unfold discrim at hd
  have hF0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [← Real.sqrt_mul hF0]
  refine Real.abs_le_sqrt ?_
  nlinarith only [hd]

theorem ca2_shift_sq {ι : Type*} (t : Finset ι) (N : ℝ) (hN : 0 < N) (hcard : (t.card : ℝ) ≤ N)
    (a : ι → ℝ) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hs : N⁻¹ * ∑ i ∈ t, a i ^ 2 ≤ A ^ 2) :
    N⁻¹ * ∑ i ∈ t, (a i + c) ^ 2 ≤ (A + c) ^ 2 := by
  have h1 : N⁻¹ * ∑ i ∈ t, a i * 1 ≤ A * 1 := by
    refine ca1_cs t N hN a (fun _ => 1) hA zero_le_one hs ?_
    simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [inv_mul_le_iff₀ hN]
    simpa using hcard
  simp only [mul_one] at h1
  have e : ∑ i ∈ t, (a i + c) ^ 2 = ∑ i ∈ t, a i ^ 2 + 2 * c * ∑ i ∈ t, a i + t.card * c ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [e, mul_add, mul_add]
  have h2 : N⁻¹ * (2 * c * ∑ i ∈ t, a i) = 2 * c * (N⁻¹ * ∑ i ∈ t, a i) := by ring
  have h3 : N⁻¹ * (t.card * c ^ 2) ≤ c ^ 2 := by
    have : N⁻¹ * (t.card * c ^ 2) = (N⁻¹ * t.card) * c ^ 2 := by ring
    rw [this]
    have h4 : N⁻¹ * t.card ≤ 1 := by rw [inv_mul_le_iff₀ hN]; simpa using hcard
    nlinarith only [h4, sq_nonneg c]
  rw [h2]
  nlinarith only [hs, h1, h3, hc, hA]

/-- The datum constant `g'` of the sum over the good cubes. -/
noncomputable def ca2_gp (d : ℕ) (a ℓ G1 G2 : ℝ) : ℝ :=
  a * (64 ^ d * (G1 + 2 * cubeBesovW12EmbeddingConstant d * ℓ * Real.sqrt d *
    (24 * a⁻¹ * G1 + G2))) / (12 * 64 ^ d)

theorem ca2_sum_good [NeZero d] (hd : 2 ≤ d) (m : ℤ) (h : ℕ) {W : Set (Vec d)} (hWo : IsOpen W)
    {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m) ∩ W) A)
    {S α1 β1 α2 β2 : ℝ} (hS : 0 ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function (openCubeSet (originCube d m) ∩ W)) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m) ∩ W)))
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m) ∩ W) u f (fun _ => 0))
    (hBB : ∀ R ∈ descendantsAtDepth (originCube d m) h, openCubeSet R ⊆ W →
      ∀ (u' : H1Function (openCubeSet (originCube d R.scale))) (f' : Vec d → ℝ),
      IsWeakSolutionOn (fun x => A (x + triadicCubeShift R)) (openCubeSet (originCube d R.scale)) u' f'
        (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) (fun x => matVecMul (A (x + triadicCubeShift R) - S • (1 : Mat d)) (u'.grad x))) ≤
        ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d R.scale)
          (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
            (ENNReal.ofReal (sobStar d)).conjExponent f')
    {a ac ℓ : ℝ} (ha : 0 < a) (hac0 : 0 < ac) (hℓ0 : 0 < ℓ)
    (hℓ : ∀ R ∈ descendantsAtDepth (originCube d m) h, cubeScaleFactor R = ℓ)
    (hac : a + ℓ ≤ 2 / 3 * ac) {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ) {G1 G2 : ℝ} (hG1 : 0 ≤ G1)
    (hG2 : 0 ≤ G2) (hb1 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1)
    (hb2 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) {Kη : ℝ≥0}
    (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i)) {G Gc Wn Fn : ℝ} (hG0 : 0 ≤ G)
    (hGc0 : 0 ≤ Gc) (hWn0 : 0 ≤ Wn) (hFn0 : 0 ≤ Fn)
    (hGs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤ G ^ 2)
    (hGcs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤ Gc ^ 2)
    (hWs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (u.toFun x - γ x) ^ 2 ≤ Wn ^ 2)
    (hFs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W, f x ^ 2 ≤ Fn ^ 2) :
    ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
        ∑ R ∈ ca2_Zi m h a W, |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x))| ≤
      (S * α2 + α1) * ((12 * 64 ^ d * 64 ^ d * a⁻¹ * G) * (Wn + ca2_gp d a ℓ G1 G2)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * α2 + α1) *
          ((12 * 64 ^ d * 64 ^ d * a⁻¹ * G) * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * α2 + α1) *
          ((((125 / 729 : ℝ) ^ d)⁻¹ * Gc) * (Wn + ca2_gp d a ℓ G1 G2)) +
        (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) * (Fn * (Wn + ca2_gp d a ℓ G1 G2)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) *
          (Fn * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη) * (S * β2 + β1) *
          (Fn * (Wn + ca2_gp d a ℓ G1 G2)) := by
  classical
  have hDm : MeasurableSet (openCubeSet (originCube d m) ∩ W) :=
    ((isOpen_openCubeSet _).inter hWo).measurableSet
  have hDQ : openCubeSet (originCube d m) ∩ W ⊆ openCubeSet (originCube d m) := Set.inter_subset_left
  have hN : 0 < ((descendantsAtDepth (originCube d m) h).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 (descendantsAtDepth_nonempty _ h))
  have hKb := cubeBesovW12EmbeddingConstant_nonneg d
  have hd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hK20 : 0 ≤ 2 * cubeBesovW12EmbeddingConstant d * ℓ := by positivity
  have hgp0 : 0 ≤ ca2_gp d a ℓ G1 G2 := by
    unfold ca2_gp
    positivity
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  -- membership in `L²(D)`
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by norm_num)
  have hwL : MemLp (fun x => u.toFun x - γ x) 2
      (volume.restrict (openCubeSet (originCube d m) ∩ W)) := by
    have hDb : Bornology.IsBounded (openCubeSet (originCube d m) ∩ W) :=
      (isBounded_openCubeSet (originCube d m)).subset hDQ
    exact u.memL2.sub (lip_witness_bdry_memLp_cont ((isOpen_openCubeSet _).inter hWo) hDb
      hγ1.continuous)
  have hgL : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2
      (volume.restrict (openCubeSet (originCube d m) ∩ W)) := memLp_eucNorm_grad u
  have hphiL : ∀ b : ℝ, MemLp (fun x => ca1_phi b x * Real.sqrt (vecNormSq (u.grad x))) 2
      (volume.restrict (openCubeSet (originCube d m) ∩ W)) := by
    intro b
    refine MemLp.of_le_mul (c := 1) hgL ((ca1_phi_continuous b).aestronglyMeasurable.mul
      hgL.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (ca1_phi_nonneg b x), one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ca1_phi_le_one b x)
  have hsq : ∀ {g : Vec d → ℝ}, MemLp g 2 (volume.restrict (openCubeSet (originCube d m) ∩ W)) →
      ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
        ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞) g ^ 2 ≤
      (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W, g x ^ 2 :=
    fun {g} hg => ca2_sum_sq_le m h a hWo hg
  have hifsq : ∀ F : TriadicCube d → ℝ, ∑ R ∈ descendantsAtDepth (originCube d m) h,
      (if ca2_good a W R then F R else 0) ^ 2 = ∑ R ∈ ca2_Zi m h a W, F R ^ 2 := by
    intro F
    unfold ca2_Zi
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun R _ => ?_
    by_cases hg : ca2_good a W R <;> simp [hg]
  have hKηnn : (0 : ℝ) ≤ Kη := NNReal.coe_nonneg _
  have key := ca1_sum_abstract (descendantsAtDepth (originCube d m) h) (ca2_Zi m h a W) ∅
    ((descendantsAtDepth (originCube d m) h).card : ℝ) hN (ca2_Zi_subset m h a W)
    (Finset.empty_subset _) (Finset.disjoint_empty_right _)
    (fun R => if ca2_good a W R then |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x))
      (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x))| else 0)
    (fun R => cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))))
    (fun R => if ca2_good a W R then cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x) +
      ca2_gp d a ℓ G1 G2 else 0)
    (fun R => if ca2_good a W R then
      cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f else 0)
    (fun R => if ca2_good a W R then 12 * 64 ^ d * 64 ^ d * a⁻¹ * cubeLpNorm R (2 : ℝ≥0∞)
      (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) else 0)
    (fun R => 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R))
    (α := S * α2 + α1) (β := S * β2 + β1) (Mb := 12 * 64 ^ d * a⁻¹)
    (K2 := 2 * cubeBesovW12EmbeddingConstant d * ℓ) (Kd := Real.sqrt d * Kη) (ε := 0)
    (Wg := Wn + ca2_gp d a ℓ G1 G2) (Fg := Fn) (Pg := 12 * 64 ^ d * 64 ^ d * a⁻¹ * G)
    (Eg := ((125 / 729 : ℝ) ^ d)⁻¹ * Gc)
    (by positivity) (by positivity) (by positivity) hK20 (by positivity) le_rfl (by positivity)
    hFn0 (by positivity) (by positivity)
    (fun R => by
      by_cases hg : ca2_good a W R
      · simp only [hg, ite_true]; exact abs_nonneg _
      · simp [hg])
    (fun R hR hRZ _ => by
      have : ¬ ca2_good a W R := fun hg => hRZ (by unfold ca2_Zi; exact Finset.mem_filter.2 ⟨hR, hg⟩)
      simp [this])
    (fun R => cubeLpNorm_nonneg _ _ _)
    (fun R => by
      by_cases hg : ca2_good a W R
      · simp only [hg, ite_true]; exact add_nonneg (cubeLpNorm_nonneg _ _ _) hgp0
      · simp [hg])
    (fun R => by
      by_cases hg : ca2_good a W R
      · simp only [hg, ite_true]; exact cubeLpNorm_nonneg _ _ _
      · simp [hg])
    (fun R => by
      by_cases hg : ca2_good a W R
      · simp only [hg, ite_true]
        have := cubeLpNorm_nonneg R (2 : ℝ≥0∞) (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))
        positivity
      · simp [hg])
    ?_ ?_ (fun R hR => by simp at hR) ?_ ?_ ?_ ?_
  rotate_left
  · -- the per-cube bound
    intro R hR
    have hR' := Finset.mem_filter.1 hR
    have hRs := hR'.1
    have hg : ca2_good a W R := hR'.2
    have hRD := ca2_good_openCube_subset m h hR
    simp only [hg, ite_true]
    have hf2 : MemLp f 2 (normalizedCubeMeasure R) :=
      ca1_memLp_of_restrict R (hf.mono_measure (Measure.restrict_mono hRD le_rfl))
    have hfin : SuperdiffusionCLT.Section2.Norms.cubeLpENorm R
        (ENNReal.ofReal (sobStar d)).conjExponent f ≠ ⊤ :=
      (hf2.mono_exponent (ca1_conj_le_two hd)).eLpNorm_ne_top
    have hx := ca2_x_good R hRD hEll hS hα1 hβ1 hα2 hβ2 u hf2 hfin hu
      (fun u' f' hsol => hBB R hRs hg.2 u' f' hsol) ha hg.1 hγ hG1 hG2
      (fun x hx => hb1 x (hRD hx)) (fun x hx => hb2 x (hRD hx)) hKη
    rw [hℓ R hRs] at hx
    refine hx.trans ?_
    set e := cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) with he
    set F := cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f with hF
    set Wu := cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - γ x) with hWu
    have he0 : 0 ≤ e := cubeLpNorm_nonneg _ _ _
    have hF0 : 0 ≤ F := cubeLpNorm_nonneg _ _ _
    have hWu0 : 0 ≤ Wu := cubeLpNorm_nonneg _ _ _
    have hφ0 := ca1_phi_nonneg a (triadicCubeShift R)
    have e1 : (S * (α2 * e + β2 * F) + (α1 * e + β1 * F)) = (S * α2 + α1) * e + (S * β2 + β1) * F := by ring
    rw [e1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hMg : 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) * ca2_gp d a ℓ G1 G2 =
        ca1_phi a (triadicCubeShift R) * (64 ^ d * (G1 + 2 * cubeBesovW12EmbeddingConstant d * ℓ *
          Real.sqrt d * (24 * a⁻¹ * G1 + G2))) := by
      unfold ca2_gp
      field_simp
    have hKK : 0 ≤ 2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * Kη * ca2_gp d a ℓ G1 G2) := by
      positivity
    nlinarith only [hMg, hKK]
  · -- the Harnack comparison
    intro R hR
    have hR' := Finset.mem_filter.1 hR
    have hg : ca2_good a W R := hR'.2
    have hRD := ca2_good_openCube_subset m h hR
    simp only [hg, ite_true]
    have hφ0 := ca1_phi_nonneg a (triadicCubeShift R)
    refine ⟨by positivity, ?_, ?_⟩
    · exact mul_le_of_le_one_right (by positivity) (ca1_phi_le_one a _)
    · exact ca2_M_le u ha hRD hg.1
  · -- the weight norm
    rw [hifsq]
    refine ca2_shift_sq _ _ hN (Nat.cast_le.2 (Finset.card_le_card (ca2_Zi_subset m h a W))) _ hWn0 hgp0 ?_
    refine (hsq hwL).trans hWs
  · -- the right-hand side
    rw [hifsq]
    have hfR : ∀ R ∈ ca2_Zi m h a W, MemLp f 2 (normalizedCubeMeasure R) := fun R hR =>
      ca1_memLp_of_restrict R (hf.mono_measure (Measure.restrict_mono (ca2_good_openCube_subset m h hR) le_rfl))
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR =>
      pow_le_pow_left₀ ENNReal.toReal_nonneg
        (ca1_cubeLpNorm_mono_exp R (ca1_conj_le_two hd) (hfR R hR)) 2)
      (inv_nonneg.2 hN.le)) ?_
    exact (hsq hf).trans hFs
  · -- the weighted gradient
    rw [hifsq]
    have e : ∀ R : TriadicCube d, (12 * 64 ^ d * 64 ^ d * a⁻¹ * cubeLpNorm R (2 : ℝ≥0∞)
        (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))) ^ 2 =
        (12 * 64 ^ d * 64 ^ d * a⁻¹) ^ 2 * cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 := fun R => by ring
    simp only [e, ← Finset.mul_sum]
    have := hsq (hphiL a)
    have h2 := hGs
    rw [mul_pow (12 * 64 ^ d * 64 ^ d * a⁻¹) G]
    calc ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
          ((12 * 64 ^ d * 64 ^ d * a⁻¹) ^ 2 * ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2)
        = (12 * 64 ^ d * 64 ^ d * a⁻¹) ^ 2 * (((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
          ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞)
            (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (this.trans h2) (sq_nonneg _)
  · -- the gradient on the good cubes
    simp only [Finset.union_empty]
    have hbound : ∀ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ≤
        ((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) := by
      intro R hR
      have hR' := Finset.mem_filter.1 hR
      have hg : ca2_good a W R := hR'.2
      have hnear : ∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2 := by
        intro k
        have := hg.1 k
        have hℓR : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
        linarith only [this, hℓR]
      exact ca2_e_le u (ca2_good_openCube_subset m h hR)
        (ca1_near_cube R hnear (by rw [hℓ R hR'.1]; exact hac)) hac0
    have hsum : ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
        ((((125 / 729 : ℝ) ^ d)⁻¹) ^ 2) * ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun R hR => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (cubeLpNorm_nonneg _ _ _) (hbound R hR) 2
    have h3 := hsq (hphiL ac)
    rw [mul_pow]
    calc ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ * ∑ R ∈ ca2_Zi m h a W,
          cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2
        ≤ ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
          ((((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hN.le)
      _ = (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * (((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
          ∑ R ∈ ca2_Zi m h a W, cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h3.trans hGcs) (sq_nonneg _)
  · -- the conversion
    have hx0 : (∑ R ∈ descendantsAtDepth (originCube d m) h, (if ca2_good a W R then
        |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x))| else 0)) =
        ∑ R ∈ ca2_Zi m h a W, |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x))
          (ca2_G (ca1_Phi a) γ (fun y => u.toFun y - γ y) x))| := by
      unfold ca2_Zi
      rw [Finset.sum_filter]
    have := key
    simp only [hx0, zero_mul, add_zero] at this
    exact this

end SuperdiffusionCLT.Section7
