/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliC

/-!
# The interior superdiffusive Caccioppoli inequality, deterministic core (step 4)

The sum over the grid of cubes `z + □_n` of the weak test of `CaccioppoliC`, for the test field
`(u - c) ∇Φ_a` with the polynomial cutoff of `CaccioppoliB`.  The grid cubes are
the descendants of the origin cube `□_m` at depth `h = m - n`; they split into the interior cubes
(Harnack inequality for the cutoff, weak test), the layer cubes (the derivative of the cutoff is
smaller than `(3^{n-m})^5 / a`, no weak test needed) and the far cubes (the cutoff vanishes).

## Main results

* `Section7.ca1_crude_norm`: the crude (unsigned) Caccioppoli inequality in normalized form.
* `Section7.ca1_identity_norm`: the energy identity in normalized form.
* `Section7.ca1_main`: `ν ‖φ_a ∇u‖² ≤ ‖f‖‖u - c‖ + (the seven weak-test terms)`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}


theorem ca1_T_aesm [NeZero d] (m : ℤ) {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A)
    (u : H1Function (openCubeSet (originCube d m))) {a : ℝ} (ha : 0 < a) (c : ℝ)
    {R : TriadicCube d} (hRQ : openCubeSet R ⊆ openCubeSet (originCube d m)) :
    AEStronglyMeasurable (ca1_T A u.toFun u.grad c a) (normalizedCubeMeasure R) := by
  have h1 := (ca1_integrable_cross m hEll u ha c).aestronglyMeasurable
  rw [normalizedCubeMeasure_eq_smul]
  refine AEStronglyMeasurable.smul_measure ?_ _
  exact h1.mono_measure (Measure.restrict_mono hRQ le_rfl)

theorem ca1_T_zero {a : ℝ} (A : CoeffField d) (u : Vec d → ℝ) (g : Vec d → Vec d) (c : ℝ) {x : Vec d}
    (hE : ∀ i, ca1_E a i x = 0) : ca1_T A u g c a x = 0 := by
  simp [ca1_T, hE, vecDot]

/-- Pointwise bound of the cross term where the cutoff derivative is small. -/
theorem ca1_T_abs_le {a Λ ε₀ : ℝ} (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε₀) (A : CoeffField d) (u : Vec d → ℝ)
    (g : Vec d → Vec d) (c : ℝ) {x : Vec d}
    (hop : ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (hE : ∀ i, |ca1_E a i x| ≤ ε₀) :
    |ca1_T A u g c a x| ≤ (Λ * (Real.sqrt d * ε₀)) * (Real.sqrt (vecNormSq (g x)) * |u x - c|) := by
  unfold ca1_T
  refine (ca1_abs_vecDot_le _ _).trans ?_
  have h1 := hop (g x)
  have h2 : eucNorm (fun i => (u x - c) * ca1_E a i x) ≤ Real.sqrt d * (|u x - c| * ε₀) := by
    refine ca1_eucNorm_le_of_abs_le (by positivity) fun i => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hE i) (abs_nonneg _)
  have h3 : eucNorm (g x) = Real.sqrt (vecNormSq (g x)) := rfl
  rw [h3] at h1
  calc eucNorm (matVecMul (A x) (g x)) * eucNorm (fun i => (u x - c) * ca1_E a i x)
      ≤ (Λ * Real.sqrt (vecNormSq (g x))) * (Real.sqrt d * (|u x - c| * ε₀)) :=
        mul_le_mul h1 h2 (ca1_eucNorm_nonneg _) (by positivity)
    _ = _ := by ring

theorem ca1_ae_openR (R : TriadicCube d) {P : Vec d → Prop}
    (h : ∀ x ∈ openCubeSet R, P x) : ∀ᵐ x ∂(normalizedCubeMeasure R), P x :=
  r1_ae_normalized _ ((ae_restrict_iff' (isOpen_openCubeSet R).measurableSet).2
    (Filter.Eventually.of_forall h))

theorem ca1_avg_far {A : CoeffField d} {W : Set (Vec d)} (u : H1Function W) {a : ℝ} (c : ℝ)
    {R : TriadicCube d}
    (hfar : ∀ x ∈ openCubeSet R, ∀ i, ca1_E a i x = 0) :
    cubeAverage R (ca1_T A u.toFun u.grad c a) = 0 := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ca1_ae_openR R (P := fun x => ca1_T A u.toFun u.grad c a x = 0)
    (fun x hx => ca1_T_zero A u.toFun u.grad c (hfar x hx))] with x hx
  exact hx

theorem ca1_avg_bdry [NeZero d] (m : ℤ) {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hop : ∀ x ∈ openCubeSet (originCube d m), ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (u : H1Function (openCubeSet (originCube d m))) {a : ℝ} (ha : 0 < a) (c : ℝ)
    {R : TriadicCube d} (hRQ : openCubeSet R ⊆ openCubeSet (originCube d m)) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (hlayer : ∀ x ∈ openCubeSet R, ∀ i, |ca1_E a i x| ≤ ε₀) :
    |cubeAverage R (ca1_T A u.toFun u.grad c a)| ≤ (Λ * (Real.sqrt d * ε₀)) *
      (cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c)) := by
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRQ
  have hG : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have hW : MemLp (fun x => u.toFun x - c) 2 (normalizedCubeMeasure R) :=
    ur.memL2_normalizedCubeMeasure.sub (memLp_const c)
  have h1 := ca1_avg_le_of_bound R (ca1_T_aesm m hEll u ha c hRQ) hG hW.norm
    (C := Λ * (Real.sqrt d * ε₀)) (by positivity)
    (ca1_ae_openR R fun x hx => by
      have := ca1_T_abs_le (a := a) hΛ hε₀ A u.toFun u.grad c (x := x) (hop x (hRQ hx)) (hlayer x hx)
      simpa [Real.norm_eq_abs] using this)
  have h3 : cubeLpNorm R (2 : ℝ≥0∞) (fun x => ‖u.toFun x - c‖) =
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c) := by
    unfold cubeLpNorm
    exact congrArg ENNReal.toReal (eLpNorm_norm (fun x => u.toFun x - c) hW.aestronglyMeasurable)
  rw [h3] at h1
  exact h1

theorem ca1_x_int [NeZero d] (m : ℤ) (R : TriadicCube d)
    (hRQ : openCubeSet R ⊆ openCubeSet (originCube d m)) {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A)
    {S α1 β1 α2 β2 : ℝ} (hS : 0 ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function (openCubeSet (originCube d m))) {f : Vec d → ℝ}
    (hf2 : MemLp f 2 (normalizedCubeMeasure R))
    (hfin : SuperdiffusionCLT.Section2.Norms.cubeLpENorm R
      (ENNReal.ofReal (sobStar d)).conjExponent f ≠ ⊤)
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (fun _ => 0))
    (hBB : ∀ (u' : H1Function (openCubeSet (originCube d R.scale))) (f' : Vec d → ℝ),
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
    (c : ℝ) {a : ℝ} (ha : 0 < a) {Kη : ℝ≥0} (hKη : ∀ i, LipschitzWith Kη (ca1_E (d := d) a i))
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) :
    |cubeAverage R (ca1_T A u.toFun u.grad c a)| ≤
      ((S * α2 + α1) * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          (S * β2 + β1) * cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f) *
        (12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) * cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c) +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R *
            (12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
                cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
              Real.sqrt d * Kη * cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c))) := by
  have hM0 : 0 ≤ 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) := by
    have := ca1_phi_nonneg a (triadicCubeShift R)
    positivity
  have hmem : ∀ x ∈ openCubeSet (originCube d R.scale), x + triadicCubeShift R ∈ openCubeSet R := by
    intro x hx
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, mem_translateSet_iff_sub_mem]
    simpa using hx
  have key := ca1_cube_ambient m R hRQ hEll hS hα1 hβ1 hα2 hβ2 u hf2 hfin hu hBB c ha hKη hM0
    (fun x hx i => ca1_harnack_cube ha R hint _ (hmem x hx) i)
  refine key.trans (le_of_eq ?_)
  ring





/-- On an interior grid cube the weighted quantity `M e` is controlled by the weighted energy. -/
theorem ca1_M_le [NeZero d] (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) {a : ℝ} (ha : 0 < a)
    {R : TriadicCube d} (hRQ : openCubeSet R ⊆ openCubeSet (originCube d m))
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) :
    12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ≤
      12 * 64 ^ d * 64 ^ d * a⁻¹ *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) := by
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRQ
  have hG : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have hGφ := ca1_memLp_phi_mul R a hG
  have hℓ : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
  have hpt : ∀ x ∈ openCubeSet R, ca1_phi a (triadicCubeShift R) ≤ 64 ^ d * ca1_phi a x := by
    intro x hx
    refine ca1_phi_harnack (a := a) (η := cubeScaleFactor R) ha hℓ.le (x := x) (y := triadicCubeShift R)
      (fun k => ?_) (fun k => ?_)
    · have := ca1_abs_le_center R hx k
      linarith only [this, hint k, hℓ]
    · have := (ca1_mem_openCube_iff R x).1 hx k
      rw [abs_sub_comm] at this
      exact this.le.trans (by linarith only [hℓ])
  have h1 := ca1_cubeLpNorm_le R (F := fun x => ca1_phi a (triadicCubeShift R) * Real.sqrt (vecNormSq (u.grad x)))
    (G := fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))
    ((hG.const_mul _).aestronglyMeasurable) hGφ (M := 64 ^ d) (by positivity)
    (ca1_ae_openR R fun x hx => by
      rw [abs_mul, abs_mul, abs_of_nonneg (ca1_phi_nonneg a _), abs_of_nonneg (ca1_phi_nonneg a x)]
      have := hpt x hx
      have h0 : 0 ≤ |Real.sqrt (vecNormSq (u.grad x))| := abs_nonneg _
      calc ca1_phi a (triadicCubeShift R) * |Real.sqrt (vecNormSq (u.grad x))|
          ≤ (64 ^ d * ca1_phi a x) * |Real.sqrt (vecNormSq (u.grad x))| :=
            mul_le_mul_of_nonneg_right this h0
        _ = _ := by ring)
  rw [cubeLpNorm_const_mul, Real.norm_of_nonneg (ca1_phi_nonneg a _)] at h1
  have h12 : 0 ≤ 12 * 64 ^ d * a⁻¹ := by positivity
  calc 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x)))
      = 12 * 64 ^ d * a⁻¹ * (ca1_phi a (triadicCubeShift R) * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x)))) := by ring
    _ ≤ 12 * 64 ^ d * a⁻¹ * (64 ^ d * cubeLpNorm R (2 : ℝ≥0∞) (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))) :=
        mul_le_mul_of_nonneg_left h1 h12
    _ = _ := by ring

/-- Near the support of the cutoff the gradient is controlled by the weighted gradient of the larger
cutoff. -/
theorem ca1_e_le [NeZero d] (m : ℤ) (u : H1Function (openCubeSet (originCube d m)))
    {R : TriadicCube d} (hRQ : openCubeSet R ⊆ openCubeSet (originCube d m)) {ac : ℝ}
    (hlow : ∀ x ∈ openCubeSet R, ∀ k, |x k| ≤ 2 / 3 * ac) (hac : 0 < ac) :
    cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ≤
      ((125 / 729 : ℝ) ^ d)⁻¹ *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) := by
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRQ
  have hG : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have hGφ := ca1_memLp_phi_mul R ac hG
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have h1 := ca1_cubeLpNorm_le R (F := fun x => Real.sqrt (vecNormSq (u.grad x)))
    (G := fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) hG.aestronglyMeasurable hGφ
    (M := ((125 / 729 : ℝ) ^ d)⁻¹) (by positivity)
    (ca1_ae_openR R fun x hx => by
      have hl := ca1_phi_lower hac (hlow x hx)
      have h0 : 0 ≤ Real.sqrt (vecNormSq (u.grad x)) := Real.sqrt_nonneg _
      rw [abs_of_nonneg h0, abs_mul, abs_of_nonneg (ca1_phi_nonneg ac x), abs_of_nonneg h0]
      have h2 : 1 ≤ ((125 / 729 : ℝ) ^ d)⁻¹ * ca1_phi ac x := by
        rw [← div_eq_inv_mul, le_div_iff₀ hc0]; linarith only [hl]
      calc Real.sqrt (vecNormSq (u.grad x)) = 1 * Real.sqrt (vecNormSq (u.grad x)) := (one_mul _).symm
        _ ≤ (((125 / 729 : ℝ) ^ d)⁻¹ * ca1_phi ac x) * Real.sqrt (vecNormSq (u.grad x)) :=
            mul_le_mul_of_nonneg_right h2 h0
        _ = _ := by ring)
  exact h1

theorem ca1_main [NeZero d] (hd : 2 ≤ d) (m : ℤ) (h : ℕ) {lam Lam ν Λ S α1 β1 α2 β2 : ℝ}
    {A : CoeffField d} (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A)
    (hΛ : 0 ≤ Λ)
    (hsym : ∀ x ∈ openCubeSet (originCube d m), symmPart (A x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d m), ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (hS : 0 ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function (openCubeSet (originCube d m))) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))))
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (fun _ => 0))
    (hBB : ∀ R ∈ descendantsAtDepth (originCube d m) h,
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
    (c : ℝ) {a ac ℓ : ℝ} (ha : 0 < a) (hat : a < 3 ^ m / 2) (hℓ0 : 0 < ℓ)
    (hℓ : ∀ R ∈ descendantsAtDepth (originCube d m) h, cubeScaleFactor R = ℓ)
    (hℓa : 4 * ℓ ≤ a) (hac : a + ℓ ≤ 2 / 3 * ac) :
    ν * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
        (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
      cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f * cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c) +
      ((S * α2 + α1) * (12 * 64 ^ d * 64 ^ d * a⁻¹ * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
            (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))) *
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * α2 + α1) *
          ((12 * 64 ^ d * 64 ^ d * a⁻¹ * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))) *
            (((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))))) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * ((ca1_K0 d * Real.toNNReal a⁻¹ ^ 2 : ℝ≥0) : ℝ)) *
          (S * α2 + α1) *
          (((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c)) +
        (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) *
          (cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) *
          (cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f *
            (((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))))) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * ((ca1_K0 d * Real.toNNReal a⁻¹ ^ 2 : ℝ≥0) : ℝ)) *
          (S * β2 + β1) *
          (cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c)) +
        (Λ * (Real.sqrt d * (12 * a⁻¹ * (4 * ℓ / a) ^ 5))) *
          (((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c))) := by
  classical
  obtain ⟨W, hW⟩ : ∃ W, W = cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c) := ⟨_, rfl⟩
  obtain ⟨Fg, hFg⟩ : ∃ Fg, Fg = cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
    (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) := ⟨_, rfl⟩
  obtain ⟨Gc, hGc⟩ : ∃ Gc, Gc = cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
    (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) := ⟨_, rfl⟩
  rw [← hW, ← hFg, ← hG, ← hGc]
  have hfm : MemLp f 2 (normalizedCubeMeasure (originCube d m)) := ca1_memLp_of_restrict _ hf
  have hwm : MemLp (fun x => u.toFun x - c) 2 (normalizedCubeMeasure (originCube d m)) :=
    u.memL2_normalizedCubeMeasure.sub (memLp_const c)
  have hGm : MemLp (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) 2
      (normalizedCubeMeasure (originCube d m)) := ca1_memLp_phi_mul _ a (r1_memLp_grad_eucNorm _ u)
  have hW0 : 0 ≤ W := by rw [hW]; exact ENNReal.toReal_nonneg
  have hF0 : 0 ≤ Fg := by rw [hFg]; exact ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := by rw [hG]; exact ENNReal.toReal_nonneg
  have hGc0 : 0 ≤ Gc := by rw [hGc]; exact ENNReal.toReal_nonneg
  have hAT : |cubeAverage (originCube d m) (ca1_T A u.toFun u.grad c a)| ≤
      ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth (originCube d m) h,
        |cubeAverage R (ca1_T A u.toFun u.grad c a)| := by
    have hint : IntegrableOn (ca1_T A u.toFun u.grad c a) (cubeSet (originCube d m)) volume :=
      ca1_integrableOn_cubeSet (ca1_integrable_cross m hEll u ha c)
    rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn (originCube d m) h
      (ca1_T A u.toFun u.grad c a) hint]
    show |((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth (originCube d m) h,
        cubeAverage R (ca1_T A u.toFun u.grad c a)| ≤ _
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.2 (Nat.cast_nonneg _))
  have hAf : |cubeAverage (originCube d m) (fun x => f x * (ca1_Phi a x * (u.toFun x - c)))| ≤ Fg * W := by
    have hΦw : MemLp (fun x => ca1_Phi a x * (u.toFun x - c)) 2 (normalizedCubeMeasure (originCube d m)) := by
      refine MemLp.of_le_mul (c := 1) hwm ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact ((ca1_Phi1_contDiff.continuous.comp (continuous_const_smul a⁻¹)).aestronglyMeasurable.mul
          hwm.aestronglyMeasurable)
      · rw [norm_mul, one_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact ca1_Phi_abs_le a x)
    have h1 := ca1_avg_mul_le (originCube d m) hfm hΦw
    have h2 : cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => ca1_Phi a x * (u.toFun x - c)) ≤
        1 * cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c) := by
      refine ca1_cubeLpNorm_le _ hΦw.aestronglyMeasurable hwm zero_le_one
        (Filter.Eventually.of_forall fun x => ?_)
      rw [abs_mul, one_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (ca1_Phi_abs_le a x)
    rw [← hW, ← hFg] at *
    have h3 := mul_le_mul_of_nonneg_left h2 hF0
    rw [hFg, hW] at *
    linarith only [h1, h3]
  have hid := ca1_identity_norm m hEll hsym u hu ha hat c
  have hG2 : G ^ 2 = cubeAverage (originCube d m) (fun x => ca1_Phi a x * vecNormSq (u.grad x)) := by
    rw [hG, ca1_cubeLpNorm_sq _ hGm]
    refine congrArg _ (funext fun x => ?_)
    rw [mul_pow, Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _),
      ← ca1_Phi_eq]
  have hsum : ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth (originCube d m) h,
        |cubeAverage R (ca1_T A u.toFun u.grad c a)| ≤
      (S * α2 + α1) * ((12 * 64 ^ d * 64 ^ d * a⁻¹ * G) * W) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * α2 + α1) *
          ((12 * 64 ^ d * 64 ^ d * a⁻¹ * G) * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * ((ca1_K0 d * Real.toNNReal a⁻¹ ^ 2 : ℝ≥0) : ℝ)) *
          (S * α2 + α1) * ((((125 / 729 : ℝ) ^ d)⁻¹ * Gc) * W) +
        (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) * (Fg * W) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (S * β2 + β1) * (12 * 64 ^ d * a⁻¹) *
          (Fg * (((125 / 729 : ℝ) ^ d)⁻¹ * Gc)) +
        2 * cubeBesovW12EmbeddingConstant d * ℓ * (Real.sqrt d * ((ca1_K0 d * Real.toNNReal a⁻¹ ^ 2 : ℝ≥0) : ℝ)) *
          (S * β2 + β1) * (Fg * W) +
        (Λ * (Real.sqrt d * (12 * a⁻¹ * (4 * ℓ / a) ^ 5))) * ((((125 / 729 : ℝ) ^ d)⁻¹ * Gc) * W) := by
    have hdesc : ∀ R ∈ descendantsAtDepth (originCube d m) h,
        openCubeSet R ⊆ openCubeSet (originCube d m) :=
      fun R hR => openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hfR : ∀ R ∈ descendantsAtDepth (originCube d m) h, MemLp f 2 (normalizedCubeMeasure R) :=
      fun R hR => memLp_on_descendant_of_memLp hR hfm
    have hKη := (ca1_K0_spec d a ha).2
    have hKe : 0 ≤ cubeBesovW12EmbeddingConstant d := cubeBesovW12EmbeddingConstant_nonneg d
    have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
    refine ca1_sum_abstract (descendantsAtDepth (originCube d m) h)
      ((descendantsAtDepth (originCube d m) h).filter fun R => ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a)
      ((descendantsAtDepth (originCube d m) h).filter fun R =>
        (∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2) ∧
          ¬ ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a)
      ((descendantsAtDepth (originCube d m) h).card : ℝ)
      (by exact_mod_cast Finset.card_pos.2 (descendantsAtDepth_nonempty (originCube d m) h))
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) ?_
      (fun R => |cubeAverage R (ca1_T A u.toFun u.grad c a)|)
      (fun R => cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))))
      (fun R => cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c))
      (fun R => cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f)
      (fun R => 12 * 64 ^ d * 64 ^ d * a⁻¹ *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))))
      (fun R => 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R))
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) hW0 hF0 (by have := hG0; positivity) (by have := hGc0; positivity)
      (fun R => abs_nonneg _) ?_ (fun R => ENNReal.toReal_nonneg) (fun R => ENNReal.toReal_nonneg)
      (fun R => ENNReal.toReal_nonneg) (fun R => by have := ENNReal.toReal_nonneg (a := eLpNorm (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R)); unfold cubeLpNorm; positivity)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Finset.disjoint_filter.2 fun R _ h1 h2 => h2.2 h1
    · intro R hR hRi hRb
      have hnear : ¬ ∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2 := by
        intro hn
        by_cases hi : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a
        · exact hRi (Finset.mem_filter.2 ⟨hR, hi⟩)
        · exact hRb (Finset.mem_filter.2 ⟨hR, hn, hi⟩)
      have := ca1_avg_far (A := A) u c (ca1_far_cube ha R hnear)
      show |cubeAverage R (ca1_T A u.toFun u.grad c a)| ≤ 0
      rw [this]; simp
    · intro R hR
      obtain ⟨hRs, hI⟩ := Finset.mem_filter.1 hR
      have hfin : SuperdiffusionCLT.Section2.Norms.cubeLpENorm R
          (ENNReal.ofReal (sobStar d)).conjExponent f ≠ ⊤ :=
        ((hfR R hRs).mono_exponent (ca1_conj_le_two hd)).eLpNorm_ne_top
      have key := ca1_x_int m R (hdesc R hRs) hEll hS hα1 hβ1 hα2 hβ2 u (hfR R hRs) hfin hu
        (hBB R hRs) c ha hKη hI
      rw [hℓ R hRs] at key
      exact key
    · intro R hR
      obtain ⟨hRs, hI⟩ := Finset.mem_filter.1 hR
      refine ⟨by have := ca1_phi_nonneg a (triadicCubeShift R); positivity, ?_, ca1_M_le m u ha (hdesc R hRs) hI⟩
      have h12 : 0 ≤ 12 * 64 ^ d * a⁻¹ := by positivity
      exact mul_le_of_le_one_right h12 (ca1_phi_le_one a _)
    · intro R hR
      obtain ⟨hRs, hn, hnI⟩ := Finset.mem_filter.1 hR
      have hl : 4 * cubeScaleFactor R ≤ a := by rw [hℓ R hRs]; exact hℓa
      have hlayer := ca1_layer_cube ha R hl hnI
      rw [hℓ R hRs] at hlayer
      have := ca1_avg_bdry m hEll hΛ hop u ha c (hdesc R hRs)
        (ε₀ := 12 * a⁻¹ * (4 * ℓ / a) ^ 5) (by positivity) hlayer
      exact this
    · rw [hW]
      exact (ca1_desc_sq (originCube d m) hwm h).le
    · rw [hFg]
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => ?_)
        (inv_nonneg.2 (Nat.cast_nonneg _))) (ca1_desc_sq (originCube d m) hfm h).le
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg
        (ca1_cubeLpNorm_mono_exp R (ca1_conj_le_two hd) (hfR R hR)) 2
    · rw [hG]
      refine le_of_eq ?_
      have h1 := ca1_desc_sq (originCube d m) hGm h
      have h2 : ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d m) h,
            (12 * 64 ^ d * 64 ^ d * a⁻¹ * cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))) ^ 2 =
          (12 * 64 ^ d * 64 ^ d * a⁻¹) ^ 2 * (((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d m) h, cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2) := by
        simp only [mul_pow, ← Finset.mul_sum]
        ring
      rw [h2]
      have h3 : ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d m) h, cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 =
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 := h1
      rw [h3]
      ring
    · rw [hGc]
      have hacpos : 0 < ac := by linarith only [hac, ha, hℓ0]
      have hZmem : ∀ R ∈ (descendantsAtDepth (originCube d m) h).filter
          (fun R => ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) ∪
          (descendantsAtDepth (originCube d m) h).filter (fun R =>
            (∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2) ∧
              ¬ ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a),
          R ∈ descendantsAtDepth (originCube d m) h ∧ ∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2 := by
        intro R hR
        rcases Finset.mem_union.1 hR with hR | hR
        · obtain ⟨hRs, hI⟩ := Finset.mem_filter.1 hR
          exact ⟨hRs, fun k => by have := hI k; have := cubeScaleFactor_pos' R; linarith only [‹_ ≤ a›, this]⟩
        · obtain ⟨hRs, hn, _⟩ := Finset.mem_filter.1 hR
          exact ⟨hRs, hn⟩
      have hbound : ∀ R ∈ (descendantsAtDepth (originCube d m) h).filter
          (fun R => ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) ∪
          (descendantsAtDepth (originCube d m) h).filter (fun R =>
            (∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2) ∧
              ¬ ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a),
          cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ≤
            ((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) := by
        intro R hR
        obtain ⟨hRs, hn⟩ := hZmem R hR
        exact ca1_e_le m u (hdesc R hRs) (ca1_near_cube R hn (by rw [hℓ R hRs]; exact hac)) hacpos
      refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR =>
        pow_le_pow_left₀ ENNReal.toReal_nonneg (hbound R hR) 2) (inv_nonneg.2 (Nat.cast_nonneg _))) ?_
      have hGcm : MemLp (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) 2
          (normalizedCubeMeasure (originCube d m)) := ca1_memLp_phi_mul _ ac (r1_memLp_grad_eucNorm _ u)
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (s := (descendantsAtDepth (originCube d m) h).filter
          (fun R => ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) ∪
          (descendantsAtDepth (originCube d m) h).filter (fun R =>
            (∀ k, |triadicCubeShift R k| ≤ a + cubeScaleFactor R / 2) ∧
              ¬ ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a))
        (t := descendantsAtDepth (originCube d m) h)
        (f := fun R => (((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x)))) ^ 2)
        (fun R hR => (hZmem R hR).1) (fun _ _ _ => sq_nonneg _)
      refine (mul_le_mul_of_nonneg_left hsub (inv_nonneg.2 (Nat.cast_nonneg _))).trans (le_of_eq ?_)
      have h1 := ca1_desc_sq (originCube d m) hGcm h
      have h2 : ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d m) h, (((125 / 729 : ℝ) ^ d)⁻¹ * cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x)))) ^ 2 =
          (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * (((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d m) h, cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2) := by
        simp only [mul_pow, ← Finset.mul_sum]
        ring
      rw [h2]
      have h3 : ((descendantsAtDepth (originCube d m) h).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d m) h, cubeLpNorm R (2 : ℝ≥0∞)
              (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 =
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 := h1
      rw [h3]
      ring
  have hν' : ν * G ^ 2 = cubeAverage (originCube d m) (fun x => f x * (ca1_Phi a x * (u.toFun x - c))) -
      cubeAverage (originCube d m) (ca1_T A u.toFun u.grad c a) := by rw [hG2]; exact hid
  have h1 := abs_sub_abs_le_abs_sub (cubeAverage (originCube d m) (fun x => f x * (ca1_Phi a x * (u.toFun x - c))))
    (cubeAverage (originCube d m) (ca1_T A u.toFun u.grad c a))
  have h2 : cubeAverage (originCube d m) (fun x => f x * (ca1_Phi a x * (u.toFun x - c))) -
      cubeAverage (originCube d m) (ca1_T A u.toFun u.grad c a) ≤
      |cubeAverage (originCube d m) (fun x => f x * (ca1_Phi a x * (u.toFun x - c)))| +
        |cubeAverage (originCube d m) (ca1_T A u.toFun u.grad c a)| := by
    have := abs_sub (cubeAverage (originCube d m) (fun x => f x * (ca1_Phi a x * (u.toFun x - c))))
      (cubeAverage (originCube d m) (ca1_T A u.toFun u.grad c a))
    exact (le_abs_self _).trans this
  linarith only [hν', h2, hAf, hAT, hsum]

theorem ca1_openCube_pred_subset (m : ℤ) :
    openCubeSet (originCube d (m - 1)) ⊆ openCubeSet (originCube d m) := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro k
  obtain ⟨h1, h2⟩ := hx k
  have h3 : (3 : ℝ) ^ (m - 1) ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) (by omega)
  constructor <;> nlinarith only [h1, h2, h3]

/-- The gradient on the middle child is controlled by the weighted gradient on the parent. -/
theorem ca1_inner_le [NeZero d] (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) :
    cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
      3 ^ d * (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
        (fun x => ca1_phi (3 ^ m / 4) x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 := by
  have hsub := ca1_openCube_pred_subset (d := d) m
  let ur : H1Function (openCubeSet (originCube d (m - 1))) :=
    u.restrict (isOpen_openCubeSet _) hsub
  have hP : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2
      (normalizedCubeMeasure (originCube d (m - 1))) := r1_memLp_grad_eucNorm _ ur
  have hQ : MemLp (fun x => ca1_phi (3 ^ m / 4) x * Real.sqrt (vecNormSq (u.grad x))) 2
      (normalizedCubeMeasure (originCube d m)) :=
    ca1_memLp_phi_mul _ _ (r1_memLp_grad_eucNorm _ u)
  rw [ca1_cubeLpNorm_sq _ hP, ca1_cubeLpNorm_sq _ hQ, ca1_cubeAverage_eq, ca1_cubeAverage_eq]
  have e0 : ∀ x : Vec d, Real.sqrt (vecNormSq (u.grad x)) ^ 2 = vecNormSq (u.grad x) := fun x =>
    Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have e1 : ∀ x : Vec d, (ca1_phi (3 ^ m / 4) x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 =
      ca1_Phi (3 ^ m / 4) x * vecNormSq (u.grad x) := by
    intro x; rw [mul_pow, e0, ← ca1_Phi_eq]
  simp only [e0, e1]
  have hL : (0 : ℝ) < 3 ^ m := zpow_pos (by norm_num) m
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have hint : IntegrableOn (fun x => ca1_Phi (3 ^ m / 4) x * vecNormSq (u.grad x))
      (openCubeSet (originCube d m)) volume := ca1_integrable_energy m u _
  -- pointwise
  have hpt : ∀ x ∈ openCubeSet (originCube d (m - 1)), vecNormSq (u.grad x) ≤
      (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * (ca1_Phi (3 ^ m / 4) x * vecNormSq (u.grad x)) := by
    intro x hx
    have hxk : ∀ k, |x k| ≤ 2 / 3 * (3 ^ m / 4) := by
      intro k
      have := (mem_openCubeSet_originCube_iff.1 hx) k
      rw [abs_le]
      have h3 : (3 : ℝ) ^ (m - 1) = 3 ^ m / 3 := by
        rw [zpow_sub₀ (by norm_num)]; simp
      constructor <;> nlinarith only [this.1, this.2, h3, hL]
    have hl := ca1_phi_lower (by positivity : (0 : ℝ) < 3 ^ m / 4) hxk
    have hn : 0 ≤ vecNormSq (u.grad x) := by
      unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 : ((125 / 729 : ℝ) ^ d) ^ 2 ≤ ca1_Phi (3 ^ m / 4) x := by
      rw [ca1_Phi_eq]; exact pow_le_pow_left₀ hc0.le hl 2
    have h3 : 1 ≤ (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ca1_Phi (3 ^ m / 4) x := by
      have e : (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ((125 / 729 : ℝ) ^ d) ^ 2 = 1 := by field_simp
      calc (1 : ℝ) = (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ((125 / 729 : ℝ) ^ d) ^ 2 := e.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    calc vecNormSq (u.grad x) = 1 * vecNormSq (u.grad x) := (one_mul _).symm
      _ ≤ ((((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ca1_Phi (3 ^ m / 4) x) * vecNormSq (u.grad x) :=
          mul_le_mul_of_nonneg_right h3 hn
      _ = _ := by ring
  have hV : 0 < cubeVolume (originCube d (m - 1)) := cubeVolume_pos _
  have hVQ : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  have hratio : cubeVolume (originCube d m) = 3 ^ d * cubeVolume (originCube d (m - 1)) := by
    unfold cubeVolume cubeScaleFactor originCube
    simp only
    rw [zpow_sub₀ (by norm_num), ← mul_pow]
    congr 1
    field_simp
  have h1 : ∫ x in openCubeSet (originCube d (m - 1)), vecNormSq (u.grad x) ≤
      (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ∫ x in openCubeSet (originCube d (m - 1)),
        ca1_Phi (3 ^ m / 4) x * vecNormSq (u.grad x) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ?_ ?_ (isOpen_openCubeSet _).measurableSet hpt
    · exact (memLp_eucNorm_grad (u.restrict (isOpen_openCubeSet _) hsub)).integrable_sq.congr
        (Filter.Eventually.of_forall fun x => by
          show eucNorm _ ^ 2 = _
          exact e0 x)
    · exact (hint.mono_set hsub).const_mul _
  have h2 : ∫ x in openCubeSet (originCube d (m - 1)), ca1_Phi (3 ^ m / 4) x * vecNormSq (u.grad x) ≤
      ∫ x in openCubeSet (originCube d m), ca1_Phi (3 ^ m / 4) x * vecNormSq (u.grad x) := by
    refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub)
    refine Filter.Eventually.of_forall fun x => ?_
    have hn : 0 ≤ vecNormSq (u.grad x) := by
      unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have : 0 ≤ ca1_Phi (3 ^ m / 4) x := by rw [ca1_Phi_eq]; exact sq_nonneg _
    exact mul_nonneg this hn
  have hV' : 0 ≤ (cubeVolume (originCube d (m - 1)))⁻¹ := inv_nonneg.2 hV.le
  have h3 := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))) hV'
  refine h3.trans (le_of_eq ?_)
  rw [hratio]
  field_simp

/-- The constant of the interior Caccioppoli inequality. -/
noncomputable def ca1_Cfin (d : ℕ) (Cα : ℝ) : ℝ :=
  3 ^ d * (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 *
    (4 / 3 * (1 / 2 + 2 * (4 * (12 * 64 ^ d * 64 ^ d)) ^ 2 * Cα +
      2 * (8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * Cα *
        (144 * (50 / 23) ^ 2) +
      ((144 * (50 / 23) ^ 2) + (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) *
        ((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * Cα) / 2 + 48 * 64 ^ d / 2 +
      96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹ * (1 + 144 * (50 / 23) ^ 2) / 2 +
      32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) / 2 +
      48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹ * (1 + 144 * (50 / 23) ^ 2) / 2))

theorem ca1_interior_det [NeZero d] (hd : 2 ≤ d) (m : ℤ) (h : ℕ) (hh : 3 ≤ h)
    {lam Lam ν Λ S α1 β1 α2 β2 Cα : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A)
    (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hsym : ∀ x ∈ openCubeSet (originCube d m), symmPart (A x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d m), ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (hνS : ν ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (hCα : 0 ≤ Cα) (hα : (S * α2 + α1) ^ 2 ≤ Cα * S * ν) (hb : S * β2 + β1 ≤ (3 : ℝ) ^ m)
    (hτs : (3 : ℝ) ^ (m - (h : ℤ)) / (3 : ℝ) ^ m * (S / ν) ^ 2 ≤ 1)
    (hτΞ : (3 : ℝ) ^ (m - (h : ℤ)) / (3 : ℝ) ^ m * (1 + d * Λ ^ 2 / ν ^ 2) ≤ 1)
    (u : H1Function (openCubeSet (originCube d m))) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))))
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (fun _ => 0))
    (hBB : ∀ R ∈ descendantsAtDepth (originCube d m) h,
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
    (c : ℝ) :
    ν * cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
      ca1_Cfin d Cα * (S * (3 : ℝ) ^ (-2 * m) * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
          (fun x => u.toFun x - c) ^ 2 +
        S⁻¹ * (3 : ℝ) ^ (2 * m) * cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f ^ 2) := by
  classical
  have hL : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hsc := ca1_scale_facts m h hh
  have hℓ0 : (0 : ℝ) < (3 : ℝ) ^ (m - (h : ℤ)) := zpow_pos (by norm_num) _
  have hS : 0 ≤ S := le_trans hν.le hνS
  have hℓR : ∀ R ∈ descendantsAtDepth (originCube d m) h, cubeScaleFactor R = (3 : ℝ) ^ (m - (h : ℤ)) := by
    intro R hR
    have := scale_eq_sub_of_mem_descendantsAtDepth hR
    simp [cubeScaleFactor, this, originCube]
  have hmain := ca1_main hd m h hEll hΛ hsym hop hS hα1 hβ1 hα2 hβ2 u hf hu hBB c
    (a := (3 : ℝ) ^ m / 4) (ac := 23 / 50 * (3 : ℝ) ^ m) (ℓ := (3 : ℝ) ^ (m - (h : ℤ)))
    (by positivity) (by linarith only [hL]) hℓ0 hℓR (by linarith only [hsc, hL]) (by linarith only [hsc, hL])
  have hcrude := ca1_crude_norm m hEll hν hΛ hsym hop u hf hu (a := 23 / 50 * (3 : ℝ) ^ m)
    (by positivity) (by linarith only [hL]) c
  have hinner := ca1_inner_le m u
  have hKη : (((ca1_K0 d * Real.toNNReal ((3 : ℝ) ^ m / 4)⁻¹ ^ 2 : ℝ≥0)) : ℝ) =
      (ca1_K0 d : ℝ) * (((3 : ℝ) ^ m / 4)⁻¹) ^ 2 := by
    push_cast
    rw [Real.coe_toNNReal _ (by positivity)]
  rw [hKη] at hmain
  obtain ⟨W, hW⟩ : ∃ W, W = cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c) := ⟨_, rfl⟩
  obtain ⟨Fg, hFg⟩ : ∃ Fg, Fg = cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
    (fun x => ca1_phi ((3 : ℝ) ^ m / 4) x * Real.sqrt (vecNormSq (u.grad x))) := ⟨_, rfl⟩
  obtain ⟨Gc, hGc⟩ : ∃ Gc, Gc = cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
    (fun x => ca1_phi (23 / 50 * (3 : ℝ) ^ m) x * Real.sqrt (vecNormSq (u.grad x))) := ⟨_, rfl⟩
  rw [← hW, ← hFg, ← hG, ← hGc] at hmain
  rw [← hW, ← hFg, ← hGc] at hcrude
  rw [← hG] at hinner
  have hW0 : 0 ≤ W := by rw [hW]; exact ENNReal.toReal_nonneg
  have hF0 : 0 ≤ Fg := by rw [hFg]; exact ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := by rw [hG]; exact ENNReal.toReal_nonneg
  have hGc0 : 0 ≤ Gc := by rw [hGc]; exact ENNReal.toReal_nonneg
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have hI := ca1_rhs_eq (d := d) (L := (3 : ℝ) ^ m) (ℓ := (3 : ℝ) ^ (m - (h : ℤ)))
    (K := cubeBesovW12EmbeddingConstant d) (K0 := (ca1_K0 d : ℝ)) (c0 := (125 / 729 : ℝ) ^ d) (D := (d : ℝ))
    (S := S) (α1 := α1) (α2 := α2) (β1 := β1) (β2 := β2) (Λ := Λ) (W := W) (Fg := Fg) (G := G) (Gc := Gc)
    hL hc0
  have hD1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hK : 0 ≤ cubeBesovW12EmbeddingConstant d := cubeBesovW12EmbeddingConstant_nonneg d
  have hK0 : 0 ≤ (ca1_K0 d : ℝ) := NNReal.coe_nonneg _
  have hα0 : 0 ≤ S * α2 + α1 := by positivity
  have hb0 : 0 ≤ (S * β2 + β1) / (3 : ℝ) ^ m := by positivity
  have hb1 : (S * β2 + β1) / (3 : ℝ) ^ m ≤ 1 := by rw [div_le_one hL]; exact hb
  have hτ0 : 0 ≤ (3 : ℝ) ^ (m - (h : ℤ)) / (3 : ℝ) ^ m := by positivity
  have hII : ν * Gc ^ 2 ≤ (144 * (50 / 23) ^ 2) * (ν⁻¹ * ((3 : ℝ) ^ m * Fg) ^ 2 + ν * (W / (3 : ℝ) ^ m) ^ 2 +
      (d : ℝ) * Λ ^ 2 * ν⁻¹ * (W / (3 : ℝ) ^ m) ^ 2) := by
    refine hcrude.trans ?_
    have hX : 0 ≤ ν⁻¹ * ((3 : ℝ) ^ m * Fg) ^ 2 := by positivity
    have hY : 0 ≤ ν * (W / (3 : ℝ) ^ m) ^ 2 := by positivity
    have hZ : 0 ≤ (d : ℝ) * Λ ^ 2 * ν⁻¹ * (W / (3 : ℝ) ^ m) ^ 2 := by positivity
    have e : (23 / 50 * (3 : ℝ) ^ m) ^ 2 / ν * Fg ^ 2 + (ν / (23 / 50 * (3 : ℝ) ^ m) ^ 2 +
        144 * (d : ℝ) * Λ ^ 2 / (ν * (23 / 50 * (3 : ℝ) ^ m) ^ 2)) * W ^ 2 =
        (23 / 50) ^ 2 * (ν⁻¹ * ((3 : ℝ) ^ m * Fg) ^ 2) + (50 / 23) ^ 2 * (ν * (W / (3 : ℝ) ^ m) ^ 2) +
          (144 * (50 / 23) ^ 2) * ((d : ℝ) * Λ ^ 2 * ν⁻¹ * (W / (3 : ℝ) ^ m) ^ 2) := by
      field_simp
      ring
    rw [e]
    nlinarith only [hX, hY, hZ]
  have hfin := ca1_alg (ν := ν) (S := S) (α := S * α2 + α1) (b := (S * β2 + β1) / (3 : ℝ) ^ m)
    (τ := (3 : ℝ) ^ (m - (h : ℤ)) / (3 : ℝ) ^ m) (Λ := Λ) (D := (d : ℝ)) (Cα := Cα)
    (c1 := 4 * (12 * 64 ^ d * 64 ^ d))
    (c2 := 8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹)
    (c3 := 32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) * ((125 / 729 : ℝ) ^ d)⁻¹)
    (c4 := 48 * 64 ^ d)
    (c5 := 96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹)
    (c6 := 32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ))
    (c7 := 48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹) (c8 := 144 * (50 / 23) ^ 2)
    (g := G) (k := Gc) (w := W / (3 : ℝ) ^ m) (f := (3 : ℝ) ^ m * Fg) hν hνS hα hb1 hτ0 hD1 hτs hτΞ
    hCα (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hGc0
    (by positivity) (by positivity) (hmain.trans_eq hI) hII
  have hL2 : (3 : ℝ) ^ (2 * m) = ((3 : ℝ) ^ m) ^ 2 := by
    rw [two_mul, zpow_add₀ (by norm_num)]; ring
  have hL2' : (3 : ℝ) ^ (-2 * m) = (((3 : ℝ) ^ m) ^ 2)⁻¹ := by
    rw [← hL2, ← zpow_neg]; congr 1; ring
  have hc0' : 0 ≤ 3 ^ d * (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hinner hν.le
  have h2 := mul_le_mul_of_nonneg_left hfin hc0'
  have e : ca1_Cfin d Cα * (S * (3 : ℝ) ^ (-2 * m) * W ^ 2 + S⁻¹ * (3 : ℝ) ^ (2 * m) * Fg ^ 2) =
      3 ^ d * (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 *
        (4 / 3 * (1 / 2 + 2 * (4 * (12 * 64 ^ d * 64 ^ d)) ^ 2 * Cα +
          2 * (8 * cubeBesovW12EmbeddingConstant d * (12 * 64 ^ d * 64 ^ d) * ((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * Cα *
            (144 * (50 / 23) ^ 2) +
          ((144 * (50 / 23) ^ 2) + (32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) *
            ((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * Cα) / 2 + 48 * 64 ^ d / 2 +
          96 * 64 ^ d * cubeBesovW12EmbeddingConstant d * ((125 / 729 : ℝ) ^ d)⁻¹ * (1 + 144 * (50 / 23) ^ 2) / 2 +
          32 * cubeBesovW12EmbeddingConstant d * Real.sqrt d * (ca1_K0 d : ℝ) / 2 +
          48 * Real.sqrt d * 16 ^ 5 * ((125 / 729 : ℝ) ^ d)⁻¹ * (1 + 144 * (50 / 23) ^ 2) / 2)) *
        (S * (W / (3 : ℝ) ^ m) ^ 2 + S⁻¹ * ((3 : ℝ) ^ m * Fg) ^ 2) := by
    unfold ca1_Cfin
    rw [hL2, hL2']
    field_simp
  rw [← hW, ← hFg, e]
  calc ν * cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ^ 2
      ≤ ν * (3 ^ d * (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * G ^ 2) := h1
    _ = 3 ^ d * (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * (ν * G ^ 2) := by ring
    _ ≤ _ := h2.trans_eq (by ring)

/-- Witness for the non-law hypotheses of `ca1_interior_det` (and, through it, of `ca1_main`,
`ca1_cube_ambient`, `ca1_cube_test`): the identity field on the unit cube of `ℝ²` at `m = h = 3`,
`ν = S = Λ = 1`, `α₂ = K`, all other coefficients `0`, the zero solution with zero data; the weak bounds
follow from the embedding `L̲² ↪ H̲^{-1/4}`. -/
example : True := by
  obtain ⟨K, hK, hD⟩ := r1_ofReal_dual_le 2
  have hz : ∀ (R : TriadicCube 2) (u' : H1Function (openCubeSet (originCube 2 R.scale))) (x : Vec 2),
      matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) x - (1 : ℝ) • (1 : Mat 2)) (u'.grad x) = (0 : Vec 2) := by
    intro R u' x; funext i; simp [matVecMul]
  have hBB : ∀ R ∈ descendantsAtDepth (originCube 2 3) 3,
      ∀ (u' : H1Function (openCubeSet (originCube 2 R.scale))) (f' : Vec 2 → ℝ),
      IsWeakSolutionOn (fun x => (fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift R))
        (openCubeSet (originCube 2 R.scale)) u' f' (fun _ => 0) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube 2 R.scale)
          (1 / 4 : ℝ) (fun x => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift R) -
            (1 : ℝ) • (1 : Mat 2)) (u'.grad x))) ≤
        ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale)
            (ENNReal.ofReal (sobStar 2)).conjExponent f' ∧
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube 2 R.scale)
          (1 / 4 : ℝ) u'.grad) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale) 2
            (fun x => Real.sqrt (vecNormSq (u'.grad x))) +
          ENNReal.ofReal 0 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 R.scale)
            (ENNReal.ofReal (sobStar 2)).conjExponent f' := by
    intro R _ u' f' _
    refine ⟨?_, ?_⟩
    · have e : (fun x => matVecMul ((fun _ : Vec 2 => (1 : Mat 2)) (x + triadicCubeShift R) -
          (1 : ℝ) • (1 : Mat 2)) (u'.grad x)) = fun _ => (0 : Vec 2) := by
        funext x i; simp [matVecMul]
      rw [e]
      refine le_trans (hD _ (fun _ => (0 : Vec 2)) (fun i => memLp_const 0)
        (by simp [vecNormSq, vecDot])) ?_
      simp [SuperdiffusionCLT.Section2.Norms.cubeLpENorm, vecNormSq, vecDot]
    · refine le_trans (hD _ u'.grad (r1_memLp_grad_comp _ u') (r1_memLp_grad_eucNorm _ u')) ?_
      simp
  have := ca1_interior_det (d := 2) (le_refl 2) 3 3 (le_refl 3) (A := fun _ => (1 : Mat 2)) (lam := 1) (Lam := 1)
    (ν := 1) (Λ := 1) (S := 1) (α1 := 0) (β1 := 0) (α2 := K) (β2 := 0) (Cα := K ^ 2)
    (Section6.ew1_ellip _ (measurableSet_openCubeSet _)) one_pos zero_le_one
    (fun x _ => by
      ext i j
      simp [symmPart, Matrix.one_apply, eq_comm])
    (fun x _ v => by simp [r1_matVecMul_one]) le_rfl le_rfl le_rfl hK le_rfl (sq_nonneg K)
    (by simp) (by norm_num) (by norm_num) (by norm_num)
    (0 : H1Function (openCubeSet (originCube 2 3))) (f := fun _ => 0) (memLp_const 0)
    (fun φ => by simp [matVecMul, vecDot]) hBB 0
  trivial

end SuperdiffusionCLT.Section7
