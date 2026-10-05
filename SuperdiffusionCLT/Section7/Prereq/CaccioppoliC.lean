/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliB
public import SuperdiffusionCLT.Section7.Prereq.Caccioppoli
public import SuperdiffusionCLT.Section6.Engine.WitnessLaplace
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.EquationRestrictionZeroExtension
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.CubeTranslationTransport
public import SuperdiffusionCLT.Section7.Analytic.CZ.Local
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube

/-!
# The energy identity and the crude Caccioppoli inequality (interior Caccioppoli, step 3)

For a solution `u` of `-∇·(A∇u) = f` in the origin cube, with `A = ν Id + (skew)`, testing with
`Φ_a (u - c)` (the cutoff weight of `CaccioppoliB`) gives
`ν ∫ Φ_a |∇u|² = ∫ f Φ_a (u - c) - ∫ (A∇u)·((u - c) ∇Φ_a)`, because the skew part has zero
quadratic form.  With the pointwise operator bound `|A v| ≤ Λ |v|` and Young's inequality this is the
unsigned Caccioppoli inequality (`e.Dir.new.Cacc.crude`) with the constant
`Λ²/ν` in front of the `L²` norm of `u - c`.

## Main results

* `Section7.ca1_energy_identity`: the identity above.
* `Section7.ca1_crude`: `ν ∫ Φ_a|∇u|² ≤ a²/ν ∫ f² + (ν/a² + 144 d Λ²/(ν a²)) ∫ (u-c)²`.
* `Section7.ca1_weak_restrict`, `Section7.ca1_exists_shift`: a weak solution restricts to an open subcube and
  translates to the origin cube of the same scale.
* `Section7.ca1_cube_test`, `Section7.ca1_cube_ambient`: the weak test on one grid cube for the
  vector field `(u - c) ∇Φ_a`, in the translated frame and in the ambient frame.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization
open SuperdiffusionCLT.Section8.Common.ExcessDecay

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The constant function as an `H¹` function on a cube. -/
noncomputable def ca1_const (Q : TriadicCube d) (c : ℝ) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_const (c := c))

theorem ca1_const_toFun (Q : TriadicCube d) (c : ℝ) (x : Vec d) : (ca1_const Q c).toFun x = c := rfl

theorem ca1_const_grad (Q : TriadicCube d) (c : ℝ) (x : Vec d) : (ca1_const Q c).grad x = 0 := by
  funext i
  show (fderiv ℝ (fun _ : Vec d => c) x) (basisVec i) = 0
  simp


theorem ca1_lipGradient (a : ℝ) (x : Vec d) : lipGradient (ca1_Phi a) x = fun i => ca1_E a i x := by
  funext i
  exact ca1_Phi_fderiv a i x

theorem ca1_Phi_abs_le (a : ℝ) (x : Vec d) : |ca1_Phi a x| ≤ 1 := by
  rw [ca1_Phi_eq, abs_of_nonneg (sq_nonneg _)]
  have h0 := ca1_phi_nonneg a x
  have h1 := ca1_phi_le_one a x
  nlinarith only [h0, h1]

/-- The test function `Φ_a (u - c)` of the energy identity. -/
noncomputable def ca1_testFn (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) {a : ℝ}
    (ha : 0 < a) (hat : a < 3 ^ m / 2) (c : ℝ) : H10Function (openCubeSet (originCube d m)) :=
  mulLipH10 (isOpen_openCubeSet _) (u - ca1_const (originCube d m) c)
    ((ca1_lipschitz (d := d)).choose_spec a ha).1 (M := 1) (ca1_Phi_abs_le a)
    (ca1_hasCompactSupport_Phi ha)
    ((ca1_tsupport_Phi_subset ha).trans (ca1_closedBall_subset_openCube m hat))

theorem ca1_testFn_toFun (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) {a : ℝ}
    (ha : 0 < a) (hat : a < 3 ^ m / 2) (c : ℝ) (x : Vec d) :
    (ca1_testFn m u ha hat c).toH1Function.toFun x = ca1_Phi a x * (u.toFun x - c) := by
  simp [ca1_testFn, mulLipH10_toH1Function, mulLip, H1Function.sub_toFun, ca1_const_toFun]

theorem ca1_testFn_grad (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) {a : ℝ}
    (ha : 0 < a) (hat : a < 3 ^ m / 2) (c : ℝ) (x : Vec d) :
    (ca1_testFn m u ha hat c).toH1Function.grad x =
      ca1_Phi a x • u.grad x + (u.toFun x - c) • (fun i => ca1_E a i x) := by
  simp [ca1_testFn, mulLipH10_toH1Function, mulLip, H1Function.sub_grad, H1Function.sub_toFun,
    ca1_const_toFun, ca1_const_grad, ca1_lipGradient]


theorem ca1_E_abs_le_const {a : ℝ} (ha : 0 < a) (i : Fin d) (x : Vec d) : |ca1_E a i x| ≤ 12 * a⁻¹ := by
  refine (ca1_E_abs_le ha i x).trans ?_
  have h := ca1_phi_le_one a x
  have h0 : 0 ≤ 12 * a⁻¹ := by positivity
  calc 12 * a⁻¹ * ca1_phi a x ≤ 12 * a⁻¹ * 1 := mul_le_mul_of_nonneg_left h h0
    _ = _ := mul_one _

theorem ca1_E_continuous (a : ℝ) (i : Fin d) : Continuous (ca1_E a i) := by
  unfold ca1_E
  exact continuous_const.mul ((ca1_E1_contDiff i).continuous.comp (continuous_const_smul a⁻¹))

/-- Integrability of the cross term of the energy identity. -/
theorem ca1_integrable_cross [NeZero d] (m : ℤ) {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A)
    (u : H1Function (openCubeSet (originCube d m))) {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun x => vecDot (matVecMul (A x) (u.grad x))
      ((u.toFun x - c) • fun i => ca1_E a i x)) (openCubeSet (originCube d m)) volume := by
  have hF : MemLp (fun x => matVecMul (A x) (u.grad x)) 2
      (volume.restrict (openCubeSet (originCube d m))) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hw : MemLp (fun x => u.toFun x - c) 2 (volume.restrict (openCubeSet (originCube d m))) := by
    have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
      exact (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
    exact u.memL2.sub (memLp_const c)
  have : (fun x => vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x)) =
      fun x => ∑ i, ca1_E a i x * (matVecMul (A x) (u.grad x) i * (u.toFun x - c)) := by
    funext x
    unfold vecDot
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [this]
  refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
  refine Integrable.bdd_mul (c := 12 * a⁻¹) ?_ (ca1_E_continuous a i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((memLp_pi_iff.1 hF) i).integrable_mul hw
  · rw [Real.norm_eq_abs]; exact ca1_E_abs_le_const ha i x


theorem ca1_integrable_energy [NeZero d] (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) (a : ℝ) :
    IntegrableOn (fun x => ca1_Phi a x * vecNormSq (u.grad x)) (openCubeSet (originCube d m)) volume := by
  have h1 : Integrable (fun x => eucNorm (u.grad x) ^ 2)
      (volume.restrict (openCubeSet (originCube d m))) := (memLp_eucNorm_grad u).integrable_sq
  have h2 : (fun x => eucNorm (u.grad x) ^ 2) = fun x => vecNormSq (u.grad x) := by
    funext x
    unfold eucNorm
    exact Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  rw [h2] at h1
  refine Integrable.bdd_mul (c := 1) h1 (ca1_Phi1_contDiff.continuous.comp
    (continuous_const_smul a⁻¹)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact ca1_Phi_abs_le a x

/-- **The energy identity** for the test function `Φ_a (u - c)` (interior case):
`ν ∫ Φ_a |∇u|² = ∫ f Φ_a (u - c) - ∫ (A ∇u)·((u - c) ∇Φ_a)`; the skew part of `A` drops out of the
quadratic form. -/
theorem ca1_energy_identity [NeZero d] (m : ℤ) {lam Lam ν : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A)
    (hsym : ∀ x ∈ openCubeSet (originCube d m), symmPart (A x) = ν • (1 : Mat d))
    (u : H1Function (openCubeSet (originCube d m))) {f : Vec d → ℝ}
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (fun _ => 0))
    {a : ℝ} (ha : 0 < a) (hat : a < 3 ^ m / 2) (c : ℝ) :
    ν * ∫ x in openCubeSet (originCube d m), ca1_Phi a x * vecNormSq (u.grad x) =
      (∫ x in openCubeSet (originCube d m), f x * (ca1_Phi a x * (u.toFun x - c))) -
        ∫ x in openCubeSet (originCube d m), vecDot (matVecMul (A x) (u.grad x))
          ((u.toFun x - c) • fun i => ca1_E a i x) := by
  have h := hu (ca1_testFn m u ha hat c)
  simp only [ca1_testFn_toFun, ca1_testFn_grad, vecDot_zero_left, integral_zero, add_zero] at h
  have hU : MeasurableSet (openCubeSet (originCube d m)) := (isOpen_openCubeSet _).measurableSet
  have hpt : ∀ x ∈ openCubeSet (originCube d m),
      vecDot (matVecMul (A x) (u.grad x)) (ca1_Phi a x • u.grad x + (u.toFun x - c) • fun i => ca1_E a i x) =
        ν * (ca1_Phi a x * vecNormSq (u.grad x)) +
          vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x) := by
    intro x hx
    rw [vecDot_add_right, vecDot_smul_right, r1_quad_symm (hsym x hx)]
    ring
  rw [setIntegral_congr_fun hU hpt, integral_add ((ca1_integrable_energy m u a).const_mul ν)
    (ca1_integrable_cross m hEll u ha c), integral_const_mul] at h
  linarith only [h]


theorem ca1_eucNorm_le_of_abs_le {v : Vec d} {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, |v i| ≤ B) :
    eucNorm v ≤ Real.sqrt d * B := by
  unfold eucNorm
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  have : vecNormSq v = ∑ i, v i ^ 2 := by simp [vecNormSq, vecDot, pow_two]
  rw [this]
  calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin d, B ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = d * B ^ 2 := by simp


theorem ca1_abs_vecDot_le (x y : Vec d) : |vecDot x y| ≤ eucNorm x * eucNorm y := by
  unfold eucNorm
  rw [← Real.sqrt_mul (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
  exact Real.abs_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq x y)

/-- Pointwise bound of the cross term of the energy identity. -/
theorem ca1_cross_pointwise {ν Λ a : ℝ} (hν : 0 < ν) (ha : 0 < a) (hΛ : 0 ≤ Λ) (A : Mat d) (v : Vec d)
    (hop : ∀ v : Vec d, eucNorm (matVecMul A v) ≤ Λ * eucNorm v) (x : Vec d) (w : ℝ) :
    |vecDot (matVecMul A v) (w • fun i => ca1_E a i x)| ≤
      ν / 2 * (ca1_Phi a x * vecNormSq v) + (144 * d * Λ ^ 2 * a⁻¹ ^ 2) / (2 * ν) * w ^ 2 := by
  have hE : eucNorm (w • fun i => ca1_E a i x) ≤ Real.sqrt d * (12 * a⁻¹ * ca1_phi a x * |w|) := by
    refine ca1_eucNorm_le_of_abs_le (by have := ca1_phi_nonneg a x; positivity) fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    calc |w| * |ca1_E a i x| ≤ |w| * (12 * a⁻¹ * ca1_phi a x) :=
          mul_le_mul_of_nonneg_left (ca1_E_abs_le ha i x) (abs_nonneg _)
      _ = _ := by ring
  have h1 := ca1_abs_vecDot_le (matVecMul A v) (w • fun i => ca1_E a i x)
  have h2 : eucNorm (matVecMul A v) * eucNorm (w • fun i => ca1_E a i x) ≤
      (Λ * eucNorm v) * (Real.sqrt d * (12 * a⁻¹ * ca1_phi a x * |w|)) :=
    mul_le_mul (hop v) hE (by unfold eucNorm; positivity) (by unfold eucNorm; positivity)
  set p : ℝ := ca1_phi a x * eucNorm v with hp
  set q : ℝ := 12 * Real.sqrt d * Λ * a⁻¹ * |w| with hq
  have h3 : (Λ * eucNorm v) * (Real.sqrt d * (12 * a⁻¹ * ca1_phi a x * |w|)) = p * q := by
    rw [hp, hq]; ring
  have h4 := ca1_young (r := ν) (p := p) (q := q) hν
  have h5 : p ^ 2 = ca1_Phi a x * vecNormSq v := by
    rw [hp, mul_pow, ← ca1_Phi_eq]
    unfold eucNorm
    rw [Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)]
  have h6 : q ^ 2 = 144 * d * Λ ^ 2 * a⁻¹ ^ 2 * w ^ 2 := by
    rw [hq]
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), sq_abs]
    ring
  rw [h5] at h4
  have h7 : q ^ 2 / (2 * ν) = (144 * d * Λ ^ 2 * a⁻¹ ^ 2) / (2 * ν) * w ^ 2 := by
    rw [h6]; ring
  rw [h7] at h4
  refine h1.trans (h2.trans ?_)
  rw [h3]
  exact h4


theorem ca1_crude_alg {ν r Cc X F2 W2 If IT : ℝ}
    (hid : ν * X = If - IT) (hIf : If ≤ r / 2 * F2 + 1 / (2 * r) * W2)
    (hIT : -IT ≤ ν / 2 * X + Cc / (2 * ν) * W2) :
    ν * X ≤ r * F2 + (1 / r + Cc / ν) * W2 := by
  have e1 : 1 / (2 * r) * W2 = 1 / r * W2 / 2 := by ring
  have e2 : Cc / (2 * ν) * W2 = Cc / ν * W2 / 2 := by ring
  have e3 := add_mul (1 / r) (Cc / ν) W2
  linarith only [hid, hIf, hIT, e1, e2, e3]

/-- **The crude (unsigned) Caccioppoli inequality**, interior case (with the
pointwise coefficient bound `|A v| ≤ Λ |v|`): the cutoff-weighted energy of a solution is bounded by
`Λ²/ν` times the `L²` norm of `u - c` at the scale `a`. -/
theorem ca1_crude [NeZero d] (m : ℤ) {lam Lam ν Λ : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A) (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hsym : ∀ x ∈ openCubeSet (originCube d m), symmPart (A x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d m), ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (u : H1Function (openCubeSet (originCube d m))) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))))
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (fun _ => 0))
    {a : ℝ} (ha : 0 < a) (hat : a < 3 ^ m / 2) (c : ℝ) :
    ν * ∫ x in openCubeSet (originCube d m), ca1_Phi a x * vecNormSq (u.grad x) ≤
      a ^ 2 / ν * (∫ x in openCubeSet (originCube d m), f x ^ 2) +
        (ν / a ^ 2 + 144 * d * Λ ^ 2 / (ν * a ^ 2)) *
          ∫ x in openCubeSet (originCube d m), (u.toFun x - c) ^ 2 := by
  have hU : MeasurableSet (openCubeSet (originCube d m)) := (isOpen_openCubeSet _).measurableSet
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isFiniteMeasure_restrict_volume
  have hw : MemLp (fun x => u.toFun x - c) 2 (volume.restrict (openCubeSet (originCube d m))) :=
    u.memL2.sub (memLp_const c)
  have hf2 : Integrable (fun x => f x ^ 2) (volume.restrict (openCubeSet (originCube d m))) :=
    hf.integrable_sq
  have hw2 : Integrable (fun x => (u.toFun x - c) ^ 2) (volume.restrict (openCubeSet (originCube d m))) :=
    hw.integrable_sq
  have hX := ca1_integrable_energy m u a
  have hid := ca1_energy_identity m hEll hsym u hu ha hat c
  set r : ℝ := a ^ 2 / ν with hr
  have hr0 : 0 < r := by positivity
  set X := ∫ x in (openCubeSet (originCube d m)), ca1_Phi a x * vecNormSq (u.grad x) with hXdef
  set F2 := ∫ x in (openCubeSet (originCube d m)), f x ^ 2 with hF2
  set W2 := ∫ x in (openCubeSet (originCube d m)), (u.toFun x - c) ^ 2 with hW2
  set Cc : ℝ := 144 * d * Λ ^ 2 * a⁻¹ ^ 2 with hCc
  -- the right-hand-side term
  have hIf : (∫ x in (openCubeSet (originCube d m)), f x * (ca1_Phi a x * (u.toFun x - c))) ≤
      r / 2 * F2 + 1 / (2 * r) * W2 := by
    have hle : ∀ x ∈ (openCubeSet (originCube d m)), f x * (ca1_Phi a x * (u.toFun x - c)) ≤
        r / 2 * f x ^ 2 + 1 / (2 * r) * (u.toFun x - c) ^ 2 := by
      intro x _
      have h1 := ca1_young (r := r) (p := f x) (q := ca1_Phi a x * (u.toFun x - c)) hr0
      have hΦ0 : 0 ≤ ca1_Phi a x := by rw [ca1_Phi_eq]; exact sq_nonneg _
      have hΦ1 : ca1_Phi a x ≤ 1 := (abs_le.1 (ca1_Phi_abs_le a x)).2
      have h2 : (ca1_Phi a x * (u.toFun x - c)) ^ 2 ≤ (u.toFun x - c) ^ 2 := by
        rw [mul_pow]
        have : ca1_Phi a x ^ 2 ≤ 1 := by nlinarith only [hΦ0, hΦ1]
        nlinarith only [this, sq_nonneg (u.toFun x - c)]
      have h3 : (ca1_Phi a x * (u.toFun x - c)) ^ 2 / (2 * r) ≤ 1 / (2 * r) * (u.toFun x - c) ^ 2 := by
        rw [div_eq_mul_inv, mul_comm, one_div]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith only [h1, h3]
    have hfw : Integrable (fun x => f x * (u.toFun x - c)) (volume.restrict (openCubeSet (originCube d m))) := hf.integrable_mul hw
    have hint : Integrable (fun x => f x * (ca1_Phi a x * (u.toFun x - c))) (volume.restrict (openCubeSet (originCube d m))) := by
      have h := hfw.bdd_mul (c := 1) (f := ca1_Phi a)
        (ca1_Phi1_contDiff.continuous.comp (continuous_const_smul a⁻¹)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact ca1_Phi_abs_le a x)
      refine h.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    have hg : IntegrableOn (fun x => r / 2 * f x ^ 2 + 1 / (2 * r) * (u.toFun x - c) ^ 2)
        (openCubeSet (originCube d m)) volume :=
      (hf2.const_mul (r / 2)).add (hw2.const_mul (1 / (2 * r)))
    have := setIntegral_mono_on hint hg hU hle
    rw [integral_add (hf2.const_mul (r / 2)) (hw2.const_mul (1 / (2 * r))), integral_const_mul,
      integral_const_mul] at this
    exact this
  -- the cross term
  have hIT : -(∫ x in (openCubeSet (originCube d m)), vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x)) ≤
      ν / 2 * X + Cc / (2 * ν) * W2 := by
    have hle : ∀ x ∈ (openCubeSet (originCube d m)), -vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x) ≤
        ν / 2 * (ca1_Phi a x * vecNormSq (u.grad x)) + Cc / (2 * ν) * (u.toFun x - c) ^ 2 := by
      intro x hx
      have := ca1_cross_pointwise hν ha hΛ (A x) (u.grad x) (hop x hx) x (u.toFun x - c)
      have h2 := neg_abs_le (vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x))
      linarith only [this, h2]
    have hcross := ca1_integrable_cross m hEll u ha c
    have hg : IntegrableOn (fun x => ν / 2 * (ca1_Phi a x * vecNormSq (u.grad x)) +
        Cc / (2 * ν) * (u.toFun x - c) ^ 2) (openCubeSet (originCube d m)) volume :=
      (hX.const_mul (ν / 2)).add (hw2.const_mul (Cc / (2 * ν)))
    have := setIntegral_mono_on (f := fun x => -vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x)) hcross.neg hg hU hle
    rw [integral_add (hX.const_mul (ν / 2)) (hw2.const_mul (Cc / (2 * ν))), integral_const_mul,
      integral_const_mul, integral_neg] at this
    exact this
  have hfinal := ca1_crude_alg hid hIf hIT
  have e : 1 / r + Cc / ν = ν / a ^ 2 + 144 * d * Λ ^ 2 / (ν * a ^ 2) := by
    rw [hr, hCc]
    field_simp
  rw [e] at hfinal
  exact hfinal


/-- Witness for `ca1_crude` (and, through it, `ca1_energy_identity`): the identity field, the zero
solution, zero data and `a = 1/4` on the unit cube of `ℝ²`. -/
example : (1 : ℝ) * ∫ x in openCubeSet (originCube 2 0),
      ca1_Phi (1 / 4 : ℝ) x * vecNormSq ((0 : H1Function (openCubeSet (originCube 2 0))).grad x) ≤
    (1 / 4 : ℝ) ^ 2 / 1 * (∫ x in openCubeSet (originCube 2 0), (fun _ : Vec 2 => (0 : ℝ)) x ^ 2) +
      (1 / (1 / 4 : ℝ) ^ 2 + 144 * ((2 : ℕ) : ℝ) * 1 ^ 2 / (1 * (1 / 4 : ℝ) ^ 2)) *
        ∫ x in openCubeSet (originCube 2 0),
          ((0 : H1Function (openCubeSet (originCube 2 0))).toFun x - 0) ^ 2 :=
  ca1_crude (d := 2) 0 (A := fun _ => (1 : Mat 2)) (lam := 1) (Lam := 1) (ν := 1) (Λ := 1)
    (Section6.ew1_ellip _ (measurableSet_openCubeSet _)) one_pos zero_le_one
    (fun x _ => by
      ext i j
      simp [symmPart, Matrix.one_apply, eq_comm])
    (fun x _ v => by
      simp [r1_matVecMul_one])
    0 (memLp_const 0) (fun φ => by simp [matVecMul, vecDot]) (by norm_num) (by norm_num) 0

theorem ca1_setIntegral_extend {V W : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    (H : Vec d → ℝ) :
    ∫ x in W, V.indicator H x = ∫ x in V, H x := by
  rw [integral_indicator hV, Measure.restrict_restrict hV, Set.inter_eq_left.mpr hVW]

/-- **A weak solution restricts to every open subset.** -/
theorem ca1_weak_restrict {W V : Set (Vec d)} (hV : IsOpen V) (hVW : V ⊆ W) {A : CoeffField d}
    {u : H1Function W} {f : Vec d → ℝ} {g : Vec d → Vec d} (h : IsWeakSolutionOn A W u f g) :
    IsWeakSolutionOn A V (u.restrict hV hVW) f g := by
  intro φ
  have h1 := h (h10ExtendToSuperset φ hV.measurableSet hVW)
  have e1 : ∀ F : Vec d → Vec d, ∫ x in W, vecDot (F x)
      ((h10ExtendToSuperset φ hV.measurableSet hVW).toH1Function.grad x) =
      ∫ x in V, vecDot (F x) (φ.toH1Function.grad x) := by
    intro F
    have : (fun x => vecDot (F x) ((h10ExtendToSuperset φ hV.measurableSet hVW).toH1Function.grad x)) =
        V.indicator (fun x => vecDot (F x) (φ.toH1Function.grad x)) := by
      funext x
      rw [h10ExtendToSuperset_grad]
      by_cases hx : x ∈ V
      · simp only [h10ZeroExtensionGrad_of_mem φ hx, Set.indicator_of_mem hx]
      · simp only [h10ZeroExtensionGrad_of_not_mem φ hx, Set.indicator_of_notMem hx, vecDot_zero_right]
    rw [this, ca1_setIntegral_extend hV.measurableSet hVW]
  have e2 : ∫ x in W, f x * (h10ExtendToSuperset φ hV.measurableSet hVW).toH1Function.toFun x =
      ∫ x in V, f x * φ.toH1Function.toFun x := by
    have : (fun x => f x * (h10ExtendToSuperset φ hV.measurableSet hVW).toH1Function.toFun x) =
        V.indicator (fun x => f x * φ.toH1Function.toFun x) := by
      funext x
      rw [h10ExtendToSuperset_toFun]
      by_cases hx : x ∈ V
      · simp only [h10ZeroExtension_of_mem φ hx, Set.indicator_of_mem hx]
      · simp only [h10ZeroExtension_of_not_mem φ hx, Set.indicator_of_notMem hx, mul_zero]
    rw [this, ca1_setIntegral_extend hV.measurableSet hVW]
  rw [e1, e2, e1] at h1
  exact h1


theorem ca1_openCube_subset_translate (R : TriadicCube d) :
    openCubeSet (originCube d R.scale) ⊆ translateSet (-triadicCubeShift R) (openCubeSet R) := by
  intro x hx
  rw [mem_translateSet_iff_sub_mem, sub_neg_eq_add]
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, mem_translateSet_iff_sub_mem]
  simpa using hx

/-- **Translation of a restricted weak solution to the origin cube of the same scale.** -/
theorem ca1_exists_shift (R : TriadicCube d) {W : Set (Vec d)} (hRW : openCubeSet R ⊆ W)
    {A : CoeffField d} (u : H1Function W) {f : Vec d → ℝ}
    (hu : IsWeakSolutionOn A W u f (fun _ => 0)) :
    ∃ u' : H1Function (openCubeSet (originCube d R.scale)),
      (∀ x, u'.toFun x = u.toFun (x + triadicCubeShift R)) ∧
      (∀ x, u'.grad x = u.grad (x + triadicCubeShift R)) ∧
      IsWeakSolutionOn (fun x => A (x + triadicCubeShift R)) (openCubeSet (originCube d R.scale)) u'
        (fun x => f (x + triadicCubeShift R)) (fun _ => 0) := by
  have hur := ca1_weak_restrict (isOpen_openCubeSet R) hRW hu
  have ht := IsWeakSolutionOn.translate (-triadicCubeShift R) hur
  have hu' := ca1_weak_restrict (isOpen_openCubeSet (originCube d R.scale))
    (ca1_openCube_subset_translate R) ht
  refine ⟨((u.restrict (isOpen_openCubeSet R) hRW).translate (-triadicCubeShift R)).restrict
    (isOpen_openCubeSet (originCube d R.scale)) (ca1_openCube_subset_translate R), fun x => ?_,
    fun x => ?_, ?_⟩
  · simp [H1Function.restrict, H1Function.translate_toFun, sub_neg_eq_add]
  · simp [H1Function.restrict, H1Function.translate_grad, sub_neg_eq_add]
  · simpa [sub_neg_eq_add] using hu'


theorem ca1_cubeLpNorm_shift (R : TriadicCube d) (p : ℝ≥0∞) {G : Vec d → ℝ}
    (hG : AEStronglyMeasurable G (normalizedCubeMeasure R)) :
    cubeLpNorm (originCube d R.scale) p (fun x => G (x + triadicCubeShift R)) =
      cubeLpNorm R p G := by
  unfold cubeLpNorm
  exact congrArg ENNReal.toReal (by
    simpa [Function.comp] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving (g := G) (p := p) hG
        (measurePreserving_addRight_normalizedCubeMeasure_originCube R)))

theorem ca1_cubeLpENorm_shift (R : TriadicCube d) (p : ℝ≥0∞) {G : Vec d → ℝ}
    (hG : AEStronglyMeasurable G (normalizedCubeMeasure R)) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale) p
        (fun x => G (x + triadicCubeShift R)) =
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm R p G := by
  unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm
  simpa [Function.comp] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving (g := G) (p := p) hG
        (measurePreserving_addRight_normalizedCubeMeasure_originCube R))

theorem ca1_elliptic_shift (R : TriadicCube d) {W : Set (Vec d)} (hRW : openCubeSet R ⊆ W)
    {lam Lam : ℝ} {A : CoeffField d} (hEll : IsEllipticFieldOn lam Lam W A) :
    IsEllipticFieldOn lam Lam (openCubeSet (originCube d R.scale)) (fun x => A (x + triadicCubeShift R)) := by
  classical
  have hmem : ∀ x ∈ openCubeSet (originCube d R.scale), x + triadicCubeShift R ∈ W := by
    intro x hx
    apply hRW
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, mem_translateSet_iff_sub_mem]
    simpa using hx
  have h1 : Measurable (fun x i j => if x ∈ W then A x i j else 0) := hEll.1
  refine ⟨?_, fun x hx => hEll.2 _ (hmem x hx)⟩
  have h2 : Measurable (fun x : Vec d => fun i j => if x + triadicCubeShift R ∈ W then
      A (x + triadicCubeShift R) i j else 0) := h1.comp (measurable_add_const _)
  have h3 : (fun x : Vec d => fun i j => if x ∈ openCubeSet (originCube d R.scale) then
      A (x + triadicCubeShift R) i j else 0) =
      fun x => if x ∈ openCubeSet (originCube d R.scale) then
        (fun i j => if x + triadicCubeShift R ∈ W then A (x + triadicCubeShift R) i j else 0) else 0 := by
    funext x
    by_cases hx : x ∈ openCubeSet (originCube d R.scale)
    · simp only [hx, ite_true, hmem x hx]
    · simp only [hx, ite_false]
      funext i j
      rfl
  rw [h3]
  exact Measurable.ite (isOpen_openCubeSet _).measurableSet h2 measurable_const


theorem ca1_cubeLpNorm_le (Q : TriadicCube d) {F G : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q))
    (hG : MemLp G 2 (normalizedCubeMeasure Q)) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ᵐ x ∂(normalizedCubeMeasure Q), |F x| ≤ M * |G x|) :
    cubeLpNorm Q (2 : ℝ≥0∞) F ≤ M * cubeLpNorm Q (2 : ℝ≥0∞) G := by
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := normalizedCubeMeasure Q) (c := M) (g := G) hF
    (h.mono fun x hx => by simpa using hx) (2 : ℝ≥0∞)
  have h2 : ENNReal.ofReal M * eLpNorm G 2 (normalizedCubeMeasure Q) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top
  have h3 := ENNReal.toReal_mono h2 h1
  unfold cubeLpNorm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] at h3
  exact h3


theorem ca1_eucNorm_smul (c : ℝ) (v : Vec d) : eucNorm (c • v) = |c| * eucNorm v := by
  unfold eucNorm
  have : vecNormSq (c • v) = c ^ 2 * vecNormSq v := by
    simp [vecNormSq, vecDot, Finset.mul_sum, pow_two]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem ca1_eucNorm_nonneg (v : Vec d) : 0 ≤ eucNorm v := Real.sqrt_nonneg _

theorem ca1_cube_test [NeZero d] (n : ℤ) {lam Lam : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) A)
    {S α1 β1 α2 β2 : ℝ} (hS : 0 ≤ S) (hα1 : 0 ≤ α1) (hβ1 : 0 ≤ β1) (hα2 : 0 ≤ α2) (hβ2 : 0 ≤ β2)
    (u : H1Function (openCubeSet (originCube d n))) (f : Vec d → ℝ)
    (hf : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n)
      (ENNReal.ofReal (sobStar d)).conjExponent f ≠ ⊤)
    (hflux : ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d n)
        (1 / 4 : ℝ) (fun x => matVecMul (A x - S • (1 : Mat d)) (u.grad x))) ≤
      ENNReal.ofReal α1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n) 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal β1 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n)
          (ENNReal.ofReal (sobStar d)).conjExponent f)
    (hgrad : ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d n)
        (1 / 4 : ℝ) u.grad) ≤
      ENNReal.ofReal α2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n) 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal β2 * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n)
          (ENNReal.ofReal (sobStar d)).conjExponent f)
    (c : ℝ) {η : Fin d → Vec d → ℝ} {Kη : ℝ≥0} (hLip : ∀ i, LipschitzWith Kη (η i))
    {Mg : ℝ} (hMg : ∀ i x, |η i x| ≤ Mg) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, ∀ x ∈ openCubeSet (originCube d n), |η i x| ≤ M) :
    |cubeAverage (originCube d n) (fun x => vecDot (matVecMul (A x) (u.grad x))
        (fun i => (u.toFun x - c) * η i x))| ≤
      (S * (α2 * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β2 * cubeLpNorm (originCube d n) (ENNReal.ofReal (sobStar d)).conjExponent f) +
          (α1 * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β1 * cubeLpNorm (originCube d n) (ENNReal.ofReal (sobStar d)).conjExponent f)) *
        (M * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u.toFun x - c) +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor (originCube d n) *
            (M * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
              Real.sqrt d * Kη * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u.toFun x - c))) := by
  classical
  have hU : IsOpen (openCubeSet (originCube d n)) := isOpen_openCubeSet _
  set w : H1Function (openCubeSet (originCube d n)) := u - ca1_const (originCube d n) c with hw
  have hwf : ∀ x, w.toFun x = u.toFun x - c := fun x => by
    simp [hw, H1Function.sub_toFun, ca1_const_toFun]
  have hwg : ∀ x, w.grad x = u.grad x := fun x => by
    simp [hw, H1Function.sub_grad, ca1_const_grad]
  let ξ : Fin d → H1Function (openCubeSet (originCube d n)) := fun i => mulLip hU w (hLip i) (hMg i)
  have hξf : ∀ i x, (ξ i).toFun x = η i x * (u.toFun x - c) := fun i x => by
    simp [ξ, mulLip, hwf]
  have hξg : ∀ i x, (ξ i).grad x = η i x • u.grad x + (u.toFun x - c) • lipGradient (η i) x :=
    fun i x => by simp [ξ, mulLip, hwf, hwg]
  have hwL : MemLp (fun x => u.toFun x - c) 2 (normalizedCubeMeasure (originCube d n)) :=
    u.memL2_normalizedCubeMeasure.sub (memLp_const c)
  have heL : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure (originCube d n)) :=
    r1_memLp_grad_eucNorm _ u
  have hΛ : ∀ i, cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (ξ i).toFun +
      2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor (originCube d n) *
        cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) ≤
      M * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u.toFun x - c) +
        2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor (originCube d n) *
          (M * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            Real.sqrt d * Kη * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u.toFun x - c)) := by
    intro i
    have hae : ∀ {P : Vec d → Prop}, (∀ x ∈ openCubeSet (originCube d n), P x) →
        ∀ᵐ x ∂(normalizedCubeMeasure (originCube d n)), P x := fun h =>
      r1_ae_normalized _ ((ae_restrict_iff' hU.measurableSet).2 (Filter.Eventually.of_forall h))
    have ha : cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (ξ i).toFun ≤
        M * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u.toFun x - c) := by
      refine ca1_cubeLpNorm_le (originCube d n) (ξ i).memL2_normalizedCubeMeasure.aestronglyMeasurable
        hwL hM0 (hae fun x hx => ?_)
      rw [hξf, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM i x hx) (abs_nonneg _)
    have hlip : ∀ x, ∀ j, |lipGradient (η i) x j| ≤ Kη := by
      intro x j
      have h1 : ‖fderiv ℝ (η i) x‖ ≤ Kη := norm_fderiv_le_of_lipschitz ℝ (hLip i)
      have h2 : ‖basisVec (d := d) j‖ = 1 := by simp [basisVec, Pi.norm_single]
      have h3 : ‖fderiv ℝ (η i) x (basisVec j)‖ ≤ Kη := by
        calc ‖fderiv ℝ (η i) x (basisVec j)‖ ≤ ‖fderiv ℝ (η i) x‖ * ‖basisVec (d := d) j‖ :=
              (fderiv ℝ (η i) x).le_opNorm _
          _ ≤ Kη := by rw [h2, mul_one]; exact h1
      simpa [lipGradient] using h3
    have hb : ∀ x ∈ openCubeSet (originCube d n), euclideanNorm ((ξ i).grad x) ≤
        M * Real.sqrt (vecNormSq (u.grad x)) + Real.sqrt d * Kη * |u.toFun x - c| := by
      intro x hx
      rw [hξg]
      change eucNorm _ ≤ _
      refine (r1_eucNorm_add_le _ _).trans ?_
      rw [ca1_eucNorm_smul, ca1_eucNorm_smul]
      have hl : eucNorm (lipGradient (η i) x) ≤ Real.sqrt d * Kη :=
        ca1_eucNorm_le_of_abs_le (by positivity) (hlip x)
      have he : eucNorm (u.grad x) = Real.sqrt (vecNormSq (u.grad x)) := rfl
      rw [he]
      have h1 : |η i x| * Real.sqrt (vecNormSq (u.grad x)) ≤ M * Real.sqrt (vecNormSq (u.grad x)) :=
        mul_le_mul_of_nonneg_right (hM i x hx) (Real.sqrt_nonneg _)
      have h2 : |u.toFun x - c| * eucNorm (lipGradient (η i) x) ≤
          |u.toFun x - c| * (Real.sqrt d * Kη) := mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      linarith only [h1, h2]
    have hG : MemLp (fun x => M * Real.sqrt (vecNormSq (u.grad x)) + Real.sqrt d * Kη * |u.toFun x - c|) 2
        (normalizedCubeMeasure (originCube d n)) :=
      (heL.const_mul M).add (hwL.norm.const_mul _)
    have hb2 : cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) ≤
        M * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          Real.sqrt d * Kη * cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u.toFun x - c) := by
      have h1 : cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => euclideanNorm ((ξ i).grad x)) ≤
          1 * cubeLpNorm (originCube d n) (2 : ℝ≥0∞)
            (fun x => M * Real.sqrt (vecNormSq (u.grad x)) + Real.sqrt d * Kη * |u.toFun x - c|) := by
        refine ca1_cubeLpNorm_le (originCube d n) ?_ hG zero_le_one (hae fun x hx => ?_)
        · exact (r1_memLp_grad_eucNorm _ (ξ i)).aestronglyMeasurable
        · have h0 : 0 ≤ euclideanNorm ((ξ i).grad x) := Real.sqrt_nonneg _
          have h5 := hb x hx
          have h6 : 0 ≤ M * Real.sqrt (vecNormSq (u.grad x)) + Real.sqrt d * Kη * |u.toFun x - c| := by
            positivity
          rw [one_mul, abs_of_nonneg h0, abs_of_nonneg h6]
          exact h5
      have h2 := Homogenization.cubeLpNorm_add_le (originCube d n) (2 : ℝ≥0∞)
        (fun x => M * Real.sqrt (vecNormSq (u.grad x))) (fun x => Real.sqrt d * Kη * |u.toFun x - c|)
        (heL.const_mul M) (hwL.norm.const_mul _) (by norm_num)
      rw [cubeLpNorm_const_mul, cubeLpNorm_const_mul] at h2
      have h3 : cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => |u.toFun x - c|) =
          cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u.toFun x - c) := by
        unfold cubeLpNorm
        simp only [← Real.norm_eq_abs]
        exact congrArg ENNReal.toReal (eLpNorm_norm (f := fun x => u.toFun x - c) hwL.aestronglyMeasurable)
      rw [h3, Real.norm_of_nonneg hM0, Real.norm_of_nonneg (by positivity)] at h2
      linarith only [h1, h2]
    have hK : 0 ≤ 2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor (originCube d n) := by
      have := cubeBesovW12EmbeddingConstant_nonneg d
      have := cubeScaleFactor_pos' (originCube d n)
      positivity
    have := mul_le_mul_of_nonneg_left hb2 hK
    linarith only [ha, this]
  have key := ca1_cube_weak_test (originCube d n) hEll hS hα1 hβ1 hα2 hβ2 u f hf ξ hflux hgrad hΛ
  have hfun : (fun x => vecDot (matVecMul (A x) (u.grad x)) (fun i => (ξ i).toFun x)) =
      fun x => vecDot (matVecMul (A x) (u.grad x)) (fun i => (u.toFun x - c) * η i x) := by
    funext x
    congr 1
    funext i
    rw [hξf, mul_comm]
  rw [hfun] at key
  exact key


theorem ca1_cube_ambient [NeZero d] (m : ℤ) (R : TriadicCube d)
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
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ openCubeSet (originCube d R.scale), ∀ i, |ca1_E a i (x + triadicCubeShift R)| ≤ M) :
    |cubeAverage R (fun x => vecDot (matVecMul (A x) (u.grad x))
        (fun i => (u.toFun x - c) * ca1_E a i x))| ≤
      (S * (α2 * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β2 * cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f) +
          (α1 * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            β1 * cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f)) *
        (M * cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c) +
          2 * cubeBesovW12EmbeddingConstant d * cubeScaleFactor R *
            (M * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) +
              Real.sqrt d * Kη * cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c))) := by
  classical
  obtain ⟨u', hu'f, hu'g, hsol⟩ := ca1_exists_shift R hRQ u hu
  obtain ⟨hflux, hgrad⟩ := hBB u' (fun x => f (x + (triadicCubeShift R))) hsol
  have hellS := ca1_elliptic_shift R hRQ hEll
  have hmeasf : AEStronglyMeasurable f (normalizedCubeMeasure R) := hf2.aestronglyMeasurable
  have hfin' : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d R.scale)
      (ENNReal.ofReal (sobStar d)).conjExponent (fun x => f (x + (triadicCubeShift R))) ≠ ⊤ := by
    rw [ca1_cubeLpENorm_shift R _ hmeasf]; exact hfin
  have hLip : ∀ i, LipschitzWith Kη (fun x : Vec d => ca1_E a i (x + (triadicCubeShift R))) := fun i =>
    LipschitzWith.of_dist_le_mul fun x y => by
      have := (hKη i).dist_le_mul (x + (triadicCubeShift R)) (y + (triadicCubeShift R))
      rwa [dist_add_right] at this
  have hMg : ∀ (i : Fin d) (x : Vec d), |ca1_E a i (x + (triadicCubeShift R))| ≤ 12 * a⁻¹ :=
    fun i x => ca1_E_abs_le_const ha i _
  have key := ca1_cube_test R.scale hellS hS hα1 hβ1 hα2 hβ2 u' (fun x => f (x + (triadicCubeShift R))) hfin' hflux hgrad c
    hLip hMg hM0 (fun i x hx => hM x hx i)
  have hT : (fun x => vecDot (matVecMul ((fun x => A (x + (triadicCubeShift R))) x) (u'.grad x))
      (fun i => (u'.toFun x - c) * ca1_E a i (x + (triadicCubeShift R)))) =
      fun x => (fun y => vecDot (matVecMul (A y) (u.grad y))
        (fun i => (u.toFun y - c) * ca1_E a i y)) (x + (triadicCubeShift R)) := by
    funext x
    simp only [hu'f, hu'g]
  have hav := cubeAverage_originCube_comp_addRight_eq R (fun y => vecDot (matVecMul (A y) (u.grad y))
    (fun i => (u.toFun y - c) * ca1_E a i y))
  rw [hT, hav] at key
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRQ
  have hG : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have hW : MemLp (fun x => u.toFun x - c) 2 (normalizedCubeMeasure R) :=
    ur.memL2_normalizedCubeMeasure.sub (memLp_const c)
  have n1 : cubeLpNorm (originCube d R.scale) (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u'.grad x))) =
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) := by
    have := ca1_cubeLpNorm_shift R (2 : ℝ≥0∞) hG.aestronglyMeasurable
    rw [← this]
    congr 1
    funext x
    simp only [hu'g]
  have n2 : cubeLpNorm (originCube d R.scale) (2 : ℝ≥0∞) (fun x => u'.toFun x - c) =
      cubeLpNorm R (2 : ℝ≥0∞) (fun x => u.toFun x - c) := by
    have := ca1_cubeLpNorm_shift R (2 : ℝ≥0∞) hW.aestronglyMeasurable
    rw [← this]
    congr 1
    funext x
    simp only [hu'f]
  have n3 : cubeLpNorm (originCube d R.scale) (ENNReal.ofReal (sobStar d)).conjExponent
      (fun x => f (x + (triadicCubeShift R))) = cubeLpNorm R (ENNReal.ofReal (sobStar d)).conjExponent f :=
    ca1_cubeLpNorm_shift R _ hmeasf
  have n4 : cubeScaleFactor (originCube d R.scale) = cubeScaleFactor R := by
    simp [cubeScaleFactor, originCube]
  rw [n1, n2, n3, n4] at key
  exact key

theorem ca1_memLp_phi_mul (Q : TriadicCube d) (a : ℝ) {g : Vec d → ℝ}
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    MemLp (fun x => ca1_phi a x * g x) 2 (normalizedCubeMeasure Q) := by
  refine MemLp.of_le_mul (c := 1) hg ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (ca1_phi_continuous (d := d) a).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · rw [norm_mul, Real.norm_of_nonneg (ca1_phi_nonneg a x), one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ca1_phi_le_one a x)

theorem ca1_memLp_of_restrict (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) : MemLp f 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem ca1_integrableOn_cubeSet {Q : TriadicCube d} {g : Vec d → ℝ}
    (hg : IntegrableOn g (openCubeSet Q) volume) : IntegrableOn g (cubeSet Q) volume := by
  unfold IntegrableOn at hg ⊢
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hg

/-- The crude inequality in normalized form. -/
theorem ca1_crude_norm [NeZero d] (m : ℤ) {lam Lam ν Λ : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A) (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hsym : ∀ x ∈ openCubeSet (originCube d m), symmPart (A x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d m), ∀ v : Vec d, eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (u : H1Function (openCubeSet (originCube d m))) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))))
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (fun _ => 0))
    {a : ℝ} (ha : 0 < a) (hat : a < 3 ^ m / 2) (c : ℝ) :
    ν * cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
        (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 ≤
      a ^ 2 / ν * cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f ^ 2 +
        (ν / a ^ 2 + 144 * d * Λ ^ 2 / (ν * a ^ 2)) *
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞) (fun x => u.toFun x - c) ^ 2 := by
  have hcr := ca1_crude m hEll hν hΛ hsym hop u hf hu ha hat c
  have hGm : MemLp (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure (originCube d m)) :=
    ca1_memLp_phi_mul (originCube d m) a (r1_memLp_grad_eucNorm (originCube d m) u)
  have hfm : MemLp f 2 (normalizedCubeMeasure (originCube d m)) := ca1_memLp_of_restrict (originCube d m) hf
  have hwm : MemLp (fun x => u.toFun x - c) 2 (normalizedCubeMeasure (originCube d m)) :=
    u.memL2_normalizedCubeMeasure.sub (memLp_const c)
  rw [ca1_cubeLpNorm_sq (originCube d m) hGm, ca1_cubeLpNorm_sq (originCube d m) hfm, ca1_cubeLpNorm_sq (originCube d m) hwm, ca1_cubeAverage_eq,
    ca1_cubeAverage_eq, ca1_cubeAverage_eq]
  have hV : 0 ≤ (cubeVolume (originCube d m))⁻¹ := inv_nonneg.2 (cubeVolume_pos (originCube d m)).le
  have e1 : ∀ x : Vec d, (ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) ^ 2 =
      ca1_Phi a x * vecNormSq (u.grad x) := by
    intro x
    rw [mul_pow, Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _),
      ← ca1_Phi_eq]
  simp only [e1]
  have := mul_le_mul_of_nonneg_left hcr hV
  linarith only [this]

/-- The integrand of the cross term of the energy identity. -/
noncomputable def ca1_T (A : CoeffField d) (u : Vec d → ℝ) (g : Vec d → Vec d) (c a : ℝ) : Vec d → ℝ :=
  fun x => vecDot (matVecMul (A x) (g x)) (fun i => (u x - c) * ca1_E a i x)

/-- The normalized energy identity. -/
theorem ca1_identity_norm [NeZero d] (m : ℤ) {lam Lam ν : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) A)
    (hsym : ∀ x ∈ openCubeSet (originCube d m), symmPart (A x) = ν • (1 : Mat d))
    (u : H1Function (openCubeSet (originCube d m))) {f : Vec d → ℝ}
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m)) u f (fun _ => 0))
    {a : ℝ} (ha : 0 < a) (hat : a < 3 ^ m / 2) (c : ℝ) :
    ν * cubeAverage (originCube d m) (fun x => ca1_Phi a x * vecNormSq (u.grad x)) =
      cubeAverage (originCube d m) (fun x => f x * (ca1_Phi a x * (u.toFun x - c))) -
        cubeAverage (originCube d m) (ca1_T A u.toFun u.grad c a) := by
  have h := ca1_energy_identity m hEll hsym u hu ha hat c
  rw [ca1_cubeAverage_eq, ca1_cubeAverage_eq, ca1_cubeAverage_eq]
  unfold ca1_T
  have hV : (cubeVolume (originCube d m))⁻¹ * (ν * ∫ x in openCubeSet (originCube d m),
      ca1_Phi a x * vecNormSq (u.grad x)) = (cubeVolume (originCube d m))⁻¹ * ((∫ x in openCubeSet (originCube d m),
        f x * (ca1_Phi a x * (u.toFun x - c))) - ∫ x in openCubeSet (originCube d m),
          vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x)) := by rw [h]
  have hT : (fun x => vecDot (matVecMul (A x) (u.grad x)) (fun i => (u.toFun x - c) * ca1_E a i x)) =
      fun x => vecDot (matVecMul (A x) (u.grad x)) ((u.toFun x - c) • fun i => ca1_E a i x) := rfl
  rw [hT]
  linarith only [hV]

end SuperdiffusionCLT.Section7
