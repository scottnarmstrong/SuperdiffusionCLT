/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.RhsLemma
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaB
public import SuperdiffusionCLT.Section7.Prereq.WellPosed
public import SuperdiffusionCLT.Section7.Prereq.FieldBridge
public import SuperdiffusionCLT.Section7.MinimalScale.TranslatedInputs
public import SuperdiffusionCLT.Section6.Lemma.Assembly
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxB

/-!
# Adding a right-hand side: the weak flux and weak gradient bounds

`l.Dirichlet.rhs.blackbox`.  The weak flux
and weak gradient bounds of the sharp-scale inputs, stated for `a`-harmonic functions, are extended
to weak solutions `u ∈ H¹` of `-∇·(a∇u) = f` on a cube, with an additional term in
`‖f‖_{L̲^{2_*}}`, `2_* = (2^*)'`.

The proof follows the print.  Let `u_z` be the `a`-harmonic function with the same boundary values
(`w0_dirichlet_exists`); then `w = u_z - u ∈ H¹₀` solves the equation with right-hand side `-f`, and
the energy estimate (`r1_energy_cube`) bounds `‖∇w‖_{L̲²}`.  The homogeneous bounds apply to `u_z`;
the differences are bounded through the subadditivity of the dual norm and its bound by the `L̲²`
norm (`RhsLemmaB`), and the `L^∞` bound of the coefficient `a - σ̄ Id` (`e.Dir.new.k.bounds`).

## Main results

* `Section7.r1_rhs_core`: the deterministic assembly on one cube.
* `Section7.r1_step`: the assembly on the translated sub-cube `y + z + □_n`.
* `Section7.r1_rhs_blackbox`: from the statement of `sharp_scale_inputs`, almost surely, for all
  `y`, the displays `e.Dir.new.flux.with.f` and `e.Dir.new.grad.with.f` for the field of
  `b2_translated_inputs`.
-/

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

theorem r1_dual_split (Q : TriadicCube d) {K : ℝ}
    (hD : ∀ F : Vec d → Vec d, (∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q)) →
      MemLp (fun x => Real.sqrt (vecNormSq (F x))) 2 (normalizedCubeMeasure Q) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (F x))))
    {Fu Fz H : Vec d → Vec d}
    (hae : Fu =ᵐ[volume.restrict (cubeSet Q)] fun x => Fz x + H x)
    (hFz : ∀ i, MemLp (fun y => Fz y i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun y => H y i) 2 (normalizedCubeMeasure Q))
    (hHn : MemLp (fun x => Real.sqrt (vecNormSq (H x))) 2 (normalizedCubeMeasure Q)) :
    ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) Fu) ≤
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) Fz) +
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (H x))) := by
  rw [Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo_eq_of_ae_eq_on_cubeSet (1 / 4) hae]
  calc _ ≤ ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) Fz +
        Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) H) :=
        ENNReal.ofReal_le_ofReal (r1_dual_vec_add_le Q hFz hH)
    _ ≤ _ := (ENNReal.ofReal_add_le).trans (add_le_add le_rfl (hD H hH hHn))


/-- The splitting `u = u_z - w` of a weak solution: `u_z` is `a`-harmonic and `w ∈ H¹₀` solves the
equation with right-hand side `-f`; the energy estimate bounds `w`. -/
theorem r1_split [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d) {nu : ℝ}, 0 < nu →
      ∀ {a : CoeffField d}, (∀ x ∈ openCubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      ∀ {lam Lam : ℝ}, IsEllipticFieldOn lam Lam (openCubeSet Q) a →
      ∀ (u : H1Function (openCubeSet Q)) (f : Vec d → ℝ),
        IsWeakSolutionOn a (openCubeSet Q) u f (fun _ => 0) →
        ∃ (v : AHarmonicFunction a (openCubeSet Q)) (w : H10Function (openCubeSet Q)),
          w.toH1Function.grad =ᵐ[volume.restrict (openCubeSet Q)]
              (fun x => v.toH1.grad x - u.grad x) ∧
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
              (fun x => Real.sqrt (vecNormSq (w.toH1Function.grad x))) ≤
            ENNReal.ofReal (C * cubeScaleFactor Q / nu) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
                (ENNReal.ofReal (sobStar d)).conjExponent f := by
  obtain ⟨C, hC, hE⟩ := r1_energy_cube hd
  refine ⟨C, hC, fun Q nu hnu a hsym lam Lam hEll u f hu => ?_⟩
  have hUo : IsOpen (openCubeSet Q) := isOpen_openCubeSet Q
  have hUb : IsBoundedDomain (openCubeSet Q) := isBoundedDomain_openCubeSet Q
  obtain ⟨uz, huz, hmem⟩ := w0_dirichlet_exists hUo hUb hEll (f := fun _ => (0 : ℝ))
    (by simp) u
  obtain ⟨v, hv⟩ := (w0_exists_aHarmonicFunction_iff a (openCubeSet Q) uz).2 huz
  subst hv
  obtain ⟨wH, hwH⟩ := hmem
  have hgr := w0_h10_grad_ae hUo u v.toH1 wH hwH
  have hweak : ∀ φ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (matVecMul (a x) (wH.toH1Function.grad x))
          (φ.toH1Function.grad x) =
        ∫ x in openCubeSet Q, (-f) x * φ.toH1Function.toFun x := by
    intro φ
    have h1 := (w0_isAHarmonicGradient_iff_isWeakSolutionOn a (openCubeSet Q) v.toH1).1
      v.isHarmonic φ
    have h2 := hu φ
    have key : ∫ x in openCubeSet Q, vecDot (matVecMul (a x) (wH.toH1Function.grad x))
          (φ.toH1Function.grad x) =
        (∫ x in openCubeSet Q, vecDot (matVecMul (a x) (v.toH1.grad x))
          (φ.toH1Function.grad x)) -
          ∫ x in openCubeSet Q, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) := by
      rw [← integral_sub (w0_integrableOn_flux hEll v.toH1 φ) (w0_integrableOn_flux hEll u φ)]
      refine integral_congr_ae ?_
      filter_upwards [hgr] with x hx
      rw [hx, sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left, vecDot_neg_left,
        ← sub_eq_add_neg]
    rw [key, h1]
    simp only [zero_mul, vecDot_zero_left, integral_zero, add_zero] at h1 h2 ⊢
    rw [h2, zero_sub, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hE' := hE Q hnu (fun x hx => hsym x hx) wH (-f) hweak
  refine ⟨v, wH, hgr, ?_⟩
  rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm_neg] at hE'
  have hLpos := r1_scaleFactor_pos Q
  calc SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (fun x => Real.sqrt (vecNormSq (wH.toH1Function.grad x)))
      = ENNReal.ofReal nu⁻¹ * (ENNReal.ofReal nu *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (wH.toH1Function.grad x)))) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hnu.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal nu⁻¹ * (ENNReal.ofReal (C * cubeScaleFactor Q) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
          (ENNReal.ofReal (sobStar d)).conjExponent f) := mul_le_mul_right hE' _
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring


theorem r1_mink_of_split [NeZero d] (Q : TriadicCube d) {a : CoeffField d}
    {u : H1Function (openCubeSet Q)}
    (v : AHarmonicFunction a (openCubeSet Q)) (wH : H10Function (openCubeSet Q))
    (hgr : wH.toH1Function.grad =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => v.toH1.grad x - u.grad x) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (wH.toH1Function.grad x))) := by
  refine r1_N2_add_le Q (z1 := v.toH1) (z2 := u) (z3 := wH.toH1Function) ?_
  filter_upwards [hgr] with x hx
  rw [hx]
  abel

theorem r1_flux_part [NeZero d] (Q : TriadicCube d) {K : ℝ} (hK : 0 ≤ K)
    (hDQ : ∀ F : Vec d → Vec d, (∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q)) →
      MemLp (fun x => Real.sqrt (vecNormSq (F x))) 2 (normalizedCubeMeasure Q) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (F x))))
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (S B Af : ℝ) (hB : 0 ≤ B) (hAf : 0 ≤ Af)
    (hAB : ∀ᵐ x ∂normalizedCubeMeasure Q,
      Book.Ch02.matrixOperatorNorm (a x - S • (1 : Mat d)) ≤ B)
    (hflux : ∀ v : AHarmonicFunction a (openCubeSet Q),
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
          (fun x => matVecMul (a x - S • (1 : Mat d)) (v.toH1.grad x))) ≤
        ENNReal.ofReal Af * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))))
    (u : H1Function (openCubeSet Q)) (v : AHarmonicFunction a (openCubeSet Q))
    (wH : H10Function (openCubeSet Q))
    (hgr : wH.toH1Function.grad =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => v.toH1.grad x - u.grad x) {X : ℝ} {G : ℝ≥0∞}
    (hEw : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (fun x => Real.sqrt (vecNormSq (wH.toH1Function.grad x))) ≤ ENNReal.ofReal X * G) :
    ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
        (fun x => matVecMul (a x - S • (1 : Mat d)) (u.grad x))) ≤
      ENNReal.ofReal Af * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal ((Af + K * B) * X) * G := by
  have hMink := r1_mink_of_split Q v wH hgr
  have hFz := r1_memLp_flux Q hEll S v.toH1
  have hFw := r1_memLp_flux Q hEll S wH.toH1Function
  have hae : (fun x => matVecMul (a x - S • (1 : Mat d)) (u.grad x)) =ᵐ[volume.restrict (cubeSet Q)]
      fun x => matVecMul (a x - S • (1 : Mat d)) (v.toH1.grad x) +
        -(matVecMul (a x - S • (1 : Mat d)) (wH.toH1Function.grad x)) := by
    filter_upwards [r1_ae_cubeSet Q hgr] with x hx
    rw [hx, sub_eq_add_neg (v.toH1.grad x) (u.grad x), matVecMul_add, matVecMul_neg]
    abel
  have hsp := r1_dual_split Q hDQ hae
    (fun i => memLp_component_of_memLp (Q := Q) _ i hFz)
    (fun i => (memLp_component_of_memLp (Q := Q) _ i hFw).neg)
    (by simp only [r1_sqrt_neg]; exact r1_memLp_eucNorm_of_memLp hFw)
  have hneg : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (-(matVecMul (a x - S • (1 : Mat d))
        (wH.toH1Function.grad x))))) =
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (matVecMul (a x - S • (1 : Mat d))
        (wH.toH1Function.grad x)))) := by
    simp only [r1_sqrt_neg]
  rw [hneg] at hsp
  have hB' := r1_enorm_flux_le Q hEll S B hB hAB wH.toH1Function
  refine hsp.trans ?_
  refine (add_le_add (hflux v) (mul_le_mul_right hB' _)).trans ?_
  refine (add_le_add (mul_le_mul_right hMink _) le_rfl).trans ?_
  refine le_trans (le_of_eq ?_) (add_le_add le_rfl (r1_ofReal_coef Af K B X hAf hK hB _ _ hEw))
  ring


theorem r1_grad_part [NeZero d] (Q : TriadicCube d) {K : ℝ} (hK : 0 ≤ K)
    (hDQ : ∀ F : Vec d → Vec d, (∀ i, MemLp (fun y => F y i) 2 (normalizedCubeMeasure Q)) →
      MemLp (fun x => Real.sqrt (vecNormSq (F x))) 2 (normalizedCubeMeasure Q) →
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) F) ≤
        ENNReal.ofReal K * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (F x))))
    {a : CoeffField d} (Ag : ℝ) (hAg : 0 ≤ Ag)
    (hgrad : ∀ v : AHarmonicFunction a (openCubeSet Q),
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
          v.toH1.grad) ≤
        ENNReal.ofReal Ag * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))))
    (u : H1Function (openCubeSet Q)) (v : AHarmonicFunction a (openCubeSet Q))
    (wH : H10Function (openCubeSet Q))
    (hgr : wH.toH1Function.grad =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => v.toH1.grad x - u.grad x) {X : ℝ} {G : ℝ≥0∞}
    (hEw : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
        (fun x => Real.sqrt (vecNormSq (wH.toH1Function.grad x))) ≤ ENNReal.ofReal X * G) :
    ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4) u.grad) ≤
      ENNReal.ofReal Ag * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
          (fun x => Real.sqrt (vecNormSq (u.grad x))) +
        ENNReal.ofReal ((Ag + K) * X) * G := by
  have hMink := r1_mink_of_split Q v wH hgr
  have hae : u.grad =ᵐ[volume.restrict (cubeSet Q)]
      fun x => v.toH1.grad x + -(wH.toH1Function.grad x) := by
    filter_upwards [r1_ae_cubeSet Q hgr] with x hx
    rw [hx]
    abel
  have hsp := r1_dual_split Q hDQ hae
    (fun i => r1_memLp_grad_comp Q v.toH1 i)
    (fun i => (r1_memLp_grad_comp Q wH.toH1Function i).neg)
    (by simp only [r1_sqrt_neg]; exact r1_memLp_grad_eucNorm Q wH.toH1Function)
  have hneg : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (-(wH.toH1Function.grad x)))) =
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (wH.toH1Function.grad x))) := by
    simp only [r1_sqrt_neg]
  rw [hneg] at hsp
  have h1 := r1_ofReal_coef Ag K 1 X hAg hK zero_le_one _ _ hEw
  simp only [ENNReal.ofReal_one, one_mul, mul_one] at h1
  refine hsp.trans ?_
  refine (add_le_add (hgrad v) le_rfl).trans ?_
  refine (add_le_add (mul_le_mul_right hMink _) le_rfl).trans ?_
  refine le_trans (le_of_eq ?_) (add_le_add le_rfl h1)
  ring


/-- **The assembly for equations with a right-hand side.**  If the flux defect and the gradient of
every `a`-harmonic function on the cube obey the two homogeneous bounds (with constants `Af`,
`Ag`) and `‖a - S Id‖_{L^∞} ≤ B`, then a weak solution `u` of `-∇·(a∇u) = f` obeys the same bounds
with the additional terms `‖f‖_{L̲^{2_*}}`. -/
theorem r1_rhs_core [NeZero d] (hd : 2 ≤ d) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (Q : TriadicCube d) {nu : ℝ}, 0 < nu →
      ∀ {a : CoeffField d}, (∀ x ∈ openCubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      ∀ {lam Lam : ℝ}, IsEllipticFieldOn lam Lam (openCubeSet Q) a →
      ∀ (S B Af Ag : ℝ), 0 ≤ B → 0 ≤ Af → 0 ≤ Ag →
      (∀ᵐ x ∂normalizedCubeMeasure Q,
        Book.Ch02.matrixOperatorNorm (a x - S • (1 : Mat d)) ≤ B) →
      (∀ v : AHarmonicFunction a (openCubeSet Q),
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
            (fun x => matVecMul (a x - S • (1 : Mat d)) (v.toH1.grad x))) ≤
          ENNReal.ofReal Af * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
            (fun x => Real.sqrt (vecNormSq (v.toH1.grad x)))) →
      (∀ v : AHarmonicFunction a (openCubeSet Q),
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
            v.toH1.grad) ≤
          ENNReal.ofReal Ag * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
            (fun x => Real.sqrt (vecNormSq (v.toH1.grad x)))) →
      ∀ (u : H1Function (openCubeSet Q)) (f : Vec d → ℝ),
        IsWeakSolutionOn a (openCubeSet Q) u f (fun _ => 0) →
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
            (fun x => matVecMul (a x - S • (1 : Mat d)) (u.grad x))) ≤
          ENNReal.ofReal Af * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
              (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            ENNReal.ofReal ((Af + K * B) * (C * cubeScaleFactor Q / nu)) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
                (ENNReal.ofReal (sobStar d)).conjExponent f ∧
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo Q (1 / 4)
            u.grad) ≤
          ENNReal.ofReal Ag * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
              (fun x => Real.sqrt (vecNormSq (u.grad x))) +
            ENNReal.ofReal ((Ag + K) * (C * cubeScaleFactor Q / nu)) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q
                (ENNReal.ofReal (sobStar d)).conjExponent f := by
  obtain ⟨C, hC, hSplit⟩ := r1_split hd
  obtain ⟨K, hK, hD⟩ := r1_ofReal_dual_le d
  refine ⟨C, K, hC, hK, fun Q nu hnu a hsym lam Lam hEll S B Af Ag hB hAf hAg hAB hflux hgrad u f hu
    => ?_⟩
  obtain ⟨v, wH, hgr, hEw⟩ := hSplit Q hnu hsym hEll u f hu
  exact ⟨r1_flux_part Q hK (fun F h1 h2 => hD Q F h1 h2) hEll S B Af hB hAf hAB hflux u v wH hgr hEw,
    r1_grad_part Q hK (fun F h1 h2 => hD Q F h1 h2) Ag hAg hgrad u v wH hgr hEw⟩


/-- The deterministic assembly on the translated sub-cube `y + z + □_n`, for the field
`ν Id + kf(y + z + ·)` on the origin cube `□_n`, with `S` the annealed diffusivity. -/
theorem r1_step [NeZero d] (hd : 2 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (C Cb : ℝ), Cb ≤ C → Cd ≤ C →
      ∀ (nu eps rho S : ℝ) (m n : ℕ) (kf : Vec d → Mat d) (y z : Vec d),
      0 < nu → 0 < eps → (1 : ℝ) ≤ m → 0 < S → 1 ≤ Cb →
      (∀ x, symmPart (nu • (1 : Mat d) + kf x) = nu • (1 : Mat d)) →
      (∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
        (fun x => nu • (1 : Mat d) + kf (y + z + x))) →
      (fun x => z + x) '' cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)) →
      ∀ X : ℝ≥0∞, ENNReal.ofReal ((m : ℝ)⁻¹) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) ∞
            (fun x => kf (y + x)) + X ≤ ENNReal.ofReal ((m : ℝ) ^ rho) →
      (∀ v : AHarmonicFunction (fun x => nu • (1 : Mat d) + kf (y + z + x))
          (openCubeSet (originCube d (n : ℤ))),
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d (n : ℤ)) (1 / 4)
            (fun x => matVecMul (nu • (1 : Mat d) + kf (y + z + x) - S • (1 : Mat d))
              (v.toH1.grad x))) ≤
          ENNReal.ofReal (Cb * Real.sqrt S * (eps * (m : ℝ) ^ (-((1 - rho) / 2)) *
              Real.log (m : ℝ)) * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
              (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) ∧
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d (n : ℤ)) (1 / 4) v.toH1.grad) ≤
          ENNReal.ofReal (Cb * (Real.sqrt S)⁻¹ * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
              (fun x => Real.sqrt (vecNormSq (v.toH1.grad x)))) →
      ∀ (u : H1Function (openCubeSet (originCube d (n : ℤ)))) (f : Vec d → ℝ),
        IsWeakSolutionOn (fun x => nu • (1 : Mat d) + kf (y + z + x))
          (openCubeSet (originCube d (n : ℤ))) u f (fun _ => 0) →
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d (n : ℤ)) (1 / 4)
            (fun x => matVecMul (nu • (1 : Mat d) + kf (y + z + x) - S • (1 : Mat d))
              (u.grad x))) ≤
          ENNReal.ofReal (C * Real.sqrt S * (eps * (m : ℝ) ^ (-((1 - rho) / 2)) *
              Real.log (m : ℝ)) * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
              (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal ((C * Real.sqrt S * (eps * (m : ℝ) ^ (-((1 - rho) / 2)) *
              Real.log (m : ℝ)) * Real.sqrt nu + C * (|nu - S| + (m : ℝ) ^ (1 + rho))) *
              (C * (3 : ℝ) ^ (n : ℤ) / nu)) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ))
              (ENNReal.ofReal (sobStar d)).conjExponent f ∧
        ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d (n : ℤ)) (1 / 4) u.grad) ≤
          ENNReal.ofReal (C * (Real.sqrt S)⁻¹ * Real.sqrt nu) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
              (fun x => Real.sqrt (vecNormSq (u.grad x))) +
          ENNReal.ofReal ((C * (Real.sqrt S)⁻¹ * Real.sqrt nu + C) *
              (C * (3 : ℝ) ^ (n : ℤ) / nu)) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ))
              (ENNReal.ofReal (sobStar d)).conjExponent f := by
  obtain ⟨C0, K0, hC0, hK0, hcore⟩ := r1_rhs_core hd
  refine ⟨max C0 K0, le_trans hC0 (le_max_left _ _), ?_⟩
  intro C Cb hCb hCd nu eps rho S m n kf y z hnu heps hm1 hS hCb1 hsymm hell himg X hkb hbul u f hu
  have hC0C : C0 ≤ C := (le_max_left _ _).trans hCd
  have hK0C : K0 ≤ C := (le_max_right _ _).trans hCd
  have hC1 : 0 ≤ C := le_trans (le_trans zero_le_one hCb1) hCb
  have hCb0 : 0 ≤ Cb := le_trans zero_le_one hCb1
  obtain ⟨lam, Lam, hl⟩ := hell
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d (n : ℤ)))
      (fun x => nu • (1 : Mat d) + kf (y + z + x)) :=
    hl.mono (isOpen_openCubeSet _).measurableSet (openCubeSet_subset_cubeSet _)
  have hsym : ∀ x ∈ openCubeSet (originCube d (n : ℤ)),
      symmPart ((fun x => nu • (1 : Mat d) + kf (y + z + x)) x) = nu • (1 : Mat d) :=
    fun x _ => hsymm _
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hδ : 0 ≤ eps * (m : ℝ) ^ (-((1 - rho) / 2)) * Real.log (m : ℝ) := by positivity
  have hsq : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have hsqn : 0 ≤ Real.sqrt nu := Real.sqrt_nonneg _
  have hB : 0 ≤ |nu - S| + (m : ℝ) ^ (1 + rho) := by positivity
  have hAf : 0 ≤ C * Real.sqrt S * (eps * (m : ℝ) ^ (-((1 - rho) / 2)) * Real.log (m : ℝ)) *
      Real.sqrt nu := by positivity
  have hAg : 0 ≤ C * (Real.sqrt S)⁻¹ * Real.sqrt nu := by positivity
  have hk := r1_ae_opnorm_k (originCube d (m : ℤ)) (g := fun x => kf (y + x)) hm1 X hkb
  have hAB0 := r1_ae_opnorm_field (originCube d (m : ℤ)) (originCube d (n : ℤ)) z himg
    (fun x => kf (y + x)) nu S _ hk
  have hAB : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (n : ℤ)),
      Book.Ch02.matrixOperatorNorm ((fun x => nu • (1 : Mat d) + kf (y + z + x)) x -
        S • (1 : Mat d)) ≤ |nu - S| + (m : ℝ) ^ (1 + rho) := by
    filter_upwards [hAB0] with x hx
    rw [← add_assoc] at hx
    exact hx
  have hflux : ∀ v : AHarmonicFunction (fun x => nu • (1 : Mat d) + kf (y + z + x))
      (openCubeSet (originCube d (n : ℤ))),
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (n : ℤ)) (1 / 4)
          (fun x => matVecMul ((fun x => nu • (1 : Mat d) + kf (y + z + x)) x - S • (1 : Mat d))
            (v.toH1.grad x))) ≤
        ENNReal.ofReal (C * Real.sqrt S * (eps * (m : ℝ) ^ (-((1 - rho) / 2)) *
            Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) := fun v =>
    (hbul v).1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCb hsq) hδ) hsqn)) _)
  have hgrad : ∀ v : AHarmonicFunction (fun x => nu • (1 : Mat d) + kf (y + z + x))
      (openCubeSet (originCube d (n : ℤ))),
      ENNReal.ofReal (Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d (n : ℤ)) (1 / 4) v.toH1.grad) ≤
        ENNReal.ofReal (C * (Real.sqrt S)⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
            (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) := fun v =>
    (hbul v).2.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb
        (inv_nonneg.2 hsq)) hsqn)) _)
  obtain ⟨h1, h2⟩ := hcore (originCube d (n : ℤ)) hnu hsym hEll S _ _ _ hB hAf hAg hAB hflux hgrad
    u f hu
  have hL : 0 ≤ (3 : ℝ) ^ (n : ℤ) := by positivity
  have hX : ∀ A : ℝ, 0 ≤ A → ∀ B : ℝ, 0 ≤ B → (A + K0 * B) * (C0 * (3 : ℝ) ^ (n : ℤ) / nu) ≤
      (A + C * B) * (C * (3 : ℝ) ^ (n : ℤ) / nu) := fun A hA B hB =>
    mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_right hK0C hB))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hL) hnu.le)
      (by positivity) (by positivity)
  have hY : ∀ A : ℝ, 0 ≤ A → (A + K0) * (C0 * (3 : ℝ) ^ (n : ℤ) / nu) ≤
      (A + C) * (C * (3 : ℝ) ^ (n : ℤ) / nu) := fun A hA =>
    mul_le_mul (add_le_add le_rfl hK0C)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hL) hnu.le)
      (by positivity) (by positivity)
  exact ⟨h1.trans (add_le_add le_rfl (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hX _ hAf _ hB)) _)),
    h2.trans (add_le_add le_rfl (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hY _ hAg)) _))⟩



/-- **Adding a right-hand side** (`l.Dirichlet.rhs.blackbox`).
The sharp-scale inputs are taken as the hypothesis. -/
theorem r1_rhs_blackbox (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ,
          0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P :
          MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
          SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0
          omega) ∧ Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ᵐ
          omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
          omega ≤ (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m
          → (∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ)) → Homogenization.HomogenizationErrorOnCube
          (Homogenization.originCube d (n : ℤ)) (1 / 9) Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 2) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 :
          Homogenization.Mat d)) ≤ ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
          Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) + SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
          (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ)) (1 / 4)
          (Homogenization.MultiscaleExponent.finite 1) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)))⁻¹ ≤ C ∧ (∀ u : Homogenization.AHarmonicFunction (fun x => nu • (1 :
          Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n :
          ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n :
          ℤ))), ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1
          : Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          omega (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^
          ((n : ℤ) - 3) * (k i : ℝ)) + x) -
          SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P • (1 : Homogenization.Mat
          d)) (u.toH1.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1
          - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧ ENNReal.ofReal
          (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
          (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤ ENNReal.ofReal (C *
          (Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ *
          Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
          (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq
          (u.toH1.grad x))) ∧ ∃ w : Homogenization.AHarmonicFunction (fun _ => (1 :
          Homogenization.Mat d)) (Homogenization.openCubeSet (Homogenization.originCube d ((n : ℤ) -
          1))), ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d ((n : ℤ) -
          1)) 2 (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤ ENNReal.ofReal (C * (ε * (m : ℝ) ^
          (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * (Real.sqrt
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2
          (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧ Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaCoarse (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) + Homogenization.matNorm
          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ •
          Homogenization.sigmaStarCoarse (Homogenization.cubeSet (Homogenization.originCube d (n :
          ℤ))) (fun x => nu • (1 : Homogenization.Mat d) +
          SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.cubeSet
          (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) +
          x)) - 1) ≤ C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧ ENNReal.ofReal ((m :
          ℝ)⁻¹) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (m
          : ℤ)) ∞ (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) + ENNReal.ofReal ((3 : ℝ)
          ^ (-((1 / 4 : ℝ) * (m : ℝ)))) * SuperdiffusionCLT.Section2.Norms.matHatNegENorm
          (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤ ENNReal.ofReal ((m : ℝ)
          ^ ρ)) :
  ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ, ∀ ε ρ M : ℝ, 0 < ε
    → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M → ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : MeasureTheory.ProbabilityMeasure
    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (hPrefix :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ2 :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 → ∃ X0 :
    SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
    Homogenization.IndependentSums.IsBigO P.toMeasure (Homogenization.IndependentSums.gammaSigma ρ)
    (fun omega => Real.log (X0 omega)) Lhat ∧ ∀ y : Homogenization.Vec d, ∀ᵐ omega :
    SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure, ∀ m n : ℕ, X0
    (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega) ≤ (3 : ℝ) ^ m →
    Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) → n ≤ m → (∀ k : Fin d → ℤ, (fun x
    => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) '' Homogenization.cubeSet
    (Homogenization.originCube d (n : ℤ)) ⊆ Homogenization.cubeSet (Homogenization.originCube d (m :
    ℤ)) → ∀ (u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d
    (n : ℤ)))) (f : Homogenization.Vec d → ℝ), SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun
    x => nu • (1 : Homogenization.Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega (Homogenization.translateSet
    y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) (y + (fun i => (3 : ℝ) ^ ((n :
    ℤ) - 3) * (k i : ℝ)) + x)) (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))) u
    f (fun _ => 0) → (ENNReal.ofReal
    (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    (Homogenization.originCube d (n : ℤ)) (1 / 4) (fun x => Homogenization.matVecMul (nu • (1 :
    Homogenization.Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
    (Homogenization.translateSet y (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))))
    (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Homogenization.Mat d))
    (u.grad x))) ≤ ENNReal.ofReal (C * Real.sqrt
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) /
    2)) * Real.log (m : ℝ)) * Real.sqrt nu) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    (Homogenization.originCube d (n : ℤ)) 2 (fun x => Real.sqrt (Homogenization.vecNormSq (u.grad
    x))) + ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
    nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu + C * (|nu -
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| + (m : ℝ) ^ (1 + ρ))) * (C *
    (3 : ℝ) ^ (n : ℤ) / nu)) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    (Homogenization.originCube d (n : ℤ)) (ENNReal.ofReal (SuperdiffusionCLT.Section7.sobStar
    d)).conjExponent f) ∧ (ENNReal.ofReal
    (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    (Homogenization.originCube d (n : ℤ)) (1 / 4) u.grad) ≤ ENNReal.ofReal (C * (Real.sqrt
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu) *
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (Homogenization.originCube d (n : ℤ)) 2 (fun x
    => Real.sqrt (Homogenization.vecNormSq (u.grad x))) + ENNReal.ofReal ((C * (Real.sqrt
    (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P))⁻¹ * Real.sqrt nu + C) * (C *
    (3 : ℝ) ^ (n : ℤ) / nu)) * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    (Homogenization.originCube d (n : ℤ)) (ENNReal.ofReal (SuperdiffusionCLT.Section7.sobStar
    d)).conjExponent f)) := by
  obtain ⟨Cb, hCb, H⟩ := b2_translated_inputs d hInputs
  obtain ⟨Cd, hCd, hstep⟩ := r1_step hd
  refine ⟨max Cb Cd, le_trans hCb (le_max_left _ _), ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1 hCM
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1
    ((le_max_left _ _).trans hCM)
  refine ⟨Lhat, hL, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, fun y => ?_⟩
  have hqmp := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving
  filter_upwards [hae y, hqmp.ae (Section6.l9_ae_exists_ell_centered hJ3 hnu)] with omega hω hell m n
    hX hLm hn1 hn2 k himg u f hu
  obtain ⟨hA, hkb⟩ := hω m n hX hLm hn1 hn2
  obtain ⟨-, -, hbul, -⟩ := hA k himg
  have hm1 : (1 : ℝ) ≤ m := hL.trans hLm
  have hσ := SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4
  obtain ⟨lam, Lam, hl⟩ := hell m n (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ))
  have hfield : (fun x : Homogenization.Vec d => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
          (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega)
          (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) =
      fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
          (Homogenization.translateSet y
            (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))))
          (y + (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) := by
    funext x
    rw [b2_csf_translate_apply, b2_add_assoc_aux]
  rw [hfield] at hl
  exact hstep (max Cb Cd) Cb (le_max_left _ _) (le_max_right _ _) nu ε ρ _ m n _ y (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) hnu hε
    hm1 hσ hCb (fun x => Section6.HarmonicApprox.symmPart_centeredStreamField_add nu omega _ x)
    ⟨lam, Lam, hl⟩ himg _ hkb (fun v => ⟨(hbul v).1, (hbul v).2.1⟩) u f hu


end SuperdiffusionCLT.Section7
