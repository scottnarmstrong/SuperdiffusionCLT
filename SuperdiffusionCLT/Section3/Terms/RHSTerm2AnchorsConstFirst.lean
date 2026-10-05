/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2DecouplingC

/-!
# `l.RHS.term2` at the glued proxy, with the cube Poincaré step proved

`l_RHS_term2_constFirst` of `RHSTerm2Glued` states `e.RHS.term2` in the
manuscript's own quantifier order — one `C`, then every admissible shell law,
scale selection, direction and response field — and the two anchor reductions
built from it, `l_RHS_term2_of_anchors` of `RHSTerm2DecouplingB` and
`l_RHS_term2_of_anchors_glued` of `RHSTerm2DecouplingC`, keep that order:
both conclude `∃ C : ℝ, 1 ≤ C ∧ ∀ (nu : ℝ), … ∀ (P : ProbabilityMeasure …), …
∀ (S : ScaleSelection), … ∀ (e : Vec d), …`, with only the dimension, the
three input constants and their lower bounds standing before the existential.
Nothing needs restating.

This module discharges two more of the four hypotheses that
`l_RHS_term2_of_anchors_glued` still carries.

* `hPoincare`, the step `l.RHS.term2#poincare-per-cube` on
  each scale-`n` sub-cube of `cu_m`.  `poincare_per_cube` of
  `RHSTerm2Displays` proves it on one triadic cube from the
  coercive estimate `Homogenization.scaledTranslatedCubeMeanZeroH1CoerciveEstimate`,
  but it asks for the `H¹` datum of the `d` components of the field *on that
  cube*.  `componentH1OnSubcube` builds that datum from the data the rendered
  statement already carries on the large cube: `MemVectorL2` of `R` and `MemLp`
  of its Jacobian restrict to a sub-cube (`memVectorL2_subcube`,
  `memLp_subcube`), the entry of a `HilbertMat`-valued `L²` field is `L²`
  (`HilbertMat.entryL`), and a weak gradient restricts to an open subset
  (`HasWeakGradientOn.restrict`).  `poincare_per_subcube` is the result, at the
  constant `termTwoPoincareConst d · 3^n` of the paper, where
  `termTwoPoincareConst d` is the coercive constant of the centred unit cube
  and `3^n = cubeScaleFactor z` is the side length of the sub-cubes.
* `hRint`, integrability in the sample of the cube means of `R`.  The statement
  already carries the measurability sentence `hRmeas` of the paper on
  those means, and the sub-`σ`-field `F_> = σ(j_r : r > ℓ)` is coarser than the
  ambient one (`highShellSigma_le`), so the means are genuinely measurable; and
  it carries `hfinR`, finiteness of the annealed squared cube norm of `R` on
  `cu_m`.  Jensen on a sub-cube
  (`ofReal_vecNormSq_volumeAverageVec_le`) and the sub-cube decomposition of
  the squared normalized norm (`vecCubeLpENorm_subcube_sq_le`) bound the mean
  by the large-cube norm, and on a probability space `a ≤ 1 + a²` turns the
  square-integrable bound into an integrable one.

## The remaining hypotheses

`hRmeas` and `hTmeas`, the printed measurability sentence of the paper
read on the two cube mean vectors.  `R = (k_{L'} − k_ℓ)ᵗ∇w` is built from the
Dirichlet response `w`, a free binder of the rendered statement given only by
`IsDirichletResponse`, so nothing in the statement records how `w` depends on
the shells; and for the glued proxy the cube pieces come from
`Book.Ch02.responseExistenceTheory` through a choice (see `qVector_apply` of
`GluedField`), so no declaration gives joint measurability in
`omega` for it either.  These are the range-of-dependence facts the paper
asserts and never proves.

## Main results

* `componentH1OnSubcube`, `poincare_per_subcube`: the cube Poincaré step
  on every scale-`n` sub-cube of `cu_m`, from large-cube data.
* `highShellSigma_le`, `vecCubeLpENorm_subcube_sq_le`,
  `integrable_volumeAverageVec_apply`: the integrability of the cube means.
* `l_RHS_term2_of_anchors_constFirst`: `l_RHS_term2_of_anchors_glued` with
  `hPoincare` and `hRint` discharged, still constant-first.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open ProbabilityTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cube Poincaré step on a sub-cube -/

/-- The `H¹` datum on a scale-`n` sub-cube of `cu_m` of one component of a
vector field that is `L²` on `cu_m`, has an `L²` Jacobian there and has that
Jacobian as its weak gradient.  This is what `poincare_per_cube` asks for at
`Q = z`, assembled from the large-cube data the rendered statement of
`l.RHS.term2` carries. -/
def componentH1OnSubcube {n m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d n m) {F : Vec d → Vec d}
    {DF : Fin d → Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) F)
    (hDF : MemLp (fun x => HilbertMat.ofMat (fun i j => DF i x j)) 2
      (volume.restrict (openCubeSet (originCube d (m : ℤ)))))
    (hweak : ∀ i, HasWeakGradientOn (openCubeSet (originCube d (m : ℤ)))
      (fun x => F x i) (DF i))
    (i : Fin d) : H1Function (openCubeSet z) where
  toFun := fun x => F x i
  grad := DF i
  memL2 := memL2On_component_of_memVectorL2 (memVectorL2_subcube hz hF) i
  gradMemL2 := by
    intro j
    have hcomp := (HilbertMat.entryL i j).comp_memLp' (memLp_subcube hz hDF)
    exact hcomp
  hasWeakGradient :=
    (hweak i).restrict (isOpen_openCubeSet z)
      (openCubeSet_subset_of_mem_descendantsAtDepth hz)

/-- The constant of `l.RHS.term2#poincare-per-cube`: the coercive constant of
the centred unit cube, which `poincare_per_cube` scales by the side length of
the cube it is applied on. -/
def termTwoPoincareConst (d : ℕ) : ℝ :=
  (originCubeMeanZeroH1CoerciveEstimate d 0).constant

theorem termTwoPoincareConst_nonneg (d : ℕ) : 0 ≤ termTwoPoincareConst d :=
  (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg

/-- **`l.RHS.term2#poincare-per-cube` on every scale-`n` sub-cube of `cu_m`**, from the large-cube
data alone: the constant is `termTwoPoincareConst d · 3^n`, the side length
`3^n` being `cubeScaleFactor z` for every member `z` of the family. -/
theorem poincare_per_subcube {n m : ℕ} (hnm : n ≤ m)
    {F : Vec d → Vec d} {DF : Fin d → Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) F)
    (hDF : MemLp (fun x => HilbertMat.ofMat (fun i j => DF i x j)) 2
      (volume.restrict (openCubeSet (originCube d (m : ℤ)))))
    (hweak : ∀ i, HasWeakGradientOn (openCubeSet (originCube d (m : ℤ)))
      (fun x => F x i) (DF i)) :
    ∀ z ∈ largeCubeSubcubes d n m,
      vecCubeLpENorm z 2 (fun x => F x - volumeAverageVec (openCubeSet z) F) ≤
        ENNReal.ofReal (termTwoPoincareConst d * (3 : ℝ) ^ ((n : ℕ) : ℝ)) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2
            (fun x => HilbertMat.ofMat (fun i j => DF i x j)) := by
  intro z hz
  have hscale : cubeScaleFactor z = (3 : ℝ) ^ ((n : ℕ) : ℝ) := by
    rw [cubeScaleFactor, scale_of_mem_largeCubeSubcubes hnm hz, zpow_natCast,
      Real.rpow_natCast]
  have h := poincare_per_cube (Q := z) (F := F) (DF := DF)
    (componentH1OnSubcube hz hF hDF hweak) (fun _ => rfl) (fun _ => rfl)
  rw [hscale] at h
  rw [mul_comm (termTwoPoincareConst d)]
  exact h

/-! ## Integrability in the sample of the cube means of `R` -/

/-- `F_> = σ(j_r : r > ℓ)` is coarser than the ambient `σ`-field of the shell
sequence, so an `F_>`-measurable observable is measurable. -/
theorem highShellSigma_le (d ell : ℕ) :
    highShellSigma d ell ≤ (inferInstance : MeasurableSpace (ShellSeq d)) :=
  iSup₂_le fun r _ => shellCoordSigma_le r

private theorem le_one_add_sq (a : ℝ≥0∞) : a ≤ 1 + a ^ (2 : ℕ) := by
  rcases le_total a 1 with h | h
  · exact le_trans h le_self_add
  · calc a = a * 1 := (mul_one a).symm
      _ ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ (2 : ℕ) := (pow_two a).symm
      _ ≤ 1 + a ^ (2 : ℕ) := le_add_self

/-- The squared normalized `L̲²` norm on one scale-`n` sub-cube is at most the
number of sub-cubes times the squared normalized norm on `cu_m`: one summand of
the sub-cube decomposition `cubeLpENorm_two_sq_eq_inv_card_mul_sum`. -/
theorem vecCubeLpENorm_subcube_sq_le {n m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d n m) (F : Vec d → Vec d) :
    vecCubeLpENorm z 2 F ^ (2 : ℕ) ≤
      ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)) *
        vecCubeLpENorm (originCube d (m : ℤ)) 2 F ^ (2 : ℕ) := by
  classical
  have hsplit := cubeLpENorm_two_sq_eq_inv_card_mul_sum
    (Q := originCube d (m : ℤ)) (m - n) (hilbertifyVecField F)
  rw [show descendantsAtDepth (originCube d (m : ℤ)) (m - n) =
    largeCubeSubcubes d n m from rfl] at hsplit
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d n m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 (largeCubeSubcubes_nonempty d n m)
  have hone : ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)) *
      ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ))⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hcardpos),
      mul_inv_cancel₀ (ne_of_gt hcardpos), ENNReal.ofReal_one]
  calc vecCubeLpENorm z 2 F ^ (2 : ℕ)
      ≤ ∑ R ∈ largeCubeSubcubes d n m,
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm R 2
            (hilbertifyVecField F) ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun R =>
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm R 2
            (hilbertifyVecField F) ^ (2 : ℕ)) (fun _ _ => zero_le) hz
    _ = ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)) *
          (ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ))⁻¹ *
            ∑ R ∈ largeCubeSubcubes d n m,
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm R 2
                (hilbertifyVecField F) ^ (2 : ℕ)) := by
        rw [← mul_assoc, hone, one_mul]
    _ = ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)) *
          vecCubeLpENorm (originCube d (m : ℤ)) 2 F ^ (2 : ℕ) := by
        rw [show vecCubeLpENorm (originCube d (m : ℤ)) 2 F =
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (m : ℤ)) 2
            (hilbertifyVecField F) from rfl, hsplit]

/-- **The cube means of an annealed-`L²` field are integrable in the sample.**
Measurability is the hypothesis; the bound is Jensen on the sub-cube followed by
the sub-cube decomposition, and `a ≤ 1 + a²` on the probability space. -/
theorem integrable_volumeAverageVec_apply {n m : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)} {Rf : ShellSeq d → Vec d → Vec d}
    (hRL2 : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (Rf omega))
    (hfin : (∫⁻ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (m : ℤ)) 2 (Rf omega) ^ (2 : ℕ)
        ∂P.toMeasure) ≠ ⊤)
    {z : TriadicCube d} (hz : z ∈ largeCubeSubcubes d n m)
    (hmeas : Measurable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet z) (Rf omega)))
    (i : Fin d) :
    Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet z) (Rf omega) i)
      P.toMeasure := by
  classical
  set c : ℝ≥0∞ := ENNReal.ofReal (((largeCubeSubcubes d n m).card : ℝ)) with hc
  have hbound : ∀ omega : ShellSeq d,
      ‖volumeAverageVec (openCubeSet z) (Rf omega) i‖ₑ ≤
        1 + c * vecCubeLpENorm (originCube d (m : ℤ)) 2 (Rf omega) ^ (2 : ℕ) := by
    intro omega
    set v : Vec d := volumeAverageVec (openCubeSet z) (Rf omega) with hv
    have hsq : ‖v i‖ₑ ^ (2 : ℕ) ≤ ENNReal.ofReal (vecNormSq v) := by
      have hle : |v i| ≤ vecNorm v := abs_apply_le_vecNorm v i
      calc ‖v i‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (|v i|) ^ (2 : ℕ) := by
            rw [← ofReal_norm, Real.norm_eq_abs]
        _ = ENNReal.ofReal (|v i| ^ (2 : ℕ)) :=
            (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
        _ ≤ ENNReal.ofReal (vecNorm v ^ (2 : ℕ)) :=
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) hle 2)
        _ = ENNReal.ofReal (vecNormSq v) := by rw [vecNorm_sq_eq_vecNormSq]
    have hjen : ENNReal.ofReal (vecNormSq v) ≤
        vecCubeLpENorm z 2 (Rf omega) ^ (2 : ℕ) :=
      ofReal_vecNormSq_volumeAverageVec_le (memVectorL2_subcube hz (hRL2 omega))
    have hsub := vecCubeLpENorm_subcube_sq_le hz (Rf omega)
    exact le_trans (le_one_add_sq _)
      (add_le_add le_rfl (le_trans (le_trans hsq hjen) hsub))
  refine ⟨((measurable_pi_apply i).comp hmeas).aestronglyMeasurable, ?_⟩
  have hmono : (∫⁻ omega : ShellSeq d,
        ‖volumeAverageVec (openCubeSet z) (Rf omega) i‖ₑ ∂P.toMeasure) ≤
      ∫⁻ omega : ShellSeq d,
        (1 + c * vecCubeLpENorm (originCube d (m : ℤ)) 2 (Rf omega) ^ (2 : ℕ))
          ∂P.toMeasure := lintegral_mono hbound
  have hsplit : (∫⁻ omega : ShellSeq d,
        (1 + c * vecCubeLpENorm (originCube d (m : ℤ)) 2 (Rf omega) ^ (2 : ℕ))
          ∂P.toMeasure) =
      1 + c * ∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (m : ℤ)) 2 (Rf omega) ^ (2 : ℕ)
          ∂P.toMeasure := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ,
      mul_one, lintegral_const_mul' _ _ (by rw [hc]; exact ENNReal.ofReal_ne_top)]
  refine lt_of_le_of_lt hmono ?_
  rw [hsplit]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
    ENNReal.mul_lt_top (by rw [hc]; exact ENNReal.ofReal_lt_top)
      (lt_of_le_of_ne le_top hfin)⟩

/-! ## `l.RHS.term2` with `hPoincare` and `hRint` discharged -/

/-- **`l_RHS_term2_of_anchors_glued` with the cube Poincaré step and the
integrability of the cube means of `R` discharged**

The quantifier order is the paper's own and is the one of
`l_RHS_term2_constFirst`: the dimension, the three input constants `C₁ C₂ C₃`
and their lower bounds stand first, then one `C`, and only then the scale `nu`,
the shell law `P`, the scale selection `S`, the direction `e`, the response
field `w` and the glued fields.  The Poincaré constant `Cpoin` of
`l_RHS_term2_of_anchors_glued` is gone from the statement, having been fixed to
`termTwoPoincareConst d`.

Every binder of `l_RHS_term2_of_anchors_glued` stands, in the same order, except
`hPoincare` and `hRint`, which the proof supplies from `poincare_per_subcube`
and `integrable_volumeAverageVec_apply`.  The two measurability hypotheses
`hRmeas` and `hTmeas` remain; the module docstring records why. -/
theorem l_RHS_term2_of_anchors_constFirst (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ C₂ C₃ : ℝ) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hC₃ : 1 ≤ C₃) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (p : Vec d), p = testVector nu S.LPrime P S.n e →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) →
      ∀ (uNGlued : ShellSeq d → Vec d → Vec d) (DR : ShellSeq d → Fin d → Vec d → Vec d),
        (∀ omega : ShellSeq d, ∀ i : Fin d,
          HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                  (coefficientCutoff nu omega S.ell).toCoeffField x)
                ((w omega).toH1Function.grad x)) i) (DR omega i)) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                (originCube d (S.m : ℤ)) 2
                (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                  (coefficientCutoff nu omega S.ell).toCoeffField x)
                  ((w omega).toH1Function.grad x)) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
          (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
            (∫⁻ omega : ShellSeq d,
                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                    (originCube d (S.m : ℤ)) 2
                    (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p)) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (S.m : ℤ)) 2
                  (fun x => uNGlued omega x -
                    gluedGradientField hnu S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
          Real.sqrt (vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) - p)) ≤
          C₂ * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
            (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (S.m : ℤ)) 2
                  (fun x => gluedGradientField hnu S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x -
                    annealedGluedAverage hnu P S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e)) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          C₃ * nu ^ (-(1 : ℝ)) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
      ∀ (Rfield : ShellSeq d → Vec d → Vec d),
        (∀ (omega : ShellSeq d) (y : Vec d), Rfield omega y =
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y)) →
      ∀ (DRmat : ShellSeq d → Vec d → HilbertMat d),
        (∀ (omega : ShellSeq d) (x : Vec d), DRmat omega x =
          HilbertMat.ofMat (fun i j => DR omega i x j)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (Rfield omega)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (uNGlued omega)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
            (gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega)) →
        (∀ omega : ShellSeq d,
          MemLp (DRmat omega) 2
            (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega) ^ (2 : ℕ)
            ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uNGlued omega x - gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e)) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uNGlued omega x - gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (uNGlued omega y - gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e)))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) - p))) P.toMeasure) →
        (∀ z ∈ largeCubeSubcubes d S.n S.m,
          Measurable[highShellSigma d S.ell]
            (fun omega : ShellSeq d =>
              volumeAverageVec (openCubeSet z) (Rfield omega))) →
        (∀ z ∈ largeCubeSubcubes d S.n S.m,
          Measurable[lowShellSigma d S.ell]
            (fun omega : ShellSeq d =>
              volumeAverageVec (openCubeSet z)
                (gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega))) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (uNGlued omega y - p))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2))
    := by
  obtain ⟨C, hC1, hC⟩ := l_RHS_term2_of_anchors_glued d hd C₁ C₂ C₃
    (termTwoPoincareConst d) hC₁ hC₂ hC₃ (termTwoPoincareConst_nonneg d)
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
    uNGlued DR hDR hRb hPe hPen Rfield hRfield DRmat hDRmat
    hRL2 hUL2 hUtL2 hDRL2 hfinR hfinDR hfinDiff hfinProx hmR hmDR hmDiff hmProx
    hIntDiff hIntProxy hIntMean hRmeas hTmeas
  have hnm : S.n ≤ S.m := hSorder.mem_pigeon_range.1.2
  have hDRmatEq : ∀ omega : ShellSeq d,
      DRmat omega = fun x => HilbertMat.ofMat (fun i j => DR omega i x j) :=
    fun omega => funext (hDRmat omega)
  have hRweak : ∀ (omega : ShellSeq d) (i : Fin d),
      HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => Rfield omega x i) (DR omega i) := by
    intro omega i
    have hfun : (fun x => Rfield omega x i) =
        fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
            (coefficientCutoff nu omega S.ell).toCoeffField x)
          ((w omega).toH1Function.grad x)) i := by
      funext x
      rw [hRfield omega x]
    rw [hfun]
    exact hDR omega i
  have hPoincare : ∀ (omega : ShellSeq d), ∀ z ∈ largeCubeSubcubes d S.n S.m,
      vecCubeLpENorm z 2
          (fun x => Rfield omega x -
            volumeAverageVec (openCubeSet z) (Rfield omega)) ≤
        ENNReal.ofReal (termTwoPoincareConst d * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 (DRmat omega) := by
    intro omega z hz
    have hDRLp : MemLp (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) 2
        (volume.restrict (openCubeSet (originCube d (S.m : ℤ)))) := by
      rw [← hDRmatEq omega]
      exact hDRL2 omega
    have h := poincare_per_subcube hnm (hRL2 omega) hDRLp (hRweak omega) z hz
    rw [hDRmatEq omega]
    exact h
  have hRint : ∀ z ∈ largeCubeSubcubes d S.n S.m, ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet z) (Rfield omega) i) P.toMeasure := by
    intro z hz i
    exact integrable_volumeAverageVec_apply hRL2 hfinR hz
      ((hRmeas z hz).mono (highShellSigma_le d S.ell) le_rfl) i
  exact hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
    uNGlued DR hDR hRb hPe hPen Rfield hRfield DRmat hDRmat
    hRL2 hUL2 hUtL2 hDRL2 hfinR hfinDR hfinDiff hfinProx hmR hmDR hmDiff hmProx
    hIntDiff hIntProxy hIntMean hPoincare hRmeas hTmeas hRint

end

end SuperdiffusionCLT.Section3.Terms
