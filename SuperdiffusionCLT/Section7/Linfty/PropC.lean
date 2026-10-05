/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.PropB

/-!
# The `L^∞` homogenization proposition

`linf_prop_of_smooth`: the text of the binder `hLinf` of `s5_superdiffusivity`, from the
inputs and the proposition for a smooth datum. Almost surely, the field is the centred field plus a
constant skew matrix, and the problem for `g` is compared with the problem for a mollified `g̃` at
the scale `3^{n_C}`, whose errors are absorbed by the polynomial scale separation.
-/

@[expose] public section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A weak solution for `a` is one for `b = a + K0`, `K0` a constant skew matrix, when `b` is
elliptic on `W`. -/
theorem linf_weak_transfer {W : Set (Vec d)} (hWo : IsOpen W)
    [IsFiniteMeasure (volumeMeasureOn W)] {a b : CoeffField d} {K0 : Mat d}
    (hK0 : matTranspose K0 = -K0) (hKx : ∀ x, b x = a x + K0) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W b) (w : H1Function W) (f : Vec d → ℝ) :
    IsWeakSolutionOn a W w f (fun _ => 0) ↔ IsWeakSolutionOn b W w f (fun _ => 0) := by
  have hfl : MemVectorL2 W (fun x => matVecMul (b x) (w.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.grad_memVectorL2
  have hflux : MemVectorL2 W (fun x => matVecMul (a x) (w.grad x)) := by
    have h2 := hfl.sub (SuperdiffusionCLT.Section2.CoarseGraining.memVectorL2_matVecMul_const
      K0 w.grad_memVectorL2)
    have e : (fun x => matVecMul (a x) (w.grad x)) =
        ((fun x => matVecMul (b x) (w.grad x)) - fun x => matVecMul K0 (w.grad x)) := by
      funext x
      rw [Pi.sub_apply]
      rw [hKx x, add_matVecMul]
      abel
    rw [e]
    exact h2
  exact (isWeakSolutionOn_congr_const_skew hWo hK0 hKx hflux).symm

/-- The scale `nK C n` is nonincreasing in `C`. -/
theorem linf_nK_anti {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) (n : ℕ) : nK C₂ n ≤ nK C₁ n := by
  unfold nK
  have hl : 0 ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · exact Real.log_nonneg (by exact_mod_cast h0)
  have := Nat.ceil_mono (mul_le_mul_of_nonneg_right h hl)
  omega

private theorem linf_pc_real {Cs Cg Kc C D S Lg T F G' : ℝ} (hCs : 0 ≤ Cs) (hCg : 0 ≤ Cg)
    (hKc : 0 ≤ Kc) (hD : 0 ≤ D) (hS : 0 ≤ S) (hLg : 0 ≤ Lg) (hT : 0 ≤ T) (hF : 0 ≤ F)
    (hG : 0 ≤ G') (hCsCg : Cs * Cg + Kc ≤ C) (hCs_le : Cs ≤ C) :
    0 ≤ Cs * D * S * F ∧ 0 ≤ Cs * D * (Lg * T * (Cg * G')) ∧ 0 ≤ Kc * (D * Lg * T) * G' ∧
      Cs * D * (S * F + Lg * T * (Cg * G')) =
        Cs * D * S * F + Cs * D * (Lg * T * (Cg * G')) ∧
      Cs * D * (Lg * T * (Cg * G')) + Kc * (D * Lg * T) * G' ≤ C * D * Lg * T * G' ∧
      Cs * D * S * F ≤ C * D * S * F := by
  have hZ : 0 ≤ D * Lg * T * G' := by positivity
  have hP : 0 ≤ D * S * F := by positivity
  refine ⟨by positivity, by positivity, by positivity, by ring, ?_, ?_⟩
  · calc _ = (Cs * Cg + Kc) * (D * Lg * T * G') := by ring
      _ ≤ C * (D * Lg * T * G') := mul_le_mul_of_nonneg_right hCsCg hZ
      _ = _ := by ring
  · calc _ = Cs * (D * S * F) := by ring
      _ ≤ C * (D * S * F) := mul_le_mul_of_nonneg_right hCs_le hP
      _ = _ := by ring

/-- **`p.Dirichlet.Linfty.blackbox`**, from the inputs `hInputs`, `hS5` and
the proposition for a smooth datum `hSmooth`, whose constant can be taken as large as needed: the
text of the binder `hLinf` of `s5_superdiffusivity`. -/
theorem linf_prop_of_smooth (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hInputs :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
        ∃ Lhat : ℝ, 1 ≤ Lhat ∧
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
        Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ρ)
        (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
        ∀ m n : ℕ,
        X0 omega ≤ (3 : ℝ) ^ m →
        Lhat ≤ (m : ℝ) →
        (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
        n ≤ m →
        (∀ k : Fin d → ℤ,
        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
        -- e.Dir.new.full.good
        Homogenization.HomogenizationErrorOnCube
        (Homogenization.originCube d (n : ℤ)) (1 / 9)
        Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 2)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
        (1 : Homogenization.Mat d)) ≤
        ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ) ∧
        -- e.Dir.new.reg.ellipticity
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)⁻¹ *
        Homogenization.LambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) +
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P *
        (Homogenization.lambdaSq (Homogenization.originCube d (n : ℤ))
        (1 / 4) (Homogenization.MultiscaleExponent.finite 1)
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)))⁻¹ ≤
        C ∧
        -- e.Dir.new.weak.flux, e.Dir.new.weak.grad, e.Dir.new.harmonic.approx
        (∀ u : Homogenization.AHarmonicFunction
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
        (Homogenization.openCubeSet (Homogenization.originCube d (n : ℤ))),
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4)
        (fun x => Homogenization.matVecMul
        (nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) -
        SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P • (1 : Homogenization.Mat d))
        (u.toH1.grad x))) ≤
        ENNReal.ofReal
        (C *
        Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ENNReal.ofReal
        (Homogenization.Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
        (Homogenization.originCube d (n : ℤ)) (1 / 4) u.toH1.grad) ≤
        ENNReal.ofReal
        (C *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x => Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x))) ∧
        ∃ w : Homogenization.AHarmonicFunction
        (fun _ => (1 : Homogenization.Mat d))
        (Homogenization.openCubeSet
        (Homogenization.originCube d ((n : ℤ) - 1))),
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d ((n : ℤ) - 1)) 2
        (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
        ENNReal.ofReal
        (C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) *
        (Real.sqrt
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P))⁻¹ *
        Real.sqrt nu) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (n : ℤ)) 2
        (fun x =>
        Real.sqrt (Homogenization.vecNormSq (u.toH1.grad x)))) ∧
        -- e.Dir.new.sstar.close
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) +
        Homogenization.matNorm
        ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
        nu m P)⁻¹ •
        Homogenization.sigmaStarCoarse
        (Homogenization.cubeSet
        (Homogenization.originCube d (n : ℤ)))
        (fun x => nu • (1 : Homogenization.Mat d) +
        SuperdiffusionCLT.Section2.Carriers.centeredStreamField
        omega
        (Homogenization.cubeSet
        (Homogenization.originCube d (m : ℤ)))
        ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x)) -
        1) ≤
        C * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ))) ∧
        -- e.Dir.new.k.bounds
        ENNReal.ofReal ((m : ℝ)⁻¹) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (Homogenization.originCube d (m : ℤ)) ∞
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) +
        ENNReal.ofReal ((3 : ℝ) ^ (-((1 / 4 : ℝ) * (m : ℝ)))) *
        SuperdiffusionCLT.Section2.Norms.matHatNegENorm
        (Homogenization.originCube d (m : ℤ)) (1 / 4) 2
        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)))) ≤
        ENNReal.ofReal ((m : ℝ) ^ ρ))
    (hS5 :
        ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
        ∃ M : ℕ,
        ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
        hPrefix hJ2 hJ3 →
        ∀ m : ℕ, M ≤ m →
        |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
        (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K))
    (hSmooth :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ kc2_Q0 d → ∀ C₀ : ℝ,
    ∃ C : ℝ, C₀ ≤ C ∧ 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : ShellSeq d → ℝ, Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
        Homogenization.IndependentSums.IsBigO P.toMeasure
          (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ᵐ omega ∂P.toMeasure, ∀ (n : ℕ) (R : ℝ), C ≤ (n : ℝ) → Lhat ≤ (nK C n : ℝ) →
          X0 omega ≤ (3 : ℝ) ^ nK C n → (3 : ℝ) ^ n < 3 * R → R ≤ (3 : ℝ) ^ n →
          ∀ (f gt : Vec d → ℝ) (F G : ℝ), ContDiff ℝ (⊤ : ℕ∞) gt → 0 ≤ F → 0 ≤ G →
            AEStronglyMeasurable f (volume.restrict (R • U)) →
            (∀ᵐ x ∂volume.restrict (R • U), |f x| ≤ F) → (∀ x, ‖fderiv ℝ gt x‖ ≤ G) →
            (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ G / (3 : ℝ) ^ nK C n) →
          ∀ v vh : H1Function (R • U),
            IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) (R • U) v f
              (fun _ => 0) →
            MemH10 (R • U) (fun x => v.toFun x - gt x) →
            IsWeakSolutionOn (fun _ => sigmaBarInfinite nu n P • (1 : Mat d)) (R • U) vh f
              (fun _ => 0) →
            MemH10 (R • U) (fun x => vh.toFun x - gt x) →
            eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict (R • U)) +
                hMinusOneVec (R • U) (fun x => v.grad x - vh.grad x) +
                hMinusOneVec (R • U) (fun x =>
                  matVecMul ((sigmaBarInfinite nu n P)⁻¹ •
                    (Section6.fullCoefficientRecentered nu omega x -
                      volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                        (Section6.fullStreamRecentered omega))) (v.grad x) - vh.grad x) ≤
              ENNReal.ofReal (C * deltaScale ε ρ (n : ℝ) *
                ((sigmaBarInfinite nu n P)⁻¹ * (3 : ℝ) ^ (2 * n) * F +
                  Real.log (n : ℝ) * (3 : ℝ) ^ n * G)))
  :
    ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ kc2_Q0 d →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
        ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
        ∃ Lhat : ℝ, 1 ≤ Lhat ∧
          ∀ (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
            (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
            (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
            (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
            SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
            ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X0 ∧ (∀ omega, 1 ≤ X0 omega) ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                (Homogenization.IndependentSums.gammaSigma ρ)
                (fun omega => Real.log (X0 omega)) Lhat ∧
              ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                ∀ (n : ℕ) (R : ℝ), C ≤ (n : ℝ) →
                  Lhat ≤ (((n : ℤ) - ⌈C * Real.log (n : ℝ)⌉ : ℤ) : ℝ) →
                  X0 omega ≤ (3 : ℝ) ^ ((n : ℤ) - ⌈C * Real.log (n : ℝ)⌉) →
                  (3 : ℝ) ^ n < 3 * R → R ≤ (3 : ℝ) ^ n →
                  ∀ W : Set (Vec d), W = R • U →
                  ∀ (f : Vec d → ℝ) (g u uhom : H1Function W),
                    IsDirichletSolution
                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega) W f g u →
                    IsDirichletSolution
                      (fun _ => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P •
                        (1 : Mat d)) W f g uhom →
                      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict W) +
                        hMinusOneVec W (fun x => u.grad x - uhom.grad x) +
                        hMinusOneVec W (fun x =>
                          matVecMul ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ •
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega x -
                              volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Section6.fullStreamRecentered omega)))
                            (u.grad x) - uhom.grad x) ≤
                      ENNReal.ofReal (C * deltaScale ε ρ (n : ℝ) *
                          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu n P)⁻¹ *
                            (3 : ℝ) ^ (2 * n))) *
                        eLpNorm f ⊤ (volume.restrict W) +
                      ENNReal.ofReal (C * deltaScale ε ρ (n : ℝ) * Real.log (n : ℝ) *
                          (3 : ℝ) ^ n) *
                        eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict W) := by
  intro U hUs hU0
  obtain ⟨r, M₁, M₂, D, hUu⟩ := exists_isUniformC11Domain_of_isSmoothBoundedDomain hUs
  obtain ⟨Cf, hCf1, HF⟩ := linf_field d hd hInputs
  obtain ⟨Cg, hCg1, HD⟩ := linf_datum hUs
  obtain ⟨cv, hcv, HG⟩ := linf_geom hUs hU0 hUu
  obtain ⟨Kc, hKc, HP⟩ := linf_pt_core (d := d) Cf cv Cg hCf1 hcv.le hCg1
  obtain ⟨Cs, hCs24, hCs1, HS⟩ := hSmooth U hUs hU0 24
  have hr0 : 0 < r := hUu.2.1
  set C : ℝ := Cs * (Cg + Kc) with hCdef
  have hCs_le : Cs ≤ C := by rw [hCdef]; nlinarith only [hCs1, hCg1, hKc]
  have hC1 : 1 ≤ C := hCs1.trans hCs_le
  have hCsCg : Cs * Cg + Kc ≤ C := by rw [hCdef]; nlinarith only [hCs1, hCg1, hKc]
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 cStar hcStar Kj ε ρ M hε hε1 hρ hρ1 hCM
  obtain ⟨Lf, hLf1, Hf⟩ := HF nu hnu hnu1 cStar hcStar Kj ε ρ Cf hε hε1 hρ hρ1 le_rfl
  obtain ⟨Ls, hLs1, Hs⟩ := HS nu hnu hnu1 cStar hcStar Kj ε ρ hε hε1 hρ hρ1
  obtain ⟨Lσ, hLσ⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar Kj
  set Lhat : ℝ := max ((3 * Real.log 2) ^ ρ⁻¹ * (Ls + Lf))
    (max (Lσ : ℝ) (max (1 / nu) (max (1 / ε ^ 2) (max 3 (36 / r))))) with hLhatdef
  have hL3 : 3 ≤ Lhat := by
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    exact le_max_left _ _
  have hLA : (3 * Real.log 2) ^ ρ⁻¹ * (Ls + Lf) ≤ Lhat := le_max_left _ _
  have hc1 : (1 : ℝ) ≤ (3 * Real.log 2) ^ ρ⁻¹ :=
    Real.one_le_rpow (by have := Real.log_two_gt_d9; linarith only [this]) (inv_nonneg.2 hρ.le)
  have hLs_le : Ls ≤ Lhat := by nlinarith only [hLA, hc1, hLs1, hLf1]
  have hLf_le : Lf ≤ Lhat := by nlinarith only [hLA, hc1, hLs1, hLf1]
  have hLσ' : (Lσ : ℝ) ≤ Lhat := (le_max_left _ _).trans (le_max_right _ _)
  have hLν : 1 / nu ≤ Lhat :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hLε : 1 / ε ^ 2 ≤ Lhat :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hLr : 36 / r ≤ Lhat :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨Lhat, by linarith only [hL3], ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X1, hX1m, hX11, hX1O, hae1⟩ := Hs P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X2, hX2m, hX21, hX2O, hae2⟩ := Hf P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨fun ω => max (X1 ω) (X2 ω), hX1m.max hX2m,
    fun ω => le_trans (hX11 ω) (le_max_left _ _), ?_, ?_⟩
  · exact SuperdiffusionCLT.Section6.l9_log_max_bigO hρ (by linarith only [hLs1])
      (by linarith only [hLf1]) hLA hX21 hX1O hX2O
  filter_upwards [hae1, hae2, SuperdiffusionCLT.Section6.ae_centered_eq_recentered_add_skew hJ3 nu]
    with ω h1 h2 hskew
  intro n R hCn hLn hXn hR1 hR2 W hW f g u uhom hu huh
  subst hW
  -- the scale bridge
  have hC0 : 0 ≤ C := by linarith only [hC1]
  have h0 : (0 : ℤ) ≤ (n : ℤ) - ⌈C * Real.log (n : ℝ)⌉ := by
    have h3 : (0 : ℝ) < (((n : ℤ) - ⌈C * Real.log (n : ℝ)⌉ : ℤ) : ℝ) :=
      lt_of_lt_of_le (by norm_num) (hL3.trans hLn)
    exact_mod_cast h3.le
  have hz := linf_scale_zcast hC0 n h0
  rw [hz] at hLn hXn
  rw [Int.cast_natCast] at hLn
  rw [zpow_natCast] at hXn
  have hmono : nK C n ≤ nK Cs n := linf_nK_anti hCs_le n
  have hLm : Lhat ≤ (nK Cs n : ℝ) := hLn.trans (by exact_mod_cast hmono)
  have hmn : nK Cs n ≤ n := Nat.sub_le _ _
  have hLn' : Lhat ≤ (n : ℝ) := hLm.trans (by exact_mod_cast hmn)
  have hn3 : (3 : ℝ) ≤ n := hL3.trans hLn'
  have hn0 : (0 : ℝ) < n := by linarith only [hn3]
  have hX1n : X1 ω ≤ (3 : ℝ) ^ (nK Cs n) :=
    ((le_max_left _ _).trans hXn).trans (pow_le_pow_right₀ (by norm_num) hmono)
  have hX2n : X2 ω ≤ (3 : ℝ) ^ n :=
    ((le_max_right _ _).trans hXn).trans (pow_le_pow_right₀ (by norm_num) (hmono.trans hmn))
  have hCsn : Cs ≤ (n : ℝ) := hCs_le.trans hCn
  have hS_ev := h1 n R hCsn (hLs_le.trans hLm) hX1n hR1 hR2
  obtain ⟨hσ1, hσn, -, -⟩ := hLσ P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 n n
    (by exact_mod_cast hLσ'.trans hLn') le_rfl (by omega)
  obtain ⟨hid, hell⟩ := h2 n hX2n (hLf_le.trans hLn')
  set σ : ℝ := sigmaBarInfinite nu n P with hσdef
  set m : ℕ := nK Cs n with hmdef
  set ms : ℕ := ⌈Cs * Real.log (n : ℝ)⌉₊ with hmsdef
  have hm1 : 1 ≤ m := by
    have : (3 : ℝ) ≤ m := hL3.trans hLm
    exact_mod_cast (by linarith only [this] : (1 : ℝ) ≤ m)
  have hm_ms : m + ms = n := by
    have hm' : m = n - ms := rfl
    omega
  have hn3' : 3 ≤ n := by exact_mod_cast hn3
  have hpowms : (n : ℝ) ^ 24 ≤ (3 : ℝ) ^ ms := linf_pow_le_three_pow hCs24 hn3'
  have h3n : (3 : ℝ) ^ n = 3 ^ m * 3 ^ ms := by rw [← pow_add, hm_ms]
  have hnr : 36 / r ≤ (n : ℝ) := hLr.trans hLn'
  have h12 : 12 * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n * (r / 3) := by
    rw [h3n]
    have h36 : 36 ≤ (n : ℝ) * r := by rwa [div_le_iff₀ hr0] at hnr
    have hn24 : (n : ℝ) ≤ (n : ℝ) ^ 24 := le_self_pow₀ (by linarith only [hn3]) (by norm_num)
    have h1' : (n : ℝ) * (r / 3) ≤ (3 : ℝ) ^ ms * (r / 3) :=
      mul_le_mul_of_nonneg_right (hn24.trans hpowms) (by positivity)
    have h2' : 12 ≤ (3 : ℝ) ^ ms * (r / 3) := by linarith only [h1', h36]
    have h3m : (0 : ℝ) < 3 ^ m := by positivity
    calc 12 * (3 : ℝ) ^ m ≤ ((3 : ℝ) ^ ms * (r / 3)) * 3 ^ m := by gcongr
      _ = 3 ^ m * 3 ^ ms * (r / 3) := by ring
  have hpow : (n : ℝ) ^ 24 * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n := by
    rw [h3n]
    calc (n : ℝ) ^ 24 * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ ms * 3 ^ m :=
          mul_le_mul_of_nonneg_right hpowms (by positivity)
      _ = 3 ^ m * 3 ^ ms := by ring
  obtain ⟨hWo, hWsub, hWb, hW0, hlay⟩ := HG hR1 hR2 h12
  have hWL : R • U ⊆ axisCube (fun _ => -((3 : ℝ) ^ n / 2)) ((3 : ℝ) ^ n) :=
    fun x hx => lip_int_harm_of_l2_engCube_subset_axis n (hWsub hx)
  have hWm : MeasurableSet (R • U) := hWo.measurableSet
  have hRpos : 0 < R := by
    have : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    linarith only [hR1, this]
  have hbd : Bornology.IsBounded (R • U) :=
    (isBounded_openCubeSet (originCube d (n : ℤ))).subset hWsub
  have hfin : IsFiniteMeasure (volumeMeasureOn (R • U)) :=
    ⟨by
      show volume.restrict (R • U) Set.univ < ⊤
      rw [Measure.restrict_apply_univ]
      exact hbd.measure_lt_top⟩
  set a : CoeffField d := SuperdiffusionCLT.Section6.fullCoefficientRecentered nu ω with hadef
  set S : Mat d := volumeAverageMat (cubeSet (originCube d (n : ℤ)))
    (SuperdiffusionCLT.Section6.fullStreamRecentered ω) with hSdef
  have hb : (fun x => a x - S) = fun x => nu • (1 : Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField ω
        (cubeSet (originCube d (n : ℤ))) x := funext hid
  have hellC := wh2_isEllipticFieldOn_mono hWm hWsub hell
  have hellW : IsEllipticFieldOn nu ((nu + Cf * (n : ℝ) ^ (1 + ρ)) ^ 2 / nu) (R • U)
      (fun x => a x - S) := by rw [hb]; exact hellC
  obtain ⟨K0, hK0, hKx⟩ := hskew n
  have htr : ∀ (w : H1Function (R • U)) (f : Vec d → ℝ),
      IsWeakSolutionOn a (R • U) w f (fun _ => 0) ↔
        IsWeakSolutionOn (fun x => a x - S) (R • U) w f (fun _ => 0) := by
    intro w f
    rw [hb]
    have := hfin
    exact linf_weak_transfer hWo hK0 hKx hellC w f
  have hnνn : 1 ≤ (n : ℝ) * nu := by
    have := hLν.trans hLn'
    rw [div_le_iff₀ hnu] at this
    linarith only [this]
  have hnε : 1 ≤ (n : ℝ) * ε ^ 2 := by
    have := hLε.trans hLn'
    rw [div_le_iff₀ (by positivity)] at this
    linarith only [this]
  have hδ : 0 < deltaScale ε ρ (n : ℝ) := deltaScale_pos hε (by linarith only [hn3])
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith only [hn3])
  have hσ0 : 0 < σ := by linarith only [hσ1]
  have hA : 0 < C * deltaScale ε ρ (n : ℝ) * (σ⁻¹ * (3 : ℝ) ^ (2 * n)) := by positivity
  have hB : 0 < C * deltaScale ε ρ (n : ℝ) * Real.log (n : ℝ) * (3 : ℝ) ^ n := by positivity
  by_cases hfT : eLpNorm f ⊤ (volume.restrict (R • U)) = ⊤
  · rw [hfT, ENNReal.mul_top (ENNReal.ofReal_pos.2 hA).ne', top_add]
    exact le_top
  by_cases hgT : eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (R • U)) = ⊤
  · rw [hgT, ENNReal.mul_top (ENNReal.ofReal_pos.2 hB).ne', add_top]
    exact le_top
  have hfm : AEStronglyMeasurable f (volume.restrict (R • U)) := by
    by_contra hnm
    exact hfT (eLpNorm_of_not_aestronglyMeasurable hnm)
  set F : ℝ := (eLpNorm f ⊤ (volume.restrict (R • U))).toReal with hFdef
  set G' : ℝ := (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (R • U))).toReal
    with hGdef
  have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G' := ENNReal.toReal_nonneg
  have hFe : eLpNorm f ⊤ (volume.restrict (R • U)) = ENNReal.ofReal F :=
    (ENNReal.ofReal_toReal hfT).symm
  have hGe : eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (R • U)) =
      ENNReal.ofReal G' := (ENNReal.ofReal_toReal hgT).symm
  have hfF : ∀ᵐ x ∂volume.restrict (R • U), |f x| ≤ F :=
    linf_det_ae_of_eLpNorm_top hfm hF0 hFe.le
  have hgm : AEStronglyMeasurable (fun x => eucNorm (g.grad x)) (volume.restrict (R • U)) :=
    p13_continuous_eucNorm.comp_aestronglyMeasurable g.grad_memVectorL2.aestronglyMeasurable
  have hgG : ∀ᵐ x ∂volume.restrict (R • U), eucNorm (g.grad x) ≤ G' := by
    filter_upwards [linf_det_ae_of_eLpNorm_top hgm hG0 hGe.le] with x hx
    rwa [abs_of_nonneg (by unfold eucNorm; exact Real.sqrt_nonneg _)] at hx
  obtain ⟨gt, hgt, hgtc, hgt1, hgt2⟩ := HD R hRpos g G' hG0 hGe.le ((3 : ℝ) ^ m) (by positivity)
  have hGs0 : 0 ≤ Cg * G' := mul_nonneg (zero_le_one.trans hCg1) hG0
  have core := HP hWo hWb hW0 hWL hlay hpow (ν := nu) (ε := ε) (ρ := ρ) (σ := σ) (Cs := Cs)
    a S hn3 hnu hnu1 hnνn hε hε1 hnε hρ hρ1 hσ1 hellW htr f g hF0 hG0 hfm hfF hgG hgt hgtc hgt1 hgt2
    (fun v vh hv hvm hvh hvhm => hS_ev f gt F (Cg * G') hgt hF0 hGs0 hfm hfF hgt1 hgt2 v vh hv hvm
      hvh hvhm) u uhom hu huh
  refine core.trans ?_
  rw [hFe, hGe, ← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul hB.le]
  obtain ⟨hPnn, hQnn, hYnn, hsplit, hQY, hPP⟩ := linf_pc_real (C := C) (D := deltaScale ε ρ (n : ℝ))
    (S := σ⁻¹ * (3 : ℝ) ^ (2 * n)) (Lg := Real.log (n : ℝ)) (T := (3 : ℝ) ^ n) (F := F) (G' := G')
    (zero_le_one.trans hCs1) (zero_le_one.trans hCg1) hKc.le hδ.le
    (mul_nonneg (inv_nonneg.2 hσ0.le) (pow_nonneg (by norm_num) _)) hlog.le
    (pow_nonneg (by norm_num) _) hF0 hG0 hCsCg hCs_le
  rw [hsplit, ENNReal.ofReal_add hPnn hQnn, add_assoc, ← ENNReal.ofReal_add hQnn hYnn]
  exact add_le_add (ENNReal.ofReal_le_ofReal hPP) (ENNReal.ofReal_le_ofReal hQY)

end SuperdiffusionCLT.Section7
