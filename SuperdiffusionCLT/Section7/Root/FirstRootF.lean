/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.FirstRootE

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise
open scoped Matrix.Norms.L2Operator

/-- **The first root**, from the `L^∞` proposition, the sharp bounds for the diffusivities and the
scale estimates of Section 2. -/
theorem s5_superdiffusivity (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hLinf : ∀ U : Set (Vec d), IsSmoothBoundedDomain U → U ⊆ kc2_Q0 d →
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
                        eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict W))
    (hSigma :
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
    (hV6 :
        ∃ C₂ : ℝ,
          ∀ s : ℝ, 0 < s → s < 1 →
            ∃ C₀ C₁ : ℝ,
              ∀ p : ℝ, 1 < p →
                ∃ C : ℝ,
                  ∀ P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    (∀ l m n : ℕ, n < m → m ≤ l →
                        (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                          Measurable X ∧
                            Homogenization.IndependentSums.IsBigO P.toMeasure
                              (Homogenization.IndependentSums.gammaSigma 2) X
                              (C * (3 : ℝ) ^ (s * (m : ℝ))) ∧
                            ∀ omega,
                              SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                  (Homogenization.originCube d (l : ℤ)) s
                                  (ENNReal.ofReal p)
                                  (fun x =>
                                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                      omega n m x) ≤
                                ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * p ^ ((1 : ℝ) / 2) * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  (3 : ℝ) ^ (-((d : ℝ) / (2 * p) * ((l - m : ℕ) : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ))
                                    (ENNReal.ofReal p)
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal
                                    (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) + X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * ((m - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                                  ((l - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                    (Homogenization.originCube d (l : ℤ)) ∞
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega)) ∧
                          (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ omega,
                                SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                                    (Homogenization.originCube d (l : ℤ)) s
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n m x) ≤
                                  ENNReal.ofReal (X omega))) ∧
                      (∀ l n : ℕ,
                          ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                            Measurable X ∧
                              Homogenization.IndependentSums.IsBigO P.toMeasure
                                (Homogenization.IndependentSums.gammaSigma 2) X
                                (C * (3 : ℝ) ^ (-(s * (n : ℝ)))) ∧
                              ∀ᵐ omega ∂P.toMeasure,
                                (⨆ M : {M : ℕ // n < M},
                                  SuperdiffusionCLT.Section2.Norms.cubeEuclideanGagliardoESeminorm
                                    (Homogenization.originCube d (l : ℤ)) s 2
                                    (fun x =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega n M.1 x)) ≤
                                  ENNReal.ofReal (X omega)) ∧
                      (∀ delta : ℝ, 0 < delta → delta < 1 →
                          ∀ sigma : ℝ, 0 < sigma →
                            ∃ Kfun : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                              Measurable Kfun ∧
                                (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
                                Homogenization.IndependentSums.IsBigO P.toMeasure
                                  (Homogenization.IndependentSums.gammaSigma (2 * sigma))
                                  (fun omega => Real.log (Kfun omega))
                                  (C₀ *
                                    (C₁ * delta⁻¹ *
                                        Real.sqrt (sigma⁻¹ *
                                          Real.log (Real.exp 1 + C₂ * delta⁻¹ * sigma⁻¹))) ^
                                      sigma⁻¹) ∧
                                ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                                    ∂P.toMeasure,
                                  (∀ i : ℕ,
                                      Summable fun k : ℕ =>
                                        SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                          (Homogenization.openCubeSet
                                            (Homogenization.originCube d (i : ℤ)))
                                          (omega k)) →
                                    ((∀ m : ℕ,
                                        Kfun omega ≤ (3 : ℝ) ^ m →
                                    (ENNReal.ofReal ((m : ℝ)⁻¹) *
                                          SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                                            (Homogenization.originCube d (m : ℤ)) ∞
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ m) *
                                          (∑' k : ℕ,
                                            ENNReal.ofReal
                                              (SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm
                                                (Homogenization.openCubeSet
                                                  (Homogenization.originCube d (m : ℤ)))
                                                (omega (m + 1 + k)))) +
                                        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
                                          SuperdiffusionCLT.Section2.Norms.matHatNegENorm
                                            (Homogenization.originCube d (m : ℤ)) s 2
                                            (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                              omega
                                              (Homogenization.cubeSet
                                                (Homogenization.originCube d (m : ℤ)))) ≤
                                      ENNReal.ofReal (delta * (m : ℝ) ^ sigma)) ∧
                                      ∀ A B : ℝ, 1 ≤ A → 1 ≤ B →
                                        ∀ n : ℕ,
                                          (m : ℤ) - ⌈A * Real.log (B * (m : ℝ))⌉ ≤ (n : ℤ) →
                                            n ≤ m →
                                              ∀ Q : Homogenization.TriadicCube d,
                                                Q.scale = (n : ℤ) →
                                                  Homogenization.cubeCenter Q ∈
                                                      Homogenization.cubeSet
                                                        (Homogenization.originCube d (m : ℤ)) →
                                                    Homogenization.Book.Ch02.matrixOperatorNorm
                                                        (Homogenization.volumeAverageMat
                                                          (Homogenization.cubeSet Q)
                                                          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                                            omega
                                                            (Homogenization.cubeSet
                                                              (Homogenization.originCube d (m : ℤ))))) ≤
                                                      A * Real.log (B * (m : ℝ)) * delta *
                                                        (m : ℝ) ^ sigma) ∧
                                      ∀ x : Homogenization.Vec d,
                                  Homogenization.Book.Ch02.matrixOperatorNorm
                                        (SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) x -
                                          SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                            omega
                                            (Homogenization.cubeSet
                                              (Homogenization.originCube d (0 : ℤ))) 0) ^ 2 ≤
                                    C *
                                      Real.log (Kfun omega ^ 2 + Homogenization.vecNormSq x) ^
                                        (2 * (1 + sigma))))) :
    ∀ α β : ℝ, 0 < α → α ≤ 1 → 0 < β → β ≤ 1 → β + 2 * α < 1 →
      ∀ U : Set (Homogenization.Vec d),
        SuperdiffusionCLT.Section7.IsSmoothBoundedDomain U →
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∃ C : ℝ, 1 ≤ C ∧
                ∀ (P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                      hPrefix hJ2 hJ3 →
                  ∃ Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable Z ∧
                    -- e.Z.integrability
                    (∀ ξ : ℝ, 1 ≤ ξ →
                      P.toMeasure {omega | ξ ≤ Z omega} ≤
                        ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                        ∀ (f : Homogenization.Vec d → ℝ) (g u uhom : Homogenization.H1Function U),
                          -- e.BVPs
                          SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                SuperdiffusionCLT.Section7.epField nu omega ε x)
                              U f g u →
                          SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun _ => (1 : Homogenization.Mat d)) U f g uhom →
                          -- e.homogenization.error
                          MeasureTheory.eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
                                (MeasureTheory.volume.restrict U) +
                              SuperdiffusionCLT.Section7.hMinusOneVec U
                                (fun x => u.grad x - uhom.grad x) +
                              SuperdiffusionCLT.Section7.hMinusOneVec U
                                (fun x =>
                                  Homogenization.matVecMul
                                      (((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                        SuperdiffusionCLT.Section7.epFieldCentered
                                          nu omega ε U x)
                                      (u.grad x) -
                                    uhom.grad x) ≤
                            ENNReal.ofReal (C * |Real.log ε| ^ (-α)) *
                              (MeasureTheory.eLpNorm
                                  (fun x => SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
                                  (MeasureTheory.volume.restrict U) +
                                MeasureTheory.eLpNorm f ⊤ (MeasureTheory.volume.restrict U)) := by
  intro α β hα hα1 hβ hβ1 hαβ U hU nu hnu hnu1 cStar hc Kn
  have hαh : α < (1 - β) / 2 := by linarith only [hαβ]
  set α0 : ℝ := (α + (1 - β) / 2) / 2 with hα0def
  have hαα0 : α < α0 := by rw [hα0def]; linarith only [hαh]
  have hα0h : α0 < (1 - β) / 2 := by rw [hα0def]; linarith only [hαh]
  have hα012 : α0 < 1 / 2 := by linarith only [hα0h, hβ]
  set ρ : ℝ := 1 - 2 * α0 with hρdef
  have hρβ : β < ρ := by rw [hρdef]; linarith only [hα0h]
  have hρ0 : 0 < ρ := by linarith only [hρβ, hβ]
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith only [hαα0, hα]
  set σc : ℝ := (β / 2 + (1 / 2 - α)) / 2 with hσcdef
  have hσc1 : β / 2 < σc := by rw [hσcdef]; linarith only [hαβ]
  have hσc2 : σc < 1 / 2 - α := by rw [hσcdef]; linarith only [hαβ]
  set εc : ℝ := (1 / 2 - α - σc) / 2 with hεcdef
  have hεc : 0 < εc := by rw [hεcdef]; linarith only [hσc2]
  have hσε : σc + εc ≤ 1 / 2 - α := by rw [hεcdef]; linarith only [hσc2]
  have hσc0 : 0 < σc := by linarith only [hσc1, hβ]
  obtain ⟨R0, hR0, hRU⟩ := hU.2.2.1
  set T : ℝ := 2 * R0 + 1 with hTdef
  have hT : 1 ≤ T := by rw [hTdef]; linarith only [hR0]
  have hT0 : 0 < T := by linarith only [hT]
  have hŨsm : IsSmoothBoundedDomain (T⁻¹ • U) := w0_isSmoothBoundedDomain_smul hU (inv_pos.2 hT0)
  have hŨQ : T⁻¹ • U ⊆ kc2_Q0 d := by
    rintro x ⟨y, hy, rfl⟩
    rw [kc2_Q0, Set.mem_pi]
    intro i _
    have hy' := abs_le.1 (hRU y hy i)
    simp only [Set.mem_Ico, Pi.smul_apply, smul_eq_mul]
    rw [← div_eq_inv_mul]
    constructor
    · rw [le_div_iff₀ hT0]; rw [hTdef]; linarith only [hy'.1]
    · rw [div_lt_iff₀ hT0]; rw [hTdef]; linarith only [hy'.2, hR0]
  set zU : Vec d := fun _ => -(R0 + 1) with hzU
  set LU : ℝ := 2 * R0 + 2 with hLUdef
  have hLU : 0 < LU := by rw [hLUdef]; linarith only [hR0]
  have hUL : U ⊆ axisCube zU LU := by
    intro x hx
    rw [axisCube, Set.mem_pi]
    intro i _
    have hx' := abs_le.1 (hRU x hx i)
    simp only [Set.mem_Ioo, hzU, hLUdef]
    constructor <;> linarith only [hx'.1, hx'.2]
  obtain ⟨C1, hC1, hLin⟩ := hLinf (T⁻¹ • U) hŨsm hŨQ
  obtain ⟨Lhat, hLhat1, hLP⟩ :=
    hLin nu hnu hnu1 cStar hc Kn 1 ρ C1 one_pos le_rfl hρ0 hρ1 le_rfl
  obtain ⟨Cs, hCs, hSg⟩ := hSigma
  obtain ⟨M, hM⟩ := hSg nu hnu hnu1 cStar hc Kn
  obtain ⟨Cσ, Cf, hK3⟩ := kc3_centering_smooth_ae d σc εc hσc0 hεc hŨsm hŨQ hV6
  obtain ⟨Cn, hCn, K0, hnum⟩ := s5_scalar_numerics (cStar := cStar) (C0 := Cs) (Kc := Kn) hc
    (by linarith only [hCs]) (M := M) (α := α) (by linarith only [hαα0, hα012])
  obtain ⟨Cx, N1, hCx, hpt⟩ := s5_pointwise hd (α := α) (α0 := α0) (ρ := ρ) (σ' := σc + εc) hα
    hαα0 hα1 hρdef hσε hU zU hLU hUL hT C1 Cn (max Cf 0) (by linarith only [hC1]) hCn.le
    (le_max_right _ _) cStar hc
  set L : ℝ := max (max C1 Lhat) (max (max N1 ((K0 : ℝ) + 1)) 3) with hLdef
  have hL3 : 3 ≤ L := (le_max_right _ _).trans' (le_max_right _ _)
  have hL0 : 0 ≤ L := by linarith only [hL3]
  have hLpos : 0 < (2 : ℝ) ^ (1 / β) * max Lhat (max Cσ 1) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (lt_of_lt_of_le (by linarith only [hLhat1]) (le_max_left _ _))
  obtain ⟨Ct', hCt'1, hTail⟩ := s5_scale_tail_unif (Ω := SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (Λ := (2 : ℝ) ^ (1 / β) * max Lhat (max Cσ 1)) (σ := β) (N₀ := C1) (L := L) hLpos hβ
    (by linarith only [hC1]) hL0
  refine ⟨max (max Ct' (Cx * Real.log 3 ^ α)) 1, le_max_right _ _, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0, hX0m, hX0, hX0O, hae1⟩ := hLP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Kc, hKcm, hKc27, hKcO, hae2⟩ := hK3 P hPrefix hJ1 hJ2 hJ3 hJ4
  have hae3 := SuperdiffusionCLT.Section6.ae_exists_entryBound_fullCoefficientRecentered hJ3 nu
  have hsh := hM P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have hnumP := hnum (fun m => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) hsh
  set Y : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ := fun ω => max (X0 ω) (Kc ω)
    with hY
  have hY1 : ∀ ω, 1 ≤ Y ω := fun ω => (hX0 ω).trans (le_max_left _ _)
  have hYm : Measurable Y := hX0m.max hKcm
  refine ⟨fun ω => (3 : ℝ) ^ ms_star C1 L (Y ω), ?_, ?_, ?_⟩
  · have := ms_star_measurable (L := L) (by linarith only [hC1]) hY1 hYm
    exact (measurable_from_nat (f := fun m : ℕ => (3 : ℝ) ^ m)).comp this
  · intro ξ hξ
    have hKcO' := hKcO.mono_scale (show Cσ ≤ max Cσ 1 from le_max_left _ _)
    have hmax := s5_tail_max_log P.toMeasure (X := X0) (Y := Kc) hβ hρβ.le (by linarith only [hσc1])
      (by linarith only [hLhat1]) (lt_of_lt_of_le one_pos (le_max_right Cσ 1)) hX0O hKcO'
    have h := hTail P.toMeasure Y hY1 hmax ξ hξ
    rw [← MeasureTheory.ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal (h.trans ?_)
    have hC0 : Ct' ≤ max (max Ct' (Cx * Real.log 3 ^ α)) 1 :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hCpos : 0 < Ct' := by linarith only [hCt'1]
    have hx : 0 ≤ Real.log ξ ^ β := Real.rpow_nonneg (Real.log_nonneg hξ) _
    refine mul_le_mul hC0 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by linarith only [hCt'1, hC0])
    have : (max (max Ct' (Cx * Real.log 3 ^ α)) 1)⁻¹ ≤ Ct'⁻¹ := inv_anti₀ hCpos hC0
    have := mul_le_mul_of_nonneg_right this hx
    linarith only [this]
  · filter_upwards [hae1, hae2, hae3] with ω h1 h2 h3
    intro ε hε hε2 hZ f g u uhom hu huh
    have hε'0 : 0 < ε / T := div_pos hε hT0
    have hε'2 : ε / T ≤ 1 / 2 := (div_le_self hε.le hT).trans hε2
    obtain ⟨hR1, hR2, hn1, h3T, hlogn, -⟩ := s5_scaleK_pack hε hε2 hT
    set n : ℕ := s12_scaleK (ε / T) with hndef
    have hεR : ε⁻¹ ≤ T / ε := by
      rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hT hε.le
    have hZn : (3 : ℝ) ^ ms_star C1 L (Y ω) ≤ (3 : ℝ) ^ n := hZ.trans (hεR.trans hR1)
    obtain ⟨-, hLe, hYe⟩ := ms_scale_consumer (by linarith only [hC1]) (hY1 ω) hZn
    have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hceil : 0 ≤ ⌈C1 * Real.log (n : ℝ)⌉ :=
      Int.ceil_nonneg (mul_nonneg (by linarith only [hC1]) (Real.log_nonneg hnr1))
    have hen : ((ms_e C1 n : ℤ) : ℝ) ≤ n := by
      unfold ms_e
      have : ((⌈C1 * Real.log (n : ℝ)⌉ : ℤ) : ℝ) ≥ 0 := by exact_mod_cast hceil
      push_cast
      linarith only [this]
    have hLn : L ≤ n := hLe.trans hen
    have hX0e : X0 ω ≤ (3 : ℝ) ^ ((n : ℤ) - ⌈C1 * Real.log (n : ℝ)⌉) :=
      (le_max_left _ _).trans hYe
    have hKce : Kc ω ≤ (3 : ℝ) ^ n := by
      refine ((le_max_right _ _).trans hYe).trans ?_
      refine (zpow_le_zpow_right₀ (by norm_num) ?_).trans_eq (zpow_natCast _ _)
      unfold ms_e at hen
      have : (ms_e C1 n : ℤ) ≤ n := by exact_mod_cast hen
      exact this
    have hC1n : C1 ≤ (n : ℝ) := ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
    have hLhe : Lhat ≤ (((n : ℤ) - ⌈C1 * Real.log (n : ℝ)⌉ : ℤ) : ℝ) :=
      (((le_max_right _ _).trans (le_max_left _ _)).trans hLe)
    have hN1n : N1 ≤ (n : ℝ) :=
      (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hLn
    have hK0n : (K0 : ℝ) + 1 ≤ (n : ℝ) :=
      (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hLn
    have hK0n' : K0 + 1 ≤ n := by exact_mod_cast hK0n
    have hK0 : (3 : ℝ) ^ K0 ≤ (ε / T)⁻¹ := by
      rw [inv_div]
      have h1' : (3 : ℝ) ^ K0 ≤ 3 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2' : (3 : ℝ) ^ n = 3 * 3 ^ (n - 1) := by
        rw [← pow_succ' ]; congr 1; omega
      linarith only [h1', h2', hR2]
    obtain ⟨hshp, hS2, hSb, hlow⟩ := hnumP (ε / T) hε'0 hε'2 hK0
    have hWeq : ε⁻¹ • U = (T / ε) • (T⁻¹ • U) := by
      rw [smul_smul, show T / ε * T⁻¹ = ε⁻¹ by field_simp]
    have hinst := h1 n (T / ε) hC1n hLhe hX0e hR2 hR1 (ε⁻¹ • U) hWeq
    have hWsm : IsSmoothBoundedDomain (ε⁻¹ • U) := w0_isSmoothBoundedDomain_smul hU (inv_pos.2 hε)
    obtain ⟨Bw, hBw⟩ := h3 (ε⁻¹ • U) hWsm.2.2.1.isBounded
    have hlam1 : 1 / 3 < T / ε / (3 : ℝ) ^ n := by
      rw [lt_div_iff₀ (by positivity)]; linarith only [hR2]
    have hlam2 : T / ε / (3 : ℝ) ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact hR1
    have hk := (h2 n hKce (T / ε / (3 : ℝ) ^ n) hlam1 hlam2).1
    have hset : (3 : ℝ) ^ n • ((T / ε / (3 : ℝ) ^ n) • (T⁻¹ • U)) = ε⁻¹ • U := by
      rw [smul_smul, show (3 : ℝ) ^ n * (T / ε / (3 : ℝ) ^ n) = T / ε by field_simp]
      exact hWeq.symm
    rw [hset] at hk
    have hBc : ∀ i j, |(Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
        SuperdiffusionCLT.Section6.fullStreamRecentered ω w i j) i j -
        (volumeAverageMat (cubeSet (originCube d (n : ℤ)))
          (SuperdiffusionCLT.Section6.fullStreamRecentered ω)) i j| ≤
        max Cf 0 * (n : ℝ) ^ (σc + εc) := by
      refine s5_entry_le (hk.trans ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith only [hnr1]) _)
    have hfin := hpt nu ω (fun m => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)
      hε hε2 hN1n hshp hS2 hSb hlow Bw _ _ hBw hBc le_rfl hinst f g u uhom hu huh
    refine hfin.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have hl : 0 < |Real.log ε| := abs_pos.2 (Real.log_neg hε (by linarith only [hε2])).ne
    have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hn0 : (0 : ℝ) < n := by linarith only [hnr1]
    have hnk : (n : ℝ) ^ (-α) ≤ Real.log 3 ^ α * |Real.log ε| ^ (-α) := by
      calc (n : ℝ) ^ (-α) ≤ (|Real.log ε| / Real.log 3) ^ (-α) :=
            Real.rpow_le_rpow_of_nonpos (div_pos hl hl3) hlogn (by linarith only [hα])
        _ = _ := by
          rw [Real.div_rpow hl.le hl3.le, Real.rpow_neg hl3.le, Real.rpow_neg hl.le]
          field_simp
    have hCfin : Cx * Real.log 3 ^ α ≤ max (max Ct' (Cx * Real.log 3 ^ α)) 1 :=
      (le_max_right _ _).trans (le_max_left _ _)
    calc Cx * (n : ℝ) ^ (-α) ≤ Cx * (Real.log 3 ^ α * |Real.log ε| ^ (-α)) :=
          mul_le_mul_of_nonneg_left hnk hCx.le
      _ = (Cx * Real.log 3 ^ α) * |Real.log ε| ^ (-α) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCfin (Real.rpow_nonneg hl.le _)

/-! ### Satisfiability witnesses -/

namespace Witness

variable {d : ℕ}

theorem hMinusOneVec_zero (V : Set (Vec d)) : s12_hMinusOneVec V (fun _ => (0 : Vec d)) = 0 := by
  simp [s12_hMinusOneVec, wMinusOneBar]

/-- For the zero shell sequence the coefficient is `ν Id`. -/
theorem coeff_zero (nu : ℝ) : SuperdiffusionCLT.Section6.fullCoefficientRecentered nu
    (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) = fun _ => nu • (1 : Mat d) := by
  funext x
  have : SuperdiffusionCLT.Section6.fullStreamRecentered
      (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) x = 0 := by
    simp [SuperdiffusionCLT.Section6.fullStreamRecentered,
      SuperdiffusionCLT.Section2.Cutoff.shellReg,
      SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq,
      SuperdiffusionCLT.Frozen.Assumptions.ShellField.zero_apply]
  simp [SuperdiffusionCLT.Section6.fullCoefficientRecentered, this]

theorem stream_zero (x : Vec d) : SuperdiffusionCLT.Section6.fullStreamRecentered
      (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) x = 0 := by
  simp [SuperdiffusionCLT.Section6.fullStreamRecentered,
    SuperdiffusionCLT.Section2.Cutoff.shellReg,
    SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq,
    SuperdiffusionCLT.Frozen.Assumptions.ShellField.zero_apply]

/-- The black-box comparison holds for the zero shell sequence (the field is `ν Id`). -/
theorem blackbox_zero [NeZero d] {V : Set (Vec d)} (hV : IsSmoothBoundedDomain V) (nu : ℝ)
    (hnu : 0 < nu) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (f' : Vec d → ℝ) (g' u' uh' : H1Function V)
    (h1 : IsDirichletSolution (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu
      (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d)) V f' g' u')
    (h2 : IsDirichletSolution (fun _ => nu • (1 : Mat d)) V f' g' uh') :
    eLpNorm (fun x => u'.toFun x - uh'.toFun x) ⊤ (volume.restrict V) +
        hMinusOneVec V (fun x => u'.grad x - uh'.grad x) +
        hMinusOneVec V (fun x =>
          matVecMul (nu⁻¹ • (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu
            (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) x - (0 : Mat d)))
            (u'.grad x) - uh'.grad x) ≤
      ENNReal.ofReal c₁ * eLpNorm f' ⊤ (volume.restrict V) +
        ENNReal.ofReal c₂ * eLpNorm (fun x => eucNorm (g'.grad x)) ⊤ (volume.restrict V) := by
  rw [coeff_zero] at h1
  by_cases hf : eLpNorm f' ⊤ (volume.restrict V) = ⊤
  · rw [hf, ENNReal.mul_top (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hc₁)]
    simp
  · have hWt : volume V ≠ ⊤ := by
      simpa only [ne_eq, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using hV.2.2.1.isFiniteMeasure_restrict_volume.measure_univ_lt_top.ne
    have hf2 : MemLp f' 2 (volume.restrict V) := by
      refine lt_of_le_of_lt (s12_eLpNorm_two_le _ f' hf) ?_
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hf)
        (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hWt))
    obtain ⟨hv, hg⟩ := (rc_dirichlet_wellPosed_of_elliptic hV.1 hV.2.2.1.isBounded
      (rc_isEllipticFieldOn_smul_one hnu hV.1.measurableSet) hf2 g').2 u' uh' h1 h2
    have e1 : eLpNorm (fun x => u'.toFun x - uh'.toFun x) ⊤ (volume.restrict V) = 0 := by
      rw [eLpNorm_congr_ae (g := fun _ => (0 : ℝ)) (hv.mono fun x hx => by simp [hx])]
      simp
    have e2 : s12_hMinusOneVec V (fun x => u'.grad x - uh'.grad x) = 0 := by
      rw [← hMinusOneVec_zero V]
      exact s12_hMinusOneVec_congr_ae (hg.mono fun x hx => by simp [hx])
    have e3 : s12_hMinusOneVec V (fun x => matVecMul (nu⁻¹ •
        (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu
          (SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d) x - (0 : Mat d)))
        (u'.grad x) - uh'.grad x) = 0 := by
      rw [← hMinusOneVec_zero V]
      refine s12_hMinusOneVec_congr_ae (hg.mono fun x hx => ?_)
      rw [coeff_zero]
      have : matVecMul (nu⁻¹ • (nu • (1 : Mat d) - 0)) (u'.grad x) = u'.grad x := by
        simp [p13_matVecMul_one, smul_smul, inv_mul_cancel₀ hnu.ne']
      rw [this, sub_eq_zero]
      exact hx
    show _ + s12_hMinusOneVec _ _ + s12_hMinusOneVec _ _ ≤ _
    rw [e1, e2, e3]
    simp

theorem ball_data [NeZero d] :
    IsSmoothBoundedDomain (SuperdiffusionCLT.Section6.euclidBall (d := d) 1) ∧
      SuperdiffusionCLT.Section6.euclidBall (d := d) 1 ⊆ axisCube (fun _ : Fin d => (-1 : ℝ)) 2 := by
  refine ⟨isSmoothBoundedDomain_euclidBall, ?_⟩
  intro x hx
  have h := SuperdiffusionCLT.Section6.euclidBall_subset_ball (d := d) one_pos hx
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)] at h
  rw [axisCube, Set.mem_pi]
  intro i _
  have := abs_lt.1 (by simpa only [Real.norm_eq_abs] using h i)
  simp only [Set.mem_Ioo]
  constructor <;> linarith only [this.1, this.2]

/-- **Witness for `s5_chain`**: the zero shell sequence, the unit ball, zero data. -/
example [NeZero d] (hd : 2 ≤ d) : True := by
  obtain ⟨CL, CH, hCL, hCH, hch⟩ := s5_chain (d := d) hd
  obtain ⟨hUs, hUL⟩ := ball_data (d := d)
  set U : Set (Vec d) := SuperdiffusionCLT.Section6.euclidBall (d := d) 1 with hU
  set ω0 := SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d with hω0
  have hBw : ∀ x ∈ (1 : ℝ)⁻¹ • U, ∀ i j,
      |SuperdiffusionCLT.Section6.fullCoefficientRecentered (1 : ℝ) ω0 x i j| ≤ 1 := by
    intro x _ i j
    rw [hω0, coeff_zero]
    by_cases h : i = j <;> simp [h]
  have hMK : ∀ i j, |(Matrix.of fun i j => ⨍ w in (1 : ℝ)⁻¹ • U,
      SuperdiffusionCLT.Section6.fullStreamRecentered ω0 w i j) i j - (0 : Mat d) i j| ≤ 0 := by
    intro i j
    simp [hω0, stream_zero]
  have hWsm : IsSmoothBoundedDomain ((1 : ℝ)⁻¹ • U) :=
    w0_isSmoothBoundedDomain_smul hUs (by norm_num)
  have key := hch hUs (fun _ : Fin d => (-1 : ℝ)) (LU := 2) (by norm_num) hUL 1 ω0 (ε := 1)
    one_pos (S := 1) (sh := 1) one_pos one_pos 1 1 1 0 zero_le_one le_rfl hBw 0 hMK
    (fun f' g' u' uh' h1 h2 => blackbox_zero hWsm 1 one_pos _ _ (by norm_num) f' g' u' uh' h1 h2)
    0 0 0 0 (rc_isDirichletSolution_zero _ _) (rc_isDirichletSolution_zero _ _) (by simp)
    (by simp [eucNorm, vecNormSq, vecDot])
  trivial

/-- **Witness for `s5_pointwise`**: `α = 1/4`, `α₀ = 1/3`, the unit ball, `T = 1`, the zero shell
sequence with `ν` equal to the scale `S_ε` (so that the field is `shom Id` exactly), `ε = 3^{-m}`
with `m` above the threshold, zero data. -/
example [NeZero d] (hd : 2 ≤ d) : True := by
  obtain ⟨hUs, hUL⟩ := ball_data (d := d)
  set U : Set (Vec d) := SuperdiffusionCLT.Section6.euclidBall (d := d) 1 with hU
  obtain ⟨Cx, N1, hCx, hpt⟩ := s5_pointwise hd (α := 1 / 4) (α0 := 1 / 3) (ρ := 1 / 3) (σ' := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hUs
    (fun _ : Fin d => (-1 : ℝ)) (LU := 2) (by norm_num) hUL (T := 1) le_rfl 1 1 0 zero_le_one
    zero_le_one le_rfl 1 one_pos
  set m : ℕ := ⌈max N1 2⌉₊ with hm
  have hmN : max N1 2 ≤ (m : ℝ) := Nat.le_ceil _
  have hm2 : (2 : ℝ) ≤ m := (le_max_right _ _).trans hmN
  have hm0 : (0 : ℝ) < m := by linarith only [hm2]
  set ε : ℝ := ((3 : ℝ) ^ m)⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hεinv : ε⁻¹ = (3 : ℝ) ^ m := inv_inv _
  have hε2 : ε ≤ 1 / 2 := by
    have h1 : (3 : ℝ) ^ 1 ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (by exact_mod_cast (by linarith only [hm2] : (1 : ℝ) ≤ m))
    rw [hε, inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith only [h1]
  have hlogb : Real.logb 3 ε⁻¹ = m := by
    rw [hεinv, ← Real.rpow_natCast, Real.logb_rpow (by norm_num) (by norm_num)]
  have hK : s12_scaleK (ε / 1) = m := by
    rw [div_one]
    unfold s12_scaleK
    rw [hlogb, Nat.ceil_natCast]
  set ν : ℝ := s12_scaleS 1 ε with hν
  have hνeq : ν = Real.sqrt (2 * 1 * Real.log 3 * m) := by
    rw [hν, s12_scaleS_eq hε0 hε2, hlogb]
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hνpos : 0 < ν := by rw [hνeq]; exact Real.sqrt_pos.2 (by positivity)
  set ω0 := SuperdiffusionCLT.Assumptions.ShellLaw.zeroShellSeq d with hω0
  have hWsm : IsSmoothBoundedDomain (ε⁻¹ • U) := w0_isSmoothBoundedDomain_smul hUs (inv_pos.2 hε0)
  have hBw : ∀ x ∈ ε⁻¹ • U, ∀ i j,
      |SuperdiffusionCLT.Section6.fullCoefficientRecentered ν ω0 x i j| ≤ ν := by
    intro x _ i j
    rw [hω0, coeff_zero]
    by_cases h : i = j <;> simp [h, abs_of_pos hνpos, hνpos.le]
  have hMK : ∀ i j, |(Matrix.of fun i j => ⨍ w in ε⁻¹ • U,
      SuperdiffusionCLT.Section6.fullStreamRecentered ω0 w i j) i j - (0 : Mat d) i j| ≤ 0 := by
    intro i j
    simp [hω0, stream_zero]
  have hcpos : 0 < (1 : ℝ) * deltaScale 1 (1 / 3) (m : ℝ) * (ν⁻¹ * (3 : ℝ) ^ (2 * m)) := by
    have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith only [hm2])
    have hδ : 0 < deltaScale 1 (1 / 3) (m : ℝ) := by
      unfold deltaScale
      exact mul_pos (mul_pos one_pos (Real.rpow_pos_of_pos hm0 _)) hlog
    exact mul_pos (mul_pos one_pos hδ) (mul_pos (inv_pos.2 hνpos) (by positivity))
  have key := hpt ν ω0 (fun _ => ν) (ε := ε) hε0 hε2 (by rw [hK]; exact (le_max_left _ _).trans hmN)
    (by simpa only using hνpos)
    (by
      have : s12_scaleS 1 (ε / 1) = ν := by rw [div_one]
      rw [this, div_self hνpos.ne']
      norm_num)
    (by
      have : s12_scaleS 1 (ε / 1) = ν := by rw [div_one]
      rw [this, div_self hνpos.ne', sub_self, abs_zero]
      positivity)
    (by
      rw [hK, ← hνeq]
      linarith only [hνpos])
    ν 0 0 hBw hMK (by simp)
    (fun f' g' u' uh' h1 h2 => by
      rw [hK] at *
      exact blackbox_zero hWsm ν hνpos _ _ (by simpa only [one_div, one_mul] using hcpos) f' g' u' uh' h1 h2)
    0 0 0 0 (rc_isDirichletSolution_zero _ _) (rc_isDirichletSolution_zero _ _)
  trivial

end Witness

end SuperdiffusionCLT.Section7
