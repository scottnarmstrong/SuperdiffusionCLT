/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorApproxF
public import SuperdiffusionCLT.Section7.Prereq.L2InteriorC
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorFinal
public import SuperdiffusionCLT.Section6.Root.CenteredRecenteredBridge

/-!
# Interior approximation: the almost-sure cell bound at a centre `y`

The local mollified flux bound `m1_mollified_flux` transferred to the cells
`y + 3^n k + □_{n+1}` of a global solution on a subset `W` of the translated cube `y + □_m`
(the translated counterpart of `l2b_ae_cell`).
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The field `ν Id + centeredStreamField ω (y + □_k)` of the inputs at the centre `y`. -/
noncomputable def ia_field (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (y : Vec d) (k : ℕ) : CoeffField d :=
  fun x => nu • (1 : Mat d) + SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
    (translateSet y (cubeSet (originCube d (k : ℤ)))) x

/-- The shifted cube is the translated open cube. -/
theorem ip_shiftCube_eq (y : Vec d) (m : ℤ) :
    shiftCube y m = translateSet y (openCubeSet (originCube d m)) := by
  ext x
  rw [mem_translateSet_iff_sub_mem]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hx
    exact ⟨x - y, hx, by simp⟩

/-- **The almost-sure cell bound at the centre `y`.** -/
theorem ia_ae_cell (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ M : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → C ≤ M →
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : MeasureTheory.ProbabilityMeasure
        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ, Measurable X0 ∧
          (∀ omega, 1 ≤ X0 omega) ∧
          Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X0 omega)) Lhat ∧
        ∀ y : Vec d, ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
          ∀ m n : ℕ,
          X0 (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence y omega) ≤
            (3 : ℝ) ^ m → Lhat ≤ (m : ℝ) → (m : ℤ) - ⌈M * Real.log (m : ℝ)⌉ ≤ (n : ℤ) →
          n + 1 ≤ m →
          ∀ W : Set (Vec d), W ⊆ shiftCube y (m : ℤ) →
          ∀ (u : H1Function W) (f : Vec d → ℝ), AEMeasurable f (volume.restrict W) →
          IsWeakSolutionOn (ia_field nu omega y m) W u f (fun _ => 0) →
          ∀ (η : Vec d → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) → LipschitzWith L η →
          (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
          ∀ j : Fin d → ℤ, l2b_cell (y + l2b_pt n j) (n + 1) ⊆ W →
          ∀ x ∈ l2b_cell (y + l2b_pt n j) n,
            ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ (n : ℤ)) η (fun w => matVecMul
                (ia_field nu omega y m w - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                  nu m P) • (1 : Mat d)) (u.grad w)) x‖ ≤
              ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) *
                (ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                    nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu) *
                  l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                    (l2b_cell (y + l2b_pt n j) (n + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
                ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                    nu m P) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu +
                    C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| +
                      (m : ℝ) ^ (1 + ρ))) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)) *
                  l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                    (l2b_cell (y + l2b_pt n j) (n + 1)) (fun x => ‖f x‖ₑ)
                    (Real.conjExponent (sobStar d))) := by
  obtain ⟨C, hC, H⟩ := m1_mollified_flux d hd hInputs
  refine ⟨C, hC, fun nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1 hCM => ?_⟩
  obtain ⟨Lhat, hL, H2⟩ := H nu hnu hnu1 cStar hcStar K ε ρ M hε hε1 hρ hρ1 hCM
  refine ⟨Lhat, hL, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨X0, hm, h1, hO, hae⟩ := H2 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨X0, hm, h1, hO, fun y => ?_⟩
  filter_upwards [hae y] with omega hω
  intro m n hX hLm hn1 hn2 W hWm u f hf hsol η A L hηA hηL hη0 j hj x hx
  set z : Vec d := l2b_pt n j with hz
  have hsub : translateSet (y + z) (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) ⊆ W := by
    refine Set.Subset.trans (fun w hw => ?_) hj
    rw [mem_translateSet_iff_sub_mem] at hw
    exact (mem_translateSet_iff_sub_mem (U := cubeSet (originCube d ((n + 1 : ℕ) : ℤ)))).2
      (openCubeSet_subset_cubeSet _ hw)
  have hWm' : W ⊆ translateSet y (openCubeSet (originCube d (m : ℤ))) := by
    rw [← ip_shiftCube_eq]; exact hWm
  have hsubz : translateSet z (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro w hw
    have h1 : w + y ∈ translateSet (y + z) (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))) := by
      rw [mem_translateSet_iff_sub_mem] at hw ⊢
      have : w + y - (y + z) = w - z := by abel
      rw [this]; exact hw
    have h2 := hWm' (hsub h1)
    rw [mem_translateSet_iff_sub_mem, add_sub_cancel_right] at h2
    exact h2
  have himg := wh2_shift_image_subset (n + 1) m z hsubz
  have hz9 : (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((fun i => 9 * j i) i : ℤ) : ℝ)) = z := by
    funext i
    simp only [hz, l2b_pt]
    have : (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * 9 = 3 ^ n := by
      have e : ((n + 1 : ℕ) : ℤ) - 3 = (n : ℤ) - 2 := by push_cast; ring
      rw [e, zpow_sub₀ (by norm_num)]
      simp only [zpow_natCast]
      norm_num
    have h9 : (((9 * j i : ℤ)) : ℝ) = 9 * (j i : ℝ) := by push_cast; ring
    show (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((9 * j i : ℤ)) : ℝ) = (3 : ℝ) ^ n * (j i : ℝ)
    rw [h9, ← mul_assoc, this]
  have himg' : (fun x => (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) *
      (((fun i => 9 * j i) i : ℤ) : ℝ)) + x) '' cubeSet (originCube d ((n + 1 : ℕ) : ℤ)) ⊆
        cubeSet (originCube d (m : ℤ)) := by
    rw [hz9]; exact himg
  have key := hω m n hX hLm hn1 hn2 (fun i => 9 * j i) himg'
  have hs : 1 < sobStar d := by linarith only [two_lt_sobStar hd]
  have hHC : (sobStar d).HolderConjugate (Real.conjExponent (sobStar d)) :=
    Real.HolderConjugate.conjExponent hs
  have hconj : (ENNReal.ofReal (sobStar d)).conjExponent =
      ENNReal.ofReal (Real.conjExponent (sobStar d)) := l2b_conj_exponent hHC
  have hp0 : 0 < Real.conjExponent (sobStar d) := hHC.symm.pos
  have hfield : ∀ w, nu • (1 : Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (translateSet y (cubeSet (originCube d (m : ℤ))))
        (y + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((fun i => 9 * j i) i : ℤ) : ℝ)) + w) =
      ia_field nu omega y m (w + (y + z)) := by
    intro w
    rw [hz9]
    unfold ia_field
    rw [show y + z + w = w + (y + z) by abel]
  have hfun : (fun w => nu • (1 : Mat d) +
      SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (translateSet y (cubeSet (originCube d (m : ℤ))))
        (y + (fun i => (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - 3) * (((fun i => 9 * j i) i : ℤ) : ℝ)) + w)) =
      fun w => ia_field nu omega y m (w + (y + z)) := funext hfield
  have hx0 : x - (y + z) ∈ cubeSet (originCube d (n : ℤ)) := (mem_translateSet_iff_sub_mem).1 hx
  have hxz : (y + z) + (x - (y + z)) = x := add_sub_cancel (y + z) x
  have b1 := l2b_cell_transfer n (y + z) hsub hf hsol
    (M := fun w => ia_field nu omega y m w -
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) • (1 : Mat d))
    (a' := fun w => ia_field nu omega y m (w + (y + z))) (fun w => rfl)
    (h := (3 : ℝ) ^ (n : ℤ)) (η := η) hp0
    (α := ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) *
      ENNReal.ofReal (C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu))
    (β := ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) *
      ENNReal.ofReal ((C * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) *
        (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) * Real.sqrt nu +
        C * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)| +
          (m : ℝ) ^ (1 + ρ))) * (C * (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) / nu)))
    (fun v g hv x0 hx0' => by
      have hv' := hv
      rw [← hfun] at hv'
      have := (key v g hv' η A L hηA hηL hη0 x0 hx0').1
      rw [hconj] at this
      refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
      · congr 3
        funext w
        rw [hfield w]
      · simp only [eucNorm]; ring)
    (x - (y + z)) hx0
  rw [hxz] at b1
  refine b1.trans (le_of_eq ?_)
  ring

open SuperdiffusionCLT.Frozen.Assumptions SuperdiffusionCLT.Section2.Cutoff in
theorem ia_ae_skew [NeZero d] {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (nu : ℝ) (y : Vec d) :
    ∀ᵐ omega ∂P.toMeasure, ∀ k : ℕ, ∃ S : Mat d, matTranspose S = -S ∧
      ∀ x : Vec d, ia_field nu omega y k x = Section6.fullCoefficientRecentered nu omega x + S := by
  have hqmp := (translateSequence_measurePreserving hPrefix hJ2 y).quasiMeasurePreserving
  filter_upwards [lip_frame_field d hJ3 nu, hqmp.ae (Section6.ae_centered_eq_recentered_add_skew hJ3 nu)]
    with omega hF hbr k
  obtain ⟨S, hS, hSx⟩ := hF y
  obtain ⟨K, hK, hKx⟩ := hbr k
  refine ⟨S + K, ?_, fun x => ?_⟩
  · ext i j
    have h1 := congrFun (congrFun hS i) j
    have h2 := congrFun (congrFun hK i) j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply, Matrix.add_apply] at h1 h2 ⊢
    linarith only [h1, h2]
  · have e1 := b2_csf_translate_apply y omega (cubeSet (originCube d (k : ℤ))) (x - y)
    rw [add_sub_cancel] at e1
    have e2 := hKx (x - y)
    have e3 := hSx (x - y)
    rw [sub_add_cancel] at e3
    unfold ia_field
    rw [← e1, e2, e3]
    abel

end SuperdiffusionCLT.Section7
