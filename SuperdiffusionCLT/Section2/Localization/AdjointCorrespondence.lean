/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.NegationClosures
public import Homogenization.Book.Ch02.Theorems.DoubledMu
public import Homogenization.Book.Ch02.Theorems.GradientUniqueness
public import Homogenization.CoarseGraining.BlockFormalism.EllipticBounds

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem potentialZeroTraceFieldOn_of_ae_eq {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) :
    Book.Ch01.PotentialZeroTraceFieldOn U g := by
  refine ⟨(MeasureTheory.memLp_congr_ae hfg).mp hf.1, ?_⟩
  rcases hf.2 with ⟨u, hu⟩
  exact ⟨u, hfg.symm.trans hu⟩

private theorem solenoidalZeroNormalTraceFieldOn_of_ae_eq {U : Set (Vec d)}
    {f g : Vec d → Vec d}
    (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hf : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U f) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g := by
  refine ⟨(MeasureTheory.memLp_congr_ae hfg).mp hf.1, ?_⟩
  intro φ
  calc
    ∫ x in U, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume =
        ∫ x in U, vecDot (f x) (φ.grad x) ∂MeasureTheory.volume := by
          exact MeasureTheory.integral_congr_ae
            (hfg.mono fun x hx => by simp [hx])
    _ = 0 := hf.2 φ

private theorem isDoubledMuAdmissible_of_sameAE
    {U : Book.Ch02.Domain d} {P : BlockVec d}
    {X Y : Book.Ch02.DoubledField d}
    (hXY : Book.Ch02.DoubledField.SameAE (U := U) X Y)
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    Book.Ch02.IsDoubledMuAdmissible U P Y := by
  refine ⟨?_, ?_⟩
  · apply potentialZeroTraceFieldOn_of_ae_eq
      (hXY.1.mono fun x hx => congrArg (· - P.1) hx)
    exact hX.1
  · apply solenoidalZeroNormalTraceFieldOn_of_ae_eq
      (hXY.2.mono fun x hx => congrArg (· - P.2) hx)
    exact hX.2

private theorem doubledMuValue_eq_of_sameAE
    {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U}
    {X Y : Book.Ch02.DoubledField d}
    (hXY : Book.Ch02.DoubledField.SameAE (U := U) X Y) :
    Book.Ch02.doubledMuValue U a X = Book.Ch02.doubledMuValue U a Y := by
  unfold Book.Ch02.doubledMuValue Book.Ch02.average
  congr 1
  exact MeasureTheory.integral_congr_ae <|
    hXY.1.and hXY.2 |>.mono fun x hxy => by
      simp only [Book.Ch02.DoubledField.eval, Book.Ch02.blockEnergyDensityAt]
      rw [hxy.1, hxy.2]

theorem isDoubledMuMinimizer_of_sameAE
    {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U} {P : BlockVec d}
    {X Y : Book.Ch02.DoubledField d}
    (hXY : Book.Ch02.DoubledField.SameAE (U := U) X Y)
    (hX : Book.Ch02.IsDoubledMuMinimizer U a P X) :
    Book.Ch02.IsDoubledMuMinimizer U a P Y := by
  refine ⟨isDoubledMuAdmissible_of_sameAE hXY hX.1, ?_⟩
  intro Z hZ
  calc
    Book.Ch02.doubledMuValue U a Y = Book.Ch02.doubledMuValue U a X :=
      (doubledMuValue_eq_of_sameAE hXY).symm
    _ ≤ Book.Ch02.doubledMuValue U a Z := hX.2 Z hZ

private theorem blockMatrixOfCoeff_lower_flipFlux (A : Mat d) (p q : Vec d) :
    (blockMatVecMul (blockMatrixOfCoeff (matTranspose A)) (p, -q)).2 =
      - (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).2 := by
  have hLR :
      (blockMatrixOfCoeff (matTranspose A)).lowerRight =
        (blockMatrixOfCoeff A).lowerRight := by
    simp [blockMatrixOfCoeff, symmPart_matTranspose]
  simp only [blockMatVecMul_snd]
  rw [blockMatrixOfCoeff_matTranspose_lowerLeft, hLR]
  simp only [neg_matVecMul, matVecMul_neg]
  abel

private theorem blockMatrixOfCoeff_upper_flipFlux (A : Mat d) (p q : Vec d) :
    (blockMatVecMul (blockMatrixOfCoeff (matTranspose A)) (p, -q)).1 =
      (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).1 := by
  simp only [blockMatVecMul_fst]
  rw [blockMatrixOfCoeff_matTranspose_upperLeft,
    blockMatrixOfCoeff_matTranspose_upperRight]
  simp only [neg_matVecMul, matVecMul_neg, neg_neg]

private theorem doubledFieldOfScalarMaximizers_sameAE_of_isResponseMaximizers
    {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) (v : Book.Ch02.Solution U a)
    (vStar : Book.Ch02.Solution U a.transpose)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v)
    (hvStar : Book.Ch02.IsResponseMaximizer U a.transpose p (-q) vStar)
    {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U a (-p, q) X) :
    Book.Ch02.DoubledField.SameAE (U := U) X
      (Book.Ch02.doubledFieldOfScalarMaximizers a v vStar) := by
  have hXFlip := isDoubledMuMinimizer_flipFlux hX
  have hXStar :
      Book.Ch02.IsDoubledMuMinimizer U a.transpose (-p, -q)
        (doubledFieldFlipFlux X) := by
    simpa [blockVecFlipFlux] using hXFlip
  have hGrad :=
    Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient
      U a p q hX
  have hFlux :=
    Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux
      U a p q hX
  have hGradStar :=
    Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient
      U a.transpose p (-q) hXStar
  have hFluxStar :=
    Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux
      U a.transpose p (-q) hXStar
  have hCanGrad :=
    Book.Ch02.canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hv
  have hCanGradStar :=
    Book.Ch02.canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hvStar
  have hCanGradFlux :
      (fun x => matVecMul (a.toCoeffField x)
        ((Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) p q).toSolution.toH1.grad x)) =ᵐ[
            volumeMeasureOn (U : Set (Vec d))]
        fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x) :=
    by
      filter_upwards [hCanGrad] with x hx
      rw [hx]
  have hCanGradStarFlux :
      (fun x => matVecMul (a.transpose.toCoeffField x)
        ((Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a.transpose) p (-q)).toSolution.toH1.grad x)) =ᵐ[
            volumeMeasureOn (U : Set (Vec d))]
        fun x => matVecMul (a.transpose.toCoeffField x)
          (vStar.toH1.grad x) :=
    by
      filter_upwards [hCanGradStar] with x hx
      rw [hx]
  have hGrad' :
      (fun x => X.potential x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2) =ᵐ[
            volumeMeasureOn (U : Set (Vec d))]
        fun x => v.toH1.grad x :=
    hGrad.trans hCanGrad
  have hFlux' :
      (fun x => X.flux x +
          (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).1) =ᵐ[
            volumeMeasureOn (U : Set (Vec d))]
        fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x) :=
    hFlux.trans hCanGradFlux
  have hGradStar' :
      (fun x => (doubledFieldFlipFlux X).potential x +
          (blockMatVecMul (blockCoeffField a.transpose.toCoeffField x)
            ((doubledFieldFlipFlux X).eval x)).2) =ᵐ[
              volumeMeasureOn (U : Set (Vec d))]
        fun x => vStar.toH1.grad x := by
    exact hGradStar.trans hCanGradStar
  have hFluxStar' :
      (fun x => (doubledFieldFlipFlux X).flux x +
          (blockMatVecMul (blockCoeffField a.transpose.toCoeffField x)
            ((doubledFieldFlipFlux X).eval x)).1) =ᵐ[
              volumeMeasureOn (U : Set (Vec d))]
        fun x => matVecMul (a.transpose.toCoeffField x) (vStar.toH1.grad x) := by
    exact hFluxStar.trans hCanGradStarFlux
  constructor
  · filter_upwards [hGrad', hGradStar'] with x hg hgs
    have hgs' := hgs
    change X.potential x +
        (blockMatVecMul (blockMatrixOfCoeff (matTranspose (a.toCoeffField x)))
          (X.potential x, -X.flux x)).2 = vStar.toH1.grad x at hgs'
    rw [blockMatrixOfCoeff_lower_flipFlux] at hgs'
    change X.potential x = (1 / 2 : ℝ) •
        (v.toH1.grad x + vStar.toH1.grad x)
    rw [← hg, ← hgs']
    ext i
    simp [blockCoeffField, Book.Ch02.DoubledField.eval]
    ring
  · filter_upwards [hFlux', hFluxStar'] with x hf hfs
    have hfs' := hfs
    change -X.flux x +
        (blockMatVecMul (blockMatrixOfCoeff (matTranspose (a.toCoeffField x)))
          (X.potential x, -X.flux x)).1 =
      matVecMul (matTranspose (a.toCoeffField x)) (vStar.toH1.grad x) at hfs'
    rw [blockMatrixOfCoeff_upper_flipFlux] at hfs'
    change X.flux x = (1 / 2 : ℝ) •
        (matVecMul (a.toCoeffField x) (v.toH1.grad x) -
          matVecMul (matTranspose (a.toCoeffField x)) (vStar.toH1.grad x))
    rw [← hf, ← hfs']
    ext i
    simp [blockCoeffField, Book.Ch02.DoubledField.eval]
    ring

theorem doubledFieldOfScalarMaximizers_isDoubledMuMinimizer
    {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) (v : Book.Ch02.Solution U a)
    (vStar : Book.Ch02.Solution U a.transpose)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v)
    (hvStar : Book.Ch02.IsResponseMaximizer U a.transpose p (-q) vStar) :
    Book.Ch02.IsDoubledMuMinimizer U a (-p, q)
      (Book.Ch02.doubledFieldOfScalarMaximizers a v vStar) := by
  rcases (Book.Ch02.doubledMuTheory U a).minimizer_exists (-p, q) with
    ⟨X, hX⟩
  exact isDoubledMuMinimizer_of_sameAE
    (doubledFieldOfScalarMaximizers_sameAE_of_isResponseMaximizers
      a p q v vStar hv hvStar hX) hX

end
end SuperdiffusionCLT.Section2.Localization
