/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu
public import Homogenization.Book.Ch02.Theorems.DoubledMu
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The raw block quadratic form carried by a matrix and a block vector. -/
def averagedBlockQuadratic (A : Mat d) (X : BlockVec d) : ℝ :=
  blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X)

/-- The normalized average of a raw block quadratic field. -/
def averagedBlockQuadraticOn (U : Set (Vec d)) (A : Vec d → Mat d)
    (X : Vec d → BlockVec d) : ℝ :=
  volumeAverage U (fun x => averagedBlockQuadratic (A x) (X x))

def doubledFieldQuadraticOn {U : Homogenization.Book.Ch02.Domain d}
    (a : Homogenization.Book.Ch02.CoeffOn U)
    (X : Homogenization.Book.Ch02.DoubledField d) : ℝ :=
  averagedBlockQuadraticOn (U : Set (Vec d))
    (fun x => a.toCoeffField x) (fun x => X.eval x)

theorem doubledMuValue_eq_half_doubledFieldQuadraticOn
    {U : Homogenization.Book.Ch02.Domain d}
    (a : Homogenization.Book.Ch02.CoeffOn U)
    (X : Homogenization.Book.Ch02.DoubledField d) :
    Homogenization.Book.Ch02.doubledMuValue U a X =
      (1 / 2 : ℝ) * doubledFieldQuadraticOn a X := by
  unfold Homogenization.Book.Ch02.doubledMuValue doubledFieldQuadraticOn
    averagedBlockQuadraticOn averagedBlockQuadratic Homogenization.Book.Ch02.average
    volumeAverage Homogenization.Book.Ch02.blockEnergyDensityAt
  simp only [Homogenization.Internal.Ch02.BookCh02.book_blockMatrixField_eq_blockCoeffField]
  simp only [Homogenization.blockCoeffField]
  rw [MeasureTheory.integral_const_mul]
  ring

private theorem memVectorL2_of_sub_const
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {f : Vec d → Vec d} {v : Vec d}
    (hf : MemVectorL2 U (fun x => f x - v)) :
    MemVectorL2 U f := by
  have h := (MeasureTheory.memLp_const
    (μ := volumeMeasureOn U) (c := v) (p := 2)).add hf
  have heq : ((fun _ : Vec d => v) + fun x => f x - v) = f := by
    funext x
    simp only [Pi.add_apply]
    abel
  rwa [heq] at h

private theorem memBlockL2_of_doubledAdmissible
    {U : Homogenization.Book.Ch02.Domain d} {P : BlockVec d}
    {X : Homogenization.Book.Ch02.DoubledField d}
    (hX : Homogenization.Book.Ch02.IsDoubledMuAdmissible U P X) :
    MemBlockL2 (U : Set (Vec d))
      (fun x => X.eval x) := by
  have hp : MemVectorL2 (U : Set (Vec d)) X.potential :=
    memVectorL2_of_sub_const hX.1.1
  have hq : MemVectorL2 (U : Set (Vec d)) X.flux :=
    memVectorL2_of_sub_const hX.2.1
  exact memBlockL2_blockField hp hq

private theorem isDoubledTestField_sub_of_admissible
    {U : Homogenization.Book.Ch02.Domain d} {P : BlockVec d}
    {X Y : Homogenization.Book.Ch02.DoubledField d}
    (hX : Homogenization.Book.Ch02.IsDoubledMuAdmissible U P X)
    (hY : Homogenization.Book.Ch02.IsDoubledMuAdmissible U P Y) :
    Homogenization.Book.Ch02.IsDoubledTestField U (X - Y) := by
  rcases hX with ⟨hXp, hXq⟩
  rcases hY with ⟨hYp, hYq⟩
  rcases hXp with ⟨hXpmem, hXpae⟩
  rcases hYp with ⟨hYpmem, hYpae⟩
  rcases hXq with ⟨hXqmem, hXqsol⟩
  rcases hYq with ⟨hYqmem, hYqsol⟩
  have hsubpot : (X - Y).potential = X.potential - Y.potential := rfl
  have hsubflux : (X - Y).flux = X.flux - Y.flux := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [hsubpot]
      have hmem := hXpmem.sub hYpmem
      have heq : (fun x => X.potential x - P.1) -
          (fun x => Y.potential x - P.1) = X.potential - Y.potential := by
        funext x
        simp only [Pi.sub_apply]
        abel
      rw [heq] at hmem
      exact hmem
    · rcases hXpae with ⟨uX, huX⟩
      rcases hYpae with ⟨uY, huY⟩
      refine ⟨uX - uY, ?_⟩
      have hgrad : (uX - uY).toH1Function.grad =
          uX.toH1Function.grad - uY.toH1Function.grad := by
        change (uX.toH1Function + (-uY.toH1Function)).grad = _
        simp [H1Function.add_grad, H1Function.neg_grad]
        funext x
        simp [sub_eq_add_neg]
      filter_upwards [huX, huY] with x hx hy
      rw [hsubpot, hgrad]
      change X.potential x - Y.potential x =
        uX.toH1Function.grad x - uY.toH1Function.grad x
      rw [← hx, ← hy]
      ring
  · refine ⟨?_, ?_⟩
    · rw [hsubflux]
      have hmem := hXqmem.sub hYqmem
      have heq : (fun x => X.flux x - P.2) -
          (fun x => Y.flux x - P.2) = X.flux - Y.flux := by
        funext x
        simp only [Pi.sub_apply]
        abel
      rw [heq] at hmem
      exact hmem
    · intro φ
      have hXint := integrableOn_vecDot_of_memVectorL2
        hXqmem φ.grad_memVectorL2
      have hYint := integrableOn_vecDot_of_memVectorL2
        hYqmem φ.grad_memVectorL2
      have hEq :
          (fun x => vecDot ((X - Y).flux x) (φ.grad x)) =
            (fun x => vecDot (X.flux x - P.2) (φ.grad x)) -
              (fun x => vecDot (Y.flux x - P.2) (φ.grad x)) := by
        funext x
        rw [hsubflux]
        change vecDot (X.flux x - Y.flux x) (φ.grad x) = _
        simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
      calc
        ∫ x in (U : Set (Vec d)), vecDot ((X - Y).flux x) (φ.grad x) ∂volume =
            ∫ x in (U : Set (Vec d)),
              (vecDot (X.flux x - P.2) (φ.grad x) -
                vecDot (Y.flux x - P.2) (φ.grad x)) ∂volume := by
              rw [hEq]
              congr 1
        _ = (∫ x in (U : Set (Vec d)),
              vecDot (X.flux x - P.2) (φ.grad x) ∂volume) -
            (∫ x in (U : Set (Vec d)),
              vecDot (Y.flux x - P.2) (φ.grad x) ∂volume) := by
          exact MeasureTheory.integral_sub hXint hYint
        _ = 0 := by rw [hXqsol φ, hYqsol φ]; simp

theorem integrableOn_averagedBlockQuadratic_of_memBlockL2
    {U : Homogenization.Book.Ch02.Domain d}
    (a : Homogenization.Book.Ch02.CoeffOn U)
    {F : Vec d → BlockVec d}
    (hF : MemBlockL2 (U : Set (Vec d)) F) :
    IntegrableOn
      (fun x => averagedBlockQuadratic (a.toCoeffField x) (F x))
      (U : Set (Vec d)) := by
  let S : BlockState d :=
    BlockState.mk (fun x => (F x).1) (fun x => (F x).2)
  have hS : MemBlockL2 (U : Set (Vec d)) S.eval := by
    exact hF
  have hrep := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hIntRep := blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    hS hrep
  have hInt : IntegrableOn (fun x => blockEnergyDensity a.toCoeffField S x)
      (U : Set (Vec d)) := by
    refine hIntRep.congr ?_
    exact (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a).mono
      (fun x hx => by simp only [blockEnergyDensity, blockCoeffField, hx])
  have hEq :
      (fun x => averagedBlockQuadratic (a.toCoeffField x) (F x)) =
        (fun x => (2 : ℝ) * blockEnergyDensity a.toCoeffField S x) := by
    funext x
    simp [S, averagedBlockQuadratic, blockEnergyDensity, blockCoeffField,
      BlockState.eval]
  rw [hEq]
  simpa [MeasureTheory.IntegrableOn, smul_eq_mul] using hInt.const_mul 2

theorem averagedGap_of_doubledMuMinimizer
    {U : Homogenization.Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    (a : Homogenization.Book.Ch02.CoeffOn U)
    {P : BlockVec d} {X Y : Homogenization.Book.Ch02.DoubledField d}
    (hX : Homogenization.Book.Ch02.IsDoubledMuMinimizer U a P X)
    (hY : Homogenization.Book.Ch02.IsDoubledMuAdmissible U P Y) :
    averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => a.toCoeffField x) (fun x => (X - Y).eval x) =
      averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => a.toCoeffField x) (fun x => Y.eval x) -
        averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => a.toCoeffField x) (fun x => X.eval x) := by
  let D : Homogenization.Book.Ch02.DoubledField d := X - Y
  have hDtest := isDoubledTestField_sub_of_admissible hX.1 hY
  have hfirst := (Homogenization.Book.Ch02.doubledMuTheory U a).minimizer_first_variation
    P X hX D hDtest
  have hXmem := memBlockL2_of_doubledAdmissible hX.1
  have hYmem := memBlockL2_of_doubledAdmissible hY
  have hDmem : MemBlockL2 (U : Set (Vec d)) (fun x => D.eval x) := by
    exact hXmem.sub hYmem
  have hIntX := integrableOn_averagedBlockQuadratic_of_memBlockL2 a hXmem
  have hIntY := integrableOn_averagedBlockQuadratic_of_memBlockL2 a hYmem
  have hrep := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  let SX : BlockState d := BlockState.mk X.potential X.flux
  let SY : BlockState d := BlockState.mk Y.potential Y.flux
  let SD : BlockState d := BlockState.mk D.potential D.flux
  have hSX : MemBlockL2 (U : Set (Vec d)) SX.eval := by
    exact hXmem
  have hSY : MemBlockL2 (U : Set (Vec d)) SY.eval := by
    exact hYmem
  have hSD : MemBlockL2 (U : Set (Vec d)) SD.eval := by
    exact hDmem
  have hIntYXRep : IntegrableOn
      (blockPairingIntegrand
        (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U a).toCoeffField
        SY SX) (U : Set (Vec d)) :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := SY) (Y := SX) hSY hSX hrep
  have hIntYX : IntegrableOn
      (fun x => blockVecDot (Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)))
      (U : Set (Vec d)) := by
    refine hIntYXRep.congr ?_
    exact (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a).mono
      (fun x hx => by
        simp only [SX, SY, blockPairingIntegrand, BlockState.eval,
          Homogenization.Book.Ch02.DoubledField.eval, blockCoeffField, hx])
  have hfirstRaw :
      ∫ x in (U : Set (Vec d)),
          blockVecDot (D.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))
          ∂volume = 0 := by
    have hfun :
        (fun x => Homogenization.Book.Ch02.doubledBlockPairingIntegrand U a D X x) =
          (fun x => blockVecDot (D.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) := by
      funext x
      simp only [Homogenization.Book.Ch02.doubledBlockPairingIntegrand,
        Homogenization.Internal.Ch02.BookCh02.book_blockMatrixField_eq_blockCoeffField,
        Homogenization.blockCoeffField, Homogenization.Book.Ch02.DoubledField.eval]
    rw [← hfun]
    exact hfirst
  have hfirstAvg :
      volumeAverage (U : Set (Vec d))
          (fun x => blockVecDot (D.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) = 0 := by
    unfold volumeAverage
    rw [hfirstRaw]
    simp
  have hsplit :
      (fun x => blockVecDot (D.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) =
        (fun x => averagedBlockQuadratic (a.toCoeffField x) (X.eval x) -
          blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) := by
    funext x
    simp only [D, Homogenization.Book.Ch02.DoubledField.eval_sub]
    rw [sub_eq_add_neg, blockVecDot_add_left]
    have hnegDot : blockVecDot (-Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) =
        -blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := by
      simp [blockVecDot, vecDot_neg_left]; ring
    rw [hnegDot]
    simp only [averagedBlockQuadratic]
    ring
  have hcross :
      volumeAverage (U : Set (Vec d))
          (fun x => blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) =
        averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => a.toCoeffField x) (fun x => X.eval x) := by
    have hsplitAvg := volumeAverage_sub hIntX hIntYX
    have hsplitAvg' :
        volumeAverage (U : Set (Vec d))
            (fun x => blockVecDot (D.eval x)
              (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) =
          averagedBlockQuadraticOn (U : Set (Vec d))
            (fun x => a.toCoeffField x) (fun x => X.eval x) -
            volumeAverage (U : Set (Vec d))
              (fun x => blockVecDot (Y.eval x)
                (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) := by
      rw [hsplit]
      exact hsplitAvg
    linarith only [hfirstAvg, hsplitAvg']
  have hquad :
      (fun x => averagedBlockQuadratic (a.toCoeffField x) (D.eval x)) =
        (fun x => averagedBlockQuadratic (a.toCoeffField x) (X.eval x) +
          averagedBlockQuadratic (a.toCoeffField x) (Y.eval x) -
          2 * blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) := by
    funext x
    simp only [D, Homogenization.Book.Ch02.DoubledField.eval_sub]
    simp only [averagedBlockQuadratic]
    have hmat : blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x))
        (X.eval x - Y.eval x) =
        blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x) -
          blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x) := by
      rw [sub_eq_add_neg, blockMatVecMul_add]
      have hneg : blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x))
          (-Y.eval x) = -blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x))
            (Y.eval x) := by
        ext <;> simp [blockMatVecMul, matVecMul_neg] <;> ring
      rw [hneg]
      rfl
    rw [hmat, blockVecDot_sub_right]
    have hnegDot (W : BlockVec d) : blockVecDot (-Y.eval x) W =
        -blockVecDot (Y.eval x) W := by
      simp [blockVecDot, vecDot_neg_left]; ring
    have hfirstDot : blockVecDot (X.eval x - Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) =
        blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) -
          blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)) := by
      rw [sub_eq_add_neg, blockVecDot_add_left, hnegDot]
      ring
    have hsecondDot : blockVecDot (X.eval x - Y.eval x)
        (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)) =
        blockVecDot (X.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)) -
          blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (Y.eval x)) := by
      rw [sub_eq_add_neg, blockVecDot_add_left, hnegDot]
      ring
    rw [hfirstDot, hsecondDot]
    have hcrossComm := blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm
      (a.toCoeffField x) (X.eval x) (Y.eval x)
    rw [hcrossComm]
    ring
  have hquadAvg' :
      averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => a.toCoeffField x) (fun x => D.eval x) =
        averagedBlockQuadraticOn (U : Set (Vec d))
          (fun x => a.toCoeffField x) (fun x => X.eval x) +
          averagedBlockQuadraticOn (U : Set (Vec d))
            (fun x => a.toCoeffField x) (fun x => Y.eval x) -
          2 * volumeAverage (U : Set (Vec d))
            (fun x => blockVecDot (Y.eval x)
              (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) := by
    unfold averagedBlockQuadraticOn
    change volumeAverage (U : Set (Vec d))
        (fun x => averagedBlockQuadratic (a.toCoeffField x) (D.eval x)) =
      (volumeAverage (U : Set (Vec d))
          (fun x => averagedBlockQuadratic (a.toCoeffField x) (X.eval x)) +
        volumeAverage (U : Set (Vec d))
          (fun x => averagedBlockQuadratic (a.toCoeffField x) (Y.eval x))) -
        2 * volumeAverage (U : Set (Vec d))
          (fun x => blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)))
    rw [hquad]
    have hfun : (fun x => averagedBlockQuadratic (a.toCoeffField x) (X.eval x) +
        averagedBlockQuadratic (a.toCoeffField x) (Y.eval x) -
        2 * blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) =
        (fun x => averagedBlockQuadratic (a.toCoeffField x) (X.eval x) +
          averagedBlockQuadratic (a.toCoeffField x) (Y.eval x)) -
        (fun x => 2 * blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) := by
      funext x
      rfl
    rw [hfun, volumeAverage_sub]
    · have haddfun :
          (fun x => averagedBlockQuadratic (a.toCoeffField x) (X.eval x) +
            averagedBlockQuadratic (a.toCoeffField x) (Y.eval x)) =
            (fun x => averagedBlockQuadratic (a.toCoeffField x) (X.eval x)) +
              (fun x => averagedBlockQuadratic (a.toCoeffField x) (Y.eval x)) := by
        funext x
        rfl
      have hsmulfun :
          (fun x => 2 * blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) =
            (2 : ℝ) • (fun x => blockVecDot (Y.eval x)
              (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x))) := by
        funext x
        rfl
      rw [haddfun, hsmulfun]
      have hadd := volumeAverage_add hIntX hIntY
      have hsmul := volumeAverage_smul (U : Set (Vec d)) (2 : ℝ)
        (fun x => blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) (X.eval x)))
      rw [hadd, hsmul]
    · exact (hIntX.add hIntY)
    · exact hIntYX.const_mul 2
  rw [hquadAvg', hcross]
  ring

/-- Averaged form of the two gap identities, the two maximality inequalities,
and the quadratic remainder used in the small branch.  The split is pointwise,
because it is an identity of fields; every energy statement is normalized by
`volumeAverage U`. -/
structure Conj3AveragedGapBundle (U : Set (Vec d))
    (A At : Vec d → Mat d) (p q : Vec d) (eta : ℝ)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] where
  Z : Vec d → BlockVec d
  Zt : Vec d → BlockVec d
  Y : Vec d → BlockVec d
  hU : MeasurableSet U
  hsplit : ∀ x ∈ U, ((p, q) : BlockVec d) = (Z x - Zt x) + Y x
  hIntAD : IntegrableOn
    (fun x => averagedBlockQuadratic (A x) (Z x - Zt x)) U
  hIntAtD : IntegrableOn
    (fun x => averagedBlockQuadratic (At x) (Z x - Zt x)) U
  hIntAZ : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Z x)) U
  hIntAtZ : IntegrableOn (fun x => averagedBlockQuadratic (At x) (Z x)) U
  hIntAZt : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Zt x)) U
  hIntAtZt : IntegrableOn (fun x => averagedBlockQuadratic (At x) (Zt x)) U
  hIntAY : IntegrableOn (fun x => averagedBlockQuadratic (A x) (Y x)) U
  hIntAP : IntegrableOn
    (fun x => averagedBlockQuadratic (A x) ((p, q) : BlockVec d)) U
  hIntAtP : IntegrableOn
    (fun x => averagedBlockQuadratic (At x) ((p, q) : BlockVec d)) U
  hgapA : averagedBlockQuadraticOn U A (fun x => Z x - Zt x) =
    averagedBlockQuadraticOn U A Zt - averagedBlockQuadraticOn U A Z
  hgapAt : averagedBlockQuadraticOn U At (fun x => Z x - Zt x) =
    averagedBlockQuadraticOn U At Z - averagedBlockQuadraticOn U At Zt
  hmaxA : averagedBlockQuadraticOn U A Z ≤
    averagedBlockQuadraticOn U A (fun _ : Vec d => ((p, q) : BlockVec d))
  hmaxAt : averagedBlockQuadraticOn U At Zt ≤
    averagedBlockQuadraticOn U At (fun _ : Vec d => ((p, q) : BlockVec d))
  hY : averagedBlockQuadraticOn U A Y ≤
    eta * eta * averagedBlockQuadraticOn U At
      (fun _ : Vec d => ((p, q) : BlockVec d))
  hratioA : ∀ x ∈ U, ∀ W : BlockVec d,
    averagedBlockQuadratic (A x) W ≤
      averagedBlockQuadratic (At x) W +
        eta * averagedBlockQuadratic (At x) W
  hratioAt : ∀ x ∈ U, ∀ W : BlockVec d,
    averagedBlockQuadratic (At x) W ≤
      averagedBlockQuadratic (A x) W +
        eta * averagedBlockQuadratic (A x) W

end

end SuperdiffusionCLT.Section2.Localization
