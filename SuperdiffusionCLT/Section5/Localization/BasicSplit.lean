/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.BlockOffsetMinimizerB
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-!
# The gluing competitor of `e.setup.basic-split`

Fields on the subcubes `z + cu_n` of `cu_K` (the triadic cubes `Q ∈ descendantsAtScale cu_K n`),
each admissible on `Q` relative to an offset that agrees with a common global offset `G`, are glued
on the open cells and equal to `G` elsewhere. The glued field is admissible for the slope `P` on
`cu_K` (`isBlockMuAdmissible_gluedState`), hence
`P · bfA(cu_K) P` is at most the mean of the cell energies (`coarse_quad_le_subcubeMean`).

The proof is by zero extension of the cell potentials (`H10Function.extendByZeroToOpenSuperset`)
and by restriction of test functions to the open cells.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory

variable {d : ℕ}

theorem isPotentialZeroTraceOn_indicator_openCubeSet {Q R : TriadicCube d}
    (hRQ : openCubeSet R ⊆ openCubeSet Q) {w : Vec d → Vec d}
    (hw : IsPotentialZeroTraceOn (openCubeSet R) w) :
    IsPotentialZeroTraceOn (openCubeSet Q) ((openCubeSet R).indicator w) := by
  obtain ⟨u, rfl⟩ := hw
  exact ⟨u.extendByZeroToOpenSuperset (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ,
    rfl⟩

theorem isPotentialZeroTraceOn_finset_sum {ι : Type*} {U : Set (Vec d)} (S : Finset ι)
    (g : ι → Vec d → Vec d) (h : ∀ i ∈ S, IsPotentialZeroTraceOn U (g i)) :
    IsPotentialZeroTraceOn U (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isPotentialZeroTraceOn_zero (U := U)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isPotentialZeroTraceOn_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem memVectorL2_finset_sum {ι : Type*} {U : Set (Vec d)} (S : Finset ι)
    (g : ι → Vec d → Vec d) (h : ∀ i ∈ S, MemVectorL2 U (g i)) :
    MemVectorL2 U (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem memVectorL2_indicator_openCubeSet {Q R : TriadicCube d} {w : Vec d → Vec d}
    (hw : MemVectorL2 (openCubeSet R) w) :
    MemVectorL2 (openCubeSet Q) ((openCubeSet R).indicator w) := by
  have h1 : MemLp ((openCubeSet R).indicator w) 2 volume :=
    (memLp_indicator_iff_restrict (measurableSet_openCubeSet R)).2 hw
  exact h1.restrict _

theorem isSolenoidalZeroNormalTraceOn_indicator_openCubeSet {Q R : TriadicCube d}
    (hRQ : openCubeSet R ⊆ openCubeSet Q) {w : Vec d → Vec d}
    (hw : IsSolenoidalZeroNormalTraceOn (openCubeSet R) w) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q) ((openCubeSet R).indicator w) := by
  intro φ
  have h0 := hw (φ.restrict (isOpen_openCubeSet R) hRQ)
  have hfun : (fun x => vecDot ((openCubeSet R).indicator w x) (φ.grad x)) =
      (openCubeSet R).indicator (fun x => vecDot (w x) (φ.grad x)) := by
    funext x
    by_cases hx : x ∈ openCubeSet R <;> simp [Set.indicator, hx, vecDot]
  rw [hfun, integral_indicator (measurableSet_openCubeSet R),
    Measure.restrict_restrict (measurableSet_openCubeSet R), Set.inter_eq_left.2 hRQ]
  simpa [H1Function.restrict] using h0

theorem isSolenoidalZeroNormalTraceOn_finset_sum {ι : Type*} {U : Set (Vec d)} (S : Finset ι)
    (g : ι → Vec d → Vec d) (hm : ∀ i ∈ S, MemVectorL2 U (g i))
    (h : ∀ i ∈ S, IsSolenoidalZeroNormalTraceOn U (g i)) :
    IsSolenoidalZeroNormalTraceOn U (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isSolenoidalZeroNormalTraceOn_zero (U := U)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine isSolenoidalZeroNormalTraceOn_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))) ?_ ?_
    · intro φ
      exact integrableOn_vecDot_of_memVectorL2 (hm a (Finset.mem_insert_self a s))
        φ.grad_memVectorL2
    · intro φ
      exact integrableOn_vecDot_of_memVectorL2
        (memVectorL2_finset_sum s g (fun i hi => hm i (Finset.mem_insert_of_mem hi)))
        φ.grad_memVectorL2

/-- The glued competitor: `X Q` on the open cell `Q ∈ S`, the global offset `G` elsewhere. -/
noncomputable def gluedState (G : BlockState d) (S : Finset (TriadicCube d)) (X : TriadicCube d → BlockState d) :
    BlockState d where
  potential x := G.potential x +
    ∑ Q ∈ S, (openCubeSet Q).indicator (fun y => (X Q).potential y - G.potential y) x
  flux x := G.flux x +
    ∑ Q ∈ S, (openCubeSet Q).indicator (fun y => (X Q).flux y - G.flux y) x

theorem gluedState_potential_sub (G : BlockState d) (P : BlockVec d) (S : Finset (TriadicCube d))
    (X : TriadicCube d → BlockState d) :
    (fun x => (gluedState G S X).potential x - P.1) =
      (fun x => G.potential x - P.1) +
        ∑ Q ∈ S, (openCubeSet Q).indicator (fun y => (X Q).potential y - G.potential y) := by
  funext x
  simp only [gluedState, Pi.add_apply, Finset.sum_apply]
  abel

theorem gluedState_flux_sub (G : BlockState d) (P : BlockVec d) (S : Finset (TriadicCube d))
    (X : TriadicCube d → BlockState d) :
    (fun x => (gluedState G S X).flux x - P.2) =
      (fun x => G.flux x - P.2) +
        ∑ Q ∈ S, (openCubeSet Q).indicator (fun y => (X Q).flux y - G.flux y) := by
  funext x
  simp only [gluedState, Pi.add_apply, Finset.sum_apply]
  abel

/-- The glued competitor is admissible for the slope `P` on the big cube. -/
theorem isBlockMuAdmissible_gluedState {Qb : TriadicCube d} {n : ℤ} (hn : n ≤ Qb.scale)
    {P : BlockVec d} {G : BlockState d} (hG : IsBlockMuAdmissible (openCubeSet Qb) P G)
    {X : TriadicCube d → BlockState d}
    (hX : ∀ Q ∈ descendantsAtScale Qb n, IsBlockOffsetAdmissible (openCubeSet Q) G (X Q)) :
    IsBlockMuAdmissible (openCubeSet Qb) P (gluedState G (descendantsAtScale Qb n) X) := by
  have hsub : ∀ Q ∈ descendantsAtScale Qb n, openCubeSet Q ⊆ openCubeSet Qb :=
    fun Q hQ => openCubeSet_subset_of_mem_descendantsAtScale hn hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gluedState_potential_sub]
    exact hG.1.add (memVectorL2_finset_sum _ _ fun Q hQ =>
      memVectorL2_indicator_openCubeSet (hX Q hQ).1)
  · rw [gluedState_potential_sub]
    exact isPotentialZeroTraceOn_add hG.2.1 (isPotentialZeroTraceOn_finset_sum _ _ fun Q hQ =>
      isPotentialZeroTraceOn_indicator_openCubeSet (hsub Q hQ) (hX Q hQ).2.1)
  · rw [gluedState_flux_sub]
    exact hG.2.2.1.add (memVectorL2_finset_sum _ _ fun Q hQ =>
      memVectorL2_indicator_openCubeSet (hX Q hQ).2.2.1)
  · rw [gluedState_flux_sub]
    refine isSolenoidalZeroNormalTraceOn_add hG.2.2.2
      (isSolenoidalZeroNormalTraceOn_finset_sum _ _
        (fun Q hQ => memVectorL2_indicator_openCubeSet (hX Q hQ).2.2.1)
        (fun Q hQ => isSolenoidalZeroNormalTraceOn_indicator_openCubeSet (hsub Q hQ)
          (hX Q hQ).2.2.2)) ?_ ?_
    · intro φ
      exact integrableOn_vecDot_of_memVectorL2 hG.2.2.1 φ.grad_memVectorL2
    · intro φ
      exact integrableOn_vecDot_of_memVectorL2
        (memVectorL2_finset_sum _ _ fun Q hQ =>
          memVectorL2_indicator_openCubeSet (hX Q hQ).2.2.1) φ.grad_memVectorL2

/-- On the open cell `R ∈ S` of a family of pairwise disjoint cells, the glued state is `X R`. -/
theorem gluedState_eval_of_mem {Qb : TriadicCube d} {n : ℤ}
    {G : BlockState d} {X : TriadicCube d → BlockState d} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale Qb n) {x : Vec d} (hx : x ∈ openCubeSet R) :
    (gluedState G (descendantsAtScale Qb n) X).eval x = (X R).eval x := by
  have hzero : ∀ Q ∈ descendantsAtScale Qb n, Q ≠ R → x ∉ openCubeSet Q := by
    intro Q hQ hne hxQ
    exact Set.disjoint_left.1
      (disjoint_cubeSet_of_ne_of_mem_descendantsAtScale hQ hR hne)
      (openCubeSet_subset_cubeSet Q hxQ) (openCubeSet_subset_cubeSet R hx)
  have hp : ∑ Q ∈ descendantsAtScale Qb n,
      (openCubeSet Q).indicator (fun y => (X Q).potential y - G.potential y) x =
        (X R).potential x - G.potential x := by
    rw [Finset.sum_eq_single R]
    · simp [Set.indicator_of_mem hx]
    · intro Q hQ hne
      simp [Set.indicator_of_notMem (hzero Q hQ hne)]
    · intro h; exact absurd hR h
  have hf : ∑ Q ∈ descendantsAtScale Qb n,
      (openCubeSet Q).indicator (fun y => (X Q).flux y - G.flux y) x =
        (X R).flux x - G.flux x := by
    rw [Finset.sum_eq_single R]
    · simp [Set.indicator_of_mem hx]
    · intro Q hQ hne
      simp [Set.indicator_of_notMem (hzero Q hQ hne)]
    · intro h; exact absurd hR h
  simp only [BlockState.eval, gluedState, hp, hf]
  ext <;> simp

/-- `avsum_{z ∈ 3^n ℤ^d ∩ cu_K} f(z + cu_n)`: the mean over the subcubes of scale `n`
(real-valued). -/
noncomputable def subcubeMean (Qb : TriadicCube d) (n : ℤ) (f : TriadicCube d → ℝ) : ℝ :=
  ((descendantsAtScale Qb n).card : ℝ)⁻¹ * ∑ Q ∈ descendantsAtScale Qb n, f Q

/-- The average over a cube is the mean of the averages over its subcubes. -/
theorem volumeAverage_cubeSet_eq_subcubeMean {Qb : TriadicCube d} {n : ℤ} (hn : n ≤ Qb.scale)
    {f : Vec d → ℝ} (hf : IntegrableOn f (cubeSet Qb) volume) :
    volumeAverage (cubeSet Qb) f =
      subcubeMean Qb n (fun R => volumeAverage (cubeSet R) f) := by
  have hca : ∀ S : TriadicCube d, volumeAverage (cubeSet S) f = cubeAverage S f := fun S => by
    simp [volumeAverage, cubeAverage]
  have h := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Qb
    (Int.toNat (Qb.scale - n)) f hf
  simp only [hca]
  rw [h, subcubeMean, descendantsAtScale_eq_descendantsAtDepth Qb hn, descendantsAverage]

theorem subcubeMean_congr {Qb : TriadicCube d} {n : ℤ} {f g : TriadicCube d → ℝ}
    (h : ∀ R ∈ descendantsAtScale Qb n, f R = g R) : subcubeMean Qb n f = subcubeMean Qb n g := by
  unfold subcubeMean
  rw [Finset.sum_congr rfl h]

/-- Two functions agreeing on the open cell have the same average over the cell. -/
theorem volumeAverage_cubeSet_congr {R : TriadicCube d} {f g : Vec d → ℝ}
    (h : ∀ x ∈ openCubeSet R, f x = g x) :
    volumeAverage (cubeSet R) f = volumeAverage (cubeSet R) g := by
  unfold volumeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet (f := f),
    setIntegral_cubeSet_eq_setIntegral_openCubeSet (f := g),
    setIntegral_congr_fun (measurableSet_openCubeSet R) h]

/-- The block quadratic form `X · bfA X` at `x`. -/
noncomputable def blockQuad (a : CoeffField d) (X : BlockState d) (x : Vec d) : ℝ :=
  blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))

theorem blockEnergyDensity_eq_half_blockQuad (a : CoeffField d) (X : BlockState d) :
    blockEnergyDensity a X = fun x => (1 / 2 : ℝ) * blockQuad a X x := rfl

theorem volumeAverage_blockQuad_eq_two_mul {U : Set (Vec d)} (a : CoeffField d) (X : BlockState d) :
    volumeAverage U (blockQuad a X) = 2 * volumeAverage U (blockEnergyDensity a X) := by
  rw [blockEnergyDensity_eq_half_blockQuad]
  unfold volumeAverage
  rw [integral_const_mul]
  ring

/-- The coarse block quadratic form on the cube `cu_K` is below the energy of any competitor. -/
theorem coarse_quad_le_volumeAverage_blockQuad [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    {Kc : ℕ} (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (Kc : ℤ))) a)
    {P : BlockVec d} {Y : BlockState d}
    (hY : IsBlockMuAdmissible (cubeSet (originCube d (Kc : ℤ))) P Y) :
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ))) a) P) ≤
      volumeAverage (cubeSet (originCube d (Kc : ℤ))) (blockQuad a Y) := by
  have hq := hasQuadraticMu_cubeSet_of_isEllipticFieldOn (originCube d (Kc : ℤ)) hEll
  have hbdd : BddBelow (muValueSet (cubeSet (originCube d (Kc : ℤ))) P a) := by
    refine ⟨vecDot P.1 P.2, ?_⟩
    rintro _ ⟨Z, hZ, rfl⟩
    exact hZ.blockEnergyAverage_ge_vecDot_cubeSet_originCube_of_isEllipticFieldOn
      (hZ.toBlockMuIntegrabilityDataOfIsEllipticFieldOn hEll) hEll
  have h1 := csInf_le hbdd (muValueSet_mem (a := a) hY)
  rw [← Mu] at h1
  rw [Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu hq] at h1
  rw [volumeAverage_blockQuad_eq_two_mul]
  linarith only [h1]

/-- **The gluing competitor** (first line of `e.setup.basic-split`): the cell fields `X Q`, each
admissible on `Q` relative to the common offset `G`, glue to an admissible competitor on `cu_K`,
so `P · bfA(cu_K) P` is at most the mean of the cell energies. -/
theorem coarse_quad_le_subcubeMean [NeZero d] {lam Lam : ℝ} {a : CoeffField d} {Kc n : ℕ}
    (hn : n ≤ Kc) (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (Kc : ℤ))) a)
    {P : BlockVec d} {G : BlockState d}
    (hG : IsBlockMuAdmissible (cubeSet (originCube d (Kc : ℤ))) P G)
    {X : TriadicCube d → BlockState d}
    (hX : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetAdmissible (cubeSet Q) G (X Q)) :
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ))) a) P) ≤
      subcubeMean (originCube d (Kc : ℤ)) (n : ℤ)
        (fun Q => volumeAverage (cubeSet Q) (blockQuad a (X Q))) := by
  have hn' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hGo : IsBlockMuAdmissible (openCubeSet (originCube d (Kc : ℤ))) P G :=
    (isBlockOffsetAdmissible_cubeSet_iff_openCubeSet _ (constBlockState P) G).1 hG
  have hXo : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetAdmissible (openCubeSet Q) G (X Q) := fun Q hQ =>
    (isBlockOffsetAdmissible_cubeSet_iff_openCubeSet Q G (X Q)).1 (hX Q hQ)
  have hglue := isBlockMuAdmissible_gluedState hn' hGo hXo
  have hglue' : IsBlockMuAdmissible (cubeSet (originCube d (Kc : ℤ))) P
      (gluedState G (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) X) :=
    (isBlockOffsetAdmissible_cubeSet_iff_openCubeSet _ (constBlockState P) _).2 hglue
  refine (coarse_quad_le_volumeAverage_blockQuad hEll hglue').trans ?_
  have hint : IntegrableOn (blockQuad a
      (gluedState G (descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)) X))
      (cubeSet (originCube d (Kc : ℤ))) volume := by
    have h := (hglue'.toBlockMuIntegrabilityDataOfIsEllipticFieldOn hEll).energyIntegrable
    rw [blockEnergyDensity_eq_half_blockQuad] at h
    exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun x => by
      show 2 * (1 / 2 * _) = _
      ring)
  rw [volumeAverage_cubeSet_eq_subcubeMean hn' hint]
  refine le_of_eq (subcubeMean_congr fun R hR => volumeAverage_cubeSet_congr fun x hx => ?_)
  unfold blockQuad
  rw [gluedState_eval_of_mem hR hx]

/-- The block cross term `Y · bfA X` at `x`. -/
noncomputable def blockCross (a : CoeffField d) (Y X : BlockState d) (x : Vec d) : ℝ :=
  blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))

theorem blockQuad_add_smul (a : CoeffField d) (X Y : BlockState d) (t : ℝ) (x : Vec d) :
    blockQuad a (X + t • Y) x =
      blockQuad a X x + 2 * t * blockCross a Y X x + t ^ 2 * blockQuad a Y x := by
  have hsymm := blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
    (isSymmetricBlockMat_blockMatrixOfCoeff (a x)) (X.eval x) (Y.eval x)
  unfold blockQuad blockCross
  simp only [BlockState.eval_add, BlockState.eval_smul, blockMatVecMul_add, blockMatVecMul_smul,
    blockVecDot_add_left, blockVecDot_add_right, blockVecDot_smul_left, blockVecDot_smul_right,
    blockCoeffField]
  rw [hsymm]
  ring

end SuperdiffusionCLT.Section5
