/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.BasicSplit

/-!
# Euler orthogonality of the offset minimizers

For a bounded elliptic coefficient on a domain `U` of positive finite volume and an offset `F` with
`L²` components, the minimizer `X` of the block energy over `IsBlockOffsetAdmissible U F` is
orthogonal, for the form `∫ Y · bfA X`, to the zero-trace class
(`integral_blockCross_eq_zero_of_isBlockOffsetMinimizer`). This is the orthogonality of the
local minimizers used in the equality of `e.setup.basic-split`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

theorem IsBlockOffsetAdmissible.add {F F' X Y : BlockState d}
    (hX : IsBlockOffsetAdmissible U F X) (hY : IsBlockOffsetAdmissible U F' Y) :
    IsBlockOffsetAdmissible U (F + F') (X + Y) := by
  have hp : (fun x => (X + Y).potential x - (F + F').potential x) =
      (fun x => X.potential x - F.potential x) + (fun x => Y.potential x - F'.potential x) := by
    funext x
    simp only [Pi.add_apply]
    show X.potential x + Y.potential x - (F.potential x + F'.potential x) = _
    abel
  have hf : (fun x => (X + Y).flux x - (F + F').flux x) =
      (fun x => X.flux x - F.flux x) + (fun x => Y.flux x - F'.flux x) := by
    funext x
    simp only [Pi.add_apply]
    show X.flux x + Y.flux x - (F.flux x + F'.flux x) = _
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; exact hX.1.add hY.1
  · rw [hp]; exact isPotentialZeroTraceOn_add hX.2.1 hY.2.1
  · rw [hf]; exact hX.2.2.1.add hY.2.2.1
  · rw [hf]
    exact isSolenoidalZeroNormalTraceOn_add hX.2.2.2 hY.2.2.2
      (fun φ => integrableOn_vecDot_of_memVectorL2 hX.2.2.1 φ.grad_memVectorL2)
      (fun φ => integrableOn_vecDot_of_memVectorL2 hY.2.2.1 φ.grad_memVectorL2)

theorem IsBlockOffsetAdmissible.smul {F X : BlockState d} (c : ℝ)
    (hX : IsBlockOffsetAdmissible U F X) : IsBlockOffsetAdmissible U (c • F) (c • X) := by
  have hp : (fun x => (c • X).potential x - (c • F).potential x) =
      c • (fun x => X.potential x - F.potential x) := by
    funext x
    show c • X.potential x - c • F.potential x = c • (X.potential x - F.potential x)
    rw [smul_sub]
  have hf : (fun x => (c • X).flux x - (c • F).flux x) =
      c • (fun x => X.flux x - F.flux x) := by
    funext x
    show c • X.flux x - c • F.flux x = c • (X.flux x - F.flux x)
    rw [smul_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; exact hX.1.const_smul c
  · rw [hp]; exact isPotentialZeroTraceOn_smul hX.2.1 c
  · rw [hf]; exact hX.2.2.1.const_smul c
  · rw [hf]; exact isSolenoidalZeroNormalTraceOn_smul hX.2.2.2 c

theorem IsBlockOffsetAdmissible.add_smul {F X Z : BlockState d}
    (hX : IsBlockOffsetAdmissible U F X)
    (hZ : IsBlockOffsetAdmissible U (constBlockState 0) Z) (t : ℝ) :
    IsBlockOffsetAdmissible U F (X + t • Z) := by
  have h := hX.add (hZ.smul t)
  have hF : F + t • constBlockState (0 : BlockVec d) = F := by
    refine BlockState.ext (funext fun x => ?_) (funext fun x => ?_)
    · show F.potential x + t • (0 : Vec d) = F.potential x
      simp
    · show F.flux x + t • (0 : Vec d) = F.flux x
      simp
  rwa [hF] at h

theorem integrableOn_blockQuad [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) {X : BlockState d}
    (hp : MemVectorL2 U X.potential) (hf : MemVectorL2 U X.flux) :
    IntegrableOn (blockQuad a X) U volume := by
  have h := blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    (memBlockL2_eval_of_components hp hf) hEll
  rw [blockEnergyDensity_eq_half_blockQuad] at h
  exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun x => by
    show 2 * (1 / 2 * _) = _
    ring)

theorem integrableOn_blockCross [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) {X Y : BlockState d}
    (hXp : MemVectorL2 U X.potential) (hXf : MemVectorL2 U X.flux)
    (hYp : MemVectorL2 U Y.potential) (hYf : MemVectorL2 U Y.flux) :
    IntegrableOn (blockCross a Y X) U volume := by
  have h1 := integrableOn_blockQuad (a := a) hEll
    (X := X + (1 : ℝ) • Y) (hXp.add (hYp.const_smul 1)) (hXf.add (hYf.const_smul 1))
  have h2 := integrableOn_blockQuad (a := a) hEll hXp hXf
  have h3 := integrableOn_blockQuad (a := a) hEll hYp hYf
  refine ((h1.sub h2).sub h3).div_const 2 |>.congr (Filter.Eventually.of_forall fun x => ?_)
  have := blockQuad_add_smul a X Y 1 x
  simp only [Pi.sub_apply]
  linarith only [this]

/-- **Euler orthogonality.** The minimizer of the block energy over `F + (zero-trace class)` is
orthogonal to the zero-trace class for the form `∫ Y · bfA X`. -/
theorem integral_blockCross_eq_zero_of_isBlockOffsetMinimizer
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (hvol : 0 < (volume U).toReal)
    {F X Z : BlockState d} (hFp : MemVectorL2 U F.potential) (hFf : MemVectorL2 U F.flux)
    (hmin : IsBlockOffsetMinimizer a U F X)
    (hZ : IsBlockOffsetAdmissible U (constBlockState 0) Z) :
    ∫ x in U, blockCross a Z X x = 0 := by
  have hXp := hmin.1.memVectorL2_potential hFp
  have hXf := hmin.1.memVectorL2_flux hFf
  have hZp := hZ.memVectorL2_potential (memVectorL2_const (U := U) (0 : Vec d))
  have hZf := hZ.memVectorL2_flux (memVectorL2_const (U := U) (0 : Vec d))
  have hqX := integrableOn_blockQuad (a := a) hEll hXp hXf
  have hqZ := integrableOn_blockQuad (a := a) hEll hZp hZf
  have hcr := integrableOn_blockCross (a := a) hEll hXp hXf hZp hZf
  set b := ∫ x in U, blockCross a Z X x with hb
  set c := ∫ x in U, blockQuad a Z x with hc
  have key : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * c := by
    intro t
    have hle := hmin.2 (X + t • Z) (hmin.1.add_smul hZ t)
    have hq : volumeAverage U (blockQuad a X) ≤ volumeAverage U (blockQuad a (X + t • Z)) := by
      rw [volumeAverage_blockQuad_eq_two_mul, volumeAverage_blockQuad_eq_two_mul]
      linarith only [hle]
    unfold volumeAverage at hq
    have hq' := le_of_mul_le_mul_left hq (inv_pos.2 hvol)
    have hexp : ∫ x in U, blockQuad a (X + t • Z) x =
        (∫ x in U, blockQuad a X x) + 2 * t * b + t ^ 2 * c := by
      simp only [blockQuad_add_smul]
      have h1 : IntegrableOn (fun x => blockQuad a X x + 2 * t * blockCross a Z X x) U volume :=
        hqX.add (hcr.const_mul (2 * t))
      have h2 : IntegrableOn (fun x => t ^ 2 * blockQuad a Z x) U volume :=
        hqZ.const_mul (t ^ 2)
      have h3 : IntegrableOn (fun x => 2 * t * blockCross a Z X x) U volume :=
        hcr.const_mul (2 * t)
      rw [integral_add h1 h2, integral_add hqX h3, integral_const_mul, integral_const_mul]
    rw [hexp] at hq'
    linarith only [hq']
  by_contra hne
  have hb2 : 0 < b ^ 2 := by positivity
  set ε : ℝ := 1 / (2 * (|c| + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hεc : ε * c ≤ 1 / 2 := by
    have h1 : ε * (|c| + 1) = 1 / 2 := by rw [hε]; field_simp
    nlinarith only [h1, hεpos, le_abs_self c, abs_nonneg c]
  have := key (-(ε * b))
  have hpos := mul_pos hεpos hb2
  nlinarith only [this, hpos, mul_le_mul_of_nonneg_left hεc hpos.le]

/-! ## The cell identity -/

theorem blockQuad_add (a : CoeffField d) (S T : BlockState d) (x : Vec d) :
    blockQuad a (S + T) x =
      blockQuad a T x + 2 * blockCross a S T x + blockQuad a S x := by
  have h := blockQuad_add_smul a T S 1 x
  have e : T + (1 : ℝ) • S = S + T := by
    refine BlockState.ext (funext fun y => ?_) (funext fun y => ?_)
    · show T.potential y + (1 : ℝ) • S.potential y = S.potential y + T.potential y
      rw [one_smul, add_comm]
    · show T.flux y + (1 : ℝ) • S.flux y = S.flux y + T.flux y
      rw [one_smul, add_comm]
  rw [e] at h
  simpa using h

theorem blockVecDot_two_smul_add_eq (a : CoeffField d) (Pz : BlockVec d) (T : BlockState d)
    (x : Vec d) :
    blockVecDot ((2 : ℝ) • Pz + T.eval x) (blockMatVecMul (blockCoeffField a x) (T.eval x)) =
      2 * blockCross a (constBlockState Pz) T x + blockQuad a T x := by
  unfold blockCross blockQuad
  rw [blockVecDot_add_left, blockVecDot_smul_left]
  rfl

/-- **The cell identity of `e.setup.basic-split`.** For the minimizers `S` (offset `Pz`) and `St`
(offset `Fz`) on a cell, the energy of `S + St` is `Pz · bfA(Q) Pz` plus the localization terms
`⨍ (2 Pz + St) · bfA St`; the cross term `⨍ S · bfA St` is replaced by `⨍ Pz · bfA St` by the Euler
orthogonality of `St`. -/
theorem volumeAverage_blockQuad_add_eq [NeZero d] {lam Lam : ℝ} {a : CoeffField d}
    (Q : TriadicCube d) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    {Pz : BlockVec d} {Fz S St : BlockState d}
    (hFp : MemVectorL2 (cubeSet Q) Fz.potential) (hFf : MemVectorL2 (cubeSet Q) Fz.flux)
    (hS : IsBlockOffsetMinimizer a (cubeSet Q) (constBlockState Pz) S)
    (hSt : IsBlockOffsetMinimizer a (cubeSet Q) Fz St) :
    volumeAverage (cubeSet Q) (blockQuad a (S + St)) =
      blockVecDot Pz (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) Pz) +
        volumeAverage (cubeSet Q) (fun x =>
          blockVecDot ((2 : ℝ) • Pz + St.eval x)
            (blockMatVecMul (blockCoeffField a x) (St.eval x))) := by
  have hvol : 0 < (volume (cubeSet Q)).toReal := by
    rw [volume_cubeSet_toReal]; exact cubeVolume_pos Q
  have hconstp : MemVectorL2 (cubeSet Q) (constBlockState Pz).potential := memVectorL2_const _
  have hconstf : MemVectorL2 (cubeSet Q) (constBlockState Pz).flux := memVectorL2_const _
  have hSp := hS.1.memVectorL2_potential hconstp
  have hSf := hS.1.memVectorL2_flux hconstf
  have hStp := hSt.1.memVectorL2_potential hFp
  have hStf := hSt.1.memVectorL2_flux hFf
  -- the correction `Z = S - Pz` is in the zero-trace class
  let Z : BlockState d := { potential := fun x => S.potential x - Pz.1
                            flux := fun x => S.flux x - Pz.2 }
  have hZ : IsBlockOffsetAdmissible (cubeSet Q) (constBlockState 0) Z := by
    have e1 : (fun x => Z.potential x - (constBlockState (0 : BlockVec d)).potential x) =
        fun x => S.potential x - (constBlockState Pz).potential x := by
      funext x; simp [Z, constBlockState]
    have e2 : (fun x => Z.flux x - (constBlockState (0 : BlockVec d)).flux x) =
        fun x => S.flux x - (constBlockState Pz).flux x := by
      funext x; simp [Z, constBlockState]
    unfold IsBlockOffsetAdmissible
    rw [e1, e2]
    exact hS.1
  have hEL := integral_blockCross_eq_zero_of_isBlockOffsetMinimizer hEll hvol hFp hFf hSt hZ
  have hqS := integrableOn_blockQuad (a := a) hEll hSp hSf
  have hqSt := integrableOn_blockQuad (a := a) hEll hStp hStf
  have hcrS := integrableOn_blockCross (a := a) hEll hStp hStf hSp hSf
  have hcrP := integrableOn_blockCross (a := a) hEll hStp hStf hconstp hconstf
  have hZe : ∀ x, blockCross a Z St x = blockCross a S St x - blockCross a (constBlockState Pz) St x := by
    intro x
    unfold blockCross
    have e : Z.eval x = S.eval x - (constBlockState Pz).eval x := rfl
    rw [e, blockVecDot_comm (S.eval x - _), blockVecDot_comm (S.eval x),
      blockVecDot_comm ((constBlockState Pz).eval x), blockVecDot_sub_right]
  have hcross : ∫ x in cubeSet Q, blockCross a S St x =
      ∫ x in cubeSet Q, blockCross a (constBlockState Pz) St x := by
    simp only [hZe] at hEL
    rw [integral_sub hcrS hcrP] at hEL
    linarith only [hEL]
  -- the minimal energy of `S`
  have hSenergy := volumeAverage_blockEnergyDensity_eq_half_coarseBlockMatrix Q hEll Pz hS
  have hSq : volumeAverage (cubeSet Q) (blockQuad a S) =
      blockVecDot Pz (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) Pz) := by
    rw [volumeAverage_blockQuad_eq_two_mul, hSenergy]; ring
  -- expand both sides
  have hL : volumeAverage (cubeSet Q) (blockQuad a (S + St)) =
      volumeAverage (cubeSet Q) (blockQuad a St) +
        2 * volumeAverage (cubeSet Q) (blockCross a (constBlockState Pz) St) +
        volumeAverage (cubeSet Q) (blockQuad a S) := by
    unfold volumeAverage
    simp only [blockQuad_add]
    have h1 : IntegrableOn (fun x => blockQuad a St x + 2 * blockCross a S St x) (cubeSet Q)
        volume := hqSt.add (hcrS.const_mul 2)
    rw [integral_add h1 hqS, integral_add hqSt (hcrS.const_mul 2), integral_const_mul, hcross]
    ring
  have hR : volumeAverage (cubeSet Q) (fun x =>
        blockVecDot ((2 : ℝ) • Pz + St.eval x)
          (blockMatVecMul (blockCoeffField a x) (St.eval x))) =
      2 * volumeAverage (cubeSet Q) (blockCross a (constBlockState Pz) St) +
        volumeAverage (cubeSet Q) (blockQuad a St) := by
    unfold volumeAverage
    simp only [blockVecDot_two_smul_add_eq]
    rw [integral_add (hcrP.const_mul 2) hqSt, integral_const_mul]
    ring
  rw [hL, hR, hSq]
  ring

/-! ## The basic split -/

/-- The class `F + (zero-trace class)` on `U` only depends on `F` on `U`. -/
theorem IsBlockOffsetAdmissible.congr_offset (hU : MeasurableSet U) {F F' X : BlockState d}
    (hF : ∀ x ∈ U, F.potential x = F'.potential x ∧ F.flux x = F'.flux x)
    (hX : IsBlockOffsetAdmissible U F X) : IsBlockOffsetAdmissible U F' X := by
  have hp : (fun x => X.potential x - F.potential x) =ᵐ[volume.restrict U]
      fun x => X.potential x - F'.potential x :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx => by
      beta_reduce; rw [(hF x hx).1])
  have hf : (fun x => X.flux x - F.flux x) =ᵐ[volume.restrict U]
      fun x => X.flux x - F'.flux x :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall fun x hx => by
      beta_reduce; rw [(hF x hx).2])
  refine ⟨hX.1.ae_eq hp, hX.2.1.congr_ae hp, hX.2.2.1.ae_eq hf, fun φ => ?_⟩
  have h := hX.2.2.2 φ
  rw [← h]
  refine setIntegral_congr_fun hU fun x hx => ?_
  simp only [(hF x hx).2]

theorem memVectorL2_cubeSet_of_subset {Q R : TriadicCube d} (h : cubeSet R ⊆ cubeSet Q)
    {f : Vec d → Vec d} (hf : MemVectorL2 (cubeSet Q) f) : MemVectorL2 (cubeSet R) f :=
  hf.mono_measure (Measure.restrict_mono_set volume h)

/-- **`e.setup.basic-split`.** Let `G` be a global offset admissible for the slope `P` on `cu_K`
(`G = P + bfAhom^{-1/2}(∇w_D, ∇w_N + shom^{-1} hshell e')`), and on each subcube `Q = z + cu_n`
let `G = Pz + Fz` (the slope and fluctuation fields), with `S` and `St` the minimizers of the block
energy over `Pz + zero class` and `Fz + zero class`. Then the glued field `Σ_Q (S + St) 1_Q` is a
competitor for `bfA(cu_K)`, and the cell energies split by Euler orthogonality:
`P · bfA(cu_K) P ≤ avsum_z ⨍_{z+cu_n} (S + St) · bfA (S + St)
  = avsum_z (Pz · bfA(z+cu_n) Pz + ⨍_{z+cu_n} (2 Pz + St) · bfA St)`. -/
theorem basic_split [NeZero d] {lam Lam : ℝ} {a : CoeffField d} {Kc n : ℕ} (hn : n ≤ Kc)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (Kc : ℤ))) a)
    {P : BlockVec d} {G : BlockState d}
    (hG : IsBlockMuAdmissible (cubeSet (originCube d (Kc : ℤ))) P G)
    {Pz : TriadicCube d → BlockVec d} {Fz : TriadicCube d → BlockState d}
    (hagree : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ), ∀ x ∈ cubeSet Q,
      G.potential x = (Pz Q).1 + (Fz Q).potential x ∧ G.flux x = (Pz Q).2 + (Fz Q).flux x)
    {S St : TriadicCube d → BlockState d}
    (hS : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetMinimizer a (cubeSet Q) (constBlockState (Pz Q)) (S Q))
    (hSt : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetMinimizer a (cubeSet Q) (Fz Q) (St Q)) :
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ))) a) P) ≤
        subcubeMean (originCube d (Kc : ℤ)) (n : ℤ)
          (fun Q => volumeAverage (cubeSet Q) (blockQuad a (S Q + St Q))) ∧
      subcubeMean (originCube d (Kc : ℤ)) (n : ℤ)
          (fun Q => volumeAverage (cubeSet Q) (blockQuad a (S Q + St Q))) =
        subcubeMean (originCube d (Kc : ℤ)) (n : ℤ)
          (fun Q => blockVecDot (Pz Q) (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) (Pz Q)) +
            volumeAverage (cubeSet Q) (fun x =>
              blockVecDot ((2 : ℝ) • Pz Q + (St Q).eval x)
                (blockMatVecMul (blockCoeffField a x) ((St Q).eval x)))) := by
  have hn' : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  have hcell : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      cubeSet Q ⊆ cubeSet (originCube d (Kc : ℤ)) := fun Q hQ =>
    cubeSet_subset_of_mem_descendantsAtScale hn' hQ
  -- `G` is `L²` on the big cube
  have hGp : MemVectorL2 (cubeSet (originCube d (Kc : ℤ))) G.potential := by
    have h := hG.1.add (memVectorL2_const (U := cubeSet (originCube d (Kc : ℤ))) P.1)
    have e : ((fun x => G.potential x - P.1) + fun _ => P.1) = G.potential := by
      funext x; simp
    rwa [e] at h
  have hGf : MemVectorL2 (cubeSet (originCube d (Kc : ℤ))) G.flux := by
    have h := hG.2.2.1.add (memVectorL2_const (U := cubeSet (originCube d (Kc : ℤ))) P.2)
    have e : ((fun x => G.flux x - P.2) + fun _ => P.2) = G.flux := by
      funext x; simp
    rwa [e] at h
  have hFp : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      MemVectorL2 (cubeSet Q) (Fz Q).potential := by
    intro Q hQ
    have h := (memVectorL2_cubeSet_of_subset (hcell Q hQ) hGp).sub
      (memVectorL2_const (U := cubeSet Q) (Pz Q).1)
    refine h.ae_eq ((ae_restrict_iff' (measurableSet_cubeSet Q)).2
      (Filter.Eventually.of_forall fun x hx => ?_))
    show G.potential x - (Pz Q).1 = (Fz Q).potential x
    rw [(hagree Q hQ x hx).1]
    abel
  have hFf : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      MemVectorL2 (cubeSet Q) (Fz Q).flux := by
    intro Q hQ
    have h := (memVectorL2_cubeSet_of_subset (hcell Q hQ) hGf).sub
      (memVectorL2_const (U := cubeSet Q) (Pz Q).2)
    refine h.ae_eq ((ae_restrict_iff' (measurableSet_cubeSet Q)).2
      (Filter.Eventually.of_forall fun x hx => ?_))
    show G.flux x - (Pz Q).2 = (Fz Q).flux x
    rw [(hagree Q hQ x hx).2]
    abel
  have hX : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      IsBlockOffsetAdmissible (cubeSet Q) G (S Q + St Q) := by
    intro Q hQ
    refine IsBlockOffsetAdmissible.congr_offset (measurableSet_cubeSet Q)
      (F := constBlockState (Pz Q) + Fz Q) (fun x hx => ?_)
      ((hS Q hQ).1.add (hSt Q hQ).1)
    exact ⟨((hagree Q hQ x hx).1).symm, ((hagree Q hQ x hx).2).symm⟩
  refine ⟨coarse_quad_le_subcubeMean hn hEll hG hX, subcubeMean_congr fun Q hQ => ?_⟩
  exact volumeAverage_blockQuad_add_eq Q (hEll.mono (measurableSet_cubeSet Q) (hcell Q hQ))
    (hFp Q hQ) (hFf Q hQ) (hS Q hQ) (hSt Q hQ)

/-! ## Witness -/

/-- Satisfiability of the hypotheses of `basic_split`: identity coefficient, slope `0`, global
offset `0`, minimizers chosen by the existence theorem. -/
example [NeZero d] {Kc n : ℕ} (hn : n ≤ Kc) : True := by
  have hex : ∀ Q : TriadicCube d, ∃ X : BlockState d,
      IsBlockOffsetMinimizer (fun _ => (1 : Mat d)) (cubeSet Q) (constBlockState 0) X := fun Q =>
    (exists_isBlockOffsetMinimizer_cubeSet (a := fun _ => (1 : Mat d)) (lam := 1) (Lam := 1) Q
      (isEllipticFieldOn_one (measurableSet_cubeSet Q)) (F := constBlockState 0)
      (memVectorL2_const _) (memVectorL2_const _)).imp fun _ h => h.1
  have e1 : (fun x => (constBlockState (0 : BlockVec d)).potential x - (0 : BlockVec d).1) =
      0 := by
    funext x; simp [constBlockState]
  have e2 : (fun x => (constBlockState (0 : BlockVec d)).flux x - (0 : BlockVec d).2) = 0 := by
    funext x; simp [constBlockState]
  have hG : IsBlockMuAdmissible (cubeSet (originCube d (Kc : ℤ))) (0 : BlockVec d)
      (constBlockState 0) := by
    unfold IsBlockMuAdmissible
    rw [e1, e2]
    exact ⟨MeasureTheory.MemLp.zero, isPotentialZeroTraceOn_zero, MeasureTheory.MemLp.zero,
      isSolenoidalZeroNormalTraceOn_zero⟩
  have h := basic_split (a := fun _ => (1 : Mat d)) (Kc := Kc) (n := n) hn
    (isEllipticFieldOn_one (measurableSet_cubeSet _)) hG
    (Pz := fun _ => 0) (Fz := fun _ => constBlockState 0)
    (fun Q _ x _ => ⟨by simp [constBlockState], by simp [constBlockState]⟩)
    (S := fun Q => Classical.choose (hex Q)) (St := fun Q => Classical.choose (hex Q))
    (fun Q _ => Classical.choose_spec (hex Q)) (fun Q _ => Classical.choose_spec (hex Q))
  trivial

end SuperdiffusionCLT.Section5
