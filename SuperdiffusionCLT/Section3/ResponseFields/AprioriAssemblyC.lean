/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.HarmonicInterpolationB
public import SuperdiffusionCLT.Section2.Norms.NegativeHatOrderOne

/-!
# Step 4 of `l.abstract.response.fields` in the order-one hatted negative norm

`AprioriAssemblyB` performs Step 4 of the proof in the order-zero carrier
`vecHatNegENorm` -- the literal reading of the definition of the hatted negative norm,
with test class `‖∇g‖_{L̲²(Q)} ≤ 1` -- and delivers `exists_responseDifferenceL2Clause`,
the fourth conjunct of the statement `responseFields_apriori_orderZero`.

The hatted negative norm of a vector field is read at order one: the test *gradient
field* is constrained in `H̲¹(U)`, in the scaled normalization.  That carrier is
`SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne`.  This file redoes Step 4
in it and delivers `exists_responseDifferenceL2Clause_orderOne`, the fourth conjunct of
the order-one version `responseFields_apriori_orderOne` of that statement.

## Why this is not a corollary of the order-zero clause

`vecHatNegENormOrderOne_le_vecHatNegENorm` says the order-one norm is the **smaller**
of the two, so the order-one clause is strictly stronger than the order-zero
clause and cannot be deduced from it.  Every step of Step 4 transfers verbatim
except the first of the two "standard estimates",

`3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)} ≤ C‖F₀‖_{Ĥ̲^{-1}(cu_M)}`,

whose order-zero proof is exactly the identity
`‖F₀‖_{Ĥ̲^{-1}(cu_M)} = ‖∇w_N‖_{L̲²(cu_M)}` of
`Section3/ResponseFields/HminusOneDuality.lean` followed by the energy gap and
Poincaré-Wirtinger.  That identity is a statement about the order-zero carrier
and is false at order one, where the norm of a flux oscillating at scale `3^k`
inside `cu_M` is smaller by `3^{k−M}`.

## The order-one derivation

At order one the display is a duality against the Poisson problems of the cube.
Write `u = v − (v)_{cu_M}`; testing the `L̲²` norm of `u` against a mean-zero
`h` and solving `Δψ_D = h` with `ψ_D ∈ H¹₀(cu_M)` for the Dirichlet half of `v`
and `Δψ_N = h` with vanishing normal derivative for the Neumann half turns
`⨍_{cu_M} u h` into `⨍_{cu_M} F₀·∇ψ_D − ⨍_{cu_M} F₀·∇ψ_N` through the two
response equations; each pairing is then bounded by
`ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul` at the level
`c = ‖∇ψ‖_{L̲²(cu_M)} + 3^M‖∇²ψ‖_{L̲²(cu_M)}`, and the cube `H²` estimate
`‖∇²ψ‖_{L̲²(cu_M)} ≲ ‖h‖_{L̲²(cu_M)}` together with Poincaré
`‖∇ψ‖_{L̲²(cu_M)} ≲ 3^M‖h‖_{L̲²(cu_M)}` gives `c ≲ 3^M‖h‖_{L̲²(cu_M)}`.

That derivation is carried out in `HminusOneOrderOneB`
(`hminusOne_response_difference_bridge`).  Here the display is taken as the single
explicit hypothesis `hHm1`, in the shape of the order-zero lemma
`cubeScaleFactor_inv_mul_cubeLpENorm_response_difference_le_vecHatNegENorm` with
`vecHatNegENorm` replaced by `vecHatNegENormOrderOne` and a general constant.  It is
not a proof step of the clause: the clause's own content is the centring, the
harmonicity of the difference, the interpolation of Step 3, the `L̲⁴` endpoint
and the algebra `∇w_N − ∇w_D = ∇v − (F)_{cu_M}`.

## Main results

* `responseDifference_step4_orderOne`: Step 4 at one origin cube, in the order-one
  carrier.
* `exists_responseDifferenceL2Clause_orderOne`: the fourth conjunct of the order-one
  a priori statement.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Bookkeeping -/

private theorem add_one_ne_zero'' (C : ℝ≥0∞) : C + 1 ≠ 0 := by
  intro h
  rw [add_eq_zero] at h
  exact one_ne_zero h.2

private theorem one_le_add_one' (C : ℝ≥0∞) : (1 : ℝ≥0∞) ≤ C + 1 := le_add_self

private theorem memLp_two_hilbertify' {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure ENNReal.ofReal_ne_top

/-! ## Step 4 of the proof, at one cube, in the order-one carrier -/

/-- **Step 4 of the proof of `l.abstract.response.fields`** at
one triadic cube, in the order-one hatted negative norm.

`hharm` is Step 3, `e.abstract.harmonic.interpolation`; `hC4` is the `L̲⁴`
endpoint; `hHm1` is the `Ĥ̲^{-1}` estimate in the order-one carrier, taken as
a hypothesis (see the module docstring). -/
private theorem responseDifference_step4_orderOne {Q : TriadicCube d}
    {Cint CHm C4 : ℝ≥0∞} {F : Vec d → Vec d} {wD : H10Function (openCubeSet Q)}
    {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hD : IsCubeDirichletResponse Q F wD) (hN : IsCubeNeumannResponse Q F wN)
    (hmem : MemLp
      (hilbertifyVecField (fun x => F x - volumeAverageVec (cubeSet Q) F)) 4
      (normalizedCubeMeasure Q))
    (hharm : ∀ v : H1Function (openCubeSet Q),
      (∀ φ : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q, vecDot (v.grad x) (φ.toH1Function.grad x) = 0) →
      vecCubeLpENorm Q 2 v.grad ≤
        Cint * (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
            Section2.Norms.cubeLpENorm Q 2 v.subAverage.toFun) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm Q 4 v.grad) ^ ((4 : ℝ) / 5))
    (hHm1 : ∀ (G : Vec d → Vec d) (u : H1MeanZeroFunction (openCubeSet Q))
        (w : H10Function (openCubeSet Q)),
      IsCubeNeumannResponse Q G u → IsCubeDirichletResponse Q G w →
      ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
          Section2.Norms.cubeLpENorm Q 2
            (u.toH1Function - w.toH1Function).subAverage.toFun ≤
        CHm * Section2.Norms.vecHatNegENormOrderOne Q G)
    (hC4 : ∀ G : Vec d → Vec d,
      MemLp (hilbertifyVecField G) 4 (normalizedCubeMeasure Q) →
      ∀ (u : H10Function (openCubeSet Q)) (w : H1MeanZeroFunction (openCubeSet Q)),
        IsCubeDirichletResponse Q G u → IsCubeNeumannResponse Q G w →
        vecCubeLpENorm Q 4
            (fun x => w.toH1Function.grad x - u.toH1Function.grad x) ≤
          C4 * vecCubeLpENorm Q 4 G) :
    vecCubeLpENorm Q 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      Cint * CHm ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) *
          (Section2.Norms.vecHatNegENormOrderOne Q
            (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm Q 4 (fun x => F x - volumeAverageVec (cubeSet Q) F)) ^
            ((4 : ℝ) / 5) +
        ‖HilbertVec.ofVec (volumeAverageVec (cubeSet Q) F)‖ₑ := by
  set c : Vec d := volumeAverageVec (cubeSet Q) F with hc
  set F0 : Vec d → Vec d := fun x => F x - c with hF0
  -- the centred flux and its two responses
  have hF04 : MemLp F0 4 (normalizedCubeMeasure Q) := memLp_hilbertifyVecField_iff.1 hmem
  have hF02 : MemLp F0 2 (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_mono (by norm_num) hF04
  have hF0L2 : MemVectorL2 (openCubeSet Q) F0 :=
    memVectorL2_of_memLp_two_normalizedCubeMeasure hF02
  have hFL2 : MemVectorL2 (openCubeSet Q) F := by
    have hsum := hF0L2.add (memVectorL2_const (U := openCubeSet Q) c)
    have hfun : (F0 + fun _ : Vec d => c) = F := by
      funext x
      simp [hF0]
    rwa [hfun] at hsum
  have hD0 : IsCubeDirichletResponse Q F0 wD :=
    isCubeDirichletResponse_sub_const hFL2 hD c
  have hN0 : IsCubeNeumannResponse Q F0 (wN + linearH1MeanZeroFunction Q c) :=
    isCubeNeumannResponse_sub_const hFL2 hN c
  have hvgrad : (((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function).grad) =
      fun x => (wN + linearH1MeanZeroFunction Q c).toH1Function.grad x -
        wD.toH1Function.grad x := H1Function.sub_grad _ _
  -- Step 3 at the harmonic difference
  have hstep3 := hharm ((wN + linearH1MeanZeroFunction Q c).toH1Function - wD.toH1Function)
    (fun φ => setIntegral_vecDot_grad_responseDifference_eq_zero hD0 hN0 φ)
  -- the `Ĥ̲^{-1}` half of the standard estimates, at order one
  have hHm := hHm1 F0 (wN + linearH1MeanZeroFunction Q c) wD hN0 hD0
  -- the `L̲⁴` half of the standard estimates
  have hL4 := hC4 F0 hmem wD (wN + linearH1MeanZeroFunction Q c) hD0 hN0
  rw [← hvgrad] at hL4
  have h1 : (ENNReal.ofReal ((cubeScaleFactor Q)⁻¹) *
        Section2.Norms.cubeLpENorm Q 2
          (((wN + linearH1MeanZeroFunction Q c).toH1Function -
            wD.toH1Function)).subAverage.toFun) ^ ((1 : ℝ) / 5) ≤
      (CHm * Section2.Norms.vecHatNegENormOrderOne Q F0) ^ ((1 : ℝ) / 5) :=
    ENNReal.rpow_le_rpow hHm (by norm_num)
  have h2 : (vecCubeLpENorm Q 4
        (((wN + linearH1MeanZeroFunction Q c).toH1Function -
          wD.toH1Function)).grad) ^ ((4 : ℝ) / 5) ≤
      (C4 * vecCubeLpENorm Q 4 F0) ^ ((4 : ℝ) / 5) :=
    ENNReal.rpow_le_rpow hL4 (by norm_num)
  have hmain : vecCubeLpENorm Q 2
        (((wN + linearH1MeanZeroFunction Q c).toH1Function - wD.toH1Function)).grad ≤
      Cint * CHm ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) *
        (Section2.Norms.vecHatNegENormOrderOne Q F0) ^ ((1 : ℝ) / 5) *
        (vecCubeLpENorm Q 4 F0) ^ ((4 : ℝ) / 5) := by
    refine le_trans hstep3 (le_trans (mul_le_mul' (mul_le_mul' (le_refl Cint) h1) h2)
      (le_of_eq ?_))
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (4 : ℝ) / 5)]
    ring
  -- the last display of Step 4, `∇w_N − ∇w_D = ∇v − (F)_Q`
  have hdiff : (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) =
      fun x => ((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function).grad x + (-c) := by
    funext x
    rw [hvgrad]
    simp only [add_linearH1MeanZeroFunction_grad]
    abel
  have hmeasv : AEStronglyMeasurable
      (hilbertifyVecField (((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function)).grad) (normalizedCubeMeasure Q) :=
    (memLp_two_hilbertify' (((wN + linearH1MeanZeroFunction Q c).toH1Function -
      wD.toH1Function)).grad_memVectorL2).aestronglyMeasurable
  have hmeasc : AEStronglyMeasurable (hilbertifyVecField (fun _ : Vec d => -c))
      (normalizedCubeMeasure Q) :=
    (memLp_two_hilbertify'
      (memVectorL2_const (U := openCubeSet Q) (-c))).aestronglyMeasurable
  have htri : vecCubeLpENorm Q 2
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
      vecCubeLpENorm Q 2 (((wN + linearH1MeanZeroFunction Q c).toH1Function -
        wD.toH1Function)).grad + ‖HilbertVec.ofVec c‖ₑ := by
    rw [hdiff]
    refine le_trans (vecCubeLpENorm_add_le (by norm_num) hmeasv hmeasc) ?_
    rw [vecCubeLpENorm_const Q (by norm_num) (-c)]
    simp
  exact le_trans htri (add_le_add hmain le_rfl)

/-! ## `e.abstract.response.ND.weak` at order one -/

/-- **The weak Neumann-Dirichlet comparison of `l.abstract.response.fields`**
(`e.abstract.response.ND.weak`) in the order-one hatted negative
norm: the shape of the fourth conjunct of the order-one version
`responseFields_apriori_orderOne` of `responseFields_apriori_orderZero`.

`hharm` is Step 3 of the proof, `e.abstract.harmonic.interpolation`, exactly as in
`exists_responseDifferenceL2Clause`.

`hHm1` is the first of the two standard estimates in the order-one carrier, taken
as a hypothesis; see the module docstring for its derivation.

`hjunk` is the branch of the conjunct on which Step 4 does not run: the centred
flux is not `L̲⁴(cu_M)`-measurable while the right-hand side is not forced to be
`⊤`, that is, either its `L̲⁴(cu_M)` size is finite or its order-one
`Ĥ̲^{-1}(cu_M)` size vanishes. The complementary branch, an infinite `L̲⁴` size
against a non-zero order-one `Ĥ̲^{-1}` size, is discharged in the proof. -/
theorem exists_responseDifferenceL2Clause_orderOne (hd : 2 ≤ d)
    (Cint : ℝ≥0∞) (hCint : Cint < ⊤) (CHm : ℝ≥0∞) (hCHm : CHm < ⊤)
    (hharm : ∀ (M : ℕ) (v : H1Function (openCubeSet (originCube d (M : ℤ)))),
      (∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
        ∫ x in openCubeSet (originCube d (M : ℤ)),
          vecDot (v.grad x) (φ.toH1Function.grad x) = 0) →
      vecCubeLpENorm (originCube d (M : ℤ)) 2 v.grad ≤
        Cint *
            (ENNReal.ofReal ((cubeScaleFactor (originCube d (M : ℤ)))⁻¹) *
              Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
                v.subAverage.toFun) ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4 v.grad) ^ ((4 : ℝ) / 5))
    (hHm1 : ∀ (M : ℕ) (G : Vec d → Vec d)
      (u : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
      (w : H10Function (openCubeSet (originCube d (M : ℤ)))),
      IsCubeNeumannResponse (originCube d (M : ℤ)) G u →
      IsCubeDirichletResponse (originCube d (M : ℤ)) G w →
      ENNReal.ofReal ((cubeScaleFactor (originCube d (M : ℤ)))⁻¹) *
          Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
            (u.toH1Function - w.toH1Function).subAverage.toFun ≤
        CHm * Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ)) G)
    (hjunk : ∀ (M : ℕ) (F : Vec d → Vec d)
      (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
      (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
      IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
      ¬ MemLp (hilbertifyVecField (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) 4
          (normalizedCubeMeasure (originCube d (M : ℤ))) →
      (vecCubeLpENorm (originCube d (M : ℤ)) 4
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) < ⊤ ∨
          Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = 0) →
      vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
        (Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
              (fun x => F x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4
              (fun x => F x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
          ‖HilbertVec.ofVec (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
        vecCubeLpENorm (originCube d (M : ℤ)) 2
            (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
          C * (Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
                (fun x => F x -
                  volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
              (vecCubeLpENorm (originCube d (M : ℤ)) 4
                (fun x => F x -
                  volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
            C * ‖HilbertVec.ofVec
              (volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)‖ₑ := by
  obtain ⟨C4, hC4top, hC4⟩ := exists_cubeResponseDifferenceL4Estimate hd
  refine ⟨Cint * CHm ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) + 1, ?_, ?_⟩
  · refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hCint ?_) ?_,
      ENNReal.one_lt_top⟩
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCHm.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC4top.ne
  intro M F wD wN hD hN
  by_cases hmem : MemLp (hilbertifyVecField (fun x =>
      F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) 4
      (normalizedCubeMeasure (originCube d (M : ℤ)))
  · refine le_trans (responseDifference_step4_orderOne (Cint := Cint) (CHm := CHm) (C4 := C4)
      hD hN hmem (hharm M) (hHm1 M)
      (fun G hG u w hu hw => hC4 (originCube d (M : ℤ)) G hG u w hu hw)) ?_
    refine add_le_add ?_ (le_mul_of_one_le_left (zero_le) (one_le_add_one' _))
    gcongr
    exact le_self_add
  · by_cases hguard : vecCubeLpENorm (originCube d (M : ℤ)) 4
        (fun x => F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) < ⊤ ∨
      Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
        (fun x => F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = 0
    · refine le_trans (hjunk M F wD wN hD hN hmem hguard) ?_
      refine add_le_add ?_ (le_mul_of_one_le_left (zero_le) (one_le_add_one' _))
      exact mul_le_mul' (le_mul_of_one_le_left (zero_le) (one_le_add_one' _)) le_rfl
    · push Not at hguard
      obtain ⟨hL4top, hhat⟩ := hguard
      have hL4eq : vecCubeLpENorm (originCube d (M : ℤ)) 4
          (fun x => F x - volumeAverageVec (cubeSet (originCube d (M : ℤ))) F) = ⊤ :=
        top_le_iff.1 hL4top
      have hrpow : (Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
          (fun x => F x -
            volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) ≠ 0 := by
        rw [Ne, ENNReal.rpow_eq_zero_iff]
        push Not
        exact ⟨fun h => absurd h hhat, fun _ => by norm_num⟩
      have htop : (Cint * CHm ^ ((1 : ℝ) / 5) * C4 ^ ((4 : ℝ) / 5) + 1) *
          (Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ))
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
          (vecCubeLpENorm (originCube d (M : ℤ)) 4
            (fun x => F x -
              volumeAverageVec (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) = ⊤ := by
        rw [hL4eq, ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top]
        exact mul_ne_zero (add_one_ne_zero'' _) hrpow
      rw [htop]
      simp

/-! ## The version-3 a priori statement from its bridges -/

end

end ResponseFields
end Section3
end SuperdiffusionCLT
