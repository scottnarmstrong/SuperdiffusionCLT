/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateB
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Section8.Prereq.BallExitTime
public import SuperdiffusionCLT.Section8.Common.Regularity.Ported.HarmonicReplacement

/-!
# The resolvent estimate on a smooth bounded domain

`l.resolvent.estimate` as a consequence
of the root theorem `t.superdiffusivity`, taken as the explicit hypothesis `hRoot` (the statement
of `SuperdiffusionCLT.Frozen.Section7.superdiffusivity`, whose proof is open).

Almost surely in the sample, for every `ε ≤ 1/2` with `Z ≤ ε⁻¹` and every shift `λ ≥ 0`:

* the general form: the weak solutions of `λ u - L^ε u = f` and `λ uhom - ½ Δ uhom = f` with the
  same datum `g` satisfy `‖u - uhom‖_∞ ≤ 4 C |log ε|^{-α} (‖∇g‖_∞ + ‖f - λ u‖_∞)`;
* the exit-time form (`f = 1`, `g = 0`, `λ > 0`): `‖v - vbar‖_∞ ≤ 4 C |log ε|^{-α}`.

Here `L^ε = opScale c⋆ ε · ∇·(a^ε ∇)`, `a^ε = epField ν ω ε`, and the equations are the weak
carriers `IsDirichletSolution` with the field `opScale c⋆ ε • a^ε` (the equation
`-∇·((½ S⁻¹ a^ε)∇u) = f - λ u`, that is `λ u - L^ε u = f`).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

/-- **Resolvent estimate** (`l.resolvent.estimate`, with the exit-time form), from the root
theorem `hRoot`. -/
theorem resEst_resolvent_estimate (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hRoot : ∀ (d : ℕ) [NeZero d], 2 ≤ d →
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
                      (∀ ξ : ℝ, 1 ≤ ξ →
                        P.toMeasure {omega | ξ ≤ Z omega} ≤
                          ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                          ∀ (f : Homogenization.Vec d → ℝ) (g u uhom : Homogenization.H1Function U),
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun x => ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ •
                                  SuperdiffusionCLT.Section7.epField nu omega ε x)
                                U f g u →
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                                (fun _ => (1 : Homogenization.Mat d)) U f g uhom →
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
                                  MeasureTheory.eLpNorm f ⊤ (MeasureTheory.volume.restrict U))
    ) :
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
                    (∀ ξ : ℝ, 1 ≤ ξ →
                      P.toMeasure {omega | ξ ≤ Z omega} ≤
                        ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log ξ ^ β)))) ∧
                    ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → Z omega ≤ ε⁻¹ →
                        ∀ lam : ℝ, 0 ≤ lam →
                          (∀ (f : Vec d → ℝ) (g u uhom : H1Function U),
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun x => opScale cStar ε •
                                SuperdiffusionCLT.Section7.epField nu omega ε x)
                              U (fun x => f x - lam * u.toFun x) g u →
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) U
                              (fun x => f x - lam * uhom.toFun x) g uhom →
                            eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict U) ≤
                              ENNReal.ofReal (4 * (C * |Real.log ε| ^ (-α))) *
                                (eLpNorm (fun x =>
                                    SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
                                    (volume.restrict U) +
                                  eLpNorm (fun x => f x - lam * u.toFun x) ⊤
                                    (volume.restrict U))) ∧
                          (0 < lam → ∀ v vb : H1Function U,
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun x => opScale cStar ε •
                                SuperdiffusionCLT.Section7.epField nu omega ε x)
                              U (fun x => 1 - lam * v.toFun x) 0 v →
                            SuperdiffusionCLT.Section7.IsDirichletSolution
                              (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) U
                              (fun x => 1 - lam * vb.toFun x) 0 vb →
                            eLpNorm (fun x => v.toFun x - vb.toFun x) ⊤ (volume.restrict U) ≤
                                ENNReal.ofReal (4 * (C * |Real.log ε| ^ (-α))) ∧
                              ∀ᵐ x ∂(volume.restrict U),
                                |v.toFun x - vb.toFun x| ≤ 4 * (C * |Real.log ε| ^ (-α))) := by
  intro α β hα hα1 hβ hβ1 hαβ U hU nu hnu hnu1 cStar hc K
  obtain ⟨hUo, hUb⟩ := resEst_open_bounded hU
  obtain ⟨C, hC, H⟩ := hRoot d hd α β hα hα1 hβ hβ1 hαβ U hU nu hnu hnu1 cStar hc K
  refine ⟨C, hC, fun P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 => ?_⟩
  obtain ⟨Z, hZm, hZt, hZae⟩ := H P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  refine ⟨Z, hZm, hZt, ?_⟩
  filter_upwards [hZae, SuperdiffusionCLT.Section7.w0_ae_isElliptic_rescaled hJ3 hnu] with
    omega hω hEllω
  intro ε hε hε2 hZε lam hlam
  have hlogpos : 0 < |Real.log ε| := by
    rw [abs_pos]
    exact (Real.log_neg hε (by linarith only [hε2])).ne
  have hE : 0 < C * |Real.log ε| ^ (-α) :=
    mul_pos (by linarith only [hC]) (Real.rpow_pos_of_pos hlogpos _)
  set s : ℝ := ((2 * cStar * |Real.log ε|) ^ ((1 : ℝ) / 2))⁻¹ with hs
  have hspos : 0 < s := by
    rw [hs]
    exact inv_pos.2 (Real.rpow_pos_of_pos (by positivity) _)
  have hErr : ∀ (F : Vec d → ℝ) (g w wt : H1Function U),
      SuperdiffusionCLT.Section7.IsDirichletSolution
        (fun x => s • SuperdiffusionCLT.Section7.epField nu omega ε x) U F g w →
      SuperdiffusionCLT.Section7.IsDirichletSolution (fun _ => (1 : Mat d)) U F g wt →
        eLpNorm (fun x => w.toFun x - wt.toFun x) ⊤ (volume.restrict U) ≤
          ENNReal.ofReal (C * |Real.log ε| ^ (-α)) *
            (eLpNorm (fun x => SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
              (volume.restrict U) + eLpNorm F ⊤ (volume.restrict U)) := by
    intro F g w wt hw hwt
    exact le_trans (le_trans le_self_add le_self_add) (hω ε hε hε2 hZε F g w wt hw hwt)
  obtain ⟨Lam, hLam⟩ := hEllω ε hε.ne' U hUb hUo.measurableSet
  have hEll : IsEllipticFieldOn (s * nu) (s * Lam) U
      (fun x => s • SuperdiffusionCLT.Section7.epField nu omega ε x) :=
    resEst_isEllipticFieldOn_smul hspos hLam
  refine ⟨fun f g u uhom hu huh => ?_, fun hlampos v vb hv hvb => ?_⟩
  · have hu' := (resEst_dirichlet_half (A := SuperdiffusionCLT.Section7.epField nu omega ε)
      s).1 hu
    have huh' := resEst_dirichlet_half_laplace.1 huh
    have H1 := resEst_compare hUo hUb hE hErr hlam f g u uhom hu' huh'
    rw [resEst_eLpNorm_two_mul (fun x => f x - lam * u.toFun x)] at H1
    refine H1.trans ?_
    set A := eLpNorm (fun x => SuperdiffusionCLT.Section7.eucNorm (g.grad x)) ⊤
      (volume.restrict U)
    set B := eLpNorm (fun x => f x - lam * u.toFun x) ⊤ (volume.restrict U)
    have h4 : ENNReal.ofReal (4 * (C * |Real.log ε| ^ (-α))) =
        ENNReal.ofReal (2 * (C * |Real.log ε| ^ (-α))) * 2 := by
      rw [show 4 * (C * |Real.log ε| ^ (-α)) = 2 * (C * |Real.log ε| ^ (-α)) * 2 by ring,
        ENNReal.ofReal_mul (by linarith only [hE])]
      simp
    rw [h4, mul_assoc]
    refine mul_le_mul_right ?_ _
    calc A + 2 * B ≤ 2 * A + 2 * B :=
          add_le_add_left (le_mul_of_one_le_left zero_le one_le_two) _
      _ = 2 * (A + B) := (mul_add _ _ _).symm
  · have hv' := (resEst_dirichlet_half (A := SuperdiffusionCLT.Section7.epField nu omega ε)
      s).1 hv
    have hvb' := resEst_dirichlet_half_laplace.1 hvb
    have H1 := resEst_exit_compare hUo hUb hEll hE hErr hlampos v vb hv' hvb'
    refine ⟨H1, ?_⟩
    have hfin : eLpNorm (fun x => v.toFun x - vb.toFun x) ⊤ (volume.restrict U) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top H1
    filter_upwards [resEst_ae_abs_le (U := U) hfin] with x hx
    refine hx.trans ?_
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top H1
    rwa [ENNReal.toReal_ofReal (by linarith only [hE])] at this

section Witness

open SuperdiffusionCLT.Section8.DivergenceForm MarkovProcess.Semigroup

open SuperdiffusionCLT.Section7 in
/-- For the identity field the comparison hypothesis `hErr` holds with every constant: two
solutions of the same Dirichlet problem agree. -/
theorem resEst_hErr_identity {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {E : ℝ} (hE : 0 < E) :
    ∀ (F : Vec d → ℝ) (g w wt : H1Function U),
      IsDirichletSolution (fun _ => (1 : Mat d)) U F g w →
      IsDirichletSolution (fun _ => (1 : Mat d)) U F g wt →
        eLpNorm (fun x => w.toFun x - wt.toFun x) ⊤ (volume.restrict U) ≤
          ENNReal.ofReal E * (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict U) +
            eLpNorm F ⊤ (volume.restrict U)) := by
  intro F g w wt hw hwt
  by_cases hF : eLpNorm F ⊤ (volume.restrict U) = ⊤
  · rw [hF, add_top, ENNReal.mul_top (by simpa using hE)]
    exact le_top
  have hbd := Homogenization.Bornology.IsBounded.isBoundedDomain hUb
  have hfinU : IsFiniteMeasure (volume.restrict U) :=
    ⟨by
      simpa [Measure.restrict_apply_univ] using
        (lt_top_iff_ne_top.2 (volume_ne_top_of_isBoundedDomain hbd))⟩
  have hF2 : MemLp F 2 (volume.restrict U) :=
    MemLp.mono_exponent (show MemLp F ⊤ (volume.restrict U) from (Ne.lt_top hF)) le_top
  have hEll1 : IsEllipticFieldOn 1 1 U (fun _ => (1 : Mat d)) := by
    simpa using rc_isEllipticFieldOn_smul_one (d := d) one_pos hU.measurableSet
  have hwp := rc_dirichlet_wellPosed_of_elliptic hU hUb hEll1 hF2 g
  have hae := (hwp.2 w wt hw hwt).1
  have h0 : eLpNorm (fun x => w.toFun x - wt.toFun x) ⊤ (volume.restrict U) = 0 := by
    have : eLpNorm (fun x => w.toFun x - wt.toFun x) ⊤ (volume.restrict U) =
        eLpNorm (fun _ => (0 : ℝ)) ⊤ (volume.restrict U) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx, sub_self]
    rw [this]
    exact eLpNorm_zero
  rw [h0]
  exact zero_le


open SuperdiffusionCLT.Section7 in
/-- **Witness.**  On the unit disc of `ℝ²`, with the field `a' = Id` and `E = 1`, all hypotheses of
`resEst_exit_compare` hold for some `λ > 0` and solutions `v`, `vbar`, and the conclusion follows. -/
example : ∃ (lam : ℝ) (v vb : H1Function (euclideanBall (0 : Vec 2) 1)), 0 < lam ∧
    eLpNorm (fun x => v.toFun x - vb.toFun x) ⊤
      (volume.restrict (euclideanBall (0 : Vec 2) 1)) ≤ ENNReal.ofReal (4 * 1) := by
  have hV : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec 2) 1) :=
    Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall 0 one_pos
  have hUb : Bornology.IsBounded (euclideanBall (0 : Vec 2) 1) := by
    obtain ⟨R, -, hUB⟩ := exists_ball_superset_of_isBoundedDomain hV.2.1
    exact Metric.isBounded_ball.subset hUB
  have hsymm : ∀ y : Vec 2, symmPart ((1 / 2 : ℝ) • (1 : Mat 2)) = (1 / 2 : ℝ) • (1 : Mat 2) := by
    intro y
    funext i j
    simp only [symmPart, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; norm_num
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  let A : WholeSpaceAnalyticData 2 :=
    ⟨fun _ => (1 / 2 : ℝ) • (1 : Mat 2), 1 / 2, by norm_num, hsymm, by
      simp only [sub_self]
      exact continuousOn_const, le_refl _, measurable_const⟩
  let lam : PositiveShift := ⟨1, Set.mem_Ioi.2 one_pos⟩
  let w := ⇑(ZeroTraceSobolev.toL2 (alphaShiftedSolution A.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        A.hnu (partEllipticity A hV) (ballExit_datumL2 hV)))
  obtain ⟨u, -, hu⟩ := ballExit_exists_h10_solution A hV lam (w := w) Filter.EventuallyEq.rfl
  have hD : IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat 2)) (euclideanBall (0 : Vec 2) 1)
      (fun x => 1 - 1 * u.toH1Function.toFun x) 0 u.toH1Function := by
    refine ⟨fun φ => ?_, ⟨u, ?_⟩⟩
    · have := hu.2 φ
      simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero]
      exact this
    · funext x
      simp
  have hD' := resEst_dirichlet_half_laplace.1 hD
  have hEll1 : IsEllipticFieldOn 1 1 (euclideanBall (0 : Vec 2) 1) (fun _ => (1 : Mat 2)) := by
    simpa using rc_isEllipticFieldOn_smul_one (d := 2) one_pos hV.1.measurableSet
  exact ⟨1, u.toH1Function, u.toH1Function, one_pos,
    resEst_exit_compare hV.1 hUb hEll1 one_pos (resEst_hErr_identity hV.1 hUb one_pos) one_pos
      u.toH1Function u.toH1Function hD' hD'⟩

end Witness

end SuperdiffusionCLT.Section8
