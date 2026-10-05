/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.PreReal
public import SuperdiffusionCLT.Section5.Principal.FreshMeasurableB
public import SuperdiffusionCLT.Section5.Principal.DzPrimeB
public import SuperdiffusionCLT.Section2.Annealed.Integrability

/-!
# The per-cube chain of `lem.principal.term`

For one subcube `R = z + cu_n`, an `F_new`-measurable upper bound `D` of `D_z`, and an
`F_new`-measurable vector `P̂ = G_{-hbar_z} X`, the chain
`E[X·A_m X] ≤ E[(1+D) P̂·A_{m-h} P̂] = E[(1+D) P̂·bfAhom_{m-h}(R) P̂] ≤ (1+ε) E[(1+D)|bfAhom^{1/2} P̂|²]`
(`e.principal.switch`, `e.principal.conditional`, `e.principal.fv.to.inf`), in `ℝ≥0∞`, as
`pa_cube_bound`; and the coordinates of `P̂` for two independent response directions.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Probability (shellSigma shellSigma_le_ambient)
open scoped ENNReal

variable {d : ℕ}

/-- The coordinates of `P̂_z` are fresh-measurable, with the Dirichlet response of the flux in the
direction `ewD` and the Neumann response of the flux in the direction `ewN`. -/
theorem pa_phat_coord_fresh [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h Kc : ℕ) (ewD ewN e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h ω ewD) (wD ω))
    (hwN : ∀ ω, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
      (originCube d (Kc : ℤ)) (hshellFlux nu P m h ω ewN) (wN ω))
    (Q : TriadicCube d) (hQ : openCubeSet Q ⊆ openCubeSet (originCube d (Kc : ℤ)))
    (a : BlockCoord d) :
    Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      (fun ω => toFullBlockVec (principalPhat m h Q ω
        (blockSlope nu (m - h) P Q e e' (wD ω).toH1Function.grad
          (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x))) a) := by
  have hD := pmeas_measurable_dirichlet_average_fresh nu P m h Kc ewD wD hwD Q hQ
  have hN := pmeas_measurable_neumann_average_fresh nu P m h Kc ewN e' wN hwN Q hQ
  have hX1 : ∀ j, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] fun ω =>
      (blockSlope nu (m - h) P Q e e' (wD ω).toH1Function.grad
        (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x)).1 j :=
    fun j => (measurable_const.add ((measurable_pi_apply j).comp hD)).const_smul _
  have hX2 : ∀ j, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] fun ω =>
      (blockSlope nu (m - h) P Q e e' (wD ω).toH1Function.grad
        (fun x => (wN ω).toH1Function.grad x + hshellFlux nu P m h ω e' x)).2 j :=
    fun j => (measurable_const.add ((measurable_pi_apply j).comp hN)).const_smul _
  have hone : ∀ i j : Fin d, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      fun _ : ShellSeq d => (1 : Mat d) i j := fun _ _ => measurable_const
  have hzero : ∀ i j : Fin d, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      fun _ : ShellSeq d => (0 : Mat d) i j := fun _ _ => measurable_const
  have hneg : ∀ i j : Fin d, Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
      fun ω : ShellSeq d => (-principalGauge m h Q ω) i j :=
    fun i j => (pmeas_measurable_principalGauge_entry_fresh m h Q i j).neg
  cases a with
  | inl i =>
      exact (pmeas_measurable_matVecMul_apply hone hX1 i).add
        (pmeas_measurable_matVecMul_apply hzero hX2 i)
  | inr i =>
      exact (pmeas_measurable_matVecMul_apply hneg hX1 i).add
        (pmeas_measurable_matVecMul_apply hone hX2 i)

/-- The quadratic form of the old coarse-grained block matrix is nonnegative. -/
theorem pa_old_quad_nonneg [NeZero d] {nu : ℝ} (hnu : 0 < nu) (l : ℕ) (R : TriadicCube d)
    (ω : ShellSeq d) (Y : BlockVec d) :
    0 ≤ blockVecDot Y (blockMatVecMul (localizationCoarseAt nu l R ω) Y) :=
  SuperdiffusionCLT.Section2.Annealed.zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff
    hnu ω l R Y


/-- **The per-cube chain** (`e.principal.switch`, `e.principal.conditional`,
`e.principal.fv.to.inf`, `e.principal.pre.average`). `D` is a fresh-shell measurable upper bound of
`D_z`, `X` an arbitrary block vector field with `P̂ = G_{-hbar_z} X` having fresh-measurable
coordinates and integrable weights `(1 + D) P̂_α P̂_β`, and `hfv` the quadratic-form version of
`e.principal.fv.to.inf` with defect `ε`. -/
theorem pa_cube_bound [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m h : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (R : TriadicCube d)
    {D : ShellSeq d → ℝ} {X : ShellSeq d → BlockVec d} {ε : ℝ} (hε : 0 ≤ ε)
    (hD : Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)] D)
    (hDle : ∀ ω, principalDz nu m h R ω ≤ D ω)
    (hPhat : ∀ α : BlockCoord d,
      Measurable[shellSigma (d := d) (Set.Ioc (m - h) m)]
        (fun ω => toFullBlockVec (principalPhat m h R ω (X ω)) α))
    (hint : ∀ α β : BlockCoord d, Integrable
      (fun ω => (1 + D ω) * (toFullBlockVec (principalPhat m h R ω (X ω)) α *
        toFullBlockVec (principalPhat m h R ω (X ω)) β)) P.toMeasure)
    (hfv : ∀ Y : BlockVec d,
      |blockVecDot Y (blockMatVecMul (annealedBlockMatrix nu (m - h) P (cubeSet R)) Y) -
          blockVecDot Y (blockMatVecMul (ahomInfinite nu (m - h) P) Y)| ≤
        ε * blockVecDot Y (blockMatVecMul (ahomInfinite nu (m - h) P) Y)) :
    ∫⁻ ω, ENNReal.ofReal (blockVecDot (X ω)
        (blockMatVecMul (localizationCoarseAt nu m R ω) (X ω))) ∂P.toMeasure ≤
      ENNReal.ofReal (1 + ε) * ∫⁻ ω, ENNReal.ofReal ((1 + D ω) *
        blockLenSq (ahomSqrtApply nu (m - h) P (principalPhat m h R ω (X ω)))) ∂P.toMeasure := by
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    sigmaBarInfinite_pos hnu (m - h) hPrefix hJ2 hJ3 hJ4
  set Ph : ShellSeq d → BlockVec d := fun ω => principalPhat m h R ω (X ω) with hPh
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω => le_trans (principalDz_nonneg hnu m h R ω) (hDle ω)
  have hq : ∀ ω, 0 ≤ blockVecDot (Ph ω)
      (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Ph ω)) :=
    fun ω => pa_old_quad_nonneg hnu (m - h) R ω _
  have hA : ∀ ω, 0 ≤ (1 + D ω) * blockVecDot (Ph ω)
      (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Ph ω)) :=
    fun ω => mul_nonneg (by linarith only [hD0 ω]) (hq ω)
  have hAint := principal_old_integrable hnu m h hPrefix hJ2 hJ3 hJ4 R hD hPhat hint
  -- step 1: switch
  have h1 : ∫⁻ ω, ENNReal.ofReal (blockVecDot (X ω)
        (blockMatVecMul (localizationCoarseAt nu m R ω) (X ω))) ∂P.toMeasure ≤
      ∫⁻ ω, ENNReal.ofReal ((1 + D ω) * blockVecDot (Ph ω)
        (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Ph ω))) ∂P.toMeasure := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    refine (principal_switch hnu m h R ω (X ω)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hDle ω]) (hq ω)
  have h2 : ∫⁻ ω, ENNReal.ofReal ((1 + D ω) * blockVecDot (Ph ω)
        (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Ph ω))) ∂P.toMeasure =
      ENNReal.ofReal (∫ ω, (1 + D ω) * blockVecDot (Ph ω)
        (blockMatVecMul (localizationCoarseAt nu (m - h) R ω) (Ph ω)) ∂P.toMeasure) :=
    (ofReal_integral_eq_lintegral_ofReal hAint (Filter.Eventually.of_forall hA)).symm
  -- step 2: conditional
  have h3 := principal_conditional hnu m h hPrefix hJ2 hJ3 hJ4 R hD hPhat hint
  -- step 3: finite volume to infinite
  have hLint : Integrable (fun ω => (1 + ε) * ((1 + D ω) *
      blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω)))) P.toMeasure := by
    have := (integrable_weight_quad hint (ahomInfinite nu (m - h) P)).const_mul (1 + ε)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [ahomInfinite_quad nu (m - h) P hσ, hPh]
  have hpt : ∀ ω, (1 + D ω) * blockVecDot (Ph ω)
      (blockMatVecMul (annealedBlockMatrix nu (m - h) P (cubeSet R)) (Ph ω)) ≤
      (1 + ε) * ((1 + D ω) * blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) := by
    intro ω
    have hf := (abs_le.mp (hfv (Ph ω))).2
    rw [ahomInfinite_quad nu (m - h) P hσ] at hf
    have hw : 0 ≤ 1 + D ω := by linarith only [hD0 ω]
    calc (1 + D ω) * blockVecDot (Ph ω)
          (blockMatVecMul (annealedBlockMatrix nu (m - h) P (cubeSet R)) (Ph ω))
        ≤ (1 + D ω) * ((1 + ε) * blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) := by
          refine mul_le_mul_of_nonneg_left ?_ hw
          linarith only [hf]
      _ = (1 + ε) * ((1 + D ω) * blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) := by ring
  have h4 : ∫ ω, (1 + D ω) * blockVecDot (Ph ω)
      (blockMatVecMul (annealedBlockMatrix nu (m - h) P (cubeSet R)) (Ph ω)) ∂P.toMeasure ≤
      ∫ ω, (1 + ε) * ((1 + D ω) *
        blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) ∂P.toMeasure :=
    integral_mono (integrable_weight_quad hint _) hLint hpt
  have hLnn : ∀ ω, 0 ≤ (1 + ε) * ((1 + D ω) *
      blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) := by
    intro ω
    refine mul_nonneg (by linarith only [hε]) (mul_nonneg (by linarith only [hD0 ω]) ?_)
    unfold blockLenSq
    exact add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  have h5 : ENNReal.ofReal (∫ ω, (1 + ε) * ((1 + D ω) *
        blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) ∂P.toMeasure) =
      ENNReal.ofReal (1 + ε) * ∫⁻ ω, ENNReal.ofReal ((1 + D ω) *
        blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) ∂P.toMeasure := by
    rw [ofReal_integral_eq_lintegral_ofReal hLint (Filter.Eventually.of_forall hLnn),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun ω => ENNReal.ofReal_mul (by linarith only [hε])
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ENNReal.ofReal (∫ ω, (1 + ε) * ((1 + D ω) *
        blockLenSq (ahomSqrtApply nu (m - h) P (Ph ω))) ∂P.toMeasure) :=
        ENNReal.ofReal_le_ofReal (h3 ▸ h4)
    _ = _ := h5

end SuperdiffusionCLT.Section5
