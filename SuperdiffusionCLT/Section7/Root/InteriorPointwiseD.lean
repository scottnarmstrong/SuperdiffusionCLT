/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorPointwiseC
public import SuperdiffusionCLT.Section7.Root.InteriorPointwise
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorFinal
public import SuperdiffusionCLT.Frozen.Section6.SharpScaleInputs
public import SuperdiffusionCLT.Frozen.Section5.SigmaBarSharpBounds

/-!
# Interior approximation: the approximation at one scale

`ia_omega`: for a fixed sample, a solution in `y + □_k` is within `C δ_k (‖u - (u)‖_{L̲²} +
σ̄_k⁻¹ 3^{2k} ‖f‖_∞)` in `L^∞(V)` of a solution of `-σ̄_k Δ uhom = f` in the rounded cube `V`, given the
bounds of the mollified flux on the cells, the Lipschitz estimate on the cubes around the cell
centres, the bound of the field and the scale separation.  `ia_approx` is the almost-sure form:
with the sharp inputs and the window of `σ̄`, almost surely, for every grid centre `y` and every
scale `k` in `[n + 1, n + k1]`, the approximation holds, with one random scale for all centres
(`l.Dirichlet.interior.Linfty.approx`).
-/

@[expose] public section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ia_omega [NeZero d] (hd : 2 ≤ d) (CF CL cL : ℝ) (hCF : 1 ≤ CF) (hCL : 1 ≤ CL) :
    ∃ (N0 : ℕ) (Cthr Cdet : ℝ), 1 ≤ N0 ∧ (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N0) < 1 ∧ 1 ≤ Cthr ∧ 1 ≤ Cdet ∧
      ∀ {omega : ShellSeq d} {P : ProbabilityMeasure (ShellSeq d)} {nu ε ρ N : ℝ}
        {n k l A k1 : ℕ} {y : Vec d},
        0 < nu → 0 < ε → 0 ≤ N →
        y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)) → nK N n ≤ l → l + 5 ≤ k →
        k ≤ n + k1 → l = nK N k → ⌈N * Real.log (k : ℝ)⌉₊ ≤ k → 2 ≤ k →
        (1 : ℝ) < (k : ℝ) - 1 →
        1 ≤ sigmaBarInfinite nu k P →
        sigmaBarInfinite nu k P ≤ 2 * sigmaBarInfinite nu (k - 1) P →
        sigmaBarInfinite nu (k - 1) P ≤ 2 * sigmaBarInfinite nu k P →
        (N * Real.log (k : ℝ) + 1) * deltaScale ε ρ ((k : ℝ) - 1) ≤ cL →
        Cthr * ((CF * Real.sqrt (sigmaBarInfinite nu k P) * deltaScale ε ρ (k : ℝ) *
              Real.sqrt nu + CF * (|nu - sigmaBarInfinite nu k P| + (k : ℝ) ^ (1 + ρ))) *
            (CF * (3 : ℝ) ^ (l + 1) / nu)) ≤ deltaScale ε ρ (k : ℝ) * 3 ^ k →
        Cthr * (3 : ℝ) ^ l ≤ deltaScale ε ρ (k : ℝ) * 3 ^ k →
        Cthr * (((d : ℝ) * d * (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 + nu ^ 2) / nu / nu) ^
            deGiorgiPower d *
          ((3 : ℝ) ^ l / 3 ^ k + sigmaBarInfinite nu k P / nu * ((3 : ℝ) ^ l / 3 ^ k) ^ 2) ≤
          deltaScale ε ρ (k : ℝ) →
        (∃ S : Mat d, matTranspose S = -S ∧ ∀ x : Vec d, ia_field nu omega y k x =
          Section6.fullCoefficientRecentered nu omega x + S) →
        (∃ Lam : ℝ, IsEllipticFieldOn nu Lam (shiftCube y (k : ℤ))
          (Section6.fullCoefficientRecentered nu omega)) →
        Continuous (Section6.fullStreamRecentered omega) →
        (∀ᵐ x ∂(volume.restrict (shiftCube y (k : ℤ))), Book.Ch02.matrixOperatorNorm
          (SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
            (translateSet y (cubeSet (originCube d (k : ℤ)))) x) ≤ (k : ℝ) ^ (1 + ρ)) →
        (∀ W : Set (Vec d), W ⊆ shiftCube y (k : ℤ) →
          ∀ (u : H1Function W) (f : Vec d → ℝ), AEMeasurable f (volume.restrict W) →
          IsWeakSolutionOn (ia_field nu omega y k) W u f (fun _ => 0) →
          ∀ (η : Vec d → ℝ) (A : ℝ) (L : NNReal), (∀ w, |η w| ≤ A) → LipschitzWith L η →
          (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
          ∀ j : Fin d → ℤ, l2b_cell (y + l2b_pt l j) (l + 1) ⊆ W →
          ∀ x ∈ l2b_cell (y + l2b_pt l j) l,
            ENNReal.ofReal ‖a16_mollify d ((3 : ℝ) ^ (l : ℤ)) η (fun w => matVecMul
                (ia_field nu omega y k w - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                  nu k P) • (1 : Mat d)) (u.grad w)) x‖ ≤
              ENNReal.ofReal (3 ^ d * (6 * (L : ℝ) + A)) *
                (ENNReal.ofReal (CF * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                    nu k P) * (ε * (k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ)) * Real.sqrt nu) *
                  l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((l + 1 : ℕ) : ℤ))))
                    (l2b_cell (y + l2b_pt l j) (l + 1)) (fun x => ‖eucNorm (u.grad x)‖ₑ) 2 +
                ENNReal.ofReal ((CF * Real.sqrt (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                    nu k P) * (ε * (k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ)) * Real.sqrt nu +
                    CF * (|nu - (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu k P)| +
                      (k : ℝ) ^ (1 + ρ))) * (CF * (3 : ℝ) ^ ((l + 1 : ℕ) : ℤ) / nu)) *
                  l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((l + 1 : ℕ) : ℤ))))
                    (l2b_cell (y + l2b_pt l j) (l + 1)) (fun x => ‖f x‖ₑ)
                    (Real.conjExponent (sobStar d)))
        ) →
        (∀ z ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + (A + k1 + 1))),
∀ m' lh : ℕ, nK N n ≤ lh → lh < m' →
            ((m' : ℝ) - (lh : ℝ)) * deltaScale ε ρ (m' : ℝ) ≤ cL →
            ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube z (m' : ℤ))),
              IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
                (shiftCube z (m' : ℤ)) u f (fun _ => 0) →
              ENNReal.ofReal ((Real.sqrt (sigmaBarInfinite nu m' P))⁻¹ * Real.sqrt nu) *
                    lpBar (shiftCube z (lh : ℤ)) 2 (fun x => eucNorm (u.grad x)) +
                  ENNReal.ofReal ((3 : ℝ) ^ (-(lh : ℝ))) *
                    lpBar (shiftCube z (lh : ℤ)) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (lh : ℤ), u.toFun w) ≤
                ENNReal.ofReal (CL * (3 : ℝ) ^ (-(m' : ℝ))) *
                    lpBar (shiftCube z (m' : ℤ)) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ), u.toFun w) +
                  ENNReal.ofReal (CL * (sigmaBarInfinite nu m' P)⁻¹ * (3 : ℝ) ^ m') *
                    eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ)))
        ) →
        ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (k : ℤ))),
          IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) (shiftCube y (k : ℤ))
            u f (fun _ => 0) →
          eLpNorm f ⊤ (volume.restrict (shiftCube y (k : ℤ))) ≠ ⊤ →
          ∃ (f' : Vec d → ℝ) (uhom : H1Function (ia_V d N0 k y)),
            Measurable f' ∧
            (∀ x, |f' x| ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y (k : ℤ)))).toReal) ∧
            IsWeakSolutionOn (fun _ => sigmaBarInfinite nu k P • (1 : Mat d)) (ia_V d N0 k y)
              uhom f' (fun _ => 0) ∧
            eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (ia_V d N0 k y)) ≤
              ENNReal.ofReal (Cdet * deltaScale ε ρ (k : ℝ) *
                (h1_l2 (h1_cube y k) u.toFun + (sigmaBarInfinite nu k P)⁻¹ * (3 : ℝ) ^ (2 * k) *
                  (eLpNorm f ⊤ (volume.restrict (shiftCube y (k : ℤ)))).toReal)) := by
  obtain ⟨N0, Cthr, Cdet, hN0, hdim, hCthr, hCdet, Hdet⟩ := ia_approx_det hd CF CL hCF hCL
  refine ⟨N0, Cthr, Cdet, hN0, hdim, hCthr, hCdet, ?_⟩
  intro omega P nu ε ρ N n k l A k1 y hnu hε hN0' hy hnl hl5 hkn hl hcnk hk2 hk1k hσ1 hσσ' hσ'σ hwinN
    hN1 hN2 hN3 hS hrecell hcont hkb hcell hLipn f u hu hfin
  set σ : ℝ := sigmaBarInfinite nu k P with hσdef
  set σ' : ℝ := sigmaBarInfinite nu ((k - 1 : ℕ)) P with hσ'def
  have hσpos : 0 < σ := by linarith only [hσ1]
  have hσ'1 : σ / 2 ≤ σ' := by linarith only [hσσ']
  have hσ'2 : σ' ≤ 2 * σ := hσ'σ
  have hσ'pos : 0 < σ' := by linarith only [hσ'1, hσpos]
  set δ : ℝ := deltaScale ε ρ (k : ℝ) with hδ
  have hk1' : (1 : ℝ) < k := by have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
                                linarith only [this]
  have hδpos : 0 < δ := deltaScale_pos hε hk1'
  -- the measurable representative and the centred equation
  obtain ⟨f', hf'm, hf'b, hf'ae⟩ := ip_fmod hfin
  set F : ℝ := (eLpNorm f ⊤ (volume.restrict (shiftCube y (k : ℤ)))).toReal with hF
  have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
  have hWo := rc_isOpen_shiftCube y (k : ℤ)
  have hWb : Bornology.IsBounded (shiftCube y (k : ℤ)) := by
    rw [ip_shiftCube_ball]; exact Metric.isBounded_ball
  obtain ⟨Lam', hEllRec⟩ := hrecell
  obtain ⟨S, hS', hSx⟩ := hS
  have hu_rec : IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega)
      (shiftCube y (k : ℤ)) u f' (fun _ => 0) := ip_sol_congr hf'ae hu
  have hu' : IsWeakSolutionOn (ia_field nu omega y k) (shiftCube y (k : ℤ)) u f' (fun _ => 0) :=
    ip_centered_of_recentered hWo hWb hEllRec hS' hSx hu_rec
  have hrc : Continuous (Section6.fullCoefficientRecentered nu omega) :=
    Section6.continuous_fullCoefficientRecentered hcont
  have hccont : Continuous (fun x => SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
      (translateSet y (cubeSet (originCube d (k : ℤ)))) x) := by
    have : (fun x => SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
        (translateSet y (cubeSet (originCube d (k : ℤ)))) x) =
        fun x => Section6.fullCoefficientRecentered nu omega x + S - nu • (1 : Mat d) := by
      funext x
      have h1 := hSx x
      unfold ia_field at h1
      rw [eq_sub_iff_add_eq, ← h1]
      abel
    rw [this]
    exact (hrc.add continuous_const).sub continuous_const
  have hEll : IsEllipticFieldOn nu (((d : ℝ) * d * (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 + nu ^ 2) / nu)
      (shiftCube y (k : ℤ)) (ia_field nu omega y k) :=
    ip_isElliptic hnu hccont
      (fun x => Section6.HarmonicApprox.symmPart_centeredStreamField_add nu omega _ x) hWo hkb
  -- the hypotheses of the deterministic core
  have hl5' : l + 5 ≤ k := hl5
  have hlk : l < k := by omega
  have hHFlux : ∀ (η : Vec d → ℝ) (A_ : ℝ) (L : NNReal), (∀ w, |η w| ≤ A_) → LipschitzWith L η →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ k / 4 + 3 ^ l →
        ∀ x ∈ l2b_cell (y + l2b_pt l j) l,
          ‖a16_mollify d ((3 : ℝ) ^ l) η
              (fun w => matVecMul (ia_field nu omega y k w - σ • (1 : Mat d)) (u.grad w)) x‖ ≤
            3 ^ d * (6 * (L : ℝ) + A_) *
              (CF * Real.sqrt σ * δ * Real.sqrt nu *
                  lipGradL2 (shiftCube (y + l2b_pt l j) ((l + 1 : ℕ) : ℤ)) u.grad +
                ((CF * Real.sqrt σ * δ * Real.sqrt nu + CF * (|nu - σ| + (k : ℝ) ^ (1 + ρ))) *
                  (CF * (3 : ℝ) ^ (l + 1) / nu)) * F) := by
    intro η A_ L hA_ hL hηs j hj x hx
    have hcellW := ip_cell_sub hl5' hj
    have h := hcell (shiftCube y (k : ℤ)) subset_rfl u f' hf'm.aemeasurable hu' η A_ L hA_ hL hηs j
      hcellW x hx
    simp only [zpow_natCast] at h
    have hsubS : shiftCube (y + l2b_pt l j) ((l + 1 : ℕ) : ℤ) ⊆ shiftCube y (k : ℤ) := by
      rw [ip_shiftCube_ball, ip_shiftCube_ball]
      exact ip_cube_sub hl5' (by omega) hj
    have hK0 : 0 ≤ (3 : ℝ) ^ d * (6 * (L : ℝ) + A_) := by
      have : 0 ≤ A_ := (abs_nonneg _).trans (hA_ 0)
      positivity
    exact ip_flux_real hsubS (ip_conj_pos hd) hf'b hK0 (by positivity) (by positivity) h
  have hLipz : ∀ j : Fin d → ℤ, dist (y + l2b_pt l j) y ≤ (3 : ℝ) ^ k / 4 + 3 ^ l →
      ∀ lh : ℕ, (lh = l + 1 ∨ lh = l + 3) →
        Real.sqrt nu / Real.sqrt σ' *
            lipGradL2 (shiftCube (y + l2b_pt l j) (lh : ℤ)) u.grad ≤
          CL * (((3 : ℝ) ^ (k - 1))⁻¹ * h1_l2 (h1_cube (y + l2b_pt l j) (k - 1)) u.toFun) +
            CL * (σ'⁻¹ * (3 : ℝ) ^ (k - 1) * F) ∧
        ((3 : ℝ) ^ lh)⁻¹ * h1_l2 (h1_cube (y + l2b_pt l j) lh) u.toFun ≤
          CL * (((3 : ℝ) ^ (k - 1))⁻¹ * h1_l2 (h1_cube (y + l2b_pt l j) (k - 1)) u.toFun) +
            CL * (σ'⁻¹ * (3 : ℝ) ^ (k - 1) * F) := by
    intro j hj lh hlh
    set z : Vec d := y + l2b_pt l j with hz
    have hlt : lh < k - 1 := by omega
    have hnl' : nK N n ≤ lh := by omega
    have hzgrid := ip_center_mem_grid (N := N) (A := A) (k1 := k1) hy hnl hlk hkn z j rfl hj
    have hw : (((k - 1 : ℕ) : ℝ) - (lh : ℝ)) * deltaScale ε ρ ((k - 1 : ℕ) : ℝ) ≤ cL := by
      have hc1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [hc1]
      have hd0 : 0 ≤ deltaScale ε ρ ((k : ℝ) - 1) :=
        (deltaScale_pos hε hk1k).le
      have hcn := (Nat.ceil_lt_add_one (mul_nonneg hN0' (Real.log_nonneg hk1'.le))).le
      have hlnat : (l : ℝ) = (k : ℝ) - (⌈N * Real.log (k : ℝ)⌉₊ : ℝ) := by
        rw [hl]; unfold nK; rw [Nat.cast_sub hcnk]
      have hlh' : (l : ℝ) + 1 ≤ lh := by
        have : l + 1 ≤ lh := by omega
        exact_mod_cast this
      refine le_trans (mul_le_mul_of_nonneg_right ?_ hd0) hwinN
      linarith only [hcn, hlnat, hlh']
    have hsubz : shiftCube z ((k - 1 : ℕ) : ℤ) ⊆ shiftCube y (k : ℤ) := by
      rw [ip_shiftCube_ball, ip_shiftCube_ball]
      exact ip_cube_sub_pred hl5' hj
    have hu_z := hu.restrict' (rc_isOpen_shiftCube z ((k - 1 : ℕ) : ℤ)) hsubz
    have hl' := hLipn z hzgrid (k - 1) lh hnl' hlt hw f
      (u.restrict (rc_isOpen_shiftCube z ((k - 1 : ℕ) : ℤ)) hsubz) hu_z
    exact ia_lipz hsubz (by omega) (rc_isOpen_shiftCube z ((k - 1 : ℕ) : ℤ)) u hfin
      (by linarith only [hCL]) hnu hσ'pos hl'
  have ha1nn : 0 ≤ CF * Real.sqrt σ * δ * Real.sqrt nu := by
    have : 0 ≤ CF := by linarith only [hCF]
    positivity
  have ha2nn : 0 ≤ (CF * Real.sqrt σ * δ * Real.sqrt nu + CF * (|nu - σ| + (k : ℝ) ^ (1 + ρ))) *
      (CF * (3 : ℝ) ^ (l + 1) / nu) := by
    have : 0 ≤ CF := by linarith only [hCF]
    positivity
  obtain ⟨uhom, hhom, hbound⟩ := Hdet (y := y) (l := l) (m := k) hl5' (a := ia_field nu omega y k)
    (nu := nu) (σ := σ) (σ' := σ') (δ := δ) (Lam := ((d : ℝ) * d * (nu + (k : ℝ) ^ (1 + ρ)) ^ 2 + nu ^ 2) / nu)
    (a1 := CF * Real.sqrt σ * δ * Real.sqrt nu)
    (a2 := (CF * Real.sqrt σ * δ * Real.sqrt nu + CF * (|nu - σ| + (k : ℝ) ^ (1 + ρ))) *
      (CF * (3 : ℝ) ^ (l + 1) / nu)) (F := F)
    hnu hσpos hσ'1 hσ'2 hδpos hF0 ha1nn ha2nn (le_of_eq (by ring)) hEll u hf'm hf'b hu'
    hHFlux (fun j hj => (hLipz j hj (l + 1) (Or.inl rfl)).1)
    (fun j hj => (hLipz j hj (l + 3) (Or.inr rfl)).2) hN1 hN2 hN3
  exact ⟨f', uhom, hf'm, hf'b, hhom, hbound⟩

theorem ip_L_le {Cm a b c : ℝ} (hCm : 1 ≤ Cm) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ≤ Cm * (Cm * (a + b) + c) ∧ b ≤ Cm * (Cm * (a + b) + c) ∧ c ≤ Cm * (Cm * (a + b) + c) := by
  have h1 : a + b ≤ Cm * (a + b) := le_mul_of_one_le_left (by linarith only [ha, hb]) hCm
  have h2 : Cm * (a + b) + c ≤ Cm * (Cm * (a + b) + c) :=
    le_mul_of_one_le_left (by nlinarith only [h1, ha, hb, hc]) hCm
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [h1, h2, ha, hb, hc]

theorem ia_approx (d : ℕ) [NeZero d] (hd : 2 ≤ d)
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
    :
    ∃ (C N : ℝ) (N0 : ℕ), 1 ≤ C ∧ 4 * deGiorgiPower d + 3 ≤ N ∧ 1 ≤ N0 ∧
      (d : ℝ) * (4 / 5 : ℝ) ^ (2 * N0) < 1 ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 → ∀ A k1 : ℕ,
      ∃ Lhat : ℝ, 1 ≤ Lhat ∧ ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∃ X : ShellSeq d → ℝ, Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
          Homogenization.IndependentSums.IsBigO P.toMeasure
            (Homogenization.IndependentSums.gammaSigma ρ) (fun omega => Real.log (X omega)) Lhat ∧
          ∀ᵐ omega ∂P.toMeasure, ∀ n k : ℕ, Lhat ≤ (nK N n : ℝ) → X omega ≤ (3 : ℝ) ^ nK N n →
            n + 1 ≤ k → k ≤ n + k1 →
            ∀ y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)),
            ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (k : ℤ))),
              IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) (shiftCube y (k : ℤ))
                u f (fun _ => 0) →
              eLpNorm f ⊤ (volume.restrict (shiftCube y (k : ℤ))) ≠ ⊤ →
              ∃ (f' : Vec d → ℝ) (uhom : H1Function (ia_V d N0 k y)),
                Measurable f' ∧
                (∀ x, |f' x| ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y (k : ℤ)))).toReal) ∧
                IsWeakSolutionOn (fun _ => sigmaBarInfinite nu k P • (1 : Mat d)) (ia_V d N0 k y)
                  uhom f' (fun _ => 0) ∧
                eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (ia_V d N0 k y)) ≤
                  ENNReal.ofReal (C * deltaScale ε ρ (k : ℝ) *
                    (h1_l2 (h1_cube y k) u.toFun + (sigmaBarInfinite nu k P)⁻¹ * (3 : ℝ) ^ (2 * k) *
                      (eLpNorm f ⊤ (volume.restrict (shiftCube y (k : ℤ)))).toReal)) := by
  obtain ⟨CF, hCF, Hcell⟩ := ia_ae_cell d hd hInputs
  obtain ⟨Cb, hCb, Hkb⟩ := ia_ae_kb d hInputs
  obtain ⟨CL, cL, hCL, hcL, HL⟩ := lip_interior_grid_final d hd hInputs hS5
  obtain ⟨N0, Cthr, Cdet, hN0, hdim, hCthr, hCdet, Homega⟩ := ia_omega hd CF CL cL hCF hCL
  have hp := ip_p_ge_one hd
  set p : ℝ := deGiorgiPower d with hpdef
  set N : ℝ := 4 * p + 3 with hNdef
  have hN0' : 0 ≤ N := by linarith only [hp]
  refine ⟨Cdet, N, N0, hCdet, le_rfl, hN0, hdim, ?_⟩
  intro nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 A k1
  set A' : ℕ := A + k1 + 1 with hA'
  obtain ⟨La, hLa, Ha⟩ := Hcell nu hnu hnu1 cStar hcStar K ε ρ (max CF N) hε hε1 hρ hρ1
    (le_max_left _ _)
  obtain ⟨Lb, hLb, Hb⟩ := Hkb nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1
  obtain ⟨Ll, hLl, Hl⟩ := HL nu hnu hnu1 cStar hcStar K ε ρ hε hε1 hρ hρ1 A' N hN0'
  obtain ⟨L0, hL0⟩ := lip_sigma_window d hd hS5 nu hnu hnu1 cStar hcStar K
  obtain ⟨Lnum, hLnum4, hLnum⟩ := ip_numeric d (N := N) hCthr hCF hcL hnu hnu1 hε hε1 hρ.le hρ1 le_rfl hp
  obtain ⟨Lfa, hLfa, Hga⟩ := ia_grid_scale d hN0' hρ A'
  obtain ⟨Cm, hCm, Hm⟩ := ia_max_scale.{0} hρ
  have hLfa0 : ∀ L : ℝ, 1 ≤ L → 0 ≤ Lfa L := fun L hL => by linarith only [(hLfa L hL).2]
  refine ⟨Cm * (Cm * (Lfa La + Lfa Lb) + Ll) + Lnum + L0 + N + 8, ?_, ?_⟩
  · have : 0 ≤ Cm * (Cm * (Lfa La + Lfa Lb) + Ll) := by
      have := hLfa0 La hLa; have := hLfa0 Lb hLb
      positivity
    linarith only [this, hLnum4, hN0', (Nat.cast_nonneg L0 : (0 : ℝ) ≤ L0)]
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0a, hX0am, hX0a1, hX0aO, haeA⟩ := Ha P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨X0b, hX0bm, hX0b1, hX0bO, haeB⟩ := Hb P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xl, hXlm, hXl1, hXlO, haeL⟩ := Hl P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨Xa, hXam, hXa1, hXaO, hXaae⟩ := Hga P hPrefix hJ2 X0a hX0am La hLa hX0aO
  obtain ⟨Xb, hXbm, hXb1, hXbO, hXbae⟩ := Hga P hPrefix hJ2 X0b hX0bm Lb hLb hX0bO
  have hXab := Hm (hLfa0 La hLa) (hLfa0 Lb hLb) hXa1 hXb1 hXaO hXbO
  have hmax1 : ∀ ω, 1 ≤ max (Xa ω) (Xb ω) := fun ω => le_max_of_le_left (hXa1 ω)
  have hXabl := Hm (X := fun ω => max (Xa ω) (Xb ω)) (by have := hLfa0 La hLa; have := hLfa0 Lb hLb; positivity)
    (by linarith only [hLl]) hmax1 hXl1 hXab hXlO
  refine ⟨fun ω => max (max (Xa ω) (Xb ω)) (Xl ω), (hXam.max hXbm).max hXlm,
    fun ω => le_max_of_le_left (hmax1 ω), ?_, ?_⟩
  · refine hXabl.mono_scale ?_
    linarith only [hLnum4, hN0', (Nat.cast_nonneg L0 : (0 : ℝ) ≤ L0)]
  have hlatA := b2_ae_forall_lattice d haeA
  have hlatB := b2_ae_forall_lattice d haeB
  have hskew : ∀ y : Vec d, ∀ᵐ omega ∂P.toMeasure, ∀ k : ℕ, ∃ S : Mat d, matTranspose S = -S ∧
      ∀ x : Vec d, ia_field nu omega y k x =
        Section6.fullCoefficientRecentered nu omega x + S := fun y => ia_ae_skew hPrefix hJ2 hJ3 nu y
  have hlatS := b2_ae_forall_lattice d hskew
  filter_upwards [hlatA, hlatB, hlatS, hXaae, hXbae, haeL, Section6.ae_continuous_fullStreamRecentered hJ3,
    w0_ae_isElliptic_bounded hJ3 hnu] with omega hA hB hS hXa hXb hLip hcont hrecell
  intro n k hLn hXn hnk hkn y hy f u hu hfin
  -- the scales
  set Lsum : ℝ := Cm * (Cm * (Lfa La + Lfa Lb) + Ll) with hLsum
  have hLsums := ip_L_le hCm (hLfa0 La hLa) (hLfa0 Lb hLb) (by linarith only [hLl])
  have hLsum0 : 0 ≤ Lsum := by
    have := hLfa0 La hLa; have := hLfa0 Lb hLb
    have : 0 ≤ Ll := by linarith only [hLl]
    positivity
  have hL0r : (0 : ℝ) ≤ L0 := Nat.cast_nonneg L0
  have hnKn : (nK N n : ℝ) ≤ n := by exact_mod_cast nK_le N n
  have hLnn : Lsum + Lnum + L0 + N + 8 ≤ (n : ℝ) := hLn.trans hnKn
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith only [hLnn, hLnum4, hLsum0, hL0r, hN0']
    exact_mod_cast this
  have hNn : N ≤ (n : ℝ) := by linarith only [hLnn, hLnum4, hLsum0, hL0r]
  have hkl : nK N n ≤ nK N k := ip_nK_mono hN0' hNn hn1 (by omega)
  have hkr : (nK N n : ℝ) ≤ nK N k := by exact_mod_cast hkl
  have hnKk : (nK N k : ℝ) ≤ k := by exact_mod_cast nK_le N k
  have hnk' : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
  have hkbig : Lsum + Lnum + L0 + N + 8 ≤ (k : ℝ) := by linarith only [hLnn, hnk']
  have hk1 : (1 : ℝ) < k := by linarith only [hkbig, hLnum4, hLsum0, hL0r, hN0']
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by linarith only [hk1, hkbig, hLnum4, hLsum0, hL0r, hN0']
    exact_mod_cast this
  have hLnk : ∀ L : ℝ, L ≤ Lsum + Lnum + L0 + N + 8 → L ≤ (nK N n : ℝ) := fun L hL => hL.trans hLn
  have hXa' : Xa omega ≤ (3 : ℝ) ^ nK N n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXn
  have hXb' : Xb omega ≤ (3 : ℝ) ^ nK N n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXn
  have hXl' : Xl omega ≤ (3 : ℝ) ^ nK N n := le_trans (le_max_right _ _) hXn
  have hyA' : y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A')) :=
    b2_gridPts_mono le_rfl (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) hy
  have hylat := b2_gridPts_subset_lattice (by positivity) hy
  have h3n : (3 : ℝ) ^ nK N n ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) ((nK_le N n).trans (by omega))
  -- the numerical facts
  obtain ⟨hσ1, hσk, -, -⟩ := hL0 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 k k (by
    have : (L0 : ℝ) ≤ k := by linarith only [hkbig, hLsum0, hLnum4, hN0']
    exact_mod_cast this) le_rfl (by omega)
  obtain ⟨-, -, hσσ', hσ'σ⟩ := hL0 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 (k - 1) k (by
    have : (L0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; linarith only [hkbig, hLsum0, hLnum4, hN0']
    exact_mod_cast this) (by omega) (by omega)
  obtain ⟨hcnk, hl5, hwinN, hN1, hN2, hN3⟩ := hLnum k (by linarith only [hkbig, hLsum0, hL0r, hN0'])
    (sigmaBarInfinite nu k P) hσ1 hσk
  have hk1k : (1 : ℝ) < (k : ℝ) - 1 := by linarith only [hkbig, hLnum4, hLsum0, hL0r, hN0']
  have hWo := rc_isOpen_shiftCube y (k : ℤ)
  have hWb : Bornology.IsBounded (shiftCube y (k : ℤ)) := by
    rw [ip_shiftCube_ball]; exact Metric.isBounded_ball
  have hwin : (k : ℤ) - ⌈(max CF N) * Real.log (k : ℝ)⌉ ≤ (nK N k : ℤ) := by
    have h1 := ip_ceil_le (N := N) (M := max CF N) hN0' (le_max_right _ _) (by linarith only [hk1])
    have h2 : (nK N k : ℤ) = (k : ℤ) - ((⌈N * Real.log (k : ℝ)⌉₊ : ℕ) : ℤ) := by
      unfold nK; rw [Nat.cast_sub hcnk]
    linarith only [h1, h2]
  have hcell := hA y hylat k (nK N k) (by
      refine (hXa n ?_ hXa' y hyA').trans h3n
      linarith only [hLsums.1, hLfa0 La hLa, hLnk (Lfa La) (by linarith only [hLsums.1, hLsum0, hLnum4, hL0r, hN0'])])
    (by linarith only [(hLfa La hLa).1, hLsums.1, hkbig, hLnum4, hL0r, hN0', hLsum0]) hwin (by omega)
  have hkb := hB y hylat k (by
      refine (hXb n ?_ hXb' y hyA').trans h3n
      linarith only [hLsums.2.1, hLnk (Lfa Lb) (by linarith only [hLsums.2.1, hLsum0, hLnum4, hL0r, hN0'])])
    (by linarith only [(hLfa Lb hLb).1, hLsums.2.1, hkbig, hLnum4, hL0r, hN0', hLsum0])
  have hLipn := hLip n (by linarith only [hLsums.2.2, hLnum4, hL0r, hN0', hLsum0, hLn]) hXl'
  exact Homega hnu hε hN0' hy hkl hl5 hkn rfl hcnk hk2 hk1k hσ1 hσσ' hσ'σ hwinN hN1 hN2 hN3
    (hS y hylat k) (hrecell (shiftCube y (k : ℤ)) hWb hWo.measurableSet) hcont hkb hcell hLipn f u hu
    hfin

/-- Witness: the hypotheses are `sharp_scale_inputs` and `sigmaBar_sharp_bounds`; the
statement therefore holds. -/
example [NeZero d] (hd : 2 ≤ d) : ∃ C : ℝ, 1 ≤ C :=
  let ⟨C, _, _, hC, _⟩ := ia_approx d hd (SuperdiffusionCLT.Frozen.Section6.sharp_scale_inputs d hd)
    (SuperdiffusionCLT.Frozen.Section5.sigmaBar_sharp_bounds d hd)
  ⟨C, hC⟩

end SuperdiffusionCLT.Section7
