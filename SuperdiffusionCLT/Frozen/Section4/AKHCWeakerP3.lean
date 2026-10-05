/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.AKHC61.FinalCutoffField
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import SuperdiffusionCLT.Frozen.Section4.ThetaCutoff

@[expose] public section

/-- **[AK, Theorem 6.1] (`t.weaker.P3`) for the infrared cutoff field** (external input),
under (P1) `a.stationarity`, (P2') `a.ellipticity.weaker`,
(P3') `a.CFS.weaker` and (P4) `a.iso`, specialized to the law of the cutoff
field `a_L = ν Id + k_L` of the paper (Section 2) under the
shell law `P`. It is
applied twice in the proof of `p.homog.below`, with the
hypotheses packaged by `l.we.can.apply.hc`.

The print: there are `C(d) < ∞` and `c(d), α(d) ∈ (0,1)` such that, with
`Υ₁ := C K_Ψ^{4d²} / (min{d+1, p_Ψ} - d)` and
`Υ₂ := C / (min{3, p_{Ψ_S}} - 2) · exp(C (L₁ log L₂ + (D + log(H + K_{Ψ_S})) / (1-γ)))`,
for every `m, m₀ ∈ ℕ` with `m ≥ max{m₂, m₃}`, `ω_m² ≤ Υ₁⁻¹` and
`m₀ ≥ C D / ((1-β)(1-γ)²) · log((Υ₁+Υ₂)(m₂ ∨ m₃ + m₀) Θ₀) · log(3 Θ₀)`,
one has, with `κ := min{α, 1-γ}`, for every `n ≥ m + 4m₀`,
`Θ_n - 1 ≤ Υ₁ ω_m² + C 3^{-κ(n-m-4m₀)}`.

Readings this text fixes.

* **Scope and quantifier order.** `C, c, α` depend only on `d`, so they are
  bound first, before `ν`, the law, `L`, and every (P2')/(P3') parameter. The print
  introduces those parameters existentially inside its assumptions and then uses them
  in `Υ₁, Υ₂` and in the conclusion; they are therefore universally quantified binders
  after the constants, each with exactly its printed range.
* **(P1) and (P4) are the shell-law binders `ShellLawPrefix`, `ShellLawJ2`, `ShellLawJ4`.**
  Stationarity of the cutoff law comes from the prefix and J2
  (`restrictionStationaryLaw_cutoffLaw hPrefix hJ2`,
  `Section3/HighContrast/StructuralLaw.lean`). Dihedral symmetry comes from the
  hyperoctahedral half of J4, and the negation symmetry `a ~ a^t` that [AK] uses to
  get `khom = 0` comes from its negation half (`isIsotropicInLawR_cutoffLaw`,
  `isAdjointInvariantInLawR_cutoffLaw`, `sigmaBarStarInvKappaMean_originCube_eq_zero`).
  `J1V2`, `J3` and `J5` are omitted: Theorem 6.1 assumes only (P1)--(P4), and (P2')/(P3') are
  explicit hypotheses here. The cutoff field lies in the class `Ω` of [AK] for every
  sample once `0 < ν`. `ν ≤ 1` is the standing range of the paper, not needed by
  [AK].
* **`Θ_n` is `thetaCutoff nu L P n`**, the value of `e.Theta.n.def` under (P4)
  (see `ThetaCutoff.lean`). `Θ₀` is `thetaCutoff nu L P 0`.
* **`O_Ψ`.** In [AK]: `X ≤ O_Ψ(A)` means `P[X > tA] ≤ 1/Ψ(t)` for every
  `t ≥ 1`. `Homogenization.IndependentSums.IsBigOWith` is exactly this, with the strict
  tail `upperTailEvent X a = {a < X}`, and `IsBigO` is its `|X|` form, the
  `X = O_Ψ(A)` of [AK]. A printed `Y ≤ O_Ψ(A)` on a nonnegative `Y` is written in the
  witness form: a measurable `X` with `IsBigO P Ψ X A` that dominates `Y` at every
  sample. When `Y` is measurable this is equivalent to the print (take `X := Y`).
* **(P2'): the `sup`/`max` is a uniform bound, and `z + cu_k` is a triadic cube.**
  `sup_{k ≤ m} 3^{γ(k-m)} max_z Y_{k,z} ≤ X` says exactly `Y_{k,z} ≤ 3^{-γ(k-m)} X` for
  every `(k, z)`. The pairs `k ∈ ℤ ∩ (-∞, m]`, `z ∈ 3^kℤ^d ∩ cu_m` are the triadic cubes
  `Q` with `Q.scale ≤ m` and centre in `cu_m`, negative scales included.
  This is the reading of `BfAmEllipticity`; no lattice point `3^k j` lies on `∂cu_m`, since
  `3^{m-k}` is odd.
* **(P2'): the positive part is read as a one-sided Loewner bound.** `bfA_L(U)` is
  symmetric: `coarseBlockMatrix` is built from the polarization `coarseBlockEntry`. So
  `S := bfAhom^{-1/2} bfA bfAhom^{-1/2}` is symmetric and `|(S - I)_+| = max(λ_max(S) - 1, 0)`.
  Hence `|(S - I)_+| ≤ t ⟺ 0 ≤ t ∧ bfA ≤ (1+t) bfAhom` in the Loewner order,
  by congruence. This is the one-sided form of the sandwich forms of the formalization
  (clause (ii)), stated with `Homogenization.BlockMatLoewnerLE` and no matrix square root.
  The side condition `0 ≤ t` (here `t = 3^{-γ(k-m)} X ω`) is not written; its omission
  is equivalent. `IsBigO` only sees `|X|`, so `X` may be replaced by `|X|`, and
  `bfAhom ⪰ 0` makes the Loewner bound monotone in `t`.
* **(P3'): the norm is read as the relative bilinear bound.** The averaged
  `|avsum_z bfAhom^{-1/2}(cu_n) bfA(z+cu_n) bfAhom^{-1/2}(cu_n) - I|` equals
  `|A^{-1/2} H A^{-1/2}|`, with `A = bfAhom(cu_n)` and
  `H = avsum_z (bfA(z+cu_n) - A)`. That operator-norm bound is read by the sandwich
  form, clause (i) with `A = B`: `2 p·Hq ≤ t (p·Ap + q·Aq)` for all `p, q`.
  This needs no symmetry of `H`, and it forces `t ≥ 0`. The lattice average is
  `(card)⁻¹ • ∑` over `descendantsAtDepth (originCube d m) (m - n)`, and the difference
  is formed by `ofFullBlockMat (toFullBlockMat · - toFullBlockMat ·)`, as in
  `l.localization.average`. The window `βm < n < m - L₁ log(L₂ n)` forces `n ≥ 1`
  (since `β ≥ 0`) and then `n < m` (since `L₂ n ≥ 1`), so `m - n` is genuine `ℕ`
  subtraction.
* **Renamed bound variables.** The `m` bound inside (P2') and the `m` bound inside
  (P3') are renamed `j`, to keep them apart from the theorem's own `m`.
* **`Ψ_S`, `Ψ`, `ω`.** "`Ψ_S : ℝ₊ → ℝ₊` nondecreasing" is `MonotoneOn` on `Set.Ici 0`
  plus nonnegativity on `Set.Ici 0`. "`Ψ : ℝ₊ → ℝ₊` increasing" is `StrictMonoOn`,
  since the print sets "increasing" against the adjacent "nondecreasing". "Nonincreasing,
  positive, `ω_n → 0`" on all of `ℕ` is `Antitone`,
  pointwise `0 <`, and `Tendsto … atTop (𝓝 0)`. `⌈p⌉` is `Nat.ceil` (`p > 1`), so
  `K^{3⌈p⌉²}` and `K_Ψ^{4d²}` are natural powers. The growth quotients `Ψ(ts)/Ψ(t)`
  are written as real division, which presupposes `Ψ(t) ≠ 0` on `[1,∞)`, as the
  print's quotient does. The notation section's further requirements on `Ψ`
  (values in `[1,∞)`, superlinear growth) are not part of (P2')/(P3') and are
  not added.
* **`Υ₁, Υ₂` are written out at each occurrence** (no `let`, no new definition), with the
  one printed constant `C`. The single `C` serves `Υ₁`, `Υ₂`, the `m₀` bound and the
  remainder term. This loses nothing against independent constants: enlarging `C`
  strengthens both hypotheses and weakens the conclusion. `m₂ ∨ m₃` is `max m2 m3`.
  Every `log` is `Real.log`, and every power with a real exponent is `Real.rpow`.
* **`c(d)`** is printed but occurs in no formula of the statement. It is carried as a
  logically inert existential, for quantifier-list fidelity.
* **The rate reads `κ = min{α, ½(1-γ)}`.** The printed statement and the claim of Step 3 state
  `κ = min{α, 1-γ}`, but the iteration that proves the claim yields `κ = min{α, ½(1-γ)}`.
  Since `α(d)` is chosen before `γ ∈ [0,1)`, the printed proof does not deliver
  the stated rate for `γ` near `1`. The paper applies the theorem with `γ = ½`,
  where either form is a positive constant depending only on `d`.
* **The `m₀` condition carries `C (1 + D)`.** The printed `m₀`
  condition carries the factor `C D`. At `D = 0` the printed
  condition reads `m₀ ≥ 0`, and the printed theorem is then false in the generic
  setting of [AK]: an i.i.d. checkerboard with values `{1, Λ}` satisfies (P1), (P2') with
  `D = 0`, (P3') and (P4), while the conclusion at `m = n = 1`, `m₀ = 0` would force
  `Θ₁ ≤ 2 + C(d)` against `Θ₁ ≥ 4^{-3^d} Λ`. The proof's own `m₀` never vanishes (its
  additive `L₁ + 16D/(1-γ)` term and the `(D+1)` exponent). The paper applies the theorem
  with `D = 1`, where the two forms differ only in the constant.
* **Further corrections of the printed statement.** (a) With `m₂ = m₃ = m₀ = 0` the
  threshold's logarithm would be `Real.log 0 = 0`. (b) The convention of [AK]'s notation
  section that `Ψ, Ψ_S` take values in `[1, ∞)` is part of the statement, so `1 ≤ Ψ t`,
  `1 ≤ Ψ_S t` for `t ≥ 0`; otherwise, with `Ψ = ε t^{d+1}`, the (P3′) clause is vacuous.
  (c) The printed threshold uses `m₂ ∨ m₃` where the proof's `m₀` uses the theorem's own `m`.
  (d) At `L₂ = 1` the printed `L₁ log L₂` removes `L₁` from the threshold. Accordingly `Υ₂`'s
  exponent reads `(L₁ + D/(1-γ))·log(2L₂) + (D + log(H + K_{Ψ_S}))/(1-γ)`, and the `m₀`
  threshold reads
  `C·(L₁ + (1+D)/(1-γ))·(1+D)/((1-β)(1-γ)) · log X · log(3Θ₀·(2 + L₁ log X))` with
  `X = (Υ₁+Υ₂)(m + m₀ + 1)Θ₀`. The `log(2 + L₁ log X)` margin rests on the repair of
  the lag factor dropped in Step 3 (`e.variance.again.prime`).
* **Restricted parameter range.** The constants of the proof cannot be delivered uniformly in
  `γ`, `p_Ψ`, `p_{Ψ_S}`: with
  `λ := min{1-γ, (min{d+1,p_Ψ}-d)/(d+1), (min{3,p_{Ψ_S}}-2)/3}` one needs polynomial factors in
  `λ⁻¹` in the threshold, in `Υ₁` and in the rate, and `Υ₁` needs `K_Ψ^{6(d+1)²}`. The
  statement therefore restricts to the range used in the paper, `γ ≤ 1/2`, `d + 1 ≤ p_Ψ`,
  `3 ≤ p_{Ψ_S}`, where `λ ≥ 1/(d+1)` and every
  `λ`-factor is a constant depending only on `d`, and has `K_Ψ^{6(d+1)²}` in place of
  `K_Ψ^{4d²}` at its four occurrences in `Υ₁`. The paper applies the
  theorem with `γ = 1/2`, `p_Ψ = d + 1`, `p_{Ψ_S} = 2d` (`l.we.can.apply.hc`).
* **The range `β ≤ 1/2`.** The weighted Step-3 recursion
  needs the (P3′) window `β m < k` at its base scale `k`, so its low-scale tail decays at rate
  at most `(1 - 2s′)(1 - β)` (the `β` obstruction of the Step-3 closure); the rate
  `κ = min{α(d), (1-γ)/2}` is fixed before `β ∈ [0,1)`. The statement restricts to `β ≤ 1/2`,
  where the delivered rate is at least a constant depending only on `d`. The paper applies the
  theorem with `β = 1/2`.
-/
theorem SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ L : ℕ,
          -- (P2') `a.ellipticity.weaker`
          ∀ (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ),
            0 ≤ gamma → gamma ≤ 1 / 2 → 1 ≤ H → 0 ≤ D →
            MonotoneOn PsiS (Set.Ici 0) → (∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t) →
            1 ≤ KPsiS → 3 ≤ pPsiS →
            (∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
              s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t)) →
            (∀ j : ℕ, m2 ≤ j →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
                  (H * (j : ℝ) ^ D) ∧
                ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                  (Q : Homogenization.TriadicCube d),
                  Q.scale ≤ (j : ℤ) →
                  Homogenization.cubeCenter Q ∈
                      Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
                    Homogenization.BlockMatLoewnerLE
                      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                            omega L).toCoeffField)
                      ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                            X omega) •
                        SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (j : ℤ))))) →
          -- (P3') `a.CFS.weaker`
          ∀ (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ),
            0 ≤ beta → beta ≤ 1 / 2 → 1 ≤ L1 → 1 ≤ L2 →
            (∀ k : ℕ, 0 < omegaSeq k) → Antitone omegaSeq →
            Filter.Tendsto omegaSeq Filter.atTop (nhds 0) →
            StrictMonoOn Psi (Set.Ici 0) → (∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t) →
            1 ≤ KPsi → (d : ℝ) + 1 ≤ pPsi →
            (∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
              s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t)) →
            (∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
              (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
                ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                  (p q : Homogenization.BlockVec d),
                  2 *
                      (((Homogenization.descendantsAtDepth
                              (Homogenization.originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
                        ∑ R ∈ Homogenization.descendantsAtDepth
                            (Homogenization.originCube d (j : ℤ)) (j - n),
                          Homogenization.blockVecDot p
                            (Homogenization.blockMatVecMul
                              (Homogenization.ofFullBlockMat
                                (Homogenization.toFullBlockMat
                                    (Homogenization.coarseBlockMatrix
                                      (Homogenization.cubeSet R)
                                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                          nu omega L).toCoeffField) -
                                  Homogenization.toFullBlockMat
                                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                      nu L P
                                      (Homogenization.cubeSet
                                        (Homogenization.originCube d (n : ℤ))))))
                              q)) ≤
                    X omega *
                      (Homogenization.blockVecDot p
                          (Homogenization.blockMatVecMul
                            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                              (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                            p) +
                        Homogenization.blockVecDot q
                          (Homogenization.blockMatVecMul
                            (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                              (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))
                            q))) →
          -- the conclusion
          ∀ m m0 : ℕ, max m2 m3 ≤ m →
            omegaSeq m ^ 2 ≤
              (C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)))⁻¹ →
            C * (L1 + (1 + D) / (1 - gamma)) * (1 + D) / ((1 - beta) * (1 - gamma)) *
                Real.log
                  ((C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
                      C / (min 3 pPsiS - 2) *
                        Real.exp (C * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                          (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0) *
                Real.log (3 * SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0 *
                  (2 + L1 * Real.log
                  ((C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) +
                      C / (min 3 pPsiS - 2) *
                        Real.exp (C * ((L1 + D / (1 - gamma)) * Real.log (2 * L2) +
                          (D + Real.log (H + KPsiS)) / (1 - gamma)))) *
                    ((m : ℝ) + (m0 : ℝ) + 1) *
                    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P 0))) ≤
              (m0 : ℝ) →
            ∀ n : ℕ, m + 4 * m0 ≤ n →
              SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P n - 1 ≤
                C * KPsi ^ (6 * (d + 1) ^ 2) / (min ((d : ℝ) + 1) pPsi - (d : ℝ)) *
                    omegaSeq m ^ 2 +
                  C * (3 : ℝ) ^
                    (-(min alpha ((1 - gamma) / 2) * ((n : ℝ) - (m : ℝ) - 4 * (m0 : ℝ))))
    := by
  exact SuperdiffusionCLT.AKHC61.akhc_weakerP3_port d hd
