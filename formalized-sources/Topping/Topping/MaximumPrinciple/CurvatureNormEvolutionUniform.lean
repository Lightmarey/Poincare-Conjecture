import Topping.MaximumPrinciple.CurvatureStarBound
import Topping.RicciFlow.CurvatureStarUniform

/-!
# Proposition 3.2.10 with Topping's `C = C(n)`, on a whole time interval

`exists_curvatureNormEvolution_const_of_ingredients` proves Topping's
Proposition 3.2.10 **at a single time**, and that restriction was not cosmetic:
its constant came from `exists_normAt_le_of_isStarProduct`, whose induction runs
over a derivation of `IsStarProduct g \Rm \Rm Q` and therefore produces a `K`
inside the scope of `g`. At a family `g t` that is `K(t)`, so the conclusion could
not be quantified over `t` with one constant — and `HasCurvatureNormEvolutionInequalityOn g c J`,
the shape Theorem 3.2.11 consumes, needs exactly that.

`exists_uniform_normAt_curvatureEvolutionCorrection_le` closes the gap:
the correction of Topping 2.5.1 is a *fixed* shape (eight double contractions of
permutations of `\Rm ⊗ \Rm`), so its bound is read off the shape rather than
extracted from a derivation, and the constant — one may take `12n` — is bound
outside `g`. This module spends that:

* the pairing ingredient is restated with the **named** correction
  `curvatureEvolutionCorrection` in place of the existentially quantified star
  product (`HasCurvatureNormSqNamedPairingBoundOn`), which is what makes a
  `g`-uniform bound applicable;
* `exists_uniform_curvatureNormEvolution_const` then gives
  `∃ c, 0 ≤ c ∧ ∀ g J, ingredients → HasCurvatureNormEvolutionInequalityOn g c J`,
  with `c` bound before the family, the interval, the time and the point. That
  quantifier order is what "there is `C = C(n)`" asserts;
* and `exists_uniform_riemannNormAt_le_of_ingredients` chains it through
  Theorem 3.2.11, so `|\Rm| ≤ M/(1 - ½CMt)` now follows from the two geometric
  ingredients with a single dimension-only `C`.

**Still hypothesis.** The two ingredients themselves: the differentiated
contraction (ingredient 1, now in named form) and the Bochner identity
`Δ|\Rm|^2 = 2|∇\Rm|^2 + 2⟨\Rm,Δ\Rm⟩` (ingredient 2). Neither is proved anywhere in
the project. So 3.2.10 and 3.2.11 remain implications from named open antecedents;
what changed here is that the constant no longer secretly depends on `t`.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The pairing against the actual correction, and its `g`-uniform bound -/

set_option linter.unusedSectionVars false in
/-- **Math.** **The pairing of `\Rm` against the curvature-evolution correction is
at most `C(n)|\Rm|^3`, with `C(n)` uniform in the metric.**

This is Cauchy--Schwarz on top of the uniform norm bound for
`curvatureEvolutionCorrection`. The binder order is the content: `K` is bound
before `g`, so a time-dependent family gets the *same* constant at every time —
unlike `exists_tensorInner_curvatureEvolutionCorrection_le`, whose constant is
per-metric because it comes from a star-product derivation. -/
theorem exists_uniform_tensorInner_curvatureEvolutionCorrection_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : RiemannianMetric I M) (p : M),
      tensorInnerAt g (riemannCovTensorField g)
          (curvatureEvolutionCorrection g) p ≤
        K * riemannNormAt g p ^ 3 := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_normAt_curvatureEvolutionCorrection_le (I := I) (M := M)
  refine ⟨K, hK, fun g p => ?_⟩
  have hRnn : 0 ≤ riemannNormAt g p := riemannNormAt_nonneg g p
  have hnorm : normAt g (curvatureEvolutionCorrection g) p ≤
      K * riemannNormAt g p ^ 2 := by
    have h := hbound g p
    rwa [← riemannNormAt_eq_normAt_riemannTensorField] at h
  calc tensorInnerAt g (riemannCovTensorField g)
        (curvatureEvolutionCorrection g) p
      ≤ normAt g (riemannCovTensorField g) p *
          normAt g (curvatureEvolutionCorrection g) p :=
        tensorInnerAt_le g _ _ p
    _ = riemannNormAt g p * normAt g (curvatureEvolutionCorrection g) p := by
        rw [riemannNormAt]
    _ ≤ riemannNormAt g p * (K * riemannNormAt g p ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm hRnn
    _ = K * riemannNormAt g p ^ 3 := by ring

/-- **Math.** Ingredient 1 of Topping's Proposition 3.2.10 with the quadratic term
**named**: differentiating the contraction defining `|\Rm|^2` and substituting the
component form of `∂_t\Rm = Δ\Rm + \Rm*\Rm` bounds the time derivative by the
`Δ\Rm` pairing plus the pairing against `curvatureEvolutionCorrection`, the actual
correction of Topping 2.5.1.

The difference from `HasCurvatureNormSqPairingBoundOn` is that the star product is
not existentially quantified: it is the one tensor the evolution equation has. That
is what makes the `g`-uniform bound applicable, and hence what makes the resulting
constant independent of `t`. -/
def HasCurvatureNormSqNamedPairingBoundOn (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
      2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
          (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannCovTensorField (g t))) p
        + 2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
            (curvatureEvolutionCorrection (g t)) p

set_option linter.unusedSectionVars false in
/-- **Math.** The named ingredient is stronger than the existential one: the
correction of Topping 2.5.1 *is* an `\Rm*\Rm`, by
`isStarProduct_curvatureEvolutionCorrection`. So nothing is lost by working with
the named form. -/
theorem hasCurvatureNormSqPairingBoundOn_of_named
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (h : HasCurvatureNormSqNamedPairingBoundOn g J) :
    HasCurvatureNormSqPairingBoundOn g J := by
  intro t ht
  refine ⟨curvatureEvolutionCorrection (g t), ?_, h t ht⟩
  have hstar := isStarProduct_curvatureEvolutionCorrection (g t)
  rwa [← riemannCovTensorField_eq_riemannTensorField] at hstar

/-! ### Proposition 3.2.10 on an interval, with one constant -/

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Proposition 3.2.10, with `C = C(n)`.** There is a constant
depending only on the dimension such that, for *every* family of metrics and
*every* time set, the two geometric ingredients imply

`∂_t|\Rm|^2 ≤ Δ|\Rm|^2 - 2|∇\Rm|^2 + C|\Rm|^3`

at every time of the set and every point.

The quantifier order is the whole point: `c` is bound before `g`, before `J`,
before `t` and before `p`, which is what the book's `C = C(n)` asserts. The
single-time version `exists_curvatureNormEvolution_const_of_ingredients` cannot be
strengthened this way, since its constant is extracted from an `IsStarProduct`
derivation mentioning the metric. -/
theorem exists_uniform_curvatureNormEvolution_const :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℝ → RiemannianMetric I M) (J : Set ℝ),
      HasCurvatureNormSqNamedPairingBoundOn g J →
      HasCurvatureBochnerIdentityOn g J →
      HasCurvatureNormEvolutionInequalityOn g c J := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_tensorInner_curvatureEvolutionCorrection_le (I := I) (M := M)
  refine ⟨2 * K, by linarith, fun g J hpair hboch t ht p => ?_⟩
  have hcs := hbound (g t) p
  have hbochp := hboch t ht p
  have hpairp := hpair t ht p
  rw [hbochp]
  linarith

/-! ### Theorem 3.2.11 with one dimension-only constant

The `|\Rm|` bound consumes the *weakened* inequality (the favourable `-2|∇\Rm|^2`
discarded), so the constant carries through unchanged. Chaining gives Topping's
Theorem 3.2.11 with a `C` fixed before the flow. -/

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Theorem 3.2.11, with `C = C(n)`.** There is a constant
depending only on the dimension such that for every family of metrics on a closed
manifold satisfying the two ingredients of Proposition 3.2.10, and with
`|\Rm| ≤ m` at `t = 0`,

`|\Rm| ≤ m / (1 - ½Cmt)`

on any interval `[0,T]` on which the denominator stays positive.

Two honest caveats, both inherited rather than introduced here.

* `hdenom` is unremovable, not merely unproved: past `t = 2/(Cm)` the right-hand
  side is negative while `|\Rm| ≥ 0`, so the book's displayed statement is false
  there and the maximal-time argument that removes the analogous hypothesis for
  the *lower* scalar barrier does not apply to an *upper* one.
* `hm : 0 < m` excludes the book's `m = 0`.

What is new is that `c` is bound before `g`, `m` and `T`, so the constant in the
conclusion is Topping's `C(n)` and not a `C(n, g)`. -/
theorem exists_uniform_riemannNormAt_le_of_ingredients [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℝ → RiemannianMetric I M) (m T : ℝ),
      0 ≤ T → 0 < m →
      ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
        ((Set.univ : Set M) ×ˢ Icc 0 T) →
      (∀ t ∈ Icc 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => riemannNormAt (g t) x ^ 2) →
      (∀ x t, t ∈ Icc 0 T →
        HasDerivWithinAt (fun s => riemannNormAt (g s) x ^ 2)
          (derivWithin (fun s => riemannNormAt (g s) x ^ 2) (Icc 0 T) t)
          (Icc 0 T) t) →
      HasCurvatureNormSqNamedPairingBoundOn g (Icc 0 T) →
      HasCurvatureBochnerIdentityOn g (Icc 0 T) →
      (∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2) →
      (∀ p, riemannNormAt (g 0) p ≤ m) →
      ∀ p t, t ∈ Icc 0 T →
        riemannNormAt (g t) p ≤ m / (1 - c * m * t / 2) := by
  obtain ⟨c, hc, hprop⟩ :=
    exists_uniform_curvatureNormEvolution_const (I := I) (M := M)
  refine ⟨c, hc, fun g m T hT hm hcont hspace hderiv hpair hboch hdenom hzero => ?_⟩
  exact riemannNormAt_le hT hc hm hcont hspace hderiv
    (hasCurvatureNormSqInequalityOn_of_evolutionInequality
      (hprop g (Icc 0 T) hpair hboch))
    hdenom hzero

end Topping

end
