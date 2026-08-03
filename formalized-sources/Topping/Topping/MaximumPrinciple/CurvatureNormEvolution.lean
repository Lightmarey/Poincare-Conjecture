import Topping.MaximumPrinciple.CurvatureNorm
import Topping.MaximumPrinciple.TensorLeibniz
import Topping.MaximumPrinciple.TensorNormAlgebra

/-!
# The evolution inequality for `|Rm|²` (Topping, Proposition 3.2.10)

Topping's Proposition 3.2.10 states that under Ricci flow

`∂_t|\Rm|^2 ≤ Δ|\Rm|^2 - 2|∇\Rm|^2 + C|\Rm|^3`,   `C = C(n)`,

and his proof has exactly two ingredients:

1. differentiating the contraction defining `|\Rm|^2` and substituting the
   curvature evolution equation `∂_t\Rm = Δ\Rm + \Rm*\Rm` gives
   `∂_t|\Rm|^2 ≤ 2⟨\Rm,Δ\Rm⟩ + C|\Rm|^3`;
2. the Bochner-type identity `Δ|\Rm|^2 = 2|∇\Rm|^2 + 2⟨\Rm,Δ\Rm⟩` converts the
   first term.

This module formalizes the proposition and proves it from those two ingredients,
and — the point of the file — it does **not** take the cubic bound `C|\Rm|^3`
on faith. Step 1 is stated in the form the geometry actually delivers,

`∂_t|\Rm|^2 ≤ 2⟨\Rm,Δ\Rm⟩ + 2⟨\Rm, Q⟩`  with  `IsStarProduct g \Rm \Rm Q`,

and the cubic bound is *derived*: Cauchy--Schwarz gives `⟨\Rm,Q⟩ ≤ |\Rm||Q|`,
and `exists_normAt_le_of_isStarProduct` gives `|Q| ≤ K|\Rm|^2`, so the whole
quadratic correction is at most `2K|\Rm|^3`. Both the existence of Topping's
constant and its dependence on `n` alone (through the metric traces inside the
star product) come out of that chain rather than being assumed.

What remains hypothesis, honestly: the two displayed ingredients above. Ingredient
1 is the term-by-term differentiation of the contraction, which needs the
evolution of the metric inside `|·|` as well as of `\Rm`; ingredient 2 is the
Bochner identity. Neither is proved here or anywhere else in the project yet.
So the theorem below is an implication with two named open antecedents, not a
closed statement of 3.2.10.
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

/-! ### `|∇Rm|²` -/

/-- **Math.** `|∇\Rm|^2`, the pointwise square norm of the covariant derivative of
the curvature tensor. `∇\Rm` is the rank-`5` field `covDeriv ∇ \Rm`, whose first
slot is the direction of differentiation in Topping's convention. -/
def gradRiemannNormSqAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  normSqAt g (covDeriv g.leviCivitaConnection (riemannCovTensorField g)) p

omit [I.Boundaryless] in
/-- **Math.** `|∇\Rm|^2 ≥ 0`. -/
theorem gradRiemannNormSqAt_nonneg (g : RiemannianMetric I M) (p : M) :
    0 ≤ gradRiemannNormSqAt g p :=
  normSqAt_nonneg g _ p

/-! ### The two geometric ingredients, as named hypotheses -/

/-- **Math.** Ingredient 1 of Topping's proof: differentiating the contraction
defining `|\Rm|^2` and substituting `∂_t\Rm = Δ\Rm + \Rm*\Rm` bounds the time
derivative by the `Δ\Rm` pairing plus a pairing against *some* star product of
the curvature with itself.

This is stated with the quadratic term still in star-product form, `Q`, rather
than as an unexplained `C|\Rm|^3`: that is what lets the constant be derived
below instead of assumed. `Q` is allowed to depend on `t`, matching
`HasCurvatureEvolutionOn`, where the star product is existentially quantified at
each time. -/
def HasCurvatureNormSqPairingBoundOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    Prop :=
  ∀ t ∈ J, ∃ Q : CovTensorField I M 4,
    IsStarProduct (g t) (riemannCovTensorField (g t))
        (riemannCovTensorField (g t)) Q ∧
      ∀ p : M,
        derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
          2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
              (roughLaplacian (g t) (g t).leviCivitaConnection
                (riemannCovTensorField (g t))) p
            + 2 * tensorInnerAt (g t) (riemannCovTensorField (g t)) Q p

/-- **Math.** Ingredient 2: the Bochner-type identity
`Δ|\Rm|^2 = 2|∇\Rm|^2 + 2⟨\Rm,Δ\Rm⟩`, which holds for the connection Laplacian of
the square norm of any parallel-compatible tensor field.

**Progress toward proving it, rather than assuming it.** The *first*
differentiation is now available: `Topping.dir_riemannNormAt_sq`
(`MaximumPrinciple/TensorLeibniz.lean`) proves
`X(|\Rm|^2) = 2⟨∇_X\Rm,\Rm⟩` from the Leibniz rule for the metric pairing, whose
cross terms cancel against the antisymmetry of a local orthonormal frame's
connection coefficients. That removes the obstruction caused by `normSqAt`
contracting against a per-point basis, which is why this definition
could not previously be attacked at all.

It is *not* the identity. Two steps remain: the second differentiation, and
commuting the metric trace past `∇` (where `roughLaplacian`'s `traceFirstTwo`, and
its own per-point `extendVector`, return). So this stays a hypothesis, and
`dir_riemannNormAt_sq` carries one open antecedent of its own —
`IsPointwiseMultilinear (covDerivAlong ∇ X \Rm)`. -/
def HasCurvatureBochnerIdentityOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    Prop :=
  ∀ t ∈ J, ∀ p : M,
    metricLaplacianAt (g t) (fun q => riemannNormAt (g t) q ^ 2) p =
      2 * gradRiemannNormSqAt (g t) p
        + 2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
            (roughLaplacian (g t) (g t).leviCivitaConnection
              (riemannCovTensorField (g t))) p

/-! ### The proposition -/

/-- **Math.** The conclusion of Topping's Proposition 3.2.10 on the time set `J`,
with the constant made explicit:
`∂_t|\Rm|^2 ≤ Δ|\Rm|^2 - 2|∇\Rm|^2 + c|\Rm|^3`. -/
def HasCurvatureNormEvolutionInequalityOn (g : ℝ → RiemannianMetric I M) (c : ℝ)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
      metricLaplacianAt (g t) (fun q => riemannNormAt (g t) q ^ 2) p
        - 2 * gradRiemannNormSqAt (g t) p
        + c * riemannNormAt (g t) p ^ 3

omit [I.Boundaryless] in
/-- **Math.** **Topping, Proposition 3.2.10, at a single time.** From the two
geometric ingredients at time `t`, the evolution inequality holds at `t` with a
constant `c ≥ 0` obtained from the star product.

The derivation of the constant is the content: writing `Q` for the quadratic
term, Cauchy--Schwarz gives `⟨\Rm,Q⟩ ≤ |\Rm||Q|`, the star bound gives
`|Q| ≤ K|\Rm|^2`, and therefore `2⟨\Rm,Q⟩ ≤ 2K|\Rm|^3`. Substituting the Bochner
identity for `2⟨\Rm,Δ\Rm⟩` turns ingredient 1 into the statement. -/
theorem exists_curvatureNormEvolution_const_of_ingredients
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {t : ℝ} (ht : t ∈ J)
    (hpair : HasCurvatureNormSqPairingBoundOn g J)
    (hboch : HasCurvatureBochnerIdentityOn g J) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p : M,
      derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
        metricLaplacianAt (g t) (fun q => riemannNormAt (g t) q ^ 2) p
          - 2 * gradRiemannNormSqAt (g t) p
          + c * riemannNormAt (g t) p ^ 3 := by
  obtain ⟨Q, hQstar, hQbound⟩ := hpair t ht
  obtain ⟨K, hK, hKbound⟩ := exists_normAt_le_of_isStarProduct hQstar
  refine ⟨2 * K, by linarith, fun p => ?_⟩
  -- the star product is at most `K |Rm| ^ 2` in norm
  have hnorm : normAt (g t) Q p ≤ K * riemannNormAt (g t) p ^ 2 := by
    have h := hKbound p
    rw [riemannNormAt]
    calc normAt (g t) Q p
        ≤ K * normAt (g t) (riemannCovTensorField (g t)) p *
            normAt (g t) (riemannCovTensorField (g t)) p := h
      _ = K * normAt (g t) (riemannCovTensorField (g t)) p ^ 2 := by ring
  -- Cauchy-Schwarz turns the pairing into the cubic term
  have hcs : tensorInnerAt (g t) (riemannCovTensorField (g t)) Q p ≤
      K * riemannNormAt (g t) p ^ 3 := by
    have hRnn : 0 ≤ riemannNormAt (g t) p := riemannNormAt_nonneg (g t) p
    calc tensorInnerAt (g t) (riemannCovTensorField (g t)) Q p
        ≤ normAt (g t) (riemannCovTensorField (g t)) p * normAt (g t) Q p :=
          tensorInnerAt_le (g t) _ _ p
      _ = riemannNormAt (g t) p * normAt (g t) Q p := by rw [riemannNormAt]
      _ ≤ riemannNormAt (g t) p * (K * riemannNormAt (g t) p ^ 2) :=
          mul_le_mul_of_nonneg_left hnorm hRnn
      _ = K * riemannNormAt (g t) p ^ 3 := by ring
  have hbochp := hboch t ht p
  have hpairp := hQbound p
  rw [hbochp]
  linarith

/-! ### Feeding Theorem 3.2.11

The bound Theorem 3.2.11 actually consumes is the *weakened* one, with the
favourable `-2|∇\Rm|^2` discarded. That is the book's own step ("after weakening
the resulting estimate"), and it is a one-line consequence since `|∇\Rm|^2 ≥ 0`. -/

set_option linter.unusedSectionVars false in
/-- **Math.** Discarding the good gradient term turns Proposition 3.2.10 into the
hypothesis of Theorem 3.2.11: `∂_t|\Rm|^2 ≤ Δ|\Rm|^2 + c|\Rm|^3`. This is the
weakening the book performs before applying the maximum principle, and it is
valid because `|∇\Rm|^2 ≥ 0`. -/
theorem hasCurvatureNormSqInequalityOn_of_evolutionInequality
    [CompactSpace M] {g : ℝ → RiemannianMetric I M} {c : ℝ} {J : Set ℝ}
    (h : HasCurvatureNormEvolutionInequalityOn g c J) :
    HasCurvatureNormSqInequalityOn g c J := by
  intro t ht p
  have hgrad : 0 ≤ gradRiemannNormSqAt (g t) p :=
    gradRiemannNormSqAt_nonneg (g t) p
  have := h t ht p
  linarith

end Topping

end
