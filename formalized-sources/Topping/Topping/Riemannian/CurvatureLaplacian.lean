import Topping.RicciFlow.Evolution
import Topping.Riemannian.TensorNorm
import Topping.Riemannian.VariationCurvature

/-!
# The rough Laplacian of the curvature tensor

Topping's Chapter 2 §4 computes `Δ\Rm` in terms of second covariant derivatives
of the Ricci tensor, curvature-Ricci contractions, and the tensor `B`
(Topping p. 41):
`B(X,Y,W,Z) = ⟨\Rm(X,\cdot,Y,\cdot),\Rm(W,\cdot,Z,\cdot)⟩`,
the pairing of two curvature slices, which is the quadratic curvature expression
appearing in both the Laplacian formula and the curvature evolution equation.

`B` has some but not all of the symmetries of `\Rm`:
`B(X,Y,W,Z) = B(W,Z,X,Y) = B(Y,X,Z,W)`, both proved below.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Topping's tensor `B(X,Y,W,Z) = ⟨\Rm(X,·,Y,·),\Rm(W,·,Z,·)⟩`
(Topping p. 41): the metric pairing of two slices of the curvature tensor,
computed as the double sum over an orthonormal basis. -/
def curvatureB (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, ∑ j,
    riemannCurvatureAt g p x (stdOrthonormalBasis ℝ (TangentSpace I p) i) y
        (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
      riemannCurvatureAt g p w (stdOrthonormalBasis ℝ (TangentSpace I p) i) z
        (stdOrthonormalBasis ℝ (TangentSpace I p) j)

omit [I.Boundaryless] in
/-- **Math.** `B(X,Y,W,Z) = B(W,Z,X,Y)`: the pairing is symmetric in its two
curvature slices. -/
theorem curvatureB_swap_pairs (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    curvatureB g p x y w z = curvatureB g p w z x y := by
  simp only [curvatureB]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    mul_comm _ _

/-- **Math.** `B(X,Y,W,Z) = B(Y,X,Z,W)`: swapping the two entries within each
slice is a symmetry, because each factor picks up the pair-swap symmetry of the
curvature tensor followed by relabelling the two summation indices. -/
theorem curvatureB_swap_within (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    curvatureB g p x y w z = curvatureB g p y x z w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have halg := riemannCurvatureAt_isAlg g p
  -- Pair-swap symmetry `Rm(a,b,c,d) = Rm(c,d,a,b)` turns each factor
  -- `Rm(x,eᵢ,y,eⱼ)` into `Rm(y,eⱼ,x,eᵢ)`; then exchange the names of `i` and `j`.
  have hswap : ∀ (a b c d : TangentSpace I p),
      riemannCurvatureAt g p a b c d = riemannCurvatureAt g p c d a b :=
    fun a b c d => halg.pairSwap a b c d
  simp only [curvatureB]
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ (TangentSpace I p)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hswap x (stdOrthonormalBasis ℝ (TangentSpace I p) j) y
      (stdOrthonormalBasis ℝ (TangentSpace I p) i),
    hswap w (stdOrthonormalBasis ℝ (TangentSpace I p) j) z
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)]

/-- **Math.** Topping's formula for the rough Laplacian of the curvature tensor,
`(Δ\Rm)(X,Y,W,Z) = -∇²_{Y,W}\Ric(X,Z) + ∇²_{X,W}\Ric(Y,Z) - ∇²_{X,Z}\Ric(Y,W)
+ ∇²_{Y,Z}\Ric(X,W) - \Ric(R(W,Z)Y,X) + \Ric(R(W,Z)X,Y)
- 2(B(X,Y,W,Z) - B(X,Y,Z,W) + B(X,W,Y,Z) - B(X,Z,Y,W))`.

The `∇²\Ric` terms use `secondCovDerivAlong` on the Ricci `2`-tensor field, and the
two `\Ric`-of-curvature terms feed the curvature operator into `\Ric`. -/
def HasCurvatureLaplacianFormula (g : RiemannianMetric I M) : Prop :=
  ∀ (X Y W Z : SmoothVectorField I M) (p : M),
    roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
        (fun i => if i = 0 then X else if i = 1 then Y else
          if i = 2 then W else Z) p =
      -secondCovDerivAlong g.leviCivitaConnection Y W (ricciTensorField g)
          (fun i => if i = 0 then X else Z) p
        + secondCovDerivAlong g.leviCivitaConnection X W (ricciTensorField g)
          (fun i => if i = 0 then Y else Z) p
        - secondCovDerivAlong g.leviCivitaConnection X Z (ricciTensorField g)
          (fun i => if i = 0 then Y else W) p
        + secondCovDerivAlong g.leviCivitaConnection Y Z (ricciTensorField g)
          (fun i => if i = 0 then X else W) p
        - ricciTensorAt g p (curvatureOperator g W Z Y p) (X p)
        + ricciTensorAt g p (curvatureOperator g W Z X p) (Y p)
        - 2 * (curvatureB g p (X p) (Y p) (W p) (Z p)
            - curvatureB g p (X p) (Y p) (Z p) (W p)
            + curvatureB g p (X p) (W p) (Y p) (Z p)
            - curvatureB g p (X p) (Z p) (Y p) (W p))

end Topping

end
