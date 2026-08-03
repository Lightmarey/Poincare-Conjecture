import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth
import Topping.Riemannian.VariationScalar

/-!
# The scalar-evolution bridge, with its smoothness hypothesis discharged

`hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn` derives Topping's
`∂_tR = ΔR + 2|\Ric|^2` from his first-variation formula 2.3.9 under the
substitution `h = -2\Ric`. It carried one side condition beyond the variation
formula itself: smoothness of the scalar curvature at each fixed time, needed to
pull the constant `-2` through the Laplacian.

That condition is now a theorem, not a hypothesis.
`MorganTianLib.scalarCurvatureAt_leviCivita_contMDiff` proves the
spatial smoothness of the scalar curvature for the canonical Levi-Civita
connection, and Topping's scalar curvature is that one across
`scalarCurvatureAt_eq_scalarCurvatureAt`. So the bridge below needs *only* the
variation formula.

Morgan--Tian supplies the spatial-smoothness analysis, while Topping Chapter 2
supplies the algebra of the substitution.
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

/-- **Math.** Topping's scalar curvature is smooth in the base point. This is
Morgan--Tian's spatial-smoothness theorem transported across the bridge identifying
Topping's scalar curvature with the Morgan--Tian one. -/
theorem scalarCurvatureAt_contMDiff (g : RiemannianMetric I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => scalarCurvatureAt g q) := by
  have hfun : (fun q => scalarCurvatureAt g q)
      = MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection
          (isLeviCivita_leviCivitaConnection g) :=
    funext fun q => scalarCurvatureAt_eq_scalarCurvatureAt g q
  rw [hfun]
  exact MorganTianLib.scalarCurvatureAt_leviCivita_contMDiff g

/-- **Math.** **Topping 2.5.4 from Topping 2.3.9, unconditionally.** If the family
`g` obeys the first-variation formula in the direction `h = -2\Ric`, then it
satisfies `∂_tR = ΔR + 2|\Ric|^2`. No smoothness side condition: the spatial
smoothness of the scalar curvature is now proved rather than assumed.

The variation formula is the only remaining antecedent under the whole scalar side
of the chapter, which is where the analytic work genuinely lives. -/
theorem hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn'
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hvar : HasScalarVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) J) :
    HasScalarCurvatureEvolutionOn g J :=
  hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn hvar
    (fun t => scalarCurvatureAt_contMDiff (g t))

end Topping

end
