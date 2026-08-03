import Topping.Riemannian.FrameTrace
import Topping.RicciFlow.Evolution

/-!
# The curvature tensors are pointwise multilinear

`FrameTrace` proves that `tr₁₂` and `|·|²` are frame-independent *for pointwise
multilinear tensors*. That hypothesis is genuine — `CovTensorField I M k` is an
arbitrary map on tuples of vector fields — so the frame results are worth nothing
until something satisfies it. This module supplies the witnesses that matter:

* `isPointwiseMultilinear_riemannTensorField` — `\Rm` as a covariant `4`-tensor
  field;
* `isPointwiseMultilinear_ricciTensorField` — `\Ric` as a covariant `2`-tensor;
* `isPointwiseMultilinear_metricTensorField` — `g` itself.

For `\Rm` the content is `IsAlgCurvatureForm`: `riemannCurvatureAt g p` is
additive and homogeneous in each of its four arguments (`add_left`/`add_two`/…,
`smul_left`/`smul_two`/… of DoCarmo's algebraic curvature form), and it depends
only on the arguments' values at `p` by construction. For `\Ric` it is
`ricciTensorAt`'s being a genuine `→ₗ[ℝ] →ₗ[ℝ] ℝ`, and for `g` it is bilinearity
of `metricInner`.

Consequently `|\Rm|²` and `|\Ric|²` are computed by *any* orthonormal frame and,
via `exists_smooth_frame_normSqAt`, by a smooth local one — the statement the
curvature Bochner identity was blocked on.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### A slot-wise criterion

For a tensor field defined by reading off the arguments' values at `p` and
feeding them to a pointwise function, `IsPointwiseTensorial` is immediate and
multilinearity reduces to slot-wise linearity of that function. The two `Fin`
case splits are packaged once here. -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A tensor field of the form `Y p ↦ f p (Y 0 p) … (Y (k-1) p)` — one
that reads only the values at `p` — is pointwise multilinear as soon as the
underlying pointwise function `b` is linear in each slot. -/
theorem isPointwiseMultilinear_of_pointwise {k : ℕ}
    {A : CovTensorField I M k} {p : M}
    (b : (Fin k → TangentSpace I p) → ℝ)
    (hval : ∀ Y : Fin k → SmoothVectorField I M, A Y p = b (fun i => Y i p))
    (hadd : ∀ (i : Fin k) (v : Fin k → TangentSpace I p) (x y : TangentSpace I p),
      b (Function.update v i (x + y))
        = b (Function.update v i x) + b (Function.update v i y))
    (hsmul : ∀ (i : Fin k) (v : Fin k → TangentSpace I p) (c : ℝ)
      (x : TangentSpace I p),
      b (Function.update v i (c • x)) = c * b (Function.update v i x)) :
    IsPointwiseMultilinear A p := by
  have hpv : ∀ v : Fin k → TangentSpace I p, pointwiseValue A p v = b v := by
    intro v
    rw [pointwiseValue, hval]
    simp
  refine ⟨fun Y Z hYZ => ?_, ?_, ?_⟩
  · rw [hval, hval]
    exact congrArg b (funext hYZ)
  · intro i v x y; rw [hpv, hpv, hpv]; exact hadd i v x y
  · intro i v c x; rw [hpv, hpv]; exact hsmul i v c x

/-! ### The Riemann tensor -/

/-- **Math.** **`\Rm` is pointwise multilinear.** The Riemann tensor as a
covariant `4`-tensor field reads only the arguments' values at `p`, and
`riemannCurvatureAt g p` is additive and homogeneous in each of its four slots —
that is `IsAlgCurvatureForm`'s content (`add_left`/`add_two`/`add_three`/
`add_four` and the four `smul_*`), which `riemannCurvatureAt_isAlg` supplies.

This is the witness the frame results need in order to say anything about
`|\Rm|²`: without it `normSqAt_eq_sum_of_frame` is a theorem about an empty
class. -/
theorem isPointwiseMultilinear_riemannTensorField (g : RiemannianMetric I M)
    (p : M) : IsPointwiseMultilinear (riemannTensorField g) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have halg := riemannCurvatureAt_isAlg g p
  refine isPointwiseMultilinear_of_pointwise
    (fun v => riemannCurvatureAt g p (v 0) (v 1) (v 2) (v 3))
    (fun Y => rfl) ?_ ?_
  · intro i v x y
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num
    · exact halg.add_left _ _ _ _ _
    · exact halg.add_two _ _ _ _ _
    · exact halg.add_three _ _ _ _ _
    · exact halg.add_four _ _ _ _ _
  · intro i v c x
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num
    · exact halg.smul_left _ _ _ _ _
    · exact halg.smul_two _ _ _ _ _
    · exact halg.smul_three _ _ _ _ _
    · exact halg.smul_four _ _ _ _ _

/-! ### The Ricci tensor and the metric -/

/-- **Math.** **`\Ric` is pointwise multilinear**: `ricciTensorAt g p` is by
construction an element of `T_pM →ₗ[ℝ] T_pM →ₗ[ℝ] ℝ`, so both slots are linear,
and `ricciTensorField` reads only the values at `p`. -/
theorem isPointwiseMultilinear_ricciTensorField (g : RiemannianMetric I M)
    (p : M) : IsPointwiseMultilinear (ricciTensorField g) p := by
  classical
  refine isPointwiseMultilinear_of_pointwise
    (fun v => ricciTensorAt g p (v 0) (v 1)) (fun Y => rfl) ?_ ?_
  · intro i v x y
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num
  · intro i v c x
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;> norm_num

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** **The metric is pointwise multilinear**, by bilinearity of
`metricInner`. Needed because `tr₁₂` of `g`-multiples appears throughout the
gravitation-tensor computations. -/
theorem isPointwiseMultilinear_metricTensorField (g : RiemannianMetric I M)
    (p : M) : IsPointwiseMultilinear (metricTensorField g) p := by
  classical
  refine isPointwiseMultilinear_of_pointwise
    (fun v => g.metricInner p (v 0) (v 1)) (fun Y => rfl) ?_ ?_
  · intro i v x y
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;>
      norm_num [g.metricInner_add_left, g.metricInner_add_right]
  · intro i v c x
    fin_cases i <;> simp only [Fin.isValue, Function.update] <;>
      norm_num [g.metricInner_smul_left, g.metricInner_smul_right]

/-! ### The payoff: `|\Rm|²` and `|\Ric|²` over a smooth frame -/

/-- **Math.** **`|\Rm|²` is a finite sum of squares of smooth-frame components
near every point.** Combining the `\Rm` witness with
`exists_smooth_frame_normSqAt`: there are global smooth vector fields
`F₁,…,F_n` and a neighbourhood of `p` on which
`|\Rm|²(q) = Σ_{ijkl} \Rm(F_i,F_j,F_k,F_l)(q)²`.

No per-point basis remains, so the regularity of `|\Rm|²` is that of the
component functions `\Rm(F_i,F_j,F_k,F_l)`. This is the unconditional form of
what the curvature Bochner identity needs. -/
theorem exists_smooth_frame_riemannNormSq (g : RiemannianMetric I M) (p : M) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      ∀ᶠ q in 𝓝 p, normSqAt g (riemannTensorField g) q
        = ∑ v : Fin 4 → Fin (Module.finrank ℝ E),
            riemannTensorField g (fun j => F (v j)) q ^ 2 := by
  obtain ⟨F, hF⟩ := exists_smooth_frame_normSqAt g (riemannTensorField g) p
  exact ⟨F, hF.mono fun q hq =>
    hq (isPointwiseMultilinear_riemannTensorField g q)⟩

/-- **Math.** The same for `|\Ric|²`. -/
theorem exists_smooth_frame_ricciNormSq (g : RiemannianMetric I M) (p : M) :
    ∃ F : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      ∀ᶠ q in 𝓝 p, normSqAt g (ricciTensorField g) q
        = ∑ v : Fin 2 → Fin (Module.finrank ℝ E),
            ricciTensorField g (fun j => F (v j)) q ^ 2 := by
  obtain ⟨F, hF⟩ := exists_smooth_frame_normSqAt g (ricciTensorField g) p
  exact ⟨F, hF.mono fun q hq =>
    hq (isPointwiseMultilinear_ricciTensorField g q)⟩

end Topping

end
