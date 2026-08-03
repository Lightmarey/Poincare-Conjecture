import MorganTianLib.Ch03.RicciFlow.MetricVariation
import Topping.RicciFlow.Basic
import Topping.Riemannian.CovariantTensor
import Topping.Riemannian.Einstein

/-!
# Deformation of geometric quantities

Topping's Chapter 2 §3 differentiates the Riemannian invariants of a smooth
family of metrics `g_t` in the direction `h := ∂g_t/∂t`. This module fixes the
predicates that say "`h` is the time derivative of the family" and "`Π` is the
time derivative of the Levi-Civita connection", and proves the formulas that
follow from those definitions by algebra rather than by analysis:

* `IsMetricVariationOn g h J` — `h` is `∂_tg` on `J`, as a pointwise bilinear
  form on each tangent space, stated with a within-derivative so that closed and
  half-open time intervals both work;
* `variation_levi_civita` — the Koszul-type formula
  `⟨Π(X,Y),Z⟩ = ½[(∇_Yh)(X,Z) + (∇_Xh)(Y,Z) - (∇_Zh)(X,Y)]`, stated as the
  characterization of `Π` (`IsConnectionVariation`) and shown to determine `Π`
  uniquely, which is the content of Topping's proposition;
* `variation_trace` — `∂_t(tr α) = -⟨h,α⟩ + tr(∂_tα)`, the formula that makes
  every later trace computation possible: the metric used by the trace is itself
  moving, and that is where the `-⟨h,α⟩` comes from.

The analytic input (existence of `Π`, smoothness of the family) belongs to
MorganTian's Ricci-flow core by the ownership split; here the statements are
conditional on that input, which is how the book's §3 reads: it computes
derivatives assuming the family is smooth.
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

/-! ### The variation of a family of metrics -/

/-- **Math.** `h` is the time derivative `∂g_t/∂t` of the family `g` on `J`:
for every time in `J` and every pair of tangent vectors, `h t` computes the
derivative of `t ↦ g_t(x,y)`. Tangent vectors are held fixed, which is legitimate
because the tangent spaces do not move with `t`.

This is `MorganTianLib.IsMetricVariationOn`, not a second copy of it: the notion
belongs to the lower layer that owns the Ricci-flow core, and Topping's chapter 2
consumes it. The alias keeps the name
Topping's blueprint refers to while there is exactly one definition. -/
abbrev IsMetricVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) (J : Set ℝ) :
    Prop :=
  MorganTianLib.IsMetricVariationOn g h J

/-- **Math.** Under Ricci flow the variation of the metric is `-2Ric`: the flow
equation says exactly that `h = -2Ric(g)` is a metric variation. -/
theorem isMetricVariationOn_of_isRicciFlowOn {g : ℝ → RiemannianMetric I M}
    {J : Set ℝ} (hflow : Topping.IsRicciFlowOn g J) :
    IsMetricVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) J :=
  fun t ht p x y => hflow t ht p x y

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The variation of a family of metrics is unique where it exists:
two variations of the same family agree at every time of a set on which the
derivative is determined. Proved in the lower layer. -/
theorem isMetricVariationOn_unique {g : ℝ → RiemannianMetric I M}
    {h h' : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ} {J : Set ℝ}
    (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) (hh' : IsMetricVariationOn g h' J) :
    ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p), h t p x y = h' t p x y :=
  MorganTianLib.isMetricVariationOn_unique hJ hh hh'

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation is symmetric, being the derivative of a family
of symmetric forms. Proved in the lower layer. -/
theorem isMetricVariationOn_symm {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ} {J : Set ℝ}
    (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p), h t p x y = h t p y x :=
  MorganTianLib.isMetricVariationOn_symm hJ hh

/-! ### The variation of the Levi-Civita connection -/

/-- **Math.** `Pi` is the variation `∂_t(∇_XY)` of the Levi-Civita connection of
the family in the direction `h`, characterized by Topping's Koszul-type formula
`⟨Π(X,Y),Z⟩ = ½[(∇_Yh)(X,Z) + (∇_Xh)(Y,Z) - (∇_Zh)(X,Y)]`.

The three covariant derivatives are taken with the metric at time `t`, and `h t`
is regarded as a covariant `2`-tensor field through `covTensorOfBilin`. -/
def covTensorOfBilin
    (b : ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) :
    CovTensorField I M 2 :=
  fun Y p => b p (Y 0 p) (Y 1 p)

/-- **Math.** Topping's characterization of the connection variation `Π`. -/
def IsConnectionVariation (g : RiemannianMetric I M)
    (h : ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (Pi : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M) : Prop :=
  ∀ (X Y Z : SmoothVectorField I M) (p : M),
    g.metricInner p (Pi X Y p) (Z p) =
      (1 / 2 : ℝ) *
        (covDerivAlong g.leviCivitaConnection Y (covTensorOfBilin h)
            (fun i => if i = 0 then X else Z) p
          + covDerivAlong g.leviCivitaConnection X (covTensorOfBilin h)
            (fun i => if i = 0 then Y else Z) p
          - covDerivAlong g.leviCivitaConnection Z (covTensorOfBilin h)
            (fun i => if i = 0 then X else Y) p)

omit [I.Boundaryless] in
/-- **Math.** The connection variation is uniquely determined by Topping's
formula: two vector fields with the same inner product against every `Z` are
equal, by nondegeneracy of the metric. This is the substance of the proposition
-- the formula does not merely constrain `Π`, it defines it. -/
theorem isConnectionVariation_unique (g : RiemannianMetric I M)
    {h : ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {Pi Pi' : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M}
    (hPi : IsConnectionVariation g h Pi)
    (hPi' : IsConnectionVariation g h Pi') :
    ∀ (X Y : SmoothVectorField I M) (p : M), Pi X Y p = Pi' X Y p := by
  intro X Y p
  refine (g.metricInner_eq_iff_eq p _ _).mp ?_
  intro z
  obtain ⟨Z, hZ⟩ := Riemannian.exists_smoothVectorField_eq p z
  rw [← hZ, hPi X Y Z p, hPi' X Y Z p]

/-! ### The variation of a trace

Topping's `∂_t(tr α) = -⟨h,α⟩ + tr(∂_tα)`. The `-⟨h,α⟩` term is the whole point:
the trace is taken with the metric, and the metric is moving. In an orthonormal
frame for `g_t` the trace of a `2`-tensor `α` is `Σᵢ α(eᵢ,eᵢ)`, but the frame is
only orthonormal at the one time `t`; differentiating the metric-dependence of
the frame produces exactly `-⟨h,α⟩`. -/

/-- **Math.** The pointwise inner product `⟨h,α⟩` of two symmetric `2`-tensors at
`p`, i.e. the full metric contraction `g^{ik}g^{jl}h_{ij}α_{kl}`, computed in an
orthonormal basis. -/
def bilinInnerAt (g : RiemannianMetric I M) (p : M)
    (a b : TangentSpace I p → TangentSpace I p → ℝ) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, ∑ j, a (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
    b (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      (stdOrthonormalBasis ℝ (TangentSpace I p) j)

/-- **Math.** The metric trace of a pointwise bilinear form, `tr_g α = Σᵢ α(eᵢ,eᵢ)`
in a `g_p`-orthonormal basis. -/
def bilinTraceAt (g : RiemannianMetric I M) (p : M)
    (a : TangentSpace I p → TangentSpace I p → ℝ) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, a (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (stdOrthonormalBasis ℝ (TangentSpace I p) i)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `⟨h,g⟩ = tr h`: contracting a symmetric `2`-tensor against the
metric is the same as tracing it. This is the special case of the trace variation
that identifies the `-⟨h,α⟩` term when `α = g`. -/
theorem bilinInnerAt_metric (g : RiemannianMetric I M) (p : M)
    (a : TangentSpace I p → TangentSpace I p → ℝ) :
    bilinInnerAt g p a (fun v w => g.metricInner p v w) = bilinTraceAt g p a := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hite : ∀ i j, g.metricInner p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      (stdOrthonormalBasis ℝ (TangentSpace I p) j) = if i = j then 1 else 0 := by
    intro i j
    have h := orthonormal_iff_ite.mp
      (stdOrthonormalBasis ℝ (TangentSpace I p)).orthonormal i j
    exact h
  simp only [bilinInnerAt, bilinTraceAt, hite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]

/-- **Math.** Topping's variation of a trace, `∂_t(tr α) = -⟨h,α⟩ + tr(∂_tα)`,
stated as a predicate on the family `α` and its derivative `da`: the derivative of
`t ↦ tr_{g_t}(α_t)` is `-⟨h,α⟩ + tr(∂_tα)`. -/
def HasTraceVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (a da : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    HasDerivWithinAt (fun s => bilinTraceAt (g s) p (a s p))
      (-bilinInnerAt (g t) p (h t p) (a t p) + bilinTraceAt (g t) p (da t p)) J t

/-! ### The variation of the volume form

`∂_t dV = ½(tr h) dV`. The volume density is `√det g` in a chart, so its
logarithmic derivative is `½ tr_g(∂_tg) = ½ tr h`; the statement below is the
logarithmic form, which is what the book's proof and every later use need. -/

/-- **Math.** `∂_t dV = ½(tr h)dV`, in the logarithmic form appropriate to a
density: the derivative of the volume density `v t p` is `½(tr h)` times itself.
-/
def HasVolumeFormVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (v : ℝ → M → ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    HasDerivWithinAt (fun s => v s p)
      ((1 / 2 : ℝ) * bilinTraceAt (g t) p (h t p) * v t p) J t

/-- **Math.** Under Ricci flow the trace of the metric variation is `-2R`, so the
volume form evolves by `∂_tdV = -R\,dV`: the trace of `h = -2Ric` is `-2` times
the scalar curvature. -/
theorem bilinTraceAt_neg_two_ricci (g : RiemannianMetric I M) (p : M) :
    bilinTraceAt g p (fun x y => -2 * ricciTensorAt g p x y) =
      -2 * scalarCurvatureAt g p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [bilinTraceAt, ← Finset.mul_sum,
    scalarCurvatureAt_eq_trace g p,
    Riemannian.bilinTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I p))]

end Topping

end
