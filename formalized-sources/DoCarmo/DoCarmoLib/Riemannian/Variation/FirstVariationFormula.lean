import DoCarmoLib.Riemannian.Variation.EnergyFirstDeriv
import DoCarmoLib.Riemannian.Variation.SegmentAssembly

/-!
# do Carmo's formula (1): the first variation of energy, assembled

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4 (`prop:dc-ch9-2-4`).

This file **composes** the two halves of do Carmo's proof, which until now had never met:

1. *the surface half* — `hasDerivAt_dcEnergy_of_dominated`
   (`Variation/EnergyFirstDeriv.lean`): differentiating `E(s) = ∫⟨∂f/∂t, ∂f/∂t⟩ dt` under
   the integral sign gives `E'(s₀) = 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩ dt`;
2. *the intrinsic half* — `IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left`
   (`Variation/FirstVariation.lean`): integrating `∫⟨DV/dt, dc/dt⟩ dt` by parts gives do
   Carmo's right-hand side.

The hinge between them is the **symmetry of the Riemannian connection**,
`D/∂s ∂f/∂t = D/∂t ∂f/∂s` (do Carmo Ch. 3, Lemma 3.4), which turns half 1's `D/∂s ∂f/∂t`
into half 2's `DV/dt`.  Here it is carried as the **hypothesis** `hsymm`; see `## Scope`.

## Scope — what is and is not claimed

The conclusion is do Carmo's formula (1) **on a single segment carrying no breakpoint**:
$$\frac{1}{2}E'(0)
  = -\int_a^b \Big\langle V, \frac{D}{dt}\frac{dc}{dt}\Big\rangle dt
    - \Big\langle V(a), \frac{dc}{dt}(a)\Big\rangle
    + \Big\langle V(b), \frac{dc}{dt}(b)\Big\rangle .$$
do Carmo's jump sum `∑_i ⟨V(t_i), Δ(dc/dt)(t_i)⟩` arises by summing this over the segments
`[t_i, t_{i+1}]` of his subdivision, where the boundary terms at the interior breakpoints
telescope into the differences `dc/dt(t_i^+) − dc/dt(t_i^-)`.  That summation is **not**
performed here, so `prop:dc-ch9-2-4` is **not** tagged by this file: what is proved is
formula (1) for a variation of a curve that is differentiable across `[a, b]`, which is do
Carmo's `k = 0` case.

`hsymm` is a hypothesis, not a theorem, in this file.  It is exactly do Carmo's "using the
symmetry of the Riemannian connection" step, and — this matters for discharging it — it is
required only at **interior** times `t ∈ (a, b)`: the boundary instances are a null set, and
the proof exchanges `d/ds` past `∫` through `intervalIntegral.integral_congr_ae`.  That is
precisely the range on which `SurfaceSymmetryManifold.covariantDerivS_velT_eq_covariantDerivT_velS`
produces the identity (its conclusion holds at times strictly interior to the covariant
pair's window).  The chart-level form is
`surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst`
(`Variation/SurfaceSymmetry.lean`); discharging `hsymm` from it requires transferring that
identity from a chart reading of the surface to the intrinsic covariant pairs used here.

Four distinct fields appear, and conflating any two of them silently changes the statement:
`T = ∂f/∂t`, `S = ∂f/∂s`, `DsT = D/∂s ∂f/∂t` and `DtT = D/∂t ∂f/∂t = D/dt(dc/dt)`, plus
`DtS = D/∂t ∂f/∂s = DV/dt`.  Only `T` is pinned to the surface by the type system, via
`hvel`; `S` is *not* forced to be `∂f/∂s`, and `DtS`, `DtT` are tied to their fields only by
the covariant-pair hypotheses `hV`, `hW` — the same convention `FirstVariation.lean` uses,
and the reason `hsymm` must be stated rather than derived from the types.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4; the symmetry of the
connection is Ch. 3, Lemma 3.4, and metric compatibility is Ch. 2, Prop. 3.2.
-/

open Set Riemannian Filter MeasureTheory
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** do Carmo Ch. 9, §2, **formula (1) on a segment with no breakpoint**
(`prop:dc-ch9-2-4` for `k = 0`):
$$\frac{1}{2}E'(s_0)
  = -\int_a^b \Big\langle V, \frac{D}{dt}\frac{dc}{dt}\Big\rangle dt
    - \Big\langle V(a), \frac{dc}{dt}(a)\Big\rangle
    + \Big\langle V(b), \frac{dc}{dt}(b)\Big\rangle ,$$
where `c = f(s₀, ·)` is the curve in the variation at `s₀`, `V = ∂f/∂s(s₀, ·)` is the
variational field, `W = ∂f/∂t(s₀, ·) = dc/dt` its velocity and `DW = D/dt(dc/dt)`.

The three inputs are do Carmo's three steps, in his order:
* `hasDerivAt_dcEnergy_of_dominated` — differentiation under the integral sign;
* `hsymm` — the symmetry of the Riemannian connection, `D/∂s ∂f/∂t = D/∂t ∂f/∂s`
  (Ch. 3, Lemma 3.4), supplied as a hypothesis;
* `IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left` — integration by
  parts, which is metric compatibility (Ch. 2, Prop. 3.2) plus the fundamental theorem of
  calculus. -/
theorem hasDerivAt_dcEnergy_eq_first_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {T S DsT DtS DtT : ℝ × ℝ → E}
    {s₀ a b ε : ℝ} {bound : ℝ → ℝ}
    (hab : a ≤ b) (hε : 0 < ε)
    (hvel : ∀ σ t, T (σ, t) = DCVelocity (I := I) (fun τ => f (σ, τ)) t)
    -- the surface half, along the transversals
    (hslice : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hsdiff : ∀ t ∈ uIoc a b, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (s₀ - ε) (s₀ + ε))
    (hscont : ∀ t ∈ uIoc a b, ∀ σ ∈ Icc (s₀ - ε) (s₀ + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds s₀, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t)) (T (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (T (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hF'_meas : AEStronglyMeasurable
      (fun t => 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      (volume.restrict (uIoc a b)))
    (h_bound : ∀ t ∈ uIoc a b, ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖2 * g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖
        ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume a b)
    -- the symmetry of the connection: `D/∂s ∂f/∂t = D/∂t ∂f/∂s`, at interior times
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    -- the intrinsic half, along the curve in the variation at `s₀`
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => S (s₀, τ)) (fun τ => DtS (s₀, τ)) a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => T (s₀, τ)) (fun τ => DtT (s₀, τ)) a b)
    (htdiff : IsChartDifferentiableOn (I := I) (fun τ => f (s₀, τ)) a b)
    (htcont : ∀ t ∈ Icc a b, ContinuousAt (fun τ => f (s₀, τ)) t)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtT (s₀, t)))
      volume a b) :
    HasDerivAt (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)
      (2 * ((g.metricInner (f (s₀, b)) (S (s₀, b) : TangentSpace I (f (s₀, b))) (T (s₀, b))
              - g.metricInner (f (s₀, a)) (S (s₀, a) : TangentSpace I (f (s₀, a))) (T (s₀, a)))
            - ∫ t in a..b, g.metricInner (f (s₀, t))
                (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtT (s₀, t)))) s₀ := by
  -- half 1: differentiation under the integral sign
  have hE := hasDerivAt_dcEnergy_of_dominated (I := I) (g := g) (f := f) (T := T) (DsT := DsT)
    (bound := bound) hε hvel hslice hsdiff hscont hF_meas hF_int hF'_meas h_bound hbound_int
  -- half 2: integration by parts, along the curve in the variation at `s₀`
  have hparts := hV.integral_metricInner_covariantDeriv_left hW htdiff htcont hab hint₁ hint₂
  -- the hinge: the symmetry of the connection turns `D/∂s ∂f/∂t` into `DV/dt`
  have hrw : (∫ t in a..b, 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      = 2 * ∫ t in a..b, g.metricInner (f (s₀, t))
        (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
    rw [hsymm t (ht.mpr htm)]
  rw [hrw, hparts] at hE
  exact hE

/-- **Math.** do Carmo Ch. 9, Prop. 2.4, the finite-subdivision assembly step.

Suppose the first-variation formula has been proved separately on every segment
`[tau i, tau (i+1)]`.  The total energy is their sum near `s0`; differentiating that finite
sum and telescoping the endpoint pairings gives the outer endpoint terms and the negative
jump sum in do Carmo's formula (1).

`bulk i` is the integral `integral <V, D/dt (dc/dt)>` on segment `i`; `minus i` and
`plus i` are the pairings with the left and right velocity limits at subdivision point
`tau i`.  The remaining hypotheses of the full proposition are precisely what must
produce the segment formulas and these one-sided values from an arbitrary variation. -/
theorem hasDerivAt_dcEnergy_eq_piecewise_first_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0) :
    HasDerivAt
      (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau 0) (tau (k + 1)))
      (2 * (minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
        - ∑ i ∈ Finset.range (k + 1), bulk i)) s0 := by
  have hsum := hasDerivAt_sum_segments_of_first_variation k
    (fun i s => DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
    bulk minus plus s0 hsegment
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hint] with s hs
  exact dcEnergy_eq_sum_subdivision (I := I) g (fun t => f (s, t)) tau (k + 1) hs

/-- **Math.** do Carmo Ch. 9, Prop. 2.5, the direction
*geodesic implies critical point of energy*, on a segment with no breakpoint.

This specializes `hasDerivAt_dcEnergy_eq_first_variation`: the covariant
acceleration of the base curve is zero, and properness makes the variational
field vanish at both endpoints, so every term in the first-variation formula
vanishes. -/
theorem hasDerivAt_dcEnergy_zero_of_geodesic
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {T S DsT DtS : ℝ × ℝ → E}
    {s₀ a b ε : ℝ} {bound : ℝ → ℝ}
    (hab : a ≤ b) (hε : 0 < ε)
    (hvel : ∀ σ t, T (σ, t) = DCVelocity (I := I) (fun τ => f (σ, τ)) t)
    (hslice : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hsdiff : ∀ t ∈ uIoc a b, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (s₀ - ε) (s₀ + ε))
    (hscont : ∀ t ∈ uIoc a b, ∀ σ ∈ Icc (s₀ - ε) (s₀ + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds s₀, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t)) (T (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (T (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hF'_meas : AEStronglyMeasurable
      (fun t => 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      (volume.restrict (uIoc a b)))
    (h_bound : ∀ t ∈ uIoc a b, ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖2 * g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖
        ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume a b)
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => S (s₀, τ)) (fun τ => DtS (s₀, τ)) a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => T (s₀, τ)) (fun _ => 0) a b)
    (htdiff : IsChartDifferentiableOn (I := I) (fun τ => f (s₀, τ)) a b)
    (htcont : ∀ t ∈ Icc a b, ContinuousAt (fun τ => f (s₀, τ)) t)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (0 : E))
      volume a b)
    (hSa : S (s₀, a) = 0) (hSb : S (s₀, b) = 0) :
    HasDerivAt (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b) 0 s₀ := by
  have hE := hasDerivAt_dcEnergy_eq_first_variation (I := I) (g := g)
    (f := f) (T := T) (S := S) (DsT := DsT) (DtS := DtS) (DtT := fun _ => 0)
    hab hε hvel hslice hsdiff hscont hF_meas hF_int hF'_meas h_bound hbound_int
    hsymm hV hW htdiff htcont hint₁ hint₂
  have hleft : g.metricInner (f (s₀, a))
      (S (s₀, a) : TangentSpace I (f (s₀, a))) (T (s₀, a)) = 0 := by
    rw [hSa]
    exact g.metricInner_zero_left _ _
  have hright : g.metricInner (f (s₀, b))
      (S (s₀, b) : TangentSpace I (f (s₀, b))) (T (s₀, b)) = 0 := by
    rw [hSb]
    exact g.metricInner_zero_left _ _
  have hzero : (∫ t in a..b, g.metricInner (f (s₀, t))
      (S (s₀, t) : TangentSpace I (f (s₀, t))) (0 : E)) = 0 := by
    have hz : ∀ t, g.metricInner (f (s₀, t))
        (S (s₀, t) : TangentSpace I (f (s₀, t))) (0 : E) = 0 :=
      fun t => g.metricInner_zero_right _ _
    simp only [hz, intervalIntegral.integral_zero]
  rw [hleft, hright, hzero] at hE
  simpa using hE

end Riemannian.Variation
