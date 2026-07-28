import DoCarmoLib.Riemannian.Variation.SecondVariationFormula

/-!
# Finite-subdivision assembly of the second variation

This file performs the finite-subdivision step in do Carmo, Ch. 9, Prop. 2.8.  Its input is
the second-variation formula on each smooth segment.  Finite additivity of energy identifies
the derivative of the total energy with the sum of the segment derivatives, and the endpoint
pairings telescope to the jump term in formula (3).
-/

open Set Riemannian Filter MeasureTheory
open scoped BigOperators ContDiff Manifold Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Finite-subdivision assembly of do Carmo's second-variation formula.

For the subdivision `tau 0, ..., tau (k + 1)`, let `bulk i` be
`integral <V, V'' + R(gamma', V) gamma'>` on segment `i`.  At a subdivision point,
`minus i` and `plus i` are the pairings `<V, DV/dt>` with the left and right one-sided
covariant derivatives.  Thus the second variation on segment `i` has derivative

`2 * ((minus (i + 1) - plus i) - bulk i)`.

The hypotheses separate the two genuine analytic requirements of the assembly:

* `hint` gives finite additivity of energy on a neighbourhood of `s0`;
* `hfirst` says the segment energy functions are differentiable there, so differentiating
  their finite sum really is the sum of their derivatives.

Together with the per-segment second-variation identities `hsegment`, these imply the global
second variation, including the outer endpoint terms and all internal jumps. -/
theorem hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0) :
    HasDerivAt
      (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))))
      (2 * (minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
        - ∑ i ∈ Finset.range (k + 1), bulk i)) s0 := by
  have henergy :
      (fun s => DCEnergy (I := I) g (fun t => f (s, t)) (tau 0) (tau (k + 1)))
        =ᶠ[nhds s0]
      (fun s => ∑ i ∈ Finset.range (k + 1),
        DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1))) := by
    filter_upwards [hint] with s hs
    exact dcEnergy_eq_sum_subdivision (I := I) g (fun t => f (s, t)) tau (k + 1) hs
  have hderivSum :
      deriv (fun s => ∑ i ∈ Finset.range (k + 1),
        DCEnergy (I := I) g (fun t => f (s, t)) (tau i) (tau (i + 1)))
        =ᶠ[nhds s0]
      (fun s => ∑ i ∈ Finset.range (k + 1),
        deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))) s) := by
    filter_upwards [hfirst] with s hs
    exact deriv_fun_sum (u := Finset.range (k + 1))
      (fun i hi => hs i (Finset.mem_range.mp hi))
  have htotal :
      deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))) =ᶠ[nhds s0]
      (fun s => ∑ i ∈ Finset.range (k + 1),
        deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))) s) :=
    henergy.deriv.trans hderivSum
  have hsum := hasDerivAt_sum_segments_of_first_variation k
    (fun i s => deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
      (tau i) (tau (i + 1))) s)
    bulk minus plus s0 hsegment
  exact hsum.congr_of_eventuallyEq htotal

/-- **Math.** Formula (3) at the finite-subdivision assembly level when the two outer
endpoint pairings vanish.

For a proper variation those endpoint pairings vanish; here their vanishing is exposed as
explicit scalar hypotheses rather than being derived from `IsProperVariation`. Consequently
the second derivative of the total energy is minus twice the sum of the segment bulk
integrals and the one-sided derivative jumps at all internal subdivision points. -/
theorem hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation_of_proper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0)
    (hplus0 : plus 0 = 0) (hminusEnd : minus (k + 1) = 0) :
    HasDerivAt
      (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
        (tau 0) (tau (k + 1))))
      (-2 * ((∑ i ∈ Finset.range (k + 1), bulk i)
        + ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1)))) s0 := by
  have hglobal := hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation
    (I := I) hint hfirst hsegment
  apply hglobal.congr_deriv
  rw [hplus0, hminusEnd]
  ring

/-- **Math.** The value form of the finite-subdivision second-variation formula
when the two outer endpoint pairings vanish. -/
theorem deriv_deriv_dcEnergy_eq_piecewise_second_variation_of_proper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {tau : ℕ → ℝ} {k : ℕ} {s0 : ℝ}
    {bulk minus plus : ℕ → ℝ}
    (hint : ∀ᶠ s in nhds s0, ∀ i < k + 1, IntervalIntegrable
      (fun t => g.metricInner (f (s, t))
        (DCVelocity (I := I) (fun u => f (s, u)) t)
        (DCVelocity (I := I) (fun u => f (s, u)) t))
      volume (tau i) (tau (i + 1)))
    (hfirst : ∀ᶠ s in nhds s0, ∀ i < k + 1, DifferentiableAt ℝ
      (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
        (tau i) (tau (i + 1))) s)
    (hsegment : ∀ i < k + 1,
      HasDerivAt
        (deriv (fun sigma => DCEnergy (I := I) g (fun t => f (sigma, t))
          (tau i) (tau (i + 1))))
        (2 * ((minus (i + 1) - plus i) - bulk i)) s0)
    (hplus0 : plus 0 = 0) (hminusEnd : minus (k + 1) = 0) :
    deriv (deriv (fun s => DCEnergy (I := I) g (fun t => f (s, t))
      (tau 0) (tau (k + 1)))) s0
      = -2 * ((∑ i ∈ Finset.range (k + 1), bulk i)
        + ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))) :=
  (hasDerivAt_deriv_dcEnergy_eq_piecewise_second_variation_of_proper
    (I := I) hint hfirst hsegment hplus0 hminusEnd).deriv

end Riemannian.Variation
