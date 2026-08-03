import MorganTianLib.Ch01.ExpDifferential
import MorganTianLib.Ch01.ExpLocalDiffeo
import MorganTianLib.Ch01.GaussLemma

/-!
# Morgan--Tian Ch. 1: the pointwise Gauss block of geodesic polar coordinates

This module joins the differential-of-exponential theorem to the manifold
Gauss lemma.  It gives the coordinate-free pointwise content of the first
part of `lem:geodesic-polar-form`: the radial differential is the geodesic
velocity, angular differentials are Jacobi endpoints, the radial direction
has the expected norm, and the radial-angular cross term vanishes.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [T2Space (TangentBundle I M)]

/-- **Math.** The intrinsic initial velocity of the global geodesic with initial vector
`v` is `v`.  The global geodesic is specified using the chart at `p`; this
lemma reads that chart velocity back as a tangent vector. -/
theorem mfderiv_globalGeodesic_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) :
    mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) 0 1 = v := by
  have hd : HasDerivAt
      (fun s => extChartAt I p (globalGeodesic (I := I) g hg p v s)) v 0 :=
    hasDerivAt_chartReading_globalGeodesic (I := I) g hg p v
  have h0 : globalGeodesic (I := I) g hg p v 0 = p :=
    globalGeodesic_zero g hg p v
  have hsrc : globalGeodesic (I := I) g hg p v 0 ∈ (chartAt H p).source := by
    rw [h0]
    exact mem_chart_source H p
  rw [mfderiv_eq_of_hasDerivAt_extChartAt (I := I)
    (continuous_globalGeodesic g hg p v).continuousAt hsrc hd, h0]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) p)

/-- **Math.** **Pointwise Gauss lemma for the exponential map.**  Let `v, Z ∈ T_pM`
with `Z ⊥ v`.  In a chart at `exp_p(v)`, the differential of `exp_p`

* sends `Z` to the endpoint of the Jacobi field with initial data `(0, Z)`;
* sends `v` to the velocity of the radial geodesic at time `1`;
* keeps these two images orthogonal; and
* preserves the squared norm of the radial vector.

Thus this theorem is the chart-independent pointwise identity behind
`exp_p^*g = dr² + g_r` in `lem:geodesic-polar-form`(1). -/
theorem expDifferential_gauss
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v Z : E)
    (horth : g.metricInner p (Z : TangentSpace I p) (v : TangentSpace I p) = 0) :
    ∃ (ζ : M) (D : E →L[ℝ] E) (J DJ : ℝ → E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasFDerivAt
        (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D v ∧
      IsJacobiFieldAlongOn (I := I) g
        (globalGeodesic (I := I) g hg p v) J DJ 0 1 ∧
      J 0 = 0 ∧ DJ 0 = Z ∧
      D Z = chartVectorRep (I := I)
        (globalGeodesic (I := I) g hg p v) ζ J 1 ∧
      D v = chartVectorRep (I := I)
        (globalGeodesic (I := I) g hg p v) ζ
          (fun t => mfderivVelocity (I := I) (E := E)
            (globalGeodesic (I := I) g hg p v) t) 1 ∧
      chartMetricInner (I := I) g ζ
          (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D Z) (D v) = 0 ∧
      chartMetricInner (I := I) g ζ
          (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D v) (D v)
        = g.metricInner p (v : TangentSpace I p) v := by
  classical
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p v
  have hgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) 1) :=
    fun t _ => hγgeo t
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p v
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t :=
    fun t _ => hγcont.continuousAt
  obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
    exists_isJacobiFieldAlongOn (I := I) (g := g) (γ := γ)
      (a := 0) (b := 1) zero_lt_one hgeo hcont
      (0 : TangentSpace I (γ 0)) (Z : TangentSpace I (γ 0))
  have hDZ : D Z = chartVectorRep (I := I) γ ζ J 1 := by
    rw [← hDJ0]
    exact hjac J DJ hJ hJ0
  have hsrc : γ 1 ∈ (chartAt H ζ).source := by
    simpa [hγdef, expMapGlobal_def] using hζ
  have hvel0 : mfderivVelocity (I := I) (E := E) γ 0 = v := by
    simpa [mfderivVelocity_def, hγdef] using
      mfderiv_globalGeodesic_zero (I := I) g hg p v
  have hinit : innerVelocity (I := I) g γ DJ 0 = 0 := by
    rw [innerVelocity_def, hDJ0, hvel0, hγ0]
    exact horth
  have hgauss : innerVelocity (I := I) g γ J 1 = 0 :=
    hJ.innerVelocity_fst_eq_zero hgeo hcont hJ0 hinit 1
      (right_mem_Icc.2 zero_le_one)

  have hscalar : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
    simpa only [id_eq, add_comm] using
      (hasDerivAt_id (0 : ℝ)).const_add 1
  have hc : HasDerivAt (fun t : ℝ => (1 + t) • v) v 0 := by
    simpa using hscalar.smul_const v
  have hleft : HasDerivAt
      (fun t : ℝ => extChartAt I ζ
        (expMapGlobal (I := I) g hg p
          (((1 + t) • v : E) : TangentSpace I p)))
      (D v) 0 := by
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq
      (x := (0 : ℝ)) (hl := hFD) (hf := hc) (hy := by simp)
    simpa [Function.comp_def] using hcomp
  let ξ : E := tangentCoordChange I (γ 1) ζ (γ 1)
    (deriv (chartLocalCurve (I := I) γ 1) 1)
  have hvelread : HasDerivAt (fun s : ℝ => extChartAt I ζ (γ s)) ξ 1 := by
    exact ((hγgeo 1).eventually_hasDerivAt_extChartAt
      hγcont.continuousAt hsrc).self_of_nhds
  have hright : HasDerivAt
      (fun t : ℝ => extChartAt I ζ (γ (1 + t))) ξ 0 := by
    have hcomp := HasDerivAt.scomp_of_eq
      (hg := hvelread) (hh := hscalar) (hy := by norm_num)
    simpa [Function.comp_def] using hcomp
  have heqcurve :
      (fun t : ℝ => extChartAt I ζ
        (expMapGlobal (I := I) g hg p
          (((1 + t) • v : E) : TangentSpace I p)))
      = fun t : ℝ => extChartAt I ζ (γ (1 + t)) := by
    funext t
    rw [expMapGlobal_def,
      globalGeodesic_smul g hg p (v : TangentSpace I p) (1 + t)]
    simp [hγdef]
  rw [heqcurve] at hleft
  have hDvξ : D v = ξ := hleft.unique hright
  have hreadEq := chartVectorRep_velocity_of_geodesicAt (I := I)
    (hγgeo 1) hγcont.continuousAt hsrc
  have hreadξ : chartVectorRep (I := I) γ ζ
      (fun t => mfderivVelocity (I := I) (E := E) γ t) 1 = ξ := by
    exact hreadEq.trans hvelread.deriv
  have hDv : D v = chartVectorRep (I := I) γ ζ
      (fun t => mfderivVelocity (I := I) (E := E) γ t) 1 :=
    hDvξ.trans hreadξ.symm

  have hchartCross :
      chartMetricInner (I := I) g ζ (extChartAt I ζ (γ 1))
        (D Z) (D v) = 0 := by
    rw [hDZ, hDv, ← metricInner_eq_chartMetricInner_rep (I := I) g hsrc J
      (fun t => mfderivVelocity (I := I) (E := E) γ t)]
    exact hgauss
  have hspeed :
      g.metricInner (γ 1)
          (mfderivVelocity (I := I) (E := E) γ 1 : TangentSpace I (γ 1))
          (mfderivVelocity (I := I) (E := E) γ 1)
        = g.metricInner p (v : TangentSpace I p) v := by
    have hs := IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ)
      isOpen_univ isPreconnected_univ hγcont.continuousOn
      (mem_univ (1 : ℝ)) (mem_univ (0 : ℝ))
    change g.metricInner (γ 1)
        (mfderivVelocity (I := I) (E := E) γ 1 : TangentSpace I (γ 1))
        (mfderivVelocity (I := I) (E := E) γ 1)
      = g.metricInner (γ 0)
        (mfderivVelocity (I := I) (E := E) γ 0 : TangentSpace I (γ 0))
        (mfderivVelocity (I := I) (E := E) γ 0) at hs
    rw [hvel0, hγ0] at hs
    exact hs
  have hchartRadial :
      chartMetricInner (I := I) g ζ (extChartAt I ζ (γ 1))
        (D v) (D v) = g.metricInner p (v : TangentSpace I p) v := by
    rw [hDv, ← metricInner_eq_chartMetricInner_rep (I := I) g hsrc
      (fun t => mfderivVelocity (I := I) (E := E) γ t)
      (fun t => mfderivVelocity (I := I) (E := E) γ t)]
    exact hspeed
  refine ⟨ζ, D, J, DJ, hζ, hFD, ?_, hJ0, hDJ0, ?_, ?_, ?_, ?_⟩
  · simpa [hγdef] using hJ
  · simpa [hγdef] using hDZ
  · simpa [hγdef] using hDv
  · simpa [hγdef, expMapGlobal_def] using hchartCross
  · simpa [hγdef, expMapGlobal_def] using hchartRadial

end MorganTianLib

end

#print axioms MorganTianLib.mfderiv_globalGeodesic_zero
#print axioms MorganTianLib.expDifferential_gauss
