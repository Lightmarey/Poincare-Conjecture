import DoCarmoLib.Riemannian.Manifold.EuclideanOpens

/-!
# Morgan--Tian Ch. 1 -- the open Riemannian cone

For a Riemannian manifold `(N,g)`, the open cone is the product
`N × (0,∞)` equipped with `dr² + r² g`.  The construction below uses the
DoCarmo pullback-form API, so both the radial term and the tangential term are
bundled as continuous bilinear forms on the product tangent space.
-/

open Set Riemannian TopologicalSpace
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib

/-! ## The positive radial factor -/

/-- **Math.** The open positive half-line, regarded as an open subset of `ℝ`.
Its subtype is the radial manifold `(0,∞)`. -/
def positiveReal : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩

@[simp] theorem positiveReal_mem (r : ↥positiveReal) : 0 < (r : ℝ) := r.property

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-! ### The cone bilinear form -/

/-- **Math.** The cone form `r² g + dr²` on `N × (0,∞)`, written as the
sum of the pullback of `g` along the first projection, scaled by `r²`, and
the pullback of the Euclidean metric along the radial projection. -/
noncomputable def coneForm (g : RiemannianMetric I N) (p : N × ↥positiveReal) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ :=
  ((p.2 : ℝ) ^ 2) •
      DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) g (Prod.fst : N × ↥positiveReal → N) p +
    DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) (opensEuclideanMetric positiveReal)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) p

omit [FiniteDimensional ℝ E] in
/-- **Math.** Evaluation of the cone form on tangent vectors. -/
@[simp] theorem coneForm_apply (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    coneForm g p u v =
      (p.2 : ℝ) ^ 2 * g.metricInner p.1
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p v) +
      (opensEuclideanMetric positiveReal).metricInner p.2
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u)
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p v) := by
  simp only [coneForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, DCInducedForm_apply]

omit [FiniteDimensional ℝ E] in
theorem coneForm_symm (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) : coneForm g p u v = coneForm g p v u := by
  rw [coneForm_apply, coneForm_apply, g.metricInner_comm,
    (opensEuclideanMetric positiveReal).metricInner_comm]

omit [FiniteDimensional ℝ E] in
theorem coneForm_self_nonneg (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) : 0 ≤ coneForm g p u u := by
  rw [coneForm_apply]
  have h₁ : 0 ≤ (p.2 : ℝ) ^ 2 * g.metricInner p.1
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (Prod.fst : N × ↥positiveReal → N) p u) :=
    mul_nonneg (sq_nonneg _) (g.metricInner_self_nonneg _ _)
  have h₂ : 0 ≤ (opensEuclideanMetric positiveReal).metricInner p.2
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u)
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u) :=
    (opensEuclideanMetric positiveReal).metricInner_self_nonneg _ _
  linarith

omit [FiniteDimensional ℝ E] in
theorem coneForm_self_pos (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) (hu : u ≠ 0) : 0 < coneForm g p u u := by
  have hfst : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) p u = u.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) p u = u.2 := by
    rw [mfderiv_snd]
    rfl
  rw [coneForm_apply, hfst, hsnd]
  have hrad : 0 < (p.2 : ℝ) ^ 2 := sq_pos_of_pos p.2.property
  have h₁ : 0 ≤ (p.2 : ℝ) ^ 2 * g.metricInner p.1 u.1 u.1 :=
    mul_nonneg (sq_nonneg _) (g.metricInner_self_nonneg _ _)
  have h₂ : 0 ≤ (opensEuclideanMetric positiveReal).metricInner p.2 u.2 u.2 :=
    (opensEuclideanMetric positiveReal).metricInner_self_nonneg _ _
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]
    exact fun h => hu (Prod.ext h.1 h.2)
  rcases hor with h₁u | h₂u
  · have hp : 0 < (p.2 : ℝ) ^ 2 * g.metricInner p.1 u.1 u.1 :=
      mul_pos hrad (g.metricInner_self_pos _ _ h₁u)
    linarith
  · have hp : 0 < (opensEuclideanMetric positiveReal).metricInner p.2 u.2 u.2 :=
      (opensEuclideanMetric positiveReal).metricInner_self_pos _ _ h₂u
    linarith

omit [FiniteDimensional ℝ E] in
theorem coneForm_contMDiff (g : RiemannianMetric I N) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p, coneForm g p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
  have hrad : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : N × ↥positiveReal ↦ ((p.2 : ℝ) ^ 2)) := by
    exact ((contMDiff_subtype_val_opens.comp contMDiff_snd).pow 2)
  have htan : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p,
        DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) g
          (Prod.fst : N × ↥positiveReal → N) p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
    exact DCInducedForm_contMDiff g contMDiff_fst
  have hradial : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)) ∞
      (fun p : N × ↥positiveReal ↦ (⟨p,
        DCInducedForm (I := I.prod 𝓘(ℝ, ℝ)) (opensEuclideanMetric positiveReal)
          (Prod.snd : N × ↥positiveReal → ↥positiveReal) p⟩ :
        Bundle.TotalSpace ((E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ)
          (fun p : N × ↥positiveReal ↦
            TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ]
              TangentSpace (I.prod 𝓘(ℝ, ℝ)) p →L[ℝ] ℝ))) := by
    exact DCInducedForm_contMDiff (opensEuclideanMetric positiveReal) contMDiff_snd
  exact (hrad.smul_section htan).add_section hradial

/-! ### The bundled metric -/

/-- **Math.** The open cone metric over `g`, with pointwise inner product
`⟨(u,a),(v,b)⟩ = r²⟨u,v⟩_g + a b`. -/
noncomputable def coneMetric (g : RiemannianMetric I N) :
    RiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (N × ↥positiveReal) where
  inner p := coneForm g p
  symm p u v := coneForm_symm g p u v
  pos p u hu := coneForm_self_pos g p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E × ℝ) (coneForm g p) (fun u hu => ?_)
    exact coneForm_self_pos g p u hu
  contMDiff := coneForm_contMDiff g

@[simp] theorem coneMetric_apply (g : RiemannianMetric I N) (p : N × ↥positiveReal)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p) :
    (coneMetric g).metricInner p u v = coneForm g p u v :=
  rfl

/-- **Math.** In the product tangent splitting, the cone metric is exactly
`r²⟨u,v⟩_g + a b`. -/
@[simp] theorem coneMetric_metricInner_mk (g : RiemannianMetric I N)
    (x : N) (r : ↥positiveReal) (u v : TangentSpace I x) (a b : ℝ) :
    (coneMetric g).metricInner (x, r) (u, a) (v, b) =
      (r : ℝ) ^ 2 * g.metricInner x u v + a * b := by
  rw [coneMetric_apply, coneForm_apply]
  have hfst_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) (u, a) = u := by
    rw [mfderiv_fst]
    rfl
  have hfst_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : N × ↥positiveReal → N) (x, r) (v, b) = v := by
    rw [mfderiv_fst]
    rfl
  have hsnd_u : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) (u, a) = a := by
    rw [mfderiv_snd]
    rfl
  have hsnd_v : mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ↥positiveReal → ↥positiveReal) (x, r) (v, b) = b := by
    rw [mfderiv_snd]
    rfl
  rw [hfst_u, hfst_v, hsnd_u, hsnd_v, opensEuclideanMetric_apply]
  rw [show (inner ℝ a b : ℝ) = a * b from by simp [inner, mul_comm]]

end Cone

end MorganTianLib
