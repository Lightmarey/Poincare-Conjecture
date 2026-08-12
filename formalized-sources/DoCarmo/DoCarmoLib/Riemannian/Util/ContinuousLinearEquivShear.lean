import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The right additive shear equivalence

This utility file provides the right additive shear map `(a, b) ↦ (a, a + b)` on
`E × E` as a continuous linear equivalence, over an arbitrary nontrivially normed
field. It is used to model do Carmo's block matrix `[[I, 0], [I, I]]` in the
inverse-function-theorem step of the totally-normal-neighborhood theorem.
-/

namespace ContinuousLinearEquiv

/-- **Math.** The right additive shear map `(a, b) ↦ (a, a + b)` on `E × E`,
over an arbitrary nontrivially normed field. -/
protected def shearAddRight (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (E × E) ≃L[𝕜] E × E :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst 𝕜 E E).prod
      ((ContinuousLinearMap.fst 𝕜 E E) + (ContinuousLinearMap.snd 𝕜 E E)))
    ((ContinuousLinearMap.fst 𝕜 E E).prod
      ((ContinuousLinearMap.snd 𝕜 E E) - (ContinuousLinearMap.fst 𝕜 E E)))
    (fun _ => by simp [ContinuousLinearMap.prod_apply])
    (fun _ => by simp [ContinuousLinearMap.prod_apply])

end ContinuousLinearEquiv
