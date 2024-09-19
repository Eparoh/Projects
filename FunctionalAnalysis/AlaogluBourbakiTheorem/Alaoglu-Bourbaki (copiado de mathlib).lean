import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.Normed.Module.WeakDual
import Nets.Nets_mathlib

noncomputable section

open Set Filter Topology Classical Function WeakDual

set_option linter.unusedVariables false
set_option linter.simpsNoConstructor false

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

#check WeakDual.polar
#check isClosed_polar
#check Iic

theorem isClosed_polar' (s : Set E) : IsClosed (polar 𝕜 s) := by
  simp only [polar_def, setOf_forall]
  apply isClosed_biInter
  intro e eins
  exact IsClosed.preimage (Continuous.norm (WeakBilin.eval_continuous (topDualPairing 𝕜 E) e)) isClosed_Iic

theorem isClosed_image_coe_of_bounded_of_closed' {s : Set (WeakDual 𝕜 E)}
    (hb : Bornology.IsBounded (NormedSpace.Dual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' s) := by
      sorry
