import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

noncomputable section

open Set Filter Topology Classical Function

set_option linter.unusedVariables false

instance WeakSpace.instHSub {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  HSub (WeakSpace 𝕂 X) (WeakSpace 𝕂 X) (WeakSpace 𝕂 X) where
    hSub := by
      dsimp [WeakSpace, WeakBilin]
      exact fun x y ↦ x - y

instance WeakDual.instHSub {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  HSub (WeakDual 𝕂 X) (WeakDual 𝕂 X) (WeakDual 𝕂 X) where
    hSub := by
      dsimp [WeakDual, WeakBilin]
      exact fun x y ↦ x - y

namespace Defs

def partial_fun {α β: Type} (p : α → Prop) (f g : α → β) (a : α) : β :=
  if p a then
    f a
  else
    g a

def SepPoints {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (S : Set F) (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) : Prop := ∀ (e : E), (∀ s ∈ S, B e s = 0) → e = 0

def DualPair {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) : Prop := SepPoints univ B ∧ SepPoints univ (B.flip)

def CompatibleTopology {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) (t: TopologicalSpace E) : Prop :=
    ∀ (g: E→ₗ[𝕂] 𝕂), Continuous g ↔ g ∈ range (fun (f: F) ↦ B.flip f)
