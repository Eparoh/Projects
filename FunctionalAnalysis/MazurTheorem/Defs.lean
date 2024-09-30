import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

noncomputable section

open Set Filter Topology Classical Function

set_option linter.unusedVariables false

/- Instance for substraction in X for the weak topology -/
instance WeakSpace.instHSub {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  HSub (WeakSpace 𝕂 X) (WeakSpace 𝕂 X) (WeakSpace 𝕂 X) where
    hSub := by
      dsimp only [WeakSpace, WeakBilin]
      exact fun x y ↦ x - y

/- Instance for substraction in X* for the weak* topology -/
instance WeakDual.instHSub {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  HSub (WeakDual 𝕂 X) (WeakDual 𝕂 X) (WeakDual 𝕂 X) where
    hSub := by
      dsimp only [WeakDual, WeakBilin]
      exact fun x y ↦ x - y

namespace Defs

/- Definition for a function defined by pieces -/
def partial_fun {α β: Type} (p : α → Prop) (f g : α → β) : α → β := fun (a: α) ↦
  if p a then
    f a
  else
    g a

/- Definition: Let E and F be two vector spaces over a field 𝕂, B: E × F → 𝕂 a bilinear form and S a subset of F (E).
               We say that S separates points of E (F) if given e ∈ E (f ∈ F) such that B(e, s) = 0 (B(s, f) = 0) for every s ∈ S
               implies that e = 0 (f = 0). -/
def SepPoints {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (S : Set F) (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) : Prop := ∀ (e : E), (∀ s ∈ S, B e s = 0) → e = 0

/- Definition: Let E and F be two vector spaces over a field 𝕂 and B: E × F → 𝕂 a bilinear form.
               We say that E and F are a dual pair (with respect to B) if F separates points of E and E separates points of F. -/
def DualPair {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) : Prop := SepPoints univ B ∧ SepPoints univ (B.flip)

/- Definition: Let E and F be two vector spaces over a field 𝕂, B: E × F → 𝕂 a bilinear form and τ a topology on E.
               We say that τ is compatible with the bilinear form B if (E, τ)* = B.flip [F]. -/
def CompatibleTopology {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) (t: TopologicalSpace E) : Prop :=
    ∀ (g: E→ₗ[𝕂] 𝕂), Continuous g ↔ g ∈ range (fun (f: F) ↦ B.flip f)
