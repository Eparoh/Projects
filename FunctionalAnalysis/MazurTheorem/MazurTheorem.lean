import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import FunctionalAnalysis.MazurTheorem.Defs
import FunctionalAnalysis.MazurTheorem.Lemmas
import FunctionalAnalysis.MazurTheorem.WeakTopology

noncomputable section

open Set Filter Topology Classical Function NormedSpace Defs Lemmas

set_option linter.unusedVariables false

theorem induced_coarsest {X Y: Type*} (f: X → Y) [tY: TopologicalSpace Y] (tX: TopologicalSpace X):
  @Continuous X Y tX _ f → ∀ (s: Set X), @IsOpen X (TopologicalSpace.induced f tY) s → @IsOpen X tX s := by
    intro f_tcont s s_iopen
    rw [isOpen_induced_iff] at s_iopen
    rcases s_iopen with ⟨V, Vopen, seqpreV⟩
    rw [continuous_def] at f_tcont
    rw [← seqpreV]
    exact f_tcont V Vopen

theorem weak_open_implies_open {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  {B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂} (h₁: DualPair B) (t: TopologicalSpace E) (h₂: CompatibleTopology B t) (s: Set E) :
  @IsOpen E (WeakBilin.instTopologicalSpace B) s → @IsOpen E t s := by
    intro s_wopen
    apply induced_coarsest (fun x y => B x y)
    · dsimp [CompatibleTopology] at h₂
      rw [continuous_pi_iff]
      intro f
      have : (fun e ↦ (B e) f) = B.flip f := by
        ext e
        simp
      rw [this]
      rw [h₂ (B.flip f)]
      simp
    · assumption

theorem weak_closed_implies_closed {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  {B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂} (h₁: DualPair B) (t: TopologicalSpace E) (h₂: CompatibleTopology B t) (s: Set E) :
  @IsClosed E (WeakBilin.instTopologicalSpace B) s → @IsClosed E t s := by
    intro s_wclosed
    rw [← @isOpen_compl_iff] at *
    exact weak_open_implies_open h₁ t h₂ sᶜ s_wclosed

theorem closed_convex_iff_weak_closed {E F: Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B: E →ₗ[ℝ] F →ₗ[ℝ] ℝ} (h₁: DualPair B) (t: TopologicalSpace E)  [TopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] (h₂: CompatibleTopology B t) (s: Set E): Convex ℝ s →
  (@IsClosed E t s ↔ @IsClosed E (WeakBilin.instTopologicalSpace B) s) := by
    intro sconvex
    constructor
    · intro s_tclosed
      rw [← @isOpen_compl_iff, @isOpen_iff_mem_nhds]
      intro e enins
      rw [mem_compl_iff] at enins
      have := geometric_hahn_banach_closed_point sconvex s_tclosed enins
      rcases this with ⟨g, a ,asupboundgs, altge⟩
      rcases (h₂ g).mp g.cont with ⟨f, Bfeqg⟩
      rw [@mem_nhds_iff]
      let I : Finset F := {f}
      use {e' : E | ∀ i ∈ I, ‖(B (e' - e) i)‖ < g e - a}
      constructor
      · intro e' ein'
        dsimp at ein'
        have := ein' f (Finset.mem_singleton.mpr (by rfl))
        have eq : ∀ (e: E), B e f = g e := by
          intro e
          apply congr_arg (fun (x: E →ₗ[ℝ] ℝ) ↦ x e) Bfeqg
        rw [LinearMap.map_sub₂, eq, eq] at this
        rw [mem_compl_iff]
        by_contra e'ins
        rw [abs_lt] at this
        have := this.1
        simp at this
        have : g e' < a := by
          exact asupboundgs e' e'ins
        linarith
      · constructor
        · apply TopologicalSpace.IsTopologicalBasis.isOpen (weak_basis_general B)
          dsimp
          use e, I, (g e - a)
          constructor
          · linarith
          · rfl
        · dsimp
          intro i iinI
          rw [sub_self, map_zero]
          simp
          assumption
    · intro s_wclosed
      exact weak_closed_implies_closed h₁ t h₂ s s_wclosed

theorem closed_convex_iff_weak_closed_normed {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (s: Set X):
  Convex ℝ s → (IsClosed s ↔ IsClosed {x : WeakSpace ℝ X | x ∈ s}) := by
    exact closed_convex_iff_weak_closed (locallyconvex_dual_pair X) (@UniformSpace.toTopologicalSpace X _) (weak_compatible_normed ℝ X) s
