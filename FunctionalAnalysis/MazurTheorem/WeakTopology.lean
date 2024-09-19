import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import FunctionalAnalysis.MazurTheorem.Defs
import FunctionalAnalysis.MazurTheorem.Lemmas
import Topology.Nets.Nets



noncomputable section

open Set Filter Topology Classical Function NormedSpace Defs Lemmas

set_option linter.unusedVariables false

universe u

/- Basis for weak topologies -/

theorem weak_basis_general {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂): TopologicalSpace.IsTopologicalBasis
  {U : Set (WeakBilin B) | ∃ (e₀ : WeakBilin B), ∃ (I : Finset F), ∃ (ε : ℝ), (0 < ε ∧
   U = {e : WeakBilin B | ∀ i ∈ I, ‖(B (e - e₀) i)‖ < ε})} := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · intro U Uin
      rcases Uin with ⟨e₀, I, ε, εpos, Ubasopen⟩
      let V : Set (F → 𝕂) := {x : F → 𝕂 | ∀ i ∈ I, x i ∈ Metric.ball (B e₀ i) ε}
      have Vopen : IsOpen V := by
        rw [isOpen_pi_iff]
        intro x xinV
        use I
        use fun (f: F) ↦ Metric.ball ((B e₀) f) ε
        constructor
        · intro i iinI
          constructor
          · exact Metric.isOpen_ball
          · exact xinV i iinI
        · intro x xin
          rw [Set.mem_pi] at xin
          exact xin
      have : U = (fun x y ↦ (B x) y) ⁻¹' V := by
        ext e
        constructor
        · intro einU
          rw [mem_preimage]
          dsimp [V]
          rw [Ubasopen] at einU
          dsimp at einU
          intro i iinI
          rw [mem_ball_iff_norm, ← LinearMap.map_sub₂ B e e₀ i]
          exact einU i iinI
        · intro ein
          rw [Ubasopen]
          intro i iinI
          rw [mem_preimage] at ein
          dsimp [V] at ein
          rw [LinearMap.map_sub₂ B e e₀ i, ← mem_ball_iff_norm]
          exact ein i iinI
      rw [this]
      exact IsOpen.preimage (WeakBilin.coeFn_continuous B) Vopen
    · intro e U einU Uopen
      rw [isOpen_induced_iff] at Uopen
      rcases Uopen with ⟨V, Vopen, UeqpreV⟩
      rw [isOpen_pi_iff] at Vopen
      rw [← UeqpreV, mem_preimage] at einU
      rcases Vopen ((fun y ↦ (B e) y)) einU with ⟨I, u, uopen, piusubV⟩
      have : ∃ (ε : ℝ), (0 < ε ∧ ∀ i ∈ I, Metric.ball (B e i) ε ⊆ u i) := by
        apply exists_ball_subset_family
        intro i iinI
        have := uopen i iinI
        rw [Metric.isOpen_iff] at this
        exact this.1 (B e i) this.2
      rcases this with ⟨ε, εpos, eq⟩
      let v := {e' : WeakBilin B | ∀ i ∈ I, ‖(B (e' - e)) i‖ < ε}
      use v
      constructor
      · simp
        use e, I, ε, εpos
        ext e'
        constructor
        · intro e'inv
          simp [v] at e'inv
          assumption
        · intro e'in
          simp [v]
          assumption
      · constructor
        · simp [v]
          intro i iinI
          assumption
        · intro e' e'inv
          simp [v] at e'inv
          rw [← UeqpreV, mem_preimage]
          apply piusubV
          rw [Set.mem_pi]
          intro i iinI
          apply eq i iinI
          rw [mem_ball_iff_norm]
          exact e'inv i iinI

theorem weak_basis {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  TopologicalSpace.IsTopologicalBasis
  {U : Set (WeakSpace 𝕂 X) | ∃ (e₀ : WeakSpace 𝕂 X), ∃ (I : Finset (Dual 𝕂 X)), ∃ (ε : ℝ), (0 < ε ∧
  U = {e : WeakSpace 𝕂 X | ∀ i ∈ I, ‖i (e - e₀)‖ < ε})} := by
    apply weak_basis_general ((topDualPairing 𝕂 X).flip)

theorem weak_star_basis {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  TopologicalSpace.IsTopologicalBasis
  {U : Set (WeakDual 𝕂 X) | ∃ (f₀ : WeakDual 𝕂 X), ∃ (I : Finset X), ∃ (ε : ℝ), (0 < ε ∧
  U = {f : WeakDual 𝕂 X | ∀ i ∈ I, ‖(f - f₀) i‖ < ε})} := by
    apply weak_basis_general ((topDualPairing 𝕂 X))

/- Convergence on weak topologies -/

theorem weak_conv_nets {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) (D: Type u_1) (h: DirectedSet D) (s: D → WeakBilin B) (e : WeakBilin B) :
  Net.Limit h s e ↔ ∀ (f : F), Net.Limit h ((fun (d : WeakBilin B) ↦ B d f) ∘ s) (B e f) := by
    constructor
    · intro slimite f
      exact (Net.continuous_iff_image_of_net_converges (fun (d : WeakBilin B) ↦ B d f) e).mp
             (continuous_iff_continuousAt.mp (WeakBilin.eval_continuous B f) e) D h s slimite
    · intro hyp
      dsimp [Net.Limit]
      intro U Unhdse
      rw [TopologicalSpace.IsTopologicalBasis.mem_nhds_iff (weak_basis_general B)] at Unhdse
      rcases Unhdse with ⟨V, Vbasic, einV, VsubU⟩
      dsimp at Vbasic
      rcases Vbasic with ⟨e₀, I, ε, εpos, Vbasic⟩
      have : ∃ (d₀ : D), ∀ i ∈ I, ∀ (d : D), d₀ ≤ d → (‖(B ((s d) - e₀) i)‖ < ε) := by
        · apply aux_sup I (fun (f : F) (d : D) ↦ (∀ (d' : D), d ≤ d' → (‖(B ((s d') - e₀) f)‖ < ε)))
          intro i iinI
          have limit := hyp i
          rw [Net.Limit] at limit
          have : Metric.ball (B e i) (ε - ‖B (e - e₀) ↑i‖) ∈ 𝓝 (B e i) := by
            apply Metric.ball_mem_nhds
            rw [sub_pos]
            rw [Vbasic] at einV
            dsimp at einV
            exact einV i iinI
          rcases limit (Metric.ball (B e i) (ε - ‖B (e - e₀) ↑i‖)) this with ⟨d₀, cond⟩
          dsimp at cond
          use d₀
          intro d d₀led
          have := cond d d₀led
          rw [Metric.mem_ball] at this
          rw [LinearMap.map_sub₂, ← dist_eq_norm]
          calc
            dist (B (s d) i) (B e₀ i) ≤ dist (B (s d) i) (B e i) + dist (B e i) (B e₀ i) := by
              exact dist_triangle (B (s d) i) (B e i) (B e₀ i)
            _ < (ε - ‖B (e - e₀) i‖) + dist (B e i) (B e₀ i) := by
              apply add_lt_add_right
              assumption
            _ = ε := by
              rw [LinearMap.map_sub₂ ,← dist_eq_norm]
              simp
          · intro i iinI t s' tles' h' d' s'led'
            exact h' d' (le_trans tles' s'led')
      rcases this with ⟨d₀, eq⟩
      use d₀
      intro d d₀led
      apply VsubU
      rw [Vbasic]
      dsimp
      intro i iinI
      exact eq i iinI d d₀led

theorem weak_conv {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]
  (D: Type u_1) (h: DirectedSet D) (x: WeakSpace 𝕂 X) (s: D → WeakSpace 𝕂 X):
  Net.Limit h s x ↔ ∀ (f : WeakDual 𝕂 X), Net.Limit h (f ∘ s) (f x) := by
    exact weak_conv_nets ((topDualPairing 𝕂 X).flip) D h s x

theorem weak_star_conv {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]
  (D: Type (max u_1 u_2)) (h: DirectedSet D) (f: WeakDual 𝕂 X) (s: D → WeakDual 𝕂 X):
  Net.Limit h s f ↔ ∀ (x : WeakSpace 𝕂 X), Net.Limit h (((topDualPairing 𝕂 X).flip x) ∘ s) (f x) := by
    exact weak_conv_nets (topDualPairing 𝕂 X) D h s f

/- Weak topologies are compatible -/

theorem weak_compatible {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) : CompatibleTopology B (WeakBilin.instTopologicalSpace B) := by
    dsimp [CompatibleTopology]
    intro g
    constructor
    · intro gcont
      rw [mem_range]
      have : ∃ (H: Finset F), g ∈ Submodule.span 𝕂 (Finset.image (fun (f: F) ↦ B.flip f) H) := by
        rw [@continuous_iff_continuousAt] at gcont
        have contzero := gcont 0
        rw [@continuousAt_def] at contzero
        simp at contzero
        have := contzero (Metric.ball (0 : 𝕂) 1) (Metric.ball_mem_nhds (0 : 𝕂) (by linarith))
        rw [@mem_nhds_iff] at this
        rcases this with ⟨V, Vsubpre, Vopen, zinV⟩
        have gVsubball : g '' V ⊆ Metric.ball (0 : 𝕂) 1 := by
          intro c cinimg
          rw [mem_image] at cinimg
          rcases cinimg with ⟨v, vinV, gvc⟩
          have := Vsubpre vinV
          rw [mem_preimage] at this
          rw [← gvc]
          assumption
        rw [TopologicalSpace.IsTopologicalBasis.isOpen_iff (weak_basis_general B)] at Vopen
        rcases Vopen (0 : E) zinV with ⟨U, Uin, zinU, UsubV⟩
        rcases Uin with ⟨e₀, I, ε, εpos, Ueq⟩
        use I
        rw [mem_submodule_iff_inter_of_ker_sub_ker]
        intro e eininter
        simp only [mem_iInter] at eininter
        have : ∀ (m : 𝕂), m • e ∈ U := by
          intro m
          rw [Ueq]
          dsimp [WeakBilin]
          intro i iinI
          have : (fun f ↦ B.flip f) i ∈ Finset.image (fun f ↦ B.flip f) I := by
            rw [Finset.mem_image]
            use i
          have:= eininter _ this
          dsimp at this
          rw [LinearMap.mem_ker] at this
          dsimp [LinearMap.flip] at this
          have : B (m • e) i = 0 := by
            rw [map_smul]
            have eq : (m • B e) i = m * (B e i) := by
              rfl
            rw [eq, this]
            simp
          rw [LinearMap.map_sub₂, this, zero_sub, norm_neg]
          rw [Ueq] at zinU
          dsimp at zinU
          have := zinU i iinI
          rw [zero_sub, LinearMap.map_neg₂, norm_neg] at this
          assumption
        have : ∀ (m : ℕ), (0 < m) → ‖g e‖ < 1/m := by
          intro m mpos
          have := UsubV (this m)
          have gin : g ((@Nat.cast 𝕂 Semiring.toNatCast m) • e) ∈ g '' V := by
            rw [mem_image]
            use (@Nat.cast 𝕂 Semiring.toNatCast m) • e
          have normltone := gVsubball gin
          rw [mem_ball_iff_norm, sub_zero, map_smul, norm_smul, RCLike.norm_natCast] at normltone
          rw [lt_div_iff (by norm_num [mpos]), mul_comm]
          assumption
        dsimp
        rw [LinearMap.mem_ker, ← norm_eq_zero]
        apply Real_archimedean'' ‖g e‖ (norm_nonneg (g e)) this
      rcases this with ⟨H, gin⟩
      have : ∃ (I: Finset F), (∀ f ∈ I, ∀ f' ∈ I, B.flip f = B.flip f' → f = f') ∧
         Finset.image (fun f ↦ B.flip f) H = Finset.image (fun f ↦ B.flip f) I := by
          have : ∀ y ∈ Finset.image (fun f ↦ B.flip f) H, ∃ f ∈ H, B.flip f = y := by
            intro i iin
            rw [Finset.mem_image] at iin
            assumption
          let t : Finset.image (fun f ↦ B.flip f) H → F := fun i ↦ if h: ∃ f ∈ H, B.flip f = i then Classical.choose h else 0
          use Finset.image t Finset.univ
          constructor
          · intro f fin f' fin' eqim
            rw [Finset.mem_image] at *
            rcases fin with ⟨x, xinuniv, txf⟩
            rcases fin' with ⟨x', x'inuniv, tx'f⟩
            have condf := x.2
            have condf' := x'.2
            rw [Finset.mem_image] at *
            have : x = x' := by
              dsimp [t] at *
              rw [dif_pos condf] at txf
              rw [dif_pos condf'] at tx'f
              have c1 := (Classical.choose_spec condf).2
              have c2 := (Classical.choose_spec condf').2
              apply SetCoe.ext
              rw [← c1, ← c2, txf, tx'f]
              assumption
            rw [← txf, ← tx'f, this]
          · ext i
            constructor
            · intro iin
              rw [Finset.mem_image]
              use t ⟨i, iin⟩
              constructor
              · rw [Finset.mem_image]
                use ⟨i, iin⟩
                exact And.intro (Finset.mem_univ ⟨i, iin⟩) (by rfl)
              · rw [Finset.mem_image] at iin
                dsimp [t]
                rw [dif_pos iin]
                exact (Classical.choose_spec iin).2
            · intro iin
              rw [Finset.mem_image] at *
              rcases iin with ⟨f, fin, ieqBf⟩
              use f
              constructor
              · rw [Finset.mem_image] at fin
                rcases fin with ⟨x, xinuniv, txf⟩
                rw [← txf]
                dsimp only [t]
                have := x.2
                rw [Finset.mem_image] at this
                rw [dif_pos this]
                exact (Classical.choose_spec this).1
              · assumption
      rcases this with ⟨I, injinI, eq⟩
      rw [mem_span_finset, eq] at gin
      rcases gin with ⟨c, geq⟩
      have : ∑ i ∈ Finset.image (fun f ↦ B.flip f) I, c i • i = ∑ f ∈ I, c (B.flip f) • (B.flip f) := by
        rw [Finset.sum_image]
        assumption
      use (∑ i ∈ I, c (B.flip i) • i)
      rw [← geq, this]
      rw [map_sum]
      congr
      ext f e
      have := (B.flip).map_smul' (c (B.flip f)) f
      dsimp at this
      rw [this]
    · intro h
      rw [mem_range] at h
      rcases h with ⟨f, geqBf⟩
      rw [← geqBf]
      apply WeakBilin.eval_continuous

theorem weak_compatible_normed (𝕂 X : Type*) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] :
  CompatibleTopology ((topDualPairing 𝕂 X).flip) (@UniformSpace.toTopologicalSpace X _) := by
    dsimp [CompatibleTopology]
    intro g
    have : range (fun f ↦ (topDualPairing 𝕂 X).flip.flip f) = {f: (X →ₗ[𝕂] 𝕂) | Continuous f} := by
      ext f
      constructor
      · intro finrange
        rw [mem_range] at finrange
        rcases finrange with ⟨h, feqh⟩
        simp [topDualPairing, ContinuousLinearMap.coeLM] at feqh
        rw [← feqh]
        dsimp
        exact h.cont
      · intro fcont
        dsimp at fcont
        rw [mem_range]
        use ⟨f, fcont⟩
        simp [topDualPairing]
    rw [this]
    rfl

theorem locallyconvex_dual_pair (X: Type*) [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [TopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T1Space X] :
  DualPair ((topDualPairing ℝ X).flip) := by
    dsimp [DualPair, SepPoints]
    constructor
    · intro x fxzero
      by_contra!
      rcases geometric_hahn_banach_point_point this with ⟨f, fxltzero⟩
      rw [map_zero] at fxltzero
      have := fxzero f (mem_univ f)
      dsimp [topDualPairing] at this
      linarith
    · intro f fxzero
      ext x
      exact fxzero x (mem_univ x)
