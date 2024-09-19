import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.Normed.Module.WeakDual
import Nets.Nets_mathlib

noncomputable section

open Set Filter Topology Classical Function NormedSpace

set_option linter.unusedVariables false
set_option linter.simpsNoConstructor false


def TVS.polar {E: Type*} (𝕂 : Type*) [RCLike 𝕂]  [AddCommMonoid E] [Module 𝕂 E] [TopologicalSpace E] (A : Set E) : Set (WeakDual 𝕂 E)
 := LinearMap.polar ((topDualPairing 𝕂 E).flip) A

example {E 𝕂: Type*} [RCLike 𝕂]  [AddCommMonoid E] [Module 𝕂 E] [TopologicalSpace E] (A : Set E) :
  TVS.polar 𝕂 A = {f | ∀ e ∈ A, ‖f e‖ ≤ 1} := by
    rfl

def algDualPairing (𝕂 E: Type*) [RCLike 𝕂] [AddCommMonoid E] [Module 𝕂 E] : E →ₗ[𝕂] (E →ₗ[𝕂] 𝕂) →ₗ[𝕂] 𝕂 where
  toFun := fun e ↦ {
      toFun := fun f ↦ f e
      map_add' := by
        intro f f'
        simp
      map_smul' := by
        intro c f
        simp
      }
  map_add' := by
    intro e e'
    ext f
    dsimp
    exact f.1.2 e e'
  map_smul' := by
    intro c e
    ext f
    dsimp
    exact f.2 c e

def alg.polar {E: Type*} (𝕂 : Type*) [RCLike 𝕂]  [AddCommMonoid E] [Module 𝕂 E] (A : Set E) : Set (E →ₗ[𝕂] 𝕂) :=
  LinearMap.polar (algDualPairing 𝕂 E) A

example {E 𝕂: Type*} [RCLike 𝕂]  [AddCommMonoid E] [Module 𝕂 E] (A : Set E) :
  alg.polar 𝕂 A = {f | ∀ e ∈ A, ‖f e‖ ≤ 1} := by
    rfl

-- Set is compact iff it is compact with respect to the relative topology of every set that contains it
theorem isOpen_restricted_iff (X : Type*) [TopologicalSpace X] (s : Set X) (U : Set s) :
  IsOpen U ↔ ∃ (V : Set X), IsOpen V ∧ U = V ∩ s := by
    constructor
    · intro Uopen
      rw [isOpen_induced_iff] at Uopen
      rcases Uopen with ⟨V, Vopen, UeqV⟩
      use V
      constructor
      · assumption
      · rw [← UeqV]
        simp
        rw [inter_comm]
    · intro h
      rcases h with ⟨V, Vopen, UeqVinters⟩
      rw [isOpen_induced_iff]
      use V
      constructor
      · assumption
      · apply image_val_injective
        simp
        rw [UeqVinters]
        simp [inter_comm]

theorem nhds_restricted_iff (X : Type*) [TopologicalSpace X] (s : Set X) (x : X) (h : x ∈ s) (U : Set s) :
   U ∈ 𝓝 ⟨x, h⟩  ↔ ∃ V ∈ 𝓝 x, V ∩ s ⊆ U := by
    constructor
    · intro Unhdsr
      rw [mem_nhds_iff] at Unhdsr
      rcases Unhdsr with ⟨t, tsubU, topen, xint⟩
      rw [isOpen_restricted_iff] at topen
      rcases topen with ⟨V, Vopen, teqVs⟩
      use V
      constructor
      · rw [mem_nhds_iff]
        use V
        constructor
        · rfl
        · constructor
          · assumption
          · have : x ∈ Subtype.val '' t := by
              rw [mem_image]
              use ⟨x, h⟩
            rw [teqVs] at this
            exact this.1
      · rw [← teqVs]
        exact image_val_mono tsubU
    · intro h
      rcases h with ⟨V, Vnhds, VseqU⟩
      rw [mem_nhds_iff] at *
      rcases Vnhds with ⟨W, WsubV, Wopen, xinW⟩
      use {y : s | y.1 ∈ W}
      constructor
      · intro y yinW
        dsimp at yinW
        have : y.1 ∈ Subtype.val '' U := by
          rw [mem_image]
          use y
          constructor
          · have : y.1 ∈ Subtype.val '' U := by
              apply VseqU
              constructor
              · apply WsubV
                assumption
              · exact y.2
            rw [mem_image] at this
            rcases this with ⟨w, winU, weqy⟩
            have := SetCoe.ext weqy
            rw [← this]
            assumption
          · rfl
        rw [mem_image] at this
        rcases this with ⟨y', y'inU, y'eqy⟩
        have := SetCoe.ext y'eqy
        rw [← this]
        assumption
      · constructor
        · rw [isOpen_restricted_iff]
          use W
          constructor
          · assumption
          · ext x
            constructor
            · intro xin
              rw [mem_image] at xin
              rcases xin with ⟨x', x'inW, x'eqx⟩
              dsimp at x'inW
              rw [← x'eqx]
              exact And.intro x'inW x'.2
            · intro xinWs
              rw [mem_image]
              use ⟨x, xinWs.2⟩
              constructor
              · simp
                exact xinWs.1
              · simp
        · simp
          assumption

theorem compact_iff_relative_compact {X: Type*} [TopologicalSpace X] (K: Set X) :
  IsCompact K ↔ ∀ Y, K ⊆ Y → IsCompact {y : Y | y.1 ∈ K} := by
    rcases Classical.em (K = ∅) with Ke | Kne
    · rw [Ke]
      simp
    · constructor
      · intro Kcompact Y KsubY
        rw [Net.compact_iff_net_has_accumulationpoint] at *
        right
        intro sY sYinK
        rw [or_iff_not_imp_left] at Kcompact
        have Kcompact:= Kcompact Kne
        let s : Net X := Net.mk' (sY.directedSet) (fun d ↦ sY d)
        have sinK : ∀ (d : s.D), s d  ∈ K := by
          intro d
          dsimp [s]
          exact sYinK d
        rcases Kcompact s sinK with ⟨k, kinK, kaccps⟩
        use ⟨k, KsubY kinK⟩
        constructor
        · dsimp
          assumption
        · dsimp [Net.AccumulationPoint] at *
          intro d U Unhds
          rw [nhds_restricted_iff] at Unhds
          rcases Unhds with ⟨V, Vnhds, VinterYsubU⟩
          rcases kaccps d V Vnhds with ⟨e, dlee, seinV⟩
          use e
          constructor
          · assumption
          · have : s e ∈ V ∩ Y := by
              constructor
              · assumption
              · exact KsubY (sinK e)
            have:= VinterYsubU this
            rw [mem_image] at this
            rcases this with ⟨x', x'inU, x'eqse⟩
            have := SetCoe.ext x'eqse
            rw [← this]
            assumption
      · intro h
        have Kcompact:= h univ (subset_univ K)
        rw [Net.compact_iff_net_has_accumulationpoint] at *
        right
        rw [or_iff_not_imp_left] at Kcompact
        have : ¬{y : univ | y.1 ∈ K} = ∅ := by
          rw [← Ne, nonempty_def'] at *
          rcases Kne with ⟨y, yinK⟩
          use ⟨y, mem_univ y⟩
          dsimp
          assumption
        have Kcompact := Kcompact this
        intro s sinK
        let s' : Net univ := Net.mk' (s.directedSet) (fun d ↦ ⟨s d, mem_univ (s d)⟩)
        have s'inK : ∀ (d : s'.D), s' d ∈ {y : univ | y.1 ∈ K} := by
          intro d
          dsimp [s']
          exact sinK d
        rcases Kcompact s' s'inK with ⟨x', x'inK, x'accs'⟩
        use x'.1
        constructor
        · exact x'inK
        · dsimp [Net.AccumulationPoint] at *
          intro d U Unhds
          have : {y : univ | y.1 ∈ U} ∈ 𝓝 x' := by
            rw [nhds_restricted_iff]
            use U, Unhds
            intro x xinU
            rw [mem_image]
            use ⟨x, mem_univ x⟩
            dsimp
            exact And.intro (xinU.1) (by rfl)
          rcases x'accs' d {y : univ | y.1 ∈ U} this with ⟨e, dlee, s'einU⟩
          use e
          constructor
          · assumption
          · dsimp at s'einU
            exact s'einU

-- Restriction of dual topology of algDualPairing to WeakDual is equal to dual-star topology

def fun_corestriction_image {X Y : Type*} (f: X → Y) : X → range f := fun x ↦ ⟨f x, by use x⟩

lemma eval_fun_corestriction_image {X Y : Type*} (f: X → Y) (x : X) : (fun_corestriction_image f) x = f x := by
  dsimp [fun_corestriction_image]

lemma preimage_corestriction_eq_preimage {X Y : Type*} (f: X → Y) (s: Set (range f)) :
  (fun_corestriction_image f) ⁻¹' s = f ⁻¹' s := by
    ext x
    constructor
    · intro xin
      rw [mem_preimage, mem_image] at *
      dsimp [fun_corestriction_image] at xin
      use ⟨f x, by use x⟩
    · intro xin
      rw [mem_preimage, mem_image] at *
      dsimp [fun_corestriction_image]
      rcases xin with ⟨y, yins, yeqfx⟩
      have : y = ⟨f x, by use x⟩ := by
        exact SetCoe.ext yeqfx
      rw [← this]
      assumption

lemma image_corestriction_eq_image {X Y : Type*} (f: X → Y) (s: Set X) :
  (fun_corestriction_image f) '' s = f '' s := by
    ext y
    constructor
    · intro yin
      rw [mem_image] at *
      rcases yin with ⟨z, zin, zeqy⟩
      rw [mem_image] at zin
      rcases zin with ⟨w, wins, fweqz⟩
      dsimp [fun_corestriction_image] at fweqz
      use w
      constructor
      · assumption
      · rw [← zeqy]
        exact congr_arg Subtype.val fweqz
    · intro yin
      rw [mem_image] at *
      rcases yin with ⟨x, xins, yeqfx⟩
      use ⟨f x, by use x⟩
      constructor
      · rw [mem_image]
        use x
        constructor
        · assumption
        · simp [fun_corestriction_image]
      · rw [← yeqfx]

theorem homeomorph_into_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f: X → Y) (h₁: Injective f) (h₂: IsOpenMap f) (h₃: Continuous f):
  IsHomeomorph (fun_corestriction_image f) := by
    constructor
    · rw [continuous_def]
      intro s sopen
      rw [preimage_corestriction_eq_preimage]
      rw [isOpen_restricted_iff] at sopen
      rcases sopen with ⟨V, Vopen, seqVrf⟩
      rw [seqVrf]
      simp
      rw [continuous_def] at h₃
      exact h₃ _ Vopen
    · dsimp [IsOpenMap]
      intro U Uopen
      rw [isOpen_restricted_iff]
      rw [image_corestriction_eq_image f U]
      use f '' U
      constructor
      · exact h₂ U Uopen
      · simp
    · constructor
      · intro x x' eqim
        dsimp [fun_corestriction_image] at eqim
        have := congr_arg Subtype.val eqim
        dsimp at this
        exact h₁ this
      · intro y
        rcases y.2 with ⟨x, fxeqy⟩
        use x
        dsimp [fun_corestriction_image]
        exact SetCoe.ext fxeqy

def inclusion_topdual_algdual (𝕂 E: Type*) [RCLike 𝕂] [AddCommMonoid E] [Module 𝕂 E] [TopologicalSpace E] : WeakDual 𝕂 E → WeakBilin ((algDualPairing 𝕂 E).flip) :=
  fun f ↦ ContinuousLinearMap.toLinearMap f

#check WeakDual.polar

theorem inclusion_topdual_algdual_ishomeomorph {𝕂 E: Type*} [RCLike 𝕂] [AddCommMonoid E] [Module 𝕂 E] [TopologicalSpace E] :
  IsHomeomorph (fun_corestriction_image (inclusion_topdual_algdual 𝕂 E)) := by
    constructor
    · sorry
    · intro U Uopen
      rw [isOpen_induced_iff] at Uopen
      rw [isOpen_restricted_iff]
      rcases Uopen with ⟨V, Vopen, UeqpreV⟩
      have : (fun x y ↦ ((topDualPairing 𝕂 E) x) y) ⁻¹' V = {f : E →L[𝕂] 𝕂 | f.toFun ∈ V} := by
        ext f
        constructor
        · intro h
          rw [mem_preimage] at h
          simp
          exact h
        · intro h
          rw [mem_preimage]
          simp at h
          exact h
      have : U = {f : E →L[𝕂] 𝕂 | f.toFun ∈ V} := by
        rw [← this]
        apply UeqpreV.symm
      let V' := {f : E →ₗ[𝕂] 𝕂 | f.toFun ∈ V}
      use V'
      constructor
      · rw [isOpen_induced_iff]
        use V
        constructor
        · assumption
        · ext f
          constructor
          · intro h
            dsimp [V', WeakBilin]
            rw [mem_preimage] at h
            dsimp [algDualPairing] at h
            exact h
          · intro h
            rw [mem_preimage]
            dsimp [algDualPairing]
            dsimp [V', WeakBilin] at h
            exact h
      · ext f
        constructor
        · intro h
          rw [mem_image] at h
          rcases h with ⟨g, gin, geqf⟩
          rw [mem_image] at gin
          rcases gin with ⟨f', f'inU, f'eqg⟩
          constructor
          · dsimp [V', WeakBilin]
            dsimp [fun_corestriction_image, inclusion_topdual_algdual] at f'eqg
            rw [← geqf, ← f'eqg]
            simp
            rw [this] at f'inU
            dsimp [WeakDual, WeakBilin] at f'inU
            assumption
          · rw [mem_range]
            use f'
            dsimp [inclusion_topdual_algdual]
            dsimp [fun_corestriction_image, inclusion_topdual_algdual] at f'eqg
            rw [← geqf, ← f'eqg]
        · intro ⟨finV', finrange⟩
          rw [mem_image]
          use ⟨f, finrange⟩
          constructor
          · rw [mem_image]
            dsimp [V', WeakBilin] at finV'
            rcases finrange with ⟨g, geqf⟩
            dsimp [inclusion_topdual_algdual] at geqf
            use g
            constructor
            · rw [this]
              dsimp [WeakDual, WeakBilin]
              have := congr_arg (fun (f: E →ₗ[𝕂] 𝕂) ↦ f.toFun) geqf
              dsimp at this
              rw [this]
              assumption
            · apply SetCoe.ext
              dsimp [fun_corestriction_image, inclusion_topdual_algdual]
              assumption
          · simp
    · constructor
      · intro f f' eqim
        dsimp [WeakDual, WeakBilin]
        ext x
        have := congr_arg (Subtype.val) eqim
        rw [eval_fun_corestriction_image, eval_fun_corestriction_image] at this
        dsimp [inclusion_topdual_algdual] at this
        exact congr_arg (fun (f: E →ₗ[𝕂] 𝕂) ↦ f x) this
      · intro g
        rcases g.2 with ⟨f, feqg⟩
        use f
        ext
        rw [eval_fun_corestriction_image]
        dsimp [inclusion_topdual_algdual] at *
        assumption



-- Coercion WeakDual to linear maps

lemma lemma1 {E 𝕂: Type*} [RCLike 𝕂]  [AddCommMonoid E] [Module 𝕂 E] [TopologicalSpace E] (A : Set E) (h: Balanced 𝕂 A) :
  alg.polar 𝕂 A = {f | ∃ g ∈ TVS.polar 𝕂 A, f.toFun = g.toFun} := by sorry


theorem AB {E 𝕂: Type*} [RCLike 𝕂]  [AddCommMonoid E] [Module 𝕂 E] [TopologicalSpace E] (A : Set E) :
  IsCompact (TVS.polar 𝕂 A) := by
    sorry
