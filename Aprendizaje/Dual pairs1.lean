import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Bases
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.Algebra.Group.Defs

noncomputable section

open Set Filter Topology Classical Function Module

set_option linter.unusedVariables false
set_option linter.simpsNoConstructor false

/- A vector space is a module where the ring is a field and the set an additive commutative group -/
--variable (𝕂 E F: Type) [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]

/- Algebraic dual of vector space -/

--example : Dual 𝕂 E = (E →ₗ[𝕂] 𝕂) := by rfl

/- Definition of bilineal forms -/

structure BilinearForm (E F 𝕂 : Type) [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F] where
  toFun : E → F → 𝕂
  right_linear : ∀ (f : F), IsLinearMap 𝕂 (fun (e : E) ↦ toFun e f)
  left_linear : ∀ (e : E), IsLinearMap 𝕂 (fun (f : F) ↦ toFun e f)

instance [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F] :
  CoeFun (BilinearForm E F 𝕂) (fun _ ↦ E → F → 𝕂) where
    coe := BilinearForm.toFun

attribute [coe] BilinearForm.toFun

lemma map_add_right {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (e e' : E) (f : F) : B (e + e') f = B e f + B e' f := by
    exact (B.right_linear f).1 e e'

lemma map_add_left {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (e : E) (f f' : F) : B e (f + f') = B e f + B e f' := by
    exact (B.left_linear e).1 f f'

lemma map_smul_right {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (c : 𝕂) (e : E) (f : F) : B (c • e) f = c • B e f := by
    exact (B.right_linear f).2 c e

lemma map_smul_left {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (c : 𝕂) (e : E) (f : F) : B e (c • f) = c • B e f := by
    exact (B.left_linear e).2 c f

lemma map_neg_right {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (e : E) (f : F) : B (-e) f = - B e f := by
    rw [← neg_one_smul 𝕂 e, map_smul_right B (-1) e f, neg_one_smul 𝕂 (B e f)]

lemma map_neg_left {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (e : E) (f : F) : B e (-f) = - B e f := by
    rw [← neg_one_smul 𝕂 f, map_smul_left B (-1) e f, neg_one_smul 𝕂 (B e f)]

lemma map_sub_right {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (e e' : E) (f : F) : B (e - e') f = B e f - B e' f := by
    rw [sub_eq_add_neg, sub_eq_add_neg, map_add_right, map_neg_right]

lemma map_sub_left {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (e : E) (f f' : F) : B e (f - f') = B e f - B e f' := by
    rw [sub_eq_add_neg, sub_eq_add_neg, map_add_left, map_neg_left]

lemma linear_zero_eq_zero {E F R : Type} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F] (f: E → F) (h: IsLinearMap R f):
  f 0 = 0 := by
    rw [← add_neg_cancel (0 : E), h.1, ← neg_one_smul R (0 : E), h.2, neg_one_smul R, add_neg_cancel]

lemma zero_right {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (f : F) : B 0 f = 0 := by
    rw [← add_neg_cancel (0 : E), ← sub_eq_add_neg, map_sub_right, sub_self]

lemma zero_left {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B : BilinearForm E F 𝕂) (e : E) : B e 0 = 0 := by
    rw [← add_neg_cancel (0 : F), ← sub_eq_add_neg, map_sub_left, sub_self]

theorem linear_inj_iff_ker_null {E F R : Type} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F] (f: E → F) (h: IsLinearMap R f):
  Injective f ↔ {e : E | f e = 0} ⊆ {(0 : E)} := by
    constructor
    · intro finj
      intro x xinker
      dsimp at xinker
      simp
      rw [← linear_zero_eq_zero f h] at xinker
      exact finj xinker
    · intro kernull
      dsimp [Injective]
      intro e e' fee'eq
      have : e - e' ∈ {e | f e = 0} := by
        simp
        rw [sub_eq_add_neg, h.1, ← neg_one_smul R e', h.2, neg_one_smul, fee'eq ,add_neg_cancel]
      have := kernull this
      simp at this
      have := congr_arg (· + e') this
      dsimp at this
      rw [zero_add, sub_add, sub_self, sub_zero] at this
      assumption

--lemma map_sub' {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
-- (f : E → F) (h: IsLinearMap 𝕂 f) :

instance BilinearForm' {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
                       (B : BilinearForm E F 𝕂) : BilinearForm F E 𝕂 where
  toFun := fun f e ↦ B e f
  right_linear := B.left_linear
  left_linear := B.right_linear

/- Defition of separating set -/

def SepPoints (E F : Type) {𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (S : Set F) (B : BilinearForm E F 𝕂) : Prop := ∀ (e : E), (∀ s ∈ S, B e s = 0) → e = 0

/- Associated map to a bilineal form -/

def AsocMap {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
            (B : BilinearForm E F 𝕂) : E → Dual 𝕂 F := fun e ↦
            {
              toFun := fun f ↦ B e f
              map_add' := by
                intro f f'
                dsimp
                exact (B.left_linear e).1 f f'
              map_smul' := by
                intro k f
                dsimp
                exact (B.left_linear e).2 k f
            }

theorem isLinearAsocMap {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
            (B : BilinearForm E F 𝕂) : IsLinearMap 𝕂 (AsocMap B) := by
              constructor
              · intro e e'
                ext f
                dsimp [AsocMap]
                exact (B.right_linear f).1 e e'
              · intro k e
                ext f
                dsimp [AsocMap]
                exact (B.right_linear f).2 k e

/- Weak topology on vector space E associated to a bilineal form B : E × F → 𝕂 and a subset H ⊆ F -/

def TopologicalSpace.instInitial {ι: Type} (X : Type) (Y : ι → Type u) (h : ∀ (i : ι), TopologicalSpace (Y i))
  (F: (i : ι) → (X → (Y i))) : TopologicalSpace X where
    IsOpen U := ∀ x ∈ U, ∃ (G : Finset {U | ∃ (i : ι) (V : Set (Y i)), IsOpen V ∧ U = (F i) ⁻¹' V}), (∀ g ∈ G, x ∈ g.1) ∧ {y | ∀ g ∈ G, y ∈ g.1} ⊆ U
    isOpen_univ := by
      dsimp
      intro x xinuniv
      use ∅
      simp
    isOpen_inter := by
      dsimp
      intro U V U_open V_open x xinUV
      rcases U_open x xinUV.1 with ⟨GU, GUeq⟩
      rcases V_open x xinUV.2 with ⟨GV, GVeq⟩
      use GU ∪ GV
      constructor
      · intro g ginUV
        rw [Finset.mem_union] at ginUV
        rcases ginUV with ginU | ginV
        · exact GUeq.1 g ginU
        · exact GVeq.1 g ginV
      · intro y yin
        have interinU := GUeq.2
        have interinV := GVeq.2
        dsimp at yin
        constructor
        · apply interinU
          dsimp
          intro g' g'inGU
          exact yin g' (Finset.mem_union_left GV g'inGU)
        · apply interinV
          dsimp
          intro g' g'inGV
          exact yin g' (Finset.mem_union_right GU g'inGV)
    isOpen_sUnion := by
      dsimp
      intro s h x xinUs
      rcases xinUs with ⟨t, tins, xint⟩
      rcases h t tins x xint with ⟨G, eq⟩
      use G
      constructor
      · exact eq.1
      · apply le_trans eq.2
        intro z zint
        use t

lemma TopologicalSpace.instInitial.isOpen {ι: Type} {X : Type} {Y : ι → Type u} {h : ∀ (i : ι), TopologicalSpace (Y i)}
  {F: (i : ι) → (X → (Y i))} (U: Set X) : @IsOpen X (TopologicalSpace.instInitial X Y h F) U ↔ ∀ x ∈ U, ∃ (G : Finset {U | ∃ (i : ι) (V : Set (Y i)), IsOpen V ∧ U = (F i) ⁻¹' V}), (∀ g ∈ G, x ∈ g.1) ∧ {y | ∀ g ∈ G, y ∈ g.1} ⊆ U := by
    rfl

def TopologicalSpace.instInitial' {ι: Type} (X : Type) (Y : ι → Type u) (h : ∀ (i : ι), TopologicalSpace (Y i))
  (F: (i : ι) → (X → (Y i))) : TopologicalSpace X := TopologicalSpace.generateFrom {U | ∃ (i : ι) (V : Set (Y i)), IsOpen V ∧ U = (F i) ⁻¹' V}

def TopologicalSpace.instInitial'' {ι: Type} (X : Type) (Y : ι → Type u) (h : ∀ (i : ι), TopologicalSpace (Y i))
  (F: (i : ι) → (X → (Y i))) : TopologicalSpace X := ⨅ (i : ι), TopologicalSpace.induced (F i) (h i)

lemma eq1 {ι: Type} (X : Type) (Y : ι → Type u) (h : ∀ (i : ι), TopologicalSpace (Y i))
  (F: (i : ι) → (X → (Y i))) : TopologicalSpace.instInitial X Y h F = TopologicalSpace.instInitial' X Y h F := by
    have : @TopologicalSpace.IsTopologicalBasis X (TopologicalSpace.instInitial' X Y h F)
      ((fun (f : Set (Set X)) => ⋂₀ f) '' {f : Set (Set X) | f.Finite ∧ f ⊆ {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V}}) := by
        apply @TopologicalSpace.isTopologicalBasis_of_subbasis X (TopologicalSpace.instInitial' X Y h F) {U | ∃ (i : ι) (V : Set (Y i)), IsOpen V ∧ U = (F i) ⁻¹' V} _
        rfl
    ext U
    constructor
    · intro Uopen
      rw [@TopologicalSpace.IsTopologicalBasis.isOpen_iff X (TopologicalSpace.instInitial' X Y h F) U (((fun f => ⋂₀ f) '' {f | f.Finite ∧ f ⊆ {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V}})) this]
      rw [TopologicalSpace.instInitial.isOpen] at Uopen
      intro a ainU
      rcases Uopen a ainU with ⟨G, aininter, interinU⟩
      use {y | ∀ g ∈ G, y ∈ g.1}
      constructor
      · rw [mem_image]
        let H := {x : Set X | ∃ g ∈ G, x = g.1}
        use H
        constructor
        · dsimp
          constructor
          · let G' := Finset.image (fun g ↦ g.1) G
            have := Finset.finite_toSet G'
            have : G'.toSet = H := by
              ext U
              constructor
              · intro UinG'
                norm_cast at UinG'
                dsimp [G'] at UinG'
                rw [Finset.mem_image] at UinG'
                dsimp [H]
                rcases UinG' with ⟨g, eq⟩
                use g
                constructor
                · exact eq.1
                · exact eq.2.symm
              · intro UinH
                norm_cast
                dsimp [G']
                rw [Finset.mem_image]
                dsimp [H] at UinH
                rcases UinH with ⟨a, eq⟩
                use a
                constructor
                · exact eq.1
                · exact eq.2.symm
            rw [← this]
            assumption
          · intro U UinH
            dsimp
            dsimp [H] at UinH
            rcases UinH with ⟨g, ginG, Ueqg⟩
            have := g.2
            rw [← Ueqg] at this
            assumption
        · ext x
          constructor
          · intro xininter
            rw [mem_sInter] at xininter
            dsimp
            intro g ginG
            have : g.1 ∈ H := by
              dsimp [H]
              use g
            exact xininter g.1 this
          · intro xin
            dsimp at xin
            rw [mem_sInter]
            intro t tinH
            dsimp [H] at tinH
            rcases tinH with ⟨g, ginG, teqg⟩
            rw [teqg]
            exact xin g ginG
      · constructor
        · dsimp
          assumption
        · assumption
    · intro Uopen2
      rw [TopologicalSpace.instInitial.isOpen]
      rw [@TopologicalSpace.IsTopologicalBasis.isOpen_iff X (TopologicalSpace.instInitial' X Y h F) U (((fun f => ⋂₀ f) '' {f | f.Finite ∧ f ⊆ {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V}})) this] at Uopen2
      intro x xinU
      rcases Uopen2 x xinU with ⟨V, Vin, xinV, VsubU⟩
      rw [mem_image] at Vin
      rcases Vin with ⟨G'', G''in, VeqinterG''⟩
      dsimp at G''in
      let G' := {U : {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V} | U.1 ∈ G''}
      have G'finite : G'.Finite := by
        let H' := image (fun g ↦ g.1) G'
        have : G'' = H' := by
          ext U
          constructor
          · intro UinG''
            dsimp [H']
            rw [mem_image]
            have := G''in.2 UinG''
            use ⟨U, this⟩
            simp [G']
            assumption
          · intro UinH'
            dsimp [H'] at UinH'
            rw [mem_image] at UinH'
            rcases UinH' with ⟨W, WinG', WeqU⟩
            dsimp [G'] at WinG'
            rw [← WeqU]
            assumption
        have G''finite := G''in.1
        rw [this] at G''finite
        apply Set.Finite.of_finite_image G''finite
        dsimp [InjOn]
        intro U UinG' W WinG' UeqW
        apply SetCoe.ext
        assumption
      let G := Set.Finite.toFinset G'finite
      use G
      constructor
      · intro g ginG
        dsimp [G] at ginG
        have : g ∈ G' := by
          rw [Finite.mem_toFinset G'finite] at ginG
          assumption
        dsimp [G'] at this
        rw [← VeqinterG'', mem_sInter] at xinV
        apply xinV g.1 this
      · intro y yin
        dsimp at yin
        apply VsubU
        rw [← VeqinterG'', mem_sInter]
        intro t tinG''
        have condt := G''in.2 tinG''
        dsimp at condt
        have tinG': ⟨t, condt⟩ ∈ G' := by
          dsimp [G']
          assumption
        have : ⟨t, condt⟩ ∈ G := by
          rw [Finite.mem_toFinset G'finite]
          assumption
        exact yin ⟨t, condt⟩ this

theorem same_basis_same_topology {X : Type} {t₁: TopologicalSpace X} {t₂: TopologicalSpace X} (s: Set (Set X)) :
   @TopologicalSpace.IsTopologicalBasis X t₁ s ∧ @TopologicalSpace.IsTopologicalBasis X t₂ s → t₁ = t₂ := by
    intro ⟨base1, base2⟩
    ext U
    constructor
    · intro open1U
      rw [TopologicalSpace.IsTopologicalBasis.isOpen_iff base2]
      rw [@TopologicalSpace.IsTopologicalBasis.isOpen_iff X t₁ U s base1] at open1U
      assumption
    · intro open2U
      rw [TopologicalSpace.IsTopologicalBasis.isOpen_iff base2] at open2U
      rw [@TopologicalSpace.IsTopologicalBasis.isOpen_iff X t₁ U s base1]
      assumption

lemma eq2 {ι: Type} (X : Type) (Y : ι → Type u) (h : ∀ (i : ι), TopologicalSpace (Y i))
  (F: (i : ι) → (X → (Y i))) : TopologicalSpace.instInitial' X Y h F = TopologicalSpace.instInitial'' X Y h F := by
    have Base': @TopologicalSpace.IsTopologicalBasis X (TopologicalSpace.instInitial' X Y h F)
      ((fun (f : Set (Set X)) => ⋂₀ f) '' {f : Set (Set X) | f.Finite ∧ f ⊆ {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V}}) := by
        apply @TopologicalSpace.isTopologicalBasis_of_subbasis X (TopologicalSpace.instInitial' X Y h F) {U | ∃ (i : ι) (V : Set (Y i)), IsOpen V ∧ U = (F i) ⁻¹' V} _
        rfl
    have Base'': @TopologicalSpace.IsTopologicalBasis X (TopologicalSpace.instInitial'' X Y h F)
      ((fun (f : Set (Set X)) => ⋂₀ f) '' {f : Set (Set X) | f.Finite ∧ f ⊆ ⋃ i, {s | @IsOpen X (TopologicalSpace.induced (F i) (h i)) s}}) := by
        apply @TopologicalSpace.isTopologicalBasis_of_subbasis X (TopologicalSpace.instInitial'' X Y h F) (⋃ i, {s | @IsOpen X (TopologicalSpace.induced (F i) (h i)) s}) _
        dsimp [TopologicalSpace.instInitial'']
        rw [← generateFrom_iUnion_isOpen (fun (i : ι) ↦ TopologicalSpace.induced (F i) (h i))]
    have : @TopologicalSpace.IsTopologicalBasis X (TopologicalSpace.instInitial'' X Y h F)
      ((fun (f : Set (Set X)) => ⋂₀ f) '' {f : Set (Set X) | f.Finite ∧ f ⊆ {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V}}) := by
        apply @TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds X (TopologicalSpace.instInitial'' X Y h F)
          ((fun (f : Set (Set X)) => ⋂₀ f) '' {f : Set (Set X) | f.Finite ∧ f ⊆ {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V}})
        · intro U Uin
          rw [@TopologicalSpace.IsTopologicalBasis.isOpen_iff X (TopologicalSpace.instInitial'' X Y h F) U ((fun f => ⋂₀ f) '' {f | f.Finite ∧ f ⊆ ⋃ i, {s | @IsOpen X (TopologicalSpace.induced (F i) (h i)) s}}) Base'']
          intro u uinU
          rw [mem_image] at Uin
          rcases Uin with ⟨s, sin, Ueqinters⟩
          dsimp at sin
          use U
          constructor
          · rw [mem_image]
            use s
            constructor
            · dsimp
              constructor
              · exact sin.1
              · intro V Vins
                rw [mem_iUnion]
                have := sin.2 Vins
                dsimp at this
                rcases this with ⟨i, W, Wopen, VpreW⟩
                use i
                dsimp
                rw [isOpen_induced_iff]
                use W
                exact And.intro Wopen VpreW.symm
            · assumption
          · exact And.intro uinU (by rfl)
        · intro x U xinU Uopen
          rw [@TopologicalSpace.IsTopologicalBasis.isOpen_iff X (TopologicalSpace.instInitial'' X Y h F) U ((fun f => ⋂₀ f) '' {f | f.Finite ∧ f ⊆ ⋃ i, {s | @IsOpen X (TopologicalSpace.induced (F i) (h i)) s}}) Base''] at Uopen
          rcases Uopen x xinU with ⟨V, Vin, xinV, VsubU⟩
          use V
          constructor
          · rw [mem_image] at *
            rcases Vin with ⟨s, sin, Veqinters⟩
            dsimp at sin
            use s
            constructor
            · dsimp
              constructor
              · exact sin.1
              · intro W WinS
                dsimp
                have := sin.2 WinS
                rw [mem_iUnion] at this
                rcases this with ⟨i, Win⟩
                dsimp at Win
                rw [isOpen_induced_iff] at Win
                rcases Win with ⟨t, topen, Weqpret⟩
                use i, t
                exact And.intro topen Weqpret.symm
            · assumption
          · exact And.intro xinV VsubU
    apply same_basis_same_topology ((fun f => ⋂₀ f) '' {f | f.Finite ∧ f ⊆ {U | ∃ i V, IsOpen V ∧ U = F i ⁻¹' V}})
    exact And.intro Base' this



instance RCLike.instTopologicalSpace {𝕂 : Type} [RCLike 𝕂] : TopologicalSpace 𝕂 := RCLike.toDenselyNormedField.toNormedField.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace


/- Para que fuera una instancia habría que hacer algo parecido a lo del "WeakBilin", porque si no
   Lean no puede encotrar F 𝕂 y B a partir solo de E -/
def WeakTopology (E : Type) {F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F] (B: BilinearForm E F 𝕂) (H : Set F) : TopologicalSpace E :=
                        TopologicalSpace.instInitial E (fun (h : H) ↦ 𝕂)
                        (by intro i; dsimp; exact RCLike.instTopologicalSpace)
                        (fun (h : H) ↦ (AsocMap (BilinearForm' B) h))

def AsocMap' {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
            (B : BilinearForm E F 𝕂) (H: Set F) : E → (H → 𝕂) := fun e ↦ (fun h ↦ B e h)

theorem isLinearAsocMap' {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
            (B : BilinearForm E F 𝕂) (H: Set F) : IsLinearMap 𝕂 (AsocMap' B H) := by
              constructor
              · intro e e'
                ext f
                dsimp [AsocMap']
                exact (B.right_linear f).1 e e'
              · intro k e
                ext f
                dsimp [AsocMap']
                exact (B.right_linear f).2 k e

def WeakBilin' {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F] (B: BilinearForm E F 𝕂) (H: Set F) := E

instance WeakBilin'.instTopologicalSpace {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F] (B : BilinearForm E F 𝕂) (H : Set F) :
TopologicalSpace (WeakBilin' B H) := TopologicalSpace.induced (AsocMap' B H) Pi.topologicalSpace

/- -------- COSAS -------- -/


def homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f: X → Y) (hf: IsHomeomorph f) : X ≃ₜ Y where
  toFun := f
  invFun := (Equiv.ofBijective f hf.3).invFun
  left_inv := (Equiv.ofBijective f hf.3).left_inv
  right_inv := (Equiv.ofBijective f hf.3).right_inv
  continuous_toFun := hf.1
  continuous_invFun := by
    dsimp
    rw [continuous_def]
    intro U Uopen
    have : (Equiv.ofBijective f hf.3).symm ⁻¹' U = f '' U := by
      ext y
      constructor
      · intro h
        rw [mem_image]
        rw [mem_preimage] at h
        use (Equiv.ofBijective f hf.3).symm y, h
        apply (Equiv.ofBijective f hf.3).right_inv
      · intro h
        rw [mem_image] at h
        rw [mem_preimage]
        rcases h with ⟨x, xinU, fxeqy⟩
        rw [← fxeqy]
        have : (Equiv.ofBijective f hf.3).symm (f x) = x := by
          apply (Equiv.ofBijective f hf.3).left_inv
        rw [this]
        assumption
    rw [this]
    exact hf.2 U Uopen

def RestrictedFun {X Y: Type} (f : X → Y) (Z : Set X) : Z → Y := fun z ↦ f z

def CoRestrictedFun {X Y: Type} (f : X → Y) (Z : Set Y) (h: range f ⊆ Z) : X → {y | y ∈ Z} := fun x ↦
  ⟨f x, (by dsimp; apply h; rw [mem_range]; use x)⟩

def CoRestrictedFunR {X Y: Type} (f : X → Y) : X → range f := fun x ↦
  ⟨f x, (by use x)⟩

/- Posible prueba de "isOpen_iff"

theorem Inducing.isOpen {X Y : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f: X → Y) (h : Inducing f) :
  ∀ (U : Set X), IsOpen U ↔ ∃ (V : Set Y), IsOpen V ∧ U= f ⁻¹' V := by
    intro U
    constructor
    · intro Uopen
      rw [h.induced] at Uopen
      rcases Uopen with ⟨V, Vopen, Veq⟩
      use V
      exact And.intro Vopen Veq.symm
    · intro h'
      rcases h' with ⟨V, Vopen, UeqpreV⟩
      rw [h.induced]
      use V
      exact And.intro Vopen UeqpreV.symm -/

theorem isOpen_restricted {X : Type} [TopologicalSpace X] (s : Set X) (U : Set s) :
  IsOpen U ↔ ∃ (V : Set X), IsOpen V ∧ U = V ∩ s := by
    constructor
    · intro Uopen
      rcases Uopen with ⟨V, Vopen, Upresub⟩
      use V
      constructor
      · exact Vopen
      · ext x
        constructor
        · intro xinimg
          rw [mem_image] at xinimg
          rcases xinimg with ⟨y, yinU, yeqx⟩
          rw [← Upresub, mem_preimage] at yinU
          rw [← yeqx]
          exact And.intro yinU y.2
        · intro xininter
          rw [mem_image]
          let y : {x // x ∈ s} := ⟨x, xininter.2⟩
          have : y ∈ U := by
            rw [← Upresub, mem_preimage]
            dsimp
            exact xininter.1
          use y
    · intro h
      rcases h with ⟨V, Vopen, eqVs⟩
      use V
      constructor
      ·  exact Vopen
      · ext y
        rw [mem_preimage]
        constructor
        · intro yinV
          have : y.1 ∈ V ∩ s := by
            exact And.intro yinV y.2
          rw [← eqVs, mem_image] at this
          rcases this with ⟨z, zinU, zeqy⟩
          have: y = z := by
            apply SetCoe.ext
            exact zeqy.symm
          rw [this]
          assumption
        · intro yinU
          have : y.1 ∈ Subtype.val '' U := by
            rw [mem_image]
            use y
          rw [eqVs] at this
          exact this.1

theorem inj_inducing_is_homeomorphism {X Y : Type} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] (f: X → Y) :
  Inducing f ∧ Injective f → IsHomeomorph (CoRestrictedFunR f) := by
    intro ⟨find, finj⟩
    constructor
    · rw [continuous_def]
      intro V Vopen
      rw [Inducing.isOpen_iff find]
      rw [isOpen_restricted] at Vopen
      rcases Vopen with ⟨t, topen, tinteq⟩
      use t
      constructor
      · exact topen
      · ext x
        constructor
        · intro h
          rw [mem_preimage] at *
          dsimp [CoRestrictedFunR]
          have : f x ∈ t ∩ range f := by
            constructor
            · exact h
            · use x
          rw [← tinteq, mem_image] at this
          rcases this with ⟨y, yinV, yeqfx⟩
          have : y = ⟨f x, (by use x)⟩ := by
            apply SetCoe.ext
            dsimp
            assumption
          rw [← this]
          assumption
        · intro h
          rw [mem_preimage] at *
          dsimp [CoRestrictedFunR] at h
          have : f x ∈ Subtype.val '' V := by
            rw [mem_image]
            use ⟨f x, (by use x)⟩
          rw [tinteq] at this
          exact this.1
    · dsimp [IsOpenMap]
      intro U Uopen
      rw [isOpen_restricted]
      rw [find.induced] at Uopen
      rcases Uopen with ⟨V, Vopen, UeqpreV⟩
      use V
      constructor
      · exact Vopen
      · ext y
        constructor
        · intro h
          rw [mem_image] at h
          rcases h with ⟨x, xinim, xeqy⟩
          rw [mem_image] at xinim
          rcases xinim with ⟨u, uinU, xeqfu⟩
          rw [← UeqpreV, mem_preimage] at uinU
          dsimp [CoRestrictedFunR] at xeqfu
          have : x.1 = f u := by
            rw [← xeqfu]
          rw [← xeqy, this]
          constructor
          · assumption
          · use u
        · intro ⟨yinV, yinf⟩
          rw [mem_image]
          use ⟨y, yinf⟩
          constructor
          · rw [mem_image]
            dsimp [CoRestrictedFunR]
            rcases yinf with ⟨x, yeqfx⟩
            rw [← yeqfx] at yinV
            have : x ∈ U := by
              rw [← UeqpreV, mem_preimage]
              assumption
            use x, this
            apply SetCoe.ext
            dsimp
            assumption
          · simp
    · constructor
      · dsimp [Injective]
        intro x x' eqim
        dsimp [CoRestrictedFunR] at eqim
        apply finj
        simp at eqim
        assumption
      · dsimp [Surjective]
        intro b
        rcases b.2 with ⟨a, faeqb⟩
        use a
        dsimp [CoRestrictedFunR]
        apply SetCoe.ext
        dsimp
        assumption

/- -------- FIN COSAS -------- -/

theorem weak_T2_iff_bil_inj {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F] (B : BilinearForm E F 𝕂) (H : Set F) :
  T2Space (WeakBilin' B H) ↔ Injective (AsocMap' B H) := by
    constructor
    · intro T2
      rw [t2Space_iff, Pairwise] at T2
      rw [linear_inj_iff_ker_null _ (isLinearAsocMap' B H)]
      by_contra cont
      simp at cont
      rcases cont with ⟨e, einker, enez⟩
      rcases T2 enez with ⟨U, V, Uopen, Vopen, einU, zinV, UVdisj⟩
      rcases Uopen with ⟨A, Aopen, UeqpreA⟩
      have : (0 : E) ∈ U := by
        rw [← UeqpreA]
        simp
        rw [linear_zero_eq_zero _ (isLinearAsocMap' B H), ← einker, ← Set.mem_preimage, UeqpreA]
        assumption
      rw [disjoint_iff_inter_eq_empty] at UVdisj
      have: (0 : E) ∈ U ∩ V := by
        exact And.intro this zinV
      rw [UVdisj] at this
      contradiction
    · intro inj
      have : @IsHomeomorph E (range (AsocMap' B H)) (WeakBilin'.instTopologicalSpace B H) _ (CoRestrictedFunR (AsocMap' B H)) := by
        apply @inj_inducing_is_homeomorphism E (H → 𝕂) (WeakBilin'.instTopologicalSpace B H) (Pi.topologicalSpace) (AsocMap' B H)
        constructor
        · have : WeakBilin'.instTopologicalSpace B H = TopologicalSpace.induced (AsocMap' B H) Pi.topologicalSpace := by
            rfl
          rw [@inducing_iff E (H → 𝕂) (WeakBilin'.instTopologicalSpace B H) (Pi.topologicalSpace) (AsocMap' B H)]
          exact this
        · assumption
      let f := @homeomorph E (range (AsocMap' B H)) (WeakBilin'.instTopologicalSpace B H) _ (CoRestrictedFunR (AsocMap' B H)) this
      let g := @Homeomorph.symm E (range (AsocMap' B H)) (WeakBilin'.instTopologicalSpace B H) _ f
      have : T2Space (range (AsocMap' B H)) := by
        infer_instance
      dsimp [WeakBilin']
      apply @Homeomorph.t2Space (range (AsocMap' B H)) E _ (WeakBilin'.instTopologicalSpace B H) this g

theorem weak_inj_iff_separate {E F 𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F] (B : BilinearForm E F 𝕂) (H : Set F) :
  Injective (AsocMap' B H) ↔ SepPoints E F H B:= by
    constructor
    · intro inj
      dsimp [SepPoints]
      intro e cond
      have AsocMapez : AsocMap' B H e = 0 := by
        ext s
        dsimp [AsocMap']
        exact cond s.1 s.2
      have AsocMapz : AsocMap' B H 0 = 0 := by
        apply linear_zero_eq_zero (AsocMap' B H) (isLinearAsocMap' B H)
      rw [← AsocMapez] at AsocMapz
      exact inj AsocMapz.symm
    · intro sep
      rw [linear_inj_iff_ker_null (AsocMap' B H) (isLinearAsocMap' B H)]
      simp
      intro e'' ime''z
      dsimp [SepPoints] at sep
      have : ∀ s ∈ H, B e'' s = 0 := by
        intro s sinH
        have := congr_arg (fun (F : H → 𝕂) ↦ F ⟨s, sinH⟩) ime''z
        dsimp [AsocMap'] at this
        assumption
      exact sep e'' this

/- Definition of dual pair -/

def DualPair (E F : Type) {𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
                   (B: BilinearForm E F 𝕂) : Prop := SepPoints E F univ B ∧ SepPoints F E univ (BilinearForm' B)


/- REDES OTRA VEZ PQ NO SE IMPORTAR ARCHIVOS -/

/-! ### Direceted sets and net definitions -/

/- We define a net as an structure that includes a directed set D (with the condition that is nonempty)
   and a function form D to X-/

/- Definition of (nonempty) directed set -/
class DirectedSet (D: Type) extends Preorder D, Inhabited D where
  directed : ∀ (d e : D), ∃ (f : D), d ≤ f ∧ e ≤ f

namespace DirectedSet

/- Default element in any directed set -/
def default' (D: Type) [DirectedSet D] := @Inhabited.default D toInhabited

-- Any finite set on a directed set has a supremum
theorem sup_finite_set {D : Type} [DirectedSet D] (I : Finset D): ∃ (d: D), ∀ c ∈ I, c ≤ d := by
  induction' I using Finset.induction_on with d I dninI ih
  · simp
  · simp
    rcases ih with ⟨d₀, leI⟩
    rcases DirectedSet.directed d d₀ with ⟨d₁, ledd₀⟩
    use d₁
    apply And.intro (ledd₀.1) _
    intro a ainI
    exact le_trans (leI a ainI) ledd₀.2

end DirectedSet

/- Definition of net -/
structure Net (X: Type) where
  D: Type
  [directedSet: DirectedSet D]
  net : D → X

/- It includes in the typeclass inference system the assertion that the domain of a net
   is a directed set, so that Lean can synthesized it when needed -/
attribute [instance] Net.directedSet

namespace Net
open Net

/-! ### Definitions about nets -/

def Limit {X: Type} [TopologicalSpace X] (s : Net X) (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ (d₀ : s.D), ∀ (d : s.D), d₀ ≤ d → s.net d ∈ U

def AccumulationPoint {X: Type} [TopologicalSpace X] (s: Net X) (x : X): Prop :=
  ∀ (d : s.D), ∀ U ∈ 𝓝 x, ∃ (e : s.D), (d ≤ e ∧ s.net e ∈ U)

def Subnet {X: Type} [TopologicalSpace X] (s s': Net X) : Prop :=
  ∃ (i: s'.D → s.D), (∀ (d : s.D), ∃ (e₀ : s'.D), ∀ (e : s'.D), (e₀ ≤ e →  d ≤ (i e))) ∧
  s'.net = s.net ∘ i

def mk' {X: Type} {D: Type} (h: DirectedSet D) (s: D → X) : Net X :=
{
  D := D
  directedSet := h
  net := s
}

-- The set of neighbourhoods of a point x (ordered by ⊇) is a directed set

@[simps]
instance Preorder.SetSubLeft (X : Type) : Preorder (Set X) where
  toLE := {le := fun U ↦ (fun V ↦ V ⊆ U)}
  toLT := {lt := fun U ↦ (fun V ↦ V ⊆ U ∧ ¬ U ⊆ V)}
  le_refl := by
    intro U
    exact le_refl U
  le_trans := by
    intro U V W UleV VleW
    exact subset_trans VleW UleV
  lt_iff_le_not_le := by
    intro U V
    constructor
    repeat
      intro h
      exact h

instance DirectedSet.instNeighbourhoodLeft {X: Type} [TopologicalSpace X] (x : X) : DirectedSet {U | U ∈ 𝓝 x} where
  toPreorder := @Subtype.preorder (Set X) (Preorder.SetSubLeft X) (fun U => U ∈ 𝓝 x)
  default := ⟨univ, univ_mem⟩
  directed := by
    intro d e
    use ⟨d.1 ∩ e.1, inter_mem d.2 e.2⟩
    constructor
    · apply inter_subset_left
    · apply inter_subset_right

@[simps]
instance instNeighbourhoodLeft {X: Type} [TopologicalSpace X] (x : X) (s: {U | U ∈ 𝓝 x} → X) : Net X :=
  Net.mk' (DirectedSet.instNeighbourhoodLeft x) s

@[simps]
def function {X Y: Type} (s : Net X) (f: X → Y) : Net Y := Net.mk' (s.directedSet) (fun (d: s.D) ↦ f (s.net d))

theorem continuous_iff_image_of_net_converges {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f: X → Y) (x : X):
  ContinuousAt f x ↔ ∀ (s : Net X), Limit s x → Limit (function s f) (f x) := by
    constructor
    · intro fcontatx
      intro s slimitx
      dsimp [Limit] at *
      intro U Unhdsfx
      dsimp [ContinuousAt] at fcontatx
      rw [tendsto_def] at fcontatx
      rcases slimitx (f ⁻¹' U) (fcontatx U Unhdsfx) with ⟨d₀, eq⟩
      use d₀
      intro d d₀led
      have := eq d d₀led
      rw [mem_preimage] at this
      assumption
    · intro h
      dsimp [ContinuousAt]
      rw [tendsto_def]
      by_contra! fnotcontatx
      rcases fnotcontatx with ⟨W, Wnhdsfx, prenotnhdsx⟩
      have existence : ∀ U ∈ 𝓝 x, ∃ u ∈ U, f u ∉ W := by
        intro U Unhds
        have: ¬ (U  ⊆ f ⁻¹' W) := by
          by_contra!
          have : f ⁻¹' W ∈ 𝓝 x := by
            apply mem_of_superset Unhds this
          contradiction
        rw [not_subset] at this
        rcases this with ⟨u, uinU, eq⟩
        rw [mem_preimage] at eq
        use u
      let r : {U | U ∈ 𝓝 x} → X := fun U ↦ if h: ∃ u ∈ U.1, f u ∉ W then Classical.choose h else x
      let s : Net X := Net.instNeighbourhoodLeft x r
      have slimitx : Limit s x := by
        dsimp [Limit]
        intro U Unhdsx
        use ⟨U, Unhdsx⟩
        intro V UleV
        dsimp [s] at UleV
        dsimp [s, r]
        rw [dif_pos (existence V.1 V.2)]
        apply UleV (Classical.choose_spec (existence V.1 V.2)).1
      have fsnotlimitx : ¬ Limit (function s f) (f x) := by
        dsimp [Limit]
        push_neg
        use W, Wnhdsfx
        intro d
        use d
        constructor
        · rfl
        · dsimp [s, r]
          rw [dif_pos (existence d.1 d.2)]
          exact (Classical.choose_spec (existence d.1 d.2)).2
      have := h s slimitx
      contradiction


end Net

/- --------------------------------------------------------------- -/

def partial_fun {α β: Type} (p : α → Prop) (f : α → β) (g: α → β) (a : α) : β :=
  if p a then
    f a
  else
    g a

/- Producto cartesiano general -/

/- Dados s : Set ι y t: (i : ι) → Set (α ι) (con α : ι → Type), Set.pi s t devuelve un subconjunto de
   (i : ι) → α i, tal que si f está en dicho conjunto, entonces para cada i ∈ s, f i ∈ t i.
   Tomando s = univ se obtiene el producto cartesiano "completo" -/
--#check Set.pi
--#check mem_pi
--#check mem_univ_pi

theorem aux_max {ι α : Type} [DirectedSet α] (I: Finset ι) (p: ι → α → Prop) (h: ∀ i ∈ I, ∃ (t : α), p i t)
  (h' : ∀ i ∈ I, ∀ (t s : α), t ≤ s → p i t → p i s) : ∃ (t : α), ∀ i ∈ I, p i t := by
    let F : ι → α := fun i ↦ if q: ∃ (t : α), p i t then Classical.choose q else DirectedSet.default' α
    let T := Finset.image F I
    rcases DirectedSet.sup_finite_set T with ⟨t, tsubT⟩
    use t
    intro i iinI
    have FiinT : F i ∈ T := by
      dsimp [T]
      rw [Finset.mem_image]
      use i
    have : p i (F i) := by
      dsimp [F]
      rw [dif_pos (h i iinI)]
      exact Classical.choose_spec (h i iinI)
    exact h' i iinI (F i) t (tsubT (F i) FiinT) this

theorem aux_min {ι α : Type} [LinearOrder α] [N: Nonempty α] (I: Finset ι) (p: ι → α → Prop) (h: ∀ i ∈ I, ∃ (t : α), p i t)
  (h' : ∀ i ∈ I, ∀ (t s : α), t ≤ s → p i s → p i t) : ∃ (t : α), ∀ i ∈ I, p i t := by
    rcases N with ⟨a₀⟩
    rcases Classical.em (I.Nonempty) with Ine | Ie
    · let F : ι → α := fun i ↦ if q: ∃ (t : α), p i t then Classical.choose q else a₀
      let T := Finset.image F I
      have Tnem: T.Nonempty := by
        apply Finset.Nonempty.image
        assumption
      let a := Finset.min' T Tnem
      have ainT: a ∈ T := by
        apply Finset.min'_mem
      dsimp [T] at ainT
      rw [Finset.mem_image] at ainT
      rcases ainT with ⟨i₀, i₀inI, aeqFi₀⟩
      use a
      intro i iinI
      apply h' i iinI a (F i)
      · have : F i ∈ T := by
          dsimp [T]
          rw [Finset.mem_image]
          use i
        exact Finset.min'_le T (F i) this
      · dsimp [F]
        rw [dif_pos (h i iinI)]
        exact Classical.choose_spec (h i iinI)
    · rw [Finset.not_nonempty_iff_eq_empty] at Ie
      use a₀
      rw [Ie]
      intro i iinI
      contradiction

theorem aux {ι X : Type} [MetricSpace X] (I: Finset ι) (f: ι → X) (u: ι → Set X) (h: ∀ i ∈ I, ∃ (t : ℝ), (0 < t ∧ Metric.ball (f i) t ⊆ u i)):
  ∃ (ε : ℝ), (0 < ε ∧ ∀ i ∈ I, Metric.ball (f i) ε ⊆ u i) := by
    rcases Classical.em (I.Nonempty) with Inem | Iem
    · let F : ι → ℝ := fun i ↦ if p: ∃ t, 0 < t ∧ Metric.ball (f i) t ⊆ u i then Classical.choose p else 0
      let T := Finset.image F I
      have Tnem: T.Nonempty := by
        apply Finset.Nonempty.image
        assumption
      let ε := Finset.min' T Tnem
      have εinT: ε ∈ T := by
        apply Finset.min'_mem
      dsimp [T] at εinT
      rw [Finset.mem_image] at εinT
      rcases εinT with ⟨i₀, i₀inI, εeqFi₀⟩
      use ε
      constructor
      · dsimp [F] at εeqFi₀
        rw [dif_pos (h i₀ i₀inI)] at εeqFi₀
        have := Classical.choose_spec (h i₀ i₀inI)
        rw [← εeqFi₀]
        exact this.1
      · intro i iinI
        let t := F i
        have : 0 < t ∧ Metric.ball (f i) t ⊆ u i := by
          dsimp [t, F]
          rw [dif_pos (h i iinI)]
          exact Classical.choose_spec (h i iinI)
        apply subset_trans _ this.2
        apply Metric.ball_subset_ball
        have tinT : t ∈ T := by
          rw [Finset.mem_image]
          use i, iinI
        exact Finset.min'_le T t tinT
    · rw [Finset.not_nonempty_iff_eq_empty] at Iem
      use 1
      constructor
      · linarith
      · intro i iinI
        rw [Iem] at iinI
        contradiction

theorem weak_basis {E F : Type} {𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: BilinearForm E F 𝕂) (H: Set F) : TopologicalSpace.IsTopologicalBasis
    {U : Set (WeakBilin' B H) | ∃ (e₀ : E), ∃ (I : Finset H), ∃ (ε : ℝ), (0 < ε ∧
     U = {e : E | ∀ i ∈ I, ‖(B (e - e₀) i)‖ < ε})} := by
      apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
      · intro UU UUin
        dsimp at UUin
        rcases UUin with ⟨e₀, I, ε, εpos, UUeq⟩
        let V := {G : H → 𝕂 | ∀ h : H, h ∈ I → ‖(G h) - B e₀ h‖ < ε}
        use V
        constructor
        · rw [isOpen_pi_iff]
          intro f finV
          dsimp [V] at finV
          use I
          let u : H → Set 𝕂 := fun (f : H) ↦ partial_fun (fun (h : H) ↦ h ∈ I)
            (fun (h : H) ↦ {t : 𝕂 | ‖t - B e₀ f‖ < ε}) (fun (h : H) ↦ univ) f
          have evalu : ∀ h ∈ I, u h = {t : 𝕂 | ‖t - B e₀ h‖ < ε} := by
            intro h hinI
            dsimp [u, partial_fun]
            simp
            intro h'
            contradiction
          use u
          constructor
          · intro i inI
            rw [evalu i inI]
            dsimp
            constructor
            · rw [Metric.isOpen_iff]
              intro s sin
              dsimp at sin
              rw [← dist_eq_norm] at sin
              use (ε - dist s (B e₀ ↑i))
              constructor
              · linarith
              · intro x xin
                rw [Metric.mem_ball] at xin
                dsimp
                rw [← dist_eq_norm]
                have := dist_triangle x s (B e₀ i)
                calc
                  dist x (B e₀ ↑i) ≤ dist x s + dist s (B e₀ ↑i) := by
                    exact this
                  _ < (ε - dist s (B e₀ ↑i)) + dist s (B e₀ ↑i) := by
                    rw [add_lt_add_iff_right]
                    exact xin
                  _ = ε := by
                    rw [sub_add, sub_self, sub_zero]
            · exact finV i inI
          · intro f finpi
            rw [Set.mem_pi] at finpi
            intro i iinI
            have := finpi i iinI
            rw [evalu i iinI] at this
            exact this
        · ext U
          rw [mem_preimage]
          constructor
          · intro AsocinV
            dsimp [V] at AsocinV
            rw [UUeq]
            dsimp [WeakBilin']
            dsimp [AsocMap'] at AsocinV
            intro i iinI
            have := AsocinV i iinI
            dsimp [WeakBilin'] at U
            rw [map_sub_right]
            assumption
          · intro UinUU
            rw [UUeq] at UinUU
            dsimp [WeakBilin'] at UinUU
            dsimp [V, AsocMap']
            intro i iinI
            have := UinUU i iinI
            rw [← map_sub_right]
            assumption
      · intro e₀ U einU uOpen
        dsimp [WeakBilin'] at e₀
        rcases uOpen with ⟨V, Vopen, upre⟩
        rw [isOpen_pi_iff] at Vopen
        have : (AsocMap' B H) e₀ ∈ V := by
          rw [← upre, mem_preimage] at einU
          assumption
        rcases Vopen ((AsocMap' B H) e₀) this with ⟨I, u, opens, sub⟩
        have : ∃ (ε : ℝ), (0 < ε ∧ ∀ i ∈ I, Metric.ball (B e₀ i) ε ⊆ u i) := by
          have existence : ∀ i ∈ I, ∃ (t : ℝ), (0 < t ∧ Metric.ball (B e₀ i) t ⊆ u i) := by
            intro i iinI
            have := (opens i iinI).1
            rw [Metric.isOpen_iff] at this
            rcases this (AsocMap' B H e₀ i) (opens i iinI).2 with ⟨t, tpos, ball_sub_ui⟩
            use t, tpos
            dsimp [AsocMap'] at ball_sub_ui
            assumption
          apply aux
          exact existence
        rcases this with ⟨ε, εpos, ball_sub⟩
        let v := {e : E | ∀ i ∈ I, ‖(B (e - e₀) i)‖ < ε}
        use v
        constructor
        · dsimp
          use e₀, I, ε, εpos
        · constructor
          · dsimp [v, WeakBilin']
            intro i iinI
            simp
            rw [zero_right]
            simp
            exact εpos
          · intro e einv
            dsimp [v, WeakBilin'] at einv
            rw [← upre, mem_preimage]
            dsimp [WeakBilin'] at e
            have : ∀ i ∈ I, (B e i) ∈ u i := by
              intro i iinI
              have : (B e i) ∈ Metric.ball (B e₀ i) ε := by
                rw [Metric.mem_ball, dist_eq_norm, ← map_sub_right]
                exact einv i iinI
              exact ball_sub i iinI this
            have : (AsocMap' B H) e ∈ Set.pi I u := by
              rw [Set.mem_pi]
              dsimp [AsocMap']
              exact this
            exact sub this

theorem continuous_proj {E F : Type} {𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: BilinearForm E F 𝕂) (H: Set F) : ∀ h ∈ H, Continuous (fun (e : WeakBilin' B H) ↦ B e h) := by
    intro h hinH
    rw [continuous_iff_continuousAt]
    intro e₀
    dsimp [WeakBilin'] at e₀
    dsimp [ContinuousAt]
    rw [tendsto_def]
    intro V Vnhds
    rw [TopologicalSpace.IsTopologicalBasis.mem_nhds_iff (weak_basis B H)]
    rw [Metric.mem_nhds_iff] at Vnhds
    rcases Vnhds with ⟨ε, εpos, ball_sub_V⟩
    let U := {e : E | ‖B (e - e₀) h‖ < ε}
    use U
    constructor
    · dsimp
      use e₀, {⟨h, hinH⟩}, ε
      constructor
      · exact εpos
      · ext e
        constructor
        · intro einU
          dsimp [U] at einU
          dsimp
          intro i iin
          simp at iin
          rw [iin]
          dsimp
          assumption
        · intro ein
          dsimp at ein
          dsimp [U]
          have := ein ⟨h, hinH⟩ (by simp)
          dsimp at this
          assumption
    · constructor
      · dsimp [U, WeakBilin']
        rw [sub_self, zero_right]
        simp
        exact εpos
      · intro e einU
        dsimp [WeakBilin'] at e
        rw [mem_preimage]
        apply ball_sub_V
        rw [Metric.mem_ball, dist_eq_norm, ← map_sub_right]
        dsimp [U, WeakBilin'] at einU
        assumption

theorem weak_conv_nets {E F : Type} {𝕂 : Type} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: BilinearForm E F 𝕂) (H: Set F) (s: Net (WeakBilin' B H)) (e : E) : Net.Limit s e ↔ ∀ h ∈ H, Net.Limit (Net.function s (fun (e' : WeakBilin' B H) ↦ B e' h)) (B e h) := by
    dsimp [WeakBilin'] at s
    constructor
    · intro slimite h hinH
      have := (continuous_proj B H) h hinH
      rw [continuous_iff_continuousAt] at this
      have := this e
      rw [Net.continuous_iff_image_of_net_converges] at this
      have := this s slimite
      assumption
    · intro hyp
      dsimp [Net.Limit]
      intro U Unhdse
      rw [TopologicalSpace.IsTopologicalBasis.mem_nhds_iff (weak_basis B H)] at Unhdse
      rcases Unhdse with ⟨V, Vbasic, einV, VsubU⟩
      dsimp at Vbasic
      rcases Vbasic with ⟨e₀, I, ε, εpos, Vbasic⟩
      dsimp [WeakBilin'] at U
      dsimp [WeakBilin'] at V
      have : ∃ (d₀ : s.D), ∀ i ∈ I, ∀ (d : s.D), d₀ ≤ d → (‖(B ((s.net d) - e₀) i)‖ < ε) := by
        · apply aux_max I (fun (h : H) (d : s.D) ↦ (∀ (d' : s.D), d ≤ d' → (‖(B ((s.net d') - e₀) h)‖ < ε) ))
          intro i iinI
          have limit := hyp i.1 i.2
          rw [Net.Limit] at limit
          have : Metric.ball (B e i) (ε - ‖B (e - e₀) ↑i‖) ∈ 𝓝 (B e i) := by
            apply Metric.ball_mem_nhds
            simp
            rw [Vbasic] at einV
            dsimp [WeakBilin'] at einV
            exact einV i iinI
          rcases limit (Metric.ball (B e i) (ε - ‖B (e - e₀) ↑i‖)) this with ⟨d₀, cond⟩
          dsimp at cond
          use d₀
          intro d d₀led
          have := cond d d₀led
          rw [Metric.mem_ball] at this
          rw [map_sub_right ,← dist_eq_norm]
          calc
            dist (B (s.net d) i) (B e₀ i) ≤ dist (B (s.net d) i) (B e i) + dist (B e i) (B e₀ i) := by
              exact dist_triangle (B (s.net d) i) (B e i) (B e₀ i)
            _ < (ε - ‖B (e - e₀) i‖) + dist (B e i) (B e₀ i) := by
              apply add_lt_add_right
              assumption
            _ = ε := by
              rw [map_sub_right ,← dist_eq_norm]
              simp
          · intro i iinI t s' tles' h' d' s'led'
            exact h' d' (le_trans tles' s'led')
      rcases this with ⟨d₀, eq⟩
      use d₀
      intro d d₀led
      apply VsubU
      rw [Vbasic]
      dsimp [WeakBilin']
      intro i iinI
      exact eq i iinI d d₀led

notation:25 X"*["𝕂"]" => ContinuousLinearMap (RingHom.id 𝕂) X 𝕂

instance BilinearForm.instNormedSpace (X 𝕂 : Type) [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X]:
  BilinearForm X (X*[𝕂]) 𝕂 where
    toFun := fun x f ↦ f x
    right_linear := by
      intro f
      constructor
      · intro x y
        dsimp
        exact f.toLinearMap.map_add' x y
      · intro c x
        dsimp
        exact f.toLinearMap.map_smul' c x
    left_linear := by
      intro e
      constructor
      · intro f g
        simp
      · intro c f
        dsimp

def Weak (𝕂 X : Type) [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X] := WeakBilin' (BilinearForm.instNormedSpace X 𝕂) univ

instance {𝕂 X : Type} [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X] : TopologicalSpace (Weak 𝕂 X) := by
  dsimp [Weak]
  apply inferInstance

def eval {𝕂 X : Type} [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X] (f: X*[𝕂]): Weak 𝕂 X → 𝕂 := fun x ↦ f x

theorem weak_conv (𝕂 X : Type) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]
  (s : Net (Weak 𝕂 X)) (x : Weak 𝕂 X) : Net.Limit s x ↔ ∀ (f : X*[𝕂]), Net.Limit (Net.function s (eval f)) (f x) := by
    have := weak_conv_nets (BilinearForm.instNormedSpace X 𝕂) (univ) s x
    dsimp [BilinearForm.instNormedSpace] at this
    constructor
    · intro slimitx f
      rw [this] at slimitx
      exact slimitx f (mem_univ f)
    · intro h
      rw [this]
      intro f finuniv
      exact h f

def Weak_star (𝕂 X : Type) [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X] := WeakBilin' (BilinearForm' (BilinearForm.instNormedSpace X 𝕂)) univ

instance [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X] :
  CoeFun (Weak_star 𝕂 X) (fun _ ↦ X → 𝕂) where
    coe := by
      dsimp [Weak_star, WeakBilin']
      exact fun f x ↦ f x

instance {𝕂 X : Type} [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X] : TopologicalSpace (Weak_star 𝕂 X) := by
  dsimp [Weak_star]
  apply inferInstance

def eval_star {𝕂 X : Type} [RCLike 𝕂] [SeminormedAddCommGroup X] [NormedSpace 𝕂 X] (x : X): Weak_star 𝕂 X → 𝕂 := fun f ↦ f x

theorem weak_star_conv (𝕂 X : Type) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]
  (s : Net (Weak_star 𝕂 X)) (f : Weak_star 𝕂 X) : Net.Limit s f ↔ ∀ (x : X), Net.Limit (Net.function s (eval_star x)) (f x) := by
    have := weak_conv_nets (BilinearForm' (BilinearForm.instNormedSpace X 𝕂)) (univ) s f
    dsimp [BilinearForm', BilinearForm.instNormedSpace] at this
    constructor
    · intro slimitf x
      rw [this] at slimitf
      exact slimitf x (mem_univ f)
    · intro h
      rw [this]
      intro x xinuniv
      exact h x
