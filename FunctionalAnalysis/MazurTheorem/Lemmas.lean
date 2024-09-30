import Mathlib.Topology.Instances.Real
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Analysis.Normed.Module.Dual
import FunctionalAnalysis.MazurTheorem.Defs
import Topology.Nets.Nets

noncomputable section

open Set Filter Topology Classical Function Defs

set_option linter.unusedVariables false
set_option trace.Meta.Tactic.simp false

namespace Lemmas

/- Evaluation of a partial function if the condition is satisfied. -/
lemma eval_pos (p : α → Prop) (f g : α → β) {a : α} (h: p a) : partial_fun p f g a = f a := by
  rw [partial_fun, ite_eq_then]
  intro npn
  contradiction

/- Evaluation of a partial function if the condition is not satisfied. -/
lemma eval_neg (p : α → Prop) (f g : α → β) {a : α} (h: ¬p a) : partial_fun p f g a = g a := by
  rw [partial_fun, ite_eq_else]
  intro npn
  contradiction

/- Lemma: Let E, F, G be vector spaces over a field 𝕜 and f: E → G, g: E → F linear maps. Then, it exists a linear map h: F → G
          such that f = h ∘ g if, and only if, Ker g ⊆ Ker f -/
lemma exist_comp_iff_ker_sub {E F G 𝕜: Type*} [Field 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
  (f: E →ₗ[𝕜] G) (g: E →ₗ[𝕜] F) : (∃ (h: F →ₗ[𝕜] G), f = h ∘ₗ g) ↔ {e | e ∈ LinearMap.ker g} ⊆ {e | e ∈ LinearMap.ker f} := by
    constructor
    · intro existence
      rcases existence with ⟨h, feqhg⟩
      intro e einkerg
      /- If e ∈ Ker g, then g e = 0, so f e = h (g e) = h 0 = 0 as h is a linear map. -/
      simp at *
      rw [feqhg]
      dsimp [LinearMap.comp]
      rw [einkerg, LinearMap.map_zero]
    · intro kergsubkerf
      /- If we define h': g[E] → G as h' (g e) = f e, we have that it is well defined because given x ∈ g[E], if there exists
         two different elements e₁, e₂ ∈ E with x = g e₁ and x = g e₂, then g (e₁ - e₂) = 0, so e₁ - e₂ ∈ Ker g ⊆ Ker f and we
         obtain that f e₁ = f e₂. To conclude the proof we just have to extend h' to some linear map h: F → G.  -/
      let s: (LinearMap.range g) → E := fun (x : LinearMap.range g) ↦ if h: ∃ (e: E), g e = x then Classical.choose h else 0 -- For every x ∈ g[E] we select an e ∈ E such that x = g e
      let h': (LinearMap.range g) →ₗ[𝕜] G := {
        toFun := f ∘ s
        map_add' := by
          intro x x'
          simp
          have xinrangeg := x.2
          have x'inrangeg := x'.2
          /- As the range of a linear map is a submodule we have that x+x' ∈ g[E] -/
          have xx'inrangeg : (x.1 + x'.1) ∈ LinearMap.range g := by
            rw [Submodule.add_mem_iff_right _ x.2]
            exact x'.2
          rw [LinearMap.mem_range] at *
          dsimp [s]
          rw [dif_pos xinrangeg, dif_pos x'inrangeg, dif_pos xx'inrangeg] -- g (choose xinrangeg) = x, g (choose x'inrangeg) = x', g (choose xx'inrangeg) = x + x'
          /- We have that g (choose xx'inrangeg - (choose xinrangeg + choose x'inrangeg)) = 0 by the selection of these elements and
             the linearity of g, so  choose xx'inrangeg - (choose xinrangeg + choose x'inrangeg) ∈ Ker g and, by assumption,
             choose xx'inrangeg - (choose xinrangeg + choose x'inrangeg) ∈ Ker f.
             By the linearity of f we conclude as wanted. -/
          have : choose xx'inrangeg - (choose xinrangeg + choose x'inrangeg) ∈ LinearMap.ker f := by
            apply kergsubkerf
            simp [Classical.choose_spec xinrangeg, Classical.choose_spec x'inrangeg, Classical.choose_spec xx'inrangeg]
          rw [LinearMap.mem_ker, map_sub, map_add, sub_eq_zero] at this
          assumption
        map_smul' := by
          intro c x
          simp
          have xinrangeg := x.2
          /- As the range of a linear map is a submodule we have that c • x ∈ g[E] -/
          have cxinrangeg : c • x.1 ∈ LinearMap.range g := by
            exact Submodule.smul_mem _ c x.2
          rw [LinearMap.mem_range] at *
          dsimp [s]
          rw [dif_pos xinrangeg, dif_pos cxinrangeg] -- g (choose xinrangeg) = x, g (choose cxinrangeg) = c • x
          /- We have that g (choose cxinrangeg - (c • choose xinrangeg)) = 0 by the selection of these elements and
             the linearity of g, so choose cxinrangeg - (c • choose xinrangeg) ∈ Ker g and, by assumption,
             choose cxinrangeg - (c • choose xinrangeg) ∈ Ker f.
             By the linearity of f we conclude as wanted. -/
          have : choose cxinrangeg - (c • choose xinrangeg) ∈ LinearMap.ker f := by
            apply kergsubkerf
            simp [Classical.choose_spec xinrangeg, Classical.choose_spec cxinrangeg]
          rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
          assumption
          }
      /- We have that h' (g e) = f (s (g e)) = f e -/
      have eqcomp : ∀ (e: E), f e = h' (⟨g e, by rw [LinearMap.mem_range]; use e⟩) := by
        intro e
        dsimp [h', s]
        have cond : ∃ e', g e' = g e := by
          use e
        rw [dif_pos cond] -- g (choose cond) = g e
        /- To obtain the desired result it is enough to prove that e - (choose cond) ∈ Ker f and, by assumption, it is enough
           to prove that e - (choose cond) ∈ Ker g, which is true by the selection done. -/
        have : choose cond - e ∈ LinearMap.ker f := by
          apply kergsubkerf
          simp [Classical.choose_spec cond]
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
        exact this.symm
      /- We define the linear extension of h' -/
      have extension : ∃ (h: F →ₗ[𝕜] G), ∀ (x : LinearMap.range g), h x.1 = h' x := by
        rcases LinearMap.exists_extend h' with ⟨h, hcircinceqh'⟩
        use h
        intro x
        rw [← hcircinceqh']
        rfl
      rcases extension with ⟨h, hexth'⟩
      use h
      ext e
      simp
      rw [hexth' ⟨g e, by rw [LinearMap.mem_range]; use e⟩]
      exact eqcomp e

lemma mem_submodule_iff_inter_of_ker_sub_ker {E 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] (f: E →ₗ[𝕂] 𝕂) (F: Finset (E →ₗ[𝕂] 𝕂)):
  f ∈ Submodule.span 𝕂 F ↔ ⋂ g ∈ F, LinearMap.ker g ⊆ {e | e ∈ LinearMap.ker f} := by
    constructor
    · intro finspan
      rw [mem_span_finset] at finspan
      rcases finspan with ⟨u, feqsum⟩
      intro e eininter
      simp only [mem_iInter] at eininter
      dsimp
      rw [LinearMap.mem_ker]
      simp at eininter
      have := congr_arg (fun (g: E →ₗ[𝕂] 𝕂) ↦ g e) feqsum
      dsimp at this
      rw [← this]
      have : ∀ i ∈ F, ((u i) • i) e = 0 := by
        intro i iinF
        have := eininter i iinF
        dsimp
        rw [this, mul_zero]
      rw [LinearMap.sum_apply]
      exact Finset.sum_eq_zero this
    · intro h
      have : ∀ (t : E →ₗ[𝕂] 𝕂), t ∈ F ↔ t ∈ (Finset.toSet F) := by
        intro t
        rfl
      have Ffinite := Set.Finite.ofFinset F this
      rw [← Set.finite_coe_iff, finite_iff_exists_equiv_fin] at Ffinite
      rcases Ffinite with ⟨n, eq⟩
      rcases eq with ⟨T⟩
      have T := T.symm
      let r : E →ₗ[𝕂] (Fin n → 𝕂) := {
        toFun := fun e ↦ (fun i ↦ (T i).1 e)
        map_add' := by
          intro e e'
          ext i
          exact (T i).1.map_add' e e'
        map_smul' := by
          intro c e
          ext i
          exact (T i).1.map_smul' c e
        }
      have :  ⋂ g ∈ F, LinearMap.ker g = {e | e ∈ LinearMap.ker r} := by
        ext e
        constructor
        · intro eininter
          simp at *
          dsimp [r]
          ext i
          have := eininter (T i) (T i).2
          assumption
        · intro einkerr
          simp only [mem_iInter]
          intro i iinF
          dsimp at *
          rw [LinearMap.mem_ker] at *
          dsimp [r] at einkerr
          let j : Fin n := T.invFun ⟨i, iinF⟩
          have := congr_arg (fun (t: Fin n → 𝕂) ↦ t j) einkerr
          dsimp [j] at this
          have aux := congr_arg (fun (x: F) ↦ x.1 e) (Equiv.apply_symm_apply T ⟨i, iinF⟩)
          dsimp at aux
          simp
          rw [← aux, this]
      rw [this, ← exist_comp_iff_ker_sub] at h
      rcases h with ⟨h, feqhr⟩
      rw [feqhr]
      rw [mem_span_set']
      use n
      let R : Fin n → (Fin n → 𝕂) := fun i ↦ (fun (j : Fin n) ↦ partial_fun (fun (j : Fin n) ↦ j = i)
        (fun (j : Fin n) ↦ (1: ℝ)) (fun (j: Fin n) ↦ (0: ℝ)) j)
      have generator : ∀ (t: Fin n → 𝕂), t = ∑ i : Fin n, (t i) • R i := by
        intro t
        ext j
        have : (∑ i : Fin n, (t i) • R i) j =  ∑ i : Fin n, (t i) • (R i j) := by
          simp
        rw [this]
        have : j ∈ Finset.univ := by
          exact Finset.mem_univ j
        have := Finset.sum_erase_add Finset.univ (fun (i: Fin n) ↦ t i • R i j) this
        rw [← this]
        dsimp
        have : ∀ i ∈ Finset.univ.erase j, t i * R i j = 0 := by
          intro i iinerase
          rw [Finset.mem_erase] at iinerase
          dsimp [R]
          rw [eval_neg]
          · norm_cast
            rw [mul_zero]
          · exact iinerase.1.symm
        rw [Finset.sum_eq_zero this, zero_add]
        dsimp [R]
        rw [eval_pos]
        · norm_cast
          rw [mul_one]
        · rfl
      use h ∘ R, T
      ext e
      dsimp [LinearMap.comp]
      rw [generator (r e), map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr
      · rfl
      · intro i iinuniv
        simp [r]
        rw [mul_comm]

theorem exists_ball_subset_family {ι : Type*} (X: Type*) [MetricSpace X] (I : Finset ι) (f : ι → X) (u : ι → Set X)
    (h: ∀ i ∈ I, ∃ (t : ℝ), (0 < t ∧ Metric.ball (f i) t ⊆ u i)):
    ∃ (ε : ℝ), (0 < ε ∧ ∀ i ∈ I, Metric.ball (f i) ε ⊆ u i) := by
  choose t ht using h
  by_cases hI : Finset.Nonempty I
  · rcases Finset.exists_min_image Finset.univ (fun i : I ↦ t i.1 i.2) (by simp [hI]) with ⟨j, jinuniv, jmin⟩
    use t j.1 j.2
    constructor
    · exact (ht j j.2).1
    · intro i iinI
      have : Metric.ball (f i) (t j.1 j.2) ⊆ Metric.ball (f i) (t i iinI) := by
        exact Metric.ball_subset_ball (jmin ⟨i, iinI⟩ (Finset.mem_univ ⟨i, iinI⟩))
      exact subset_trans this (ht i iinI).2
  · rw [Finset.nonempty_iff_ne_empty, Ne, not_not] at hI
    use 1
    constructor
    · linarith
    · rw [hI]
      intro i iinI
      contradiction

theorem aux_sup {ι α : Type*} [DirectedSet α] (I: Finset ι) (p: ι → α → Prop) (h: ∀ i ∈ I, ∃ (t : α), p i t)
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

theorem Real_archimedean' (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  simpa using exists_lt_nsmul x_pos y

theorem Real_archimedean'' (x: ℝ) (h₁: 0 ≤ x) (h₂: ∀ (m : ℕ), (0 < m) → x < 1/m) : x = 0 := by
  by_contra! xnz
  have xpos: 0 < x := by
    exact lt_of_le_of_ne h₁ (Ne.symm xnz)
  rcases Real_archimedean' x 1 xpos with ⟨n, oneltnx⟩
  have : 0 < n := by
    by_contra! neqz
    rw [Nat.le_zero] at neqz
    rw [neqz] at oneltnx
    norm_cast at oneltnx
    rw [zero_mul] at oneltnx
    linarith
  rw [mul_comm, ← div_lt_iff] at oneltnx
  · have := h₂ n this
    linarith
  · norm_cast
