import Mathlib.Topology.Instances.Real
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Analysis.Normed.Module.Dual
import FunctionalAnalysis.MazurTheorem.Defs
import Topology.Nets.Nets

noncomputable section

open Set Filter Topology Classical Function Defs

set_option linter.unusedVariables false

namespace Lemmas

lemma eval_pos (p : α → Prop) (f g : α → β) {a : α} (h: p a) : partial_fun p f g a = f a := by
  dsimp [partial_fun]
  simp
  intro npn
  contradiction

lemma eval_neg (p : α → Prop) (f g : α → β) {a : α} (h: ¬p a) : partial_fun p f g a = g a := by
  dsimp [partial_fun]
  simp
  intro npn
  contradiction

lemma exist_comp_iff_ker_sub {E F G 𝕜: Type*} [Field 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
  (f: E →ₗ[𝕜] G) (g: E →ₗ[𝕜] F) : (∃ (h: F →ₗ[𝕜] G), f = h ∘ₗ g) ↔ {e | e ∈ LinearMap.ker g} ⊆ {e | e ∈ LinearMap.ker f} := by
    constructor
    · intro existence
      rcases existence with ⟨h, feqhg⟩
      intro e einkerg
      dsimp at *
      rw [LinearMap.mem_ker] at *
      rw [feqhg]
      dsimp [LinearMap.comp]
      rw [einkerg, LinearMap.map_zero]
    · intro kergsubkerf
      let h'': (LinearMap.range g) → E := fun (f : LinearMap.range g) ↦ if h: ∃ (e: E), g e = f then Classical.choose h else 0
      let h': (LinearMap.range g) →ₗ[𝕜] G := {
        toFun := f ∘ h''
        map_add' := by
          intro x x'
          have cond1 := x.2
          have cond2 := x'.2
          rw [LinearMap.mem_range] at *
          have cond3 : ∃ y, g y = x + x' := by
            rcases cond1 with ⟨y₁, gy₁x⟩
            rcases cond2 with ⟨y₂, gy₂x'⟩
            use y₁ + y₂
            rw [map_add, gy₁x, gy₂x']
          dsimp [h'']
          rw [dif_pos cond1, dif_pos cond2, dif_pos cond3]
          have g1 := Classical.choose_spec cond1
          have g2 := Classical.choose_spec cond2
          have g3 := Classical.choose_spec cond3
          have : choose cond3 - (choose cond1 + choose cond2) ∈ LinearMap.ker f := by
            apply kergsubkerf
            dsimp
            rw [LinearMap.mem_ker, map_sub, sub_eq_zero, map_add, g1, g2, g3]
          rw [LinearMap.mem_ker, map_sub, map_add, sub_eq_zero] at this
          assumption
        map_smul' := by
          intro c x
          have cond1 := x.2
          rw [LinearMap.mem_range] at cond1
          have cond2 : ∃ y, g y = c • x := by
            rcases cond1 with ⟨y₁, gy₁x⟩
            use c • y₁
            rw [map_smul, gy₁x]
          dsimp [h'']
          rw [dif_pos cond1, dif_pos cond2]
          have g1 := Classical.choose_spec cond1
          have g2 := Classical.choose_spec cond2
          have : choose cond2 - (c • choose cond1) ∈ LinearMap.ker f := by
            apply kergsubkerf
            dsimp
            rw [LinearMap.mem_ker, map_sub, sub_eq_zero, map_smul, g1, g2]
          rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
          assumption
          }
      have eqcomp : ∀ (e: E), f e = h' (⟨g e, by rw [LinearMap.mem_range]; use e⟩) := by
        intro e
        dsimp [h', h'']
        have cond : ∃ e_1, g e_1 = g e := by
          use e
        rw [dif_pos cond]
        have := Classical.choose_spec cond
        have : choose cond - e ∈ LinearMap.ker f := by
          apply kergsubkerf
          dsimp
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
          assumption
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
        exact this.symm
      have extension : ∃ (h: F →ₗ[𝕜] G), ∀ (x: {x : F // x ∈ LinearMap.range g}), h x.1 = h' x := by
        rcases LinearMap.exists_extend h' with ⟨h, hcircinceqh'⟩
        use h
        intro x
        rw [← hcircinceqh']
        dsimp
      rcases extension with ⟨h, hexth'⟩
      use h
      ext e
      simp [LinearMap.comp]
      rw [hexth' ⟨g e, by rw [LinearMap.mem_range]; use e⟩]
      exact eqcomp e

lemma mem_submodule_iff_inter_of_ker_sub_ker {E 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] (f: E →ₗ[𝕂] 𝕂) (F: Finset (E →ₗ[𝕂] 𝕂)):
  f ∈ Submodule.span 𝕂 F ↔ ⋂ g ∈ F, {e | e ∈ LinearMap.ker g} ⊆ {e | e ∈ LinearMap.ker f} := by
    constructor
    · intro finspan
      rw [mem_span_finset] at finspan
      rcases finspan with ⟨u, feqsum⟩
      intro e eininter
      simp only [mem_iInter] at eininter
      dsimp
      rw [LinearMap.mem_ker]
      dsimp at eininter
      have := congr_arg (fun (g: E →ₗ[𝕂] 𝕂) ↦ g e) feqsum
      dsimp at this
      rw [← this]
      have : ∀ i ∈ F, ((u i) • i) e = 0 := by
        intro i iinF
        have := eininter i iinF
        rw [LinearMap.mem_ker] at this
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
      have :  ⋂ g ∈ F, {e | e ∈ LinearMap.ker g} = {e | e ∈ LinearMap.ker r} := by
        ext e
        constructor
        · intro eininter
          simp only [mem_iInter] at eininter
          dsimp at *
          rw [LinearMap.mem_ker]
          ext i
          dsimp [r]
          have := eininter (T i) (T i).2
          rw [LinearMap.mem_ker] at this
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
