import ZFVP.SetTheory.PiOneHierarchy
import ZFVP.SetTheory.LeastRankWitnesses
import ZFVP.SetTheory.FormulaReflection

/-! Rank segments make the least-rank witness condition bounded apart from its given matrix. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def piOnePowerFormula : SetTheorySemisentence 2 := “B A. ∀ x, x ∈ B ↔ !isSubsetOf x A”

theorem piOnePowerFormula_piOne : IsPiFormula 1 piOnePowerFormula :=
  .all (.and (.or (.bounded (.nrel _ _)) (.bounded (isSubsetOf_bounded.subst _)))
    (.or (.bounded (isSubsetOf_bounded.subst _).neg) (.bounded (.rel _ _))))

def leastWitnessLayerFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence (n + 5) :=
  (Semiformula.nrel Language.Set.Rel.mem ![.bvar 0, .bvar 2]).and
    (ψ.subst (.bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ))

def leastWitnessBodyFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1)) : SetTheorySemisentence (n + 4) :=
  (piOneHierarchyFormula.subst ![.bvar 1, .bvar 0]).and
    ((piOnePowerFormula.subst ![.bvar 2, .bvar 1]).and
      ((boundedSetExs (.bvar 3) .verum).and
        ((isSubsetOf.subst ![.bvar 3, .bvar 2]).and
          ((boundedSetAll (.bvar 1) (∼(ψ.subst (.bvar 0 :> fun i : Fin n ↦ .bvar i.succ.succ.succ.succ.succ)))).and
            (boundedSetAll (.bvar 2)
              (((Semiformula.nrel Language.Set.Rel.mem ![.bvar 0, .bvar 4]).or (leastWitnessLayerFormula ψ)).and
                ((∼leastWitnessLayerFormula ψ).or (.rel Language.Set.Rel.mem ![.bvar 0, .bvar 4]))))))))

theorem leastWitnessBodyFormula_pi {n k : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    (hψ : IsPiFormula k ψ) : IsPiFormula (k + 1) (leastWitnessBodyFormula ψ) := by
  have hp : IsPiFormula (k + 1) (leastWitnessLayerFormula ψ) :=
    .and (.bounded (.nrel _ _)) (hψ.subst _).raise
  have hn : IsPiFormula (k + 1) (∼leastWitnessLayerFormula ψ) :=
    .or (.bounded (.rel _ _)) (hψ.subst _).neg.raise
  exact .and ((piOneHierarchyFormula_piOne.subst _).mono (by omega))
    (.and ((piOnePowerFormula_piOne.subst _).mono (by omega))
      (.and (.bounded (.exs (.bvar 3) .verum))
        (.and (.bounded (isSubsetOf_bounded.subst _))
          (.and (.boundedAll (.bvar 1) (hψ.subst _).neg.raise)
            (.boundedAll (.bvar 2) (.and (.or (.bounded (.nrel _ _)) hp)
              (.or hn (.bounded (.rel _ _)))))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

@[simp] theorem eval_piOnePowerFormula (B A : V) : piOnePowerFormula.Evalb ![B, A] ↔ B = ℘ A := by
  simp [piOnePowerFormula, mem_ext_iff]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_and {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.and ψ).Evalb v ↔ φ.Evalb v ∧ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_or {n : ℕ} (φ ψ : SetTheorySemisentence n) (v : Fin n → V) :
    (φ.or ψ).Evalb v ↔ φ.Evalb v ∨ ψ.Evalb v := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem eval_verum {n : ℕ} (v : Fin n → V) :
    (Semiformula.verum : SetTheorySemisentence n).Evalb v := trivial

def LeastWitnessBody {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (α A B C : V) : Prop :=
  IsOrdinal α ∧ A = hierarchy α ∧ B = hierarchy (succ α) ∧ IsNonempty C ∧ C ⊆ B ∧
    (∀ u ∈ A, ¬ψ.Evalb (u :> v)) ∧ ∀ u ∈ B, u ∈ C ↔ u ∉ A ∧ ψ.Evalb (u :> v)

theorem eval_leastWitnessBodyFormula {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (α A B C : V) :
    (leastWitnessBodyFormula ψ).Evalb (α :> A :> B :> C :> v) ↔ LeastWitnessBody ψ v α A B C := by
  simp [leastWitnessBodyFormula, eval_boundedSetExs, eval_boundedSetAll,
    eval_and, eval_or, Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
    Matrix.constant_eq_singleton, leastWitnessLayerFormula, IsHierarchySegment, LeastWitnessBody,
    eval_verum, and_assoc]
  intro hα hA
  let := hα
  subst A
  simp only [hierarchy_succ, Structure.rel]
  apply and_congr_right
  intro _
  have hnonempty : (∃ y : V, y ∈ C) ↔ IsNonempty C :=
    ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy⟩⟩
  rw [hnonempty]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact forall_congr' fun y ↦ imp_congr_right fun _ ↦ by tauto

theorem mem_rank_layer_iff (u α : V) [IsOrdinal α] :
    u ∈ hierarchy (succ α) ∧ u ∉ hierarchy α ↔ rank u = α := by
  simp only [mem_hierarchy_iff_rank_mem, mem_succ_iff]
  constructor
  · rintro ⟨h | h, hn⟩
    · exact h
    · exact False.elim (hn h)
  · intro h
    exact ⟨Or.inl h, by rw [h]; exact mem_irrefl α⟩

theorem LeastWitnessBody.witness {n : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    {v : Fin n → V} {α A B C u : V} (h : LeastWitnessBody ψ v α A B C) (hu : u ∈ C) :
    ψ.Evalb (u :> v) ∧ rank u = α := by
  obtain ⟨hα, rfl, rfl, _, hCB, _, hmem⟩ := h
  let := hα
  have hub := hCB u hu
  have hw := (hmem u hub).mp hu
  exact ⟨hw.2, (mem_rank_layer_iff u α).mp ⟨hub, hw.1⟩⟩

theorem leastWitnessBody_exists {n : ℕ} (ψ : SetTheorySemisentence (n + 1))
    (v : Fin n → V) (hex : ∃ u : V, ψ.Evalb (u :> v)) :
    ∃ α A B C : V, LeastWitnessBody ψ v α A B C := by
  have hexR : ∃ u : V, formulaWitnessRelation ψ (standardTuple v) u := by
    simpa [formulaWitnessRelation] using hex
  obtain ⟨C, hC, _⟩ := leastRankWitnessSet_existsUnique (formulaWitnessRelation ψ)
    (formulaWitnessRelation_definable ψ) (standardTuple v) hexR
  have hnonempty := hC.nonempty
  obtain ⟨α, hα, hmem⟩ := hC
  let := hα.1
  have hmem' : ∀ u : V, u ∈ C ↔ ψ.Evalb (u :> v) ∧ rank u = α := by
    simpa [formulaWitnessRelation] using hmem
  refine ⟨α, hierarchy α, hierarchy (succ α), C, hα.1, rfl, rfl, hnonempty, ?_, ?_, ?_⟩
  · intro u hu
    exact ((mem_rank_layer_iff u α).mpr ((hmem' u).mp hu).2).1
  · intro u hu hψ
    have hlt := (mem_hierarchy_iff_rank_mem u α).mp hu
    have hle : α ⊆ rank u := hα.2.2 (rank u) inferInstance
      ⟨u, by simpa [formulaWitnessRelation] using hψ, rfl⟩
    exact mem_irrefl (rank u) (hle (rank u) hlt)
  · intro u hu
    rw [hmem']
    exact ⟨fun h ↦ ⟨((mem_rank_layer_iff u α).mpr h.2).2, h.1⟩,
      fun h ↦ ⟨h.2, (mem_rank_layer_iff u α).mp ⟨hu, h.1⟩⟩⟩

theorem LeastWitnessBody.unique {n : ℕ} {ψ : SetTheorySemisentence (n + 1)}
    {v : Fin n → V} {α A B C β D E F : V}
    (h : LeastWitnessBody ψ v α A B C) (h' : LeastWitnessBody ψ v β D E F) :
    α = β ∧ A = D ∧ B = E ∧ C = F := by
  let := h.1
  let := h'.1
  obtain ⟨u, hu⟩ := h.2.2.2.1
  obtain ⟨w, hw⟩ := h'.2.2.2.1
  have huw := h.witness hu
  have hww := h'.witness hw
  have hab : α = β := by
    rcases IsOrdinal.mem_trichotomy α β with hl | he | hg
    · have huD : u ∈ D := by
        rw [h'.2.1, mem_hierarchy_iff_rank_mem, huw.2]
        exact hl
      exact False.elim (h'.2.2.2.2.2.1 u huD huw.1)
    · exact he
    · have hwA : w ∈ A := by
        rw [h.2.1, mem_hierarchy_iff_rank_mem, hww.2]
        exact hg
      exact False.elim (h.2.2.2.2.2.1 w hwA hww.1)
  have hAD : A = D := h.2.1.trans (hab ▸ h'.2.1.symm)
  have hBE : B = E := h.2.2.1.trans (hab ▸ h'.2.2.1.symm)
  refine ⟨hab, hAD, hBE, ?_⟩
  apply mem_ext
  intro x
  constructor
  · intro hx
    have hxB := h.2.2.2.2.1 x hx
    apply (h'.2.2.2.2.2.2 x (hBE ▸ hxB)).mpr
    simpa [← hAD] using (h.2.2.2.2.2.2 x hxB).mp hx
  · intro hx
    have hxE := h'.2.2.2.2.1 x hx
    apply (h.2.2.2.2.2.2 x (hBE.symm ▸ hxE)).mpr
    simpa [hAD] using (h'.2.2.2.2.2.2 x hxE).mp hx

end ZFVP
