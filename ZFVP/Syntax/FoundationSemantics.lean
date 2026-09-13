import ZFVP.Syntax.FoundationEncoding
import ZFVP.Syntax.SatisfactionEquations

/-! The external Foundation structure and semantics represented by internal codes. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
variable {Λ : Language} {ξ : Type*} {L M : V}

abbrev CodedDomain (M : V) := {x : V // x ∈ structureDomain M}

theorem codedDomain_nonempty (hM : IsStructureCode L M) : Nonempty (CodedDomain M) := by
  have := hM.domain_nonempty
  obtain ⟨x, hx⟩ := this.nonempty
  exact ⟨⟨x, hx⟩⟩

@[instance_reducible] noncomputable def codedFoundationStructure (hM : IsStructureCode L M)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V)) : Structure Λ (CodedDomain M) where
  func := fun {k} f v ↦ ⟨((structureFunctions M) ‘ (F f)) ‘ (standardTuple (fun i ↦ (v i).val)), by
    apply hM.function_value_mem (hF k f).1
    rw [(hF k f).2]
    exact standardTuple_mem_function _ (fun i ↦ (v i).property)⟩
  rel := fun {_} r v ↦ standardTuple (fun i ↦ (v i).val) ∈ (structureRelations M) ‘ (R r)

theorem encodeSemiterm_value (hM : IsStructureCode L M)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    {Γ E : V} (e : ξ → V) (he : ∀ x, e x ∈ Γ)
    (a : ξ → CodedDomain M) (hE : ∀ x, E ‘ (e x) = (a x).val)
    {n : ℕ} (b : Fin n → CodedDomain M) (t : Semiterm Λ ξ n) :
    (termEvaluation L Γ (n : V) M (standardTuple (fun i ↦ (b i).val)) E) ‘
      (encodeSemiterm F e t) =
      (t.val (s := codedFoundationStructure hM F R hF) b a).val := by
  induction t with
  | bvar i =>
    rw [encodeSemiterm, termEvaluation_boundVar hM.language (by simp) _ _ _ _
      (natCast_mem_of_lt i.isLt), value_standardTuple]
    rfl
  | fvar x =>
    rw [encodeSemiterm, termEvaluation_freeVar hM.language (by simp) _ _ _ _ (he x), hE]
    rfl
  | @func k f ts ih =>
    rw [encodeSemiterm, termEvaluation_function hM.language (by simp) _ _ _ _
      (encodeSemiterm_mem hM.language F e hF he (.func f ts))]
    rw [compose_standardTuple _ _ (fun i ↦ by
      simpa using encodeSemiterm_mem hM.language F e hF he (ts i))]
    simp only [ih, Semiterm.val]
    rfl

theorem encodeSemiformula_satisfies (hM : IsStructureCode L M)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    (hR : ∀ k (r : Λ.Rel k), R r ∈ relationSymbols L ∧
      (relationArities L) ‘ (R r) = (k : V))
    {Γ E : V} (e : ξ → V) (he : ∀ x, e x ∈ Γ)
    (a : ξ → CodedDomain M) (hE : ∀ x, E ‘ (e x) = (a x).val)
    {n : ℕ} (b : Fin n → CodedDomain M) (φ : Semiformula Λ ξ n) :
    Satisfies L Γ M E (n : V) (encodeSemiformula F R e φ)
      (standardTuple (fun i ↦ (b i).val)) ↔
      φ.EvalAux (codedFoundationStructure hM F R hF) a b := by
  have ht : ∀ n (ψ : Semiformula Λ ξ n),
      encodeSemiformula F R e ψ ∈ formulaSet L Γ (n : V) := fun n ψ ↦
    (mem_formulaSet_iff _ _ _ _).mpr
      (encodeSemiformula_mem_family hM.language F R e hF hR he ψ)
  have hb : ∀ n (b : Fin n → CodedDomain M),
      standardTuple (fun i ↦ (b i).val) ∈ structureDomain M ^ (n : V) :=
    fun n b ↦ standardTuple_mem_function _ (fun i ↦ (b i).property)
  have ha : ∀ n k (r : Λ.Rel k) (ts : Fin k → Semiterm Λ ξ n),
      IsAtomicArguments L Γ (n : V) (relationToken (R r))
        (standardTuple (fun i ↦ encodeSemiterm F e (ts i))) := by
    intro n k r ts
    refine Or.inr ⟨R r, (hR k r).1, rfl, ?_⟩
    rw [(hR k r).2]
    exact standardTuple_mem_function _ (fun i ↦ encodeSemiterm_mem hM.language F e hF he (ts i))
  have hv : ∀ n k (r : Λ.Rel k) (ts : Fin k → Semiterm Λ ξ n) (b : Fin n → CodedDomain M),
      AtomicHolds L Γ M E (n : V) (standardTuple (fun i ↦ (b i).val))
        (relationToken (R r)) (standardTuple (fun i ↦ encodeSemiterm F e (ts i))) ↔
      (codedFoundationStructure hM F R hF).rel r
        (fun i ↦ (ts i).val (s := codedFoundationStructure hM F R hF) b a) := by
    intro n k r ts b
    rw [atomicHolds_relation, and_iff_right (hR k r).1]
    unfold evaluatedArguments evaluateWithFreeAssignment
    rw [compose_standardTuple _ _ (fun i ↦ by
      simpa using encodeSemiterm_mem hM.language F e hF he (ts i))]
    simp only [encodeSemiterm_value hM F R hF e he a hE]
    rfl
  induction φ with
  | verum =>
    simpa only [encodeSemiformula, Semiformula.EvalAux, iff_true] using
      (satisfies_truth hM.language (by simp)).mpr (hb _ b)
  | falsum =>
    simpa only [encodeSemiformula, Semiformula.EvalAux, iff_false] using
      (not_satisfies_falsity (Γ := Γ) (M := M) (e := E)
        (b := standardTuple (fun i ↦ (b i).val)) hM.language (by simp))
  | rel r ts =>
    exact (satisfies_atom hM.language (by simp) (ha _ _ r ts) (hb _ b)).trans (hv _ _ r ts b)
  | nrel r ts =>
    exact (satisfies_negAtom hM.language (by simp) (ha _ _ r ts) (hb _ b)).trans
      (not_congr (hv _ _ r ts b))
  | and φ ψ ihφ ihψ =>
    exact (satisfies_and hM.language (by simp) (ht _ φ) (ht _ ψ) (hb _ b)).trans
      (and_congr (ihφ b) (ihψ b))
  | or φ ψ ihφ ihψ =>
    exact (satisfies_or hM.language (by simp) (ht _ φ) (ht _ ψ) (hb _ b)).trans
      (or_congr (ihφ b) (ihψ b))
  | all φ ih =>
    rw [encodeSemiformula, satisfies_all hM.language (by simp)
      (by simpa [num_succ_def] using ht _ φ) (hb _ b)]
    change (∀ x ∈ structureDomain M, _) ↔ ∀ x : CodedDomain M, _
    constructor
    · intro h x
      exact (ih (x :> b)).mp (by simpa [standardTuple, num_succ_def] using h x.val x.property)
    · intro h x hx
      simpa [standardTuple, num_succ_def] using (ih (⟨x, hx⟩ :> b)).mpr (h ⟨x, hx⟩)
  | exs φ ih =>
    rw [encodeSemiformula, satisfies_exists hM.language (by simp)
      (by simpa [num_succ_def] using ht _ φ) (hb _ b)]
    change (∃ x ∈ structureDomain M, _) ↔ ∃ x : CodedDomain M, _
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨⟨x, hx⟩, (ih (⟨x, hx⟩ :> b)).mp (by simpa [standardTuple, num_succ_def] using h)⟩
    · rintro ⟨x, h⟩
      exact ⟨x.val, x.property, by simpa [standardTuple, num_succ_def] using (ih (x :> b)).mpr h⟩

end ZFVP
