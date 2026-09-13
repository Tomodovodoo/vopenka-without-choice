import Foundation.FirstOrder.Basic

/-! Consistency of a set of syntactic formulas (with free variables) over a theory of sentences.

Foundation's `Entailment.Consistent T` speaks only about sentences, but a Henkin construction whose
witnesses are fresh free variables needs to know that a set `H` of `Proposition L`
(= `SyntacticFormula L`) is consistent together with the axioms of `T`. `Refutable T Δ` says that
the finite list `Δ` is refutable from finitely many axioms of `T`, and `ConsistentOver T H` says no
finite sublist of `H` is refutable. The three steps a Henkin construction needs are proved here:
the link with `Entailment.Consistent`, the decision step (add `φ` or add `∼φ`), and the witness step
(if `∃¹ φ` is in `H` and `m` is a variable free in no member of `H`, then `φ/[&m]` may be added). -/

namespace ZFVP

open LO LO.FirstOrder

variable {L : Language} {T : Theory L} {H H' : Set (Proposition L)}

/-- `Δ` is refutable over `T`: there are finitely many axioms `A` of `T` and a one-sided derivation
of the sequent `∼Δ ++ ∼A`, that is, a proof that the members of `Δ` and the members of `A` cannot
all hold. -/
def Refutable (T : Theory L) (Δ : List (Proposition L)) : Prop :=
  ∃ A : List (Sentence L), (∀ σ ∈ A, σ ∈ T) ∧ Nonempty (⊢ᴸᴷ¹ ∼Δ ++ ∼Sequent.embed A)

/-- `H` is consistent over `T`: no finite list of members of `H` is refutable over `T`. -/
def ConsistentOver (T : Theory L) (H : Set (Proposition L)) : Prop :=
  ∀ Δ : List (Proposition L), (∀ φ ∈ Δ, φ ∈ H) → ¬Refutable T Δ

theorem not_consistentOver_iff :
    ¬ConsistentOver T H ↔ ∃ Δ : List (Proposition L), (∀ φ ∈ Δ, φ ∈ H) ∧ Refutable T Δ := by
  simp [ConsistentOver]

/-! ### Weakening -/

private lemma tilde_subset {Δ Δ' : List (Proposition L)} (h : Δ ⊆ Δ') : ∼Δ ⊆ ∼Δ' := by
  rw [List.tilde_def, List.tilde_def]; exact List.map_subset _ h

theorem Refutable.mono {Δ Δ' : List (Proposition L)} (h : Refutable T Δ) (hsub : Δ ⊆ Δ') :
    Refutable T Δ' := by
  obtain ⟨A, hA, ⟨d⟩⟩ := h
  refine ⟨A, hA, ⟨d.contraction ?_⟩⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (tilde_subset hsub hx)
  · exact List.mem_append_right _ hx

theorem ConsistentOver.mono (h : ConsistentOver T H) (hsub : H' ⊆ H) : ConsistentOver T H' :=
  fun Δ hΔ ↦ h Δ fun φ hφ ↦ hsub (hΔ φ hφ)

/-! ### The link with `Entailment.Consistent` -/

theorem consistentOver_empty_iff :
    ConsistentOver T (∅ : Set (Proposition L)) ↔ Entailment.Consistent T := by
  rw [← Entailment.not_inconsistent_iff_consistent, Theory.Proof.inconsistent_iff]
  constructor
  · rintro h ⟨A, hA, ⟨d⟩⟩
    exact h [] (by simp) ⟨A, hA, ⟨d.contraction (by simp)⟩⟩
  · intro h Δ hΔ hr
    obtain ⟨A, hA, ⟨d⟩⟩ := hr
    have : Δ = [] := List.eq_nil_iff_forall_not_mem.mpr fun φ hφ ↦ by simpa using hΔ φ hφ
    subst this
    exact h ⟨A, hA, ⟨d.contraction (by simp)⟩⟩

/-! ### Splitting off one extra formula

For `Δ` drawn from `insert χ H` we keep the part lying in `H` and pay for the rest with a single
occurrence of `∼χ` at the head of the sequent. -/

private noncomputable def stagePart (H : Set (Proposition L)) (Δ : List (Proposition L)) :
    List (Proposition L) :=
  Δ.filter (fun φ ↦ @decide (φ ∈ H) (Classical.dec _))

private lemma mem_stagePart {Δ : List (Proposition L)} {ψ : Proposition L} :
    ψ ∈ stagePart H Δ ↔ ψ ∈ Δ ∧ ψ ∈ H := by
  simp [stagePart, List.mem_filter]

private lemma stagePart_mem (Δ : List (Proposition L)) : ∀ ψ ∈ stagePart H Δ, ψ ∈ H :=
  fun _ h ↦ (mem_stagePart.mp h).2

private lemma split_subset {Δ : List (Proposition L)} {χ : Proposition L}
    (hsub : ∀ ψ ∈ Δ, ψ ∈ insert χ H) (rest : List (Proposition L)) :
    ∼Δ ++ rest ⊆ ∼χ :: (∼stagePart H Δ ++ rest) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [List.tilde_def] at hx
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hx
    rcases Set.mem_insert_iff.mp (hsub ψ hψ) with rfl | hmem
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
      rw [List.tilde_def]
      exact List.mem_map_of_mem (mem_stagePart.mpr ⟨hψ, hmem⟩)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)

/-- A refutation of a list drawn from `insert χ H` becomes a derivation with `∼χ` in front and the
rest of the list drawn from `H`. -/
private lemma refutable_insert {Δ : List (Proposition L)} {χ : Proposition L}
    (hsub : ∀ ψ ∈ Δ, ψ ∈ insert χ H) (h : Refutable T Δ) :
    ∃ A : List (Sentence L), (∀ σ ∈ A, σ ∈ T) ∧
      Nonempty (⊢ᴸᴷ¹ ∼χ :: (∼stagePart H Δ ++ ∼Sequent.embed A)) := by
  obtain ⟨A, hA, ⟨d⟩⟩ := h
  exact ⟨A, hA, ⟨d.contraction (split_subset hsub _)⟩⟩

/-! ### Adding provable sentences -/

private lemma provable_of_mem {σ : Sentence L} (hσ : σ ∈ T) : T ⊢ σ :=
  Theory.Proof.provable_iff.mpr ⟨[σ], by simpa using hσ, ⟨Derivation.close (σ : Proposition L)⟩⟩

/-- A sentence provable in `T` may be added to a consistent set. -/
theorem consistentOver_insert_of_provable (h : ConsistentOver T H) {σ : Sentence L} (hσ : T ⊢ σ) :
    ConsistentOver T (insert (Rewriting.emb σ : Proposition L) H) := by
  intro Δ hΔ hr
  obtain ⟨A, hA, ⟨d₁⟩⟩ := refutable_insert hΔ hr
  obtain ⟨B, hB, ⟨d₂⟩⟩ := Theory.Proof.provable_iff.mp hσ
  have d : ⊢ᴸᴷ¹ ∼Sequent.embed B ++ (∼stagePart H Δ ++ ∼Sequent.embed A) := Derivation.cut d₂ d₁
  refine h (stagePart H Δ) (stagePart_mem Δ) ⟨A ++ B, ?_, ⟨d.contraction ?_⟩⟩
  · intro τ hτ
    rcases List.mem_append.mp hτ with hτ | hτ
    · exact hA τ hτ
    · exact hB τ hτ
  · have e : (∼Sequent.embed (A ++ B) : Sequent L) = ∼Sequent.embed A ++ ∼Sequent.embed B := by
      simp [List.tilde_def]
    rw [e]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_right _ (List.mem_append_right _ hx)
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_append_left _ hx)

/-- An axiom of `T` may be added to a consistent set. -/
theorem consistentOver_insert_axiom (h : ConsistentOver T H) {σ : Sentence L} (hσ : σ ∈ T) :
    ConsistentOver T (insert (Rewriting.emb σ : Proposition L) H) :=
  consistentOver_insert_of_provable h (provable_of_mem hσ)

/-! ### Directed unions -/

private lemma exists_stage {H : ℕ → Set (Proposition L)} (hmono : Monotone H)
    (Δ : List (Proposition L)) (h : ∀ φ ∈ Δ, φ ∈ ⋃ n, H n) : ∃ n, ∀ φ ∈ Δ, φ ∈ H n := by
  induction Δ with
  | nil => exact ⟨0, by simp⟩
  | cons a Δ ih =>
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (h a (by simp))
      obtain ⟨k, hk⟩ := ih fun φ hφ ↦ h φ (by simp [hφ])
      refine ⟨max n k, ?_⟩
      intro φ hφ
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact hmono (le_max_left n k) hn
      · exact hmono (le_max_right n k) (hk φ hφ)

/-- A monotone union of sets consistent over `T` is consistent over `T`. -/
theorem consistentOver_iUnion {H : ℕ → Set (Proposition L)} (hmono : Monotone H)
    (h : ∀ n, ConsistentOver T (H n)) : ConsistentOver T (⋃ n, H n) := by
  intro Δ hΔ hr
  obtain ⟨n, hn⟩ := exists_stage hmono Δ hΔ
  exact h n Δ hn hr

/-! ### The decision step -/

/-- For any formula `φ`, a consistent set stays consistent after adding `φ` or after adding `∼φ`. -/
theorem consistentOver_insert_or (h : ConsistentOver T H) (φ : Proposition L) :
    ConsistentOver T (insert φ H) ∨ ConsistentOver T (insert (∼φ) H) := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨Δ, hΔ, hr⟩ := not_consistentOver_iff.mp hc.1
  obtain ⟨Δ', hΔ', hr'⟩ := not_consistentOver_iff.mp hc.2
  obtain ⟨A, hA, ⟨d₁⟩⟩ := refutable_insert hΔ hr
  obtain ⟨A', hA', ⟨d₂⟩⟩ := refutable_insert hΔ' hr'
  have d₂' : ⊢ᴸᴷ¹ φ :: (∼stagePart H Δ' ++ ∼Sequent.embed A') := by
    simpa using d₂
  have d : ⊢ᴸᴷ¹ (∼stagePart H Δ' ++ ∼Sequent.embed A') ++ (∼stagePart H Δ ++ ∼Sequent.embed A) :=
    Derivation.cut d₂' d₁
  refine h (stagePart H Δ ++ stagePart H Δ') ?_ ⟨A ++ A', ?_, ⟨d.contraction ?_⟩⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact stagePart_mem Δ ψ hψ
    · exact stagePart_mem Δ' ψ hψ
  · intro τ hτ
    rcases List.mem_append.mp hτ with hτ | hτ
    · exact hA τ hτ
    · exact hA' τ hτ
  · have e1 : (∼(stagePart H Δ ++ stagePart H Δ') : Sequent L)
        = ∼stagePart H Δ ++ ∼stagePart H Δ' := by simp [List.tilde_def]
    have e2 : (∼Sequent.embed (A ++ A') : Sequent L) = ∼Sequent.embed A ++ ∼Sequent.embed A' := by
      simp [List.tilde_def]
    rw [e1, e2]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (List.mem_append_right _ hx)
      · exact List.mem_append_right _ (List.mem_append_right _ hx)
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (List.mem_append_left _ hx)
      · exact List.mem_append_right _ (List.mem_append_left _ hx)

/-! ### The witness step -/

private lemma not_fvar?_tilde {m : ℕ} {ψ : Proposition L} (h : ¬ψ.FVar? m) : ¬(∼ψ).FVar? m := by
  show m ∉ (∼ψ).freeVariables
  rw [Semiformula.freeVariables_not]
  exact h

private lemma not_fvar?_of_mem {m : ℕ} {Δ₀ : List (Proposition L)} {A : List (Sentence L)}
    (hΔ : ∀ ψ ∈ Δ₀, ¬ψ.FVar? m) :
    ∀ χ ∈ ∼Δ₀ ++ ∼Sequent.embed A, ¬Semiformula.FVar? χ m := by
  intro χ hχ
  rcases List.mem_append.mp hχ with hχ | hχ
  · rw [List.tilde_def] at hχ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hχ
    exact not_fvar?_tilde (hΔ ψ hψ)
  · rw [List.tilde_def] at hχ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hχ
    obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hψ
    simp [Semiformula.FVar?]

/-- The Henkin witness step. If `∃¹ φ` belongs to `H` and the variable `m` is free in no member of
`H`, then the instance `φ/[&m]` may be added to `H`. -/
theorem consistentOver_insert_subst (h : ConsistentOver T H) {φ : Semiproposition L 1}
    (hmem : (∃¹ φ) ∈ H) {m : ℕ} (hm : ∀ ψ ∈ H, ¬ψ.FVar? m) :
    ConsistentOver T (insert (φ/[&m]) H) := by
  intro Δ hΔ hr
  obtain ⟨A, hA, ⟨d⟩⟩ := refutable_insert hΔ hr
  have hφm : ¬(∼φ).FVar? m := by
    have h0 : ¬(∃¹ φ).FVar? m := hm _ hmem
    show m ∉ (∼φ).freeVariables
    rw [Semiformula.freeVariables_not]
    exact h0
  have d' : ⊢ᴸᴷ¹ (∼φ)/[&m] :: (∼stagePart H Δ ++ ∼Sequent.embed A) := by
    simpa using d
  have dg : ⊢ᴸᴷ¹ (∀¹ ∼φ) :: (∼stagePart H Δ ++ ∼Sequent.embed A) :=
    Derivation.genelalizeByNewver hφm
      (not_fvar?_of_mem (fun ψ hψ ↦ hm ψ (stagePart_mem Δ ψ hψ))) d'
  refine h ((∃¹ φ) :: stagePart H Δ) ?_ ⟨A, hA, ⟨dg.contraction ?_⟩⟩
  · intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hmem
    · exact stagePart_mem Δ ψ hψ
  · intro x hx
    simpa using hx

/-- The witness step with the fresh variable read off a finite list that covers `H`. -/
theorem consistentOver_insert_subst_newVar (h : ConsistentOver T H) {Γ : Sequent L}
    (hH : ∀ ψ ∈ H, ψ ∈ Γ) {φ : Semiproposition L 1} (hmem : (∃¹ φ) ∈ H) :
    ConsistentOver T (insert (φ/[&Γ.newVar]) H) :=
  consistentOver_insert_subst h hmem fun _ hψ ↦ Sequent.not_fvar?_newVar (hH _ hψ)

end ZFVP
