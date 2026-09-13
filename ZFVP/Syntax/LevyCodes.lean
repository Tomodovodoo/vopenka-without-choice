import ZFVP.Syntax.BoundedCodes
import ZFVP.SetTheory.LevyFormulas

/-! Internal formula-code families at each standard Levy level.
The construction uses closure under Booleans, bounded quantifiers and the
polarity's unbounded quantifier. Exact complexity and prenex equivalence are separate. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def levyQuantifierCode (p : LevyPolarity) (φ : V) : V :=
  match p with
  | .sigma => existsCode φ
  | .pi => allCode φ

instance levyQuantifierCode_definable (p : LevyPolarity) : ℒₛₑₜ-function₁[V] (levyQuantifierCode p) := by
  cases p <;> unfold levyQuantifierCode <;> definability

def IsLevyExtensionClosed (p : LevyPolarity) (B Q : V) : Prop := B ⊆ Q ∧ ∀ n ∈ (ω : V),
  (∀ φ ψ, ⟨n, φ⟩ₖ ∈ Q → ⟨n, ψ⟩ₖ ∈ Q → ⟨n, andCode φ ψ⟩ₖ ∈ Q ∧ ⟨n, orCode φ ψ⟩ₖ ∈ Q) ∧
  (∀ i ∈ n, ∀ φ, ⟨succ n, φ⟩ₖ ∈ Q → ⟨n, boundedAllCode i φ⟩ₖ ∈ Q ∧ ⟨n, boundedExistsCode i φ⟩ₖ ∈ Q) ∧
  ∀ φ, ⟨succ n, φ⟩ₖ ∈ Q → ⟨n, levyQuantifierCode p φ⟩ₖ ∈ Q

instance isLevyExtensionClosed_definable (p : LevyPolarity) : ℒₛₑₜ-relation[V] (IsLevyExtensionClosed p) := by
  unfold IsLevyExtensionClosed
  definability

theorem formulaFamily_levyClosed (p : LevyPolarity) {B : V}
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) :
    IsLevyExtensionClosed p B (formulaFamily membershipLanguageCode ∅) := by
  refine ⟨hB, ?_⟩
  intro n hn
  have hc := formulaFamily_boundedClosed (V := V) n hn
  refine ⟨hc.2.2.1, hc.2.2.2, ?_⟩
  intro φ hφ
  have hq := (formulaFamily_closed membershipLanguageCode_valid ∅ n hn).2.2.2 φ hφ
  cases p
  · exact hq.2
  · exact hq.1

noncomputable def levyExtensionFamily (p : LevyPolarity) (B : V) : V :=
  {q ∈ formulaFamily (membershipLanguageCode : V) ∅ ; ∀ Q : V, IsLevyExtensionClosed p B Q → q ∈ Q}

theorem mem_levyExtensionFamily_iff (p : LevyPolarity) (B q : V) : q ∈ levyExtensionFamily p B ↔
    q ∈ formulaFamily (membershipLanguageCode : V) ∅ ∧ ∀ Q : V, IsLevyExtensionClosed p B Q → q ∈ Q := by
  simp [levyExtensionFamily]

instance levyExtensionFamily_definable (p : LevyPolarity) : ℒₛₑₜ-function₁[V] (levyExtensionFamily p) := by
  have h : ℒₛₑₜ-relation (fun F B : V ↦ ∀ q, q ∈ F ↔
      q ∈ formulaFamily (membershipLanguageCode : V) ∅ ∧ ∀ Q : V, IsLevyExtensionClosed p B Q → q ∈ Q) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = levyExtensionFamily p (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_levyExtensionFamily_iff]

theorem levyExtensionFamily_subset (p : LevyPolarity) (B : V) :
    levyExtensionFamily p B ⊆ formulaFamily membershipLanguageCode ∅ :=
  fun q hq ↦ ((mem_levyExtensionFamily_iff p B q).mp hq).1

theorem levyExtensionFamily_minimal {p : LevyPolarity} {B Q : V} (hQ : IsLevyExtensionClosed p B Q) :
    levyExtensionFamily p B ⊆ Q := fun q hq ↦ ((mem_levyExtensionFamily_iff p B q).mp hq).2 Q hQ

theorem levyExtensionFamily_closed (p : LevyPolarity) {B : V}
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) :
    IsLevyExtensionClosed p B (levyExtensionFamily p B) := by
  have hf := formulaFamily_levyClosed p hB
  refine ⟨?_, ?_⟩
  · intro q hq
    exact (mem_levyExtensionFamily_iff p B q).mpr ⟨hB q hq, fun Q hQ ↦ hQ.1 q hq⟩
  · intro n hn
    refine ⟨?_, ?_, ?_⟩
    · intro φ ψ hφ hψ
      have hv := (hf.2 n hn).1 φ ψ (levyExtensionFamily_subset p B _ hφ) (levyExtensionFamily_subset p B _ hψ)
      exact ⟨(mem_levyExtensionFamily_iff p B _).mpr ⟨hv.1, fun Q hQ ↦
          ((hQ.2 n hn).1 φ ψ (levyExtensionFamily_minimal hQ _ hφ) (levyExtensionFamily_minimal hQ _ hψ)).1⟩,
        (mem_levyExtensionFamily_iff p B _).mpr ⟨hv.2, fun Q hQ ↦
          ((hQ.2 n hn).1 φ ψ (levyExtensionFamily_minimal hQ _ hφ) (levyExtensionFamily_minimal hQ _ hψ)).2⟩⟩
    · intro i hi φ hφ
      have hv := (hf.2 n hn).2.1 i hi φ (levyExtensionFamily_subset p B _ hφ)
      exact ⟨(mem_levyExtensionFamily_iff p B _).mpr ⟨hv.1, fun Q hQ ↦
          ((hQ.2 n hn).2.1 i hi φ (levyExtensionFamily_minimal hQ _ hφ)).1⟩,
        (mem_levyExtensionFamily_iff p B _).mpr ⟨hv.2, fun Q hQ ↦
          ((hQ.2 n hn).2.1 i hi φ (levyExtensionFamily_minimal hQ _ hφ)).2⟩⟩
    · intro φ hφ
      exact (mem_levyExtensionFamily_iff p B _).mpr
        ⟨(hf.2 n hn).2.2 φ (levyExtensionFamily_subset p B _ hφ), fun Q hQ ↦
          (hQ.2 n hn).2.2 φ (levyExtensionFamily_minimal hQ _ hφ)⟩

theorem levyExtensionFamily_induction (p : LevyPolarity) {B : V}
    (hB : B ⊆ formulaFamily membershipLanguageCode ∅) (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (hbase : ∀ q ∈ B, P q)
    (hb : ∀ n ∈ (ω : V), ∀ φ ψ, ⟨n, φ⟩ₖ ∈ levyExtensionFamily p B →
      ⟨n, ψ⟩ₖ ∈ levyExtensionFamily p B → P ⟨n, φ⟩ₖ → P ⟨n, ψ⟩ₖ →
      P ⟨n, andCode φ ψ⟩ₖ ∧ P ⟨n, orCode φ ψ⟩ₖ)
    (hq : ∀ n ∈ (ω : V), ∀ i ∈ n, ∀ φ, ⟨succ n, φ⟩ₖ ∈ levyExtensionFamily p B →
      P ⟨succ n, φ⟩ₖ → P ⟨n, boundedAllCode i φ⟩ₖ ∧ P ⟨n, boundedExistsCode i φ⟩ₖ)
    (hu : ∀ n ∈ (ω : V), ∀ φ, ⟨succ n, φ⟩ₖ ∈ levyExtensionFamily p B →
      P ⟨succ n, φ⟩ₖ → P ⟨n, levyQuantifierCode p φ⟩ₖ) :
    ∀ q ∈ levyExtensionFamily p B, P q := by
  let S : V := {q ∈ levyExtensionFamily p B ; P q}
  have hc := levyExtensionFamily_closed p hB
  have hS : IsLevyExtensionClosed p B S := by
    refine ⟨?_, ?_⟩
    · intro q hq
      exact mem_sep_iff.mpr ⟨hc.1 q hq, hbase q hq⟩
    · intro n hn
      refine ⟨?_, ?_, ?_⟩
      · intro φ ψ hφ hψ
        obtain ⟨hφf, hφP⟩ := mem_sep_iff.mp hφ
        obtain ⟨hψf, hψP⟩ := mem_sep_iff.mp hψ
        exact ⟨mem_sep_iff.mpr ⟨((hc.2 n hn).1 φ ψ hφf hψf).1, (hb n hn φ ψ hφf hψf hφP hψP).1⟩,
          mem_sep_iff.mpr ⟨((hc.2 n hn).1 φ ψ hφf hψf).2, (hb n hn φ ψ hφf hψf hφP hψP).2⟩⟩
      · intro i hi φ hφ
        obtain ⟨hφf, hφP⟩ := mem_sep_iff.mp hφ
        exact ⟨mem_sep_iff.mpr ⟨((hc.2 n hn).2.1 i hi φ hφf).1, (hq n hn i hi φ hφf hφP).1⟩,
          mem_sep_iff.mpr ⟨((hc.2 n hn).2.1 i hi φ hφf).2, (hq n hn i hi φ hφf hφP).2⟩⟩
      · intro φ hφ
        obtain ⟨hφf, hφP⟩ := mem_sep_iff.mp hφ
        exact mem_sep_iff.mpr ⟨(hc.2 n hn).2.2 φ hφf, hu n hn φ hφf hφP⟩
  intro q hq
  exact (mem_sep_iff.mp (levyExtensionFamily_minimal hS q hq)).2

noncomputable def levyFormulaFamily : ℕ → LevyPolarity → V
  | 0, _ => boundedFormulaFamily
  | k + 1, p => levyExtensionFamily p (levyFormulaFamily k .sigma ∪ levyFormulaFamily k .pi)

theorem levyFormulaFamily_subset (k : ℕ) (p : LevyPolarity) :
    (levyFormulaFamily k p : V) ⊆ formulaFamily membershipLanguageCode ∅ := by
  cases k
  · exact boundedFormulaFamily_subset
  · exact levyExtensionFamily_subset _ _

theorem levyFormulaFamily_successor_closed (k : ℕ) (p : LevyPolarity) :
    IsLevyExtensionClosed p (levyFormulaFamily k .sigma ∪ levyFormulaFamily k .pi) (levyFormulaFamily (k + 1) p : V) := by
  apply levyExtensionFamily_closed
  intro q hq
  rcases mem_union_iff.mp hq with hq | hq
  · exact levyFormulaFamily_subset k .sigma q hq
  · exact levyFormulaFamily_subset k .pi q hq

def IsLevyFormulaCode (p : LevyPolarity) (k : ℕ) (n φ : V) : Prop := ⟨n, φ⟩ₖ ∈ (levyFormulaFamily k p : V)

instance isLevyFormulaCode_definable (p : LevyPolarity) (k : ℕ) : ℒₛₑₜ-relation[V] (IsLevyFormulaCode p k) := by
  unfold IsLevyFormulaCode
  definability

theorem IsLevyFormulaCode.valid {p k} {n φ : V} (hφ : IsLevyFormulaCode p k n φ) :
    φ ∈ formulaSet membershipLanguageCode ∅ n :=
  (mem_formulaSet_iff _ _ _ _).mpr (levyFormulaFamily_subset k p _ hφ)

theorem IsLevyFormulaCode.context {p k} {n φ : V} (hφ : IsLevyFormulaCode p k n φ) : n ∈ (ω : V) :=
  formulaSet_context membershipLanguageCode_valid hφ.valid

theorem isLevyFormulaCode_zero_iff (p : LevyPolarity) (n φ : V) :
    IsLevyFormulaCode p 0 n φ ↔ IsBoundedFormulaCode n φ := Iff.rfl

theorem IsLevyFormulaCode.raise {p q k} {n φ : V} (hφ : IsLevyFormulaCode p k n φ) :
    IsLevyFormulaCode q (k + 1) n φ := by
  apply (levyFormulaFamily_successor_closed k q).1
  cases p
  · exact mem_union_iff.mpr (Or.inl hφ)
  · exact mem_union_iff.mpr (Or.inr hφ)

theorem IsLevyFormulaCode.bounded {p k} {n φ : V} (hφ : IsBoundedFormulaCode n φ) :
    IsLevyFormulaCode p k n φ := by
  induction k with
  | zero => exact hφ
  | succ k ih => exact ih.raise

theorem IsLevyFormulaCode.mono {p k l} {n φ : V} (hφ : IsLevyFormulaCode p k n φ) (hkl : k ≤ l) :
    IsLevyFormulaCode p l n φ := by
  induction hkl with
  | refl => exact hφ
  | step _ ih => exact ih.raise

theorem IsLevyFormulaCode.and {p k} {n φ ψ : V} (hφ : IsLevyFormulaCode p k n φ) (hψ : IsLevyFormulaCode p k n ψ) :
    IsLevyFormulaCode p k n (andCode φ ψ) := by
  cases k with
  | zero => exact ((boundedFormulaFamily_closed n hφ.context).2.2.1 φ ψ hφ hψ).1
  | succ k => exact (((levyFormulaFamily_successor_closed k p).2 n hφ.context).1 φ ψ hφ hψ).1

theorem IsLevyFormulaCode.or {p k} {n φ ψ : V} (hφ : IsLevyFormulaCode p k n φ) (hψ : IsLevyFormulaCode p k n ψ) :
    IsLevyFormulaCode p k n (orCode φ ψ) := by
  cases k with
  | zero => exact ((boundedFormulaFamily_closed n hφ.context).2.2.1 φ ψ hφ hψ).2
  | succ k => exact (((levyFormulaFamily_successor_closed k p).2 n hφ.context).1 φ ψ hφ hψ).2

theorem IsLevyFormulaCode.boundedAll {p k} {n i φ : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : IsLevyFormulaCode p k (succ n) φ) : IsLevyFormulaCode p k n (boundedAllCode i φ) := by
  cases k with
  | zero => exact ((boundedFormulaFamily_closed n hn).2.2.2 i hi φ hφ).1
  | succ k => exact (((levyFormulaFamily_successor_closed k p).2 n hn).2.1 i hi φ hφ).1

theorem IsLevyFormulaCode.boundedExists {p k} {n i φ : V} (hn : n ∈ (ω : V)) (hi : i ∈ n)
    (hφ : IsLevyFormulaCode p k (succ n) φ) : IsLevyFormulaCode p k n (boundedExistsCode i φ) := by
  cases k with
  | zero => exact ((boundedFormulaFamily_closed n hn).2.2.2 i hi φ hφ).2
  | succ k => exact (((levyFormulaFamily_successor_closed k p).2 n hn).2.1 i hi φ hφ).2

theorem IsLevyFormulaCode.quantifier {p k} {n φ : V} (hn : n ∈ (ω : V))
    (hφ : IsLevyFormulaCode p (k + 1) (succ n) φ) : IsLevyFormulaCode p (k + 1) n (levyQuantifierCode p φ) :=
  ((levyFormulaFamily_successor_closed k p).2 n hn).2.2 φ hφ

theorem levyFormulaCode_successor_induction (k : ℕ) (p : LevyPolarity)
    (P : V → V → Prop) (hP : ℒₛₑₜ-relation P)
    (hbase : ∀ q n φ, IsLevyFormulaCode q k n φ → P n φ)
    (hb : ∀ n ∈ (ω : V), ∀ φ ψ, IsLevyFormulaCode p (k + 1) n φ →
      IsLevyFormulaCode p (k + 1) n ψ → P n φ → P n ψ → P n (andCode φ ψ) ∧ P n (orCode φ ψ))
    (hq : ∀ n ∈ (ω : V), ∀ i ∈ n, ∀ φ, IsLevyFormulaCode p (k + 1) (succ n) φ →
      P (succ n) φ → P n (boundedAllCode i φ) ∧ P n (boundedExistsCode i φ))
    (hu : ∀ n ∈ (ω : V), ∀ φ, IsLevyFormulaCode p (k + 1) (succ n) φ →
      P (succ n) φ → P n (levyQuantifierCode p φ)) :
    ∀ n φ, IsLevyFormulaCode p (k + 1) n φ → P n φ := by
  have hB : (levyFormulaFamily k .sigma : V) ∪ levyFormulaFamily k .pi ⊆
      formulaFamily membershipLanguageCode ∅ := by
    intro q hq
    exact (mem_union_iff.mp hq).elim (levyFormulaFamily_subset k .sigma q) (levyFormulaFamily_subset k .pi q)
  have hall : ∀ q ∈ levyExtensionFamily p ((levyFormulaFamily k .sigma : V) ∪ levyFormulaFamily k .pi),
      P (kpair.π₁ q) (kpair.π₂ q) := by
    refine levyExtensionFamily_induction p hB (fun q ↦ P (kpair.π₁ q) (kpair.π₂ q)) (by definability)
      ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨n, _, φ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ (hB q hq)
      simp only [kpair.π₁_kpair, kpair.π₂_kpair]
      exact (mem_union_iff.mp hq).elim (hbase .sigma n φ) (hbase .pi n φ)
    · intro n hn φ ψ hφ hψ ihφ ihψ
      simpa using hb n hn φ ψ hφ hψ (by simpa using ihφ) (by simpa using ihψ)
    · intro n hn i hi φ hφ ih
      simpa using hq n hn i hi φ hφ (by simpa using ih)
    · intro n hn φ hφ ih
      simpa using hu n hn φ hφ (by simpa using ih)
  intro n φ hφ
  simpa using hall ⟨n, φ⟩ₖ hφ

theorem IsLevyFormula.encode {p k n} {φ : SetTheorySemisentence n} (hφ : IsLevyFormula p k φ) :
    IsLevyFormulaCode p k (n : V) (encodeMembershipFormula φ) := by
  induction hφ with
  | bounded hφ => exact IsLevyFormulaCode.bounded hφ.encode
  | raise hφ ih => exact ih.raise
  | and hφ hψ ihφ ihψ => exact ihφ.and ihψ
  | or hφ hψ ihφ ihψ => exact ihφ.or ihψ
  | boundedAll t hφ ih =>
    cases t with
    | bvar i =>
      rw [encodeMembershipFormula_boundedAll]
      exact IsLevyFormulaCode.boundedAll (by simp) (natCast_mem_of_lt i.isLt)
        (by simpa [num_succ_def] using ih)
    | fvar x => exact Empty.elim x
    | func f ts => exact Empty.elim f
  | boundedExs t hφ ih =>
    cases t with
    | bvar i =>
      rw [encodeMembershipFormula_boundedExists]
      exact IsLevyFormulaCode.boundedExists (by simp) (natCast_mem_of_lt i.isLt)
        (by simpa [num_succ_def] using ih)
    | fvar x => exact Empty.elim x
    | func f ts => exact Empty.elim f
  | exs hφ ih =>
    exact IsLevyFormulaCode.quantifier (by simp) (by simpa only [num_succ_def, encodeMembershipFormula] using ih)
  | all hφ ih =>
    exact IsLevyFormulaCode.quantifier (by simp) (by simpa only [num_succ_def, encodeMembershipFormula] using ih)

end ZFVP
