import ZFVP.SetTheory.VopenkaScheme
import ZFVP.SetTheory.MagidorSupercompact
import ZFVP.SetTheory.DeltaOneRank
import ZFVP.ModelTheory.GenericRankEmbeddingRestriction
import ZFVP.ModelTheory.RankEmbeddingDictionary

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! # Bagaria, Theorem 4.3, the Pi(1) case, forward direction

A proper class of small-embedding supercompact cardinals gives every Pi(1) instance of the
parameterized arbitrary-language Vopenka scheme.

The hypothesis used is not the plain predicate `IsMagidorSupercompact` of
`ZFVP.SetTheory.MagidorSupercompact` but the strengthened
`IsCorrectHighCriticalMagidorSupercompact`, which asks the same small embeddings
`e : V_β → V_γ` with critical point `ab` and `e(ab) = κ` and adds two clauses:

* the critical point can be pushed above any prescribed `η ∈ κ`, and
* the source rank `β` is a `C(n+1)` stage.

Both are used, and the docstring of the definition says where. Neither is available from
`IsMagidorSupercompact` as stated, and deriving them is the ZFC content that this project does
not formalize: it is the ultrapower half of Magidor's characterization, which needs a normal
fine measure on `P_κ(γ)` and the closure of the target model under `γ`-sequences.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Some `X` satisfying the class formula with the second variable has rank above the first
variable. Read inside a rank stage this says that the class has a member of rank above `α`
in that stage. -/
def magidorReflectionFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 2 :=
  “α a. ∃ X r, !piOneRankFormula r X ∧ α ∈ r ∧ !φ X a”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Magidor's small embedding into `V_γ` with two extra clauses: the critical point `ab` is
above the prescribed ordinal `η`, and the source rank `lb` is a `C(n+1)` stage.

The first clause is what makes the embedding fix the parameters of a Vopenka instance: the
parameter `a`, the language code `L` and its syntax universe all have rank below `ab`, so `e`
is the identity on them. The plain predicate `IsMagidorSupercompactAt` says nothing about where
`ab` sits below `κ`, so it cannot fix a prescribed parameter.

The second clause is what makes `V_lb` compute the syntax dictionary and the class formula
correctly, which is needed to read the reflected statement off the source rank and to restrict
`e` to an elementary embedding of coded structures. The same clause on the source rank appears
in the project's other small-embedding criterion, `SmallEmbeddingCriterion`. -/
def IsCorrectHighCriticalMagidorSupercompactAt (n : ℕ) (κ γ η : V) : Prop :=
  ∃ lb ∈ κ, Cn (n + 1) lb ∧ ∃ ab ∈ lb, η ∈ ab ∧ ∃ e,
    IsCodedMembershipEmbedding (hierarchy lb) (hierarchy γ) e ∧
    IsCriticalPoint (hierarchy lb) e ab ∧ e ‘ ab = κ

/-- `κ` is an ordinal above `ω` admitting, at every rank above `κ` and for every prescribed
`η ∈ κ`, a small embedding with `C(n+1)` source and critical point above `η` sent to `κ`. -/
def IsCorrectHighCriticalMagidorSupercompact (n : ℕ) (κ : V) : Prop :=
  IsOrdinal κ ∧ (ω : V) ∈ κ ∧
    ∀ γ, IsOrdinal γ → κ ∈ γ → ∀ η ∈ κ, IsCorrectHighCriticalMagidorSupercompactAt n κ γ η

/-- The strengthened predicate implies the plain one, so it is a genuine strengthening and not
a different statement: drop the two extra clauses and take `η := ∅`. -/
theorem IsCorrectHighCriticalMagidorSupercompact.magidorSupercompact {n : ℕ} {κ : V}
    (h : IsCorrectHighCriticalMagidorSupercompact n κ) : IsMagidorSupercompact κ := by
  refine ⟨h.1, ?_⟩
  intro γ hγ hκγ
  let := h.1
  have hzκ : (∅ : V) ∈ κ :=
    IsOrdinal.toIsTransitive.mem_trans (show (∅ : V) ∈ (ω : V) by simp) h.2.1
  obtain ⟨lb, hlb, _, ab, hab, _, e, he, hc, hec⟩ := h.2.2 γ hγ hκγ ∅ hzκ
  exact ⟨lb, hlb, ab, hab, e, he, hc, hec⟩

/-- Bagaria, Theorem 4.3, Pi(1) case, forward direction: a proper class of small-embedding
supercompact cardinals in the strengthened sense gives every Pi(1) instance of the
parameterized arbitrary-language Vopenka scheme.

The proof takes a class member `C` of rank above `κ`, a correct stage `γ` above `rank C`, and
a small embedding `e : V_β → V_γ` with critical point `α` above the rank of the parameters and
`e(α) = κ`. The statement "the class has a member of rank above the first variable" holds in
`V_γ` at `κ`, witnessed by `C`, so by elementarity it holds in `V_β` at `α`, witnessed by some
`X ∈ V_β`. Then `X` and `e(X)` are two class members and `e` restricted to the domain of `X`
is an elementary embedding between them; they differ because `rank X ∈ β ∈ κ ∈ rank (e(X))`.

Nothing here has to stay Pi(1) except `φ` itself: the stages `β` and `γ` are used with full
`C(n+1)` correctness. What `φ` being Pi(1) buys is that one fixed correctness level works for
every instance of the scheme at once. -/
theorem magidorSupercompact_unbounded_implies_pi_one_vopenka_of_bound {k : ℕ}
    (hk : coreSyntaxDictionaryBound ≤ k + 1)
    (hM : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧
      IsCorrectHighCriticalMagidorSupercompact k κ)
    (φ : SetTheorySemisentence 2) (hφ : IsPiFormula 1 φ) : VopenkaInstance (V := V) φ := by
  intro L a hproper hclass
  let b := ⟨L, ⟨a, syntaxUniverse L ∅⟩ₖ⟩ₖ
  obtain ⟨κ, hbκ, hκ⟩ := hM (rank b) inferInstance
  let := hκ.1
  obtain ⟨C, hCclass, hκC⟩ := hproper.rank_unbounded κ
  obtain ⟨γ, hCγ, hγ⟩ := cn_unbounded (k + 1) (rank C)
  let := hγ.ordinal
  let := hierarchy_transitive γ
  have hκγ : κ ∈ γ := IsOrdinal.toIsTransitive.mem_trans hκC hCγ
  obtain ⟨β, hβκ, hβ, α, hαβ, hbα, e, he, hc, heα⟩ := hκ.2.2 γ hγ.ordinal hκγ (rank b) hbκ
  let := hβ.ordinal
  let := IsOrdinal.of_mem hαβ
  let := hierarchy_transitive β
  let := hierarchy_transitive α
  let := IsFunction.of_mem he.function
  have hbα' : b ∈ hierarchy α := (mem_hierarchy_iff_rank_mem _ _).mpr hbα
  obtain ⟨hLα, hap⟩ := kpair_components_mem_transitive hbα'
  obtain ⟨haα, hsyntaxα⟩ := kpair_components_mem_transitive hap
  have hβγ : β ∈ γ := IsOrdinal.toIsTransitive.mem_trans hβκ hκγ
  have hαV : α ∈ hierarchy β := ordinal_subset_hierarchy β α hαβ
  have haβ : a ∈ hierarchy β := (hierarchy_transitive β).mem_trans haα (hierarchy_mem hαβ)
  have hκV : κ ∈ hierarchy γ := ordinal_subset_hierarchy γ κ hκγ
  have haγ : a ∈ hierarchy γ := (hierarchy_transitive γ).mem_trans haβ (hierarchy_mem hβγ)
  have hCγV : C ∈ hierarchy γ := (mem_hierarchy_iff_rank_mem _ _).mpr hCγ
  have hrCγ : rank C ∈ hierarchy γ := ordinal_subset_hierarchy γ (rank C) hCγ
  have hφn : IsPiFormula (k + 1) φ := hφ.mono (Nat.succ_le_succ (Nat.zero_le k))
  let : Defined (fun v : Fin 2 → V ↦ φ.Evalb v) φ := ⟨fun _ ↦ Iff.rfl⟩
  have hafix : e ‘ a = a := rankEmbedding_fixed_below_criticalPoint hβ hγ he hc a haα
  -- the class has a member of rank above `κ` inside `V_γ`
  have hγΘ : (magidorReflectionFormula φ).Evalb
      (![⟨κ, hκV⟩, ⟨a, haγ⟩] : Fin 2 → SetDomain (hierarchy γ)) := by
    simp only [magidorReflectionFormula]
    simp
    refine ⟨⟨C, hCγV⟩, ⟨rank C, hrCγ⟩, ?_, hκC, ?_⟩
    · exact (hγ.rank_formula_correct ⟨rank C, hrCγ⟩ ⟨C, hCγV⟩).mpr rfl
    · have hd := hγ.defined_correct hφn (fun v ↦ φ.Evalb v)
        ![⟨C, hCγV⟩, ⟨a, haγ⟩]
      have hv : (fun i ↦ ((![⟨C, hCγV⟩, ⟨a, haγ⟩] : Fin 2 → SetDomain (hierarchy γ)) i).val)
          = ![C, a] := by
        funext i
        exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
      rw [hv] at hd
      exact hd.mpr hCclass
  -- pull it back along the embedding, which fixes `a` and sends `α` to `κ`
  have hβΘ : (magidorReflectionFormula φ).Evalb
      (![⟨α, hαV⟩, ⟨a, haβ⟩] : Fin 2 → SetDomain (hierarchy β)) := by
    rw [he.eval_semisentence]
    convert hγΘ using 2
    funext i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun t ↦ Fin.elim0 t) j) i
    · exact Subtype.ext heα
    · exact Subtype.ext hafix
  simp only [magidorReflectionFormula] at hβΘ
  simp at hβΘ
  obtain ⟨X, r, hr, hαr, hφX⟩ := hβΘ
  have hrX : r.val = rank X.val := (hβ.rank_formula_correct r X).mp hr
  have hXβ : X.val ∈ hierarchy β := X.property
  have hφX' : φ.Evalb ![X.val, a] := by
    have hd := hβ.defined_correct hφn (fun v ↦ φ.Evalb v) ![X, ⟨a, haβ⟩]
    have hv : (fun i ↦ ((![X, ⟨a, haβ⟩] : Fin 2 → SetDomain (hierarchy β)) i).val)
        = ![X.val, a] := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.elim0 t) j) i
    rw [hv] at hd
    exact hd.mp hφX
  -- the image of `X` is a second member of the class
  have hetr := rankEmbedding_defined_iff hβ hγ he hφn (fun v ↦ φ.Evalb v) ![X.val, a]
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hXβ, haβ])
  have hv : (fun i ↦ e ‘ ((![X.val, a] : Fin 2 → V) i)) = ![e ‘ X.val, a] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases hafix (fun t ↦ Fin.elim0 t) j) i
  rw [hv] at hetr
  have htarget := hetr.mp hφX'
  -- and `e` restricted to the domain of `X` is an elementary embedding between them
  have hgeneric := rankEmbedding_generic_restrict hβ hγ he hc hk hLα
    ((hierarchy_transitive α).transitive _ hsyntaxα) (hclass X.val hφX') hXβ
  have hrank : e ‘ (rank X.val) = rank (e ‘ X.val) := rankEmbedding_value_rank hβ hγ he hXβ
  have hmem : κ ∈ rank (e ‘ X.val) := by
    have hm := (he.value_mem_iff hαV (hβ.rank_closed hXβ)).mpr (hrX ▸ hαr)
    rwa [heα, hrank] at hm
  have hne : X.val ≠ e ‘ X.val := by
    intro hs
    rw [← hs] at hmem
    have h1 : rank X.val ∈ β := (mem_hierarchy_iff_rank_mem _ _).mp hXβ
    have h2 : rank X.val ∈ κ := IsOrdinal.toIsTransitive.mem_trans h1 hβκ
    exact mem_irrefl κ (IsOrdinal.toIsTransitive.mem_trans hmem h2)
  exact ⟨X.val, e ‘ X.val, e ↾ (structureDomain X.val), hne, hφX', htarget, hgeneric⟩

/-- The same statement at the one fixed correctness level that works for every Pi(1) instance:
`coreSyntaxDictionaryBound`, the level at which a rank stage computes the coded syntax
dictionary. -/
theorem magidorSupercompact_unbounded_implies_pi_one_vopenka
    (hM : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧
      IsCorrectHighCriticalMagidorSupercompact coreSyntaxDictionaryBound κ)
    (φ : SetTheorySemisentence 2) (hφ : IsPiFormula 1 φ) : VopenkaInstance (V := V) φ :=
  magidorSupercompact_unbounded_implies_pi_one_vopenka_of_bound (Nat.le_add_right _ 1) hM φ hφ

end ZFVP
