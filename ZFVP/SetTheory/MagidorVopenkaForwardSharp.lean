import ZFVP.SetTheory.MagidorVopenkaForward
import ZFVP.ModelTheory.GenericRankEmbeddingZFRestriction

/-! Pi-one Vopenka from high-critical small embeddings between C(1) ranks modeling ZF.
Arbitrary-language elementarity uses end-extension absoluteness, with no syntax dictionary bound.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem eval_magidorReflectionFormula_components {W : Type*} [SetStructure W]
    (φ : SetTheorySemisentence 2) (α a : W) :
    (magidorReflectionFormula φ).Evalb ![α, a] ↔
      ∃ X r : W, piOneRankFormula.Evalb ![r, X] ∧ α ∈ r ∧ φ.Evalb ![X, a] := by
  simp [magidorReflectionFormula]

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsZFRank (δ : V) : Prop :=
  ∃ hne : Nonempty (SetDomain (hierarchy δ)),
    letI := hne
    (SetDomain (hierarchy δ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙

/-- Cofinally many target ranks suffice; both ranks are C(1) and model ZF. -/
def IsZFHighCriticalMagidorSupercompact (κ : V) : Prop :=
  IsOrdinal κ ∧ (ω : V) ∈ κ ∧
    ∀ ρ, IsOrdinal ρ → κ ∈ ρ → ∀ η ∈ κ,
      ∃ γ, ρ ∈ γ ∧ Cn 1 γ ∧ IsZFRank γ ∧
        ∃ β ∈ κ, Cn 1 β ∧ IsZFRank β ∧
          ∃ α ∈ β, η ∈ α ∧ ∃ e,
            IsCodedMembershipEmbedding (hierarchy β) (hierarchy γ) e ∧
            IsCriticalPoint (hierarchy β) e α ∧ e ‘ α = κ

/-- The sharp forward implication uses only C(1) correctness and rank models of ZF. -/
theorem magidorSupercompact_unbounded_implies_pi_one_vopenka_zf
    (hM : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsZFHighCriticalMagidorSupercompact κ)
    (φ : SetTheorySemisentence 2) (hφ : IsPiFormula 1 φ) : VopenkaInstance (V := V) φ := by
  intro L a hproper hclass
  let b := ⟨L, ⟨a, syntaxUniverse L ∅⟩ₖ⟩ₖ
  obtain ⟨κ, hbκ, hκ⟩ := hM (rank b) inferInstance
  let := hκ.1
  obtain ⟨C, hCclass, hκC⟩ := hproper.rank_unbounded κ
  obtain ⟨γ, hCγ, hγ, hγZF, β, hβκ, hβ, hβZF, α, hαβ, hbα, e, he, hc, heα⟩ :=
    hκ.2.2 (rank C) inferInstance hκC (rank b) hbκ
  let := hγ.ordinal
  let := hierarchy_transitive γ
  have hκγ : κ ∈ γ := IsOrdinal.toIsTransitive.mem_trans hκC hCγ
  obtain ⟨hβne, hβZF⟩ := hβZF
  obtain ⟨hγne, hγZF⟩ := hγZF
  let := hβne
  let := hγne
  let := hβZF
  let := hγZF
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
  have hφn : IsPiFormula 1 φ := hφ
  let : Defined (fun v : Fin 2 → V ↦ φ.Evalb v) φ := ⟨fun _ ↦ Iff.rfl⟩
  have hafix : e ‘ a = a := rankEmbedding_fixed_below_criticalPoint hβ hγ he hc a haα
  -- the class has a member of rank above `κ` inside `V_γ`
  have hγΘ : (magidorReflectionFormula φ).Evalb
      (![⟨κ, hκV⟩, ⟨a, haγ⟩] : Fin 2 → SetDomain (hierarchy γ)) := by
    apply (eval_magidorReflectionFormula_components (W := SetDomain (hierarchy γ)) φ
      (⟨κ, hκV⟩ : SetDomain (hierarchy γ)) ⟨a, haγ⟩).mpr
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
  have hβΘ := (eval_magidorReflectionFormula_components (W := SetDomain (hierarchy β)) φ
    (⟨α, hαV⟩ : SetDomain (hierarchy β)) ⟨a, haβ⟩).mp hβΘ
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
  have hgeneric := rankEmbedding_generic_restrict_zf hβ hγ he hc hLα
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

end ZFVP
