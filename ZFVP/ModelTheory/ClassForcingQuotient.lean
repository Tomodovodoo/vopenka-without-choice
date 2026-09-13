import ZFVP.ModelTheory.ForcingQuotient
import ZFVP.SetTheory.ClassFormulaForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def ClassForcingQuotient (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (N : V → Prop) (hnames : ∀ x, N x → IsForcingName P x) :=
  {x : ForcingQuotient P R G hR hG //
    ∃ σ : V, ∃ hσ : N σ, x = forcingQuotientMk P R G hR hG ⟨σ, hnames σ hσ⟩}

namespace ClassForcingQuotient

variable (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingFilter P R G) (N : V → Prop) (hnames : ∀ x, N x → IsForcingName P x)

instance setStructure : SetStructure (ClassForcingQuotient P R G hR hG N hnames) where
  mem y x := x.val ∈ y.val

def ofName (σ : {x : V // N x}) : ClassForcingQuotient P R G hR hG N hnames :=
  ⟨forcingQuotientMk P R G hR hG ⟨σ.val, hnames σ.val σ.property⟩, σ.val, σ.property, rfl⟩

theorem ofName_surjective : Function.Surjective (ofName P R G hR hG N hnames) := by
  intro x
  obtain ⟨σ, hσ, hx⟩ := x.property
  exact ⟨⟨σ, hσ⟩, Subtype.ext hx.symm⟩

instance nonempty [Nonempty {x : V // N x}] :
    Nonempty (ClassForcingQuotient P R G hR hG N hnames) :=
  Nonempty.map (ofName P R G hR hG N hnames) inferInstance

theorem ofName_eq_iff (σ τ : {x : V // N x}) :
    ofName P R G hR hG N hnames σ = ofName P R G hR hG N hnames τ ↔
      GenericMeets G (atomicEquality P R σ.val τ.val) := by
  unfold ofName ClassForcingQuotient
  rw [Subtype.mk.injEq]
  exact forcingQuotientMk_eq_iff P R G hR hG _ _

theorem ofName_mem_iff (σ τ : {x : V // N x}) :
    ofName P R G hR hG N hnames σ ∈ ofName P R G hR hG N hnames τ ↔
      GenericMeets G (atomicMembership P R σ.val τ.val) := Iff.rfl

def assignment {n : ℕ} (v : Fin n → {x : V // N x}) :
    Fin n → ClassForcingQuotient P R G hR hG N hnames :=
  fun i ↦ ofName P R G hR hG N hnames (v i)

theorem assignment_cons {n : ℕ} (v : Fin n → {x : V // N x}) (σ : {x : V // N x}) :
    assignment P R G hR hG N hnames (σ :> v) =
      ofName P R G hR hG N hnames σ :> assignment P R G hR hG N hnames v := by
  funext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

def nameTerm {n : ℕ} (v : Fin n → {x : V // N x}) :
    Semiterm ℒₛₑₜ Empty n → {x : V // N x}
  | .bvar i => v i
  | .fvar x => Empty.elim x
  | .func f _ => Empty.elim f

theorem term_value {n : ℕ} (v : Fin n → {x : V // N x}) (t : Semiterm ℒₛₑₜ Empty n) :
    t.val (assignment P R G hR hG N hnames v) Empty.elim =
      ofName P R G hR hG N hnames (nameTerm N v t) := by
  cases t with
  | bvar _ => rfl
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem term_tuple {n : ℕ} (v : Fin n → {x : V // N x}) (t : Semiterm ℒₛₑₜ Empty n) :
    forcingTermValue t (standardTuple (fun i ↦ (v i).val)) = (nameTerm N v t).val := by
  cases t with
  | bvar i => exact value_standardTuple _ i
  | fvar x => exact Empty.elim x
  | func f _ => exact Empty.elim f

theorem nameTuple_cons {n : ℕ} (v : Fin n → {x : V // N x}) (σ : {x : V // N x}) :
    standardTuple (fun i ↦ ((σ :> v) i).val) =
      assignmentPrepend (n : V) (standardTuple (fun i ↦ (v i).val)) σ.val := rfl

theorem atomic_truth {n k : ℕ} (r : Language.Set.Rel k)
    (ts : Fin k → Semiterm ℒₛₑₜ Empty n) (v : Fin n → {x : V // N x}) :
    (Semiformula.rel r ts).Evalb (assignment P R G hR hG N hnames v) ↔
      GenericMeets G (forcingAtomic P R r ts (standardTuple (fun i ↦ (v i).val))) := by
  cases r <;> simp only [forcingAtomic, Semiformula.eval_rel, term_value,
    term_tuple, Function.comp_def]
  · exact ofName_eq_iff P R G hR hG N hnames _ _
  · exact ofName_mem_iff P R G hR hG N hnames _ _

end ClassForcingQuotient
end ZFVP
