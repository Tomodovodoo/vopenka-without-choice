import Mathlib.SetTheory.Cardinal.Aleph
import ZFVP.SetTheory.ElementaryMap

/-! Elementary chains of models of set theory, indexed by an external linear order, and their
colimits. The main result is the Tarski-Vaught elementary chain theorem: each stage embeds
elementarily into the colimit, so the colimit models every theory all the stages model. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- A chain of models of ZF indexed by a linear order, with elementary transition maps that are
the identity at a stage and compose along the order. -/
structure ElementaryChain (I : Type u) [LinearOrder I] where
  /-- The model at stage `i`. -/
  Model : I → Type u
  /-- The membership relation on each stage. -/
  setStructure : ∀ i, SetStructure (Model i)
  /-- Each stage is nonempty. -/
  nonempty : ∀ i, Nonempty (Model i)
  /-- Each stage models ZF. -/
  models : ∀ i, letI := setStructure i; letI := nonempty i; (Model i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙
  /-- The transition map from an earlier stage to a later one. -/
  map : ∀ {i j : I}, i ≤ j →
    letI := setStructure i; letI := setStructure j; ElementaryMap (Model i) (Model j)
  /-- The transition map from a stage to itself is the identity. -/
  map_self : ∀ (i : I) (h : i ≤ i) (x : Model i),
    letI := setStructure i; (map h).toFun x = x
  /-- Transition maps compose. -/
  map_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : Model i),
    letI := setStructure i; letI := setStructure j; letI := setStructure k;
    (map (hij.trans hjk)).toFun x = (map hjk).toFun ((map hij).toFun x)

namespace ElementaryChain

variable {I : Type u} [LinearOrder I]

instance instSetStructure (C : ElementaryChain I) (i : I) : SetStructure (C.Model i) :=
  C.setStructure i

instance instNonempty (C : ElementaryChain I) (i : I) : Nonempty (C.Model i) :=
  C.nonempty i

instance instModelsZF (C : ElementaryChain I) (i : I) : (C.Model i)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 :=
  C.models i

variable (C : ElementaryChain I)

theorem map_apply_self (i : I) (h : i ≤ i) (x : C.Model i) : C.map h x = x :=
  C.map_self i h x

theorem map_map {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : C.Model i) :
    C.map hjk (C.map hij x) = C.map (hij.trans hjk) x :=
  (C.map_comp hij hjk x).symm

/-- Two elements of the disjoint union of the stages are identified when they already have the
same image at some later stage. -/
def Rel (a b : Σ i, C.Model i) : Prop :=
  ∃ (k : I) (hik : a.1 ≤ k) (hjk : b.1 ≤ k), C.map hik a.2 = C.map hjk b.2

/-- The identification can be tested at any common upper bound of the two stages. -/
theorem rel_iff {i j k : I} (x : C.Model i) (y : C.Model j) (hik : i ≤ k) (hjk : j ≤ k) :
    C.Rel ⟨i, x⟩ ⟨j, y⟩ ↔ C.map hik x = C.map hjk y := by
  constructor
  · rintro ⟨m, him, hjm, h⟩
    have e1 : C.map (le_max_left k m) (C.map hik x) = C.map (le_max_right k m) (C.map him x) := by
      rw [C.map_map hik (le_max_left k m), C.map_map him (le_max_right k m)]
    have e2 : C.map (le_max_left k m) (C.map hjk y) = C.map (le_max_right k m) (C.map hjm y) := by
      rw [C.map_map hjk (le_max_left k m), C.map_map hjm (le_max_right k m)]
    refine (C.map (le_max_left k m)).injective ?_
    rw [e1, e2, h]
  · intro h
    exact ⟨k, hik, hjk, h⟩

instance chainSetoid : Setoid (Σ i, C.Model i) where
  r := C.Rel
  iseqv := by
    refine ⟨fun a ↦ ⟨a.1, le_refl _, le_refl _, rfl⟩, ?_, ?_⟩
    · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, hik, hjk, h⟩
      exact ⟨k, hjk, hik, h.symm⟩
    · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨l, z⟩ h1 h2
      set k := max (max i j) l with hk
      have hik : i ≤ k := le_trans (le_max_left i j) (le_max_left _ _)
      have hjk : j ≤ k := le_trans (le_max_right i j) (le_max_left _ _)
      have hlk : l ≤ k := le_max_right _ _
      have e1 := (C.rel_iff x y hik hjk).mp h1
      have e2 := (C.rel_iff y z hjk hlk).mp h2
      exact (C.rel_iff x z hik hlk).mpr (e1.trans e2)

/-- The colimit of the chain: the disjoint union of the stages modulo eventual equality. -/
def ChainColimit : Type u := Quotient C.chainSetoid

/-- The image of a stage element in the colimit. -/
def ChainColimit.mk (C : ElementaryChain I) (i : I) (x : C.Model i) : ChainColimit C :=
  Quotient.mk C.chainSetoid ⟨i, x⟩

/-- Membership on the disjoint union, tested at the larger of the two stages. -/
def MemRel (a b : Σ i, C.Model i) : Prop :=
  C.map (le_max_left a.1 b.1) a.2 ∈ C.map (le_max_right a.1 b.1) b.2

/-- Membership can be tested at any common upper bound of the two stages. -/
theorem memRel_iff {i j k : I} (x : C.Model i) (y : C.Model j) (hik : i ≤ k) (hjk : j ≤ k) :
    C.MemRel ⟨i, x⟩ ⟨j, y⟩ ↔ C.map hik x ∈ C.map hjk y := by
  have hmk : max i j ≤ k := max_le hik hjk
  have h := (C.map hmk).map_mem_iff (C.map (le_max_left i j) x) (C.map (le_max_right i j) y)
  rw [C.map_map (le_max_left i j) hmk, C.map_map (le_max_right i j) hmk] at h
  exact h.symm

theorem memRel_congr {a₁ a₂ b₁ b₂ : Σ i, C.Model i} (ha : C.Rel a₁ a₂) (hb : C.Rel b₁ b₂) :
    C.MemRel a₁ b₁ ↔ C.MemRel a₂ b₂ := by
  obtain ⟨i₁, x₁⟩ := a₁
  obtain ⟨i₂, x₂⟩ := a₂
  obtain ⟨j₁, y₁⟩ := b₁
  obtain ⟨j₂, y₂⟩ := b₂
  set k := max (max i₁ i₂) (max j₁ j₂) with hk
  have h1 : i₁ ≤ k := le_trans (le_max_left i₁ i₂) (le_max_left _ _)
  have h2 : i₂ ≤ k := le_trans (le_max_right i₁ i₂) (le_max_left _ _)
  have h3 : j₁ ≤ k := le_trans (le_max_left j₁ j₂) (le_max_right _ _)
  have h4 : j₂ ≤ k := le_trans (le_max_right j₁ j₂) (le_max_right _ _)
  have ea := (C.rel_iff x₁ x₂ h1 h2).mp ha
  have eb := (C.rel_iff y₁ y₂ h3 h4).mp hb
  rw [C.memRel_iff x₁ y₁ h1 h3, C.memRel_iff x₂ y₂ h2 h4, ea, eb]

instance instSetStructureChainColimit : SetStructure (ChainColimit C) :=
  ⟨fun w z ↦ Quotient.liftOn₂ z w C.MemRel
    (fun _ _ _ _ ha hb ↦ propext (C.memRel_congr ha hb))⟩

namespace ChainColimit

variable {C}

theorem mk_eq_iff {i j k : I} (x : C.Model i) (y : C.Model j) (hik : i ≤ k) (hjk : j ≤ k) :
    mk C i x = mk C j y ↔ C.map hik x = C.map hjk y :=
  Iff.trans Quotient.eq (C.rel_iff x y hik hjk)

theorem mk_mem_iff {i j k : I} (x : C.Model i) (y : C.Model j) (hik : i ≤ k) (hjk : j ≤ k) :
    mk C i x ∈ mk C j y ↔ C.map hik x ∈ C.map hjk y :=
  C.memRel_iff x y hik hjk

theorem mk_eq_mk_iff {i : I} (x y : C.Model i) : mk C i x = mk C i y ↔ x = y := by
  rw [mk_eq_iff x y (le_refl i) (le_refl i), C.map_apply_self i (le_refl i),
    C.map_apply_self i (le_refl i)]

theorem mk_mem_mk_iff {i : I} (x y : C.Model i) : mk C i x ∈ mk C i y ↔ x ∈ y := by
  rw [mk_mem_iff x y (le_refl i) (le_refl i), C.map_apply_self i (le_refl i),
    C.map_apply_self i (le_refl i)]

/-- Moving an element to a later stage does not change its image in the colimit. -/
theorem mk_map {i k : I} (h : i ≤ k) (x : C.Model i) : mk C k (C.map h x) = mk C i x := by
  rw [mk_eq_iff (C.map h x) x (le_refl k) h, C.map_apply_self k (le_refl k)]

theorem mk_comp_map {i k : I} (h : i ≤ k) :
    mk C k ∘ (C.map h).toFun = mk C i :=
  funext fun x ↦ mk_map h x

/-- Every element of the colimit comes from some stage. -/
theorem exists_mk (C : ElementaryChain I) (z : ChainColimit C) :
    ∃ (i : I) (x : C.Model i), z = mk C i x :=
  Quotient.inductionOn z (fun a ↦ ⟨a.1, a.2, by cases a; rfl⟩)

instance instNonempty (C : ElementaryChain I) [Nonempty I] : Nonempty (ChainColimit C) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  obtain ⟨x⟩ := C.nonempty i
  exact ⟨mk C i x⟩

end ChainColimit

section Elementarity

variable {C}

theorem val_mk_term {ξ : Type*} {n : ℕ} {i : I} (b : Fin n → C.Model i) (f : ξ → C.Model i)
    (t : SetTheorySemiterm ξ n) :
    t.val (fun l ↦ ChainColimit.mk C i (b l)) (fun x ↦ ChainColimit.mk C i (f x)) =
      ChainColimit.mk C i (t.val b f) := by
  cases t with
  | bvar l => rfl
  | fvar x => rfl
  | func h _ => exact Empty.elim h

theorem mk_vecCons {V W : Type*} {n : ℕ} (g : V → W) (x : V) (b : Fin n → V) :
    g ∘ (x :> b) = (g x :> g ∘ b) := by
  funext l
  refine Fin.cases ?_ (fun m ↦ ?_) l <;> rfl

/-- Tarski-Vaught elementary chain theorem: every stage of the chain is an elementary
substructure of the colimit. -/
theorem eval_mk (C : ElementaryChain I) {ξ : Type} :
    ∀ {n : ℕ} (φ : SetTheorySemiformula ξ n) (i : I) (b : Fin n → C.Model i)
      (f : ξ → C.Model i),
      φ.Eval b f ↔ φ.Eval (ChainColimit.mk C i ∘ b) (ChainColimit.mk C i ∘ f) := by
  intro n φ
  induction φ with
  | verum => intro i b f; rfl
  | falsum => intro i b f; rfl
  | rel r ts =>
    intro i b f
    cases r <;>
      simp only [Semiformula.eval_rel, Structure.rel, Function.comp_def, val_mk_term]
    · exact (ChainColimit.mk_eq_mk_iff _ _).symm
    · exact (ChainColimit.mk_mem_mk_iff _ _).symm
  | nrel r ts =>
    intro i b f
    cases r <;>
      simp only [Semiformula.eval_nrel, Structure.rel, Function.comp_def, val_mk_term]
    · exact not_congr (ChainColimit.mk_eq_mk_iff _ _).symm
    · exact not_congr (ChainColimit.mk_mem_mk_iff _ _).symm
  | and φ ψ ihφ ihψ => intro i b f; exact and_congr (ihφ i b f) (ihψ i b f)
  | or φ ψ ihφ ihψ => intro i b f; exact or_congr (ihφ i b f) (ihψ i b f)
  | all φ ih =>
    intro i b f
    change (∀ x : C.Model i, φ.Eval (x :> b) f) ↔
      ∀ z : ChainColimit C, φ.Eval (z :> ChainColimit.mk C i ∘ b) (ChainColimit.mk C i ∘ f)
    constructor
    · intro h z
      obtain ⟨j, y, rfl⟩ := ChainColimit.exists_mk C z
      have hik : i ≤ max i j := le_max_left i j
      have hjk : j ≤ max i j := le_max_right i j
      have hall : ∀ x : C.Model (max i j),
          φ.Eval (x :> C.map hik ∘ b) (C.map hik ∘ f) := by
        have h' := ((C.map hik).elementary (.all φ) b f).mp h
        exact h'
      have hy := (ih (max i j) (C.map hjk y :> C.map hik ∘ b) (C.map hik ∘ f)).mp
        (hall (C.map hjk y))
      rw [mk_vecCons, ← Function.comp_assoc, ← Function.comp_assoc] at hy
      simpa only [ChainColimit.mk_comp_map hik, ChainColimit.mk_map hjk y] using hy
    · intro h x
      refine (ih i (x :> b) f).mpr ?_
      have hx := h (ChainColimit.mk C i x)
      rwa [mk_vecCons]
  | exs φ ih =>
    intro i b f
    change (∃ x : C.Model i, φ.Eval (x :> b) f) ↔
      ∃ z : ChainColimit C, φ.Eval (z :> ChainColimit.mk C i ∘ b) (ChainColimit.mk C i ∘ f)
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨ChainColimit.mk C i x, ?_⟩
      have := (ih i (x :> b) f).mp hx
      rwa [mk_vecCons] at this
    · rintro ⟨z, hz⟩
      obtain ⟨j, y, rfl⟩ := ChainColimit.exists_mk C z
      have hik : i ≤ max i j := le_max_left i j
      have hjk : j ≤ max i j := le_max_right i j
      have hy : φ.Eval (C.map hjk y :> C.map hik ∘ b) (C.map hik ∘ f) := by
        refine (ih (max i j) (C.map hjk y :> C.map hik ∘ b) (C.map hik ∘ f)).mpr ?_
        rw [mk_vecCons, ← Function.comp_assoc, ← Function.comp_assoc]
        simpa only [ChainColimit.mk_comp_map hik, ChainColimit.mk_map hjk y] using hz
      have hex : ∃ x : C.Model (max i j), φ.Eval (x :> C.map hik ∘ b) (C.map hik ∘ f) :=
        ⟨C.map hjk y, hy⟩
      exact ((C.map hik).elementary (.exs φ) b f).mpr hex

/-- The embedding of a stage into the colimit, as an elementary map. -/
def ChainColimit.embedding (C : ElementaryChain I) (i : I) :
    ElementaryMap (C.Model i) (ChainColimit C) where
  toFun := ChainColimit.mk C i
  elementary φ b f := eval_mk C φ i b f

@[simp] theorem ChainColimit.embedding_apply (C : ElementaryChain I) (i : I) (x : C.Model i) :
    ChainColimit.embedding C i x = ChainColimit.mk C i x := rfl

end Elementarity

/-- The colimit of a chain of models of ZF models ZF. -/
instance ChainColimit.models_zf (C : ElementaryChain I) [Nonempty I] :
    (ChainColimit C)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  refine ⟨?_⟩
  intro φ hφ
  have hs := Theory.models (C.Model i) 𝗭𝗙 hφ
  change φ.Eval ![] Empty.elim at hs
  have he := (eval_mk C φ i ![] Empty.elim).mp hs
  have hf : ChainColimit.mk C i ∘ (Empty.elim : Empty → C.Model i) = Empty.elim := by
    funext x
    exact Empty.elim x
  have hb : ChainColimit.mk C i ∘ (![] : Fin 0 → C.Model i) = ![] := by
    funext l
    exact Fin.elim0 l
  rw [hf, hb] at he
  exact he

/-- The colimit is no larger than the disjoint union of the stages. -/
theorem ChainColimit.mk_le (C : ElementaryChain I) :
    Cardinal.mk (ChainColimit C) ≤ Cardinal.sum (fun i ↦ Cardinal.mk (C.Model i)) := by
  rw [← Cardinal.mk_sigma]
  exact Cardinal.mk_le_of_surjective (f := Quotient.mk C.chainSetoid) Quotient.mk_surjective

end ElementaryChain
end ZFVP
