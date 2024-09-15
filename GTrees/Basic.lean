import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.FinEnum

-- Based on https://g-trees.github.io/g_trees

variable {α : Type u}

inductive Tree (α : Type u) : Type u
| vertex (k : ℕ) (items : Fin (k - 1) → α) (children : Fin k → Tree α) : Tree α

namespace Tree

instance : EmptyCollection (Tree α) := ⟨vertex 0 Fin.elim0 Fin.elim0⟩

theorem empty_def : (∅ : Tree α) = vertex 0 Fin.elim0 Fin.elim0 := rfl

instance : Inhabited (Tree α) := ⟨∅⟩

instance : Nontrivial (Tree α) := ⟨⟨∅, vertex 1 Fin.elim0 (λ_ => ∅), by simp [empty_def]⟩⟩

@[simp]
def num_children : Tree α → ℕ
| vertex k _ _ => k

@[simp]
theorem num_children_empty : num_children (α := α) ∅ = 0
  := by simp [empty_def, num_children]

def num_items (t : Tree α) : ℕ := t.num_children - 1

@[simp]
theorem num_items_vertex {k : ℕ} {items : Fin (k - 1) → α} {children : Fin k → Tree α}
  : (vertex k items children).num_items = k - 1 := rfl

@[simp]
theorem num_items_empty : num_items (α := α) ∅ = 0
  := by simp [num_items]

theorem num_items_def {t : Tree α} : t.num_items = t.num_children - 1 := rfl

@[simp]
theorem items_le_children {t : Tree α} : t.num_items ≤ t.num_children
  := by simp [num_items_def]

def items : (t : Tree α) → Fin t.num_items → α
| vertex _ items _ => items

def children : (t : Tree α) → Fin t.num_children → Tree α
| vertex _ _ children => children

def length : Tree α → ℕ
| vertex k _ children => (k - 1) + Finset.univ.sum (λ i => (children i).length)

def size : Tree α → ℕ
| vertex k _ children => k + Finset.univ.sum (λ i => (children i).size)

def depth : Tree α → ℕ
| vertex _ _ children => match Finset.univ.sup (λ i => ((children i).depth : WithBot ℕ)) with
  | ⊥ => 0
  | (d : ℕ) => d + 1

theorem depth_children_lt {t : Tree α} {i : Fin t.num_children}
  : (t.children i).depth < t.depth := by
  cases t with
  | vertex k _ children =>
    simp [depth]
    split
    case _ h =>
      rw [WithBot.none_eq_bot] at h
      simp only [Finset.sup_eq_bot_iff, Finset.mem_univ, WithBot.coe_ne_bot, imp_false,
        not_true_eq_false] at h
      exact (h i).elim
    case _ h =>
      simp only [Tree.children, Nat.lt_succ_iff]
      apply WithBot.coe_le_coe.mp
      apply le_trans _ (le_of_eq h)
      simp only [WithBot.bot_lt_coe, Finset.le_sup_iff, Finset.mem_univ, WithBot.coe_le_coe,
        true_and]
      exact ⟨i, le_refl _⟩

inductive LiftRelation (R : α → β → Prop) : Tree α → Tree β → Prop
| vertex {k : ℕ}
  {items : Fin (k - 1) → α} {items' : Fin (k - 1) → β}
  {children : Fin k → Tree α} {children' : Fin k → Tree β}
  (hItems : ∀i : Fin (k - 1), R (items i) (items' i))
  (hChildren : ∀i : Fin k, LiftRelation R (children i) (children' i))
  : LiftRelation R (vertex k items children) (vertex k items' children')

theorem LiftRelation.num_children {R : α → β → Prop} {t t'}
  (h : LiftRelation R t t') : t.num_children = t'.num_children := by
  cases h; rfl

theorem LiftRelation.num_items {R : α → β → Prop} {t t'}
  (h : LiftRelation R t t') : t.num_items = t'.num_items := by
  cases h; rfl

theorem LiftRelation.items {R : α → β → Prop} {t t'}
  (h : LiftRelation R t t') (i : Fin t.num_items)
  : R (t.items i) (t'.items (i.cast h.num_items)) := by
  cases h; apply_assumption

theorem LiftRelation.children {R : α → β → Prop} {t t'}
  (h : LiftRelation R t t') (i : Fin t.num_children)
  : LiftRelation R (t.children i) (t'.children (i.cast h.num_children)) := by
  cases h; apply_assumption

theorem LiftRelation.eq {t t' : Tree α} (h : LiftRelation Eq t t') : t = t' := by
  induction h; simp only [vertex.injEq, heq_eq_eq, true_and]; constructor <;> funext i <;> simp [*]

theorem LiftRelation.reflexive {R : α → α → Prop} (hR : Reflexive R)
  : Reflexive (LiftRelation R)
  := by
  intro t; induction t; constructor
  intro i; apply hR
  assumption

instance LiftRelation.IsRefl {R : α → α → Prop} [h : IsRefl α R]
  : IsRefl (Tree α) (LiftRelation R) := ⟨reflexive h.refl⟩

theorem LiftRelation.symmetric {R : α → α → Prop} (hR : Symmetric R)
  : Symmetric (LiftRelation R)
  := by
  intro t t' h; induction h with | vertex hi _ I =>
    constructor
    intro i; apply hR; apply hi
    intro i; apply I

theorem LiftRelation.IsSymm {R : α → α → Prop} [h : IsSymm α R]
  : IsSymm (Tree α) (LiftRelation R) := ⟨symmetric h.symm⟩

theorem LiftRelation.transitive {R : α → α → Prop} (hR : Transitive R)
  : Transitive (LiftRelation R)
  := by
  intro t₁ t₂ t₃ h₁₂ h₂₃
  induction h₁₂ generalizing t₃ with | vertex hi₁₂ _ I₁₂ =>
  cases h₂₃ with | vertex hi₂₃ hc₂₃ =>
  constructor
  intro i; apply hR; apply hi₁₂; apply hi₂₃
  intro i; apply I₁₂; apply hc₂₃

theorem LiftRelation.IsTrans {R : α → α → Prop} [h : IsTrans α R]
  : IsTrans (Tree α) (LiftRelation R) := ⟨transitive h.trans⟩

theorem LiftRelation.eq_iff {t t' : Tree α} : LiftRelation Eq t t' ↔ t = t' :=
  ⟨LiftRelation.eq, λ h => by cases h; apply IsRefl.refl⟩

open Tree

instance liftRelationDecidable {R : α → β → Prop} [∀a b, Decidable (R a b)]
  : ∀t t', Decidable (LiftRelation R t t')
| vertex k items children, vertex k' items' children' => if h : k = k' then
    if hItems : ∀i : Fin (k - 1), R (items i) (items' (i.cast (by simp [h]))) then
      if hChildren : ∀i : Fin k,
                      (liftRelationDecidable (R := R) (children i) (children' (i.cast h))).decide
      then
        Decidable.isTrue (by
          simp only [decide_eq_true_eq] at hChildren; cases h; constructor <;> assumption)
      else
        Decidable.isFalse (by
          intro c;
          simp only [decide_eq_true_eq] at hChildren
          exact hChildren c.children
        )
    else
      Decidable.isFalse (by intro c; cases c; contradiction)
  else
    Decidable.isFalse (by intro c; cases c; contradiction)

instance decidableEq [DecidableEq α] : DecidableEq (Tree α)
  := λ _ _ => decidable_of_iff _ LiftRelation.eq_iff

def itemSet [DecidableEq α] : Tree α → Finset α
| vertex _ items _ => Finset.univ.sup (λi => {items i})

def itemList (t : Tree α) : List α := (FinEnum.toList _).map t.items

def elementList : Tree α → List α
| vertex _ items children =>
  (FinEnum.toList _).map items ++ (FinEnum.toList _).bind (λ i => (children i).elementList)

def elementsM : Tree α → Multiset α
| vertex _ items children =>
  Finset.univ.sum (λi => {items i}) + Finset.univ.sum (λ i => (children i).elementsM)

def elements [DecidableEq α] : Tree α → Finset α
| vertex _ items children =>
  Finset.univ.sup (λi => {items i}) ∪ Finset.univ.sup (λ i => (children i).elements)

inductive IsElement (a : α) : Tree α → Prop
| item {k : ℕ} {items : Fin (k - 1) → α} {children : Fin k → Tree α} (i : Fin (k - 1))
  : a = items i → IsElement a (vertex k items children)
| child {k : ℕ} {items : Fin (k - 1) → α} {children : Fin k → Tree α} (i : Fin k)
  : IsElement a (children i) → IsElement a (vertex k items children)

theorem mem_elements_iff [DecidableEq α] {t : Tree α} {a : α}
  : a ∈ t.elements ↔ IsElement a t := by
  induction t with
  | vertex k items children ih =>
    simp only [elements, Finset.mem_union, Finset.mem_sup, Finset.mem_singleton, Finset.mem_univ,
      ih, true_and]
    constructor
    intro h
    cases h with
    | inl h => cases h; constructor; assumption
    | inr h => cases h; apply IsElement.child; assumption
    intro h
    cases h with
    | item i h => cases h; left; exact ⟨_, rfl⟩
    | child i h => right; exact ⟨_, h⟩

def subtrees [DecidableEq α] : Tree α → Finset (Tree α)
| vertex k items children
  => {vertex k items children} ∪ Finset.univ.sup (λ i => (children i).subtrees)

inductive IsSubtree (t : Tree α) : Set (Tree α)
| refl : IsSubtree t t
| child {k : ℕ} {items : Fin (k - 1) → α} {children : Fin k → Tree α} (i : Fin k)
  : IsSubtree t (children i) → IsSubtree t (vertex k items children)

theorem mem_subtrees_iff [DecidableEq α] {t t' : Tree α}
  : t' ∈ t.subtrees ↔ IsSubtree t' t := by
  induction t generalizing t' with
  | vertex k items children ih =>
    simp only [subtrees, Finset.mem_union, Finset.mem_singleton, Finset.mem_sup, Finset.mem_univ,
      ih, true_and]
    constructor
    intro i
    cases i with
    | inl h => cases h; constructor
    | inr h => cases h; apply IsSubtree.child; assumption
    intro h
    cases h with
    | refl => simp
    | child i h => right; exact ⟨_, h⟩

theorem IsSubtree.trans {t₁ t₂ t₃ : Tree α}
  (h₁ : IsSubtree t₁ t₂) (h₂ : IsSubtree t₂ t₃) : IsSubtree t₁ t₃ := by
  induction h₂ generalizing t₁ with
  | refl => assumption
  | child i _ ih => apply child; exact ih h₁

theorem IsSubtree.subset [DecidableEq α] {t t' : Tree α}
  (h : IsSubtree t t') : t.subtrees ⊆ t'.subtrees := by
  intro x
  simp only [mem_subtrees_iff]
  intro h'
  exact h'.trans h

theorem IsSubtree.of_subset [DecidableEq α] {t t' : Tree α}
  (h : t.subtrees ⊆ t'.subtrees) : IsSubtree t t' := by
  rw [<-mem_subtrees_iff]
  apply h
  rw [mem_subtrees_iff]
  constructor

theorem IsSubtree.subset_iff [DecidableEq α] {t t' : Tree α}
  : t.subtrees ⊆ t'.subtrees ↔ IsSubtree t t' := ⟨of_subset, subset⟩

theorem IsSubtree.depth_le {t t' : Tree α} (h : IsSubtree t t') : t.depth ≤ t'.depth := by
  induction h with
  | refl => rfl
  | child i _ ih => exact le_of_lt (lt_of_le_of_lt ih (depth_children_lt (t := vertex _ _ _)))

theorem IsSubtree.eq_of_depth_eq {t t' : Tree α} (h : IsSubtree t t') (h' : t.depth = t'.depth)
  : t = t' := by
  cases h with
  | refl => rfl
  | child i h =>
    apply False.elim
    rw [<-lt_self_iff_false (α := ℕ)]
    have h := lt_of_le_of_lt h.depth_le (depth_children_lt (t := vertex _ ?i _))
    rw [h'] at h
    exact h

theorem IsSubtree.antisymm {t₁ t₂ : Tree α}
  (h₁ : IsSubtree t₁ t₂) (h₂ : IsSubtree t₂ t₁) : t₁ = t₂
  := h₁.eq_of_depth_eq (h₁.depth_le.antisymm h₂.depth_le)

theorem subtrees_injective [DecidableEq α] : Function.Injective (@subtrees α _) := by
  intro t₁ t₂ h; apply IsSubtree.antisymm <;> apply IsSubtree.of_subset <;> simp [h]

instance IsSubtree.instIsPartialOrder : IsPartialOrder (Tree α) (IsSubtree) where
  refl _ := refl
  trans _ _ _ := trans
  antisymm _ _ := antisymm

theorem IsSubtree.closed_down {Q : Tree α → Prop}
  (hQ : ∀t, Q t → ∀i, Q (t.children i)) (ht : Q t) (ht' : t'.IsSubtree t) : Q t' := by
  induction ht' with
  | refl => exact ht
  | child _ _ I => apply I; apply hQ _ ht

theorem subtrees_closed_down [DecidableEq α] {Q : Tree α → Prop}
  (hQ : ∀t, Q t → ∀i, Q (t.children i)) (ht : Q t) : ∀t' ∈ t.subtrees, Q t' := by
  simp only [mem_subtrees_iff]; intro t'; apply IsSubtree.closed_down hQ ht

theorem subtrees_closed_down' [DecidableEq α] {Q : Tree α → Prop}
  (hQ : ∀t, Q t → ∀i, Q (t.children i)) {t} : Q t ↔ ∀t' ∈ t.subtrees, Q t' :=
  ⟨subtrees_closed_down hQ, λh => h t (by simp [mem_subtrees_iff, IsSubtree.refl])⟩

theorem IsSubtree.closed_up {P : Tree α → Prop} {Q : Tree α → Prop}
  (hPQ : ∀t, P t → (∀i, Q (t.children i)) → Q t) (ht : ∀t' : Tree α, t'.IsSubtree t → P t')
  : Q t := by induction t with
  | vertex k items children I =>
    apply hPQ
    apply ht
    apply refl
    intro i
    apply I
    intro t' ht'
    apply ht
    apply child
    assumption

theorem subtrees_closed_up [DecidableEq α] {P : Tree α → Prop} {Q : Tree α → Prop}
  (hPQ : ∀t, P t → (∀i, Q (t.children i)) → Q t) (ht : ∀t' ∈ t.subtrees, P t')
  : Q t := by
  simp only [mem_subtrees_iff] at ht; apply IsSubtree.closed_up hPQ; apply ht

inductive AllSubtrees (P : Tree α → Prop) : Tree α → Prop
| vertex {k : ℕ} {items : Fin (k - 1) → α} {children : Fin k → Tree α}
    (hRoot : P (vertex k items children))
    (hChildren : ∀i, AllSubtrees P (children i))
  : AllSubtrees P (vertex k items children)

theorem AllSubtrees.root {P : Tree α → Prop} {t : Tree α} (h : AllSubtrees P t)
  : P t := by cases h; assumption

theorem AllSubtrees.children {P : Tree α → Prop} {t : Tree α} (h : AllSubtrees P t)
  : ∀i, AllSubtrees P (t.children i) := by cases h; assumption

theorem AllSubtrees.subtree' [DecidableEq α] {P : Tree α → Prop} (h : AllSubtrees P t)
  : ∀t' ∈ t.subtrees, AllSubtrees P t' := subtrees_closed_down (λ_ => children) h

theorem AllSubtrees.subtree [DecidableEq α] {P : Tree α → Prop} (h : AllSubtrees P t)
  : ∀t' ∈ t.subtrees, P t' := λ_ h' => (h.subtree' _ h').root

theorem AllSubtrees.mk {P : Tree α → Prop} {t : Tree α}
  : P t → (∀i, AllSubtrees P (t.children i)) → AllSubtrees P t :=
  λhr hc => by cases t; exact vertex hr hc

theorem AllSubtrees.of_subtree [DecidableEq α] {P : Tree α → Prop} (h : ∀t' ∈ t.subtrees, P t')
  : AllSubtrees P t := subtrees_closed_up (λ_ => mk) h

theorem AllSubtrees.mk_iff [DecidableEq α] {P : Tree α → Prop}
  : AllSubtrees P t ↔ ∀t' ∈ t.subtrees, P t' := ⟨subtree, of_subtree⟩

def lowerItem {α : Type u} (t : Tree α) (i : Fin t.num_children) : WithBot α
  := if h : ↑i ≠ (0 : ℕ) ∧ i - 1 < t.num_items then
    t.items ⟨i - 1, h.2⟩
  else
    ⊥

def upperItem {α : Type u} (t : Tree α) (i : Fin t.num_children) : WithTop α
  := if h : ↑i < t.num_items then
    t.items ⟨i, h⟩
  else
    ⊤

@[simp]
theorem lowerItem_empty (i : Fin 0) : lowerItem (α := α) ∅ i = ⊥ := by
  simp [lowerItem]

@[simp]
theorem upperItem_empty (i : Fin 0) : upperItem (α := α) ∅ i = ⊤ := by
  simp [upperItem]

structure SearchRoot (R : α → α → Prop) (t : Tree α) : Prop where
  (itemsSorted : ∀i j, i < j → R (t.items i) (t.items j))
  (childrenLower : ∀i, (hi : i - 1 < t.num_items) → (hc : i + 1 < t.num_children)
    → ∀j, R (t.items ⟨i - 1, hi⟩) ((t.children ⟨i + 1, hc⟩).items j))
  (childrenUpper : ∀i, (hi : i < t.num_items)
    → ∀j : Fin (t.children ⟨i, lt_of_lt_of_le hi items_le_children⟩).num_items,
        R ((t.children ⟨i, lt_of_lt_of_le hi items_le_children⟩).items j) a)

abbrev SearchRootLE [LE α] (t : Tree α) := SearchRoot LE.le t

abbrev SearchRootLT [LT α] (t : Tree α) := SearchRoot LT.lt t

abbrev SearchTree (R : α → α → Prop) (t : Tree α) : Prop := AllSubtrees (SearchRoot R) t

abbrev SearchTreeLE [LE α] (t : Tree α) := SearchTree LE.le t

abbrev SearchTreeLT [LT α] (t : Tree α) := SearchTree LT.lt t

-- TODO: an lt search tree (i.e. transitive, irreflexive) contains no duplicates

-- TODO: being a search tree is antitone

def HeapRoot (R : α → α → Prop) (t : Tree α) : Prop :=
  ∀i j k, R ((t.children i).items j) (t.items k)

abbrev HeapRootLE [LE α] (t : Tree α) := HeapRoot LE.le t

abbrev Heap (R : α → α → Prop) (t : Tree α) : Prop := AllSubtrees (HeapRoot R) t

abbrev HeapLE [LE α] (t : Tree α) := Heap LE.le t

-- TODO: being a heap is antitone

structure IsZipTree (orderLT : α → α → Prop) (rankLE : α → α → Prop) (t : Tree α) : Prop where
  (hSearch : SearchTree orderLT t)
  (hHeap : Heap rankLE t)

-- TODO: recursive definition of zip tree, equivalence

-- TODO: if rankLE is a partial order and orderLT is a strict partial order,
-- then two zip trees with the same elements are equal

-- TODO: sorted linked list ziptrees

-- TODO: geometric search tree

-- TODO: how would probabilistic bounds be modeled here?

-- TODO: zip trees are G trees

-- TODO: zip^k trees

-- TODO: treaps

-- TODO: extended stuff

end Tree

-- TODO: use mutual inductive here?

inductive GTree (σ : Type v) : Type v
| empty : GTree σ
| node (set : σ) (right : GTree σ) (rank : ℕ)

inductive GTree.IsNode {σ : Type v} : GTree σ → Prop
| node (set : σ) (right : GTree σ) (rank : ℕ) : GTree.IsNode (GTree.node set right rank)

def GTreeNode (σ : Type v) : Type v := { t : GTree σ // GTree.IsNode t }

def GTreeNode.set {σ : Type v} (t : GTreeNode σ) : σ
  := match t with | ⟨GTree.node set _ _, _⟩ => set

def GTreeNode.right {σ : Type v} (t : GTreeNode σ) : GTree σ
  := match t with | ⟨GTree.node _ right _, _⟩ => right

def GTreeNode.rank {σ : Type v} (t : GTreeNode σ) : ℕ
  := match t with | ⟨GTree.node _ _ rank, _⟩ => rank

-- TODO: drag this over to discretion

def WithEmpty (σ : Type v) : Type v := Option σ

namespace WithEmpty

def empty : WithEmpty σ := none

instance : EmptyCollection (WithEmpty σ) := ⟨empty⟩

instance : Inhabited (WithEmpty σ) := ⟨empty⟩

instance [Membership α σ] : Membership α (WithEmpty σ) where
  mem
  | none => λ_ => False
  | some a => λx => x ∈ a

instance [Union σ] : Union (WithEmpty σ) where
  union
  | none, a | a, none => a
  | some a, some b => some (a ∪ b)

instance [Singleton α σ] : Singleton α (WithEmpty σ) where
  singleton a := some (singleton a)

end WithEmpty

class NGSet (α : outParam (Type u)) (σ : Type v) where
  singleton (item : α) (subtree : GTree σ) : σ
  split (this : σ) (key : α) : WithEmpty σ × Option (GTree σ) × WithEmpty σ
  join (lo : σ) (hi : σ) : σ
  remove_min (this : σ) : α × GTree σ × WithEmpty σ
  insert_min (this : σ) (new_min :  α × GTree σ) : σ
  search (this : σ) (key : α) : Option (α × GTree σ)

open NGSet

def WithEmpty.insert_min [NGSet α σ] (this : WithEmpty σ) (new_min : α × GTree σ) : σ :=
  match this with
  | none => singleton new_min.1 new_min.2
  | some s => NGSet.insert_min s new_min

namespace GTree
