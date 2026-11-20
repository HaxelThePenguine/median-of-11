import Std

namespace Median11

structure Gate (n : Nat) where
  lo : Fin n
  hi : Fin n
  distinct : lo ≠ hi
  deriving DecidableEq

abbrev Network (n : Nat) := List (Gate n)
abbrev Row (n : Nat) (α : Type u) := Vector α n

def Standard (net : Network n) : Prop := ∀ g ∈ net, g.lo < g.hi

def step [LE α] [DecidableRel (fun (a b : α) => a ≤ b)] (g : Gate n) (x : Row n α) :
    Row n α :=
  if x.get g.lo ≤ x.get g.hi then x
  else (x.set g.lo.val (x.get g.hi) g.lo.isLt).set g.hi.val (x.get g.lo) g.hi.isLt

def run [LE α] [DecidableRel (fun (a b : α) => a ≤ b)] :
    Network n → Row n α → Row n α
  | [], x => x
  | g :: net, x => run net (step g x)

@[simp] theorem run_append [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (p s : Network n) (x : Row n α) : run (p ++ s) x = run s (run p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons g p ih => exact ih (step g x)

@[simp] theorem get_set (x : Row n α) (i j : Fin n) (a : α) :
    (x.set i.val a i.isLt).get j = if i = j then a else x.get j := by
  change (x.set i.val a i.isLt)[j.val] = _
  rw [Vector.getElem_set]
  simp [Fin.ext_iff, Vector.get]

theorem step_get [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (g : Gate n) (x : Row n α) (i : Fin n) :
    (step g x).get i =
      if x.get g.lo ≤ x.get g.hi then x.get i
      else if g.hi = i then x.get g.lo else if g.lo = i then x.get g.hi else x.get i := by
  by_cases h : x.get g.lo ≤ x.get g.hi <;> simp [step, h]

def rowMap (f : α → β) (x : Row n α) : Row n β := Vector.ofFn (fun i => f (x.get i))

@[simp] theorem get_rowMap (f : α → β) (x : Row n α) (i : Fin n) :
    (rowMap f x).get i = f (x.get i) := by
  simp [rowMap, Vector.get]

theorem row_ext {x y : Row n α} (h : ∀ i, x.get i = y.get i) : x = y :=
  Vector.ext (fun i hi => h ⟨i, hi⟩)

theorem step_map [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    [LE β] [DecidableRel (fun (a b : β) => a ≤ b)]
    (f : α → β) (mono : ∀ {a b}, a ≤ b → f a ≤ f b)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a)
    (antisymm : ∀ {a b : β}, a ≤ b → b ≤ a → a = b)
    (g : Gate n) (x : Row n α) :
    rowMap f (step g x) = step g (rowMap f x) := by
  apply row_ext
  intro i
  simp only [get_rowMap, step_get]
  by_cases h : x.get g.lo ≤ x.get g.hi
  · simp [h, mono h]
  · have rev := (total (x.get g.lo) (x.get g.hi)).resolve_left h
    by_cases hf : f (x.get g.lo) ≤ f (x.get g.hi)
    · have equal := antisymm hf (mono rev)
      by_cases ehi : g.hi = i
      · subst i
        simp [h, hf, equal]
      · by_cases elo : g.lo = i
        · subst i
          simp [h, hf, ehi, equal]
        · simp [h, hf, ehi, elo]
    · simp only [if_neg h, if_neg hf]
      split
      · rfl
      · split <;> rfl

theorem run_map [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    [LE β] [DecidableRel (fun (a b : β) => a ≤ b)]
    (f : α → β) (mono : ∀ {a b}, a ≤ b → f a ≤ f b)
    (total : ∀ a b : α, a ≤ b ∨ b ≤ a)
    (antisymm : ∀ {a b : β}, a ≤ b → b ≤ a → a = b)
    (net : Network n) (x : Row n α) :
    rowMap f (run net x) = run net (rowMap f x) := by
  induction net generalizing x with
  | nil => rfl
  | cons g net ih =>
    simp only [run, ih, step_map f mono total antisymm]

end Median11
