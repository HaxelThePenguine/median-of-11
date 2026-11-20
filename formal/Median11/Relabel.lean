import Median11.ConcreteBoundary

namespace Median11

/-- Small equivalence record, to keep the project independent of Mathlib. -/
structure Relabel (α β : Type) where
  forward : α → β
  backward : β → α
  left : ∀ a, backward (forward a) = a
  right : ∀ b, forward (backward b) = b

theorem Relabel.injective (e : Relabel α β) {a b : α} (h : e.forward a = e.forward b) :
    a = b := by simpa only [e.left] using congrArg e.backward h

def Relabel.symm (e : Relabel α β) : Relabel β α :=
  ⟨e.backward, e.forward, e.right, e.left⟩

def Relabel.trans (e : Relabel α β) (f : Relabel β γ) : Relabel α γ :=
  ⟨f.forward ∘ e.forward, e.backward ∘ f.backward,
    fun a => by simp [Function.comp, f.left, e.left],
    fun b => by simp [Function.comp, e.right, f.right]⟩

def swapIndex [DecidableEq α] (a b i : α) : α :=
  if a = i then b else if b = i then a else i

theorem swapIndex_swapIndex [DecidableEq α] (a b i : α) :
    swapIndex a b (swapIndex a b i) = i := by
  by_cases ha : a = i
  · subst i
    by_cases hab : a = b
    · simp [swapIndex, hab]
    · simp [swapIndex, hab]
  · by_cases hb : b = i
    · subst i
      simp [swapIndex, ha]
    · simp [swapIndex, ha, hb]

def swapIso [DecidableEq α] (a b : α) : Relabel α α :=
  ⟨swapIndex a b, swapIndex a b, swapIndex_swapIndex a b, swapIndex_swapIndex a b⟩

def renameGate (e : Relabel (Fin n) (Fin m)) (g : Gate n) : Gate m :=
  ⟨e.forward g.lo, e.forward g.hi, fun h => g.distinct (e.injective h)⟩

def renameRow (e : Relabel (Fin n) (Fin m)) (x : Row n α) : Row m α :=
  Vector.ofFn (fun i => x.get (e.backward i))

@[simp] theorem renameRow_get (e : Relabel (Fin n) (Fin m)) (x : Row n α) (i : Fin m) :
    (renameRow e x).get i = x.get (e.backward i) := by simp [renameRow, Vector.get]

theorem rename_step [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (e : Relabel (Fin n) (Fin m)) (g : Gate n) (x : Row n α) :
    step (renameGate e g) (renameRow e x) = renameRow e (step g x) := by
  apply row_ext
  intro i
  simp only [renameRow_get, step_get, renameGate, e.left]
  have eq (a : Fin n) : e.forward a = i ↔ a = e.backward i := by
    constructor
    · intro h
      simpa only [e.left] using congrArg e.backward h
    · intro h
      rw [h, e.right]
  simp only [eq]

theorem rename_run [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (e : Relabel (Fin n) (Fin m)) (s : Network n) (x : Row n α) :
    run (s.map (renameGate e)) (renameRow e x) = renameRow e (run s x) := by
  induction s generalizing x with
  | nil => rfl
  | cons g s ih => simp [run, rename_step, ih]

def dualGate (g : Gate n) : Gate n := ⟨g.hi, g.lo, Ne.symm g.distinct⟩

theorem dual_step (g : Gate n) (x : Row n Bool) :
    step (dualGate g) (rowMap Bool.not x) = rowMap Bool.not (step g x) := by
  apply row_ext
  intro i
  by_cases ha : g.lo = i
  · subst i
    change (step (dualGate g) (rowMap Bool.not x)).get (dualGate g).hi = _
    simp only [step_hi, get_rowMap, step_lo]; change (!(x.get g.hi) || !(x.get g.lo)) = _
    cases x.get g.lo <;> cases x.get g.hi <;> decide
  · by_cases hb : g.hi = i
    · subst i
      change (step (dualGate g) (rowMap Bool.not x)).get (dualGate g).lo = _
      simp only [step_lo, get_rowMap, step_hi]; change (!(x.get g.hi) && !(x.get g.lo)) = _
      cases x.get g.lo <;> cases x.get g.hi <;> decide
    · rw [step_other _ _ _ hb ha, get_rowMap, get_rowMap, step_other _ _ _ ha hb]

theorem dual_run (net : Network n) (x : Row n Bool) :
    run (net.map dualGate) (rowMap Bool.not x) = rowMap Bool.not (run net x) := by
  induction net generalizing x with
  | nil => rfl
  | cons g net ih => simp [run, dual_step, ih]

theorem complement_weight (x : Row n Bool) :
    weight (rowMap Bool.not x) + weight x = n := by
  have e : (rowMap Bool.not x).toList = x.toList.map Bool.not := by
    apply List.ext_getElem
    · simp
    · intro i ha hb
      simpa [Vector.get] using get_rowMap Bool.not x ⟨i, by simpa using ha⟩
  unfold weight
  rw [e]
  have len := Vector.length_toList (xs := x)
  generalize x.toList = bits at *
  clear e x
  subst n
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [List.count_cons] <;> omega

theorem selects_dual {net : Network n} {r : Nat} {q : Fin n}
    (valid : r ≤ n) (h : SelectsBinary net r q) :
    SelectsBinary (net.map dualGate) (n + 1 - r) q := by
  intro x
  have e : rowMap Bool.not (rowMap Bool.not x) = x := by
    apply row_ext
    intro i
    simp
  have hr := dual_run net (rowMap Bool.not x)
  rw [e] at hr
  rw [hr, get_rowMap, h _]
  have hw := complement_weight x
  by_cases hlt : n - weight (rowMap Bool.not x) < r
  · rw [decide_eq_true hlt]
    have hn : ¬n - weight x < n + 1 - r := by omega
    rw [decide_eq_false hn]
    rfl
  · rw [decide_eq_false hlt]
    have hn : n - weight x < n + 1 - r := by omega
    rw [decide_eq_true hn]
    rfl

#print axioms rename_run
#print axioms selects_dual

end Median11
