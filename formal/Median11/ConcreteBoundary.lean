import Median11.BinaryReduction
import Median11.Boundary

namespace Median11

def Pointwise (x y : Row n Bool) : Prop := ∀ i, x.get i ≤ y.get i

theorem weight_set (x : Row n Bool) (i : Fin n) (b : Bool) :
    weight (x.set i.val b i.isLt) =
      weight x - (if x.get i then 1 else 0) + (if b then 1 else 0) := by
  rw [weight, Vector.toList_set, List.count_set (by simpa using i.isLt)]
  cases b <;> cases h : x.get i <;> simp_all [weight, Vector.get]

theorem weight_step (g : Gate n) (x : Row n Bool) : weight (step g x) = weight x := by
  unfold step
  cases ha : x.get g.lo <;> cases hb : x.get g.hi <;>
    simp [ha, hb, weight_set, get_set, g.distinct,
      show (false : Bool) ≤ false by decide, show (false : Bool) ≤ true by decide,
      show (true : Bool) ≤ true by decide, show ¬(true : Bool) ≤ false by decide]
  have one : 1 ≤ weight x := by
    have h := List.boole_getElem_le_count (l := x.toList) (a := true)
      (i := g.lo.val) (by simpa using g.lo.isLt)
    simpa [weight, ← ha, Vector.get] using h
  omega

theorem weight_run (net : Network n) (x : Row n Bool) : weight (run net x) = weight x := by
  induction net generalizing x with
  | nil => rfl
  | cons g net ih => rw [run, ih, weight_step]

theorem step_lo (g : Gate n) (x : Row n Bool) :
    (step g x).get g.lo = (x.get g.lo && x.get g.hi) := by
  rw [step_get]
  cases x.get g.lo <;> cases x.get g.hi <;> simp [Ne.symm g.distinct] <;> decide

theorem step_hi (g : Gate n) (x : Row n Bool) :
    (step g x).get g.hi = (x.get g.lo || x.get g.hi) := by
  rw [step_get]
  cases x.get g.lo <;> cases x.get g.hi <;> simp <;> decide

theorem step_other [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    (g : Gate n) (x : Row n α) (i : Fin n) (a : g.lo ≠ i) (b : g.hi ≠ i) :
    (step g x).get i = x.get i := by
  simp [step_get, a, b]

theorem step_mono (g : Gate n) {x y : Row n Bool} (h : Pointwise x y) :
    Pointwise (step g x) (step g y) := by
  intro i
  by_cases a : g.lo = i
  · subst i
    simp only [step_lo]
    have ha := h g.lo
    have hb := h g.hi
    cases hxl : x.get g.lo <;> cases hyl : y.get g.lo <;> cases hxh : x.get g.hi <;> cases hyh : y.get g.hi <;>
      simp_all
  · by_cases b : g.hi = i
    · subst i
      simp only [step_hi]
      have ha := h g.lo
      have hb := h g.hi
      cases hxl : x.get g.lo <;> cases hyl : y.get g.lo <;> cases hxh : x.get g.hi <;> cases hyh : y.get g.hi <;>
        simp_all
    · simpa [step_other g x i a b, step_other g y i a b] using h i

theorem run_mono (net : Network n) {x y : Row n Bool} (h : Pointwise x y) :
    Pointwise (run net x) (run net y) := by
  induction net generalizing x y with
  | nil => exact h
  | cons g net ih => exact ih (step_mono g h)

theorem list_below_iff (a b : List Bool) :
    Boundary.Below a b ↔ a.length = b.length ∧
      ∀ i : Nat, (a[i]?.getD false) ≤ (b[i]?.getD false) := by
  induction a generalizing b with
  | nil => cases b <;> simp [Boundary.Below]
  | cons x a ih =>
    cases b with
    | nil => simp [Boundary.Below]
    | cons y b =>
      simp only [Boundary.Below, List.length_cons, Nat.succ.injEq, ih]
      constructor
      · rintro ⟨head, len, tail⟩
        refine ⟨len, ?_⟩
        intro i
        cases i with
        | zero => cases x <;> cases y <;> simp_all [show ¬(true : Bool) ≤ false by decide]
        | succ i => exact tail i
      · rintro ⟨len, all⟩
        have head := all 0
        refine ⟨?_, len, fun i => all (i+1)⟩
        cases x <;> cases y <;> simp_all [show ¬(true : Bool) ≤ false by decide]

theorem below_rows {x y : Row n Bool} (h : Pointwise x y) :
    Boundary.Below x.toList y.toList := by
  apply (list_below_iff _ _).2
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · have hx : i < x.toList.length := by simpa using hi
    have hy : i < y.toList.length := by simpa using hi
    rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy]
    exact h ⟨i, hi⟩
  · have hx : x.toList.length ≤ i := by simpa using hi
    have hy : y.toList.length ≤ i := by simpa using hi
    simp [List.getElem?_eq_none hx, List.getElem?_eq_none hy]

def readRow (n : Nat) (l : List Bool) : Row n Bool :=
  Vector.ofFn fun i => l[i.val]?.getD false

@[simp] theorem get_readRow (l : List Bool) (i : Fin n) :
    (readRow n l).get i = l[i.val]?.getD false := by simp [readRow, Vector.get]

theorem readRow_list (l : List Bool) (len : l.length = n) : (readRow n l).toList = l := by
  apply List.ext_getElem
  · simp [len]
  · intro i a b
    change (readRow n l).get ⟨i, by simpa using a⟩ = l[i]
    simp [List.getElem?_eq_getElem b]

@[simp] theorem readRow_toList (x : Row n Bool) : readRow n x.toList = x :=
  Vector.toList_inj.mp (readRow_list _ (by simp))

def clear (x : Row n Bool) (q : Fin n) : Row n Bool :=
  x.set q.val false q.isLt

theorem clear_mass (x : Row n Bool) (q : Fin n) :
    weight x = weight (clear x q) + (if x.get q then 1 else 0) := by
  simp only [clear, weight_set, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  cases h : x.get q
  · simp
  · have one : 1 ≤ weight x := by
      have h' := List.boole_getElem_le_count (l := x.toList) (a := true)
        (i := q.val) (by simpa using q.isLt)
      simpa [weight, ← h, Vector.get] using h'
    simp
    omega

def layers {net : Network n} {r : Nat} {q : Fin n}
    (positive : 0 < r) (valid : r ≤ n) (sel : SelectsBinary net r q) :
    Boundary.OutputMap n (n-r) where
  bit l := (run net (readRow n l)).get q
  rest l := (clear (run net (readRow n l)) q).toList
  mono hlen h := by
    apply below_rows
    have le := (list_below_iff _ _).1 h
    have hh : Pointwise (readRow n _) (readRow n _) := fun i => by
      simpa using le.2 i.val
    intro i
    simp only [clear, get_set]
    split
    · decide
    · exact run_mono net hh i
  mass l len := by
    have h := clear_mass (run net (readRow n l)) q
    rw [weight_run, weight, readRow_list l len] at h
    exact h
  lo l len hw := by
    rw [sel, weight, readRow_list l len]
    simp only [Boundary.wt] at hw
    rw [hw]
    exact decide_eq_false (by omega)
  hi l len hw := by
    rw [sel, weight, readRow_list l len]
    simp only [Boundary.wt] at hw
    rw [hw]
    exact decide_eq_true (by omega)

theorem boundary_constant {net : Network n} {r : Nat} {q : Fin n}
    (positive : 0 < r) (valid : r ≤ n) (sel : SelectsBinary net r q)
    (x y : Row n Bool) (eq : weight x = weight y)
    (hw : weight x = n-r ∨ weight x = n-r+1) :
    run net x = run net y := by
  let f := layers positive valid sel
  have h := Boundary.rigidity f (x := x.toList) (y := y.toList)
    (by simp) (by simp) eq hw
  have a := congrArg Prod.fst h
  have b := congrArg Prod.snd h
  simp [f, layers] at a b
  have c := b
  apply row_ext
  intro i
  by_cases hi : q = i
  · subst i; exact a
  · simpa [clear, get_set, hi] using congrArg (fun z : Row n Bool => z.get i) c

#print axioms boundary_constant

end Median11
