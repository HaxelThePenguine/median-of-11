import Median11.ReplayRules
import Init.Data.BitVec.Bitblast

namespace Median11

namespace PackedRows

theorem id_lt (x : Row n Bool) : rowId x < 2^n := by
  simpa [rowId] using (BitVec.ofBoolListLE x.toList).isLt

def row (n id : Nat) : Row n Bool :=
  Vector.ofFn fun i => id.testBit i.val

@[simp] theorem row_get (n id : Nat) (i : Fin n) : (row n id).get i = id.testBit i := by
  simp [row, Vector.get]

theorem id_row {id : Nat} (h : id < 2^n) : rowId (row n id) = id := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact (rowId_testBit (row n id) ⟨i, hi⟩).trans (row_get n id ⟨i, hi⟩)
  · have le : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (id_lt _) le),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h le)]

/-- One row occupies one bit. Column masks select rows with a one at the wire. -/
def column (n : Nat) (i : Fin n) : Nat :=
  rowSet ((rows n).filter (fun x => x.get i))

theorem column_bit (i : Fin n) (x : Row n Bool) :
    (column n i).testBit (rowId x) = x.get i := by
  apply Bool.eq_iff_iff.mpr
  rw [column, rowSet_mem]
  simp [rows_complete]

def mask (n : Nat) : Nat := 2^(2^n)-1

def minus (a b : Nat) : Nat := a ^^^ (a &&& b)

@[simp] theorem minus_bit (a b i : Nat) :
    (minus a b).testBit i = (a.testBit i && !b.testBit i) := by
  simp only [minus, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

def disjointAdd (n x y : Nat) (hx : x < 2^n) (hy : y < 2^n)
    (h : x &&& y = 0) : x + y = x ||| y := by
  let a := BitVec.ofNatLT x hx
  let b := BitVec.ofNatLT y hy
  have hz : a &&& b = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa [a, b] using h
  have e := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero a b hz)
  simpa [a,b, BitVec.toNat_add_of_and_eq_zero hz] using e

theorem id_exchange (g : Gate n) (x : Row n Bool) :
    rowId (exchange g x) =
      if x.get g.lo = x.get g.hi then rowId x
      else rowId x ^^^ 2^g.lo.val ^^^ 2^g.hi.val := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (rowId (exchange g x)).testBit j.val = _
    rw [rowId_testBit]
    by_cases lo : g.lo = j
    · have eq : i = g.lo.val := congrArg Fin.val lo.symm
      have neq : g.hi.val ≠ g.lo.val := fun e => g.distinct (Fin.ext e.symm)
      rw [← lo]
      simp only [exchange, renameRow_get, swapIso, swapIndex, if_pos rfl]
      rw [eq]
      cases a : x.get g.lo <;> cases b : x.get g.hi <;>
        simp [Nat.testBit_two_pow, rowId_testBit, neq, a, b]
    · by_cases other : g.hi = j
      · have eq : i = g.hi.val := congrArg Fin.val other.symm
        have neq : g.lo.val ≠ g.hi.val := fun e => g.distinct (Fin.ext e)
        simp only [exchange, renameRow_get, swapIso, swapIndex, lo, other, if_false, if_true]
        rw [eq]
        cases a : x.get g.lo <;> cases b : x.get g.hi <;>
          simp [← other, Nat.testBit_two_pow, rowId_testBit, neq, a, b]
      · have nlo : g.lo.val ≠ i := fun e => lo (Fin.ext e)
        have nhi : g.hi.val ≠ i := fun e => other (Fin.ext e)
        simp only [exchange, renameRow_get, swapIso, swapIndex, lo, other, if_false]
        split <;> simp [Nat.testBit_two_pow, nlo, nhi, ← rowId_testBit x j, j]
  · have le : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (id_lt _) le)]
    have xx := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (id_lt x) le)
    have lo : g.lo.val ≠ i := by have := g.lo.isLt; omega
    have hh : g.hi.val ≠ i := by have := g.hi.isLt; omega
    split <;> simp [xx, Nat.testBit_two_pow, lo, hh]

theorem exchange_id_add (g : Gate n) (x : Row n Bool)
    (lo : x.get g.lo = true) (hi : x.get g.hi = false) :
    rowId (exchange g x) + 2^g.lo.val = rowId x + 2^g.hi.val := by
  have powLo : 2^g.lo.val < 2^n := Nat.pow_lt_pow_of_lt (by decide) g.lo.isLt
  have powHi : 2^g.hi.val < 2^n := Nat.pow_lt_pow_of_lt (by decide) g.hi.isLt
  have disj (y : Row n Bool) (i : Fin n) (h : y.get i = false) :
      rowId y &&& 2^i.val = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases eq : i.val = j
    · subst j
      simp [rowId_testBit, h]
    · simp [Nat.testBit_two_pow, eq]
  have lo' : (exchange g x).get g.lo = false := by simp [exchange, swapIso, swapIndex, hi]
  rw [disjointAdd n _ _ (id_lt _) powLo (disj _ _ lo'),
    disjointAdd n _ _ (id_lt _) powHi (disj _ _ hi), id_exchange]
  simp only [lo, hi, Bool.true_eq_false, if_false]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases a : g.lo.val = j
  · subst j
    simp [Nat.testBit_two_pow, rowId_testBit, lo]
  · by_cases b : g.hi.val = j
    · subst j
      simp [Nat.testBit_two_pow, rowId_testBit, hi, a]
    · simp [Nat.testBit_two_pow, a,b]

theorem column_le (x : Row n Bool) (g : Gate n) (h : x.get g.lo = true)
    (h' : x.get g.hi = false) : step g x = exchange g x := by
  have bad : ¬ x.get g.lo ≤ x.get g.hi := by rw [h,h']; decide
  apply row_ext
  intro i
  by_cases e : g.lo = i
  · subst i
    simp [step_get, bad, exchange, swapIso, swapIndex, Ne.symm g.distinct]
  · by_cases e' : g.hi = i
    · subst i
      simp [step_get, bad, exchange, swapIso, swapIndex, g.distinct]
    · simp [step_get, bad, exchange, swapIso, swapIndex, e, e']

def filterBits (bits : Nat) (xs : List (Row n Bool)) : List (Row n Bool) :=
  xs.filter fun x => bits.testBit (rowId x)

theorem rowSet_filter (bits : Nat) (xs : List (Row n Bool)) :
    rowSet (filterBits bits xs) = rowSet xs &&& bits := by
  induction xs with
  | nil => simp [filterBits, rowSet]
  | cons x xs ih =>
    have split : filterBits bits (x :: xs) =
        if bits.testBit (rowId x) then x :: filterBits bits xs else filterBits bits xs := by
      cases h : bits.testBit (rowId x) <;> simp [filterBits, List.filter_cons, h]
    rw [split]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases e : rowId x = i
    · subst i
      cases h : bits.testBit (rowId x) <;> simp [h, rowSet, ih]
    · cases h : bits.testBit (rowId x) <;> simp [h, rowSet, ih, Nat.testBit_two_pow, e]

theorem rowSet_outside (xs : List (Row n Bool)) {i : Nat} (hi : 2^n ≤ i) :
    (rowSet xs).testBit i = false := by
  induction xs with
  | nil => simp [rowSet]
  | cons x xs ih =>
    have ne : rowId x ≠ i := by have := id_lt x; omega
    simp [rowSet, Nat.testBit_two_pow, ne, ih]

theorem rowSet_filter_not (bits : Nat) (xs : List (Row n Bool)) :
    rowSet (filterBits (minus (mask n) bits) xs) = minus (rowSet xs) bits := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [rowSet_filter, Nat.testBit_and, minus_bit, minus_bit]
  by_cases hi : i < 2^n
  · simp [mask, hi]
  · simp [rowSet_outside xs (by omega : 2^n ≤ i)]

theorem rowSet_map_shift (f : Row n Bool → Row n Bool) (d : Nat)
    (xs : List (Row n Bool)) (h : ∀ x ∈ xs, rowId (f x) = rowId x + d) :
    rowSet (xs.map f) = rowSet xs <<< d := by
  induction xs with
  | nil => simp [rowSet]
  | cons x xs ih =>
    rw [List.map_cons, rowSet, rowSet, ih (fun y hy => h y (by simp [hy])),
      h x (by simp), Nat.shiftLeft_or_distrib]
    simp [Nat.shiftLeft_eq, Nat.pow_add]

theorem rowSet_map_shift_right (f : Row n Bool → Row n Bool) (d : Nat)
    (xs : List (Row n Bool)) (h : ∀ x ∈ xs, rowId (f x) + d = rowId x) :
    rowSet (xs.map f) = rowSet xs >>> d := by
  induction xs with
  | nil => simp [rowSet]
  | cons x xs ih =>
    rw [List.map_cons, rowSet, rowSet, ih (fun y hy => h y (by simp [hy])),
      Nat.shiftRight_or_distrib, ← h x (by simp), Nat.pow_add]
    simp [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem rowSet_append (xs ys : List (Row n Bool)) :
    rowSet (xs ++ ys) = rowSet xs ||| rowSet ys := by
  induction xs with
  | nil => simp [rowSet]
  | cons x xs ih => simp [rowSet, ih, Nat.or_assoc]

theorem rowSet_same {xs ys : List (Row n Bool)} (h : ∀ x, x ∈ xs ↔ x ∈ ys) :
    rowSet xs = rowSet ys := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases valid : i < 2^n
  · rw [← id_row valid]
    apply Bool.eq_iff_iff.mpr
    simpa only [rowSet_mem] using h (row n i)
  · rw [rowSet_outside xs (by omega), rowSet_outside ys (by omega)]

structure Columns (n : Nat) where
  ones : Fin n → Nat
  correct : ∀ (i : Fin n) (x : Row n Bool), (ones i).testBit (rowId x) = x.get i

def columns (n : Nat) : Columns n := ⟨column n, column_bit⟩

def Columns.discord (c : Columns n) (lo hi : Fin n) : Nat := minus (c.ones lo) (c.ones hi)

@[simp] theorem Columns.discord_bit (c : Columns n) (lo hi : Fin n) (x : Row n Bool) :
    (c.discord lo hi).testBit (rowId x) = (x.get lo && !x.get hi) := by
  simp [Columns.discord, c.correct]

def Columns.compare (c : Columns n) (g : Gate n) (bits : Nat) : Nat :=
  let src := c.discord g.lo g.hi
  let d := 2^g.hi.val - 2^g.lo.val
  minus bits src ||| ((bits &&& src) <<< d)

def Columns.exchange (c : Columns n) (g : Gate n) (bits : Nat) : Nat :=
  let up := c.discord g.lo g.hi
  let down := c.discord g.hi g.lo
  let d := 2^g.hi.val - 2^g.lo.val
  minus bits (up ||| down) ||| ((bits &&& up) <<< d) ||| ((bits &&& down) >>> d)

theorem Columns.compare_correct (c : Columns n) (g : Gate n) (ordered : g.lo < g.hi)
    (xs : List (Row n Bool)) : c.compare g (rowSet xs) = rowSet (xs.map (step g)) := by
  let src := c.discord g.lo g.hi
  let unchanged := filterBits (minus (mask n) src) xs
  let moved := filterBits src xs
  have inside (x : Row n Bool) : (mask n).testBit (rowId x) = true := by
    simp [mask, id_lt]
  have stay (x : Row n Bool) (hx : x ∈ unchanged) : step g x = x := by
    have e := (List.mem_filter.mp hx).2
    simp [inside, src] at e
    have hxle : x.get g.lo ≤ x.get g.hi := by
      cases h₁ : x.get g.lo <;> cases h₂ : x.get g.hi <;> simp_all
    simp [step, hxle]
  have shift (x : Row n Bool) (h : x ∈ moved) :
      rowId (step g x) = rowId x + (2^g.hi.val - 2^g.lo.val) := by
    have e := (List.mem_filter.mp h).2
    simp [src, Bool.and_eq_true] at e
    rw [column_le x g e.1 e.2]
    have t := exchange_id_add g x e.1 e.2
    have le : 2^g.lo.val ≤ 2^g.hi.val := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt ordered)
    omega
  have splitRows : rowSet (xs.map (step g)) =
      rowSet (unchanged.map (step g) ++ moved.map (step g)) := by
    apply rowSet_same
    intro y
    simp only [List.mem_append, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      cases h : src.testBit (rowId x)
      · exact Or.inl ⟨x, List.mem_filter.mpr ⟨hx, by simp [inside, h]⟩, rfl⟩
      · exact Or.inr ⟨x, List.mem_filter.mpr ⟨hx,h⟩, rfl⟩
    · rintro (⟨x,hx,e⟩ | ⟨x,hx,e⟩) <;> exact ⟨x, (List.mem_filter.mp hx).1, e⟩
  rw [splitRows, rowSet_append, List.map_congr_left stay]
  change _ = rowSet (unchanged.map id) ||| _
  rw [List.map_id_fun, rowSet_map_shift _ _ _ shift, rowSet_filter]
  change _ = rowSet unchanged ||| _
  rw [rowSet_filter_not]
  rfl

theorem Columns.exchange_correct (c : Columns n) (g : Gate n) (ordered : g.lo < g.hi)
    (xs : List (Row n Bool)) :
    c.exchange g (rowSet xs) = rowSet (xs.map (Median11.exchange g)) := by
  let up := c.discord g.lo g.hi
  let down := c.discord g.hi g.lo
  let unchanged := filterBits (minus (mask n) (up ||| down)) xs
  let left := filterBits up xs
  let right := filterBits down xs
  let f := Median11.exchange g
  have inside (x : Row n Bool) : (mask n).testBit (rowId x) = true := by
    simp [mask, id_lt]
  have le : 2^g.lo.val ≤ 2^g.hi.val := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt ordered)
  have stay (x : Row n Bool) (hx : x ∈ unchanged) : f x = x := by
    have h := (List.mem_filter.mp hx).2
    have eq : x.get g.lo = x.get g.hi := by
      cases a : x.get g.lo <;> cases b : x.get g.hi <;>
        simp_all [up, down, inside]
    apply rowId_injective
    simp [f, id_exchange, eq]
  have shiftUp (x : Row n Bool) (hx : x ∈ left) :
      rowId (f x) = rowId x + (2^g.hi.val - 2^g.lo.val) := by
    have h := (List.mem_filter.mp hx).2
    simp [up, Bool.and_eq_true] at h
    have t := exchange_id_add g x h.1 h.2
    change rowId (f x) + _ = _ at t
    omega
  have shiftDown (x : Row n Bool) (hx : x ∈ right) :
      rowId (f x) + (2^g.hi.val - 2^g.lo.val) = rowId x := by
    have h := (List.mem_filter.mp hx).2
    simp [down, Bool.and_eq_true] at h
    have a : (f x).get g.lo = true := by simp [f, Median11.exchange, swapIso, swapIndex, h.1]
    have b : (f x).get g.hi = false := by
      simp [f, Median11.exchange, swapIso, swapIndex, g.distinct, h.2]
    have t := exchange_id_add g (f x) a b
    change rowId (Median11.exchange g (Median11.exchange g x)) + _ = _ at t
    rw [exchange_twice] at t
    omega
  have splitRows : rowSet (xs.map f) =
      rowSet ((unchanged.map f ++ left.map f) ++ right.map f) := by
    apply rowSet_same
    intro y
    simp only [List.mem_append, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      cases u : up.testBit (rowId x)
      · cases d : down.testBit (rowId x)
        · exact Or.inl (Or.inl ⟨x, List.mem_filter.mpr ⟨hx, by simp [inside,u,d]⟩, rfl⟩)
        · exact Or.inr ⟨x, List.mem_filter.mpr ⟨hx,d⟩, rfl⟩
      · exact Or.inl (Or.inr ⟨x, List.mem_filter.mpr ⟨hx,u⟩, rfl⟩)
    · rintro ((⟨x,hx,e⟩ | ⟨x,hx,e⟩) | ⟨x,hx,e⟩) <;> exact ⟨x,(List.mem_filter.mp hx).1,e⟩
  change _ = rowSet (xs.map f)
  rw [splitRows, rowSet_append, rowSet_append, List.map_congr_left stay]
  change _ = rowSet (unchanged.map id) ||| _ ||| _
  rw [List.map_id_fun, rowSet_map_shift _ _ _ shiftUp, rowSet_map_shift_right _ _ _ shiftDown,
    rowSet_filter, rowSet_filter]
  change _ = rowSet unchanged ||| _ ||| _
  rw [rowSet_filter_not]
  rfl

end PackedRows

end Median11
