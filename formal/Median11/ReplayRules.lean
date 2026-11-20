import Median11.RowBits

namespace Median11

def standardGates (n : Nat) : List (Gate n) :=
  (wires n).flatMap fun i =>
    (wires n).filterMap fun j => if h : i < j then some ⟨i, j, Fin.ne_of_lt h⟩ else none

theorem mem_standardGates (g : Gate n) (ordered : g.lo < g.hi) :
    g ∈ standardGates n := by
  apply List.mem_flatMap.mpr
  exact ⟨g.lo, mem_wires _, List.mem_filterMap.mpr ⟨g.hi, mem_wires _, by simp [ordered]⟩⟩

def distinctRows (xs : List (Row n Bool)) : List (Row n Bool) := (gatherDistinct xs).2

@[simp] theorem mem_distinctRows (x : Row n Bool) (xs : List (Row n Bool)) :
    x ∈ distinctRows xs ↔ x ∈ xs := (gatherDistinct_spec xs).2.2 x

theorem distinctRows_nodup (xs : List (Row n Bool)) : (distinctRows xs).Nodup :=
  (gatherDistinct_spec xs).2.1

def Layers.distinct (a : Layers n) : Layers n :=
  ⟨distinctRows a.low, distinctRows a.high⟩

theorem Layers.distinct_same (a : Layers n) : SameMembers a.distinct a :=
  ⟨fun x => mem_distinctRows x a.low, fun x => mem_distinctRows x a.high⟩

def pathTest (p : Network n) (k b : Nat) (i : Fin n) (v : Bool) : Bool :=
  decide (rootBudget p k < (trace p i v).2 + b)

def varies (xs : List (Row n Bool)) (j : Fin n) : Bool :=
  xs.any (fun x => x.get j) && xs.any (fun x => !(x.get j))

theorem varies_sound (xs : List (Row n Bool)) (j : Fin n) (h : varies xs j = true) :
    ∃ x ∈ xs, ∃ y ∈ xs, x.get j ≠ y.get j := by
  simp only [varies, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true] at h
  obtain ⟨⟨x, hx, xb⟩, y, hy, yb⟩ := h
  exact ⟨x, hx, y, hy, fun e => by rw [← e, xb] at yb; contradiction⟩

def frozenTest (a : Layers n) (p : Network n) (k b : Nat) (i : Fin n) (v : Bool) : Bool :=
  let t := trace p i v
  decide (t.2 + b = rootBudget p k) && (varies a.low t.1 || varies a.high t.1)

theorem frozen_test_sound {a : Layers (n+1)} {p : Network (n+1)} {r k b : Nat}
    (same : SameMembers a (images p r))
    (pos : 0 < r) (valid : r ≤ n+1) (i : Fin (n+1)) (v : Bool)
    (bound : IncidenceBound n r v b) (h : frozenTest a p k b i v = true) :
    Excludes a k := by
  apply (same.exclusion k).mpr
  simp only [frozenTest, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  have close {xs : List (Row (n+1) Bool)} {w : Nat}
      (incl : ∀ z ∈ xs, ∃ u, weight u = w ∧ run p u = z)
      (layer : w = n+1-r ∨ w = n+1-r+1) (vary : varies xs (trace p i v).1 = true) :
      Excludes (images p r) k := by
    obtain ⟨u, hu, z, hz, diff⟩ := varies_sound _ _ vary
    obtain ⟨x, wx, rfl⟩ := incl u hu
    obtain ⟨y, wy, rfl⟩ := incl z hz
    exact frozen_prune p r k b i v pos valid bound h.1 x y (wx.trans wy.symm) (wx ▸ layer) diff
  rcases h.2 with low | high
  · apply close (w := n+1-r) _ (Or.inl rfl) low
    intro z hz
    have e := (same.1 z).mp hz
    simpa only [images, Layers.map, Layers.initial, List.mem_map, List.mem_filter,
      rows_complete, true_and, decide_eq_true_eq] using e
  · apply close (w := n+1-r+1) _ (Or.inr rfl) high
    intro z hz
    have e := (same.2 z).mp hz
    simpa only [images, Layers.map, Layers.initial, List.mem_map, List.mem_filter,
      rows_complete, true_and, decide_eq_true_eq] using e

theorem cardinality_test_sound {a : Layers n} {p : Network n} {r k : Nat}
    (same : SameMembers a (images p r)) (pos : 0 < r) (valid : r ≤ n)
    (h : 2^k < a.distinct.low.length ∨ 2^k < a.distinct.high.length) : Excludes a k := by
  apply (same.exclusion k).mpr
  have normalized := a.distinct_same.trans same
  rcases h with h | h
  · exact cardinality_prune p r k pos valid _ (distinctRows_nodup a.low) false
      (fun {x} hx => (normalized.1 x).mp hx) h
  · exact cardinality_prune p r k pos valid _ (distinctRows_nodup a.high) true
      (fun {x} hx => (normalized.2 x).mp hx) h

def relabelBySwaps (swaps : List (Fin n × Fin n)) : Relabel (Fin n) (Fin n) :=
  match swaps with
  | [] => ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  | (i,j) :: rest => (swapIso i j).trans (relabelBySwaps rest)

def contained (a b : List (Row n Bool)) : Bool :=
  let old := rowSet a
  old &&& rowSet b == old

theorem contained_sound {a b : List (Row n Bool)} (h : contained a b = true) : a ⊆ b := by
  intro x hx
  have old := (rowSet_mem x a).mpr hx
  have equal : rowSet a &&& rowSet b = rowSet a := of_decide_eq_true h
  have bits := congrArg (fun mask : Nat => mask.testBit (rowId x)) equal
  exact (rowSet_mem x b).mp (by simpa [old] using bits)

def memoTest (old current : Layers n) (k saved : Nat) (swaps : List (Fin n × Fin n)) : Bool :=
  let target := current.map (renameRow (relabelBySwaps swaps))
  decide (k ≤ saved) && contained old.low target.low && contained old.high target.high

theorem memo_test_sound (old current : Layers n) (k saved : Nat) (swaps : List (Fin n × Fin n))
    (done : Excludes old saved) (h : memoTest old current k saved swaps = true) :
    Excludes current k := by
  simp only [memoTest, Bool.and_eq_true, decide_eq_true_eq] at h
  exact memo_reuse _ _ _ _ _ h.1.1 done (contained_sound h.1.2) (contained_sound h.2)

end Median11
