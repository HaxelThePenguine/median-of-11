import Median11.PackedRows
import Median11.ReplayEncoding

namespace Median11
namespace PackedReplay

open PackedRows

abbrev Packed := Nat × Nat

def pack (a : Layers n) : Packed := (rowSet a.low, rowSet a.high)

theorem pack_same {a b : Layers n} (eq : pack a = pack b) : SameMembers a b := by
  have low : rowSet a.low = rowSet b.low := congrArg Prod.fst eq
  have high : rowSet a.high = rowSet b.high := congrArg Prod.snd eq
  exact ⟨fun x => by rw [← rowSet_mem, ← rowSet_mem, low],
    fun x => by rw [← rowSet_mem, ← rowSet_mem, high]⟩

def compare (c : Columns n) (g : Gate n) (a : Packed) : Packed :=
  (c.compare g a.1, c.compare g a.2)

theorem compare_pack (c : Columns n) (g : Gate n) (ordered : g.lo < g.hi) (a : Layers n) :
    compare c g (pack a) = pack (a.map (step g)) := by
  simp [compare, pack, Layers.map, c.compare_correct g ordered]

def setHas (bits mask : Nat) : Bool := bits &&& mask != 0

theorem rowSet_ne_zero (xs : List (Row n Bool)) :
    rowSet xs ≠ 0 ↔ ∃ x, x ∈ xs := by
  cases xs with
  | nil => simp [rowSet]
  | cons x xs =>
    refine ⟨fun _ => ⟨x, by simp⟩, fun _ e => ?_⟩
    have h := (rowSet_mem x (x :: xs)).mpr (by simp)
    simp [e] at h

theorem setHas_iff (xs : List (Row n Bool)) (m : Nat) :
    setHas (rowSet xs) m = true ↔ ∃ x ∈ xs, m.testBit (rowId x) = true := by
  simp only [setHas, bne_iff_ne, ← rowSet_filter, rowSet_ne_zero, filterBits, List.mem_filter]

def useful (c : Columns n) (g : Gate n) (a : Packed) : Bool :=
  setHas (a.1 ||| a.2) (c.discord g.lo g.hi) &&
    setHas (a.1 ||| a.2) (c.discord g.hi g.lo)

theorem useful_pack (c : Columns n) (g : Gate n) (a : Layers n) :
    useful c g (pack a) = keepsBoth a g := by
  apply Bool.eq_iff_iff.mpr
  simp [useful, pack, ← rowSet_append, setHas_iff, keepsBoth_iff, Bool.and_eq_true, and_comm]

def variesAt (c : Columns n) (bits : Nat) (i : Fin n) : Bool :=
  setHas bits (c.ones i) && (minus bits (c.ones i) != 0)

theorem varies_pack (c : Columns n) (xs : List (Row n Bool)) (i : Fin n) :
    variesAt c (rowSet xs) i = varies xs i := by
  apply Bool.eq_iff_iff.mpr
  simp [variesAt, varies, setHas_iff, Bool.and_eq_true, c.correct, bne_iff_ne,
    ← rowSet_filter_not, rowSet_ne_zero, filterBits, List.mem_filter, mask, id_lt, List.any_eq_true]

def noSeparator (c : Columns n) (a : Packed) : Bool :=
  (wires n).all fun i => setHas a.1 (c.ones i) || minus a.2 (c.ones i) != 0

theorem noSeparator_pack (c : Columns n) (a : Layers n) :
    noSeparator c (pack a) = immediateFailure a := by
  apply Bool.eq_iff_iff.mpr
  simp only [noSeparator, immediateFailure, isSeparator, pack, List.all_eq_true]
  have aux (i : Fin n) :
      (setHas (rowSet a.low) (c.ones i) || minus (rowSet a.high) (c.ones i) != 0) = true ↔
        (!(a.low.all (fun x => !x.get i) && a.high.all fun x => x.get i)) = true := by
    rw [show (!(a.low.all (fun x => !x.get i) && a.high.all fun x => x.get i)) = true ↔
      (a.low.all (fun x => !x.get i) && a.high.all fun x => x.get i) = false by
        cases a.low.all (fun x => !x.get i) <;> cases a.high.all (fun x => x.get i) <;> decide]
    simp [Bool.or_eq_true, setHas_iff, c.correct, bne_iff_ne, ← rowSet_filter_not,
      rowSet_ne_zero, filterBits, List.mem_filter, minus_bit, mask, Nat.testBit_two_pow_sub_one,
      id_lt, Bool.and_eq_false_iff, List.all_eq_false, -Bool.and_eq_false_imp]
  exact ⟨fun h i hi => (aux i).mp (h i hi), fun h i hi => (aux i).mpr (h i hi)⟩

def frozen (c : Columns n) (a : Packed) (p : Network n) (k b : Nat)
    (i : Fin n) (v : Bool) : Bool :=
  let t := trace p i v
  decide (t.2 + b = rootBudget p k) && (variesAt c a.1 t.1 || variesAt c a.2 t.1)

theorem frozen_pack (c : Columns n) (a : Layers n) (p : Network n) (k b : Nat)
    (i : Fin n) (v : Bool) : frozen c (pack a) p k b i v = frozenTest a p k b i v := by
  simp [frozen, pack, frozenTest, varies_pack]

def exchangeWires (c : Columns n) (i j : Fin n) (a : Packed) : Packed :=
  if h : i < j then
    let g : Gate n := ⟨i,j,Fin.ne_of_lt h⟩
    (c.exchange g a.1, c.exchange g a.2)
  else if h : j < i then
    let g : Gate n := ⟨j,i,Fin.ne_of_lt h⟩
    (c.exchange g a.1, c.exchange g a.2)
  else a

theorem swapIndex_comm (i j k : Fin n) : swapIndex i j k = swapIndex j i k := by
  by_cases a : i = k <;> by_cases b : j = k <;> simp_all [swapIndex]

theorem exchangeWires_pack (c : Columns n) (i j : Fin n) (a : Layers n) :
    exchangeWires c i j (pack a) = pack (a.map (renameRow (swapIso i j))) := by
  unfold exchangeWires
  split
  · rename_i h
    simp only [pack, Layers.map, c.exchange_correct ⟨i,j,Fin.ne_of_lt h⟩ h]
    rfl
  · split
    · rename_i h
      have e : renameRow (swapIso j i) = (renameRow (swapIso i j) : Row n Bool → Row n Bool) := by
        funext x
        apply row_ext
        intro k
        simp [swapIso, swapIndex_comm j i]
      simp only [pack, Layers.map, c.exchange_correct ⟨j,i,Fin.ne_of_lt h⟩ h]
      change (_, _) = (_, _)
      change (rowSet (a.low.map (renameRow (swapIso j i))), rowSet (a.high.map (renameRow (swapIso j i)))) = _
      rw [e]
    · rename_i le ge
      have eq : i = j := Fin.ext (Nat.le_antisymm (Nat.le_of_not_gt ge) (Nat.le_of_not_gt le))
      subst j
      have self : renameRow (swapIso i i) = (id : Row n Bool → Row n Bool) := by
        funext x
        apply row_ext
        intro k
        by_cases h : i = k <;> simp [swapIso, swapIndex, h]
      simp [self, pack, Layers.map]

def relabel (c : Columns n) : List (Fin n × Fin n) → Packed → Packed
  | [], a => a
  | (i,j) :: more, a => relabel c more (exchangeWires c i j a)

theorem relabel_pack (c : Columns n) (swaps : List (Fin n × Fin n)) (a : Layers n) :
    relabel c swaps (pack a) = pack (a.map (renameRow (relabelBySwaps swaps))) := by
  induction swaps generalizing a with
  | nil =>
    have e : renameRow (relabelBySwaps ([] : List (Fin n × Fin n))) =
        (id : Row n Bool → Row n Bool) := by
      funext x
      exact row_ext fun k => by simp [relabelBySwaps]
    simp [relabel, e, Layers.map]
  | cons pair rest ih =>
    obtain ⟨i,j⟩ := pair
    rw [relabel, exchangeWires_pack, ih]
    have e : renameRow (relabelBySwaps ((i,j) :: rest)) =
        (renameRow (relabelBySwaps rest) ∘ renameRow (swapIso i j) : Row n Bool → Row n Bool) := by
      funext x
      exact row_ext fun k => by simp [relabelBySwaps, Relabel.trans]
    simp [e, Layers.map, List.map_map]

def cover (a b : Nat) : Bool := a &&& b == a

theorem cover_sound {xs ys : List (Row n Bool)} (ok : cover (rowSet xs) (rowSet ys) = true) :
    xs ⊆ ys := contained_sound ok

/-- A cardinality leaf supplies distinct row IDs in the chosen layer. -/
def sample (n : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k+1, bits, data =>
    let i := data % 2^n
    bits.testBit i && sample n k (minus bits (2^i)) (data / 2^n)

theorem sample_sound (xs : List (Row n Bool)) (k data : Nat)
    (ok : sample n k (rowSet xs) data = true) :
    ∃ ys : List (Row n Bool), ys.Nodup ∧ ys ⊆ xs ∧ ys.length = k := by
  induction k generalizing xs data with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    let i := data % 2^n
    let x := row n i
    have id : rowId x = i := id_row (Nat.mod_lt _ (Nat.two_pow_pos n))
    have h : (rowSet xs).testBit i = true ∧
        sample n k (minus (rowSet xs) (2^i)) (data / 2^n) = true := by
      simpa only [sample, Bool.and_eq_true] using ok
    have mem : x ∈ xs := (rowSet_mem _ _).mp (id ▸ h.1)
    let rest := filterBits (minus (mask n) (2^i)) xs
    have next : sample n k (rowSet rest) (data / 2^n) = true := by
      rw [rowSet_filter_not]
      exact h.2
    obtain ⟨ys, nd, sub, len⟩ := ih rest _ next
    have absent : x ∉ ys := by
      intro hx
      have e := (List.mem_filter.mp (sub hx)).2
      simp [id] at e
    exact ⟨x :: ys, List.nodup_cons.mpr ⟨absent, nd⟩,
      List.cons_subset.mpr ⟨mem, fun _ hz => (List.mem_filter.mp (sub hz)).1⟩, by simp [len]⟩

structure Entry where
  start : Nat
  stop : Nat
  budget : Nat
  layers : Packed
  deriving Inhabited

def Entry.Valid (n : Nat) (e : Entry) : Prop :=
  ∃ a : Layers n, pack a = e.layers ∧ Excludes a e.budget

inductive Rule (n : Nat) where
  | redundant
  | path (wire : Fin n) (sign : Bool)
  | child (slot : Nat)
  | cardinality (side : Bool) (rows : Nat)
  | reference (slot offset : Nat) (swaps : List (Fin n × Fin n))
  | frozen (wire : Fin n) (sign : Bool)

def lookupChild (find : Nat → Option Entry) (slot start budget : Nat) (a : Packed) :
    Option Nat := do
  let e ← find slot
  if e.start == start && e.budget == budget && decide (e.layers = a) && decide (start < e.stop) then
    some e.stop
  else none

def lookupReference (c : Columns n) (find : Nat → Option Entry) (slot offset start budget : Nat)
    (a : Packed) (swaps : List (Fin n × Fin n)) : Bool :=
  match find slot with
  | none => false
  | some e =>
    let target := relabel c swaps a
    e.start == offset && decide (e.stop ≤ start) && decide (budget ≤ e.budget) &&
      cover e.layers.1 target.1 && cover e.layers.2 target.2

def checkEdge (c : Columns n) (find : Nat → Option Entry) (b₀ b₁ k : Nat)
    (p : Network n) (a : Packed) (g : Gate n) (start : Nat) : Rule n → Option Nat
  | .redundant => if useful c g a then none else some start
  | .path i v => if pathTest (p ++ [g]) k (if v then b₁ else b₀) i v then some start else none
  | .child slot => lookupChild find slot start k (compare c g a)
  | .cardinality side rows =>
    let child := compare c g a
    if sample n (2^k+1) (if side then child.2 else child.1) rows then some (start+1) else none
  | .frozen i v =>
    if frozen c (compare c g a) (p ++ [g]) k (if v then b₁ else b₀) i v then
      some (start+1)
    else none
  | .reference slot offset swaps =>
    if lookupReference c find slot offset start k (compare c g a) swaps then some (start+1) else none

theorem checkEdge_sound {r b₀ b₁ : Nat} (pos : 0 < r) (valid : r ≤ n+1)
    (lower : IncidenceBound n r false b₀) (upper : IncidenceBound n r true b₁)
    (c : Columns (n+1)) (find : Nat → Option Entry)
    (well : ∀ i e, find i = some e → e.Valid (n+1))
    (k : Nat) (p : Network (n+1)) (g : Gate (n+1)) (ordered : g.lo < g.hi)
    (start stop : Nat) (rule : Rule (n+1))
    (checked : checkEdge c find b₀ b₁ k p (pack (images p r)) g start rule = some stop) :
    keepsBoth (images p r) g = true → Excludes ((images p r).map (step g)) k := by
  have packed : compare c g (pack (images p r)) = pack (images (p ++ [g]) r) := by
    rw [compare_pack c g ordered, image_descend]
  have same : SameMembers (images (p ++ [g]) r) (images (p ++ [g]) r) :=
    ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  cases rule with
  | redundant =>
    intro h
    simp [checkEdge, useful_pack, h] at checked
  | path i v =>
    intro _
    cases v
    · have h : pathTest (p ++ [g]) k b₀ i false = true := by
        cases h : pathTest (p ++ [g]) k b₀ i false <;> simp_all [checkEdge]
      rw [← image_descend]
      exact path_prune _ _ _ _ _ _ pos valid lower (of_decide_eq_true h)
    · have h : pathTest (p ++ [g]) k b₁ i true = true := by
        cases h : pathTest (p ++ [g]) k b₁ i true <;> simp_all [checkEdge]
      rw [← image_descend]
      exact path_prune _ _ _ _ _ _ pos valid upper (of_decide_eq_true h)
  | child slot =>
    intro _
    simp only [checkEdge, packed, lookupChild] at checked
    cases h : find slot with
    | none => simp [h] at checked
    | some e =>
      obtain ⟨old, eq, excluded⟩ := well slot e h
      simp only [h, bind, Option.bind] at checked
      split at checked
      · rename_i cond
        have data : e.budget = k ∧ e.layers = pack (images (p ++ [g]) r) := by
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at cond
          exact ⟨cond.1.1.2, cond.1.2⟩
        rw [← image_descend]
        exact ((pack_same (eq.trans data.2)).exclusion k).mp (data.1 ▸ excluded)
      · contradiction
  | cardinality side ids =>
    intro _
    rw [← image_descend]
    simp only [checkEdge, packed] at checked
    let layer := if side then (images (p ++ [g]) r).high else (images (p ++ [g]) r).low
    have pass : sample (n+1) (2^k+1) (rowSet layer) ids = true := by
      have test : (if side then (pack (images (p ++ [g]) r)).2 else (pack (images (p ++ [g]) r)).1) =
          rowSet layer := by cases side <;> rfl
      rw [test] at checked
      cases h : sample (n+1) (2^k+1) (rowSet layer) ids <;> simp_all
    obtain ⟨rows, nd, sub, len⟩ := sample_sound layer _ ids pass
    exact cardinality_prune _ _ _ pos valid rows nd side sub (by omega)
  | frozen i sign =>
    intro _
    rw [← image_descend]
    simp only [checkEdge, packed, frozen_pack] at checked
    have ok : frozenTest (images (p ++ [g]) r) (p ++ [g]) k (if sign then b₁ else b₀) i sign = true := by
      cases h : frozenTest (images (p ++ [g]) r) (p ++ [g]) k (if sign then b₁ else b₀) i sign <;>
        simp_all only [Bool.false_eq_true, if_false, if_true, reduceCtorEq]
    cases sign
    · exact frozen_test_sound same pos valid i false lower ok
    · exact frozen_test_sound same pos valid i true upper ok
  | reference slot offset swaps =>
    intro _
    rw [← image_descend]
    simp only [checkEdge, packed, lookupReference] at checked
    cases h : find slot with
    | none => simp [h] at checked
    | some e =>
      obtain ⟨old, eq, excluded⟩ := well slot e h
      simp only [h] at checked
      split at checked
      · rename_i ok
        rw [← eq, relabel_pack] at ok
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
        exact memo_reuse _ _ _ _ _ ok.1.1.2 excluded
          (cover_sound ok.1.2) (cover_sound ok.2)
      · contradiction

theorem standardGates_ordered {g : Gate n} (h : g ∈ standardGates n) : g.lo < g.hi := by
  unfold standardGates at h
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hi
  split at hj
  · rename_i ord
    cases Option.some.inj hj
    assumption
  · contradiction

def checkEdges (visit : Gate n → Nat → Rule n → Option Nat) :
    List (Gate n) → List (Rule n) → Nat → Option Nat
  | [], [], start => some start
  | g :: gs, op :: ops, start => (visit g start op).bind (checkEdges visit gs ops)
  | _, _, _ => none

theorem checkEdges_sound (visit : Gate n → Nat → Rule n → Option Nat)
    (claim : Gate n → Prop) (gates : List (Gate n)) (rules : List (Rule n))
    (sound : ∀ g ∈ gates, ∀ i j op, visit g i op = some j → claim g)
    (i j : Nat) (checked : checkEdges visit gates rules i = some j) :
    ∀ g ∈ gates, claim g := by
  induction gates generalizing i rules with
  | nil => simp
  | cons g gs ih =>
    cases rules with
    | nil => simp [checkEdges] at checked
    | cons op ops =>
      cases h : visit g i op with
      | none => simp [checkEdges,h] at checked
      | some t =>
        intro a ha
        rcases List.mem_cons.mp ha with eq | hh
        · subst a
          exact sound g (by simp) i t op h
        · exact ih ops (fun a h => sound a (List.mem_cons_of_mem _ h)) t
            (by simpa [checkEdges,h] using checked) a hh

structure Job (n : Nat) where
  path : Network n
  children : List (Rule n)

def checkJob (c : Columns n) (root : Packed) (find : Nat → Option Entry)
    (b₀ b₁ : Nat) (job : Job n) (e : Entry) : Bool :=
  match e.budget with
  | 0 => false
  | k+1 =>
    job.path.all (fun g => decide (g.lo < g.hi)) &&
    decide (job.path.foldl (fun a g => compare c g a) root = e.layers) &&
    noSeparator c e.layers &&
    checkEdges (checkEdge c find b₀ b₁ k job.path e.layers) (standardGates n)
      job.children (e.start+1) == some e.stop

theorem fold_pack (c : Columns n) (p : Network n) (a : Layers n) (ordered : Standard p) :
    p.foldl (fun a g => compare c g a) (pack a) = pack (a.map (run p)) := by
  induction p generalizing a with
  | nil =>
    have identity : run ([] : Network n) (α := Bool) = id := rfl
    simp [identity, Layers.map]
  | cons g gs ih =>
    rw [List.foldl_cons, compare_pack c g (ordered g (by simp))]
    rw [ih _ (fun g h => ordered g (List.mem_cons_of_mem _ h))]
    simp [Layers.map, List.map_map, run, Function.comp_def]

theorem checkJob_sound {r b₀ b₁ : Nat} (pos : 0 < r) (valid : r ≤ n+1)
    (lower : IncidenceBound n r false b₀) (upper : IncidenceBound n r true b₁)
    (c : Columns (n+1)) (root : Packed) (root_eq : root = pack (Layers.initial (n+1) r))
    (find : Nat → Option Entry) (well : ∀ i e, find i = some e → e.Valid (n+1))
    (job : Job (n+1)) (e : Entry) (checked : checkJob c root find b₀ b₁ job e = true) :
    e.Valid (n+1) := by
  cases h : e.budget with
  | zero => simp [checkJob,h] at checked
  | succ k =>
    simp only [checkJob, h, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
    have ordered : Standard job.path := by
      simpa [Standard, List.all_eq_true] using checked.1.1.1
    have eq : pack (images job.path r) = e.layers := by
      have computed := checked.1.1.2
      rw [root_eq, fold_pack c job.path _ ordered] at computed
      exact computed
    refine ⟨images job.path r, eq, ?_⟩
    rw [h]
    have empty := checked.1.2
    rw [← eq, noSeparator_pack] at empty
    have edges := checked.2
    rw [← eq] at edges
    apply expand_sound _ _ empty
    intro g ord
    exact checkEdges_sound _ _ _ _
      (fun g hh i j op ok => checkEdge_sound pos valid lower upper c find well k job.path g
        (standardGates_ordered hh) i j op ok) _ _ edges g (mem_standardGates g ord)

/-- Entries imported by a block have already been checked. The rule's slot
is either an even index in the imports or an odd index in the local outputs. -/
structure Certified (n : Nat) where
  entries : Array Entry
  sound : ∀ e ∈ entries, e.Valid n

def pickEntries (source : Array Entry) (ids : List Nat) : Array Entry :=
  (ids.filterMap (fun i => source[i]?)).toArray

def mergeEntries (sources : List (Array Entry)) : Array Entry :=
  (sources.flatMap Array.toList).toArray

def Certified.pick (source : Certified n) (ids : List Nat) : Certified n where
  entries := pickEntries source.entries ids
  sound := by
    intro e h
    have listed : e ∈ ids.filterMap (fun i => source.entries[i]?) := by simpa [pickEntries] using h
    obtain ⟨i, _, h⟩ := List.mem_filterMap.mp listed
    exact source.sound e (Array.mem_of_getElem? h)

def Certified.merge (sources : List (Certified n)) : Certified n where
  entries := mergeEntries (sources.map (·.entries))
  sound := by
    intro e h
    have listed : e ∈ sources.flatMap (fun s => s.entries.toList) := by
      simpa [mergeEntries, List.flatMap_map] using h
    obtain ⟨src, _, h⟩ := List.mem_flatMap.mp listed
    exact src.sound e (by simpa using h)

def lookup (imports outputs : Array Entry) (position slot : Nat) : Option Entry :=
  let i := slot / 2
  if slot % 2 == 0 then imports[i]?
  else if i < position then outputs[i]? else none

def VerifiedPrefix (n : Nat) (outputs : Array Entry) (position : Nat) : Prop :=
  ∀ i < position, ∀ e, outputs[i]? = some e → e.Valid n

theorem lookup_sound (imports : Certified n) (outputs : Array Entry) (position : Nat)
    (prev : VerifiedPrefix n outputs position) :
    ∀ i e, lookup imports.entries outputs position i = some e → e.Valid n := by
  intro slot e h
  unfold lookup at h
  split at h
  · exact imports.sound e (Array.mem_of_getElem? h)
  · dsimp only at h
    split at h <;> rename_i hi
    · exact prev _ hi e h
    · contradiction

def checkJobs (c : Columns n) (root : Packed) (imports outputs : Array Entry)
    (b₀ b₁ : Nat) : Nat → List (Job n) → Bool
  | i, [] => i == outputs.size
  | i, job :: jobs =>
    match outputs[i]? with
    | none => false
    | some e => checkJob c root (lookup imports outputs i) b₀ b₁ job e &&
        checkJobs c root imports outputs b₀ b₁ (i+1) jobs

theorem checkJobs_sound {r b₀ b₁ : Nat} (pos : 0 < r) (valid : r ≤ n+1)
    (lower : IncidenceBound n r false b₀) (upper : IncidenceBound n r true b₁)
    (c : Columns (n+1)) (root : Packed) (root_eq : root = pack (Layers.initial (n+1) r))
    (imports : Certified (n+1)) (outputs : Array Entry) (i : Nat) (jobs : List (Job (n+1)))
    (prev : VerifiedPrefix (n+1) outputs i)
    (checked : checkJobs c root imports.entries outputs b₀ b₁ i jobs = true) :
    ∀ e ∈ outputs, e.Valid (n+1) := by
  induction jobs generalizing i with
  | nil =>
    have eq : i = outputs.size := by simpa [checkJobs] using checked
    intro e he
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp he
    exact prev j (eq ▸ hj) _ (by simp [hj])
  | cons job remaining ih =>
    cases h : outputs[i]? with
    | none => simp [checkJobs,h] at checked
    | some e =>
      simp only [checkJobs,h,Bool.and_eq_true] at checked
      apply ih (i+1) _ checked.2
      intro j hj entry found
      by_cases lt : j < i
      · exact prev j lt entry found
      · have same : j = i := by omega
        subst j
        rw [h] at found
        cases Option.some.inj found
        exact checkJob_sound pos valid lower upper c root root_eq _
          (lookup_sound imports outputs i prev) job e checked.1

def certify (c : Columns (n+1)) (r b₀ b₁ : Nat) (root : Packed) (imports : Certified (n+1))
    (outputs : Array Entry) (jobs : List (Job (n+1)))
    (pos : 0 < r) (valid : r ≤ n+1)
    (lower : IncidenceBound n r false b₀) (upper : IncidenceBound n r true b₁)
    (root_eq : root = pack (Layers.initial (n+1) r))
    (checked : checkJobs c root imports.entries outputs b₀ b₁ 0 jobs = true) : Certified (n+1) :=
  ⟨outputs, checkJobs_sound pos valid lower upper c root root_eq imports outputs 0 jobs
    (by simp [VerifiedPrefix]) checked⟩

theorem root_bound (pos : 0 < r) (valid : r ≤ n) (block : Certified n)
    (i budget size : Nat) (root : Packed) (root_eq : root = pack (Layers.initial n r))
    (checked : (block.entries[i]?.map (fun e => (e.start,e.stop,e.budget,e.layers))) =
      some (0,size,budget,root)) : Bound n r (budget+1) := by
  cases h : block.entries[i]? with
  | none => simp [h] at checked
  | some e =>
    obtain ⟨a,eq,excluded⟩ := block.sound e (Array.mem_of_getElem? h)
    simp [h] at checked
    exact initial_exclusion_sound pos valid
      (((pack_same (eq.trans (checked.2.2.2.trans root_eq))).exclusion budget).mp
        (checked.2.2.1 ▸ excluded))

def decodePath (n count code : Nat) : Network (n+1) :=
  (decodeSwaps n count code).filterMap fun (i,j) =>
    if h : i < j then some ⟨i,j,Fin.ne_of_lt h⟩ else none

end PackedReplay
end Median11
