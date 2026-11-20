import Median11.ReplayRules

namespace Median11

/-- A sparse persistent table. A memo entry becomes visible only when its
whole expansion has been verified. Keys are preorder offsets. -/
inductive MemoTable (α : Type) where
  | empty
  | leaf (value : α)
  | branch (even odd : MemoTable α)

def MemoTable.getAt (t : MemoTable α) : List Bool → Option α
  | [] => match t with | .leaf value => some value | _ => none
  | bit :: rest =>
    match t with
    | .branch l r => (if bit then r else l).getAt rest
    | _ => none

def MemoTable.putAt (t : MemoTable α) (value : α) : List Bool → MemoTable α
  | [] => .leaf value
  | bit :: rest =>
    let (l,r) := match t with | .branch l r => (l,r) | _ => (.empty,.empty)
    if bit then .branch l (r.putAt value rest) else .branch (l.putAt value rest) r

def memoAddress : Nat → Nat → List Bool
  | 0, _ => []
  | k+1, id => (id % 2 == 1) :: memoAddress k (id/2)

def MemoTable.get (t : MemoTable α) (id : Nat) : Option α := t.getAt (memoAddress 20 id)

def MemoTable.put (t : MemoTable α) (id : Nat) (value : α) : MemoTable α :=
  t.putAt value (memoAddress 20 id)

@[simp] theorem MemoTable.getAt_empty (key : List Bool) :
    (MemoTable.empty : MemoTable α).getAt key = none := by
  cases key <;> rfl

theorem MemoTable.getAt_putAt_source (t : MemoTable α) (a b : List Bool) (value result : α)
    (h : (t.putAt value a).getAt b = some result) :
    result = value ∨ t.getAt b = some result := by
  induction a generalizing t b with
  | nil => cases b <;> simp_all [MemoTable.getAt, MemoTable.putAt, eq_comm]
  | cons bit rest ih =>
    cases b with
    | nil => cases bit <;> cases t <;> simp [MemoTable.getAt, MemoTable.putAt] at h
    | cons q tail =>
      cases bit <;> cases q <;> cases t <;>
        simp_all [MemoTable.getAt, MemoTable.putAt] <;>
        first | exact ih _ _ h | exact (ih _ _ h).resolve_right (by simp)

theorem MemoTable.get_put_source (t : MemoTable α) (id q : Nat) (value result : α)
    (h : (t.put id value).get q = some result) :
    result = value ∨ t.get q = some result :=
  t.getAt_putAt_source _ _ _ _ h

/-- Opcodes 0 through 3 match the distributed preorder format. The reference
adds a proposed earlier offset and a permutation witness. Both are checked. -/
inductive ReplayOp (n : Nat) where
  | expand
  | cardinality
  | reference (offset : Nat) (swaps : List (Fin n × Fin n))
  | frozen
  deriving Inhabited

def ReplayOp.code : ReplayOp n → Nat
  | .expand => 0
  | .cardinality => 1
  | .reference _ _ => 2
  | .frozen => 3

structure ReplayState (n : Nat) where
  stream : List (ReplayOp n)
  index : Nat
  table : MemoTable (Layers n × Nat)

def ReplayState.advance (s : ReplayState n) (tail : List (ReplayOp n)) : ReplayState n :=
  ⟨tail, s.index + 1, s.table⟩

def ReplayState.save (s : ReplayState n) (offset : Nat) (a : Layers n) (k : Nat) :
    ReplayState n := {s with table := s.table.put offset (a,k)}

def ReplayState.valid (s : ReplayState n) : Prop :=
  ∀ id a k, s.table.get id = some (a,k) → Excludes a k

theorem ReplayState.save_valid {s : ReplayState n} (good : s.valid)
    {a : Layers n} {k : Nat} (closed : Excludes a k) (offset : Nat) :
    (s.save offset a k).valid := by
  intro id b j found
  rcases MemoTable.get_put_source s.table offset id (a,k) (b,j) found with equal | before
  · cases equal
    exact closed
  · exact good _ _ _ before

def scanChildren (visit : Gate n → ReplayState n → Option (ReplayState n))
    : List (Gate n) → ReplayState n → Option (ReplayState n)
  | [], state => some state
  | g :: rest, state => (visit g state).bind (scanChildren visit rest)

theorem scan_children_sound (visit : Gate n → ReplayState n → Option (ReplayState n))
    (claim : Gate n → Prop) (gates : List (Gate n))
    (sound : ∀ g ∈ gates, ∀ s t, s.valid → visit g s = some t → t.valid ∧ claim g)
    (s t : ReplayState n) (valid : s.valid) (checked : scanChildren visit gates s = some t) :
    t.valid ∧ ∀ g ∈ gates, claim g := by
  induction gates generalizing s with
  | nil =>
    have eq : s = t := by simpa [scanChildren] using checked
    subst s
    exact ⟨valid, by simp⟩
  | cons g gs ih =>
    cases pass : visit g s with
    | none => simp [scanChildren, pass] at checked
    | some next =>
      have done := sound g (by simp) s next valid pass
      have rest := ih (fun h hh => sound h (List.mem_cons_of_mem g hh))
        next done.1 (by simpa [scanChildren, pass] using checked)
      exact ⟨rest.1, fun h hh => (List.mem_cons.mp hh).elim (fun eq => eq.symm ▸ done.2)
        (rest.2 h)⟩

def somePathTest (p : Network n) (k b₀ b₁ : Nat) : Bool :=
  (wires n).any (fun i => pathTest p k b₀ i false || pathTest p k b₁ i true)

def someFrozenTest (a : Layers n) (p : Network n) (k b₀ b₁ : Nat) : Bool :=
  (wires n).any (fun i => frozenTest a p k b₀ i false || frozenTest a p k b₁ i true)

theorem some_path_sound {p : Network (n+1)} {r k b₀ b₁ : Nat}
    (pos : 0 < r) (valid : r ≤ n+1) (lower : IncidenceBound n r false b₀)
    (upper : IncidenceBound n r true b₁) (h : somePathTest p k b₀ b₁ = true) :
    Excludes (images p r) k := by
  obtain ⟨i, _, tests⟩ := List.any_eq_true.mp h
  simp only [Bool.or_eq_true] at tests
  rcases tests with lo | hi
  · exact path_prune p r k b₀ i false pos valid lower (of_decide_eq_true lo)
  · exact path_prune p r k b₁ i true pos valid upper (of_decide_eq_true hi)

theorem some_frozen_sound {a : Layers (n+1)} {p : Network (n+1)} {r k b₀ b₁ : Nat}
    (same : SameMembers a (images p r)) (pos : 0 < r) (valid : r ≤ n+1)
    (lower : IncidenceBound n r false b₀) (upper : IncidenceBound n r true b₁)
    (h : someFrozenTest a p k b₀ b₁ = true) : Excludes a k := by
  obtain ⟨i, _, tests⟩ := List.any_eq_true.mp h
  simp only [Bool.or_eq_true] at tests
  rcases tests with lo | hi
  · exact frozen_test_sound same pos valid i false lower lo
  · exact frozen_test_sound same pos valid i true upper hi

def replay (b₀ b₁ : Nat) :
    Nat → Network n → Layers n → ReplayState n → Option (ReplayState n)
  | k, p, a, s =>
    if !immediateFailure a then none else
      match s.stream with
      | [] => none
      | cmd :: tail =>
        let next := s.advance tail
        match cmd with
        | .cardinality =>
          if 2^k < a.distinct.low.length ∨ 2^k < a.distinct.high.length then some next else none
        | .frozen =>
          if someFrozenTest a p k b₀ b₁ then some next else none
        | .reference id swaps => do
          let (old, saved) ← s.table.get id
          if memoTest old a k saved swaps then some next else none
        | .expand =>
          match k with
          | 0 => none
          | j+1 => do
            let after ← scanChildren (fun g state =>
              if !keepsBoth a g || somePathTest (p++[g]) j b₀ b₁ then some state
              else replay b₀ b₁ j (p++[g]) ((a.map (step g)).distinct) state)
              (standardGates n) next
            some (after.save s.index a (j+1))

theorem replay_sound {r b₀ b₁ : Nat} (pos : 0 < r) (valid : r ≤ n+1)
    (lower : IncidenceBound n r false b₀) (upper : IncidenceBound n r true b₁)
    (k : Nat) (p : Network (n+1)) (a : Layers (n+1))
    (same : SameMembers a (images p r)) (s t : ReplayState (n+1))
    (well : s.valid) (checked : replay b₀ b₁ k p a s = some t) :
    t.valid ∧ Excludes a k := by
  induction k using Nat.strongRecOn generalizing p a s t with
  | ind k ih =>
    by_cases empty : immediateFailure a = true
    · cases cmds : s.stream with
      | nil => simp [replay, empty, cmds] at checked
      | cons cmd tail =>
        have nxt : (s.advance tail).valid := well
        cases cmd with
        | cardinality =>
          by_cases many : 2^k < a.distinct.low.length ∨ 2^k < a.distinct.high.length
          · have e : s.advance tail = t := by simpa [replay, empty, cmds, many] using checked
            exact ⟨e ▸ nxt, cardinality_test_sound same pos valid many⟩
          · simp [replay, empty, cmds, many] at checked
        | frozen =>
          cases h : someFrozenTest a p k b₀ b₁ with
          | false => simp [replay, empty, cmds, h] at checked
          | true =>
            have e : s.advance tail = t := by simpa [replay, empty, cmds, h] using checked
            exact ⟨e ▸ nxt, some_frozen_sound same pos valid lower upper h⟩
        | reference offset swaps =>
          cases found : s.table.get offset with
          | none => simp [replay, empty, cmds, found] at checked
          | some hit =>
            obtain ⟨old, saved⟩ := hit
            cases h : memoTest old a k saved swaps with
            | false => simp [replay, empty, cmds, found, h] at checked
            | true =>
              have e : s.advance tail = t := by simpa [replay, empty, cmds, found, h] using checked
              exact ⟨e ▸ nxt, memo_test_sound _ _ _ _ _ (well _ _ _ found) h⟩
        | expand =>
          cases k with
          | zero => simp [replay, empty, cmds] at checked
          | succ j =>
            let visit := fun (g : Gate (n+1)) (state : ReplayState (n+1)) =>
              if !keepsBoth a g || somePathTest (p++[g]) j b₀ b₁ then some state
              else replay b₀ b₁ j (p++[g]) ((a.map (step g)).distinct) state
            let all := standardGates (n+1)
            have proceed :
                ∀ g ∈ all, ∀ u v, u.valid → visit g u = some v →
                  v.valid ∧ (keepsBoth a g = true → Excludes (a.map (step g)) j) := by
              intro g _ u v good ok
              have mapSame : SameMembers (a.map (step g)) (images (p++[g]) r) := by
                rw [image_descend]
                exact same.maps _
              cases useful : keepsBoth a g with
              | false =>
                have e : u = v := by simpa [visit, useful] using ok
                subst v
                exact ⟨good, by simp⟩
              | true =>
                cases path : somePathTest (p++[g]) j b₀ b₁ with
                | true =>
                  have e : u = v := by simpa [visit, useful, path] using ok
                  subst v
                  exact ⟨good, fun _ => (mapSame.exclusion j).mpr
                    (some_path_sound pos valid lower upper path)⟩
                | false =>
                  have run := ih j (by omega) (p++[g]) _
                    ((Layers.distinct_same _).trans mapSame) u v good
                    (by simpa [visit, useful, path] using ok)
                  exact ⟨run.1, fun _ => ((Layers.distinct_same _).exclusion j).mp run.2⟩
            rw [replay] at checked
            simp only [empty, Bool.not_true, Bool.false_eq_true, if_false, cmds] at checked
            change ((scanChildren visit all (s.advance tail)).bind fun out =>
              some (out.save s.index a (j+1))) = some t at checked
            cases h : scanChildren visit all (s.advance tail) with
            | none => simp [h] at checked
            | some out =>
              have result := scan_children_sound visit _ all proceed _ out nxt h
              have closed : Excludes a (j+1) := expand_sound a j empty
                (fun g lo useful => result.2 g (mem_standardGates g lo) useful)
              have e : out.save s.index a (j+1) = t := by simpa [h] using checked
              exact ⟨e ▸ ReplayState.save_valid result.1 closed _, closed⟩
    · simp [replay, Bool.eq_false_iff.mpr empty] at checked

def verifyReplay (n r budget b₀ b₁ : Nat) (stream : List (ReplayOp n)) : Bool :=
  match replay b₀ b₁ budget [] (Layers.initial n r) ⟨stream, 0, .empty⟩ with
  | none => false
  | some done => done.stream.isEmpty

theorem verify_replay_sound {r budget b₀ b₁ : Nat} (pos : 0 < r) (valid : r ≤ n+1)
    (lower : IncidenceBound n r false b₀) (upper : IncidenceBound n r true b₁)
    (ops : List (ReplayOp (n+1))) (checked : verifyReplay (n+1) r budget b₀ b₁ ops = true) :
    Bound (n+1) r (budget+1) := by
  let start : ReplayState (n+1) := ⟨ops, 0, .empty⟩
  cases run : replay b₀ b₁ budget [] (Layers.initial (n+1) r) start with
  | none => simp [verifyReplay, start] at run checked; simp [run] at checked
  | some result =>
    have same : SameMembers (Layers.initial (n+1) r) (images [] r) := by
      have h : images ([] : Network (n+1)) r = Layers.initial (n+1) r := by
        have idRun : Median11.run ([] : Network (n+1)) (α := Bool) = id := rfl
        simp [images, Layers.map, idRun]
      rw [h]
      exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    apply initial_exclusion_sound pos valid
    exact (replay_sound pos valid lower upper budget [] _ same start result
      (by intro id a k h; simp [start, MemoTable.get, memoAddress, MemoTable.getAt] at h) run).2

#print axioms verify_replay_sound

end Median11
