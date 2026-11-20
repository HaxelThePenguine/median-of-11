import Median11.Relabel
import Median11.FiniteLists

namespace Median11

abbrev Frame (n : Nat) := Relabel (Option (Fin n)) (Fin (n+1))

def initialFrame (n : Nat) : Frame n :=
  ⟨fun i => i.elim 0 Fin.succ, Fin.cases none some,
    fun i => by cases i <;> rfl,
    fun i => by refine Fin.cases ?_ (fun _ => ?_) i <;> rfl⟩

theorem frame_some_ne (f : Frame n) (i : Fin n) :
    f.forward (some i) ≠ f.forward none := by
  intro h
  have := f.injective h
  contradiction

def liftRow (f : Frame n) (sentinel : Bool) (x : Row n Bool) : Row (n+1) Bool :=
  Vector.ofFn fun i => (f.backward i).elim sentinel x.get

@[simp] theorem liftRow_at (f : Frame n) (v : Bool) (x : Row n Bool) (i : Option (Fin n)) :
    (liftRow f v x).get (f.forward i) = i.elim v x.get := by
  simp [liftRow, Vector.get, f.left]

def touches (f : Frame n) (g : Gate (n+1)) : Prop :=
  g.lo = f.forward none ∨ g.hi = f.forward none

/-- A sentinel's port is determined by its sign. The frame records the
ordinary labels on the remaining wires even when an ordinary bit is equal
to the sentinel. Moving two equal values still satisfies the simulation. -/
def nextFrame (f : Frame n) (v : Bool) (g : Gate (n+1)) : Frame n :=
  if (if v then g.lo else g.hi) = f.forward none then
    f.trans (swapIso g.lo g.hi)
  else f

private def projectGate : Option (Fin n) → Option (Fin n) → Option (Gate n)
  | some a, some b => if h : a = b then none else some ⟨a,b,h⟩
  | _, _ => none

def omitGate (f : Frame n) (g : Gate (n+1)) : Option (Gate n) :=
  projectGate (f.backward g.lo) (f.backward g.hi)

private theorem swap_lo (g : Gate n) : swapIndex g.lo g.hi g.lo = g.hi := by
  simp [swapIndex]

private theorem swap_hi (g : Gate n) : swapIndex g.lo g.hi g.hi = g.lo := by
  simp [swapIndex, g.distinct]

private theorem lift_swap (f : Frame n) (v : Bool) (x : Row n Bool) (g : Gate (n+1))
    (i : Fin (n+1)) :
    (liftRow (f.trans (swapIso g.lo g.hi)) v x).get i =
      (liftRow f v x).get (swapIndex g.lo g.hi i) := by
  simp [liftRow, Relabel.trans, swapIso, Vector.get]

theorem step_delete (f : Frame n) (v : Bool) (x : Row n Bool) (g : Gate (n+1)) :
    step g (liftRow f v x) =
      liftRow (nextFrame f v g) v ((omitGate f g).elim x (fun h => step h x)) := by
  have lo := f.right g.lo
  have hi := f.right g.hi
  cases ha : f.backward g.lo <;> cases hb : f.backward g.hi
  · simp only [ha, hb] at lo hi
    exact False.elim (g.distinct (lo.symm.trans hi))
  · rename_i b
    simp only [ha, hb] at lo hi
    have hn : g.hi ≠ f.forward none := hi ▸ frame_some_ne f b
    have loBit : (liftRow f v x).get g.lo = v := by
      rw [← lo, liftRow_at]; rfl
    have hiBit : (liftRow f v x).get g.hi = x.get b := by
      rw [← hi, liftRow_at]; rfl
    cases v
    · have ord : (liftRow f false x).get g.lo ≤ (liftRow f false x).get g.hi := by
        rw [loBit, hiBit]; cases x.get b <;> decide
      simp [omitGate, projectGate, ha, hb, nextFrame, hn, step, ord]
    · apply row_ext
      intro i
      have next : nextFrame f true g = f.trans (swapIso g.lo g.hi) := by
        unfold nextFrame
        exact if_pos lo.symm
      have skipped : omitGate f g = none := by simp [omitGate, projectGate, ha]
      rw [next, skipped]
      change (step g (liftRow f true x)).get i =
        (liftRow (f.trans (swapIso g.lo g.hi)) true x).get i
      rw [lift_swap]
      by_cases a : g.lo = i
      · subst i; rw [step_lo, swap_lo, loBit, hiBit]; cases x.get b <;> rfl
      · by_cases c : g.hi = i
        · subst i; rw [step_hi, swap_hi, loBit, hiBit]; cases x.get b <;> rfl
        · rw [step_other _ _ _ a c]; simp [swapIndex, a, c]
  · rename_i a
    simp only [ha, hb] at lo hi
    have hn : g.lo ≠ f.forward none := lo ▸ frame_some_ne f a
    have loBit : (liftRow f v x).get g.lo = x.get a := by
      rw [← lo, liftRow_at]; rfl
    have hiBit : (liftRow f v x).get g.hi = v := by
      rw [← hi, liftRow_at]; rfl
    cases v
    · apply row_ext
      intro i
      have next : nextFrame f false g = f.trans (swapIso g.lo g.hi) := by
        unfold nextFrame
        exact if_pos hi.symm
      have skipped : omitGate f g = none := by simp [omitGate, projectGate, ha, hb]
      rw [next, skipped]
      change (step g (liftRow f false x)).get i =
        (liftRow (f.trans (swapIso g.lo g.hi)) false x).get i
      rw [lift_swap]
      by_cases b : g.lo = i
      · subst i; rw [step_lo, swap_lo, loBit, hiBit]; cases x.get a <;> rfl
      · by_cases c : g.hi = i
        · subst i; rw [step_hi, swap_hi, loBit, hiBit]; cases x.get a <;> rfl
        · rw [step_other _ _ _ b c]; simp [swapIndex, b, c]
    · have ord : (liftRow f true x).get g.lo ≤ (liftRow f true x).get g.hi := by
        rw [loBit, hiBit]; cases x.get a <;> decide
      simp [omitGate, projectGate, ha, hb, nextFrame, hn, step, ord]
  · rename_i a b
    simp only [ha, hb] at lo hi
    have na : g.lo ≠ f.forward none := lo ▸ frame_some_ne f a
    have nb : g.hi ≠ f.forward none := hi ▸ frame_some_ne f b
    have ab : a ≠ b := by intro h; apply g.distinct; rw [← lo, ← hi, h]
    have keep : omitGate f g = some ⟨a,b,ab⟩ := by simp [omitGate, projectGate, ha, hb, ab]
    have same : nextFrame f v g = f := by cases v <;> simp [nextFrame, na, nb]
    rw [keep, same]
    change step g (liftRow f v x) = liftRow f v (step ⟨a,b,ab⟩ x)
    apply row_ext
    intro i
    suffices all : ∀ j : Option (Fin n),
        (step g (liftRow f v x)).get (f.forward j) =
          (liftRow f v (step ⟨a,b,ab⟩ x)).get (f.forward j) by
      simpa only [f.right] using all (f.backward i)
    rintro (_ | j)
    · rw [step_other _ _ _ na nb, liftRow_at, liftRow_at]; rfl
    · by_cases hja : a = j
      · subst j
        rw [lo, step_lo, ← lo, ← hi, liftRow_at, liftRow_at, liftRow_at]
        exact (step_lo ⟨a,b,ab⟩ x).symm
      · by_cases hjb : b = j
        · subst j
          rw [hi, step_hi, ← lo, ← hi, liftRow_at, liftRow_at, liftRow_at]
          exact (step_hi ⟨a,b,ab⟩ x).symm
        · have a' : g.lo ≠ f.forward (some j) := by
            rw [← lo]
            intro h
            exact hja (Option.some.inj (f.injective h))
          have b' : g.hi ≠ f.forward (some j) := by
            rw [← hi]
            intro h
            exact hjb (Option.some.inj (f.injective h))
          rw [step_other _ _ _ a' b', liftRow_at, liftRow_at]
          exact (step_other ⟨a,b,ab⟩ x j hja hjb).symm

def route (net : Network (n+1)) (f : Frame n) (v : Bool) : Frame n :=
  match net with
  | [] => f
  | g :: rest => route rest (nextFrame f v g) v

def reduced (net : Network (n+1)) (f : Frame n) (v : Bool) : Network n :=
  match net with
  | [] => []
  | g :: rest =>
    match omitGate f g with
    | none => reduced rest (nextFrame f v g) v
    | some h => h :: reduced rest (nextFrame f v g) v

def encounters (net : Network (n+1)) (f : Frame n) (v : Bool) : Nat :=
  match net with
  | [] => 0
  | g :: rest =>
    (if g.lo = f.forward none ∨ g.hi = f.forward none then 1 else 0) +
      encounters rest (nextFrame f v g) v

theorem deletion_simulation (net : Network (n+1)) (f : Frame n) (v : Bool) (x : Row n Bool) :
    run net (liftRow f v x) = liftRow (route net f v) v (run (reduced net f v) x) := by
  induction net generalizing f x with
  | nil => rfl
  | cons g net ih =>
    rw [run, step_delete, ih, route, reduced]
    split <;> rename_i e <;> simp [e, run]

theorem omit_iff (f : Frame n) (g : Gate (n+1)) :
    omitGate f g = none ↔ touches f g := by
  have a : f.backward g.lo = none ↔ g.lo = f.forward none := by
    constructor
    · intro h; rw [← h, f.right]
    · intro h; rw [h, f.left]
  have b : f.backward g.hi = none ↔ g.hi = f.forward none := by
    constructor
    · intro h; rw [← h, f.right]
    · intro h; rw [h, f.left]
  unfold touches
  rw [← a, ← b]
  cases ha : f.backward g.lo <;> cases hb : f.backward g.hi <;> simp [omitGate, projectGate, ha, hb]
  intro h
  apply g.distinct
  apply f.symm.injective
  simp [Relabel.symm, ha, hb, h]

theorem deletion_count (net : Network (n+1)) (f : Frame n) (v : Bool) :
    (reduced net f v).length + encounters net f v = net.length := by
  induction net generalizing f with
  | nil => rfl
  | cons g net ih =>
    rw [reduced, encounters, List.length_cons]
    have sum := ih (nextFrame f v g)
    split
    · rename_i e
      have hit := (omit_iff f g).1 e
      simp only [touches] at hit
      simp [hit]
      omega
    · rename_i h e
      have miss : ¬touches f g := by rw [← omit_iff, e]; simp
      simp only [touches] at miss
      simp [miss]
      omega

theorem liftRow_weight (f : Frame n) (v : Bool) (x : Row n Bool) :
    weight (liftRow f v x) = weight x + (if v then 1 else 0) := by
  let actual := List.ofFn f.backward
  let standard : List (Option (Fin n)) := none :: List.ofFn some
  have ap : actual.Nodup := nodup_ofFn (fun _ _ h => f.symm.injective h)
  have sp : standard.Nodup := by
    simp only [standard, List.nodup_cons, List.mem_ofFn]
    exact ⟨by simp, nodup_ofFn (fun _ _ => Option.some.inj)⟩
  have perm := perm_of_nodup_mem ap sp (by
    intro a
    have inActual : a ∈ actual := List.mem_ofFn.mpr ⟨f.forward a, f.left a⟩
    cases a with
    | none => simp [standard, inActual]
    | some b => simp [standard, List.mem_ofFn, inActual])
  have bits := perm.map (fun i : Option (Fin n) => i.elim v x.get)
  have all : (liftRow f v x).toList.Perm (v :: x.toList) := by
    simp only [actual, standard, List.map_cons, map_ofFn, Function.comp, Option.elim] at bits
    have reassemble : List.ofFn x.get = x.toList := by
      apply List.ext_getElem
      · simp
      · intro i a b
        simp [Vector.get]
    rw [← reassemble]
    simpa [liftRow, Vector.toList_ofFn, Function.comp, Option.elim] using bits
  have h := all.count_eq true
  cases v <;> simpa [weight, List.count_cons, Nat.add_comm] using h

theorem deletion_rank (net : Network (n+1)) (f : Frame n) (v : Bool) (q : Fin (n+1))
    (r : Nat) (pos : 0 < r) (valid : r ≤ n+1)
    (keeps : if v then r ≤ n else 1 < r) (h : SelectsBinary net r q) :
    ∃ j : Fin n, SelectsBinary (reduced net f v) (if v then r else r-1) j := by
  let final := route net f v
  cases e : final.backward q with
  | none =>
    have loc : final.forward none = q := by rw [← e, final.right]
    let x : Row n Bool := Vector.replicate n (!v)
    have w : weight x = if v then 0 else n := by cases v <;> simp [x, weight, List.count_replicate]
    have hh := h (liftRow f v x)
    rw [deletion_simulation, ← loc, liftRow_at, liftRow_weight, w] at hh
    cases v
    · have hr : 1 < r := keeps
      have t : n+1 - (n+0) < r := by omega
      simp [t] at hh
      omega
    · have hr : r ≤ n := keeps
      have t : ¬ n+1 - (0+1) < r := by omega
      simp [t] at hh
      omega
  | some j =>
    refine ⟨j, ?_⟩
    have loc : final.forward (some j) = q := by rw [← e, final.right]
    intro x
    have hh := h (liftRow f v x)
    rw [deletion_simulation, ← loc, liftRow_at, liftRow_weight] at hh
    have wb := weight_le x
    change (run (reduced net f v) x).get j = _ at hh
    cases v
    · have hr : 1 < r := keeps
      have eq : (n+1 - weight x < r) ↔ n - weight x < r-1 := by omega
      simpa [eq] using hh
    · have eq : (n+1 - (weight x + 1) < r) ↔ n - weight x < r := by omega
      simpa [eq] using hh

#print axioms deletion_simulation
#print axioms deletion_count

end Median11
