import Median11.Pruning

namespace Median11

def SameMembers (a b : Layers n) : Prop :=
  (∀ x, x ∈ a.low ↔ x ∈ b.low) ∧ (∀ x, x ∈ a.high ↔ x ∈ b.high)

theorem SameMembers.symm {a b : Layers n} (h : SameMembers a b) : SameMembers b a :=
  ⟨fun x => (h.1 x).symm, fun x => (h.2 x).symm⟩

theorem SameMembers.trans {a b c : Layers n} (h : SameMembers a b) (j : SameMembers b c) :
    SameMembers a c :=
  ⟨fun x => (h.1 x).trans (j.1 x), fun x => (h.2 x).trans (j.2 x)⟩

theorem SameMembers.maps {a b : Layers n} (h : SameMembers a b)
    (f : Row n Bool → Row n Bool) : SameMembers (a.map f) (b.map f) := by
  constructor
  · intro x; simp [Layers.map,h.1]
  · intro x; simp [Layers.map,h.2]

theorem SameMembers.separation {a b : Layers n} (h : SameMembers a b)
    (s : Network n) (q : Fin n) : separates a s q ↔ separates b s q := by
  simp [separates, h.1, h.2]

theorem SameMembers.exclusion {a b : Layers n} (h : SameMembers a b)
    (k : Nat) : Excludes a k ↔ Excludes b k := by
  simp [Excludes, h.separation]

theorem image_descend (p : Network n) (r : Nat) (g : Gate n) :
    images (p++[g]) r = (images p r).map (step g) := by
  simp [images, Layers.map, List.map_map, run, Function.comp_def]

theorem map_eq_on (a : Layers n) (f g : Row n Bool → Row n Bool)
    (h : ∀ x ∈ a.low ++ a.high, f x = g x) : a.map f = a.map g := by
  unfold Layers.map
  congr 1
  · exact List.map_congr_left (fun x hx => h x (List.mem_append_left _ hx))
  · exact List.map_congr_left (fun x hx => h x (List.mem_append_right _ hx))

def keepsBoth (a : Layers n) (g : Gate n) : Bool :=
  let l := a.low ++ a.high
  l.any (fun x => x.get g.lo && !(x.get g.hi)) &&
    l.any (fun x => !(x.get g.lo) && x.get g.hi)

theorem keepsBoth_iff (a : Layers n) (g : Gate n) :
    keepsBoth a g = true ↔
      (∃ x ∈ a.low ++ a.high, x.get g.lo = true ∧ x.get g.hi = false) ∧
      (∃ x ∈ a.low ++ a.high, x.get g.lo = false ∧ x.get g.hi = true) := by
  have flip (v : Bool) : ((!v) = true) ↔ v = false := by cases v <;> decide
  simp only [keepsBoth, Bool.and_eq_true, List.any_eq_true, flip]

theorem keepsBoth_dual (a : Layers n) (g : Gate n) :
    keepsBoth a (dualGate g) = keepsBoth a g := by
  apply Bool.eq_iff_iff.mpr
  simp only [keepsBoth_iff, dualGate]
  constructor <;> rintro ⟨⟨x,hx,a,b⟩,⟨y,hy,c,d⟩⟩ <;> exact ⟨⟨y,hy,d,c⟩,⟨x,hx,b,a⟩⟩

theorem exchange_cancel (a : Layers n) (g : Gate n) :
    (a.map (exchange g)).map (exchange g) = a := by
  cases a
  simp [Layers.map,List.map_map,Function.comp_def,exchange_twice]

theorem exchange_separation_back (a : Layers n) (g : Gate n) (s : Network n) (q : Fin n)
    (h : separates (a.map (exchange g)) s q) :
    separates a (s.map (renameGate (swapIso g.lo g.hi))) (swapIndex g.lo g.hi q) := by
  have hh := rename_separates (swapIso g.lo g.hi) (a.map (exchange g)) s q h
  change separates ((a.map (exchange g)).map (exchange g)) _ _ at hh
  rw [exchange_cancel] at hh
  exact hh

theorem redundant_first (a : Layers n) (g : Gate n) (s : Network n) (q : Fin n)
    (redundant : keepsBoth a g = false) (h : separates a (g::s) q) :
    ∃ t j, t.length = s.length ∧ separates a t j := by
  have cases' := fixed_if_no_discord g a (by
    apply Classical.not_and_iff_not_or_not.mp
    intro yes
    have check := (keepsBoth_iff a g).mpr yes
    rw [redundant] at check
    contradiction)
  have after := (separates_cons a g s q).mp h
  rcases cases' with h | h
  · have eq := map_eq_on a (step g) id h
    rw [eq] at after
    exact ⟨s,q,rfl,by simpa [Layers.map] using after⟩
  · rw [map_eq_on a (step g) (exchange g) h] at after
    exact ⟨_,_,by simp,exchange_separation_back a g s q after⟩

theorem expand_sound (a : Layers n) (k : Nat)
    (empty : immediateFailure a = true)
    (children : ∀ g : Gate n, g.lo < g.hi → keepsBoth a g = true →
      Excludes (a.map (step g)) k) : Excludes a (k+1) := by
  suffices enough : ∀ d (s : Network n), s.length = d → d ≤ k+1 →
      ∀ q, ¬ separates a s q from fun s q fit => enough s.length s rfl fit q
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro s len fit q h
    cases s with
    | nil => exact no_empty a empty q h
    | cons g s =>
      cases useful : keepsBoth a g
      · obtain ⟨t,j,lt,good⟩ := redundant_first a g s q useful h
        have shorter : t.length < d := by simp at len; omega
        exact ih t.length shorter t rfl (by omega) j good
      · have lenS : s.length ≤ k := by simp at len; omega
        by_cases std : g.lo < g.hi
        · exact children g std useful s q lenS ((separates_cons a g s q).mp h)
        · have std' : (dualGate g).lo < (dualGate g).hi := by
            change g.hi.val < g.lo.val
            have ne : g.lo.val ≠ g.hi.val := fun e => g.distinct (Fin.ext e)
            change ¬g.lo.val < g.hi.val at std
            omega
          have canonical : keepsBoth a (dualGate g) = true := by rwa [keepsBoth_dual]
          have back (x : Row n Bool) :
              step g x = exchange (dualGate g) (step (dualGate g) x) := by
            simpa [dualGate] using reverse_orientation (dualGate g) x
          have sep := (separates_cons a g s q).mp h
          have eq := map_eq_on a (step g) (exchange (dualGate g) ∘ step (dualGate g))
            (fun x _ => back x)
          rw [eq] at sep
          have target := exchange_separation_back (a.map (step (dualGate g))) (dualGate g)
            s q (by simpa [Layers.map, List.map_map,Function.comp_def] using sep)
          exact children (dualGate g) std' canonical _ _ (by simpa using lenS) target

#print axioms expand_sound

end Median11
