import Median11.Certificate

namespace Median11

def exchange (g : Gate n) (x : Row n Bool) : Row n Bool :=
  renameRow (swapIso g.lo g.hi) x

theorem exchange_twice (g : Gate n) (x : Row n Bool) : exchange g (exchange g x) = x := by
  apply row_ext
  intro i
  simp [exchange, swapIso, swapIndex_swapIndex]

theorem step_or_exchange (g : Gate n) (x : Row n Bool) :
    step g x = x ∨ step g x = exchange g x := by
  by_cases h : x.get g.lo ≤ x.get g.hi
  · exact Or.inl (by simp [step,h])
  · right
    apply row_ext
    intro i
    rw [step_get, if_neg h]
    by_cases a : g.lo = i
    · subst i
      simp [exchange, swapIso, swapIndex, Ne.symm g.distinct]
    · by_cases b : g.hi = i
      · subst i
        simp [exchange, swapIso, swapIndex, g.distinct]
      · simp [exchange, swapIso, swapIndex, a,b]

def preimages (s : Network n) (y : Row n Bool) : List (Row n Bool) :=
  match s with
  | [] => [y]
  | g :: rest => (preimages rest y).flatMap (fun x => [x, exchange g x])

theorem mem_preimages (s : Network n) (x : Row n Bool) :
    x ∈ preimages s (run s x) := by
  induction s generalizing x with
  | nil => simp [preimages, run]
  | cons g s ih =>
    apply List.mem_flatMap.mpr
    refine ⟨step g x, ih (step g x), ?_⟩
    rcases step_or_exchange g x with e | e
    · simp [e]
    · simp [e, exchange_twice]

theorem length_preimages (s : Network n) (y : Row n Bool) :
    (preimages s y).length = 2 ^ s.length := by
  have len (a : List (Row n Bool)) (g : Gate n) :
      (a.flatMap fun x => [x, exchange g x]).length = 2 * a.length := by
    induction a with
    | nil => rfl
    | cons x a ih => simp [ih]; omega
  induction s with
  | nil => rfl
  | cons g s ih =>
    rw [preimages, len, ih, List.length_cons, Nat.pow_succ, Nat.mul_comm]

theorem cardinality_bound (s : Network n) (states : List (Row n Bool)) (nd : states.Nodup)
    (y : Row n Bool) (constant : ∀ x ∈ states, run s x = y) : states.length ≤ 2 ^ s.length := by
  rw [← length_preimages s y]
  apply length_le_of_nodup_subset nd
  intro x hx
  rw [← constant x hx]
  exact mem_preimages s x

def rootBudget (p : Network n) (k : Nat) : Nat := p.length + k

theorem suffix_selects {p s : Network n} {r : Nat} {q : Fin n}
    (pos : 0 < r) (valid : r ≤ n) (h : separates (images p r) s q) :
    SelectsBinary (p++s) r q :=
  selectsBinary_of_layers pos valid ((separates_images_iff p s r q).1 h)

theorem cardinality_prune (p : Network n) (r k : Nat)
    (pos : 0 < r) (valid : r ≤ n) (states : List (Row n Bool)) (nd : states.Nodup)
    (side : Bool) (sub : states ⊆ if side then (images p r).high else (images p r).low)
    (tooMany : 2^k < states.length) : Excludes (images p r) k := by
  intro s q fits hs
  let good := suffix_selects pos valid hs
  let w := if side then n-r+1 else n-r
  have hw : w = (if side then n-r+1 else n-r) := rfl
  have source (x : Row n Bool) (hx : x ∈ states) :
      ∃ z : Row n Bool, weight z = w ∧ run p z = x := by
    have incl := sub hx
    cases side <;> simp [images, Layers.initial, Layers.map, rows_complete, hw] at *
    · obtain ⟨z, hz,e⟩ := incl
      exact ⟨z,hz,e⟩
    · obtain ⟨z, hz,e⟩ := incl
      exact ⟨z,hz,e⟩
  have distinctPair : ∀ x ∈ states, ∀ y ∈ states, run s x = run s y := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := source x hx
    obtain ⟨v, hv, rfl⟩ := source y hy
    have boundary : weight u = n-r ∨ weight u = n-r+1 := by rw [hu,hw]; cases side <;> simp
    simpa only [run_append] using boundary_constant pos valid good u v (hu.trans hv.symm) boundary
  cases e : states with
  | nil => simp [e] at tooMany
  | cons x xs =>
    have bound := cardinality_bound s states nd (run s x) (fun y hy =>
      distinctPair y hy x (by simp [e]))
    have power := Nat.pow_le_pow_right (show 0 < 2 by decide) fits
    omega

def IncidenceBound (n r : Nat) (v : Bool) (b : Nat) : Prop :=
  b = 0 ∨ ((if v then r ≤ n else 1 < r) ∧ Bound n (if v then r else r-1) b)

theorem cap_bound {n r budget b : Nat} {net : Network (n+1)} {i q : Fin (n+1)}
    (pos : 0 < r) (valid : r ≤ n+1) (sel : SelectsBinary net r q) (v : Bool)
    (bound : IncidenceBound n r v b) (fits : net.length ≤ budget) :
    (trace net i v).2 + b ≤ budget := by
  rcases bound with zero | ⟨keeps,h⟩
  · subst b
    have sum := deletion_count net (frameAt i) v
    rw [encounters_trace, frameAt_sentinel] at sum
    omega
  · exact deletion_size_bound pos valid sel v keeps b h fits

theorem path_prune (p : Network (n+1)) (r k b : Nat) (i : Fin (n+1)) (v : Bool)
    (pos : 0 < r) (valid : r ≤ n+1) (bound : IncidenceBound n r v b)
    (over : rootBudget p k < (trace p i v).2 + b) : Excludes (images p r) k := by
  intro s q fits sep
  have cap := cap_bound (i := i) pos valid (suffix_selects pos valid sep) v bound
    (budget := rootBudget p k) (by simp [rootBudget]; omega)
  rw [trace_append] at cap
  dsimp only at cap
  omega

theorem frozen_prune (p : Network (n+1)) (r k b : Nat) (i : Fin (n+1)) (v : Bool)
    (pos : 0 < r) (valid : r ≤ n+1) (bound : IncidenceBound n r v b)
    (exhausted : (trace p i v).2 + b = rootBudget p k)
    (x y : Row (n+1) Bool) (same : weight x = weight y)
    (layer : weight x = (n+1)-r ∨ weight x = (n+1)-r+1)
    (vary : (run p x).get (trace p i v).1 ≠ (run p y).get (trace p i v).1) :
    Excludes (images p r) k := by
  intro s q fits sep
  have successful := suffix_selects pos valid sep
  have cap := cap_bound (i := i) pos valid successful v bound
    (budget := rootBudget p k) (by simp [rootBudget]; omega)
  rw [trace_append] at cap
  dsimp only at cap
  have untouched : Untouched s (trace p i v).1 := by
    apply Classical.byContradiction
    intro hit
    have positive := trace_positive hit v
    omega
  apply vary
  have sameOut := congrArg (fun z : Row (n+1) Bool => z.get (trace p i v).1)
    (boundary_constant pos valid successful x y same layer)
  simpa only [run_append, run_untouched untouched] using sameOut

theorem rename_separates (e : Relabel (Fin n) (Fin n)) (a : Layers n) (s : Network n) (q : Fin n)
    (h : separates a s q) :
    separates (a.map (renameRow e)) (s.map (renameGate e)) (e.forward q) := by
  constructor
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    simpa [rename_run, e.left] using h.1 x hx
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    simpa [rename_run, e.left] using h.2 x hx

/-- Completed exclusions refer to the residual problem alone. Membership in
each image may be tested independently after applying the SAME relabelling
to both images. No hypothesis relates the traces of the incoming prefixes. -/
theorem memo_reuse (old current : Layers n) (e : Relabel (Fin n) (Fin n))
    (k saved : Nat) (enough : k ≤ saved) (done : Excludes old saved)
    (low : old.low ⊆ (current.map (renameRow e)).low)
    (high : old.high ⊆ (current.map (renameRow e)).high) : Excludes current k := by
  intro s q fits hs
  have transported := rename_separates e current s q hs
  exact done (s.map (renameGate e)) (e.forward q) (by simpa using Nat.le_trans fits enough)
    ⟨fun x mem => transported.1 x (low mem), fun x mem => transported.2 x (high mem)⟩

theorem reverse_orientation (g : Gate n) (x : Row n Bool) :
    step (dualGate g) x = exchange g (step g x) := by
  apply row_ext
  intro i
  simp only [exchange, renameRow_get, swapIso]
  by_cases a : g.lo = i
  · subst i
    change (step (dualGate g) x).get (dualGate g).hi = _
    rw [show swapIndex g.lo g.hi g.lo = g.hi by simp [swapIndex], step_hi, step_hi]
    exact Bool.or_comm _ _
  · by_cases b : g.hi = i
    · subst i
      change (step (dualGate g) x).get (dualGate g).lo = _
      rw [show swapIndex g.lo g.hi g.hi = g.lo by simp [swapIndex,g.distinct], step_lo, step_lo]
      exact Bool.and_comm _ _
    · rw [show swapIndex g.lo g.hi i = i by simp [swapIndex,a,b]]
      rw [step_other _ _ _ b a, step_other _ _ _ a b]

theorem fixed_if_no_discord (g : Gate n) (a : Layers n)
    (h : ¬ (∃ x ∈ a.low ++ a.high, x.get g.lo = true ∧ x.get g.hi = false) ∨
         ¬ (∃ x ∈ a.low ++ a.high, x.get g.lo = false ∧ x.get g.hi = true)) :
    (∀ x ∈ a.low ++ a.high, step g x = x) ∨
      (∀ x ∈ a.low ++ a.high, step g x = exchange g x) := by
  rcases h with h | h
  · left
    intro x hx
    have ordered : x.get g.lo ≤ x.get g.hi := by
      cases l : x.get g.lo <;> cases r : x.get g.hi
      · decide
      · decide
      · exact False.elim (h ⟨x,hx,l,r⟩)
      · decide
    simp [step,ordered]
  · right
    intro x hx
    rcases step_or_exchange g x with same | swapped
    · apply row_ext
      intro i
      rw [same]
      simp only [exchange,renameRow_get,swapIso]
      have eq : x.get g.lo = x.get g.hi := by
        cases l : x.get g.lo <;> cases r : x.get g.hi
        · rfl
        · exact False.elim (h ⟨x,hx,l,r⟩)
        · have out := congrArg (fun y : Row n Bool => y.get g.lo) same
          simp [step_lo, l, r] at out
        · rfl
      by_cases a : g.lo = i
      · subst i; simpa [swapIndex] using eq
      · by_cases b : g.hi = i
        · subst i; simpa [swapIndex,g.distinct] using eq.symm
        · simp [swapIndex,a,b]
    · exact swapped

#print axioms cardinality_prune
#print axioms path_prune
#print axioms frozen_prune
#print axioms memo_reuse
#print axioms reverse_orientation
#print axioms fixed_if_no_discord

end Median11
