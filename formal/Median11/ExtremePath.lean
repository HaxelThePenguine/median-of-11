import Median11.BalancedRows

namespace Median11

def Hits (g : Gate n) (i : Fin n) : Prop := g.lo = i ∨ g.hi = i

def Untouched (net : Network n) (i : Fin n) : Prop := ∀ g ∈ net, ¬ Hits g i

def Disjoint (a b : Gate n) : Prop := ∀ i, Hits a i → ¬ Hits b i

abbrev Matching (net : Network n) : Prop := net.Pairwise Disjoint

theorem disjoint_symm {a b : Gate n} (h : Disjoint a b) : Disjoint b a :=
  fun i hb ha => h i ha hb

theorem run_untouched [LE α] [DecidableRel (fun (a b : α) => a ≤ b)]
    {net : Network n} {i : Fin n} (h : Untouched net i) (x : Row n α) :
    (run net x).get i = x.get i := by
  induction net generalizing x with
  | nil => rfl
  | cons g net ih =>
    have miss := h g (by simp)
    rw [run, ih (fun a ha => h a (by simp [ha])), step_other _ _ _]
    · exact fun a => miss (Or.inl a)
    · exact fun b => miss (Or.inr b)

def hop (g : Gate n) (i : Fin n) (v : Bool) : Fin n :=
  if g.lo = i ∨ g.hi = i then (if v then g.hi else g.lo) else i

def trace (net : Network n) (i : Fin n) (v : Bool) : Fin n × Nat :=
  match net with
  | [] => (i,0)
  | g :: rest =>
    let tail := trace rest (hop g i v) v
    (tail.1, (if g.lo = i ∨ g.hi = i then 1 else 0) + tail.2)

theorem trace_append (a b : Network n) (i : Fin n) (v : Bool) :
    trace (a ++ b) i v =
      let first := trace a i v
      let second := trace b first.1 v
      (second.1, first.2 + second.2) := by
  induction a generalizing i with
  | nil => simp [trace]
  | cons g a ih => simp [trace, ih, Nat.add_assoc]

theorem trace_untouched {net : Network n} {i : Fin n} (h : Untouched net i) (v : Bool) :
    trace net i v = (i,0) := by
  induction net with
  | nil => rfl
  | cons g net ih =>
    have miss := h g (by simp)
    have tail : Untouched net i := fun a ha => h a (by simp [ha])
    have neg : ¬ (g.lo = i ∨ g.hi = i) := miss
    simp [trace, hop, neg, ih tail]

theorem trace_positive {net : Network n} {i : Fin n} (h : ¬ Untouched net i) (v : Bool) :
    1 ≤ (trace net i v).2 := by
  induction net with
  | nil => exact False.elim (h (by simp [Untouched]))
  | cons g net ih =>
    by_cases hit : Hits g i
    · have yes : g.lo = i ∨ g.hi = i := hit
      simp only [trace, yes, if_true]
      omega
    · have tail : ¬ Untouched net i := by
        intro untouched
        apply h
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hit
        · exact untouched a ha
      simpa [trace, hop, Hits, show ¬(g.lo = i ∨ g.hi = i) from hit] using ih tail

theorem sentinel_hop (f : Frame n) (v : Bool) (g : Gate (n+1)) :
    (nextFrame f v g).forward none = hop g (f.forward none) v := by
  have ne := g.distinct
  unfold nextFrame hop
  by_cases a : g.lo = f.forward none <;> by_cases b : g.hi = f.forward none
  · exact False.elim (ne (a.trans b.symm))
  · cases v <;> simp [a, b, Relabel.trans, swapIso, swapIndex]
  · cases v <;> simp [a, b, Relabel.trans, swapIso, swapIndex]
  · cases v <;> simp [a, b]

theorem encounters_trace (net : Network (n+1)) (f : Frame n) (v : Bool) :
    encounters net f v = (trace net (f.forward none) v).2 := by
  induction net generalizing f with
  | nil => rfl
  | cons g net ih => simp [encounters, trace, ih, sentinel_hop]

theorem uniform_gate (g : Gate n) (x : Row n Bool) (b : Bool)
    (hlo : x.get g.lo = b) (hhi : x.get g.hi = b) : step g x = x := by
  have ord : x.get g.lo ≤ x.get g.hi := by rw [hlo, hhi]; cases b <;> decide
  simp [step, ord]

theorem matching_wires {p s : Network n} {g : Gate n}
    (h : Matching (p ++ g :: s)) (i : Fin n) (hit : Hits g i) :
    Untouched p i ∧ Untouched s i := by
  have a := List.pairwise_append.mp h
  refine ⟨?_, ?_⟩
  · intro j hj
    exact disjoint_symm (a.2.2 j hj g (by simp)) i hit
  · intro j hj
    exact (List.pairwise_cons.mp a.2.1).1 j hj i hit

theorem matching_support {net : Network n} (h : Matching net) (i : Fin n) :
    ∃ support : List (Fin n), support.length ≤ 2 ∧
      ∀ (x : Row n Bool) (v : Bool), (∀ j ∈ support, x.get j = v) →
        (run net x).get i = v := by
  classical
  by_cases miss : Untouched net i
  · refine ⟨[i], by simp, fun x v hx => ?_⟩
    exact (run_untouched miss x).trans (hx i (by simp))
  · have found : ∃ g ∈ net, Hits g i := by
      apply Classical.byContradiction
      intro absent
      exact miss (fun g hg yes => absent ⟨g,hg,yes⟩)
    obtain ⟨g, hg, hit⟩ := found
    obtain ⟨p, s, rfl⟩ := List.append_of_mem hg
    have beforeLo := (matching_wires h g.lo (Or.inl rfl)).1
    have beforeHi := (matching_wires h g.hi (Or.inr rfl)).1
    have after := (matching_wires h i hit).2
    refine ⟨[g.lo,g.hi], by simp, fun x v hx => ?_⟩
    rw [run_append, run, run_untouched after, uniform_gate g _ v]
    · rcases hit with h | h
      · rw [← h, run_untouched beforeLo]; exact hx _ (by simp)
      · rw [← h, run_untouched beforeHi]; exact hx _ (by simp)
    · rw [run_untouched beforeLo]; exact hx _ (by simp)
    · rw [run_untouched beforeHi]; exact hx _ (by simp)

theorem find_reuse (net : Network n) (h : ¬ Matching net) :
    ∃ p g s, net = p ++ g :: s ∧ Matching p ∧
      ∃ earlier ∈ p, ∃ i, Hits earlier i ∧ Hits g i := by
  classical
  suffices general : ∀ (s p : Network n), Matching p → ¬Matching (p++s) →
      ∃ before g after, p++s = before ++ g :: after ∧ Matching before ∧
        ∃ earlier ∈ before, ∃ i, Hits earlier i ∧ Hits g i by
    simpa using general net [] List.Pairwise.nil (by simpa using h)
  intro s
  induction s with
  | nil => intro p yes no; exact False.elim (no (by simpa using yes))
  | cons g s ih =>
    intro p hp hps
    by_cases overlap : ∃ earlier ∈ p, ∃ i, Hits earlier i ∧ Hits g i
    · exact ⟨p,g,s,rfl,hp,overlap⟩
    · have extend : Matching (p++[g]) := by
        apply List.pairwise_append.mpr
        refine ⟨hp, by simp, ?_⟩
        intro a ha b hb i hi hj
        simp only [List.mem_singleton] at hb
        subst b
        exact overlap ⟨a, ha, i, hi, hj⟩
      simpa using ih (p++[g]) extend (by simpa using hps)

theorem matched_extreme (p : Network n) (m : Matching p) (g : Gate n) (hg : g ∈ p)
    (i : Fin n) (hi : Hits g i) :
    ∃ j v, trace p j v = (i,1) := by
  obtain ⟨a,b,rfl⟩ := List.append_of_mem hg
  have aLo := (matching_wires m g.lo (Or.inl rfl)).1
  have bI := (matching_wires m i hi).2
  refine ⟨g.lo, decide (g.hi = i), ?_⟩
  rw [trace_append, trace_untouched aLo]
  change ((trace (g::b) g.lo _).1, 0 + (trace (g::b) g.lo _).2) = _
  have routeTo : hop g g.lo (decide (g.hi = i)) = i := by
    rcases hi with f | f
    · rw [← f]; simp [hop, Ne.symm g.distinct]
    · rw [← f]; simp [hop]
  simp [trace, routeTo, trace_untouched bI]

theorem three_comparisons {net : Network n} {r : Nat} {q : Fin n}
    (pos : 0 < r) (valid : r ≤ n) (sel : SelectsBinary net r q)
    (k : Nat) (layer : k = n-r ∨ k = n-r+1) (ones : 4 ≤ k) (zeros : k+4 ≤ n) :
    ∃ i v, 3 ≤ (trace net i v).2 := by
  have varies (pre : Network n) (wire : Fin n) (support : List (Fin n))
      (small : support.length ≤ 4)
      (controls : ∀ (x : Row n Bool) (b : Bool),
        (∀ j ∈ support, x.get j = b) → (run pre x).get wire = b) :
      ∃ x y : Row n Bool, weight x = k ∧ weight y = k ∧
        (run pre x).get wire ≠ (run pre y).get wire := by
    obtain ⟨x, hx, cx⟩ := uniform_on_layer support k false (by omega) (by omega)
    obtain ⟨y, hy, cy⟩ := uniform_on_layer support k true (by omega) (by omega)
    exact ⟨x,y,hx,hy,by rw [controls x false cx, controls y true cy]; decide⟩
  have nm : ¬ Matching net := by
    intro m
    obtain ⟨s, hs, cs⟩ := matching_support m q
    obtain ⟨x,y,hx,hy,diff⟩ := varies net q s (by omega) cs
    exact diff (congrArg (fun z : Row n Bool => z.get q)
      (boundary_constant pos valid sel x y (hx.trans hy.symm) (hx ▸ layer)))
  obtain ⟨p,g,s,rfl,m,h,hp,i,hi,hg⟩ := find_reuse net nm
  obtain ⟨j,v,first⟩ := matched_extreme p m h hp i hi
  let out := hop g i v
  obtain ⟨a,ha,ca⟩ := matching_support m g.lo
  obtain ⟨b,hb,cb⟩ := matching_support m g.hi
  have control (x : Row n Bool) (bit : Bool)
      (all : ∀ w ∈ a++b, x.get w = bit) :
      (run (p++[g]) x).get out = bit := by
    have lo := ca x bit (fun w h => all w (List.mem_append_left _ h))
    have hi := cb x bit (fun w h => all w (List.mem_append_right _ h))
    rw [run_append, run, run, uniform_gate g _ bit lo hi]
    have hit : g.lo = i ∨ g.hi = i := hg
    cases v <;> simpa [out, hop, hit] using (by first | exact lo | exact hi)
  have len : (a++b).length ≤ 4 := by simp; omega
  obtain ⟨x,y,hx,hy,diff⟩ := varies (p++[g]) out (a++b) len control
  have tail : ¬ Untouched s out := by
    intro untouched
    have eq := congrArg (fun z : Row n Bool => z.get out)
      (boundary_constant pos valid sel x y (hx.trans hy.symm) (hx ▸ layer))
    rw [show p ++ g :: s = (p++[g])++s by simp] at eq
    simp only [run_append, run_untouched untouched] at eq
    apply diff
    simpa only [run_append] using eq
  refine ⟨j,v,?_⟩
  rw [trace_append, first]
  have hit : g.lo = i ∨ g.hi = i := hg
  simp only [trace, hit, if_true]
  have more := trace_positive tail v
  change 3 ≤ 1 + (1 + (trace s out v).2)
  omega

#print axioms three_comparisons

end Median11
