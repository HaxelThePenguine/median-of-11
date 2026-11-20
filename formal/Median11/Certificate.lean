import Median11.RankLayers
import Median11.Cube

namespace Median11

structure Layers (n : Nat) where
  low : List (Row n Bool)
  high : List (Row n Bool)
  deriving DecidableEq

def separates (a : Layers n) (s : Network n) (q : Fin n) : Prop :=
  (∀ x ∈ a.low, (run s x).get q = false) ∧
  (∀ x ∈ a.high, (run s x).get q = true)

def Excludes (a : Layers n) (budget : Nat) : Prop :=
  ∀ (s : Network n) (q : Fin n), s.length ≤ budget → ¬ separates a s q

def Layers.map (f : Row n Bool → Row n Bool) (a : Layers n) : Layers n :=
  ⟨a.low.map f, a.high.map f⟩

def Layers.initial (n r : Nat) : Layers n :=
  ⟨(rows n).filter (fun x => decide (weight x = n-r)),
    (rows n).filter (fun x => decide (weight x = n-r+1))⟩

def images (p : Network n) (r : Nat) : Layers n :=
  (Layers.initial n r).map (run p)

theorem separates_initial_iff (s : Network n) (r : Nat) (q : Fin n) :
    separates (Layers.initial n r) s q ↔ SelectsLayers s r q := by
  simp [separates, Layers.initial, SelectsLayers, rows_complete]

theorem separates_images_iff (p s : Network n) (r : Nat) (q : Fin n) :
    separates (images p r) s q ↔ SelectsLayers (p++s) r q := by
  simp [separates, images, Layers.map, Layers.initial, SelectsLayers, rows_complete]

theorem initial_exclusion_sound {n r budget : Nat} (pos : 0 < r) (valid : r ≤ n)
    (h : Excludes (Layers.initial n r) budget) : Bound n r (budget+1) := by
  intro s q good
  have hs := (separates_initial_iff s r q).2 (selectsLayers_of_binary pos valid good)
  have no : ¬ s.length ≤ budget := fun fits => h s q fits hs
  omega

theorem separates_cons (a : Layers n) (g : Gate n) (s : Network n) (q : Fin n) :
    separates a (g::s) q ↔ separates (a.map (step g)) s q := by
  simp [separates, Layers.map, run]

def isSeparator (a : Layers n) (q : Fin n) : Bool :=
  a.low.all (fun x => !(x.get q)) && a.high.all (fun x => x.get q)

theorem isSeparator_iff (a : Layers n) (q : Fin n) :
    isSeparator a q = true ↔ separates a [] q := by
  simp [isSeparator, separates, run, List.all_eq_true]

def immediateFailure (a : Layers n) : Bool :=
  (wires n).all (fun q => !(isSeparator a q))

theorem no_empty (a : Layers n) (h : immediateFailure a = true) :
    ∀ q, ¬ separates a [] q := by
  intro q hq
  have closed := List.all_eq_true.mp h q (mem_wires q)
  simp [(isSeparator_iff a q).mpr hq] at closed

def allGates (n : Nat) : List (Gate n) :=
  (wires n).flatMap fun a =>
    (wires n).filterMap fun b => if h : a = b then none else some ⟨a,b,h⟩

theorem mem_allGates (g : Gate n) : g ∈ allGates n := by
  apply List.mem_flatMap.mpr
  exact ⟨g.lo, mem_wires _, List.mem_filterMap.mpr ⟨g.hi, mem_wires _, by simp [g.distinct]⟩⟩

/-- Reference checker that explores all ordered gates. It is intended for
small-width tests and as a soundness baseline for pruning rules. -/
def verifyExhaustive (a : Layers n) : Nat → Bool
  | 0 => immediateFailure a
  | k+1 => immediateFailure a &&
      (allGates n).all (fun g => verifyExhaustive (a.map (step g)) k)

theorem verify_exhaustive_sound (a : Layers n) (budget : Nat)
    (h : verifyExhaustive a budget = true) : Excludes a budget := by
  induction budget generalizing a with
  | zero =>
    intro s q fits
    cases s with
    | nil => exact no_empty a h q
    | cons g s => simp at fits
  | succ k ih =>
    have hh : immediateFailure a = true ∧
        (allGates n).all (fun g => verifyExhaustive (a.map (step g)) k) = true := by
      simpa only [verifyExhaustive, Bool.and_eq_true] using h
    intro s q fits hs
    cases s with
    | nil => exact no_empty a hh.1 q hs
    | cons g s =>
      have checked := List.all_eq_true.mp hh.2 g (mem_allGates g)
      exact ih _ checked s q (by simpa using fits) ((separates_cons a g s q).1 hs)

theorem three_input_lower : Bound 3 2 3 :=
  initial_exclusion_sound (by decide) (by decide)
    (verify_exhaustive_sound (Layers.initial 3 2) 2 (by decide +kernel))

-- A small countermodel to an unqualified deletion recurrence.
theorem median_three_not_balanced (k : Nat) : ¬ (4 ≤ k ∧ k+4 ≤ 3) := by omega

#print axioms verify_exhaustive_sound
#print axioms three_input_lower

end Median11
