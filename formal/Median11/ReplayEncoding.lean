import Median11.Replay

namespace Median11

def decodeSwaps (n : Nat) : Nat → Nat → List (Fin (n+1) × Fin (n+1))
  | 0, _ => []
  | m+1, word => (Fin.ofNat' (n+1) (word % 16), Fin.ofNat' (n+1) (word / 16 % 16)) ::
      decodeSwaps n m (word / 256)

/-- Read a bounded block. The opcode word uses two bits per node, least
significant first. Only reference opcodes consume a separate hint word. -/
def decodeOps {n : Nat} : Nat → Nat → Nat → List (ReplayOp (n+1))
  | 0, _, _ => []
  | k+1, codes, hints =>
    let op := codes % 4
    let tail := codes / 4
    if op = 2 then
      .reference (hints % 2^20) (decodeSwaps n (hints / 2^20 % 16) (hints / 2^24)) ::
        decodeOps k tail (hints / 2^112)
    else
      (if op = 0 then .expand else if op = 1 then .cardinality else .frozen) ::
        decodeOps k tail hints

def decodeOpcodes : Nat → Nat → List Nat
  | 0, _ => []
  | k+1, codes => codes % 4 :: decodeOpcodes k (codes / 4)

/-- Optional reference hints do not change the decoded opcode sequence. -/
theorem decodeOps_codes (n count codes hints : Nat) :
    ((decodeOps (n := n) count codes hints).map ReplayOp.code) =
      decodeOpcodes count codes := by
  induction count generalizing codes hints with
  | zero => rfl
  | succ k ih =>
    rw [decodeOps, decodeOpcodes]
    by_cases h₂ : codes % 4 = 2
    · simp [h₂, ReplayOp.code, ih]
    · by_cases h₀ : codes % 4 = 0
      · simp [h₂, h₀, ReplayOp.code, ih]
      · by_cases h₁ : codes % 4 = 1
        · simp [h₂, h₀, h₁, ReplayOp.code, ih]
        · have h₃ : codes % 4 = 3 := by omega
          simp [h₀, h₁, h₂, h₃, ReplayOp.code, ih]

end Median11
