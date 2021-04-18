variable (P : Type) [BEq P]

structure Board where
  contents : Array (Array P)
  contiguous (rank : Nat) : contents[rank].size ≠ 0
  nontrivial : contents ≠ #[]
  rectangular : ∃ n, ∀ rank, contents[rank].size = n

namespace Board

variable (B : Board P)

def width := B.contents[0].size
def height := B.contents.size

end Board
