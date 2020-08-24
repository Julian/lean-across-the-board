/-!

Chess piece implementation.

-/

namespace chess

inductive color
| white : color
| black : color

inductive pieces
| bishop
| king
| knight
| pawn
| queen
| rook

namespace pieces

  notation ` ♔ ` := king
  notation ` ♕ ` := queen
  notation ` ♖ ` := rook
  notation ` ♗ ` := bishop
  notation ` ♘ ` := knight
  notation ` ♙ ` := pawn

end pieces

end chess
