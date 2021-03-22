/-!

Chess piece implementation.

-/

namespace Chess

inductive Color
| white
| black

inductive Piece
| bishop
| king
| knight
| pawn
| queen
| rook

structure ColoredPiece where
  piece : Piece
  color : Color

/-- "Forget" a piece's color. -/
instance : Coe ColoredPiece Piece := ⟨ColoredPiece.piece⟩

@[matchPattern] def whiteBishop : ColoredPiece := ⟨Piece.bishop, Color.white⟩
@[matchPattern] def whiteKing : ColoredPiece := ⟨Piece.king, Color.white⟩
@[matchPattern] def whiteKnight : ColoredPiece := ⟨Piece.knight, Color.white⟩
@[matchPattern] def whitePawn : ColoredPiece := ⟨Piece.pawn, Color.white⟩
@[matchPattern] def whiteQueen : ColoredPiece := ⟨Piece.queen, Color.white⟩
@[matchPattern] def whiteRook : ColoredPiece := ⟨Piece.rook, Color.white⟩

@[matchPattern] def blackBishop : ColoredPiece := ⟨Piece.bishop, Color.black⟩
@[matchPattern] def blackKing : ColoredPiece := ⟨Piece.king, Color.black⟩
@[matchPattern] def blackKnight : ColoredPiece := ⟨Piece.knight, Color.black⟩
@[matchPattern] def blackPawn : ColoredPiece := ⟨Piece.pawn, Color.black⟩
@[matchPattern] def blackQueen : ColoredPiece := ⟨Piece.queen, Color.black⟩
@[matchPattern] def blackRook : ColoredPiece := ⟨Piece.rook, Color.black⟩

notation " ♔ " => Chess.whiteKing
notation " ♕ " => Chess.whiteQueen
notation " ♖ " => Chess.whiteRook
notation " ♗ " => Chess.whiteBishop
notation " ♘ " => Chess.whiteKnight
notation " ♙ " => Chess.whitePawn

notation " ♚ " => Chess.blackKing
notation " ♛ " => Chess.blackQueen
notation " ♜ " => Chess.blackRook
notation " ♝ " => Chess.blackBishop
notation " ♞ " => Chess.blackKnight
notation " ♟︎ " => Chess.blackPawn

notation " __ " => none

instance : Repr ColoredPiece where
  reprPrec
    | ♔, _ => "♔"
    | ♕, _ => "♕"
    | ♖, _ => "♖"
    | ♗, _ => "♗"
    | ♘, _ => "♘"
    | ♙, _ => "♙"
    | ♚, _ => "♚"
    | ♛, _ => "♛"
    | ♜, _ => "♜"
    | ♝, _ => "♝"
    | ♞, _ => "♞"
    | ♟︎, _ => "♟︎"

end Chess
