=============
API Reference
=============

``chess.board``
===============

Definitions and theorems about a chess board
--------------------------------------------

Summary
~~~~~~~

The chess board is a set of indexed ``piece``\ s on a ``playfield``. A
board is valid, and can only be constructed, if all the pieces are
present on the board, and no two distinct (by index) pieces share the
same position on the board.

Main definitions
~~~~~~~~~~~~~~~~

1. The ``board`` itself, which requires an indexed vector of
   ``piece``\ s, and the ``playfield`` which will serve as the where
   those pieces are placed. Additionally, all pieces must be present on
   the playfield, and no two distinct (by index) pieces can share a
   position on the playfield.

2. A way to reduce the board, following the indices to just the pieces.
   This allows comparison of boards that are equivalent modulo
   permutation of indices that point to equivalent pieces.

Implementation notes
~~~~~~~~~~~~~~~~~~~~

1. A ``board`` requires finite dimensions for the ``playfield``, finite
   indices, and a finite piece set. Ideally, this should be generizable
   to potentially infinite types. However, since ``playfield``\ s are
   usually provided by ``matrix``, which is restricted to finite
   dimensions, it is easiest to define the board as finite.
   Additionally, to perform position math, more constraints on the
   dimension types will likely be necessary, like
   ``decidable_linear_order``.

2. The requirement of ``decidable_eq`` on the dimensions and index
   allows use of ``dec_trivial`` to automatically infer proofs for board
   constraint propositions. That means instantiation of a ``board`` will
   not require explicit proofs for the propositions.

3. The board does not define what are valid position comparisons – the
   geometry of the space is not defined other than what the
   ``playfield`` provides.

4. Currently, all pieces are constrained by the definition of a board to
   be present on the playfield. That means no capturing moves and no
   piece introduction moves are possible.



.. theorem:: chess.board

    A board is axiomatized as a set of indexable (ergo distinguishable)
    pieces which are placed on distinct squares of a ``playfield``.


.. theorem:: board_repr

    A board’s representation is just the concatentation of the
    representations of the ``pieces`` and ``contents`` via
    ``board_repr_pieces`` and ``board_repr_contents``, respectively, with
    newlines inserted for clarity.


.. theorem:: board_repr_contents

    A board’s ``contents`` can be represented by reducing the board
    according to the indexed vector at ``pieces``, and placing the pieces on
    the ``playfield``. We override the default ``option K`` representation
    by using ``option_wrap``, and supply an underscore to represent empty
    positions.


.. theorem:: board_repr_instance




.. theorem:: board_repr_pieces

    A board’s ``pieces`` is a “vector”, so ``vec_repr`` is used to represent
    it.


.. theorem:: contents_is_some_injective




.. theorem:: has_equiv




.. theorem:: has_mem




.. theorem:: height

    The height of the board.


.. theorem:: reduce

    The state of the board, where pieces of the same type are equivalent


.. theorem:: width

    The width of the board.


``chess.move``
==============


.. theorem:: chess.board.has_sequence_len

    Assert the existence of a ``sequence`` of length ``o`` from a
    ``start_board`` to a given end board.


.. theorem:: chess.board.has_sequence_to

    Assert the existence of a ``sequence`` from a ``start_board`` to a given
    end board.


.. theorem:: chess.move

    A move is a (distinct) start and end square whose start square is
    occupied and whose end square is not.

    (Captures are not implemented yet.)


.. theorem:: after_occupied_end

    End squares are occupied after a move.


.. theorem:: after_unoccupied_start

    Start squares are unoccupied after a move.


.. theorem:: before_after_same

    Other squares are unchanged after a move.


.. theorem:: before_occupied_start

    Start squares are occupied before a move.


.. theorem:: before_unoccupied_end

    End squares are unoccupied before a move.


.. theorem:: no_superimpose

    Pieces do not become superimposed after a move.


.. theorem:: perform_move

    A valid ``move`` on a ``board`` retains a valid board state.


.. theorem:: piece

    The piece that is being moved.


.. theorem:: scan_contents




.. theorem:: sequence

    A move ``sequence`` represents a sequential set of moves from a starting
    ``board``.


.. theorem:: sequence.all_occupied_start




.. theorem:: sequence.all_unoccupied_end




.. theorem:: sequence.boards

    The board which results from applying the first ``ix₀ + 1`` ``move``\ s
    in the ``sequence``.


.. theorem:: sequence.contents_at

    Shorthand for referring to the contents at a sequence index
    ``ixₒ : fin (o + 1)``.


.. theorem:: sequence.contents_at_def

    Shorthand for referring to the contents at a sequence index
    ``ixₒ : fin (o + 1)``.


.. theorem:: sequence.end_board

    The board which results from applying all ``move``\ s in the
    ``sequence``.


.. theorem:: sequence.fixes_unmentioned_squares

    Any square which is not the ``start_square`` or ``end_square`` of any
    ``move`` in the ``sequence`` is fixed across all ``move``\ s
    (i.e. contains the same piece or remains empty).


.. theorem:: sequence.moves

    The ``ix₀``\ ’th ``move`` in the ``sequence``.


.. theorem:: sequence.no_superimpose

    Pieces do not become superimposed after any ``move`` in a ``sequence``.


.. theorem:: sequence.retains_injectivity




.. theorem:: sequence.retains_pieces

    Pieces do not disappear after any ``move_piece`` in a ``sequence``.


.. theorem:: sequence.sequence_step

    Any ``contents_at`` a step in the ``sequence`` is the result of
    performing a ``move_piece`` using the ``sequence.elements`` at that
    step.


.. theorem:: sequence.sequence_zero

    The first contents in a ``scan_contents`` ``sequence`` is of the
    ``start_board``.


.. theorem:: start_square_is_some




``chess.piece``
===============

Chess piece implementation.



.. theorem:: chess.black_bishop




.. theorem:: chess.black_king




.. theorem:: chess.black_knight




.. theorem:: chess.black_pawn




.. theorem:: chess.black_queen




.. theorem:: chess.black_rook




.. theorem:: chess.color




.. theorem:: chess.color.decidable_eq




.. theorem:: chess.colored_pieces




.. theorem:: chess.colored_pieces.decidable_eq




.. theorem:: chess.has_repr




.. theorem:: chess.piece_repr




.. theorem:: chess.pieces




.. theorem:: chess.pieces.decidable_eq




.. theorem:: chess.white_bishop




.. theorem:: chess.white_king




.. theorem:: chess.white_knight




.. theorem:: chess.white_pawn




.. theorem:: chess.white_queen




.. theorem:: chess.white_rook




``chess.playfield``
===================

Definitions and theorems about the chess board field
----------------------------------------------------

Summary
~~~~~~~

The field on which chess pieces are placed is a 2D plane, where each
position corresponds to a piece index. This is because we think of
defining pieces and moves, usually, by indicating which position they
are at, and which position they are moved to.

Main definitions
~~~~~~~~~~~~~~~~

1. The playfield itself (``playfield``)
2. Conversion from a ``matrix`` of (possibly) occupied spaces to a
   ``playfield``
3. Moving a piece by switching the indices at two specified positions
   using ``move_piece``
4. Making a sequence of moves at once using ``move_sequence``

Implementation details
~~~~~~~~~~~~~~~~~~~~~~

1. The ``playfield`` type itself has no requirements to be finite in any
   dimension, or that the indices used are finite. We represent the
   actual index wrapped by ``option``, such that the empty square can be
   an ``option.none``. The playfield definition wraps the two types used
   to define the dimensions of the board into a pair.

2. In the current implementation, the way to construct a ``playfield``
   is to provide a matrix. This limits the ``playfield`` to a finite 2D
   plane. Another possible implementation is of a “sparse matrix”, where
   for each index, we can look up where the piece is. This now allows
   for an infinite playfield, but still complicates using infinite
   pieces. For now, the closely-tied ``matrix`` definition makes
   ``playfield`` a light type wrapper on top of ``matrix``, i.e. a
   function of two variables.

3. Currently, ``move_piece`` just swaps the (potentially absent) indices
   at two positions. This is done by using an ``equiv.swap`` as an
   updating function. For now, this means that moves that use
   ``move_piece`` are non-capturing. Additionally, no math or other
   requirements on the positions or their contents is required. This
   means that ``move_piece`` supports a move from a position to itself.
   A separate ``move`` is defined in ``chess.move`` that has more
   chess-like rule constraints.

4. Index presence on the board is not limited to have each index on
   at-most-one position. Preventing duplication of indices is not
   enforced by the ``playfield`` itself. However, any given position can
   hold at-most-one index on it. The actual chess-like rule constraints
   are in ``chess.board``.

5. Sequences of moves are implemented on top of ``move``\ s, rather than
   vice versa (``move``\ s being defined as sequences of length one).
   This *probably* causes a bit of duplication, which may warrant
   flipping things later.



.. theorem:: matrix_to_playfield

    A conversion function to turn a bare ``matrix`` into a ``playfield``. A
    ``matrix`` requires the dimensions to be finite.

    An example empty 3 × 3 playfield for 4 pieces could be generated by:

    .. code:: lean

       matrix_to_playfield ((
         ![![none, none, none],
           ![none, none, none],
           ![none, none, none]] : matrix (fin 3) (fin 3) (option (fin 4))

    where the positions are 0-indexed, with the origin in the top-left,
    first dimension for the row, and second dimension for the column (0,0)
    (0,1) (0,2) (1,0) (1,1) (1,2) (2,0) (2,1) (2,2)


.. theorem:: playfield

    A ``playfield m n ι`` represents a ``matrix (m × n) option ι``, which is
    a model for a ``m × n`` shaped game board where not every square is
    occupied.


.. theorem:: playfield.has_mem

    A piece, identified by an index, is on the board, if there is any
    position such that the index at that position is the one we’re inquiring
    about. Providing a ``has_mem`` instance allows using ``ix ∈ pf`` for
    ``ix : ι, pf : playfield m n ι``. This definition does not preclude
    duplicated indices on the playfield. See “Implementation details”.


.. theorem:: playfield.inhabited

    A ``playfield`` is by default ``inhabited`` by empty squares everywhere.


.. theorem:: playfield.move_piece

    Move an (optional) index from ``start_square`` to ``end_square`` on a
    ``playfield``, swapping the indices at those squares.

    Does not assume anything about occupancy.


.. theorem:: playfield.move_piece_def

    Equivalent to to ``move_piece``, but useful for ``rewrite`` ing.


.. theorem:: playfield.move_piece_diff

    Moving an (optional) index retains whatever (optional) indices that were
    at other squares.


.. theorem:: playfield.move_piece_end

    Moving an (optional) index that was at ``end_square`` places it at
    ``start_square``


.. theorem:: playfield.move_piece_start

    Moving an (optional) index that was at ``start_square`` places it at
    ``end_square``


.. theorem:: playfield.move_sequence

    Make a sequence of ``move``\ s all at once.


.. theorem:: playfield.move_sequence_def

    Equivalent to to ``move_sequence``, but useful for ``rewrite`` ing.


.. theorem:: playfield.move_sequence_diff

    Throughout a sequence, moving an (optional) index retains whatever
    (optional) indices that were at other squares on the next board.


.. theorem:: playfield.move_sequence_end

    Throughout a sequence, moving an (optional) index that was at
    ``end_square`` places it at ``start_square`` on the next board.


.. theorem:: playfield.move_sequence_start

    Throughout a sequence, moving an (optional) index that was at
    ``start_square`` places it at ``end_square`` on the next board.


.. theorem:: playfield.playfield_repr_instance




.. theorem:: playfield.retains_injectivity

    Each index that is present on the playfield and appears only once,
    appears only once after a ``move_piece``.


.. theorem:: playfield.retains_pieces

    Pieces do not disappear after a ``move_piece``.


.. theorem:: playfield.some_injective

    A ``playfield`` on which every index that appears, appears only once.


``chess.utils``
===============

Helpers that don’t currently fit elsewhere…



.. theorem:: matrix_repr

    For a ``matrix`` ``X^(m' × n')`` where the ``X`` has a ``has_repr``
    instance itself, we can provide a ``has_repr`` for the matrix, using
    ``vec_repr`` for each of the rows of the matrix. This definition is used
    for displaying the playfield, when it is defined via a ``matrix``,
    likely through notation.


.. theorem:: matrix_repr_instance




.. theorem:: option_wrap

    Construct an ``option_wrapper`` term from a provided ``option X`` and
    the ``string`` that will override the ``has_repr.repr`` for ``none``.


.. theorem:: option_wrapper

    An auxiliary wrapper for ``option X`` that allows for overriding the
    ``has_repr`` instance for ``option``, and rather, output just the value
    in the ``some`` and a custom provided ``string`` for ``none``.


.. theorem:: vec_repr

    For a “vector” ``X^n'`` represented by the type
    ``Π n' : ℕ, fin n' → X``, where the ``X`` has a ``has_repr`` instance
    itself, we can provide a ``has_repr`` for the “vector”. This definition
    is used for displaying rows of the playfield, when it is defined via a
    ``matrix``, likely through notation.


.. theorem:: vec_repr_instance




.. theorem:: wrapped_option_repr




.. theorem:: fin.induction_on




.. theorem:: split_eq




.. theorem:: vector.last




.. theorem:: vector.last_def




.. theorem:: vector.reverse_nth_zero




.. theorem:: vector.scanl




.. theorem:: vector.scanl.induction_on




.. theorem:: vector.scanl_cons




.. theorem:: vector.scanl_head




.. theorem:: vector.scanl_nil




.. theorem:: vector.scanl_nth




.. theorem:: vector.scanl_singleton




.. theorem:: vector.scanl_val




.. theorem:: vector.singleton_tail




.. theorem:: vector.tail_nil




.. theorem:: vector.to_list_reverse




.. theorem:: vector.to_list_scanl




.. theorem:: vector.to_list_singleton




``guarini``
===========

“Proof” of Guarini’s Problem: swapping some knights.

Given a board like:

::

   ♞ _ ♞
   _ _ _
   ♘ _ ♘

Guarini’s problem asks for a sequence of moves that swaps the knights,
producing:

::

   ♘ _ ♘
   _ _ _
   ♞ _ ♞

Solution:

::

   ♞ _ ♞     ♞ _ ♞     ♞ _ _     ♞ _ ♘     _ _ ♘
   _ _ _  →  ♘ _ _  →  ♘ _ _  →  _ _ _  →  _ _ ♞
   ♘ _ ♘     ♘ _ _     ♘ ♞ _     ♘ ♞ _     ♘ ♞ _


             _ ♘ ♘     _ _ ♘     _ _ ♘     _ _ ♘
          →  _ _ ♞  →  _ _ ♞  →  ♘ _ ♞  →  ♘ _ _
             _ ♞ _     _ ♞ ♘     _ ♞ _     ♞ ♞ _


             _ ♞ ♘     ♞ ♞ ♘     _ ♞ ♘     _ ♞ _
          →  ♘ _ _  →  ♘ _ _  →  ♘ _ ♞  →  ♘ _ ♞
             _ ♞ _     _ _ _     _ _ _     _ ♘ _


             ♘ ♞ _     ♘ ♞ ♘     ♘ ♞ ♘     ♘ _ ♘
          →  ♘ _ ♞  →  _ _ ♞  →  _ _ _  →  _ _ _
             _ _ _     _ _ _     ♞ _ _     ♞ _ ♞



.. theorem:: ending_position




.. theorem:: first_move




.. theorem:: guarini




.. theorem:: guarini_seq




.. theorem:: starting_position
