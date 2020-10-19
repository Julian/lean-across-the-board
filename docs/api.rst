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

    No inhabited instance because the index type can be larger than the
    cardinality of the playfield dimensions.


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

    A board’s representation is provided by ``board_repr``.


.. theorem:: board_repr_pieces

    A board’s ``pieces`` is a “vector”, so ``vec_repr`` is used to represent
    it.


.. theorem:: contents_decidable

    Explicitly state that the proposition that an index ``ix : ι`` is in the
    board is ``decidable``, when the ``ι`` is itself ``decidable_eq``.


.. theorem:: has_equiv




.. theorem:: has_mem




.. theorem:: height

    The height of the board. Explicit argument for projection notation.


.. theorem:: inj_iff

    Given that the board is ``occupied_at`` some ``pos : m × n``, then the
    index at some ``pos' : m × n`` is equal to the index at ``pos``, iff
    that ``pos'`` is equal ``pos' = pos``.


.. theorem:: no_superimposed

    A board maps each index ``ix : ι`` to a unique position ``pos : m × n``,
    stated explicitly. Uses the ``board.injects`` constraint.


.. theorem:: reduce

    The state of the board, where pieces of the same type are equivalent


.. theorem:: retains_pieces

    A board contains all of the ``ix : ι`` indices that it knows of, stated
    explicitly. Uses the ``board.contains`` constraint.


.. theorem:: width

    The width of the board. Explicit argument for projection notation.


``chess.move``
==============

Definitions and theorems about chess board movements
----------------------------------------------------

Summary
~~~~~~~

A ``move`` on a particular ``board`` is a pair of squares whose start
square contains a ``piece`` and whose end square does not.

Moves may be combined into ``sequence``\ s of moves, which encapsulate
multiple sequential moves all iteratively satisfying the above
condition.

Main definitions
~~~~~~~~~~~~~~~~

1. The ``move`` itself, which requires specifying the particular
   ``board`` it will occur on

2. ``perform_move``, which yields the ``board`` whose playfield has the
   start and end squares of a ``move`` suitably modified

3. A move ``sequence``, rooted on a starting board, containing a
   sequence of start and end squares which can be treated as iterated
   moves.

Implementation notes
~~~~~~~~~~~~~~~~~~~~

1. ``move`` and ``sequence`` are implemented independently of each
   other. ``sequence.moves`` can be used to extract a ``move`` from a
   particular index into a ``sequence``. ``sequence``\ s are also
   currently finite, and therefore also may automatically infer proofs
   of move conditions via ``dec_trivial``.

2. Currently, no legality checks or piece math whatsoever is performed,
   meaning ``move``\ s are not yet programmatically confirmed to be
   legal. Captures are similarly not yet supported.



.. theorem:: chess.board.has_sequence_len

    Assert the existence of a ``sequence`` of length ``o`` from a
    ``start_board`` to a given end board.


.. theorem:: chess.board.has_sequence_to

    Assert the existence of a ``sequence`` from a ``start_board`` to a given
    end board.


.. theorem:: chess.move

    A move is a (distinct) start and end square whose start square is
    occupied and whose end square is not.

    No inhabited instance because the board might be made up of a single
    occupied position.

    (Captures are not implemented yet.)


.. theorem:: after_occupied_end

    End squares are occupied after a move.


.. theorem:: after_unoccupied_start

    Start squares are unoccupied after a move.


.. theorem:: before_after_same

    Other squares are unchanged after a move.


.. theorem:: before_after_same_occupied

    Other occupation are unchanged after a move.


.. theorem:: before_occupied_start

    Start squares are occupied before a move.


.. theorem:: before_unoccupied_end

    End squares are unoccupied before a move.


.. theorem:: diff_squares

    The start and end squares of a move are distinct.


.. theorem:: no_superimposed

    Pieces do not become superimposed after a move.


.. theorem:: perform_move

    A valid ``move`` on a ``board`` retains a valid board state.


.. theorem:: piece

    The piece that is being moved.


.. theorem:: retains_injectivity

    A ``move`` retains accesing indices injectively on the ``board`` it
    operates on.


.. theorem:: retains_surjectivity

    A ``move`` retains all indices, ignoring empty squares, present on the
    ``board`` it operates on.


.. theorem:: scan_contents

    Define the mapping of ``playfield``\ s after performing successive
    ``move_piece``\ s using the pairs of positions in the provided
    ``elements``, starting from the ``start_board``.


.. theorem:: sequence

    A move ``sequence`` represents a sequential set of moves from a starting
    ``board``.

    No inhabited instance because boards do not have an inhabited instance.


.. theorem:: sequence.all_occupied_start

    Every scanned board is occupied at the start square of the upcoming
    move.


.. theorem:: sequence.all_unoccupied_end

    Every scanned board is unoccupied at the end square of the upcoming
    move.


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


.. theorem:: sequence.no_superimposed

    Pieces do not become superimposed after any ``move`` in a ``sequence``.


.. theorem:: sequence.retains_injectivity

    Every ``playfield`` in a sequence of moves injectively accesses the
    indices.


.. theorem:: sequence.retains_pieces

    Pieces do not disappear after any ``move_piece`` in a ``sequence``.


.. theorem:: sequence.retains_surjectivity

    Every ``playfield`` in a sequence of moves contains all the indices it
    can.


.. theorem:: sequence.sequence_step

    Any ``contents_at`` a step in the ``sequence`` is the result of
    performing a ``move_piece`` using the ``sequence.elements`` at that
    step.


.. theorem:: sequence.sequence_zero

    The first contents in a ``scan_contents`` ``sequence`` is of the
    ``start_board``.


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




.. theorem:: chess.colored_piece




.. theorem:: chess.colored_piece.decidable_eq




.. theorem:: chess.has_repr




.. theorem:: chess.piece_repr




.. theorem:: chess.piece




.. theorem:: chess.piece.decidable_eq




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


.. theorem:: playfield.coe_occ_t

    A ``pos : pf.occupied_positions`` can be used as a ``pos : m × n``.


.. theorem:: playfield.coe_occ_val

    A ``pos : pf.occupied_positions`` can be used as a ``pos : m × n``.


.. theorem:: playfield.decidable_pred

    The predicate that ``pf.occupied_at pos`` for some pos is decidable if
    the indices ``ix : ι`` are finite and decidably equal.


.. theorem:: playfield.exists_of_occupied

    A
    ``pos : pf.occupied_positions' has the property that there is an not-necessarily-unique``\ ix
    : ι\ ``such that``\ pf pos = some ix`.


.. theorem:: playfield.exists_unique_of_occupied

    A
    ``pos : pf.occupied_positions' has the property that there is a necessarily-unique``\ ix
    : ι\ ``such that``\ pf pos = some ix`.


.. theorem:: playfield.fintype




.. theorem:: playfield.has_coe




.. theorem:: playfield.has_mem

    A piece, identified by an index, is on the board, if there is any
    position such that the index at that position is the one we’re inquiring
    about. Providing a ``has_mem`` instance allows using ``ix ∈ pf`` for
    ``ix : ι, pf : playfield m n ι``. This definition does not preclude
    duplicated indices on the playfield. See “Implementation details”.


.. theorem:: playfield.index_at

    Extract the ``ix : ι`` that is at ``pf pos = some ix``.


.. theorem:: playfield.index_at.implies_surjective

    Index retrieval via ``pf`` is known to be surjective, given an
    surjectivity condition via ``function.surjective pf.index_at`` and an
    unoccupied square somewhere.


.. theorem:: playfield.index_at.injective

    Index retrieval via ``pf.index_at`` is known to be injective, given an
    injectivity condition via ``pf.some_injective``.


.. theorem:: playfield.index_at.surjective

    Index retrieval via ``pf.index_at`` is known to be surjective, given an
    surjectivity condition via ``function.surjective pf``.


.. theorem:: playfield.index_at_def

    Extract the ``ix : ι`` that is at ``pf pos = some ix``.


.. theorem:: playfield.index_at_exists

    The index retrieved via ``pf.index_at`` is known to be in the ``pf``, in
    existential format.


.. theorem:: playfield.index_at_exists'

    The index retrieved via ``pf.index_at`` is known to be in the ``pf``, in
    existential format, operating on the ``pf.occupied_positions`` subtype.


.. theorem:: playfield.index_at_iff

    For a ``pos : pf.occupied_positions``, the wrapped index ``ix : ι``
    given by ``pf.index_at pos`` is precisely ``pf pos``, in iff form.


.. theorem:: playfield.index_at_in

    The index retrieved via ``pf.index_at`` is known to be in the ``pf``.


.. theorem:: playfield.index_at_inj

    Index retrieval via ``pf.index_at`` is known to be injective, given an
    injectivity condition via ``pf.some_injective``.


.. theorem:: playfield.index_at_inv_pos_from'

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the right inverse of ``pf.index_at``
    is ``pf.pos_from'``.


.. theorem:: playfield.index_at_mk

    For a ``pos : m × n``, and the hypothesis that ``h : pf pos = some ix``,
    the index given by ``pf.index_at (occupied_positions.mk _ h)`` is
    precisely ``ix``.


.. theorem:: playfield.index_at_retains_surjectivity

    If every index and the empty square is present in the
    ``pf : playfield m n ι``, as given by a ``function.surjective pf``
    proposition, then each index is present on the playfield after a
    ``move_piece``.


.. theorem:: playfield.index_at_some

    For a ``pos : pf.occupied_positions``, the wrapped index given by
    ``pf.index_at pos`` is precisely ``pf pos``.


.. theorem:: playfield.index_equiv

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, there is an explicit equivalence
    from the indices ``ι`` to the type of positions in
    ``pf.occupied_positions``.


.. theorem:: playfield.inhabited

    A ``playfield`` is by default ``inhabited`` by empty squares everywhere.


.. theorem:: playfield.inj_iff

    When a ``pf : playfield m n ι`` is ``some_injective``, if it is occupied
    at some ``pos : m × n``, then it is injective at that ``pos``.


.. theorem:: playfield.injective

    When a ``pf : playfield m n ι`` is ``some_injective``, if it is not
    empty at some ``pos : m × n``, then it is injective at that ``pos``.


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


.. theorem:: playfield.move_piece_occupied_diff

    The ``pf : playfield m n ι`` is ``occupied_at other_square`` after a
    ``move_piece``, for a ``pos`` that is neither ``start_square`` nor
    ``end_square``, iff it is ``occupied_at other_square`` before the piece
    move.


.. theorem:: playfield.move_piece_occupied_end

    The ``pf : playfield m n ι`` is ``occupied_at end_square`` after a
    ``move_piece`` iff it is ``occupied_at start_square`` before the piece
    move.


.. theorem:: playfield.move_piece_occupied_start

    The ``pf : playfield m n ι`` is ``occupied_at start_square`` after a
    ``move_piece`` iff it is ``occupied_at end_square`` before the piece
    move.


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


.. theorem:: playfield.nonempty_pos

    Given a surjectivity condition of ``pf.index_at``, the type of
    ``pos : pf.occupied_positions`` that identify a particular index is a
    nonempty.


.. theorem:: playfield.occupied_at

    A wrapper to indicate that there is some ``ix : ι`` such that for a
    ``pf : playfield m n ι``, at ``pos : m × n``, ``pf pos = some ix``.


.. theorem:: playfield.occupied_at_def

    A wrapper to indicate that there is some ``ix : ι`` such that for a
    ``pf : playfield m n ι``, at ``pos : m × n``, ``pf pos = some ix``.


.. theorem:: playfield.occupied_at_iff

    A wrapper to indicate that there is some ``ix : ι`` such that for a
    ``pf : playfield m n ι``, at ``pos : m × n``, ``pf pos = some ix``.


.. theorem:: playfield.occupied_at_of_ne

    If for some ``pf : playfield m n ι``, at ``pos : m × n``,
    ``pf pos ≠ none``, then that is equivalent to ``pf.occupied_at pos``.


.. theorem:: playfield.occupied_at_of_some

    If for some ``pf : playfield m n ι``, at ``pos : m × n``,
    ``pf pos = some ix``, then that is equivalent to ``pf.occupied_at pos``.


.. theorem:: playfield.occupied_at_unique

    A ``pf : playfield m n ι`` maps any occupied ``pos`` uniquely.


.. theorem:: playfield.occupied_fintype

    The ``occupied_positions`` of a ``pf : playfield m n ι`` are finite if
    the dimensions of the playfield and the indices are finite.


.. theorem:: playfield.occupied_has_not_none

    A wrapper API for converting between inequalities and existentials.


.. theorem:: playfield.occupied_has_some

    A wrapper API for underlying ``option.is_some`` propositions.


.. theorem:: playfield.occupied_is_some

    A ``pos : pf.occupied_positions'`` has the property that ``pf pos`` is
    occupied.


.. theorem:: playfield.occupied_positions

    The positions ``pos : m × n`` for a ``pf : playfield m n ι`` such that
    there is an index ``ix : ι`` at ``pf pos``. In other words, the
    positions of ``pf`` that are occupied.

    No inhabited instance exists because the type could be empty, if all the
    positions of the playfield are empty.


.. theorem:: playfield.occupied_positions.mk

    Given some ``ix : ι`` such that for ``pf : playfield m n ι`` and
    ``pos : m × n``, ``pf pos = some ix``, we can subtype into
    ``pos : pf.occupied_positions``.


.. theorem:: playfield.occupied_positions_def

    Given some ``ix : ι`` such that for ``pf : playfield m n ι`` and
    ``pos : m × n``, ``pf pos = some ix``, we can subtype into
    ``pos : pf.occupied_positions``.


.. theorem:: playfield.occupied_some_injective

    The injectivity of ``pf.some_injective`` extends to the
    ``pf.occupied_positions`` subtype.


.. theorem:: playfield.occupied_unique_of_injective

    The index retrieved via ``pf.index_at`` is known to be unique in the
    ``pf``, given an injectivity condition via ``pf.some_injective``.


.. theorem:: playfield.playfield_decidable_in




.. theorem:: playfield.playfield_repr_instance




.. theorem:: playfield.pos_from

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the type there exists a
    ``pos : m × n' such that``\ pf pos = some ix`.


.. theorem:: playfield.pos_from'

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, we can retrieve the
    ``pos : pf.occupied_positions`` such that ``pf.index_at pos = ix``.


.. theorem:: playfield.pos_from.injective

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the function ``pf.pos_from`` is
    injective.


.. theorem:: playfield.pos_from_at

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, round-tripping to get the
    ``pf (pf.pos_from ix _ _)`` is exactly ``some ix``,


.. theorem:: playfield.pos_from_at'

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, round-tripping to get the
    ``pf (pf.pos_from' ix _ _)`` is exactly ``some ix``, which goes through
    the coercion down to ``pos : m × n``.


.. theorem:: playfield.pos_from_aux

    A helper subtype definition describing all the positions that match an
    index.

    No inhabited instance exists because the type could be empty, if none of
    the positions of the playfield have this index.


.. theorem:: playfield.pos_from_aux_subtype

    A helper subtype definition describing all the positions that match an
    index.


.. theorem:: playfield.pos_from_auxf

    A helper finset definition describing all the positions that match an
    index.


.. theorem:: playfield.pos_from_auxf_finset

    A helper finset definition describing all the positions that match an
    index.


.. theorem:: playfield.pos_from_auxf_in

    A helper finset definition describing all the positions that match an
    index.


.. theorem:: playfield.pos_from_auxf_set

    A helper set definition describing all the positions that match an
    index.


.. theorem:: playfield.pos_from_def

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the type there exists a
    ``pos : m × n' such that``\ pf pos = some ix`.


.. theorem:: playfield.pos_from_def'

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, we can retrieve the
    ``pos : pf.occupied_positions`` such that ``pf.index_at pos = ix``.


.. theorem:: playfield.pos_from_index_at'

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, round-tripping to get the
    ``pf.index_at (pf.pos_from' ix _ _)`` is exactly ``ix``.


.. theorem:: playfield.pos_from_inv

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the partial inverse of
    ``pf.pos_from`` is ``pf`` itself.


.. theorem:: playfield.pos_from_inv_index_at'

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the left inverse of ``pf.index_at``
    is ``pf.pos_from'``.


.. theorem:: playfield.pos_from_occupied

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the position retrieved via
    ``pf.pos_from`` means that the ``pf`` is ``occupied_at`` it.


.. theorem:: playfield.retains_injectivity

    Each index that is present on the playfield and appears only once,
    appears only once after a ``move_piece``.


.. theorem:: playfield.retains_pieces

    Pieces do not disappear after a ``move_piece``.


.. theorem:: playfield.retains_surjectivity

    If every index and the empty square is present in the
    ``pf : playfield m n ι``, as given by a ``function.surjective pf``
    proposition, then each index is present on the playfield after a
    ``move_piece``.


.. theorem:: playfield.some_injective

    A ``playfield`` on which every index that appears, appears only once.


.. theorem:: playfield.some_injective_decidable

    Explicitly state that the proposition that ``pf.some_injective`` is
    ``decidable``, when the ``ι`` is itself ``decidable_eq``.


.. theorem:: playfield.subsingleton_pos

    Given an injectivity condition of ``pf.some_injective``, the type of
    ``pos : pf.occupied_positions`` that identify a particular index is a
    subsingleton.


.. theorem:: playfield.unique_of_injective

    When a ``pf : playfield m n ι`` is ``some_injective``, every index
    ``ix : ι ∈ pf`` exists in the ``pf`` uniquely.


.. theorem:: playfield.unique_of_occupied

    When a ``pf : playfield m n ι`` is ``some_injective``, every
    ``pos : pf.occupied_positions`` maps to a unique index via ``pf pos``.


.. theorem:: playfield.unique_pos

    Given a surjectivity condition of ``pf.index_at``, and an injectivity
    condition of ``pf.some_injective``, the type of
    ``pos : pf.occupied_positions`` that identify a particular index is a
    unique.


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




.. theorem:: split_eq




.. theorem:: vector.scanl




.. theorem:: vector.scanl_cons




.. theorem:: vector.scanl_head




.. theorem:: vector.scanl_nil




.. theorem:: vector.scanl_nth




.. theorem:: vector.scanl_singleton




.. theorem:: vector.scanl_val




.. theorem:: vector.to_list_scanl




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
