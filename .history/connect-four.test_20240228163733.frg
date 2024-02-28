#lang forge/bsl

open "connect-four.frg"

//------------- wellformed -------------//
pred positiveWellFormed {
    all b: Board | { 
        all row, col: Int | {
            not inBounds[row, col] implies no b.position[row][col]
        } 
    }
}

pred fullBoard {
    all b: Board | {
        all row, col: Int | {
            not inBounds[row, col] implies no b.position[row][col]
        }
    }
}

pred noNegativeEntryBoard {
    all b: Board | {
        all row, col: Int | {
            (row < 0 or col < 0) implies no b.position[row][col]
        }
    }
}

pred noOverSizeEntryBoard {
    all b: Board | {
        all row, col: Int | {
            (row > 5 or col > 6) implies no b.position[row][col]
        }
    }
}

pred negativeWellFormed {
    all b: Board | {
        some row, col: Int | {
            not inBounds[row, col]
            some b.position[row][col]
        }
    }
}

pred notWellFormed {
    not wellformed
}

test suite for wellformed {
    assert fullBoard is sufficient for wellformed 
    assert negativeWellFormed is sufficient for notWellFormed
    assert positiveWellFormed is necessary for wellformed
    assert noNegativeEntryBoard is necessary for wellformed
    assert noOverSizeEntryBoard is necessary for wellformed
}

//------------- initial -------------//
pred positiveInitial[b: Board] {
    all row, col: Int | {
        inBounds[row, col] implies no b.position[row][col]
        not inBounds[row, col] implies no b.position[row][col]
    }
}

pred noPlayerInRow[b: Board] {
    all row: Int | {
        #{col: Int | b.position[row][col] = Red} = 0
        #{col: Int | b.position[row][col] = Black} = 0
    }
}

pred noPlayerInColumn[b: Board] {
    all col: Int | {
        #{row: Int | b.position[row][col] = Red} = 0
        #{row: Int | b.position[row][col] = Black} = 0
    }
}

pred negativeInitial[b: Board] {
    some row, col: Int | {
        inBounds[row, col] and some b.position[row][col]
    }
}

pred notInitial[b: Board] {
    not initial[b]
}

test suite for initial {
    assert all b:Board | positiveInitial[b] is sufficient for initial[b]
    assert all b:Board | negativeInitial[b] is sufficient for notInitial[b]
    assert all b:Board | noPlayerInRow[b] is necessary for initial[b]
    assert all b:Board | noPlayerInColumn[b] is necessary for initial[b]
}

//------------- red turn -------------//
pred positiveRedTurn[b:Board] {
    add[#{row, col: Int | b.position[row][col] = Red}, 1]
    = 
    add[#{row, col: Int | b.position[row][col] = Black}, 1]
}

pred RedYellowEqual[b:Board] {
    all i : Int | {
        add[#{row, col: Int | b.position[row][col] = Red}, i]
        = 
        add[#{row, col: Int | b.position[row][col] = Black}, i]
    }  
}

pred negativeRedTurn[b:Board] {
    #{row, col: Int | b.position[row][col] = Red} 
    > 
    #{row, col: Int | b.position[row][col] = Black}
}

pred notRedTurn[b: Board] {
    not red_turn[b]
}

test suite for red_turn {
    assert all b:Board | positiveRedTurn[b] is sufficient for red_turn[b]
    assert all b:Board | negativeRedTurn[b] is sufficient for notRedTurn[b]
    assert all b:Board | RedYellowEqual[b] is necessary for red_turn[b]
}

//------------- yellow turn -------------//
pred positiveYellowTurn[b:Board] {
    subtract[#{row, col: Int | b.position[row][col] = Red}, 1]
    = 
    #{row, col: Int | b.position[row][col] = Black}
}

pred RedMoreThanYellow[b:Board] {
    all i : Int | {
        add[#{row, col: Int | b.position[row][col] = Red}, i]
        !=
        add[#{row, col: Int | b.position[row][col] = Black}, i]
    }  
}

pred negativeYellowTurn[b:Board] {
    #{row, col: Int | b.position[row][col] = Red} 
    =
    #{row, col: Int | b.position[row][col] = Black}
}

pred notYellowTurn[b: Board] {
    not yellow_turn[b]
}

test suite for yellow_turn {
    assert all b:Board | positiveYellowTurn[b] is sufficient for yellow_turn[b]
    assert all b:Board | negativeYellowTurn[b] is sufficient for notYellowTurn[b]
    assert all b:Board | RedMoreThanYellow[b] is necessary for yellow_turn[b]
}

//------------- winning -------------//
pred positiveRowWin[b: Board, p: Player] {
    (some row: Int | {
        #{col: Int | b.position[row][col] = p} = 4 
    }) 
}

pred positiveColWin[b: Board, p: Player] {
    (some col: Int | {
        #{row: Int | b.position[row][col] = p} = 4 
    }) 
}

pred positiveDiagonalWin[b: Board, p: Player] {
    (some row1, col1: Int | b.position[row1][col1] = p and {
        #{row2, col2: Int | (subtract[row2, row1] = subtract[col2, col1]) and (b.position[row2][col2]) = p} = 4 
    }) 
}

pred allWinning[b: Board, p: Player] {
    -- 4 in a row
    (some row: Int | {
        #{col: Int | b.position[row][col] = Red} = 4 
        or
        #{col: Int | b.position[row][col] = Black} = 4 
    }) 

    or

    -- 4 in a col
    (some col: Int | {
        #{row: Int | b.position[row][col] = Red} = 4 
        or
        #{row: Int | b.position[row][col] = Black} = 4 
    }) 

    or 

    -- 4 in a diagonal
    (some row1, col1: Int | b.position[row1][col1] = p and {
        #{row2, col2: Int | (subtract[row1, row2] = subtract[col1, col2]) and (b.position[row2][col2]) = p} = 4 
    }) 
}

pred negativeWinning[b: Board, p: Player] {
    (all row: Int | {
        #{col: Int | b.position[row][col] = p} < 4 
    }) 

    and

    (all col: Int | {
        #{row: Int | b.position[row][col] = p} < 4 
    }) 

    and

    (all row1, col1: Int | b.position[row1][col1] = p and {
        #{row2, col2: Int | (subtract[row2, row1] = subtract[col2, col1]) and (b.position[row2][col2]) = p} < 4 
    }) 
}

pred notWinning[b: Board, p: Player] {
    not winning[b, p]
}

test suite for winning {
    assert all b:Board, p:Player | positiveRowWin[b, p] is sufficient for winning[b, p]
    assert all b:Board, p:Player | positiveColWin[b, p] is sufficient for winning[b, p]
    assert all b:Board, p:Player | positiveDiagonalWin[b, p] is sufficient for winning[b, p]
    assert all b:Board, p:Player | negativeWinning[b, p] is sufficient for notWinning[b, p]
    assert all b:Board, p:Player | allWinning[b, p] is necessary for winning[b, p]
}

//------------- move -------------//
pred positiveMoveRed[pre: Board, 
                    row, col: Int, 
                    turn: Player, 
                    post: Board] {
    turn = Red
    -- guard: conditions necessary to make a move  
    no pre.position[row][col]
    red_turn[pre]
    not yellow_turn[pre]

    -- prevent winning boards from progressing
    all p: Player | not winning[pre, p]

    -- enforce valid move index
    inBounds[row, col]
    row = 0 or some pre.position[subtract[row, 1], col]

    -- mark the location with the player 
    post.position[row][col] = turn 
    -- updating the board; check for winner or tie 
    -- other squares stay the same  ("frame condition")
    all row2: Int, col2: Int | (row!=row2 or col!=col2) implies {
        post.position[row2][col2] = pre.position[row2][col2]
    }
}

pred numberIncrease[pre: Board, 
             row, col: Int, 
             turn: Player, 
             post: Board] {
    (#{row, col: Int | pre.position[row][col] = Red} = #{row, col: Int | pre.position[row][col] = Black})
    implies
    (#{row, col: Int | post.position[row][col] = Red} > #{row, col: Int | post.position[row][col] = Black})

    (#{row, col: Int | pre.position[row][col] = Red} > #{row, col: Int | pre.position[row][col] = Black})
    implies
    (#{row, col: Int | post.position[row][col] = Red} = #{row, col: Int | post.position[row][col] = Black})
}

pred negativeMoveIndex[pre: Board, 
                          row, col: Int, 
                          turn: Player, 
                          post: Board] {
    inBounds[row, col]
    row > 0
    no pre.position[subtract[row, 1], col]
}

pred negativeMoveTurn[pre: Board, 
                      row, col: Int, 
                      turn: Player, 
                      post: Board] {
    turn = Red implies not red_turn[pre]
    turn = Black implies not yellow_turn[pre]
}

//TODO: Runs too slowly
pred negativeMoveWinning[pre: Board, 
                         row, col: Int, 
                         turn: Player, 
                         post: Board] {
    winning[pre, turn]
}

pred negativeMovePosition[pre: Board, 
                         row, col: Int, 
                         turn: Player, 
                         post: Board] {
    -- satisfy all guards
    no pre.position[row][col]
    turn = Red implies red_turn[pre]
    turn = Black implies yellow_turn[pre]
    all p: Player | not winning[pre, p]
    inBounds[row, col]
    row = 0 or some pre.position[subtract[row, 1], col]

    post.position[row][col] != turn
}

pred negativeMovePost[pre: Board, 
                         row, col: Int, 
                         turn: Player, 
                         post: Board] {
    -- satisfy all guards
    no pre.position[row][col]
    turn = Red implies red_turn[pre]
    turn = Black implies yellow_turn[pre]
    all p: Player | not winning[pre, p]
    inBounds[row, col]
    row = 0 or some pre.position[subtract[row, 1], col]

    post.position[row][col] != turn

    some row2: Int, col2: Int | {
        (row!=row2 or col!=col2)
        post.position[row2][col2] != pre.position[row2][col2]
    } 
}

pred notMove[pre: Board, 
             row, col: Int, 
             turn: Player, 
             post: Board] {
    not move[pre, row, col, turn, post]
}

test suite for move {
    assert all pre, post:Board, row, col:Int, turn:Player | positiveMoveRed[pre, row, col, turn, post] is sufficient for move[pre, row, col, turn, post] for exactly 2 Board

    assert all pre, post:Board, row, col:Int, turn:Player | negativeMoveIndex[pre, row, col, turn, post] is sufficient for notMove[pre, row, col, turn, post] for exactly 2 Board
    assert all pre, post:Board, row, col:Int, turn:Player | negativeMoveTurn[pre, row, col, turn, post] is sufficient for notMove[pre, row, col, turn, post] for exactly 2 Board
    // assert all pre, post:Board, row, col:Int, turn:Player | negativeMoveWinning[pre, row, col, turn, post] is sufficient for notMove[pre, row, col, turn, post] for exactly 2 Board
    assert all pre, post:Board, row, col:Int, turn:Player | negativeMovePosition[pre, row, col, turn, post] is sufficient for notMove[pre, row, col, turn, post] for exactly 2 Board
    assert all pre, post:Board, row, col:Int, turn:Player | negativeMovePost[pre, row, col, turn, post] is sufficient for notMove[pre, row, col, turn, post] for exactly 2 Board

    // assert all pre, post:Board, row, col:Int, turn:Player | redMore[pre, row, col, turn, post] is necessary for move[pre, row, col, turn, post] for exactly 2 Board
}

//------------- doNothing -------------//
pred positiveDoNothingRed[pre, post: Board] {
    some p: Player | p = Red and winning[pre, p]

    all r, c: Int | {
        pre.position[r][c] = post.position[r][c]
    }
}

pred numberDoesntChange[pre: Board,post: Board] {
    (#{row, col: Int | pre.position[row][col] = Red} = #{row, col: Int | post.position[row][col] = Red})
    (#{row, col: Int | pre.position[row][col] = Black} = #{row, col: Int | post.position[row][col] = Black})
}

//TODO: Runs too slowly
pred negativeDoNothingNotWinning[pre, post: Board] {
    not winning[pre, Red]
    not winning[pre, Black]

    all r, c: Int | {
        pre.position[r][c] = post.position[r][c]
    }
}

pred negativeDoNothingMoving[pre, post: Board] {
    some p: Player | winning[pre, p]

    some r, c: Int | {
        inBounds[r, c]
        pre.position[r][c] != post.position[r][c]
    }
}

pred notDoNothing[pre, post: Board] {
    not doNothing[pre, post]
}

test suite for doNothing {
    assert all pre, post:Board | positiveDoNothingRed[pre, post] is sufficient for doNothing[pre, post]
    // assert all pre, post:Board | negativeDoNothingNotWinning[pre, post] is sufficient for notDoNothing[pre, post]
    assert all pre, post:Board | negativeDoNothingMoving[pre, post] is sufficient for notDoNothing[pre, post]
    assert all pre, post:Board | numberDoesntChange[pre, post] is necessary for doNothing[pre, post]
}