#lang forge/bsl

open "connect-four.frg"

//------------- wellformed -------------//
-- A positive board must have no entries outside of scope
pred positiveWellFormed {
    all b: Board | { 
        all row, col: Int | {
            not inBounds[row, col] implies no b.position[row][col]
        } 
    }
}

-- A full board is a wellformed board
pred fullBoard {
    all b: Board | {
        all row, col: Int | {
            not inBounds[row, col] implies no b.position[row][col]
        }
    }
}

-- Any board that has negative entry is invalid
pred noNegativeEntryBoard {
    all b: Board | {
        all row, col: Int | {
            (row < 0 or col < 0) implies no b.position[row][col]
        }
    }
}

-- Any board that has oversized entry is invalid
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
-- Any initial board should not has anything on it
pred positiveInitial[b: Board] {
    all row, col: Int | {
        inBounds[row, col] implies no b.position[row][col]
        not inBounds[row, col] implies no b.position[row][col]
    }
}

-- A board which all row has no player is a valid initial board
pred noPlayerInRow[b: Board] {
    all row: Int | {
        #{col: Int | b.position[row][col] = Red} = 0
        #{col: Int | b.position[row][col] = Black} = 0
    }
}

-- A board which all col has no player is a valid initial board
pred noPlayerInColumn[b: Board] {
    all col: Int | {
        #{row: Int | b.position[row][col] = Red} = 0
        #{row: Int | b.position[row][col] = Black} = 0
    }
}

-- Any board that has something on board is invalid
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
-- If its a red turn, the number of red and black should be the same
pred positiveRedTurn[b:Board] {
    add[#{row, col: Int | b.position[row][col] = Red}, 1]
    = 
    add[#{row, col: Int | b.position[row][col] = Black}, 1]
}

--  If the number of red and black should be the same, then it should be the red turn
pred RedBlackEqual[b:Board] {
    all i : Int | {
        add[#{row, col: Int | b.position[row][col] = Red}, i]
        = 
        add[#{row, col: Int | b.position[row][col] = Black}, i]
    }  
}

--  If the number of red is larger than black, then it should not be the red turn
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
    assert all b:Board | RedBlackEqual[b] is necessary for red_turn[b]
}

//------------- black turn -------------//
-- If its a black turn, the number of red should be 1 greater than the number of  black
pred positiveBlackTurn[b:Board] {
    subtract[#{row, col: Int | b.position[row][col] = Red}, 1]
    = 
    #{row, col: Int | b.position[row][col] = Black}
}

-- If the number of red is greater than the number of  black, then its black turn
pred RedMoreThanBlack[b:Board] {
    all i : Int | {
        add[#{row, col: Int | b.position[row][col] = Red}, i]
        !=
        add[#{row, col: Int | b.position[row][col] = Black}, i]
    }  
}

-- If the number of red equals to black, then it should not be the red turn
pred negativeBlackTurn[b:Board] {
    #{row, col: Int | b.position[row][col] = Red} 
    =
    #{row, col: Int | b.position[row][col] = Black}
}

pred notBlackTurn[b: Board] {
    not black_turn[b]
}

test suite for black_turn {
    assert all b:Board | positiveBlackTurn[b] is sufficient for black_turn[b]
    assert all b:Board | negativeBlackTurn[b] is sufficient for notBlackTurn[b]
    assert all b:Board | RedMoreThanBlack[b] is necessary for black_turn[b]
}

//------------- winning -------------//
-- If a row has 4 , then this player should win
pred positiveRowWin[b: Board, p: Player] {
    some row1, col1: Int | {
        b.position[row1][col1] = p
        #{col2: Int | col2 >= col1 and subtract[col2, col1] < 4 and b.position[row1][col2] = p} = 4
    }
}

-- If a col has 4 , then this player should win
pred positiveColWin[b: Board, p: Player] {
    some row1, col1: Int | {
        b.position[row1][col1] = p
        #{row2: Int | row2 >= row1 and subtract[row2, row1] < 4 and b.position[row2][col1] = p} = 4
    }
}

-- If a disgonal has 4 , then this player should win
pred positiveDiagonalWin[b: Board, p: Player] {
     some row1, col1: Int | {
        b.position[row1][col1] = p
        #{row2, col2: Int | (subtract[row1, row2] = subtract[col1, col2]) 
                             and (b.position[row2][col2]) = p
                             and subtract[row2, row1] < 4} = 4 
     }
}

-- A full board which has either of the 3 winning condition is winning 
pred allWinning[b: Board, p: Player] {
    some row1, col1: Int | b.position[row1][col1] = p and {
        -- 4 in a row
        #{col2: Int | col2 >= col1 and subtract[col2, col1] < 4 and b.position[row1][col2] = p} = 4
        
        or

        -- 4 in a column
        #{row2: Int | row2 >= row1 and subtract[row2, row1] < 4 and b.position[row2][col1] = p} = 4

        or

        -- 4 in a diagonal
        #{row2, col2: Int | (subtract[row1, row2] = subtract[col1, col2]) 
                             and (b.position[row2][col2]) = p
                             and subtract[row2, row1] < 4} = 4 
    }
}

pred negativeWinning[b: Board, p: Player] {
    all row1, col1: Int | b.position[row1][col1] = p and {
        -- 4 in a row
        #{col2: Int | col2 >= col1 and subtract[col2, col1] < 4 and b.position[row1][col2] = p} < 4
        
        and

        -- 4 in a column
        #{row2: Int | row2 >= row1 and subtract[row2, row1] < 4 and b.position[row2][col1] = p} < 4

        and

        -- 4 in a diagonal
        #{row2, col2: Int | (subtract[row1, row2] = subtract[col1, col2]) 
                             and (b.position[row2][col2]) = p
                             and subtract[row2, row1] < 4} < 4 
    }
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
-- A move with red turn and not black turn is a valid move
pred positiveMoveRed[pre: Board, 
                    row, col: Int, 
                    turn: Player, 
                    post: Board] {
    turn = Red
    no pre.position[row][col]
    red_turn[pre]
    not black_turn[pre]

    all p: Player | not winning[pre, p]

    inBounds[row, col]
    row = 0 or some pre.position[subtract[row, 1], col]

    post.position[row][col] = turn 
    all row2: Int, col2: Int | (row!=row2 or col!=col2) implies {
        post.position[row2][col2] = pre.position[row2][col2]
    }
}

-- A move should increase the number of players on board (either red or black)
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

--  A move should not be on the place where there is already a player
pred negativeMoveIndex[pre: Board, 
                          row, col: Int, 
                          turn: Player, 
                          post: Board] {
    inBounds[row, col]
    row > 0
    no pre.position[subtract[row, 1], col]
}

--  A move should not be with the wrong player turn
pred negativeMoveTurn[pre: Board, 
                      row, col: Int, 
                      turn: Player, 
                      post: Board] {
    turn = Red implies not red_turn[pre]
    turn = Black implies not black_turn[pre]
}

-- When a move is made, there should not be winning
pred negativeMoveWinning[pre: Board, 
                         row, col: Int, 
                         turn: Player, 
                         post: Board] {
    winning[pre, turn]
}

--  A move should not be on invalid board position
pred negativeMovePosition[pre: Board, 
                         row, col: Int, 
                         turn: Player, 
                         post: Board] {
    -- satisfy all guards
    no pre.position[row][col]
    turn = Red implies red_turn[pre]
    turn = Black implies black_turn[pre]
    all p: Player | not winning[pre, p]
    inBounds[row, col]
    row = 0 or some pre.position[subtract[row, 1], col]

    post.position[row][col] != turn
}

-- After moving, other positions on the board should not be changed
pred negativeMovePost[pre: Board, 
                         row, col: Int, 
                         turn: Player, 
                         post: Board] {
    -- satisfy all guards
    no pre.position[row][col]
    turn = Red implies red_turn[pre]
    turn = Black implies black_turn[pre]
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
-- If Red has won, then should do nothing
pred positiveDoNothingRed[pre, post: Board] {
    some p: Player | p = Red and winning[pre, p]

    all r, c: Int | {
        pre.position[r][c] = post.position[r][c]
    }
}

-- If Red has won, then should do nothing
pred numberDoesntChange[pre: Board,post: Board] {
    (#{row, col: Int | pre.position[row][col] = Red} = #{row, col: Int | post.position[row][col] = Red})
    (#{row, col: Int | pre.position[row][col] = Black} = #{row, col: Int | post.position[row][col] = Black})
}

-- If both Red and Black are not winning, then there should not be doing nothing
pred negativeDoNothingNotWinning[pre, post: Board] {
    not winning[pre, Red]
    not winning[pre, Black]

    all r, c: Int | {
        pre.position[r][c] = post.position[r][c]
    }
}

-- If do nothing, then nothing on the board should change
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