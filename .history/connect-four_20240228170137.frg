#lang forge/bsl 

option run_sterling "vis.js"

/*
Modeling Connect Four
*/

-- Two players
-- Red starts first
abstract sig Player {} 
one sig Red, Black extends Player {} 

-- A board
sig Board {
    position: pfunc Int -> Int -> Player
}

-- The board is 6 x 7
fun MIN_ROW: one Int { 0 }
fun MAX_ROW: one Int { 5 }
fun MIN_COL: one Int { 0 }
fun MAX_COL: one Int { 6 }

-- predicate: rule out "garbage"
pred wellformed {
    all b: Board | { 
        all row, col: Int | {
            (row < MIN_ROW or row > MAX_ROW or 
            col < MIN_COL or col > MAX_COL) implies
                no b.position[row][col]
    } }
}

-- predicate: initial board
pred initial[b: Board] {
    all row, col: Int | no b.position[row][col]
}

-- predicate: Turn for the red player
pred red_turn[b: Board] {
    #{row, col: Int | b.position[row][col] = Red} 
    = 
    #{row, col: Int | b.position[row][col] = Black} 
}

-- predicate: Turn for the black player
pred black_turn[b: Board] {
    #{row, col: Int | b.position[row][col] = Red} 
    = 
    add[#{row, col: Int | b.position[row][col] = Black}, 1]
}

pred balanced[b: Board] {
    red_turn[b] or red_turn[b]
}

pred winning[b: Board, p: Player] {
    -- 4 in a row
    // (some row: Int | {
    //     #{col: Int | b.position[row][col] = p} = 4 
    // }) 

    some row1, col1: Int | b.position[row1][col1] = p and {
        -- 4 in a row
        #{col2: Int | col2 >= col1 and subtract[col2, col1] < 4}
    }

    some row, col1: Int | b.position[row][col1] = p and {
        #{col2: Int | col2 >= col1 and subtract[col2, col1] < 4 and b.position[row][col2] = p} = 4
    }

    or

    -- 4 in a col
    // (some col: Int | {
    //     #{row: Int | b.position[row][col] = p} = 4 
    // }) 
    some row1, col: Int | b.position[row1][col1] = p and {
        #{row2: Int | row2 >= row1 and subtract[row2, row1] < 4 and b.position[row2][col] = p} = 4
    }

    or 

    -- 4 in a diagonal
    (some row1, col1: Int | b.position[row1][col1] = p and {
        #{row2, col2: Int | (subtract[row1, row2] = subtract[col1, col2]) and (b.position[row2][col2]) = p} = 4 
    }) 
}

// pred tie[b: Board, p1, p2: Player] {
//     // not winning[b, p1]
//     // not winning[b, p2]
//     all row, col: Int | {
//         inBounds[row, col] implies some b.position[row][col]
//     }
// }


pred inBounds[r: Int, c: Int] {
  r>=0 r<=5
  c>=0 c<=6
}

pred move[pre: Board, 
          row, col: Int, 
          turn: Player, 
          post: Board] {
    -- guard: conditions necessary to make a move  
    -- cant move somewhere with an existing mark
    -- valid move location
    -- it needs to be the player's turn 
    no pre.position[row][col]
    turn = Red implies red_turn[pre]
    turn = Black implies black_turn[pre]

    -- prevent winning boards from progressing
    all p: Player | not winning[pre, p]

    -- enforce valid move index
    inBounds[row, col]
    row = 0 or some pre.position[subtract[row, 1], col]

    -- balanced game
    -- game hasn't been won yet
    -- if it's a tie can't move 
    -- board needs to be well-formed 

    -- action: effects of making a move

    -- mark the location with the player 
    post.position[row][col] = turn 
    -- updating the board; check for winner or tie 
    -- other squares stay the same  ("frame condition")
    all row2: Int, col2: Int | (row!=row2 or col!=col2) implies {
        post.position[row2][col2] = pre.position[row2][col2]
    }
}

pred doNothing[pre, post: Board] {
    -- guard
    some p: Player | winning[pre, p]

    -- action
    all r, c: Int | {
        pre.position[r][c] = post.position[r][c]
    }
}

one sig Game {
    first: one Board, 
    next: pfunc Board -> Board
}

pred game_trace {
    wellformed
    initial[Game.first]
    // some g: Board | {
    //     winning[g, Red]    
    // }
    all b: Board | { some Game.next[b] implies {
        (some row, col: Int, p: Player | 
            move[b, row, col, p, Game.next[b]])
        or
        doNothing[b, Game.next[b]]
    }}
}

run {game_trace} for 3 Board for {next is linear}