#lang forge/bsl 

option run_sterling "vis.js"

/*
Modeling Connect Four
*/

-- Two players
-- Red starts first
abstract sig Player {} 
one sig Red, Yellow extends Player {} 

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
    #{row, col: Int | b.position[row][col] = Yellow} 
}

-- predicate: Turn for the yellow player
pred yellow_turn[b: Board] {
    #{row, col: Int | b.position[row][col] = Red} 
    = 
    add[#{row, col: Int | b.position[row][col] = Yellow}, 1]
}

pred balanced[b: Board] {
    red_turn[b] or red_turn[b]
}

pred winning[b: Board, p: Player] {
    -- 4 in a row
    (some row: Int | {
        #{col: Int | b.position[row][col] = p} = 4 
    }) 

    or

    -- 4 in a col
    (some col: Int | {
        #{row: Int | b.position[row][col] = p} = 4 
    }) 

    or 

    -- 4 in a diagonal
    (some row1, col1: Int | b.position[row1][col1] = p and {
        #{row2, col2: Int | (subtract[row1, row2] = subtract[col1, col2]) and (b.position[row2][col2]) = p} = 4 
    }) 
}

one sig Game {
    first: one Board, 
    next: pfunc Board -> Board
}

pred game_trace {
    wellformed
    initial[Game.first]
    some g: Board | {
        winning[g, Red]    
    }
    
}

run {game_trace}