#lang forge/bsl 

option run_sterling "vis.js"

/*
Modeling Connect Four
*/

-- Two players
-- Red starts first
abstract sig Player {} 
one sig Red, Yellow extends Player {} 

-- A grid
sig Grid {
    grid: pfunc Int -> Int -> Player
}

-- The grid is 6 x 7
fun MIN_ROW: one Int { 0 }
fun MAX_ROW: one Int { 5 }
fun MIN_COL: one Int { 0 }
fun MAX_COL: one Int { 6 }

-- predicate: rule out "garbage"
pred wellformed {
    all g: Grid | { 
        all row, col: Int | {
            (row < MIN_ROW or row > MAX_ROW or 
            col < MIN_COL or col > MAX_COL) implies
                no g.grid[row][col]
    } }
}

-- predicate: initial grid
pred initial[g: Grid] {
    all row, col: Int | no g.grid[row][col]
}

-- predicate: Turn for the red player
pred red_turn[g: Grid] {
    #{row, col: Int | g.grid[row][col] = Red} 
    = 
    #{row, col: Int | g.grid[row][col] = Yellow} 
}

-- predicate: Turn for the yellow player
pred yellow_turn[g: Grid] {
    #{row, col: Int | g.grid[row][col] = Red} 
    = 
    add[#{row, col: Int | g.grid[row][col] = Yellow}, 1]
}

pred balanced[g: Grid] {
    red_turn[g] or red_turn[g]
}

pred winning[g: Grid, p: Player] {
    -- 4 in a row
    (some row: Int | {
        #{col: Int | g.grid[row][col] = p} = 4 
    }) 

    or

    -- 4 in a col
    (some col: Int | {
        #{row: Int | g.grid[row][col] = p} = 4 
    }) 

    or 

    -- 4 in a diagonal
    (some row1, col1: Int | g.grid[row1][col1] = p and {
        #{row2, col2: Int | (subtract[row1, row2] = subtract[col1, col2]) and (g.grid[row2][col2]) = p} = 4 
    }) 
}

one sig Game {
    first: one Grid, 
    next: pfunc Grid -> Grid
}

pred game_trace {
    wellformed
    initial[Game.first]
    some g: Grid | {
        winning[g, Red]    
    }
    
}

run {game_trace}