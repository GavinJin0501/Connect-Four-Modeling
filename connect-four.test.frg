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
    assert positiveWellFormed is sufficient for wellformed 
    assert negativeWellFormed is sufficient for notWellFormed
}

//------------- winning -------------//
// pred positiveRowWin[b: Board] {
//     some row, col: Int | {
//         inBounds[]
//     }
// }
