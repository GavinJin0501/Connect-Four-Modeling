// INSTRUCTIONS: Since this script loads external elements, "Execute" may need to be run twice
// to guarantee that visualization is showing properly.

// Setup for importing necessary scripts/plugins
function loadSources() {
  var styleSheet = document.createElement('link');
  styleSheet.setAttribute('rel','stylesheet');
  styleSheet.setAttribute('href','https://unpkg.com/@chrisoakman/chessboardjs@1.0.0/dist/chessboard-1.0.0.min.css');
  styleSheet.setAttribute('integrity','sha384-q94+BZtLrkL1/ohfjR8c6L+A6qzNH9R2hBLwyoAfu3i/WCvQjzL2RQJ3uNHDISdU');
  styleSheet.setAttribute('crossorigin','anonymous');
  document.head.appendChild(styleSheet);

  var jQueryImport = document.createElement('script');
  jQueryImport.setAttribute('src','https://code.jquery.com/jquery-3.5.1.min.js');
  jQueryImport.setAttribute('integrity','sha384-ZvpUoO/+PpLXR1lu4jmpXWu80pZlYUAfxl5NsBMWOEPSjUn/6Z/hRTt8+pR6L4N2');
  jQueryImport.setAttribute('crossorigin','anonymous');
  document.head.appendChild(jQueryImport);

  var chessboardImport = document.createElement('script');
  chessboardImport.setAttribute('src','https://unpkg.com/@chrisoakman/chessboardjs@1.0.0/dist/chessboard-1.0.0.min.js');
  chessboardImport.setAttribute('integrity','sha384-8Vi8VHwn3vjQ9eUHUxex3JSN/NFqUg3QbPyX8kWyb93+8AC/pPWTzj+nHtbC5bxD');
  chessboardImport.setAttribute('crossorigin','anonymous');
  document.head.appendChild(chessboardImport);
}



function boardFENString(board) {

  var boardArr = [];
  for (r = 0; r < 8; r++) {
    var thisRank = [];
    for (f = 0; f < 8; f++) {
      thisRank.push("1");
    }
    boardArr.push(thisRank);
  }
  
  const positions = board.join(position).tuples();
  for (idx = 0; idx < positions.length; idx++) {
      const atms = positions[idx]._atoms;
      const thisFile = atms[0].toString() ;
      const thisRank = atms[1].toString() ;
      if(0 <= thisFile && thisFile <= 7 && 0 <= thisRank && thisRank <=7){
         boardArr[thisFile][thisRank] = "q";
      }
  } 

  var boardString = "";
  for (r = 7; r >= 0; r--) {
    for (f = 0; f < 8; f++) {
      boardString += boardArr[r][f];
    }
    boardString += "/";
  }
  console.log(boardString.slice(0, -1));
  return boardString.slice(0, -1);
}

function loadChessboard() {
  //setColors();
  let board = Board
    var config = {
      pieceTheme: 'https://chessboardjs.com/img/chesspieces/wikipedia/{piece}.png',
      position: boardFENString(board)
    }
    var chessboard = document.createElement('div');
    var boardName = 'board' ;
    chessboard.setAttribute('id',boardName);
    chessboard.setAttribute('style','width: 300px; margin: 10px');
    div.appendChild(chessboard);
    var board1 = Chessboard(boardName, config)
  

}

div.innerHTML = '';
div.style.overflow = 'scroll';
if (!document.head.innerHTML.includes('chessboardjs@1.0.0')) {
  alert('Since this script loads external elements, "Execute" may need to be run twice or thrice (!!) to guarantee that visualization is showing properly.');
}
loadSources();
loadChessboard();
