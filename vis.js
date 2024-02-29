// const boardConfig = {
//   // Absolute location in parent (here, of the stage itself)
//   grid_location: { x:10, y:150},
//   // How large is each cell?
//   cell_size: {x_size:80,y_size:50},
//   // How many rows and columns?
//   grid_dimensions: {
//       // Col
//       x_size:7,
//       // Row
//       y_size:6}}

// const board = new Grid(boardConfig);
// const positions = Board.join(position).tuples();
// for (let idx = 0; idx < positions.length; idx++) {
//   const atms = positions[idx]._atoms;
//   const row = parseInt(atms[0].toString());
//   const col = parseInt(atms[1].toString());
//   let color = atms[2].toString();
//   color = color.slice(0, color.length - 1);
//   board.add({x: col, y: 5 - row}, new TextBox({text: `${color}`, 'color': `${color}`}));
// }

// const stage = new Stage() 
// stage.add(board)
// stage.render(svg)

const boardConfig = {
  // Initial y-location, will be updated for each board
  grid_location: { x: 10, y: 150 },
  cell_size: { x_size: 80, y_size: 50 },
  grid_dimensions: {
    x_size: 7,
    y_size: 6
  }
};

const positions = Board.join(position).tuples();
const stage = new Stage();

// Function to create a new board at a specific vertical offset
function createBoardAtYOffset(yOffset) {
  let newBoardConfig = {...boardConfig, grid_location: {...boardConfig.grid_location, y: boardConfig.grid_location.y + yOffset}};
  return new Grid(newBoardConfig);
}

// Initial vertical offset, adjust based on the size of your boards and desired spacing
let verticalOffset = 0;
const verticalSpacing = 50; // Additional space between boards

for (let idx = 0; idx < positions.length; idx++) {
  const board = createBoardAtYOffset(verticalOffset);
  stage.add(board);

  // Now, place only the pieces up to the current step
  for (let j = 0; j <= idx; j++) {
    const atms = positions[j]._atoms;
    const row = parseInt(atms[0].toString());
    const col = parseInt(atms[1].toString());
    let color = atms[2].toString();
    color = color.slice(0, color.length - 1);

    board.add({x: col, y: 5 - row}, new TextBox({text: `${color}`, 'color': `${color}`}));
  }

  // Adjust the vertical offset for the next board
  verticalOffset += boardConfig.cell_size.y_size * boardConfig.grid_dimensions.y_size + verticalSpacing;
}

stage.render(svg);








