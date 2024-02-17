const boardConfig = {
  // Absolute location in parent (here, of the stage itself)
  grid_location: { x:10, y:150},
  // How large is each cell?
  cell_size: {x_size:80,y_size:50},
  // How many rows and columns?
  grid_dimensions: {
      // Col
      x_size:7,
      // Row
      y_size:6}}

const board = new Grid(boardConfig);
const positions = Board.join(position).tuples();
for (let idx = 0; idx < positions.length; idx++) {
  const atms = positions[idx]._atoms;
  const row = parseInt(atms[0].toString());
  const col = parseInt(atms[1].toString());
  let color = atms[2].toString();
  color = color.slice(0, color.length - 1);
  board.add({x: col, y: 5 - row}, new TextBox({text: `${color}`, 'color': `${color}`}));
}

const stage = new Stage() 
stage.add(board)
stage.render(svg)







