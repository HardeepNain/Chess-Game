/* Chess with: legal move safety, castling, en passant, promotion (Q),
   check/checkmate/stalemate, captured bins, fixed cell sizing,
   and UNDO support. */

const $ = (id) => document.getElementById(id);
const boardEl = $('board');
const turnEl = $('turn');
const movesEl = $('moves');
const newGameBtn = $('newGame');
const undoBtn = $('undo');            // NEW
const errBanner = $('err');
const capsByWhiteEl = $('capsByWhite');
const capsByBlackEl = $('capsByBlack');

const UNI = {
  w: { K:'\u2654', Q:'\u2655', R:'\u2656', B:'\u2657', N:'\u2658', P:'\u2659' },
  b: { K:'\u265A', Q:'\u265B', R:'\u265C', B:'\u265D', N:'\u265E', P:'\u265F' },
};
const initialFEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR";

let board = [];
let turn = 'w';
let selected = null;
let legal = [];
let lastDouble = null;
let gameOver = false;
let captured = { byWhite: [], byBlack: [] };
let history = [];                      // NEW: stack of snapshots

/* ---------- Build board UI ---------- */
function buildBoard(){
  boardEl.innerHTML = '';
  for(let r=0;r<8;r++){
    for(let c=0;c<8;c++){
      const sq = document.createElement('button');
      sq.type = 'button';
      sq.className = `square ${ (r+c)%2===0 ? 'light' : 'dark' }`;
      sq.dataset.r = r;
      sq.dataset.c = c;
      sq.setAttribute('role','gridcell');
      sq.addEventListener('click', onSquareClick);
      boardEl.appendChild(sq);
    }
  }
}

/* ---------- FEN ---------- */
function loadFEN(fen){
  board = Array.from({length:8},()=>Array(8).fill(null));
  const rows = fen.split(' ')[0].split('/');
  for(let r=0;r<8;r++){
    let file=0;
    for(const ch of rows[r]){
      if(/\d/.test(ch)){ file+=+ch; continue; }
      const color = ch===ch.toUpperCase()?'w':'b';
      const type = ch.toUpperCase();
      board[r][file] = {t:type, c:color, moved:false};
      file++;
    }
  }
  lastDouble = null;
  captured.byWhite = [];
  captured.byBlack = [];
}

/* ---------- Utilities ---------- */
const inBounds = (r,c)=> r>=0 && r<8 && c>=0 && c<8;
const at = (r,c)=> inBounds(r,c) ? board[r][c] : null;
const empty = (r,c)=> inBounds(r,c) && !board[r][c];
const ally = (r,c,clr)=> inBounds(r,c) && board[r][c] && board[r][c].c===clr;
const enemy = (r,c,clr)=> inBounds(r,c) && board[r][c] && board[r][c].c!==clr;
const algebra = (r,c)=> String.fromCharCode(97 + c) + (8 - r);

function cloneBoard(){ return board.map(row=>row.map(p=>p?{...p}:null)); }

/* Snapshot state for UNDO (NEW: also store moves HTML) */
function snapshot(){
  return {
    board: cloneBoard(),
    turn,
    selected: selected?{...selected}:null,
    legal: JSON.parse(JSON.stringify(legal)),
    lastDouble: lastDouble?{...lastDouble}:null,
    captured: { byWhite: [...captured.byWhite], byBlack: [...captured.byBlack] },
    movesHTML: movesEl.innerHTML
  };
}
function restoreSnapshot(s){
  board = s.board.map(row=>row.map(p=>p?{...p}:null));
  turn = s.turn;
  selected = s.selected?{...s.selected}:null;
  legal = JSON.parse(JSON.stringify(s.legal));
  lastDouble = s.lastDouble?{...s.lastDouble}:null;
  captured.byWhite = [...s.captured.byWhite];
  captured.byBlack = [...s.captured.byBlack];
  movesEl.innerHTML = s.movesHTML;
}

/* ---------- Attack / Check detection ---------- */
function kingPos(color){
  for(let r=0;r<8;r++)
    for(let c=0;c<8;c++)
      if(board[r][c]?.t==='K' && board[r][c].c===color) return {r,c};
  return null;
}
function attacksSquare(color, r, c){
  for(let rr=0; rr<8; rr++){
    for(let cc=0; cc<8; cc++){
      const p = board[rr][cc];
      if(!p || p.c!==color) continue;
      const m = genPseudo(rr,cc,true);
      if(m.some(x=>x.r===r && x.c===c)) return true;
    }
  }
  return false;
}
function inCheck(color){
  const kp = kingPos(color);
  return kp ? attacksSquare(color==='w'?'b':'w', kp.r, kp.c) : false;
}

/* ---------- Pseudo & Legal moves ---------- */
function genPseudo(r,c,forAttack=false){
  const p = at(r,c); if(!p) return [];
  const color = p.c, type = p.t;
  const moves = [];
  const rays = (dirs)=> {
    for(const [dr,dc] of dirs){
      let rr=r+dr, cc=c+dc;
      while(inBounds(rr,cc)){
        if(board[rr][cc]){
          if(board[rr][cc].c!==color) moves.push({r:rr,c:cc,cap:true});
          break;
        } else {
          moves.push({r:rr,c:cc});
        }
        rr+=dr; cc+=dc;
      }
    }
  };

  if(type==='P'){
    const dir = color==='w'?-1:1;
    const start = color==='w'?6:1;
    if(!forAttack){
      if(empty(r+dir,c)){
        moves.push({r:r+dir,c});
        if(r===start && empty(r+2*dir,c)) moves.push({r:r+2*dir,c,double:true});
      }
    }
    for(const dc of [-1,1]){
      const rr=r+dir, cc=c+dc;
      if(enemy(rr,cc,color)) moves.push({r:rr,c:cc,cap:true});
    }
    if(lastDouble && lastDouble.r===r && Math.abs(lastDouble.c - c)===1 && r===(color==='w'?3:4)){
      moves.push({r:r+dir, c:lastDouble.c, cap:true, ep:true});
    }
  }
  else if(type==='N'){
    const deltas = [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]];
    for(const [dr,dc] of deltas){
      const rr=r+dr, cc=c+dc;
      if(inBounds(rr,cc) && !ally(rr,cc,color))
        moves.push({r:rr,c:cc,cap: enemy(rr,cc,color)});
    }
  }
  else if(type==='B'){ rays([[1,1],[1,-1],[-1,1],[-1,-1]]); }
  else if(type==='R'){ rays([[1,0],[-1,0],[0,1],[0,-1]]); }
  else if(type==='Q'){ rays([[1,1],[1,-1],[-1,1],[-1,-1],[1,0],[-1,0],[0,1],[0,-1]]); }
  else if(type==='K'){
    for(let dr=-1; dr<=1; dr++){
      for(let dc=-1; dc<=1; dc++){
        if(dr===0 && dc===0) continue;
        const rr=r+dr, cc=c+dc;
        if(inBounds(rr,cc) && !ally(rr,cc,color))
          moves.push({r:rr,c:cc,cap: enemy(rr,cc,color)});
      }
    }
    if(!forAttack && !p.moved && !inCheck(color)){
      if(canCastle(color,'k')) moves.push({r, c:c+2, castle:'k'});
      if(canCastle(color,'q')) moves.push({r, c:c-2, castle:'q'});
    }
  }
  return moves;
}
function canCastle(color, side){
  const row = (color==='w')?7:0;
  const kC = 4;
  const rC = side==='k'?7:0;
  const step = side==='k'?1:-1;
  const rook = at(row,rC), king = at(row,kC);
  if(!king || !rook) return false;
  if(king.t!=='K' || rook.t!=='R' || king.moved || rook.moved) return false;
  for(let c=kC+step; c!==rC; c+=step){ if(!empty(row,c)) return false; }
  for(let c=kC; c!==kC+2*step; c+=step){
    if(attacksSquare(color==='w'?'b':'w', row, c)) return false;
  }
  return true;
}
function genLegal(r,c){
  const pseudo = genPseudo(r,c,false);
  const p = at(r,c); if(!p) return [];
  const color = p.c;
  const legalMoves = [];
  for(const m of pseudo){
    const snap = snapshot();             // NEW: use snapshot/restore
    applyMove({from:{r,c}, to:{r:m.r,c:m.c}, meta:m}, true);
    const safe = !inCheck(color);
    restoreSnapshot(snap);
    if(safe) legalMoves.push(m);
  }
  return legalMoves;
}

/* ---------- Apply move & capture bins ---------- */
function applyMove(m, simulate=false){
  const {from, to, meta} = m;
  const piece = at(from.r, from.c);
  const target = at(to.r, to.c);

  if(target && !simulate){
    const icon = UNI[target.c][target.t];
    if(piece.c==='w') captured.byWhite.push(icon);
    else captured.byBlack.push(icon);
  }
  if(meta?.ep && !simulate){
    const epPawn = at(from.r, to.c);
    if(epPawn){
      const icon = UNI[epPawn.c][epPawn.t];
      if(piece.c==='w') captured.byWhite.push(icon);
      else captured.byBlack.push(icon);
    }
  }
  if(meta?.ep){ board[from.r][to.c] = null; }

  board[to.r][to.c] = {...piece, moved:true};
  board[from.r][from.c] = null;

  if(meta?.castle){
    const row = to.r;
    if(meta.castle==='k'){ board[row][5] = {...board[row][7], moved:true}; board[row][7] = null; }
    else { board[row][3] = {...board[row][0], moved:true}; board[row][0] = null; }
  }

  if(board[to.r][to.c].t==='P' && (to.r===0 || to.r===7)){
    board[to.r][to.c].t = 'Q';
  }

  if(piece.t==='P' && meta?.double){ lastDouble = { r: to.r, c: to.c, dir: piece.c==='w'?-1:1 }; }
  else { lastDouble = null; }

  if(!simulate){
    logMove(piece, target, from, to, meta);
    renderCaptured();
  }
}

/* ---------- Render ---------- */
function render(){
  for(const sq of boardEl.children){
    sq.classList.remove('sel','sugg','cap','check');
    sq.innerHTML = '';
  }
  for(let r=0;r<8;r++){
    for(let c=0;c<8;c++){
      const p = board[r][c];
      if(p){
        const el = document.createElement('span');
        el.className = 'piece';
        el.textContent = UNI[p.c][p.t];
        boardEl.children[r*8+c].appendChild(el);
      }
    }
  }
  if(selected){
    boardEl.children[selected.r*8+selected.c].classList.add('sel');
    for(const m of legal){
      const i = m.r*8 + m.c;
      boardEl.children[i].classList.add(m.cap ? 'cap' : 'sugg');
    }
  }
  const kp = kingPos(turn);
  if(kp && inCheck(turn)) boardEl.children[kp.r*8+kp.c].classList.add('check');

  const status = gameStatus(turn);
  if(status==='checkmate'){
    turnEl.textContent = (turn==='w'?'Black':'White') + ' wins by checkmate';
    gameOver = true;
  } else if(status==='stalemate'){
    turnEl.textContent = 'Draw (stalemate)';
    gameOver = true;
  } else {
    turnEl.textContent = (turn==='w'?'White':'Black') + (inCheck(turn)?' to move — in check!':' to move');
    gameOver = false;
  }

  updateUndoUI();   // NEW: enable/disable Undo
}
function renderCaptured(){
  capsByWhiteEl.innerHTML = '';
  for(const icon of captured.byWhite){
    const s = document.createElement('span');
    s.className = 'cap-piece';
    s.textContent = icon;
    capsByWhiteEl.appendChild(s);
  }
  capsByBlackEl.innerHTML = '';
  for(const icon of captured.byBlack){
    const s = document.createElement('span');
    s.className = 'cap-piece';
    s.textContent = icon;
    capsByBlackEl.appendChild(s);
  }
}

/* ---------- Status helpers ---------- */
function gameStatus(colorToMove){
  const hasMove = anyLegalMove(colorToMove);
  if(hasMove) return 'ongoing';
  return inCheck(colorToMove) ? 'checkmate' : 'stalemate';
}
function anyLegalMove(color){
  for(let r=0;r<8;r++){
    for(let c=0;c<8;c++){
      const p = at(r,c);
      if(!p || p.c!==color) continue;
      const leg = genLegal(r,c);
      if(leg.length) return true;
    }
  }
  return false;
}

/* ---------- Click handling ---------- */
function onSquareClick(e){
  if(gameOver) return;
  const r = +e.currentTarget.dataset.r;
  const c = +e.currentTarget.dataset.c;
  const cellPiece = at(r,c);

  if(!selected){
    if(!cellPiece || cellPiece.c!==turn) return;
    selected = {r,c};
    legal = genLegal(r,c);
    render();
    return;
  }

  if(cellPiece && cellPiece.c===turn){
    selected = {r,c};
    legal = genLegal(r,c);
    render();
    return;
  }

  const mv = legal.find(m=>m.r===r && m.c===c);
  if(!mv){ selected=null; legal=[]; render(); return; }

  // NEW: push snapshot BEFORE applying the move
  history.push(snapshot());

  applyMove({from:{...selected}, to:{r,c}, meta:mv}, false);
  turn = (turn==='w')?'b':'w';
  selected=null; legal=[];
  render();
}

/* ---------- Move notation ---------- */
function logMove(piece, capturedPiece, from, to, meta){
  let name = piece.t==='P' ? '' : piece.t;
  let capture = (capturedPiece || meta?.ep) ? 'x' : '';
  let dest = algebra(to.r,to.c);
  let promo = (piece.t==='P' && (to.r===0 || to.r===7)) ? '=Q' : '';
  let castle = meta?.castle==='k' ? 'O-O' : (meta?.castle==='q' ? 'O-O-O' : '');
  const moveText = castle || `${name}${capture}${dest}${promo}`;
  const whiteTurn = (turn==='w');

  if(whiteTurn){
    const li = document.createElement('li');
    li.textContent = `${Math.ceil((movesEl.children.length+1)/1)}. ${moveText}`;
    movesEl.appendChild(li);
  }else{
    const last = movesEl.lastElementChild;
    last.textContent = `${last.textContent}   ${moveText}`;
  }
}

/* ---------- UNDO (NEW) ---------- */
function undo(){
  if(history.length===0) return;
  const last = history.pop();
  restoreSnapshot(last);
  gameOver = false;      // undo may revert from mate/draw to normal
  selected = null; legal = [];
  renderCaptured();
  render();
}
function updateUndoUI(){
  if(!undoBtn) return;
  undoBtn.disabled = history.length===0;
}

/* ---------- Init ---------- */
function showErr(msg, e){
  errBanner.hidden = false;
  errBanner.textContent = `⚠️ ${msg}`;
  if(e) console.error(msg, e);
}
function init(){
  if(!boardEl || !turnEl || !movesEl || !newGameBtn || !undoBtn || !capsByWhiteEl || !capsByBlackEl){
    showErr("DOM elements not found. Check IDs and ensure app.js loads with 'defer'.");
    return;
  }
  buildBoard();
  loadFEN(initialFEN);
  turn='w'; selected=null; legal=[]; gameOver=false;
  history = [];                         // NEW: clear history
  renderCaptured();
  newGameBtn.addEventListener('click', ()=>{
    loadFEN(initialFEN);
    movesEl.innerHTML='';
    turn='w'; selected=null; legal=[]; lastDouble=null; gameOver=false;
    history = [];                       // NEW: clear history
    renderCaptured();
    render();
  });
  undoBtn.addEventListener('click', undo); // NEW
  render();
}
try { init(); } catch(e){ showErr("Initialization failed. See console.", e); }