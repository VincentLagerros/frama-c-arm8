#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>
#include <stdbool.h>

#define boxArea(box) (box >= 1 && box <= 9 ? TRUE : FALSE)
#define validCoord(x, y) ((x < 0 || x > N-1 || y < 0 || y > N-1) ? FALSE : TRUE)
#define emptyBox(box) (box == ' ' ? TRUE : FALSE)
#define OTHER(player) (player == playerX ? playerO : playerX)
//#define playerX 'X'
//#define playerO 'O'
#define TRUE 1
#define FALSE 0
// #define open_spot ((char)' ')
#define GAMEWIN 1
#define GAMETIE 0
#define GAMELOSE -1
#define INCOMPLETE 2
#define value_type char
#define N 3

const char playerX = 'X';
const char playerO = 'O';
const char open_spot=' ';
int game_result = -15;

// **Functions**
void initialize(char board[N][N]);

void print_board(char board[N][N]);

int comp_turn(char board[N][N], char player);

int player_turn(char board[N][N], char player);

bool gridTurn(char board[N][N], char player, int grid_var);

int coordTurn(char board[N][N], char player, int x, int y);

int win_check(char board[N][N], char player);

int diag_check(char board[N][N], char player);

int tie_check(char board[N][N]);

int minNum(char board[N][N], char player);

int maxNum(char board[N][N], char player);

void new_board_check(char board[N][N], char new_board[N][N]);

void minimax(char board[N][N], char player);

bool end_game(int play);

/*@
  predicate zeroed(char *a, integer numCols) =
  orall int i; 0<=i<numCols ==> a[i] == ' ';
  predicate zeroed2d(char (*a)[N], integer numRows) =
  orall int i; 0<=i<numRows ==> zeroed(&a[i][0], N);
 */


// predicate zeroed2d{A}(char **a, integer n, integer m) =
// orall int i; 0<=i<n ==> zeroed(a[i], m);

/*@
  predicate
  HasValue(char* a, integer m, integer n, char v) =
  \exists integer i; m <= i < n && a[i] == v;
  predicate
  HasValue(char* a, integer n, char v) =
  HasValue(a, 0, n, v);
  predicate
  HasValue2d(char (*a)[N], integer numRows, char v) =
  \exists integer i; 0<=i<numRows && HasValue(&a[i][0], N, v);
*/

/*@
  predicate Won(char (*a)[N], char p) =
  (\exists integer i; 0<=i<N && orall integer j; 0<=j<N==>a[i][j]== p) ||
  (\exists integer i; 0<=i<N && orall integer j; 0<=j<N==>a[j][i]== p) ||
  (orall integer i; 0<=i<N==>a[i][i]==p) ||
  (a[2][0]==p && a[1][1]==p && a[0][2]);
  @*/



int main() {

    char board[N][N];
    initialize(board);
    print_board(board);
    while (TRUE) {
        if (player_turn(board, playerX) == TRUE)
            break;
        if (comp_turn(board, playerO) == TRUE)
            break;
    }
    return 0;
}


// Initialize board

/*@
  @ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns board[0.. (N-1) ][0..2];
  @ ensures zeroed2d(board,N);
  @*/
void initialize(char board[N][N]) {
    /*@
          @ loop invariant 0<=i<=N;
          @ loop invariant zeroed2d(board, i);
          @ loop assigns i, board[0.. (N-1) ][0..2];
          @ loop variant N-i;
          @*/
    for (int i = 0; i < N; ++i) {
        /*@ loop invariant 0<=i<= N && 0<=j<=N;
          @ loop invariant zeroed2d(board, i);
          @ loop invariant zeroed(&board[i][0],j);
          @ loop assigns j, board[0.. (N-1) ][0..2];
          @ loop variant N-j;
          @*/
        for (int j = 0; j < N; ++j) {
            board[i][j] = ' ';
        }
    }
}

/*@ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns board[0..(N-1)][0..2];
  @*/
void print_board(char board[N][N]) {
    //printf("
");
    int i;
    /*@ loop invariant 0<=i<=N; 
      @ loop assigns i, board[0.. (N-1)][0..2];
      @ loop variant N-i;
      @*/
    for (i = 0; i < N; ++i) {
        //printf("| %c | %c | %c |
", board[0][i], board[1][i], board[2][i]);
    }
    //printf("
");
}

/*@
  @ assigns 
othing;
  @ behavior GameWin:
                assumes play == GAMEWIN;
                ensures esult == TRUE;
  @ behavior GameTie:
                assumes play == GAMETIE;
                ensures esult == TRUE;
  @ behavior return_false:
                assumes play != GAMEWIN  && play != GAMETIE;
                ensures esult == FALSE;
  @*/
bool end_game(int play) {
    if (play == GAMEWIN) {
        //printf("
Winner is: Computer
");
        return TRUE;
    } else if (play == GAMETIE) {
        //printf("
Tie game
");
        return TRUE;
    }
    return FALSE;

}

/*@
  @ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns board[0.. (N-1) ][0..2], game_result;
  @*/
int comp_turn(char board[N][N], char player) {
    //printf("			Computer's turn
");

    minimax(board, player);
    print_board(board);

    int play = win_check(board, player);
    return end_game(play);

}

// Player's turn

/*@
  @ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns board[0.. (N-1) ][0..2], game_result;
  @*/
int player_turn(char board[N][N], char player) {
    int grid_var;
        /*@
          @ loop assigns grid_var, board[0.. (N-1) ][0..2], game_result;
          @*/
    while (TRUE) {
        //printf("Enter number: "); // Allows the user to pick a spot according to the diagram
        //scanf("%d", &grid_var);
        //printf("			Player's turn
");
        if (gridTurn(board, player, grid_var) == 0) // If incorrect location is chosen, make user try again
            break;

        //printf("Wrong selection, try again
");
    }

    print_board(board);

    int play = win_check(board, player);
    return end_game(play);
}

/*@
  @ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns board[0.. (N-1) ][0..2];
  @ behavior box_area:
                assumes boxArea(grid_var) == FALSE;
                ensures esult == TRUE;
  @*/

bool gridTurn(char board[N][N], char player, int grid_var) {
    if (boxArea(grid_var) == FALSE) {
        return TRUE;
    }
    //Calculates i, j coordinates on grid
    int i, j;
        /*@
          @ ensures j >= 0;
          @ ensures emptyBox(board[i][j]) == FALSE ==> TRUE;
          @ ensures grid_var < 4 ==> j == 0;
          @ ensures j == 1 ==> grid_var < 7;
          @ ensures j == 2 ==> grid_var < 10;
      @ assigns i,j, grid_var;
          @*/

    if (grid_var < 4) {
        j = 0;
    } else if (grid_var < 7) {
        j = 1;
    } else {
        j = 2;
    }
    i = grid_var - 1 - (j * N);
        /*@
          @ ensures i == grid_var-1-(j*N);
          @ ensures orall integer i, j; emptyBox(board[i][j]) == FALSE ==> TRUE;
          @*/
    if (emptyBox(board[i][j]) == FALSE) {
        return TRUE;
    }
    board[i][j] = player;

    return FALSE;
}

/*@
  @ behavior validCoord:
                assumes validCoord(x,y) == FALSE;
                ensures esult == TRUE;
  @ behavior emptyBox:
                assumes emptyBox(board[x][y]) == FALSE;
                ensures esult == TRUE;
  @ behavior return_false:
                assumes validCoord(x,y) == TRUE && emptyBox(board[x][y]) == TRUE;
                ensures board[x][y] == player;
                ensures esult == FALSE;
  complete behaviors validCoord, emptyBox, return_false;
  @*/

int coordTurn(char board[N][N], char player, int x, int y) {
    // Check if coordinates are valid
    if (validCoord(x, y) == FALSE) {
        return TRUE;
    }
    if (emptyBox(board[x][y]) == FALSE) {
        return TRUE;
    }
    board[x][y] = player;

    return FALSE;
}

/*@
  @ requires alid_read(board[0..(N-1)]+(0..2));
  @ assigns 
othing;
  @ ensures (board[0][0] != open_spot && board[0][0] == board[1][0] && board[1][0] == board[2][0]) && board[0][0] == player ==> GAMEWIN;
  @ ensures (board[0][1] != open_spot && board[0][1] == board[1][1] && board[1][1] == board[2][1]) && board[0][1] == player ==> GAMEWIN;
  @ ensures (board[0][2] != open_spot && board[0][2] == board[1][2] && board[1][2] == board[2][2]) && board[0][2] == player ==> GAMEWIN;
  @ ensures (board[0][0] != open_spot && board[0][0] == board[1][0] && board[1][0] == board[2][0]) && board[0][0] != player ==> GAMELOSE;
  @ ensures (board[0][1] != open_spot && board[0][1] == board[1][1] && board[1][1] == board[2][1]) && board[0][1] != player ==> GAMELOSE;
  @ ensures (board[0][2] != open_spot && board[0][2] == board[1][2] && board[1][2] == board[2][2]) && board[0][2] != player ==> GAMELOSE;
  @ ensures (board[0][0] != open_spot && board[0][0] == board[0][1] && board[0][1] == board[0][2]) && board[0][0] == player ==> GAMEWIN;
  @ ensures (board[1][0] != open_spot && board[1][0] == board[1][1] && board[1][1] == board[1][2]) && board[1][0] == player ==> GAMEWIN;
  @ ensures (board[2][0] != open_spot && board[2][0] == board[2][1] && board[2][1] == board[2][2]) && board[2][0] == player ==> GAMEWIN;
  @ ensures (board[0][0] != open_spot && board[0][0] == board[0][1] && board[0][1] == board[0][2]) && board[0][0] != player ==> GAMELOSE;
  @ ensures (board[1][0] != open_spot && board[1][0] == board[1][1] && board[1][1] == board[1][2]) && board[1][0] != player ==> GAMELOSE;
  @ ensures (board[2][0] != open_spot && board[2][0] == board[2][1] && board[2][1] == board[2][2]) && board[2][0] != player ==> GAMELOSE;
  @ ensures orall integer diag; diag ==> (diag != FALSE);
  @*/
int win_check(char board[N][N], char player) {
  int i, j;
  // For rows and columns

  /*@
    @ loop invariant win_check_outerLoop: 0<=i<=N;
    @ loop assigns i;
    @ loop variant N-i;
    @*/
  for (i = 0; i < N; ++i) {
    // Row
    if (board[0][i] != open_spot) {
      if (board[0][i] == board[1][i] && board[1][i] == board[2][i]) {
        return board[0][i] == player ? GAMEWIN : GAMELOSE;
      }
    }
    // Column
    if (board[i][0] != open_spot) {
      if (board[i][0] == board[i][1] && board[i][1] == board[i][2]) {
        return board[i][0] == player ? GAMEWIN : GAMELOSE;
      }
    }
  }

  //check the diagonal
  int diag = diag_check(board, player);

  if (diag != FALSE){
    return diag;
  }

  // check for a tie
  return tie_check(board);

}



/*@
  @ requires alid_read(board[0..(N-1)]+(0.. (N-1)));
  @ assigns 
othing;
  @ behavior left_true:
                assumes board[0][0] != open_spot && board[0][0] == board[1][1] && board[1][1] == board[2][2] && board[0][0] == player;
                ensures esult == GAMEWIN;
  @ behavior right_true:
                assumes board[0][0] != open_spot && board[0][0] == board[1][1] && board[1][1] == board[2][2] && board[0][0] != player;
                ensures esult == GAMELOSE;
  @ behavior left_false:
                assumes board[2][0] != open_spot && board[2][0] == board[1][1] && board[1][1] == board[0][2] && board[2][0] == player;
                ensures esult == GAMEWIN;
  @ behavior right_false:
                assumes board[2][0] != open_spot && board[2][0] == board[1][1] && board[1][1] == board[0][2] && board[2][0] != player;
                ensures esult == GAMELOSE;
  @*/

int diag_check(char board[N][N], char player){

    // Check left diagonal
    if (board[0][0] != open_spot && board[0][0] == board[1][1] && board[1][1] == board[2][2]) {
        return board[0][0] == player ? GAMEWIN : GAMELOSE;
    }

    // Check right diagonal
    if (board[2][0] != open_spot && board[2][0] == board[1][1] && board[1][1] == board[0][2]) {
        return board[2][0] == player ? GAMEWIN : GAMELOSE;
    }

    return FALSE;

}

/*@
  @ requires alid_read(board[0..(N-1)]+(0.. (N-1)));
  @ assigns 
othing;
  @ behavior incomplete_game:
                assumes HasValue2d(board, N, open_spot);
                ensures esult == INCOMPLETE;
  @ behavior tie_game:
                assumes !HasValue2d(board, N, open_spot);
                ensures esult == GAMETIE;
  @*/
int tie_check(char board[N][N]){
  // Check for a tie

  /*@
    @ loop invariant outer: 0<=i<=N;
    @ loop invariant outer_prev_rows: !HasValue2d(board, i, open_spot);
    @ loop assigns i;
        @ loop variant N-i;
    @*/
  for (int i = 0; i < N; ++i) {
    /*@
      @ loop invariant inner_range: 0<=i<=N && 0<=j<=N;
      @ loop invariant inner_prev_rows: !HasValue2d(board, i, open_spot);
      @ loop invariant inner_left: !HasValue(&board[i][0], j, open_spot);
      @ loop assigns j;
          @ loop variant N-j;
      @*/
    for (int j = 0; j < N; ++j) {
      if (board[i][j] == open_spot)
        // Incomplete board
        return INCOMPLETE;
    }
  }
  return GAMETIE;
}

/*@
  @ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns func_min_assign: game_result, board[0.. (N-1) ][0..2];
  @
  @ behavior test:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot;
           ensures esult == game_result;
  @ behavior test2:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot && Won(board,player);
           ensures game_result == GAMEWIN && esult == game_result ;
  @ behavior test3:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot && Won(board,player);
           ensures game_result == GAMELOSE && esult == game_result ;
  @ behavior test4:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot && !Won(board,playerX) && !Won(board, playerO);
           ensures game_result == GAMETIE && esult == game_result ;
  @
  @*/
int minNum(char board[N][N], char player) {
    game_result = win_check(board, OTHER(player));

    if (game_result != INCOMPLETE)
        return game_result;

    int min = 10;
  /*@
    @ loop invariant 0<=i<=N;
    @ loop assigns i, min, game_result;
    @ loop variant N-i;
    @*/
  for (int i = 0; i < N; ++i) {
    /*@
      @ loop invariant 0<=i<=N && 0<=j<=N;
      @ loop assigns j, min, game_result;
      @ loop variant N-j;
      @*/
        for (int j = 0; j < N; ++j) {
            if (board[i][j] != ' ')
                continue;
                        char new_board[N][N];
                        new_board_check( board, new_board);
                        new_board[i][j] = player;
                        int temp = maxNum(new_board, OTHER(player));
                        if (temp < min)
                                min = temp;
                }
    }
    return min;
}

/*@
  @ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns funct_assign: game_result, board[0.. (N-1) ][0..2];
  @
  @ behavior test:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot;
           ensures esult == game_result;
  @ behavior test2:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot && Won(board,player);
           ensures game_result == GAMEWIN && esult == game_result ;
  @ behavior test3:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot && Won(board,player);
           ensures game_result == GAMELOSE && esult == game_result ;
  @ behavior test4:
           assumes orall int i, j; 0<=j<=i<=N && board[i][j] != open_spot && !Won(board,playerX) && !Won(board, playerO);
           ensures game_result == GAMETIE && esult == game_result ;
  @
  @*/
int maxNum(char board[N][N], char player) {
    game_result = win_check(board, player);
    if (game_result != INCOMPLETE)
        return game_result;

    int max = -10;
        /*@
          @ loop invariant outerloop: 0<=i<=N;
          @ loop assigns outer_assign: i, max, game_result;
          @ loop variant N-i;
          @*/
    for (int i = 0; i < N; ++i) {
                /*@
                  @ loop invariant inner_loop: 0<=i<=N && 0<=j<=N;
              @ loop assigns inner_assign: j, max, game_result;
              @ loop variant N-j;
              @*/
        for (int j = 0; j < N; ++j) {
            if (board[i][j] != ' ')
                continue;
            char new_board[N][N];
            new_board_check( board, new_board);
            new_board[i][j] = player;
            int temp = minNum(new_board, OTHER(player));
            if (temp > max)
                max = temp;
        }
    }
    return max;
}

/*@
  @ requires alid_read(board[0..(N-1)]+(0..2));
  @ requires alid(new_board[0..(N-1)]+(0..2));
  @ assigns new_board[0.. (N-1) ][0..2];
  @ ensures orall int i,j; 0<=i<=N && 0<=j<=N ==> new_board[i][j] == board[i][j];
  @*/
void new_board_check(char board[N][N], char new_board[N][N]){
  /*@
    @ loop invariant 0<=x<=N;
    @ loop assigns x, new_board[0.. (N-1) ][0..2];
    @ loop variant N-x;
    @*/
  for (int x = 0; x < N; ++x) {
    /*@
      @ loop invariant 0<=x<=N && 0<=y<=N;
      @ loop assigns y, new_board[0.. (N-1) ][0..2];
      @ loop variant N-y;
      @*/
    for (int y = 0; y < N; ++y) {
      new_board[x][y] = board[x][y];
    }
  }

}

/*@
  @ requires alid(board[0..(N-1)]+(0.. (N-1)));
  @ assigns board[0.. (N-1) ][0..2], game_result;
  @*/

void minimax(char board[N][N], char player) {
    //@ assigns max, mval_i, mval_j;
    int  max, mval_i, mval_j;
    max = -10;
    /*@
      @ loop invariant minimax_first_loop: 0<=i<=N;
      @ loop assigns i, max,mval_i,mval_j, game_result;
          @ loop variant N-i;
      @*/
    for (int i = 0; i < N; ++i) {
        /*@
          @ loop invariant minimax_second_loop: 0<=i<=N && 0<=j<=N;
          @ loop assigns j, max,mval_i,mval_j, game_result;
                  @ loop variant N-j;
          @*/
        for (int j = 0; j < N; ++j) {
            if (board[i][j] != ' ')
                continue;
            char new_board[N][N];
                        new_board_check( board, new_board);
            new_board[i][j] = player;
            int temp = minNum(new_board, OTHER(player)); // Computer is at top of tree
            if (temp > max) { // Finish with the highest outcome of minNum loop
                max = temp;
                mval_i = i;
                mval_j = j;
            }
        }
    }
    if (coordTurn(board, player, mval_i, mval_j) == TRUE) {
        //printf("Minimax error
");
        exit(0);
    }
}