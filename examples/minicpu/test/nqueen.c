#define   NUM_QUEENS     7
#define   FALSE          0
#define   TRUE      	 1

typedef int BoardPosition;

int Threatens(int x, int y, BoardPosition *board, int numPiecesPlaced);
void PrintSolution(BoardPosition *board, int numQueens, int solutionsFound);
void FindSolution(BoardPosition *board, int piecesPlaced, int *solutionsFound);

int main() {
  BoardPosition board[NUM_QUEENS];
  int piecesPlaced = 0;
  int solutionsFound = 0;


  FindSolution(board, piecesPlaced, &solutionsFound);  
  printf("\n%d solutions found, program terminated successfully.\n", solutionsFound);  
  
  exit(2);
}

int Threatens(int x, int y, BoardPosition *board, int numPiecesPlaced)  {

  int i = 0;
  int threats = FALSE;   /* set if threat detected */ 

  int temp;

  while ((i < numPiecesPlaced) && (threats == FALSE)) {
    if (board[i] == y)    /* test rows */
      threats = TRUE;

    /* now test diagonals */
    temp = x-i;
    if ((y == (board[i]-temp)) || (y == (board[i]+temp)))
      threats = TRUE;

    ++i;
  }

  return threats;

}

void FindSolution(BoardPosition *board, int piecesPlaced, int *solutionsFound) {

  int i;

  for (i=0; i<NUM_QUEENS; ++i) {
    if (!Threatens(piecesPlaced, i, board, piecesPlaced)) {
      board[piecesPlaced] = i;   /* record it */

      if (piecesPlaced == (NUM_QUEENS-1)) {
	PrintSolution(board, NUM_QUEENS, *solutionsFound); 
	++(*solutionsFound);
      }

      FindSolution(board, piecesPlaced+1, solutionsFound);
    }
  }

  return;

}

void PrintSolution(BoardPosition *board, int numQueens, int solutionsFound) {

  int i;


  printf("%3d   |   ", solutionsFound);

  for (i = 0; i<numQueens; ++i) {
    printf("(%d,%d), ", i, board[i]);
  }

  printf("\n");
}
