/* 
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 *
 * Name: Yang Wu
 * Andrew ID: yangwu
 */ 
#include <stdio.h>
#include "cachelab.h"
#include "contracts.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. The REQUIRES and ENSURES from 15-122 are included
 *     for your convenience. They can be removed if you like.
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{
    REQUIRES(M > 0);
    REQUIRES(N > 0);

    //cache-oblivious algorithm
    int i,j,k,l;

    int* buffer; // for 64*64 case
    int v0,v1,v2,v3,v4,v5,v6,v7;

    if(N==32){//32*32, (4*4)*(8*8)
        for(i=0;i<32;i+=8){
            for(j=0;j<32;j+=8){
                if(i==j){
                    for(k=0;k<8;k++){
                        B[j+0][i+k]=A[i+k][j+0];
                        B[j+1][i+k]=A[i+k][j+1];
                        B[j+2][i+k]=A[i+k][j+2];
                        B[j+3][i+k]=A[i+k][j+3];
                        B[j+4][i+k]=A[i+k][j+4];
                        B[j+5][i+k]=A[i+k][j+5];
                        B[j+6][i+k]=A[i+k][j+6];
                        B[j+7][i+k]=A[i+k][j+7];
                    }
                }
                else {
                    for(k=0;k<8;k++){
                        for(l=0;l<8;l++){
                            B[j+l][i+k] = A[i+k][j+l];
                        }
                    }
                }
            }
        }
    }
    else if(N==64){//64*64, 4*8 as buffer in B
        for(i=0;i<64;i+=8){
            for(j=0;j<64;j+=8){
                for(k=0;k<8;k++){
                    buffer = &A[j+k][i];
                    v0 = buffer[0]; //first row of A
                    v1 = buffer[1];
                    v2 = buffer[2];
                    v3 = buffer[3];
                    if(k==0){
                        v4 = buffer[4];
                        v5 = buffer[5];
                        v6 = buffer[6];
                        v7 = buffer[7];
                    }
                    buffer = &B[i][j+k];
                    buffer[0] = v0;
                    buffer[64] = v1;
                    buffer[64*2] = v2;
                    buffer[64*3] = v3;
                }
                for(k=7;k>0;k--){
                    buffer = &A[j+k][i+4];
                    v0 = buffer[0];
                    v1 = buffer[1];
                    v2 = buffer[2];
                    v3 = buffer[3];

                    buffer = &B[i+4][j+k];
                    buffer[0] = v0;
                    buffer[64] = v1;
                    buffer[64*2] = v2;
                    buffer[64*3] = v3;
                }
                buffer = &B[i+4][j];
                buffer[0] = v4;
                buffer[64] = v5;
                buffer[64*2] = v6;
                buffer[64*3] = v7;
            }
        }
    }
    else{ //61*67
        for(i=0;i<67;i+=8){
            for(j=0;j<61;j+=8){
                for(k=j;k<j+8 && k<61; k++){
                    for(l=i;i<i+8 && l<67; l++){
                        B[k][l] = A[l][k];
                    }
                }
            }
        }
    }

    ENSURES(is_transpose(M, N, A, B));
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }    

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc); 

    /* Register any additional transpose functions */
    registerTransFunction(trans, trans_desc); 

}

/* 
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

