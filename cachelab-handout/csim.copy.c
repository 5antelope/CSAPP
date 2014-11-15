/**
 * Name: Yang Wu
 * Andrew ID: yangwu
 */

#include "cachelab.h"

#include <unistd.h> 
#include <stdio.h>
#include <stdlib.h> 
#include <getopt.h> 
 
typedef struct {
    int valid; 
    long tag; 
} Line;
 
typedef struct {
    Line *ptr_line;
} Set;
 
int main(int argc, char **argv){
    Set *cache;

    FILE *ptr_file; 
    
    int i;
    int j;
    int s, S, E, b; // parameters for cache

    char readline[30];

    int iSet; 
    long tag; 
    
    int isMiss;
    int isVerbose = 0; 
    
    int hit_count = 0, miss_count = 0, eviction_count = 0; 
    
    int c;
    while ((c=getopt(argc,argv,"vs:E:b:t:")) != -1) {
        switch (c) {
            case 'v': 
                isVerbose = 1;
                break;
            case 's':
                s = atoi(optarg);
                S = 1 << s;
                break;
            case 'E': 
                E = atoi(optarg); 
                break;
            case 'b':
                b = atoi(optarg);
                break;
            case 't': 
                ptr_file = fopen(optarg, "r"); 
                break;
            default:
                return 0;
        }
    }

    cache = (Set *)malloc(S * sizeof(Set));
    for (i = 0; i != S; i++) {
        cache[i].ptr_line = (Line *)malloc(E * sizeof(Line));
        for (j = 0; j != E; j++) {
            cache[i].ptr_line[j].valid = 0;
        }
    }
 
    char opt; 
    long addr;
    int size; 
 
    while (fgets(readline, 30, ptr_file)) { 
        sscanf(readline, " %c %lx,%d", &opt, &addr, &size); 
        tag = addr & (-1 << (b + s)); 
        iSet = (addr >> b) & (S - 1); 
        switch (opt) 
        { 
            case 'M':
                if (isVerbose) { 
                    printf("%c %lx,%d", opt, addr, size);
                }
                isMiss = 1;
                for (i = 0; i != E && isMiss; i++) { 
                    if (cache[iSet].ptr_line[i].valid && cache[iSet].ptr_line[i].tag == tag) { // Hit
                        isMiss = 0;
                        hit_count += 2; 
                        for (j = 1; j != i + 1; j++) {
                            cache[iSet].ptr_line[i-j+1].valid = cache[iSet].ptr_line[i-j].valid;
                            cache[iSet].ptr_line[i-j+1].tag = cache[iSet].ptr_line[i-j].tag;
                        }
                        cache[iSet].ptr_line[0].valid = 1;
                        cache[iSet].ptr_line[0].tag = tag;
                        if (isVerbose) { 
                            printf(" hit hit\n");
                        }
                    }
                }
                if (isMiss) {
                    hit_count++; 
                    miss_count++; 
                    if (isVerbose) {
                        printf(" miss");
                    }
                    if (cache[iSet].ptr_line[E-1].valid) { 
                        eviction_count++;
                        if (isVerbose) {
                            printf(" eviction");
                        }
                    }
                    for (i = 1; i != E; i++) { 
                        cache[iSet].ptr_line[E-i].valid = cache[iSet].ptr_line[E-i-1].valid;
                        cache[iSet].ptr_line[E-i].tag = cache[iSet].ptr_line[E-i-1].tag;
                    }
                    cache[iSet].ptr_line[0].valid = 1;
                    cache[iSet].ptr_line[0].tag = tag;
                    if (isVerbose) { 
                        printf(" hit\n");
                    }
                }
                break;
            case 'L':
            case 'S': 
                if (isVerbose) { 
                    printf("%c %lx,%d", opt, addr, size);
                }
                isMiss = 1;
                for (i = 0; i != E && isMiss; i++) { 
                    if (cache[iSet].ptr_line[i].valid && cache[iSet].ptr_line[i].tag == tag) { // Hit
                        isMiss = 0;
                        hit_count++;
                        for (j = 1; j != i + 1; j++) { 
                            cache[iSet].ptr_line[i-j+1].valid = cache[iSet].ptr_line[i-j].valid;
                            cache[iSet].ptr_line[i-j+1].tag = cache[iSet].ptr_line[i-j].tag;
                        }
                        cache[iSet].ptr_line[0].valid = 1;
                        cache[iSet].ptr_line[0].tag = tag;
                        if (isVerbose) { 
                            printf(" hit\n");
                        }
                    }
                }
                if (isMiss) { 
                    miss_count++;
                    if (isVerbose) { 
                        printf(" miss");
                    }
                    if (cache[iSet].ptr_line[E-1].valid) { 
                        if (isVerbose) { 
                            printf(" eviction");
                        }
                        eviction_count++;
                    }
                    for (i = 1; i != E; i++) { 
                        cache[iSet].ptr_line[E-i].valid = cache[iSet].ptr_line[E-i-1].valid;
                        cache[iSet].ptr_line[E-i].tag = cache[iSet].ptr_line[E-i-1].tag;
                    }
                    cache[iSet].ptr_line[0].valid = 1;
                    cache[iSet].ptr_line[0].tag = tag;
                    
                }
                break;
            default:
                ;
        }
    }
    printSummary(hit_count, miss_count, eviction_count); 
 
    for (i = 0; i != S; i++) {
        free(cache[i].ptr_line);
    }
    free(cache);
    fclose(ptr_file);
 
    return 0;
}
