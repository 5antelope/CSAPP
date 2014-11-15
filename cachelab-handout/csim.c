/**
 * Name: Yang Wu
 * Andrew ID: yangwu
 */
#include "cachelab.h"

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <getopt.h>

typedef struct {
	int valid;
	long tag;
} Line;

typedef struct {
	Line *ptr_line;
} Set;

int main(int argc, char **argv) {
	Set *cache;

	FILE *ptr_file;
	
	int i;
	int j;
	int s,S,b,E; //parameters for cache
	int hit_count = 0; 
	int miss_count = 0; 
	int eviction_count = 0;

	int verbose = 0;//use as boolean flag for verbose
	int isMiss = 1;

	char readLine[50];

	char opt;
	long addr;
	int size;
	// tag and set from address
	long tag;
	int setIndex;

	int c;
	while((c=getopt(argc,argv,"vs:E:b:t:"))!=-1) {
		switch(c) {
			case 'v':
				verbose = 1;
				break;
			case 's':
				s = atoi(optarg);
				S = 1<<s; //S = 2^s
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
	for(i=0; i!=S; ++i) {
		cache[i].ptr_line = (Line *)malloc(E * sizeof(Line));
		for(j=0; j!=E; ++j) {
			cache[i].ptr_line[j].valid = 0;
		}
	}

	while(fgets(readLine, 50, ptr_file)){
		sscanf(readLine,"%c %lx,%d",&opt,&addr,&size);
		tag = addr & (-1<<(b+s));
		setIndex = (addr>>b)&(S-1);
		switch(opt){
			case 'M':
				if(verbose){
					printf("%c %lx,%d", opt, addr, size);
				}
				isMiss = 1;
				for(i=0; i!=E && isMiss; ++i){
					if(cache[setIndex].ptr_line[i].valid && cache[setIndex].ptr_line[i].tag == tag) {
						isMiss = 0;
						hit_count += 2;
						for(j=1; j!=i+1; ++j){
							cache[setIndex].ptr_line[i-j+1].valid = cache[setIndex].ptr_line[i-j].valid;
							cache[setIndex].ptr_line[i-j+1].tag = cache[setIndex].ptr_line[i-j].tag;
						}
						cache[setIndex].ptr_line[0].valid = 1;
						cache[setIndex].ptr_line[0].tag = tag;
						if(verbose){
							printf("hit hit\n");
						}
					}
				}
				if(isMiss){
					hit_count++;
					miss_count++;
					if(verbose){
						printf("miss");
					}
					if(cache[setIndex].ptr_line[E-1].valid){
						eviction_count++;
						if(verbose){
							printf("eviction");
						}
					}
					for(i=1; i!=E; ++i){
						cache[setIndex].ptr_line[E-i].valid = cache[setIndex].ptr_line[E-i-1].valid;
						cache[setIndex].ptr_line[E-i].tag = cache[setIndex].ptr_line[E-i-1].tag; 
					}
					cache[setIndex].ptr_line[0].valid = 1;
					cache[setIndex].ptr_line[0].tag = tag;
					if(verbose){
						printf("hit\n");
					}
					break;
				}
			case 'L':
			case 'S':
				if(verbose){
					printf("%c %lx,%d", opt, addr, size);
				}
				isMiss = 1;
				for(i=0; i!=E && isMiss; ++i){
					if(cache[setIndex].ptr_line[i].valid && cache[setIndex].ptr_line[i].tag == tag){
						isMiss = 0;
						hit_count++;
						for(j=1; j!=i+1; ++j){
							cache[setIndex].ptr_line[i-j+1].valid = cache[setIndex].ptr_line[i-j].valid;
							cache[setIndex].ptr_line[i-j+1].tag = cache[setIndex].ptr_line[i-j].tag;
						}
						cache[setIndex].ptr_line[0].valid = 1;
						cache[setIndex].ptr_line[0].tag = tag;
						if(verbose){
							printf("hit\n");
						}
					}
				}
				if(isMiss){
					miss_count++;
					if(verbose){
						printf("miss");
					}
					if(cache[setIndex].ptr_line[E-1].valid){
						eviction_count++;
						if(verbose){
							printf("eviction\n");
						}
					}
					for(i=1; i!=E; ++i){
						cache[setIndex].ptr_line[E-i].valid = cache[setIndex].ptr_line[E-i-1].valid;
						cache[setIndex].ptr_line[E-i].tag = cache[setIndex].ptr_line[E-i-1].tag; 
					}
					cache[setIndex].ptr_line[0].valid = 1;
					cache[setIndex].ptr_line[0].tag = tag;
					printf("\n");
				}
				break;
			default:
				;
			}
		}
		 printSummary(hit_count, miss_count, eviction_count);

		for(i=0; i!=S; ++i){
			free(cache[i].ptr_line);
		}

		free(cache);
		fclose(ptr_file);
		return 0;
	
}