//KK defines  safe_malloc, safe_realloc
#include<stdio.h>
#include<stdlib.h>
 


static inline void* safe_malloc(size_t size){ 
  void* p;
  if ((p = malloc(size))==NULL){
    fprintf(stderr, "ERROR: Out of Memory\n");
    fflush(stderr);
    fprintf(stdout, "ERROR: Out of Memory\n");
    fflush(stdout);
    exit(EXIT_FAILURE); 
  }
  return p;
}

static inline  void* safe_realloc(void* ptr, size_t size){
  void* p;
  if ((p = realloc(ptr,size))==NULL){
    fprintf(stderr, "ERROR: Out of Memory\n");
    fflush(stderr);
    fprintf(stdout, "ERROR: Out of Memory\n");
    fflush(stdout);
    exit(EXIT_FAILURE); 
  }
  return p;
}

