#include<stdio.h>
#include<stdlib.h>
#include<unistd.h>

#define MAX_LENGTH 25

// F* -> C generated code
extern void Ex2_process_msg(char* buffer);

// Expects a valid file name as input
// Encrypt and decrypt its content on the fly
int main(int argc, char **argv){
  char *mod = "r+";
  int size_read, fd;
  char msg[MAX_LENGTH + 3];
  FILE *file;

  file = fopen(argv[1],mod);

  if (file == NULL){
    printf("ERROR : Cannot open input file");
    exit(1);
  }

  fd = fileno(file);

  // Fill msg buffer with at most 25 characters of the input file
  size_read = read(fd, (msg+2), MAX_LENGTH);
  
  if (size_read == -1){
    printf("ERROR : Cannot read input file");
    exit(1);
  }

  // Set the msg size
  msg[0] = size_read;
  msg[1] = 0;

  // Call encryption function
  Ex2_process_msg(msg);
  // Print result
  printf("After first encryption : %s\n\n", msg+2);
  // Call decryption function
  Ex2_process_msg(msg);
  // Print result
  printf("After second encryption : %s\n\n", msg+2);

  // Close fd and exit
  fclose(file);
  return 0;
}
