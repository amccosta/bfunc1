#include <stdlib.h>
#include <stdio.h>

#define BITS_MAX (63)

char *bin(n, bits)
unsigned long int n, bits;
{
  static char st1[BITS_MAX + 1];
  register unsigned long int i, j;

  for(i = 0, j = bits - 1; i < bits; i++, j--)
    st1[i] = ((n >> j) & 1) ? '1' : '0';
  st1[i] = '\0';
  return st1;
}

main(argc, argv)
int argc;
char *argv[];
{
  unsigned int bits, count, i;

  if(argc > 3)
    exit(1);

  if(argc == 1)
    bits = 8;
  else
  {
    if(sscanf(argv[1], "%d", &bits) != 1 || bits < 2 || bits > BITS_MAX)
      exit(1);
  }

  if(argc == 2)
    count = 8;
  else
  {
    if(sscanf(argv[2], "%d", &count) != 1 || count < 1)
      exit(1);
  }

  printf("random\n");

  printf("# inputs\n");
  for(i = 1; i <= bits; i++)
    printf("A%d high\n", bits - i);

  printf("# outputs\n");
  printf("B1 high 1\n");
  printf("B0 high 1\n");

  printf("# flags\n");
  printf("0\n0\n3\n0\n");

  printf("# table\n");
  for(i = 0; i < count; i++)
    printf("%s %c%c\n", bin(random() % ((unsigned long int) 1 << bits), bits),
           random() & 1 ? '1' : '0', random() & 1 ? '1' : '0');

  exit(0);
}
