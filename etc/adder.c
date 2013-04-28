/*
 * Copyright (c) 1988, 1992 Antonio Costa, INESC-Norte.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms are permitted
 * provided that the above copyright notice and this paragraph are
 * duplicated in all such forms and that any documentation,
 * advertising materials, and other materials related to such
 * distribution and use acknowledge that the software was developed
 * by Antonio Costa, at INESC-Norte. The name of the author and
 * INESC-Norte may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
 * WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 */
#include <stdio.h>
#include <string.h>

#define BITS_MAX (10)

char *bin(n, bits)
unsigned int n, bits;
{
  static char st1[BITS_MAX + 1];
  register unsigned int i, j;

  for(i = 0, j = bits - 1; i < bits; i++, j--)
    st1[i] = ((n >> j) & 1) ? '1' : '0';
  st1[i] = '\0';
  return st1;
}

/*****
char *
bin_gray(n, bits)
  unsigned int    n, bits;
{
  static char     st2[BITS_MAX + 1];
  static char     st_gray[] = {'0', '1', '1', '0'};
  register unsigned int i, j;

  for (i = 0, j = bits - 1; i < bits; i++, j--)
    st2[i] = st_gray[(n >> j) & 3];
  st2[i] = '\0';
  return st2;
}
*****/

main(argc, argv)
int argc;
char *argv[];
{
  unsigned int bits, i, j;
  char st1[BITS_MAX + 1], st2[BITS_MAX + 1], st3[BITS_MAX + 2];

  if(argc > 2)
    exit(1);

  if(argc == 1)
    bits = 8;
  else
  {
    if(sscanf(argv[1], "%d", &bits) != 1 || bits < 2 || bits > BITS_MAX)
      exit(1);
  }

  printf("2 operand adder with no carry\n");

  printf("# inputs\n");
  for(i = 1; i <= bits; i++)
    printf("A%d high\n", bits - i);
  for(i = 1; i <= bits; i++)
    printf("B%d high\n", bits - i);

  printf("# outputs\n");
  printf("COUT high 1\n");
  for(i = 1; i <= bits; i++)
    printf("C%d high 1\n", bits - i);

  printf("# flags\n");
  printf("0\n0\n3\n0\n");

  printf("# table\n");
  for(i = 0; i < (1 << bits); i++)
    for(j = 0; j < (1 << bits); j++)
    {
      strcpy(st1, bin(i, bits));
      strcpy(st2, bin(j, bits));
      strcpy(st3, bin(i + j, bits + 1));
      printf("%s %s %s\n", st1, st2, st3);
    }

  exit(0);
}
