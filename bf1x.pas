PROGRAM boolean_functions;
{$RANGECHECKS OFF}
{$OVERFLOWCHECKS OFF}
{$PACKENUM 1}
{$M 16777216,33554432}

(*
 * Copyright (c) 1988-2007 Antonio Costa.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms are permitted
 * provided that the above copyright notice and this paragraph are
 * duplicated in all such forms and that any documentation,
 * advertising materials, and other materials related to such
 * distribution and use acknowledge that the software was developed
 * by Antonio Costa. The name of the author may not be used to endorse
 * or promote products derived from this software without specific
 * prior written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
 * WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 *)
(*
   BOOLEAN FUNCTIONS - QUINE McCLUSKEY MINIMIZATION

   Version 11.3 - Local Outputs

   Made by    : ANTONIO COSTA, PORTO, DECEMBER 1986
   Modified by: ANTONIO COSTA, PORTO, AUGUST 2007
*)

CONST
  variable_max=64;
  multiple_max=64;

  term_max=32767;
  prime_max=32767;
  cube_max=32767;

  count1_max=32767;
  count2_max=32767;

  product_max=32767;

  char_max=5;

  space=' ';
  tab=CHR(9);
  marker='#';

  assign_op='=';
  invert_op='/';
  or_op='+';
  and_op='*';

  high='H';
  low='L';
  zero='0';
  one='1';
  dont_care='X';

TYPE
  signal=RECORD
           state:BOOLEAN;
           name:STRING[char_max]
         END;

  input_value=(sN,s0,s1,sX);
  input_code=PACKED ARRAY[1..variable_max] OF input_value;
  output_code=PACKED ARRAY[1..multiple_max] OF BOOLEAN;
  pointer=0..prime_max;
  pointer_table=PACKED ARRAY[1..product_max] OF pointer;

{$INCLUDE spmatbits1.inc}

VAR
  termtable:PACKED ARRAY[1..term_max] OF QWORD;
  inpsignal:ARRAY[1..variable_max] OF signal;
  outsignal:ARRAY[1..multiple_max] OF signal;
  outlevel:PACKED ARRAY[1..multiple_max] OF BOOLEAN;
  termtotal:PACKED ARRAY[1..multiple_max] OF 0..term_max;
  mterm:PACKED ARRAY[1..term_max] OF input_code;
  check,outcode:PACKED ARRAY[1..term_max] OF output_code;
  primeimp:PACKED ARRAY[0..prime_max] OF input_code;
  essential:PACKED ARRAY[1..prime_max] OF BOOLEAN;
  petrick:PACKED ARRAY[1..prime_max] OF pointer;
  count:pointer_table;
  i,j,k,l,m,n,o:LONGINT;
  out,variable,multiple,term,prime,product:LONGINT;
  flag1,flag2,table_flag,stats_flag:BOOLEAN;
  equat_flag:LONGINT;

  runtime_error_flag:BOOLEAN;
  env1,env2:jmp_buf;

PROCEDURE exit_proc;

BEGIN
IF runtime_error_flag THEN
  BEGIN
  WRITELN;
  WRITELN('***** RUNTIME ERROR: too much data or out of memory');
  WRITELN
  END;
ExitCode:=0;
ErrorAddr:=NIL
END;

FUNCTION max(A,B:LONGINT):LONGINT;

BEGIN
IF A>B THEN
  max:=A
ELSE
  max:=B
END;

{$INCLUDE spmatbits2.inc}

PROCEDURE runtime_abort;

BEGIN
WRITELN;
WRITELN('***** RUNTIME ERROR: too many sub-cubes');
WRITELN;
LONGJMP(env2,1)
END;

PROCEDURE input_data;

VAR
  inpterm,temp:BitsMatrix;
  code01,codeX:BitsMatrix;
  ones:BitsMatrix; (* vector, dim 8 *)
  group:PACKED ARRAY[0..variable_max] OF 0..count1_max;
  lin,col:LONGINT;
  c:CHAR;
  termtable_dim:LONGWORD;
  tv:QWORD;

PROCEDURE input_abort(error:LONGINT);

BEGIN
WRITE('***** INPUT ERROR: ');
CASE error OF
  0:
    WRITE('unable to read input');
  1:
    WRITE('no block marker [',marker,'] found');
  2:
    WRITE('illegal input variable');
  3:
    WRITE('too many input variables');
  4:
    WRITE('illegal output variable');
  5:
    WRITE('too many output variables');
  6:
    WRITE('wrong mode option');
  7:
    WRITE('wrong table option');
  8:
    WRITE('wrong equations option');
  9:
    WRITE('wrong statistics option');
  10:
    WRITE('illegal input term definition');
  11:
    WRITE('illegal output term definition');
  12:
    WRITE('too many input terms')
  END;
IF error>0 THEN
  WRITE(' (line ',lin:0,', column ',col:0,')');
WRITELN;
LONGJMP(env1,1)
END;

PROCEDURE read_ch(VAR ch:CHAR;error:SHORTINT);

BEGIN
IF EOF OR EOLN THEN
  input_abort(error);
READ(ch);
col:=SUCC(col)
END;

PROCEDURE read_ln(error:SHORTINT);

BEGIN
IF EOF THEN
  input_abort(error);
READLN;
col:=0;
lin:=SUCC(lin)
END;

FUNCTION uppercase(ch:CHAR):CHAR;

BEGIN
IF ch IN ['a'..'z'] THEN
  uppercase:=CHR(ORD('A')+ORD(ch)-ORD('a'))
ELSE
  uppercase:=ch
END;

PROCEDURE skip_comments(flag:BOOLEAN;error:SHORTINT);

BEGIN
IF flag THEN
  read_ln(error);
REPEAT
  WHILE EOLN DO
    read_ln(error);
  read_ch(c,error);
  read_ln(error)
UNTIL c=marker
END;

PROCEDURE get_signal(VAR s:signal;error:SHORTINT);

BEGIN
WITH s DO
  BEGIN
  name:='';
  WHILE c IN [space,tab] DO
    read_ch(c,error);
  WHILE NOT (c IN [space,tab]) OR (name='') DO
    BEGIN
    IF LENGTH(name)<char_max THEN
    IF uppercase(c) IN ['A'..'Z','0'..'9'] THEN
       name:=name+c;
    read_ch(c,error)
    END;
  REPEAT
    read_ch(c,error);
    c:=uppercase(c)
  UNTIL c IN [low,high];
  state:=c=high
  END
END;

FUNCTION term_value:QWORD;

VAR
  value,weight:QWORD;
  z:LONGINT;

BEGIN
value:=1;
weight:=1;
FOR z:=1 TO variable DO
  BEGIN
  IF GetBM(@temp,j,z)=WORD(s1) THEN
    value:=value+weight;
  weight:=2*weight
  END;
term_value:=value
END;

FUNCTION valid_output(n:QWORD):BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=BOOLEAN(GetBM(@code01,n,z))
UNTIL (z=multiple) OR flag;
valid_output:=flag
END;

PROCEDURE init_termtable;

BEGIN
termtable_dim:=0
END;

PROCEDURE set_termtable(n:QWORD;value:BOOLEAN);

VAR
  ok:BOOLEAN;
  i:LONGWORD;

BEGIN
ok:=TRUE;
i:=1;
WHILE (i<=termtable_dim) AND ok DO
  BEGIN
  IF termtable[i]<>n THEN
    i:=SUCC(i)
  ELSE
    BEGIN
    IF NOT value THEN
      BEGIN
      IF i<>termtable_dim THEN
        termtable[i]:=termtable[termtable_dim];
      termtable_dim:=PRED(termtable_dim)
      END;
    ok:=FALSE
    END
  END;
IF ok AND value THEN
  BEGIN
  termtable_dim:=SUCC(termtable_dim);
  IF termtable_dim>term_max THEN
    input_abort(12);
  termtable[termtable_dim]:=n
  END
END;

FUNCTION check_termtable(n:QWORD):BOOLEAN;

VAR
  ok:BOOLEAN;
  i:LONGWORD;

BEGIN
check_termtable:=FALSE;
ok:=TRUE;
i:=1;
WHILE (i<=termtable_dim) AND ok DO
  BEGIN
  IF termtable[i]<>n THEN
    i:=SUCC(i)
  ELSE
    BEGIN
    check_termtable:=TRUE;
    ok:=FALSE
    END
  END
END;

BEGIN
InitBM(@inpterm,2);
InitBM(@temp,2);
InitBM(@code01,1);
InitBM(@codeX,1);
InitBM(@ones,8);
lin:=1;
col:=0;
skip_comments(FALSE,1);
variable:=0;
read_ch(c,2);
REPEAT
  variable:=SUCC(variable);
  IF variable>variable_max THEN
    input_abort(3);
  get_signal(inpsignal[variable],2);
  read_ln(1);
  read_ch(c,1)
UNTIL c=marker;
read_ln(4);
multiple:=0;
read_ch(c,4);
REPEAT
  multiple:=SUCC(multiple);
  IF multiple>multiple_max THEN
    input_abort(5);
  get_signal(outsignal[multiple],4);
  REPEAT
    read_ch(c,4)
  UNTIL c IN [zero,one];
  outlevel[multiple]:=c=one;
  read_ln(1);
  read_ch(c,1)
UNTIL c=marker;
read_ln(6);
REPEAT
  read_ch(c,6)
UNTIL c IN [zero..'6'];
flag1:=c<>zero;
o:=ORD(c)-ORD(zero);
read_ln(7);
REPEAT
  read_ch(c,7)
UNTIL c IN [zero,one];
table_flag:=c=one;
read_ln(8);
REPEAT
  read_ch(c,8)
UNTIL c IN [zero..'3'];
equat_flag:=ORD(c)-ORD(zero);
read_ln(9);
REPEAT
  read_ch(c,9)
UNTIL c IN [zero,one];
stats_flag:=c=one;
skip_comments(TRUE,1);
init_termtable;
FOR i:=0 TO variable DO
  group[i]:=0;
WHILE NOT EOF DO
  BEGIN
  n:=0;
  FOR j:=1 TO variable DO
    BEGIN
    REPEAT
      read_ch(c,10);
      c:=uppercase(c)
    UNTIL c IN [zero,one,dont_care];
    CASE c OF
      zero:
        SetBM(@temp,1,j,WORD(s0));
      one:
        SetBM(@temp,1,j,WORD(s1));
      dont_care:
        BEGIN
        SetBM(@temp,1,j,WORD(sX));
        n:=SUCC(n)
        END
      END
    END;
  FOR j:=1 TO multiple DO
    BEGIN
    REPEAT
      read_ch(c,11);
      c:=uppercase(c)
    UNTIL c IN [zero,one,dont_care];
    IF outlevel[j] THEN
      SetBM(@code01,0,j,WORD(c<>zero))
    ELSE
      SetBM(@code01,0,j,WORD(c<>one));
    SetBM(@codeX,0,j,WORD(c<>dont_care))
    END;
  i:=1;
  FOR j:=1 TO n DO
    BEGIN
    k:=i;
    FOR l:=1 TO k DO
      BEGIN
      m:=1;
      WHILE GetBM(@temp,l,m)<>WORD(sX) DO
        m:=SUCC(m);
      i:=SUCC(i);
      SetBM(@temp,l,m,WORD(s0));
      CRowBM(@temp,i,@temp,l);
      SetBM(@temp,i,m,WORD(s1))
      END
    END;
  FOR j:=1 TO i DO
    BEGIN
    tv:=term_value;
    IF flag1 AND check_termtable(tv) THEN
    FOR l:=1 TO multiple DO
    CASE o OF
      1:
        BEGIN
        SetBM(@code01,tv,l,GetBM(@code01,tv,l) AND GetBM(@code01,0,l));
        SetBM(@codeX,tv,l,GetBM(@codeX,tv,l) AND GetBM(@codeX,0,l)
          OR NOTWORD(GetBM(@code01,tv,l)) OR NOTWORD(GetBM(@code01,0,l)))
        END;
      2:
        BEGIN
        SetBM(@code01,tv,l,GetBM(@code01,tv,l) AND GetBM(@code01,0,l));
        SetBM(@codeX,tv,l,GetBM(@codeX,tv,l) OR GetBM(@codeX,0,l))
        END;
      3:
        BEGIN
        SetBM(@code01,tv,l,GetBM(@code01,tv,l) AND GetBM(@code01,0,l)
          OR NOTWORD(GetBM(@codeX,tv,l)) OR NOTWORD(GetBM(@codeX,0,l)));
        SetBM(@codeX,tv,l,GetBM(@codeX,tv,l) AND GetBM(@codeX,0,l))
        END;
      4:
        BEGIN
        SetBM(@code01,tv,l,GetBM(@code01,tv,l) OR GetBM(@code01,0,l));
        SetBM(@codeX,tv,l,GetBM(@codeX,tv,l) AND GetBM(@codeX,0,l))
        END;
      5:
        BEGIN
        SetBM(@code01,tv,l,GetBM(@code01,tv,l) AND GetBM(@code01,0,l)
          OR GetBM(@code01,tv,l) AND GetBM(@codeX,tv,l)
          OR GetBM(@code01,0,l) AND GetBM(@codeX,0,l));
        SetBM(@codeX,tv,l,GetBM(@codeX,tv,l) OR GetBM(@codeX,0,l))
        END;
      6:
        BEGIN
        SetBM(@code01,tv,l,GetBM(@code01,tv,l) OR GetBM(@code01,0,l));
        SetBM(@codeX,tv,l,GetBM(@codeX,tv,l) AND GetBM(@codeX,0,l)
          OR GetBM(@code01,tv,l) AND GetBM(@codeX,tv,l)
          OR GetBM(@code01,0,l) AND GetBM(@codeX,0,l))
        END
      END
    ELSE
      BEGIN
      IF NOT check_termtable(tv) THEN
        BEGIN
        set_termtable(tv,TRUE);
        CRowBM(@inpterm,tv,@temp,j);
        l:=0;
        FOR m:=1 TO variable DO
        IF GetBM(@inpterm,tv,m)=WORD(s1) THEN
          l:=SUCC(l);
        SetBM(@ones,0,tv,l);
        group[l]:=SUCC(group[l])
        END;
      CRowBM(@code01,tv,@code01,0);
      CRowBM(@codeX,tv,@codeX,0)
      END
    END;
  read_ln(11)
  END;
IF stats_flag THEN
FOR i:=1 TO multiple DO
  termtotal[i]:=0;
term:=0;
FOR i:=0 TO variable DO
  BEGIN
  j:=1;
  WHILE (group[i]>0) AND (j<=termtable_dim) DO
    BEGIN
    tv:=termtable[j];
    IF GetBM(@ones,0,tv)=i THEN
      BEGIN
      IF valid_output(tv) THEN
        BEGIN
        term:=SUCC(term);
        FOR k:=1 to variable DO
          BEGIN
          mterm[term,k]:=INPUT_VALUE(GetBM(@inpterm,tv,k));
          outcode[term,k]:=BOOLEAN(GetBM(@code01,tv,k))
          END;
        IF stats_flag THEN
        FOR k:=1 TO multiple DO
        IF outcode[term,k] THEN
          termtotal[k]:=SUCC(termtotal[k]);
        FOR k:=1 to variable DO
          check[term,k]:=BOOLEAN(GetBM(@codeX,tv,k))
        END;
      group[i]:=PRED(group[i]);
      set_termtable(tv,FALSE)
      END
    ELSE
      j:=SUCC(j)
    END
  END;
CleanBM(@inpterm);
CleanBM(@temp);
CleanBM(@code01);
CleanBM(@codeX);
CleanBM(@ones)
END;

PROCEDURE generate_primes;

VAR
  term1,term2:PACKED ARRAY[1..cube_max] OF input_code;
  ones1,ones2:PACKED ARRAY[0..cube_max] OF 0..variable_max;
  group1,group2:PACKED ARRAY[0..variable_max] OF 0..count2_max;
  primeflag1,primeflag2:PACKED ARRAY[1..cube_max] OF BOOLEAN;

FUNCTION terms_combine:BOOLEAN;

VAR
  diff,z:LONGINT;

BEGIN
diff:=0;
z:=0;
REPEAT
  z:=SUCC(z);
  IF term1[l,z]<>term1[m,z] THEN
    diff:=SUCC(diff)
UNTIL (z=variable) OR (diff>1);
terms_combine:=diff=1
END;

FUNCTION groups_combine:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=(group1[PRED(z)]>0) AND (group1[z]>0)
UNTIL (z=variable) OR flag;
groups_combine:=flag
END;

FUNCTION found_before:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

FUNCTION equal_input_code:BOOLEAN;

VAR
  flag:BOOLEAN;
  w:LONGINT;

BEGIN
w:=0;
REPEAT
  w:=SUCC(w);
  flag:=term2[j,w]<>term2[z,w]
UNTIL (w=variable) OR flag;
equal_input_code:=NOT flag
END;

BEGIN
IF j=1 THEN
  found_before:=FALSE
ELSE
  BEGIN
  z:=0;
  REPEAT
    z:=SUCC(z);
    flag:=equal_input_code
  UNTIL (z=PRED(j)) OR flag;
  found_before:=flag
  END
END;

BEGIN
FOR i:=0 TO variable DO
  group1[i]:=0;
i:=0;
FOR j:=1 TO term DO
IF outcode[j,out] THEN
  BEGIN
  i:=SUCC(i);
  term1[i]:=mterm[j];
  o:=0;
  FOR k:=1 TO variable DO
  IF term1[i,k]=s1 THEN
    o:=SUCC(o);
  ones1[i]:=o;
  group1[o]:=SUCC(group1[o]);
  primeflag1[i]:=TRUE
  END
ELSE
  check[j,out]:=FALSE;
WRITE('##### Function ');
WITH outsignal[out] DO
  BEGIN
  IF NOT state THEN
    WRITE(invert_op);
  WRITELN(name)
  END;
WRITELN;
WRITELN('Total Local Terms     : ',i:0);
ones1[0]:=0;
ones2[0]:=0;
prime:=0;
flag1:=groups_combine;
WHILE flag1 DO
  BEGIN
  FOR l:=0 TO variable DO
    group2[l]:=0;
  j:=0;
  k:=1;
  FOR l:=1 TO i-group1[ones1[i]] DO
    BEGIN
    IF (ones1[l]>ones1[PRED(l)]) OR (l=1) THEN
      BEGIN
      k:=k+group1[ones1[l]];
      o:=PRED(k)+group1[SUCC(ones1[l])]
      END;
    FOR m:=k TO o DO
    IF terms_combine THEN
      BEGIN
      j:=SUCC(j);
      IF j>cube_max THEN
        runtime_abort;
      term2[j]:=term1[l];
      n:=1;
      WHILE term1[l,n]=term1[m,n] DO
        n:=SUCC(n);
      term2[j,n]:=sX;
      primeflag1[l]:=FALSE;
      primeflag1[m]:=FALSE;
      IF found_before THEN
        j:=PRED(j)
      ELSE
        BEGIN
        ones2[j]:=ones1[l];
        group2[ones2[j]]:=SUCC(group2[ones2[j]]);
        primeflag2[j]:=TRUE
        END
      END;
    IF primeflag1[l] THEN
      BEGIN
      prime:=SUCC(prime);
      primeimp[prime]:=term1[l]
      END
    END;
  FOR l:=k TO i DO
  IF primeflag1[l] THEN
    BEGIN
    prime:=SUCC(prime);
    primeimp[prime]:=term1[l]
    END;
  i:=j;
  IF i>0 THEN
    BEGIN
    term1:=term2;
    group1:=group2;
    flag1:=groups_combine;
    IF flag1 THEN
      BEGIN
      ones1:=ones2;
      primeflag1:=primeflag2
      END
    END
  ELSE
    flag1:=FALSE
  END;
FOR j:=1 TO i DO
  BEGIN
  prime:=SUCC(prime);
  primeimp[prime]:=term1[j]
  END;
WRITELN('Total Prime Imps      : ',prime:0)
END;

PROCEDURE reduce_primes;

VAR
  removed:PACKED ARRAY[1..prime_max] OF BOOLEAN;
  repeated:PACKED ARRAY[1..prime_max] OF 0..product_max;
  flag3:BOOLEAN;

FUNCTION in_table(x,y:LONGINT):BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
IF check[y,out] THEN
  BEGIN
  z:=0;
  REPEAT
    z:=SUCC(z);
    flag:=(primeimp[x,z]<>sX) AND (primeimp[x,z]<>mterm[y,z])
  UNTIL (z=variable) OR flag;
  in_table:=NOT flag
  END
ELSE
  in_table:=FALSE
END;

FUNCTION less_cost:BOOLEAN;

VAR
  diff,z:LONGINT;

BEGIN
diff:=0;
FOR z:=1 TO variable DO
  BEGIN
  IF primeimp[i,z]=sX THEN
    diff:=SUCC(diff);
  IF primeimp[j,z]=sX THEN
    diff:=PRED(diff)
  END;
less_cost:=diff<=0
END;

FUNCTION covers:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=in_table(i,z) AND NOT in_table(j,z)
UNTIL (z=term) OR flag;
covers:=NOT flag
END;

BEGIN
FOR i:=1 TO prime DO
  BEGIN
  essential[i]:=FALSE;
  removed[i]:=FALSE
  END;
REPEAT
  FOR j:=1 TO term DO
  IF check[j,out] THEN
    BEGIN
    k:=0;
    l:=0;
    REPEAT
      k:=SUCC(k);
      IF NOT removed[k] AND in_table(k,j) THEN
        BEGIN
        l:=SUCC(l);
        o:=k
        END
    UNTIL (l=2) OR (k=prime);
    IF l=0 THEN
      check[j,out]:=FALSE
    ELSE
    IF l=1 THEN
      BEGIN
      essential[o]:=TRUE;
      removed[o]:=TRUE;
      FOR m:=1 TO term DO
      IF in_table(o,m) THEN
        check[m,out]:=FALSE
      END
    END;
  i:=0;
  REPEAT
    i:=SUCC(i);
    flag1:=check[i,out]
  UNTIL (i=term) OR flag1;
  flag2:=FALSE;
  IF flag1 THEN
    BEGIN
    FOR i:=1 TO prime DO
    IF NOT removed[i] THEN
      BEGIN
      j:=0;
      REPEAT
        j:=SUCC(j);
        flag3:=in_table(i,j)
      UNTIL (j=term) OR flag3;
      removed[i]:=NOT flag3
      END;
    FOR i:=1 TO prime DO
    IF NOT removed[i] THEN
      BEGIN
      flag3:=FALSE;
      j:=0;
      REPEAT
        j:=SUCC(j);
        IF (j<>i) AND NOT removed[j] THEN
        IF less_cost THEN
        IF covers THEN
          BEGIN
          removed[i]:=TRUE;
          flag2:=TRUE;
          flag3:=TRUE
          END
      UNTIL (j=prime) OR flag3
      END
    END
UNTIL NOT flag2;
n:=0;
FOR i:=1 TO prime DO
IF essential[i] THEN
  n:=SUCC(n);
WRITELN('1st reduced Prime Imps: ',n:0);
n:=0;
WHILE flag1 DO
  BEGIN
  flag1:=FALSE;
  flag2:=FALSE;
  FOR i:=1 TO prime DO
    repeated[i]:=0;
  FOR i:=1 TO term DO
  IF check[i,out] THEN
  FOR k:=1 TO prime DO
  IF NOT removed[k] AND in_table(k,i) THEN
    BEGIN
    repeated[k]:=SUCC(repeated[k]);
    flag2:=TRUE
    END;
  IF flag2 THEN
    BEGIN
    i:=2;
    j:=-1;
    FOR k:=1 TO prime DO
    IF repeated[k]>i THEN
      BEGIN
      i:=repeated[k];
      o:=k;
      flag1:=TRUE
      END
    ELSE
    IF repeated[k]=i THEN
      BEGIN
      l:=0;
      FOR m:=1 TO variable DO
      IF primeimp[k,m]=sX THEN
        l:=SUCC(l);
      IF l>j THEN
        BEGIN
        o:=k;
        j:=l;
        flag1:=TRUE
        END
      END;
    IF flag1 THEN
      BEGIN
      n:=SUCC(n);
      essential[o]:=TRUE;
      removed[o]:=TRUE;
      FOR i:=1 TO term DO
      IF in_table(o,i) THEN
        check[i,out]:=FALSE
      END
    END
  END;
WRITELN('2nd reduced Prime Imps: ',n:0);
product:=0;
IF flag2 THEN
  BEGIN
  i:=1;
  FOR j:=1 TO term DO
  IF check[j,out] THEN
    BEGIN
    product:=SUCC(product);
    count[product]:=0;
    FOR l:=1 TO prime DO
    IF NOT removed[l] AND in_table(l,j) THEN
      BEGIN
      count[product]:=SUCC(count[product]);
      petrick[i]:=l;
      i:=SUCC(i)
      END
    END
  END;
WRITELN('3rd reduced Prime Imps: ',product:0)
END;

PROCEDURE petrick_primes;

VAR
  best:pointer;

BEGIN
m:=0;
FOR i:=1 TO product DO
  BEGIN
  n:=-1;
  FOR j:=1 TO count[i] DO
    BEGIN
    m:=SUCC(m);
    o:=petrick[m];
    k:=0;
    l:=0;
    REPEAT
      k:=SUCC(k);
      IF primeimp[o,k]=sX THEN
        l:=SUCC(l)
    UNTIL k>=variable-max(n-l,0);
    IF l>n THEN
      BEGIN
      n:=l;
      best:=o
      END
    END;
  essential[best]:=TRUE
  END
END;

PROCEDURE simplify_primes;

VAR
  termtable:BitsMatrix;
  bit01,bitX:PACKED ARRAY[1..variable_max] OF BOOLEAN;
  outcode1:PACKED ARRAY[1..term_max] OF output_code;

FUNCTION common_terms:BOOLEAN;

VAR
  flag:BOOLEAN;
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  flag:=(primeimp[i,z]<>sX) AND (primeimp[k,z]<>sX) AND (primeimp[i,z]<>primeimp[k,z])
UNTIL (z=variable) OR flag;
common_terms:=NOT flag
END;

PROCEDURE set_up(x:input_code);

VAR
  z:LONGINT;

BEGIN
flag2:=TRUE;
FOR z:=1 TO variable DO
CASE x[z] OF
  s0:
    BEGIN
    bit01[z]:=FALSE;
    bitX[z]:=FALSE
    END;
  s1:
    BEGIN
    bit01[z]:=TRUE;
    bitX[z]:=FALSE
    END;
  sX:
    BEGIN
    bit01[z]:=FALSE;
    bitX[z]:=TRUE;
    flag2:=FALSE
    END
  END
END;

FUNCTION term_value:QWORD;

VAR
  value,weight:QWORD;
  z:LONGINT;

BEGIN
value:=1;
weight:=1;
FOR z:=1 TO variable DO
  BEGIN
  IF bit01[z] THEN
    value:=value+weight;
  weight:=2*weight
  END;
term_value:=value
END;

PROCEDURE next_term;

VAR
  z:LONGINT;

BEGIN
z:=0;
REPEAT
  z:=SUCC(z);
  IF bitX[z] THEN
    BEGIN
    bit01[z]:=NOT bit01[z];
    flag2:=bit01[z]
    END
UNTIL (z=variable) OR flag2
END;

PROCEDURE fill_termtable;

BEGIN
set_up(primeimp[k]);
IF flag2 THEN
  SetBM(@termtable,0,term_value,1)
ELSE
REPEAT
  SetBM(@termtable,0,term_value,1);
  flag2:=FALSE;
  next_term
UNTIL NOT flag2
END;

FUNCTION redundant:BOOLEAN;

VAR
  flag:BOOLEAN;

BEGIN
set_up(primeimp[i]);
IF flag2 THEN
  redundant:=TRUE
ELSE
  BEGIN
  REPEAT
    flag2:=FALSE;
    flag:=BOOLEAN(GetBM(@termtable,0,term_value));
    IF flag THEN
      next_term
  UNTIL NOT flag OR NOT flag2;
  redundant:=flag
  END
END;

BEGIN
n:=0;
FOR i:=1 TO term_max DO
  outcode1[i]:=outcode[i];
FOR i:=1 TO prime DO
IF essential[i] THEN
  BEGIN
  flag1:=FALSE;
  FOR j:=1 TO multiple DO
  IF outcode1[i,j] THEN
    BEGIN
    flag2:=FALSE;
    k:=0;
    REPEAT
      k:=SUCC(k);
      IF (i<>k) AND essential[k] AND outcode1[k,j] THEN
      IF common_terms THEN
        BEGIN
        InitBM(@termtable,1);
        fill_termtable;
        flag2:=redundant;
        CleanBM(@termtable)
        END
    UNTIL (k=prime) OR flag2;
    outcode1[i,j]:=NOT flag2;
    flag1:=flag1 OR NOT flag2
    END;
  essential[i]:=flag1;
  IF NOT flag1 THEN
    n:=SUCC(n)
  END;
WRITELN('<Redundant> Prime Imps: ',n:0)
END;

PROCEDURE sort_primes;

BEGIN
i:=0;
FOR j:=1 TO prime DO
IF essential[j] THEN
  BEGIN
  i:=SUCC(i);
  primeimp[i]:=primeimp[j]
  END;
prime:=i;
FOR i:=1 TO prime DIV 2 DO
  BEGIN
  j:=SUCC(prime)-i;
  primeimp[0]:=primeimp[i];
  primeimp[i]:=primeimp[j];
  primeimp[j]:=primeimp[0]
  END
END;

PROCEDURE output_data;

VAR
  flag3:BOOLEAN;

PROCEDURE truth_table;

BEGIN
WRITELN('##### Truth Table');
WRITELN;
IF prime>0 THEN
  BEGIN
  FOR i:=1 TO prime DO
    BEGIN
    FOR j:=1 TO variable DO
    CASE primeimp[i,j] OF
      s0:
        WRITE(zero);
      s1:
        WRITE(one);
      sX:
        WRITE(dont_care)
      END;
    IF outlevel[out] THEN
      WRITELN(space,one)
    ELSE
      WRITELN(space,zero)
    END
  END
ELSE
  WRITELN('None');
WRITELN
END;

PROCEDURE equations;

BEGIN
WRITELN('##### Boolean Equation');
WRITELN;
WITH outsignal[out] DO
  BEGIN
  IF outlevel[out]=state THEN
    k:=LENGTH(name)
  ELSE
    BEGIN
    WRITE(invert_op);
    k:=SUCC(LENGTH(name))
    END;
  WRITE(name,assign_op)
  END;
flag1:=TRUE;
IF prime>0 THEN
  BEGIN
  flag2:=TRUE;
  j:=0;
  REPEAT
    j:=SUCC(j);
    IF NOT flag1 THEN
      BEGIN
      WRITELN;
      WRITE(space:k,or_op)
      END;
    flag1:=FALSE;
    l:=0;
    REPEAT
      l:=SUCC(l);
      flag2:=primeimp[j,l]<>sX
    UNTIL (l=variable) OR flag2;
    IF flag2 THEN
      BEGIN
      flag3:=FALSE;
      FOR l:=1 TO variable DO
      WITH inpsignal[l] DO
      IF primeimp[j,l] IN [s0,s1] THEN
        BEGIN
        IF flag3 THEN
          WRITE(and_op);
        IF (primeimp[j,l]=s0)=state THEN
          WRITE(invert_op);
        WRITE(name);
        flag3:=TRUE
        END
      END
    ELSE
      WRITE(one)
  UNTIL (j=prime) OR NOT flag2
  END;
IF flag1 THEN
  WRITE(zero);
WRITELN;
WRITELN
END;

PROCEDURE statistics;

VAR
  primetotal:PACKED ARRAY[0..variable_max] OF 0..cube_max;

FUNCTION prime_order:LONGINT;

VAR
  order,z:LONGINT;

BEGIN
order:=variable;
FOR z:=1 TO variable DO
IF primeimp[l,z]=sX THEN
 order:=PRED(order);
prime_order:=order
END;

BEGIN
WRITELN('##### Statistics');
WRITELN;
FOR j:=0 TO variable DO
  primetotal[j]:=0;
j:=0;
k:=0;
FOR l:=1 TO prime DO
  BEGIN
  j:=SUCC(j);
  m:=prime_order;
  IF m>1 THEN
    k:=k+PRED(m);
  primetotal[m]:=SUCC(primetotal[m])
  END;
j:=max(0,PRED(j));
WRITELN('Total of Boolean Operators');
WRITELN('  - OR  operators: ',j:0);
WRITELN('  - AND operators: ',k:0);
WRITELN;
WRITELN('Total of Prime Imps');
FOR j:=0 TO variable DO
  BEGIN
  WRITE('  - ',j:2,' order Prime Imps: ');
  WRITELN(primetotal[j]:0)
  END;
WRITELN;
j:=0;
k:=primetotal[0];
l:=0;
FOR m:=1 TO variable DO
  BEGIN
  j:=j+primetotal[m]*m;
  k:=k+primetotal[m];
  l:=l+SQR(primetotal[m]*m)
  END;
m:=ROUND(10000.0-10000.0*j/variable/max(1,termtotal[out]));
WRITELN('Efficiency: ',m DIV 100:0,'.',m MOD 100:0,' %');
k:=max(1,k);
m:=ROUND(100.0*j/k);
WRITELN('Average   : ',m DIV 100:0,'.',m MOD 100:0);
m:=ROUND(100.0*SQRT(SQR(j)-l)/k);
WRITELN('Deviation : ',m DIV 100:0,'.',m MOD 100:0);
WRITELN
END;

BEGIN
WRITELN('<Essential> Prime Imps: ',prime:0);
WRITELN;
IF table_flag THEN
  truth_table;
IF equat_flag>0 THEN
  equations;
IF stats_flag THEN
  statistics
END;

BEGIN
runtime_error_flag:=TRUE;
ExitProc:=@exit_proc;

IF SETJMP(env1)=0 THEN
  BEGIN
  input_data;
  WRITELN('##### Boolean Functions');
  WRITELN;
  WRITELN('Total Terms: ',term:0);
  WRITELN;
  IF term>0 THEN
    FOR out:=1 TO multiple DO
      BEGIN
      IF SETJMP(env2)=0 THEN
        BEGIN
        generate_primes;
        IF prime>0 THEN
          BEGIN
          reduce_primes;
          IF flag2 THEN
            petrick_primes;
          simplify_primes
          END;
        sort_primes;
        output_data
        END
      END
  ELSE
    WRITELN('***** INPUT ERROR: no truth table')
  END;
runtime_error_flag:=FALSE
END.

