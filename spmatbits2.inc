PROCEDURE InitBM(spmat:BitsMatrixPtr;dim:BYTE);

BEGIN
IF (dim<>1) AND (dim<>2) AND (dim<>4) AND (dim<>8) AND (dim<>16) THEN
  dim:=0;
spmat^.head:=NIL;
spmat^.free:=NIL;
spmat^.dim:=BYTE(dim)
END;

PROCEDURE CleanBM(spmat:BitsMatrixPtr);

VAR
  row_curr_ptr,row_prev_ptr:BitsRowList;
  col_curr_ptr,col_prev_ptr:BitsColList;

BEGIN
IF spmat^.head=NIL THEN
  EXIT;
row_curr_ptr:=spmat^.head;
WHILE row_curr_ptr<>NIL DO
  BEGIN
  col_curr_ptr:=row_curr_ptr^.head;
  WHILE col_curr_ptr<>NIL DO
    BEGIN
    col_prev_ptr:=col_curr_ptr;
    col_curr_ptr:=col_curr_ptr^.next;
    DISPOSE(col_prev_ptr)
    END;
  row_prev_ptr:=row_curr_ptr;
  row_curr_ptr:=row_curr_ptr^.next;
  DISPOSE(row_prev_ptr)
  END;
IF spmat^.free<>NIL THEN
  BEGIN
  DISPOSE(spmat^.free);
  spmat^.free:=NIL
  END
END;

FUNCTION SetValue(oldvalue:LONGWORD;value:LONGWORD;dim:BYTE;icol:BYTE):LONGWORD;

VAR
  outvalue:LONGWORD;

BEGIN
outvalue:=oldvalue;
IF dim=1 THEN
  outvalue:=outvalue AND NOT(LONGWORD(1) SHL icol)
ELSE IF dim=2 THEN
  BEGIN
  icol:=icol SHL 1;
  outvalue:=outvalue AND NOT(LONGWORD(3) SHL icol)
  END
ELSE IF dim=4 THEN
  BEGIN
  icol:=icol SHL 2;
  outvalue:=outvalue AND NOT(LONGWORD(15) SHL icol)
  END
ELSE IF dim=8 THEN
  BEGIN
  icol:=icol SHL 3;
  outvalue:=outvalue AND NOT(LONGWORD(255) SHL icol)
  END
ELSE IF dim=16 THEN
  BEGIN
  icol:=icol SHL 4;
  outvalue:=outvalue AND NOT(LONGWORD(65535) SHL icol)
  END;
IF value>0 THEN
  SetValue:=outvalue OR (value SHL icol)
ELSE
  SetValue:=outvalue
END;

FUNCTION GetValue(oldvalue:LONGWORD;dim:BYTE;icol:BYTE):WORD;

BEGIN
IF dim=1 THEN
  GetValue:=(oldvalue SHR icol) AND WORD(1)
ELSE IF dim=2 THEN
  BEGIN
  icol:=icol SHL 1;
  GetValue:=(oldvalue SHR icol) AND WORD(3)
  END
ELSE IF dim=4 THEN
  BEGIN
  icol:=icol SHL 2;
  GetValue:=(oldvalue SHR icol) AND WORD(15)
  END
ELSE IF dim=8 THEN
  BEGIN
  icol:=icol SHL 3;
  GetValue:=(oldvalue SHR icol) AND WORD(255)
  END
ELSE IF dim=16 THEN
  BEGIN
  icol:=icol SHL 4;
  GetValue:=(oldvalue SHR icol) AND WORD(65535)
  END
END;

PROCEDURE SetBM(spmat:BitsMatrixPtr;row:QWORD;col:QWORD;val:WORD);

CONST
  sizevalue=32;

VAR
  dim,icol:LONGWORD;
  value:LONGWORD;
  row_curr_ptr,row_prev_ptr:BitsRowList;
  col_curr_ptr,col_prev_ptr:BitsColList;
  continue:BOOLEAN;

BEGIN
dim:=spmat^.dim;
icol:=col AND ((sizevalue DIV dim)-1);
col:=(col * dim) DIV sizevalue;
value:=LONGWORD(val AND ((1 SHL dim)-1));
IF spmat^.head=NIL THEN (* no entries! *)
  BEGIN
  IF value=0 THEN
    EXIT;
  (* create entry *)
  IF spmat^.free<>NIL THEN
    BEGIN
    col_curr_ptr:=spmat^.free;
    spmat^.free:=NIL
    END
  ELSE
    NEW(col_curr_ptr);
  col_curr_ptr^.index:=col;
  col_curr_ptr^.value:=SetValue(0,value,dim,icol);
  col_curr_ptr^.next:=NIL;
  NEW(row_curr_ptr);
  row_curr_ptr^.index:=row;
  row_curr_ptr^.head:=col_curr_ptr;
  row_curr_ptr^.next:=NIL;
  spmat^.head:=row_curr_ptr;
  EXIT
  END;
(* entry exists! *)
row_prev_ptr:=NIL;
row_curr_ptr:=spmat^.head;
continue:=TRUE;
WHILE continue AND (row_curr_ptr<>NIL) DO
  BEGIN
  IF row_curr_ptr^.index=row THEN
    continue:=FALSE
  ELSE
    BEGIN
    row_prev_ptr:=row_curr_ptr;
    row_curr_ptr:=row_curr_ptr^.next
    END
  END;
IF row_curr_ptr<>NIL THEN (* row exists! *)
  BEGIN
  col_prev_ptr:=NIL;
  col_curr_ptr:=row_curr_ptr^.head;
  continue:=TRUE;
  WHILE continue AND (col_curr_ptr<>NIL) DO
    BEGIN
    IF col_curr_ptr^.index=col THEN
      continue:=FALSE
    ELSE
      BEGIN
      col_prev_ptr:=col_curr_ptr;
      col_curr_ptr:=col_curr_ptr^.next
      END
    END;
  IF col_curr_ptr<> NIL THEN (* column exists! *)
    BEGIN
    (* keep entry *)
    col_curr_ptr^.value:=SetValue(col_curr_ptr^.value,value,dim,icol);
    IF col_curr_ptr^.value<>0 THEN
      EXIT;
    (* delete column entry *)
    IF col_prev_ptr<>NIL THEN (* not first column entry *)
      BEGIN
      col_prev_ptr^.next:=col_curr_ptr^.next;
      IF spmat^.free<>NIL THEN
        DISPOSE(col_curr_ptr)
      ELSE
        spmat^.free:=col_curr_ptr;
      EXIT
      END;
    IF col_curr_ptr^.next<>NIL THEN (* first and not unique column entry *)
      BEGIN
      row_curr_ptr^.head:=col_curr_ptr^.next;
      IF spmat^.free<>NIL THEN
        DISPOSE(col_curr_ptr)
      ELSE
        spmat^.free:=col_curr_ptr;
      EXIT
      END;
    (* first and unique column entry *)
    IF spmat^.free<>NIL THEN
      DISPOSE(col_curr_ptr)
    ELSE
      spmat^.free:=col_curr_ptr;
    (* clean row *)
    IF row_prev_ptr<>NIL THEN (* not first row entry *)
      BEGIN
      row_prev_ptr^.next:=row_curr_ptr^.next;
      DISPOSE(row_curr_ptr);
      EXIT
      END;
    (* first row entry *)
    spmat^.head:=row_curr_ptr^.next;
    DISPOSE(row_curr_ptr);
    EXIT
    END;
  (* column not exists! *)
  IF value=0 THEN (* ignore entry *)
    EXIT;
  (* create entry *)
  IF spmat^.free<>NIL THEN
    BEGIN
    col_curr_ptr:=spmat^.free;
    spmat^.free:=NIL
    END
  ELSE
    NEW(col_curr_ptr);
  col_curr_ptr^.index:=col;
  col_curr_ptr^.value:=SetValue(0,value,dim,icol);
  col_curr_ptr^.next:=row_curr_ptr^.head;
  row_curr_ptr^.head:=col_curr_ptr;
  EXIT
  END;
(* row not exists! *)
IF value=0 THEN (* ignore entry *)
  EXIT;
(* create entry *)
IF spmat^.free<>NIL THEN
  BEGIN
  col_curr_ptr:=spmat^.free;
  spmat^.free:=NIL
  END
ELSE
  NEW(col_curr_ptr);
col_curr_ptr^.index:=col;
col_curr_ptr^.value:=SetValue(0,value,dim,icol);
col_curr_ptr^.next:=NIL;
NEW(row_curr_ptr);
row_curr_ptr^.index:=row;
row_curr_ptr^.head:=col_curr_ptr;
row_curr_ptr^.next:=spmat^.head;
spmat^.head:=row_curr_ptr
END;

FUNCTION GetBM(spmat:BitsMatrixPtr;row:QWORD;col:QWORD):WORD;

CONST
  sizevalue=32;

VAR
  dim,icol:LONGWORD;
  row_curr_ptr:BitsRowList;
  col_curr_ptr:BitsColList;
  continue:BOOLEAN;

BEGIN
dim:=spmat^.dim;
icol:=col AND ((sizevalue DIV dim)-1);
col:=(col * dim) DIV sizevalue;
IF spmat^.head=NIL THEN (* no entries! *)
  BEGIN
  GetBM:=0;
  EXIT
  END;
(* entry exists! *)
row_curr_ptr:=spmat^.head;
continue:=TRUE;
WHILE continue AND (row_curr_ptr<>NIL) DO
  BEGIN
  IF row_curr_ptr^.index=row THEN
    continue:=FALSE
  ELSE
    row_curr_ptr:=row_curr_ptr^.next
  END;
IF row_curr_ptr<>NIL THEN (* row exists! *)
  BEGIN
  col_curr_ptr:=row_curr_ptr^.head;
  WHILE col_curr_ptr<>NIL DO
    BEGIN
    IF col_curr_ptr^.index=col THEN
      BEGIN
      GetBM:=GetValue(col_curr_ptr^.value,dim,icol);
      EXIT
      END;
    col_curr_ptr:=col_curr_ptr^.next
    END;
  GetBM:=0;
  EXIT
  END;
(* row not exists! *)
GetBM:=0
END;

PROCEDURE CRowBM(dst_spmat:BitsMatrixPtr;dst_row:QWORD;
                 src_spmat:BitsMatrixPtr;src_row:QWORD);

VAR
  src_row_curr_ptr:BitsRowList;
  dst_row_curr_ptr,dst_row_prev_ptr:BitsRowList;
  src_col_curr_ptr:BitsColList;
  dst_col_curr_ptr,dst_col_prev_ptr:BitsColList;
  src_row_exists,dst_row_exists,continue:BOOLEAN;

BEGIN
src_row_exists:=TRUE;
IF src_spmat^.head=NIL THEN
  src_row_exists:=FALSE
ELSE
  BEGIN
  src_row_curr_ptr:=src_spmat^.head;
  continue:=TRUE;
  WHILE continue AND (src_row_curr_ptr<>NIL) DO
    BEGIN
    IF src_row_curr_ptr^.index=src_row THEN
      continue:=FALSE
    ELSE
      src_row_curr_ptr:=src_row_curr_ptr^.next
    END;
  IF src_row_curr_ptr=NIL THEN
    src_row_exists:=FALSE
  END;
dst_row_exists:=TRUE;
IF dst_spmat^.head=NIL THEN
  dst_row_exists:=FALSE
ELSE
  BEGIN
  dst_row_prev_ptr:=NIL;
  dst_row_curr_ptr:=dst_spmat^.head;
  continue:=TRUE;
  WHILE continue AND (dst_row_curr_ptr<>NIL) DO
    BEGIN
    IF dst_row_curr_ptr^.index=dst_row THEN
      continue:=FALSE
    ELSE
      BEGIN
      dst_row_prev_ptr:=dst_row_curr_ptr;
      dst_row_curr_ptr:=dst_row_curr_ptr^.next
      END
    END;
  IF dst_row_curr_ptr=NIL THEN
    dst_row_exists:=FALSE
  END;
IF NOT src_row_exists AND NOT dst_row_exists THEN
  EXIT;
IF NOT src_row_exists THEN (* only dst row exists *)
  BEGIN (* remove dst row *)
  dst_col_curr_ptr:=dst_row_curr_ptr^.head;
  WHILE dst_col_curr_ptr<>NIL DO
    BEGIN
    dst_col_prev_ptr:=dst_col_curr_ptr;
    dst_col_curr_ptr:=dst_col_curr_ptr^.next;
    IF dst_spmat^.free<>NIL THEN
      DISPOSE(dst_col_prev_ptr)
    ELSE
      dst_spmat^.free:=dst_col_prev_ptr
    END;
  IF dst_row_prev_ptr<>NIL THEN
    dst_row_prev_ptr^.next:=dst_row_curr_ptr^.next
  ELSE
    dst_spmat^.head:=dst_row_curr_ptr^.next;
  DISPOSE(dst_row_curr_ptr);
  EXIT
  END;
IF NOT dst_row_exists THEN (* only src row exists *)
  BEGIN (* create dst row *)
  src_col_curr_ptr:=src_row_curr_ptr^.head;
  NEW(dst_row_curr_ptr);
  dst_row_curr_ptr^.index:=dst_row;
  dst_row_curr_ptr^.next:=dst_spmat^.head;
  dst_spmat^.head:=dst_row_curr_ptr;
  IF dst_spmat^.free<>NIL THEN
    BEGIN
    dst_col_curr_ptr:=dst_spmat^.free;
    dst_spmat^.free:=NIL
    END
  ELSE
    NEW(dst_col_curr_ptr);
  dst_row_curr_ptr^.head:=dst_col_curr_ptr;
  dst_col_curr_ptr^.index:=src_col_curr_ptr^.index;
  dst_col_curr_ptr^.value:=src_col_curr_ptr^.value;
  dst_col_curr_ptr^.next:=NIL;
  dst_col_prev_ptr:=dst_col_curr_ptr;
  src_col_curr_ptr:=src_col_curr_ptr^.next;
  WHILE src_col_curr_ptr<>NIL DO
    BEGIN
    NEW(dst_col_curr_ptr);
    dst_col_curr_ptr^.index:=src_col_curr_ptr^.index;
    dst_col_curr_ptr^.value:=src_col_curr_ptr^.value;
    dst_col_curr_ptr^.next:=NIL;
    dst_col_prev_ptr^.next:=dst_col_curr_ptr;
    dst_col_prev_ptr:=dst_col_curr_ptr;
    src_col_curr_ptr:=src_col_curr_ptr^.next
    END;
  EXIT
  END;
  (* src and dst rows exist *)
  src_col_curr_ptr:=src_row_curr_ptr^.head;
  dst_col_curr_ptr:=dst_row_curr_ptr^.head;
  dst_row_curr_ptr^.index:=dst_row;
  dst_col_prev_ptr:=NIL;
  WHILE src_col_curr_ptr<>NIL DO
    BEGIN
    IF dst_col_curr_ptr=NIL THEN
      BEGIN
      NEW(dst_col_curr_ptr);
      dst_col_curr_ptr^.next:=NIL;
      IF dst_col_prev_ptr<>NIL THEN
        dst_col_prev_ptr^.next:=dst_col_curr_ptr
      END;
    dst_col_curr_ptr^.index:=src_col_curr_ptr^.index;
    dst_col_curr_ptr^.value:=src_col_curr_ptr^.value;
    dst_col_prev_ptr:=dst_col_curr_ptr;
    src_col_curr_ptr:=src_col_curr_ptr^.next;
    dst_col_curr_ptr:=dst_col_curr_ptr^.next
    END;
  WHILE dst_col_curr_ptr<>NIL DO (* remove extra columns *)
    BEGIN
    dst_col_prev_ptr:=dst_col_curr_ptr;
    dst_col_curr_ptr:=dst_col_curr_ptr^.next;
    DISPOSE(dst_col_prev_ptr)
    END
END;

FUNCTION NOTWORD(w:WORD):WORD;

BEGIN
NOTWORD:=WORD(w=0)
END;
