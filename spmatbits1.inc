  BitsColList=^BitsColCell;
  BitsColCell=RECORD
                index:QWORD;
                value:LONGWORD;
                next:BitsColList
              END;

  BitsRowList=^BitsRowCell;
  BitsRowCell=RECORD
                index:QWORD;
                head:BitsColList;
                next:BitsRowList
              END;

  BitsMatrixPtr=^BitsMatrix;
  BitsMatrix=RECORD
               head:BitsRowList;
               free:BitsColList;
               dim:BYTE
             END;
