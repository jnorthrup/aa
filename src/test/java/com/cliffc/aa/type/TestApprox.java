package com.cliffc.aa.type;

import com.cliffc.aa.Env;
import org.junit.Test;

import java.util.HashMap;

import static org.junit.Assert.*;


public class TestApprox {
  // temp/junk holder for "instant" junits, when debugged moved into other tests
  @Test public void testType() {
  }

  // Check TypeStruct.meet for a more complex recursive case
  @Test public void testTSMeet() {
    Object dummy0 = TypeStruct.TYPES;
    Object dummy1 = TypeMemPtr.TYPES;
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);

    // Build two structs pointing to each other.
    //   -> [,int] -> * -> [,flt] -> * ->
    TypeFld fbint = TypeFld.make("b",TypeInt.INT64,1);
    TypeFld fbflt = TypeFld.make("b",TypeFlt.FLT64,1);
    Type.RECURSIVE_MEET++;
    TypeFld[] flds0 = TypeFlds.ts(TypeFld.malloc("a",null,0), fbint);
    TypeFld[] flds1 = TypeFlds.ts(TypeFld.malloc("a",null,0), fbflt);
    TypeStruct t0 = TypeStruct.malloc("",false,flds0,true);
    TypeStruct t1 = TypeStruct.malloc("",false,flds1,true);
    t0._hash = t0.compute_hash();  t0._cyclic = true;
    t1._hash = t1.compute_hash();  t1._cyclic = true;
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    t0.fld(0).setX(p1           );
    t1.fld(0).setX(p0           );
    Type.RECURSIVE_MEET--;
    t0 = t0.install_cyclic(t0.reachable());

    // Meet them
    TypeStruct mt = (TypeStruct)t0.meet(t1);

    // End result should be a cycle of length 1: [,real] -> * ->
    // And NOT: [,real] -> * -> [,real] -> * ->
    assertEquals(Type.REAL,mt.at(1));
    TypeMemPtr pmt = (TypeMemPtr)mt.at(0);
    assertSame(mt,pmt._obj);
    TypeStruct head = mt.repeats_in_cycles();
    assertNull(head);
  }

  // Test approximating infinite recursive types.  Most simple test case: a
  // single linked-list chain of depth == CUTOFF.
  @Test public void testApprox1() {
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);

    // Build a depth-CUTOFF linked list chain
    TypeStruct t0 = TypeStruct.make(TypeFld.make("a",Type.XNIL      ,0),
                                    TypeFld.make("b",TypeInt.con(99),1));
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    HashMap<Type,Integer> ds = p0.depth();
    assertEquals(0,(int)ds.get(t0));

    TypeStruct t1 = TypeStruct.make(TypeFld.make("a",p0,0), TypeFld.make("b",TypeInt.con(98),1));
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    ds = p1.depth();
    assertEquals(1,(int)ds.get(t0));
    assertEquals(0,(int)ds.get(t1));
    assertEquals(0,(int)ds.get(p0));

    TypeStruct t2 = TypeStruct.make(TypeFld.make("a",p1,0), TypeFld.make("b",TypeInt.con(97),1));
    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
    ds = p2.depth();
    assertEquals(2,(int)ds.get(t0));

    TypeStruct t3 = TypeStruct.make(TypeFld.make("a",p2,0), TypeFld.make("b",TypeInt.con(96),1));
    TypeMemPtr p3 = TypeMemPtr.make(alias0,t3);
    ds = p3.depth();
    assertEquals(CUTOFF  ,(int)ds.get(t0));
    assertEquals(CUTOFF-1,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(t2));
    assertEquals(0,(int)ds.get(t3));
    // No single depth is beyond cutoff
    assertEquals(CUTOFF,TypeMemPtr.max(alias0,ds));

    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
    // graph, except every edge to a type at depth CUTOFF is replaced with the
    // X clone.

    // original, too deep
    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> nil

    // replace ptrs to t0 with ptrs to t1
    // t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*

    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
    // t3[,99] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}

    TypeStruct tax = t3.approx(CUTOFF,alias0);
    TypeMemPtr pax = TypeMemPtr.make(alias0,tax);
    HashMap<Type,Integer> ds2 = pax.depth();
    assertEquals(CUTOFF,TypeMemPtr.max(alias0,ds2));
    TypeMemPtr txp1 = (TypeMemPtr)tax.at(0);
    assertEquals(0,(int)ds2.get(txp1));
    TypeStruct txs1 = (TypeStruct)txp1._obj;
    assertEquals(1,(int)ds2.get(txs1));
    TypeMemPtr txp2 = (TypeMemPtr)txs1.at(0);
    assertEquals(1,(int)ds2.get(txp2));
    TypeStruct txs2 = (TypeStruct)txp2._obj;
    assertEquals(2,(int)ds2.get(txs2));
    assertEquals(TypeInt.NINT8,txs2.at(1));
    TypeMemPtr txp3 = (TypeMemPtr)txs2.at(0);
    assertEquals(2,(int)ds2.get(txp3));
    // Weakened expected results after NIL expands to [0]->obj
    assertEquals(txs2,txp3._obj);
    //assertEquals(TypeObj.OBJ,txp3._obj);

    assertTrue(t3.isa(tax));
  }

  // Test approximating infinite recursive types.  End of chain is already
  // cyclic, and we add a few more depth.
  @Test public void testApprox2() {
    final int CUTOFF = 3;
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);
    BitsAlias alias = BitsAlias.make0(alias0);

    // p3 -> t3[,99] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*

    // Build two structs pointing to each other
    Object dummy0 = TypeStruct.TYPES;
    Object dummy1 = TypeMemPtr.TYPES;
    Type.RECURSIVE_MEET++;
    TypeFld[] flds0 = TypeFlds.ts(TypeFld.malloc("a",null,0), TypeFld.malloc("b",null,1));
    TypeFld[] flds1 = TypeFlds.ts(TypeFld.malloc("a",null,0), TypeFld.malloc("b",null,1));
    TypeStruct t0 = TypeStruct.malloc("",false,flds0,true);
    TypeStruct t1 = TypeStruct.malloc("",false,flds1,true);
    t0._hash = t0.compute_hash();  t0._cyclic = true;
    t1._hash = t1.compute_hash();  t1._cyclic = true;
    TypeMemPtr p0 = TypeMemPtr.make(alias0,t0);
    TypeMemPtr p1 = TypeMemPtr.make(alias0,t1);
    t0.fld(0).setX(p1           );
    t0.fld(1).setX(TypeInt.INT64);
    t1.fld(0).setX(p0           );
    t1.fld(1).setX(TypeFlt.FLT64);
    Type.RECURSIVE_MEET--;
    t0 = t0.install_cyclic(t0.reachable());
    p1 = (TypeMemPtr)t0.at(0);

    HashMap<Type,Integer> ds = p1.depth();
    assertEquals(1,(int)ds.get(t0));
    assertEquals(0,(int)ds.get(t1));

    // Build a depth-CUTOFF linked list chain
    TypeStruct t2 = TypeStruct.make(TypeFld.make("a",p1,0), TypeFld.make("b",TypeInt.con(99),1));
    TypeMemPtr p2 = TypeMemPtr.make(alias0,t2);
    ds = p2.depth();
    assertEquals(2,(int)ds.get(t0));

    TypeStruct t3 = TypeStruct.make(TypeFld.make("a",p2,0), TypeFld.make("b",TypeInt.con(98),1));
    TypeMemPtr p3 = TypeMemPtr.make(alias0,t3);
    ds = p3.depth();
    assertEquals(CUTOFF  ,(int)ds.get(t0));
    assertEquals(CUTOFF-1,(int)ds.get(t1));
    assertEquals(1,(int)ds.get(t2));
    assertEquals(0,(int)ds.get(t3));
    // No single depth is beyond cutoff
    assertEquals(CUTOFF,TypeMemPtr.max(alias0,ds));

    // For all TypeStruct X at depth CUTOFF-1, make a clone of X and X's sub-
    // graph, except every edge to a type at depth CUTOFF is replaced with the
    // X clone.

    // original, too deep
    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t0[,int] -> p1*

    // replace ptrs to t0 with ptrs to t1
    // t3[,98] -> p2 -> t2[,99] -> p1 -> t1[,flt] -> p0 -> t1*

    // collapse redundant ptrs to t1, and MEET t0-tail and t1-tail
    // t3[,98] -> p2 -> t2[,99] -> {p0,p1} -> t1[,{flt&int}] -> {p0,p1}

    TypeStruct tax = t3.approx(CUTOFF,alias0);
    TypeMemPtr pax = TypeMemPtr.make(alias0,tax);

    HashMap<Type,Integer> ds2 = pax.depth();
    assertEquals(CUTOFF-1,TypeMemPtr.max(alias0,ds2));
    TypeMemPtr txp1 = (TypeMemPtr)tax.at(0);
    assertEquals(0,(int)ds2.get(txp1));
    TypeStruct txs1 = (TypeStruct)txp1._obj;
    assertEquals(1,(int)ds2.get(txs1));
    TypeMemPtr txp2 = (TypeMemPtr)txs1.at(0);
    assertEquals(1,(int)ds2.get(txp2));
    TypeStruct txs2 = (TypeStruct)txp2._obj;
    assertEquals(CUTOFF-1,(int)ds2.get(txs2));
    assertEquals(Type.REAL,txs2.at(1));
    TypeMemPtr txp3 = (TypeMemPtr)txs2.at(0);
    // Pointer-equals; 'equals()' is not good enough
    assertSame(txp2, txp3);
    assertSame(txs2, txp3._obj);
    assertTrue(t3.isa(tax));

    // Add another layer, and approx again
    TypeStruct t4 = TypeStruct.make(TypeFld.make("a",pax,0), TypeFld.make("b",TypeInt.con(97),1));
    TypeMemPtr p4 = TypeMemPtr.make(alias0,t4);
    ds = p4.depth();
    assertEquals(CUTOFF,(int)ds.get(txs2)); // Structure too deep
    TypeStruct tax4 = t4.approx(CUTOFF,alias0);
    TypeMemPtr pax4 = TypeMemPtr.make(alias0,tax4);

    ds2 = pax4.depth();
    assertEquals(CUTOFF-1,TypeMemPtr.max(alias0,ds2));
    TypeMemPtr t4p1 = (TypeMemPtr)tax4.at(0);
    assertEquals(0,(int)ds2.get(t4p1));
    TypeStruct t4s1 = (TypeStruct)t4p1._obj;
    assertEquals(1,(int)ds2.get(t4s1));
    TypeMemPtr t4p2 = (TypeMemPtr)t4s1.at(0);
    assertEquals(1,(int)ds2.get(t4p2));
    TypeStruct t4s2 = (TypeStruct)t4p2._obj;
    assertEquals(CUTOFF-1,(int)ds2.get(t4s2));
    assertEquals(Type.REAL,t4s2.at(1));
    TypeMemPtr t4p3 = (TypeMemPtr)t4s2.at(0);
    assertEquals(1,(int)ds2.get(t4p3));
    assertEquals(t4s2,t4p3._obj);
    assertTrue(t4.isa(tax4));
  }

  // Interleaving unrelated type X, and approximating type A which is too deep.
  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
  // Approx:
  // A0 -> (X0 <-> X1) -> A1 -> X2 -> A23-> (X35<-> X45) -> A23
  @Test public void testApprox3() {
    int alias0 = BitsAlias.new_alias(BitsAlias.REC);
    int alias1 = BitsAlias.new_alias(BitsAlias.REC);

    // ......................................................... -> X5
    Type str_x5 = TypeStr.con("X5");
    TypeStruct  x5 = TypeStruct.make(TypeFld.make("v",str_x5   ,0),
                                     TypeFld.make("x",Type.XNIL,1),
                                     TypeFld.make("a",Type.XNIL,2));
    TypeMemPtr px5 = TypeMemPtr.make(alias1,x5);

    // ................................................... -> A3 -> X5
    TypeStr str_a3 = TypeStr.con("A3");
    TypeStruct  a3 = TypeStruct.make(TypeFld.make("v",str_a3,0),
                                     TypeFld.make("x",px5   ,1));
    TypeMemPtr pa3 = TypeMemPtr.make(alias0,a3);

    // Build two structs pointing to each other
    // ...................................... (X3 <-> X4 ) -> A3 -> X5
    Type i13 = TypeStr.con("X3");
    Type i14 = TypeStr.con("X4");
    TypeFld fi13 = TypeFld.make("v",i13,0);
    TypeFld fi14 = TypeFld.make("v",i14,0);
    TypeFld fpa3 = TypeFld.make("a",pa3,2);
    Type.RECURSIVE_MEET++;
    TypeFld[] flds3 = TypeFlds.ts(fi13, TypeFld.malloc("x",null,1), fpa3);
    TypeFld[] flds4 = TypeFlds.ts(fi14, TypeFld.malloc("x",null,1), fpa3);
    TypeStruct x3 = TypeStruct.malloc("",false,flds3,true);
    TypeStruct x4 = TypeStruct.malloc("",false,flds4,true);
    x3._hash = x3.compute_hash();  x3._cyclic = true;
    x4._hash = x4.compute_hash();  x4._cyclic = true;
    TypeMemPtr px3 = TypeMemPtr.make(alias1,x3);
    TypeMemPtr px4 = TypeMemPtr.make(alias1,x4);
    x3.fld(1).setX(px4);
    x4.fld(1).setX(px3);
    Type.RECURSIVE_MEET--;
    x3 = x3.install_cyclic(x3.reachable());
    px3 = (TypeMemPtr)x4.at(1);

    // ................................ A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStr str_a2 = TypeStr.con("A2");
    TypeStruct  a2 = TypeStruct.make(TypeFld.make("v",str_a2,0),
                                     TypeFld.make("x",px3   ,1));
    TypeMemPtr pa2 = TypeMemPtr.make(alias0,a2);

    // Check sanity
    HashMap<Type,Integer> depths = pa2.depth();
    int maxd = TypeMemPtr.max(alias0,depths);
    assertEquals(1,maxd);
    assertEquals(1,(int)depths.get(a3));

    // .......................... X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  x2 = TypeStruct.make(TypeFld.make("v",TypeStr.con("X2"),0),
                                     TypeFld.make("x",Type.NIL,1),
                                     TypeFld.make("a",pa2,2));
    TypeMemPtr px2 = TypeMemPtr.make(alias1,x2);

    // .................... A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  a1 = TypeStruct.make(TypeFld.make("v",TypeStr.con("A1"),0),
                                     TypeFld.make("x",px2,1));
    TypeMemPtr pa1 = TypeMemPtr.make(alias0,a1);

    // Build two structs pointing to each other
    // ..... (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    Type i10 = TypeStr.con("X0");
    Type i11 = TypeStr.con("X1");
    TypeFld fil0 = TypeFld.make("v",i10,0);
    TypeFld fil1 = TypeFld.make("v",i11,0);
    TypeFld fpa1 = TypeFld.make("a",pa1,2);
    Type.RECURSIVE_MEET++;
    TypeFld[] flds0 = TypeFlds.ts(fil0, TypeFld.malloc("x",null,1), fpa1);
    TypeFld[] flds1 = TypeFlds.ts(fil1, TypeFld.malloc("x",null,1), fpa1);
    TypeStruct x0 = TypeStruct.malloc("",false,flds0,true);
    TypeStruct x1 = TypeStruct.malloc("",false,flds1,true);
    x0._hash = x0.compute_hash();  x0._cyclic = true;
    x1._hash = x1.compute_hash();  x1._cyclic = true;
    TypeMemPtr px0 = TypeMemPtr.make(alias1,x0);
    TypeMemPtr px1 = TypeMemPtr.make(alias1,x1);
    x0.fld(1).setX(px1);
    x1.fld(1).setX(px0);
    Type.RECURSIVE_MEET--;
    x0 = x0.install_cyclic(x0.reachable());
    px0 = (TypeMemPtr)x1.at(1);

    // A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <-> X4 ) -> A3 -> X5
    TypeStruct  a0 = TypeStruct.make(TypeFld.make("v",TypeStr.con("A0"),0),
                                     TypeFld.make("x",px0,1));
    TypeMemPtr pa0 = TypeMemPtr.make(alias0,a0);

    // Check sanity
    depths = pa0.depth();
    assertEquals(0,(int)depths.get(a0));
    assertEquals(1,(int)depths.get(a1));
    assertEquals(2,(int)depths.get(a2));
    assertEquals(3,(int)depths.get(a3));
    assertEquals(3,TypeMemPtr.max(alias0,depths));

    // Approximate
    TypeStruct  zsa0 = a0.approx(3,alias0);
    TypeMemPtr pzsa0 = TypeMemPtr.make(alias0,zsa0);

    // Check sanity!
    // Was: A0 -> (X0 <-> X1) -> A1 -> X2 -> A2 -> (X3 <->  X4) -> A3 -> X5
    // Apx: A0 -> (X0 <-> X1) -> A1 -> X2 -> A23->  X35 -> (X4 <-> X3) -> A23
    assertSame(TypeStr.con("A0"), zsa0.at(0));
    TypeMemPtr zpx0 = (TypeMemPtr)zsa0.at(1);

    TypeStruct zsx0 = (TypeStruct)zpx0._obj;
    assertSame  (i10 ,            zsx0.at(0));
    TypeMemPtr zpx1 = (TypeMemPtr)zsx0.at(1);
    TypeMemPtr zpa1 = (TypeMemPtr)zsx0.at(2);

    TypeStruct zsx1 = (TypeStruct)zpx1._obj;
    assertSame  (i11 ,            zsx1.at(0));
    assertSame  (zpx0,            zsx1.at(1));
    assertSame  (zpa1,            zsx1.at(2));

    TypeStruct zsa1 = (TypeStruct)zpa1._obj;
    assertSame(TypeStr.con("A1"), zsa1.at(0));
    TypeMemPtr zpx2 = (TypeMemPtr)zsa1.at(1);

    TypeStruct zsx2 = (TypeStruct)zpx2._obj;
    assertSame(TypeStr.con("X2"), zsx2.at(0));
    assertSame(Type.NIL,          zsx2.at(1));
    TypeMemPtr zpa23= (TypeMemPtr)zsx2.at(2);

    TypeStruct zsa23= (TypeStruct)zpa23._obj;
    assertSame(str_a2.meet(str_a3), zsa23.at(0));
    TypeMemPtr zpx35= (TypeMemPtr)zsa23.at(1);

    TypeStruct zsx35= (TypeStruct)zpx35._obj;
    assertSame(str_x5.meet(i13),  zsx35.at(0));
    TypeMemPtr zpa4 = (TypeMemPtr)zsx35.at(1) ;
    TypeMemPtr zpa23q=(TypeMemPtr)zsx35.at(2) ;
    // Weakened expected results after NIL expands to [0]->obj
    assertSame(zsa23,             zpa23q._obj);
    //assertSame(TypeObj.OBJ,       zpa23q._obj);
    TypeStruct zsx4 = (TypeStruct)zpa4._obj;
    assertSame(i14,               zsx4.at(0));
    assertSame(zpx35,             zsx4.at(1));
    assertSame(zpa23,             zsx4.at(2));

    depths = pzsa0.depth();
    assertEquals(0,(int)depths.get(zsa0));
    assertEquals(1,(int)depths.get(zsa1));
    assertEquals(2,(int)depths.get(zsa23));
    assertEquals(3,TypeMemPtr.max(alias0,depths));
    assertTrue(a0.isa(zsa0));
  }


  // Type A expands tree-like and gets too deep.
  // A1 -> A2 -> A4
  //          -> A5
  //       A3 -> A6
  //          -> A7
  // And then:
  // A1 -> A2 -> A4 -> A8
  // A1 -> A2 -> A4 -> A9
  // A1 -> A2 -> A5 -> A10
  // A1 -> A2 -> A6 -> A12
  // Approx:
  // A1 -> A2 -> A4.8.9      A1.l -> A2.l ->   (nint8, T?, T?)
  //          -> A5.10               A2.r -> T:(nint8, T?, nil)
  //       A3 -> A6.12       A1.r -> A3.l -> T
  //          -> A7               -> A3.r -> (nint8, nil, nil)
  // ... and so forth.
  // The first few tree layers remain expanded, but the tree tail collapses.
  @Test public void testApprox4() {
    final int CUTOFF = 3;
    int alias = BitsAlias.new_alias(BitsAlias.REC);
    TypeFld lnil = TypeFld.make("l",Type.NIL,1);
    TypeFld rnil = TypeFld.make("r",Type.NIL,2);

    TypeStruct  x12= TypeStruct.make(TypeFld.make("v",TypeInt.con(12),0),lnil,rnil);
    TypeMemPtr px12= TypeMemPtr.make(alias,x12);

    TypeStruct  x10= TypeStruct.make(TypeFld.make("v",TypeInt.con(10),0),lnil,rnil);
    TypeMemPtr px10= TypeMemPtr.make(alias,x10);

    TypeStruct  x9 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 9),0),lnil,rnil);
    TypeMemPtr px9 = TypeMemPtr.make(alias,x9 );

    TypeStruct  x8 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 8),0),lnil,rnil);
    TypeMemPtr px8 = TypeMemPtr.make(alias,x8 );

    TypeStruct  x7 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 7),0),lnil,rnil);
    TypeMemPtr px7 = TypeMemPtr.make(alias,x7 );

    TypeStruct  x6 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 6),0),TypeFld.make("l",px12,1),rnil);
    TypeMemPtr px6 = TypeMemPtr.make(alias,x6 );

    TypeStruct  x5 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 5),0),TypeFld.make("l",px10,1),rnil);
    TypeMemPtr px5 = TypeMemPtr.make(alias,x5 );

    TypeStruct  x4 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 4),0),TypeFld.make("l",px8 ,1),TypeFld.make("r",px9,2) );
    TypeMemPtr px4 = TypeMemPtr.make(alias,x4 );

    TypeStruct  x3 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 3),0),TypeFld.make("l",px6 ,1),TypeFld.make("r",px7,2) );
    TypeMemPtr px3 = TypeMemPtr.make(alias,x3 );

    TypeStruct  x2 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 2),0),TypeFld.make("l",px4 ,1),TypeFld.make("r",px5,2) );
    TypeMemPtr px2 = TypeMemPtr.make(alias,x2 );

    TypeStruct  x1 = TypeStruct.make(TypeFld.make("v",TypeInt.con( 1),0),TypeFld.make("l",px2 ,1),TypeFld.make("r",px3,2) );
    TypeMemPtr px1 = TypeMemPtr.make(alias,x1 );

    // Check sanity
    HashMap<Type,Integer> depths = px1.depth();
    assertEquals(0,(int)depths.get(x1));
    assertEquals(1,(int)depths.get(x2));
    assertEquals(1,(int)depths.get(x3));
    assertEquals(2,(int)depths.get(x4));
    assertEquals(2,(int)depths.get(x5));
    assertEquals(2,(int)depths.get(x6));
    assertEquals(2,(int)depths.get(x7));
    assertEquals(3,(int)depths.get(x8));
    assertEquals(3,(int)depths.get(x9));
    assertEquals(3,(int)depths.get(x10));
    assertEquals(3,(int)depths.get(x12));
    assertEquals(3,TypeMemPtr.max(alias,depths));

    // Approximate
    TypeStruct z1 = x1.approx(CUTOFF,alias);
    TypeMemPtr pz1 = TypeMemPtr.make(alias,z1);
    assertSame( TypeInt.con(1), z1.at(0));
    TypeMemPtr p2 = (TypeMemPtr)z1.at(1) ;
    TypeMemPtr p3 = (TypeMemPtr)z1.at(2) ;

    TypeStruct z2 = (TypeStruct)p2._obj   ;
    assertSame( TypeInt.con(2), z2.at(0));
    TypeMemPtr p4 = (TypeMemPtr)z2.at(1) ;
    TypeMemPtr p5 = (TypeMemPtr)z2.at(2) ;

    TypeStruct z3 = (TypeStruct)p3._obj   ;
    assertSame( TypeInt.con(3), z3.at(0));
    TypeMemPtr p6 = (TypeMemPtr)z3.at(1) ;
    TypeMemPtr p7 = (TypeMemPtr)z3.at(2) ;

    check_leaf(p4,alias,TypeInt.NINT8);
    check_leaf(p5,alias,TypeInt.NINT8);
    check_leaf(p6,alias,TypeInt.NINT8);
    check_leaf(p7,alias,TypeInt.con(7));

    depths = pz1.depth();
    assertEquals(3,TypeMemPtr.max(alias,depths));
  }

  // Leaf is a TypeInt.NINT8, and both pointer fields are either NIL or contain
  // alias 8 (and optionally nil) and point to a leaf type.
  private void check_leaf( TypeMemPtr p, int alias, TypeInt vt ) {
    TypeStruct z = (TypeStruct)p._obj;
    assertSame( vt, z.at(0));
    Type x1 = z.at(1);
    if( x1 != Type.NIL ) {
      TypeMemPtr px = (TypeMemPtr)x1;
      assertTrue(px._aliases.test(alias));
    }
    Type x2 = z.at(2);
    if( x2 != Type.NIL ) {
      TypeMemPtr px = (TypeMemPtr)x2;
      assertTrue(px._aliases.test(alias));
    }
  }

  // Type A expands tree-like and gets too deep; CUTOFF=2
  // A1 -> {l=S ,r=S ,v} depth=1
  // A2 -> {l=A1,r=S ,v} depth=2
  // A3 -> {l=A1,r=A1,v} depth=2
  // A4 -> {l=A2,r=A3,v} depth=3
  // Should approx to:
  // Z1 -> {l=A1,r=A1,v} depth=2, and Z1=A3
  @Test public void testApprox5() {
    final int CUTOFF = 2;
    int alias = BitsAlias.new_alias(BitsAlias.REC);

    TypeStruct  x1= TypeStruct.make(TypeFld.make("l",Type.SCALAR,0),TypeFld.make("r",Type.SCALAR,0),TypeFld.make("v",Type.SCALAR,0));
    TypeMemPtr px1= TypeMemPtr.make(alias,x1);
    assertEquals(0,TypeMemPtr.max(alias,px1.depth()));

    TypeStruct  x2= TypeStruct.make(TypeFld.make("l",   px1     ,0),TypeFld.make("r",Type.SCALAR,0),TypeFld.make("v",Type.SCALAR,0));
    TypeMemPtr px2= TypeMemPtr.make(alias,x2);
    assertEquals(1,TypeMemPtr.max(alias,px2.depth()));

    TypeStruct  x3= TypeStruct.make(TypeFld.make("l",   px1     ,0),TypeFld.make("r",     px1   ,0),TypeFld.make("v",Type.SCALAR,0));
    TypeMemPtr px3= TypeMemPtr.make(alias,x3);
    assertEquals(1,TypeMemPtr.max(alias,px3.depth()));

    TypeStruct  x4= TypeStruct.make(TypeFld.make("l",   px2     ,0),TypeFld.make("r",     px3   ,0),TypeFld.make("v",Type.SCALAR,0));
    TypeMemPtr px4= TypeMemPtr.make(alias,x4);
    assertEquals(2,TypeMemPtr.max(alias,px4.depth()));

    // Approximate
    TypeStruct z1 = x4.approx(CUTOFF,alias);
    TypeMemPtr pz1 = TypeMemPtr.make(alias,z1);
    assertEquals(1,TypeMemPtr.max(alias,pz1.depth()));
    assertSame(x3,z1);
  }

  // Type A expands tree-like and gets too deep; CUTOFF=2
  // A1[0,18] -> {l=0 ,r=A1,v} depth=1, cyclic
  // A2[0,18] -> {l=A1,r=A1,v} depth=2, not cyclic
  //             {l=A1,r=A2,v} depth=3, not cyclic
  // Should approx to:
  // A3[0,18] -> {l=A3,r=A3,v} depth=1, cyclic
  //             {l=A1,r=A3,v} depth=2
  @Test public void testApprox6() {
    Object dummy0 = TypeStruct.TYPES;
    Object dummy1 = TypeMemPtr.TYPES;
    final int CUTOFF = 2;
    int alias = BitsAlias.new_alias(BitsAlias.REC);

    Type.RECURSIVE_MEET++;
    TypeFld[] flds1 = TypeFlds.ts(TypeFld.malloc("l",null,0), TypeFld.malloc("r",null,1), TypeFld.malloc("v",null,2));
    TypeStruct  x1 = TypeStruct.malloc("",false,flds1,true);
    x1._hash = x1.compute_hash();  x1._cyclic = true;
    TypeMemPtr px1 = TypeMemPtr.make_nil(alias,x1);
    x1.fld(0).setX(Type.XNIL  );
    x1.fld(1).setX(px1        );
    x1.fld(2).setX(Type.SCALAR);
    Type.RECURSIVE_MEET--;
    x1 = x1.install_cyclic(x1.reachable());
    assertSame(px1,x1.at(1));

    TypeStruct  x2= TypeStruct.make(TypeFld.make("l",px1,0),TypeFld.make("r",px1,1),TypeFld.make("v",Type.SCALAR,2));
    TypeMemPtr px2= TypeMemPtr.make_nil(alias,x2);

    TypeStruct  z0= TypeStruct.make(TypeFld.make("l",px1,0),TypeFld.make("r",px2,1),TypeFld.make("v",Type.SCALAR,2));
    // Approximate
    TypeStruct z1 = z0.approx(CUTOFF,alias);

    Type.RECURSIVE_MEET++;
    TypeFld[] flds3 = TypeFlds.ts(TypeFld.malloc("l",null,0), TypeFld.malloc("r",null,1), TypeFld.malloc("v",null,2));
    TypeStruct  x3 = TypeStruct.malloc("",false,flds3,true);
    x3._hash = x3.compute_hash();  x3._cyclic = true;
    TypeMemPtr px3 = TypeMemPtr.make_nil(alias,x3);
    x3.fld(0).setX(px3);//TypeMemPtr.make_nil(alias,TypeObj.OBJ);
    x3.fld(1).setX(px3);
    x3.fld(2).setX(Type.SCALAR);
    Type.RECURSIVE_MEET--;
    x3 = x3.install_cyclic(x3.reachable());
    px3 = (TypeMemPtr)x3.at(1);

    TypeStruct x4= TypeStruct.make(TypeFld.make("l",px1,0),TypeFld.make("r",px3,1),TypeFld.make("v",Type.SCALAR,2));

    assertSame(x4,z1);
  }

  // Regression test.  Verify that a closed DATA cycle in the Node graph makes
  // a finite Type graph.  Basically, endless applying NewObj results to a
  // NewObj (as happens when making simple cyclic structures via storing fields
  // from one into the other) ends with a simple cyclic graph and not an
  // endlessly growing or endlessly "ping ponging" result.
  @Test public void testApprox7() {

    // Make a short cycle using alias RECORD.  Repeated add instances & approx,
    // until fixed point.
    final int CUTOFF=2;
    TypeStruct ts0 = TypeStruct.make(TypeFld.NO_DISP);
    TypeMemPtr tmp0 = TypeMemPtr.make(BitsAlias.RECORD_BITS0,ts0), tmp1=null;

    int cnt=0;
    while( tmp0 != tmp1 && cnt < 100 ) {
      TypeStruct ts1 = TypeStruct.make(TypeFld.make("^",tmp1=tmp0,0));
      TypeStruct ts1x = ts1.approx(CUTOFF,BitsAlias.REC);
      // Extend with nil-or-not endlessly.
      tmp0 = TypeMemPtr.make(BitsAlias.RECORD_BITS0,ts1x);
      cnt++;
    }
    // End result has no prefix, since NIL is allowed at every step.  i.e., we
    // added NIL-or-ptr-to-self 3 times, which is exactly approximated by a
    // tight loop with no prefix.
    assertEquals(CUTOFF+1,cnt);


    // Make some child aliases.
    final int alias6 = BitsAlias.new_alias(BitsAlias.REC);
    final int alias7 = BitsAlias.new_alias(BitsAlias.REC);
    final int alias8 = BitsAlias.new_alias(BitsAlias.REC);
    final BitsAlias ba6 = BitsAlias.make0(alias6);
    final BitsAlias ba7 = BitsAlias.make0(alias7);
    final BitsAlias ba8 = BitsAlias.make0(alias8);
    final BitsAlias ba60 = ba6.meet_nil();
    final BitsAlias ba70 = ba7.meet_nil();
    final BitsAlias ba80 = ba8.meet_nil();

    // Add a struct with alias6 & approx.  Expect no change, despite alias6
    // being a child of RECORD.
    TypeStruct ts6 = TypeStruct.make(TypeFld.make("^",tmp0,0));
    TypeStruct ts6x = ts6.approx(CUTOFF,alias6);
    assertEquals(ts6,ts6x);
    TypeMemPtr tmp6 = TypeMemPtr.make(ba60,ts6);
    // Again with alias7
    TypeStruct ts7 = TypeStruct.make(TypeFld.make("^",tmp6,0));
    TypeStruct ts7x = ts7.approx(CUTOFF,alias7);
    assertEquals(ts7,ts7x);
    TypeMemPtr tmp7 = TypeMemPtr.make(ba70,ts7);
    // Again with alias8
    TypeStruct ts8 = TypeStruct.make(TypeFld.make("^",tmp7,0));
    TypeStruct ts8x = ts8.approx(CUTOFF,alias8);
    assertEquals(ts8,ts8x);


    // Start with short cycle:
    //  10_( 11_* );  11#2 -> 10
    // Add this on top (alias#4 and#3 are children of #2):
    //   12#4 -> 13; 13_( 17_*, 14_* );  14#3 -> 15;  15_( 16_*, 2.3 ); 16#4 -> 10;  17#5 -> 18; 18_(nil,1.2)
    // Approx alias#4 should do nothing (only depth 2 for alias#4 till hit cycle).
    // Then add it again & approx at depth 2 for alias#2.


    // Start with: A -> A
    // A is basic RECORD type, actually equal to TypeStruct.DISPLAY.
    // B,C,D are child aliases of A and are alias6,7,8.
    // D is a LHS end type: D -> (nil,88)
    TypeStruct tsD = TypeStruct.make(TypeFld.fldBot,TypeInt.con(88));
    TypeMemPtr tmpD = TypeMemPtr.make(ba8,tsD); // Note not nil
    // Add (alternating the repeating field left and right):
    //   B1 = ( A , 99 )
    TypeStruct tsB1 = TypeStruct.make(TypeFld.make("^",tmp0,0),TypeFld.make(TypeFld.fldBot,TypeInt.con(99),1));
    assertEquals(tsB1,tsB1.approx(CUTOFF,alias6));
    TypeMemPtr tmpB1= TypeMemPtr.make(ba6,tsB1); // Note not nil
    //   C1 = ( D , B1 )
    TypeStruct tsC1 = TypeStruct.make(TypeFld.make("^",tmpD,0),TypeFld.make(TypeFld.fldBot,tmpB1,1));
    assertEquals(tsC1,tsC1.approx(CUTOFF,alias7));
    TypeMemPtr tmpC1= TypeMemPtr.make(ba7,tsC1); // Note not nil

    // Add repeatedly until stable:
    //   B2 = ( C1, 99 )
    //   C2 = ( D , B2 )
    // This should approx by meeting a C with a A, which should drop off the
    // RHS of the C.  The C LHS is a D, which again meets with A to finish the
    // collapse.  Bug is that types flip-flop between 2 variants endlessly.
    cnt = 0;  tmp1 = null;
    while( tmpC1 != tmp1 && cnt < 100 ) {
      tmp1 = tmpC1;
      //   B2 = ( C1, 99 )
      TypeStruct tsB2 = TypeStruct.make(TypeFld.make("^",tmpC1,0),TypeFld.make(TypeFld.fldBot,TypeInt.con(99),1));
      TypeStruct tsB2x = tsB2.approx(CUTOFF,alias6);
      TypeMemPtr tmpB2= TypeMemPtr.make(ba6,tsB2x); // Note not nil

      //   C2 = ( D , B2 )
      TypeStruct tsC2 = TypeStruct.make(TypeFld.make("^",tmpD,0),TypeFld.make(TypeFld.fldBot,tmpB2,1));
      TypeStruct tsC2x = tsC2.approx(CUTOFF,alias7);
      TypeMemPtr tmpC2= TypeMemPtr.make(ba7,tsC2x); // Note not nil
      tmpC1 = tmpC2;
      cnt++;
    }
    assertEquals(CUTOFF,cnt);

  }

  @Test public void testApprox8() {
    Object dummy0 = TypeStruct.TYPES;
    Object dummy1 = TypeFunPtr.TYPES;
    Object dummy2 = Env.GVN;
    final int CUTOFF=2;
    final int fidx = BitsFun.new_fidx(1), fidx0 = BitsFun.new_fidx(fidx), fidx1 = BitsFun.new_fidx(fidx);
    final BitsFun fidxs = BitsFun.make0(fidx0,fidx1).dual();
    final int alias = BitsAlias.new_alias(BitsAlias.REC);
    Env.ALL_DISPLAYS = Env.ALL_DISPLAYS.set(alias); // Declare a display

    // Args for the forward-ref fib(^ ->Scalar).  This has to start as hi-args
    // for this test, as the cyclic approx is supposed to be low - and it has
    // args known post-parse but not pre-parse.
    TypeStruct tfp0_args = TypeStruct.make("", true, TypeFlds.ts(TypeMemPtr.DISP_FLD), false);

    TypeFunPtr tfp0 = TypeFunPtr.make(BitsFun.ANY,2,(TypeMemPtr)TypeFunPtr.DISP.simple_ptr()); // fib with generic display
    TypeStruct dsp0 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp0,1));// The display with weak fib-type
    TypeMemPtr ptr0 = TypeMemPtr.make(alias,dsp0);
    // Args for a strong fib: { ^:ptr0 x:int64 -> ~Scalar } // LOW
    TypeStruct arg0 = TypeStruct.make(TypeFld.make("->",Type.SCALAR,0),
                                      TypeFld.make("^",ptr0.simple_ptr(),1),
                                      TypeFld.make("x",TypeInt.INT64,2));

    TypeFunPtr tfp1 = TypeFunPtr.make(fidxs,2,(TypeMemPtr)ptr0.simple_ptr()); // FIB with weak display
    TypeStruct dsp1 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp1,1)); // Display with stronger FIB-type
    TypeMemPtr ptr1 = TypeMemPtr.make(alias,dsp1);
    // Args for a strong fib: { ^:ptr x:int -> ~Scalar } // LOW.  Display still not recursive.
    TypeStruct arg1 = TypeStruct.make(TypeFld.make("->",Type.SCALAR,0),
                                      TypeFld.make("^",ptr1.simple_ptr(),1),
                                      TypeFld.make("x",TypeInt.INT64,2));

    TypeFunPtr tfp2 = TypeFunPtr.make(fidxs,2,(TypeMemPtr)ptr1.simple_ptr()); // fib2->dsp1->fib1->dsp0->fib0->generic_display
    TypeStruct dsp2 = TypeStruct.make(TypeMemPtr.DISP_FLD,TypeFld.make("fib",tfp2,1)); // dsp2->fib2->dsp1->fib1->dsp0->fib0->generic_display

    // The approx that gets built: fib3->dsp3->fib3->dsp3->...
    Type.RECURSIVE_MEET++;
    TypeFld[] flds3 = TypeFlds.ts(TypeFld.malloc("^",null,0), TypeFld.malloc("fib",null,1));
    TypeStruct dsp3 = TypeStruct.malloc("",false,flds3,false);
    dsp3._hash = dsp3.compute_hash();  dsp3._cyclic = true;
    TypeMemPtr ptr3 = TypeMemPtr.make(alias,dsp3);
    TypeStruct arg3 = TypeStruct.make(TypeFld.make("->",Type.SCALAR,0),
                                      TypeFld.make("^",ptr3.simple_ptr(),1),
                                      TypeFld.make("x",TypeInt.INT64,2));
    TypeFunPtr tfp3 = TypeFunPtr.make(fidxs,2,(TypeMemPtr)ptr3.simple_ptr());
    dsp3.fld(0).setX(TypeMemPtr.DISPLAY_PTR);
    dsp3.fld(1).setX(tfp3);
    Type.RECURSIVE_MEET--;
    dsp3 = dsp3.install_cyclic(dsp3.reachable());

    // This should pass an isa-test (was crashing)
    Type mt0 = dsp0.meet(dsp3);

    // This should pass an isa-test (was crashing)
    Type mt1 = dsp1.meet(dsp3);

    // Check the isa
    Type mt = dsp2.meet(dsp3);
    assertEquals(dsp3,mt);

    // Build the approx
    TypeStruct rez = dsp2.approx(CUTOFF,alias);
    assertEquals(dsp3,rez);
  }
}
