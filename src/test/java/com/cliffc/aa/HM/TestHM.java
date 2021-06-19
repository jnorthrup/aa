package com.cliffc.aa.HM;

import com.cliffc.aa.HM.HM.*;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TestHM {

  @Before public void reset() { HM.reset(); }

  @Test(expected = RuntimeException.class)
  public void test00() {
    HM.hm("fred");
  }

  @Test
  public void test01() {
    Syntax syn = HM.hm("3");
    assertEquals("3",syn._t.p());
  }

  @Test
  public void test02() {
    Syntax syn = HM.hm("(pair1 3)");
    assertEquals("{ A:any -> ( 3, $A) }",syn._t.p());
  }

  @Test
  public void test03() {
    Syntax syn = HM.hm("{ z -> (pair (z 3) (z \"abc\")) }");
    assertEquals("{ { all -> A:any } -> ( $A, $A) }",syn._t.p());
  }

  @Test
  public void test04() {
    Syntax syn = HM.hm("fact = { n -> (if (?0 n) 1 (* n (fact (dec n))))}; fact");
    assertEquals("{ A:int64 -> $A }",syn._t.p());
  }

  @Test
  public void test05() {
    // Because {y->y} is passed in, all 'y' types must agree.
    // This unifies 3 and "abc" which results in 'all'
    Syntax syn = HM.hm("({ x -> (pair (x 3) (x \"abc\")) } {y->y})");
    assertEquals("( A:all, $A)",syn._t.p());
  }

  @Test
  public void test06() {
    Syntax syn = HM.hm("id={x->x}; (pair (id 3) (id \"abc\"))");
    assertEquals("( 3, \"abc\")",syn._t.p());
  }

  @Test//(expected = RuntimeException.class)  No longer throws, but returns a recursive type
  public void test07() {
    // recursive unification
    Syntax syn = HM.hm("{ f -> (f f) }");
    assertEquals("{ A:any:{ $A -> B:any } -> $B }",syn._t.p());
    // We can argue the pretty-print should print:
    // "A:{ $A -> B }"
  }

  @Test
  public void test08() {
    Syntax syn = HM.hm("g = {f -> 5}; (g g)");
    assertEquals("5",syn._t.p());
  }

  @Test
  public void test09() {
    // example that demonstrates generic and non-generic variables:
    Syntax syn = HM.hm("{ g -> f = { x -> g }; (pair (f 3) (f \"abc\"))}");
    assertEquals("{ A:any -> ( $A, $A) }",syn._t.p());
  }

  @Test
  public void test10() {
    Syntax syn = HM.hm("{ f g -> (f g)}");
    assertEquals("{ { A:any -> B:any } $A -> $B }",syn._t.p());
  }

  @Test
  public void test11() {
    // Function composition
    Syntax syn = HM.hm("{ f g -> { arg -> (g (f arg))} }");
    assertEquals("{ { A:any -> B:any } { $B -> C:any } -> { $A -> $C } }",syn._t.p());
  }

  @Test
  public void test12() {
    // Stacked functions ignoring all function arguments
    Syntax syn = HM.hm("map = { fun -> { x -> 2 } }; ((map 3) 5)");
    assertEquals("2",syn._t.p());
  }

  @Test
  public void test13() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    Syntax syn = HM.hm("map = { fun -> { x -> (fun x)}}; { p -> 5 }");
    assertEquals("{ any -> 5 }",syn._t.p());
  }

  @Test
  public void test14() {
    // Looking at when tvars are duplicated ("fresh" copies made).
    // This is the "map" problem with a scalar instead of a collection.
    // Takes a '{a->b}' and a 'a' for a couple of different prims.
    Syntax syn = HM.hm("map = { fun -> { x -> (fun x)}};"+
                  "(pair ((map str) 5) ((map factor) 2.3))");
    assertEquals("( *[4]str, (divmod A:flt64 $A))",syn._t.p());
  }

  @Test
  public void test15() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    Syntax syn = HM.hm("map = { fun x -> (fun x)}; (map {a->3} 5)");
    assertEquals("3",syn._t.p());
  }

  @Test
  public void test16() {
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    Syntax syn = HM.hm("map = { fun x -> (fun x)}; (map { a-> (pair a a)} 5)");
    assertEquals("( A:5, $A)",syn._t.p());
  }

  @Test
  public void test17() {
    Syntax syn = HM.hm("fcn = { p -> { a -> (pair a a) }};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("{ any -> ( A:5, $A) }",syn._t.p());
  }

  @Test
  public void test18() {
    // Checking behavior when using "if" to merge two functions with
    // sufficiently different signatures, then attempting to pass them to a map
    // & calling internally.
    // fcn takes a predicate 'p' and returns one of two fcns.
    //   let fcn = { p -> (if p {a -> pair[a,a        ]}
    //                               {b -> pair[b,pair[3,b]]}) } in
    // map takes a function and an element (collection?) and applies it (applies to collection?)
    //   let map = { fun x -> (fun x) }
    //          in { q -> ((map (fcn q)) 5) }
    // Should return { q -> q ? [5,5] : [5,[3,5]] }
    // Ultimately, unifies "a" with "pair[3,a]" which throws recursive unification.
    Syntax syn = HM.hm("fcn = {p -> (if p {a -> (pair a a)} {b -> (pair b (pair 3 b))})};"+
                  "map = { fun x -> (fun x)};"+
                  "{ q -> (map (fcn q) 5)}");
    assertEquals("{ any -> ( A:\"Cannot unify 5 and A:*[7](any, any, any):( 3, $A)\", $A) }",syn._t.p());
  }

  @Test
  public void test19() {
    Syntax syn = HM.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                  "cdr ={mycons -> (mycons { p q -> q})};"+
                  "(cdr (cons 2 3))");
    assertEquals("3",syn._t.p());
  }

  // Take 2nd element of pair, and applies a function.
  //    let map = fn parg fun => (fun (cdr parg))
  // Some pairs:
  //    let intz = (pair2 false 3)
  //    let strz = (pair2 false "abc")
  // in pair(map(str,intz),map(isempty,strz))
  // Expects: ("2",false)
  @Test
  public void test20() {
    Syntax syn = HM.hm("cons ={x y-> {cadr -> (cadr x y)}};"+
                  "cdr ={mycons -> (mycons { p q -> q})};"+
                  "map ={fun parg -> (fun (cdr parg))};"+
                  "(pair (map str (cons 0 5)) (map isempty (cons 0 \"abc\")))"
                  );
    assertEquals("( *[4]str, int1)",syn._t.p());
  }

  // Obscure factorial-like
  @Test
  public void test21() {
    Syntax syn = HM.hm("f0 = { f x -> (if (?0 x) 1 (f (f0 f (dec x)) 2))}; (f0 * 99)");
    assertEquals("int64",syn._t.p());
  }

  // Obscure factorial-like
  @Test
  public void test22() {
    // let f0 = fn f x => (if (?0 x) 1 (* (f0 f (dec x)) 2) ) in f0 f0 99
    // let f0 = fn f x => (if (?0 x) 1 (f (f0 f (dec x)) 2) ) in f0 *  99
    Syntax syn = HM.hm("f0 = { f x -> (if (?0 x) 1 (* (f0 f (dec x)) 2))}; (f0 f0 99)");
    assertEquals("int64",syn._t.p());
  }

  // Mutual recursion
  @Test
  public void test23() {
    Syntax syn = HM.hm("is_even = "+
                  "  is_odd = { n -> (if (?0 n) 0 (is_even (dec n)))}; "+
                  "     { n -> (if (?0 n) 1 (is_odd (dec n)))};"+
                  "(is_even 3)"
                  );
    assertEquals("int1",syn._t.p());
  }

  // Toss a function into a pair & pull it back out
  @Test
  public void test24() {
    Syntax syn = HM.hm("{ g -> fgz = "+
                  "         cons = {x y -> {cadr -> (cadr x y)}};"+
                  "         cdr = {mycons -> (mycons { p q -> q})};"+
                  "         (cdr (cons 2 { z -> (g z) }));"+
                  "      (pair (fgz 3) (fgz 5))"+
                  "}"
                  );
    assertEquals("{ { nint8 -> A:any } -> ( $A, $A) }",syn._t.p());
  }

  // Basic structure test
  @Test
  public void test25() {
    Syntax syn = HM.hm("@{x=2, y=3}");
    assertEquals("@{ x = 2, y = 3}",syn._t.p());
  }

  // Basic field test
  @Test
  public void test26() {
    Syntax syn = HM.hm(".x @{x =2, y =3}");
    assertEquals("2",syn._t.p());
  }

  // Basic field test
  @Test
  public void test27() {
    Syntax syn = HM.hm(".x 5");
    assertEquals("\"Cannot unify 5 and @{ x = any}\"",syn._t.p());
  }

  // Basic field test.
  @Test
  public void test28() {
    Syntax syn = HM.hm(".x @{ y =3}");
    assertEquals("\"Missing field definition x in @{ y = 3}:[9]\"",syn._t.p());
  }

  @Test
  public void test29() {
    Syntax syn = HM.hm("{ g -> @{x=g, y=g}}");
    assertEquals("{ A:any -> @{ x = $A, y = $A} }",syn._t.p());
  }

  @Test
  public void test30() {
    // Load common field 'x', ignoring mismatched fields y and z
    Syntax syn = HM.hm("{ pred -> .x (if pred @{x=2,y=3} @{x=3,z= \"abc\"}) }");
    assertEquals("{ any -> nint8 }",syn._t.p());
  }

  @Test
  public void test31() {
    // Load some fields from an unknown struct: area of a square.
    // Since no nil-check, correctly types as needing a not-nil input.
    Syntax syn = HM.hm("{ sq -> (* .x sq .y sq) }"); // { sq -> sq.x * sq.y }
    assertEquals("{ @{ y = A:int64, x = $A} -> $A }",syn._t.p());
  }

  @Test
  public void test32() {
    // Recursive linked-list discovery, with no end clause
    Syntax syn = HM.hm("map = { fcn lst -> @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } }; map");
    assertEquals("{ { A:any -> B:any } C:*[]@{^=any; n0=any; v0=any}:@{ v0 = $A, n0 = $C} -> D:*[9]@{^==any; n1==any; v1==any}:@{ n1 = $D, v1 = $B} }",syn._t.p());
  }

  @Test
  public void test33() {
    // Recursive linked-list discovery, with nil.  Note that the output memory
    // has the output memory alias, but not the input memory alias (which must
    // be made before calling 'map').
    Syntax syn = HM.hm("map = { fcn lst -> (if lst @{ n1=(map fcn .n0 lst), v1=(fcn .v0 lst) } nil) }; map");
    assertEquals("{ { A:any -> B:any } C: 0:@{ v0 = $A, n0 = $C} -> D:*[0,9]@{^=any; n1=any; v1=any}?:@{ n1 = $D, v1 = $B} }",syn._t.p());
  }

  @Test
  public void test34() {
    // Recursive linked-list discovery, with no end clause
    Syntax syn = HM.hm("map = { fcn lst -> (if lst @{ n1 = (map fcn .n0 lst), v1 = (fcn .v0 lst) } nil) }; (map dec @{n0 = nil, v0 = 5})");
    assertEquals("A:*[0,9]@{^=any; n1=any; v1=any}?:@{ n1 = $A, v1 = int64}",syn._t.p());
  }

  // try the worse-case expo blow-up test case from SO
  @Test
  public void test35() {
    // Recursive linked-list discovery, with nil
    Syntax syn = HM.hm("p0 = { x y z -> (triple x y z) };"+
                 "p1 = (triple p0 p0 p0);"+
                 "p2 = (triple p1 p1 p1);"+
                 "p3 = (triple p2 p2 p2);"+
                 "p3");
    assertEquals("( ( ( { A:any B:any C:any -> ( $A, $B, $C) }, { D:any E:any F:any -> ( $D, $E, $F) }, { G:any H:any I:any -> ( $G, $H, $I) }), ( { J:any K:any L:any -> ( $J, $K, $L) }, { M:any N:any O:any -> ( $M, $N, $O) }, { P:any Q:any R:any -> ( $P, $Q, $R) }), ( { S:any T:any U:any -> ( $S, $T, $U) }, { V21:any V22:any V23:any -> ( $V21, $V22, $V23) }, { V24:any V25:any V26:any -> ( $V24, $V25, $V26) })), ( ( { V27:any V28:any V29:any -> ( $V27, $V28, $V29) }, { V30:any V31:any V32:any -> ( $V30, $V31, $V32) }, { V33:any V34:any V35:any -> ( $V33, $V34, $V35) }), ( { V36:any V37:any V38:any -> ( $V36, $V37, $V38) }, { V39:any V40:any V41:any -> ( $V39, $V40, $V41) }, { V42:any V43:any V44:any -> ( $V42, $V43, $V44) }), ( { V45:any V46:any V47:any -> ( $V45, $V46, $V47) }, { V48:any V49:any V50:any -> ( $V48, $V49, $V50) }, { V51:any V52:any V53:any -> ( $V51, $V52, $V53) })), ( ( { V54:any V55:any V56:any -> ( $V54, $V55, $V56) }, { V57:any V58:any V59:any -> ( $V57, $V58, $V59) }, { V60:any V61:any V62:any -> ( $V60, $V61, $V62) }), ( { V63:any V64:any V65:any -> ( $V63, $V64, $V65) }, { V66:any V67:any V68:any -> ( $V66, $V67, $V68) }, { V69:any V70:any V71:any -> ( $V69, $V70, $V71) }), ( { V72:any V73:any V74:any -> ( $V72, $V73, $V74) }, { V75:any V76:any V77:any -> ( $V75, $V76, $V77) }, { V78:any V79:any V80:any -> ( $V78, $V79, $V80) })))",syn._t.p());
  }

  // Need to see if a map call, inlined a few times, 'rolls up'.  Sometimes
  // rolls up, sometimes not; depends on worklist visitation order.
  @Test
  public void test36() {
    // Recursive linked-list discovery, with nil.  Unrolled once.
    Syntax syn = HM.hm("map = { lst -> (if lst @{ n1= arg= .n0 lst; (if arg @{ n1=(map .n0 arg), v1=(str .v0 arg)} nil), v1=(str .v0 lst) } nil) }; map");
    assertEquals("{ A: 0:@{ v0 = int64, n0 = @{ n0 = $A, v0 = int64}} -> B:*[0,10]@{^=any; n1=any; v1=any}?:@{ n1 = @{ n1 = $B, v1 = *[4]str}, v1 = *[4]str} }",syn._t.p());
  }

  @Test
  public void test37() {
    Syntax syn = HM.hm("x = { y -> (x (y y))}; x");
    assertEquals("{ A:any:{ $A -> $A } -> any }",syn._t.p());
  }

  @Test
  public void test38() {
    // Example from SimpleSub requiring 'x' to be both a struct with field
    // 'v', and also a function type - specifically disallowed in 'aa'.
    Syntax syn = HM.hm("{ x -> y = ( x .v x ); 0}");
    assertEquals("{ Cannot unify *[-2]@{ v = V31} and { V31 -> V29 } -> 0 }",syn._t.p());
  }

  @Test
  public void test39() {
    Syntax syn = HM.hm("x = { z -> z}; (x { y -> .u y})");
    assertEquals("{ *[-2]@{ u = A} -> A }",syn._t.p());
  }

  @Test
  public void test40() {
    // Example from SimpleSub requiring 'x' to be both:
    // - a recursive self-call function from "w = (x x)": $V66:{ $V66 -> V67 } AND
    // - a function which takes a struct with field 'u'
    // The first arg to x is two different kinds of functions, so fails unification.
    Syntax syn = HM.hm("x = w = (x x); { z -> z}; (x { y -> .u y})");
    assertEquals("Cannot unify $V43:{ $V43 -> V44 } and *[-2]@{ u = V32}",syn._t.p());
  }

  @Test
  public void test41() {
    // Example from test15:
    //   map={lst fcn -> lst ? fcn lst.1};
    //   in_int=(0,2);"+       // List of ints
    //   in_str=(0,"abc");" +  // List of strings
    //   out_str = map(in_int,str:{int->str});"+        // Map over ints with int->str  conversion, returning a list of strings
    //   out_bool= map(in_str,{str -> str==\"abc\"});"+ // Map over strs with str->bool conversion, returning a list of bools
    //   (out_str,out_bool)",

    Syntax syn = HM.hm("map={lst fcn -> (fcn .y lst) }; "+
                       "in_int=@{ x=0 y=2}; " +
                       "in_str=@{ x=0 y=\"abc\"}; " +
                       "out_str = (map in_int str); " +
                       "out_bool= (map in_str { xstr -> (eq xstr \"def\")}); "+
                       "(pair out_str out_bool)"  );
    assertEquals("(pair str int1)",syn._t.p());
  }


}

/**

noinline_map: { lst:@{y=A} fcn:{A->B} -> B }
in_int : @{ x=Nil, y=int}
out_str: @{ x=Nil, y=str}
pi     : @{ pi=flt }
out_bol: int1/bool
(pair str bool)

Unify_Lift:
  - assigns a type to a tvar, based on tvar?  Structure-for-structure, plus meet of Bases.
  - applies the join to flow types in everywhere tvar appears
  - follow top-level types/tvars
  - No-esc-out uses pre-call memory
  -- Concept: lift flow memory from non-memory TVars.
  -- STUCK HERE...




Example w/Store

mem[#1s:@{y=Nil}]
  Store.y mem #1s 5.2     adr<->@{y=Flt}  val=Flt
mem[#1s:@{y=flt }]

Now unify-lift: mem[#1s].y join with Flt.


Example w/Call

fcn = { mem adr val -> mem[adr].y = val }
fcn: { @{y=A} A -> A }   // H-M tvar type

mem[#1s:@{y=Nil}]   // Leaf:Nil can unify with anything
  Call mem #1s  5.2  fcn
    - val: flow makes it a Scalar
    - lst: flow makes it a TMP[14,16,...]
    - mem: flow makes it mem[14,16,...].y = Scalar
    - fresh { @{y=A} A -> A } with { lst 5.2 -> rez }
    - lst becomes @{y=A}
    - A becomes 5.2
    - unify Nil and 5.2 --> Flt



Conflict on fcns:
- Flow tracks set of valid call fidxs... until i start calling on things that
  have merged, required H-M, and the merge loses the fidxs.

- H-M can play top-down w/Opto/GCP; get H-M types.  So can track fcns thru args
  and calls.  Unify_lift can recover some flow-fcn-fidxs, which can limit flow
  targets.
- Limit flow targets can limit H-M unification requirements:
  fcn = pred ? {A->B} : {C->D}
  (fcn foo)   // Implies foo:A:C all unified
  // Suppose pred=TRUE, so {C->D} never happens, so foo[{A->B}] only
  // Then foo:A




Add combo GCP & HM ?

-- really fighting memory state here
-- did want mem to be indexed by alias#s... but this is variant over GCP time.
-- Similar to the unify of pred case:

-- unify (if pred x y):
  -- pred==0 : y
  -- pred==1 : x
  -- pred==TOP : neither, skip
  -- pred==BOT : x.unify(y)

-- unify of memory loads:  (load.fld mem adr)
  -- adr is an ever-widening set of alais#s
  -- mem[forAll aliases].fld unify Load
  -- New alias in flow types: unify it also

-- Similar to unify of Stores

-- Still need a way to lift flows from unify;
  -- Apply result type can be lifted to join of matching TVar inputs?...
     (fcn arg1 arg2):rez
     fcn is flow-typed as (TFP int:A scalar:B -> scalar:B)
     arg1 is :>int, or else flow error
     arg2 is e.g. str
     rez is scalar, but join with arg2:str.
  -- (fcn arg1 arg2):rez
  -- fcn:{ int:A {xxx -> yyy}:{B -> C} -> C}
     arg1 is int
     -- arg2 is scalar - no lift
     -- arg2 is {bbb -> ccc} - rez.join(ccc)


So... no unify during iter/lift.  Start all unifies at leafs at GCP.
Unify "like normal"


Some decisions:
- HM type structures carry a flowtype at every point, or not.
- - If not, then when the HM type alters at a point, need to walk both HM and
    flow types and "align" them: expect flow types to be sharper than HM, except for Applys, where HM's join.
- - If so, then at each incremental HM union: leaf-vs-non-leaf the leaf type needs to meet with the
    non-leaf-HM's flow types incrementally.
- - or do not ever walk both?  Just JOIN at Applys

Bare-HM-Leafs type as ANY (not ALL), and MEET with the base types they unify
with.  When the Leaf unifies with something with structure, then we have to
decide what to do (meet the structure dataflow and leaf dataflow; walk the
structure and matching dataflow, just taking leaves, etc)


 */
