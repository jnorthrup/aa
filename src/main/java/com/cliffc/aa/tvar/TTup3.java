package com.cliffc.aa.tvar;

import com.cliffc.aa.TNode;
import com.cliffc.aa.type.Type;
import com.cliffc.aa.type.TypeTuple;
import com.cliffc.aa.util.SB;
import org.jetbrains.annotations.NotNull;

// Type of a Hindley-Milner 3-tuple operator
// "CMV" for {Control,Memory,Value} as the result of Rets and CallEpis.

public class TTup3 extends TypeVar {

  // Basic H-M type variable supporting U-F and parametric types.
  public TTup3( @NotNull TNode tn ) { super(tn); }

  // Type from parts
  @Override public Type _type(boolean head) {
    // A 3-tuple from inputs
    Type t0 = _tnode.tvar(0).type();
    Type t1 = _tnode.tvar(1).type();
    Type t2 = _tnode.tvar(2).type();
    return TypeTuple.make(t0,t1,t2);
  }

  // Unify this into tv.
  @Override public Object unify(TypeVar tv) {
    if( tv instanceof TVar ) return tv.unify(this);
    if( !(tv instanceof TTup3) )
      throw com.cliffc.aa.AA.unimpl(); // Fails unification
    TTup3 t3 = (TTup3)tv;
    // Structural unification
    throw com.cliffc.aa.AA.unimpl();
  }

  // U-F find algo.  Only TVars can be a child in U-F.
  @Override TypeVar find() { return this; }
  // Pretty print
  @Override public SB _str(SB sb, boolean pretty) {
    sb.p("V").p(uid()).p("[");
    _tnode.tvar(0)._str(sb,pretty).p(",");
    _tnode.tvar(1)._str(sb,pretty).p(",");
    _tnode.tvar(2)._str(sb,pretty).p("]");
    return sb;
  }
}