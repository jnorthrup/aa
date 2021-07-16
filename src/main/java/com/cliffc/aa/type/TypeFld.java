package com.cliffc.aa.type;

import com.cliffc.aa.AA;
import com.cliffc.aa.util.*;
import static com.cliffc.aa.AA.unimpl;

import org.jetbrains.annotations.NotNull;


// A field in a TypeStruct
public class TypeFld extends Type<TypeFld> {
  // Field names are never null, and never zero-length.  If the 1st char is a
  // '*' the field is Top; a '.' is Bot; all other values are valid field names.
  public @NotNull String _fld;  // The field name
  public Type _t;               // Field type.  Usually some type of Scalar, or ANY or ALL.
  public Access _access;        // Field access type: read/write, final, read/only
  public int _order;            // Field order in the struct, or -1 for undefined (Bot) or -2 for conforming (top)

  private TypeFld     ( String fld, Type t, Access access, int order ) { super(TFLD); init(fld,t,access,order); }
  private TypeFld init( String fld, Type t, Access access, int order ) { _fld=fld; _t=t; _access=access; _order=order; return this; }

  // Note: hash does not depend on field type, to support building cyclic TypeStructs.
  @Override public int compute_hash() { return _fld.hashCode()+_access.hashCode()+_order; }
  @Override public boolean equals( Object o ) {
    if( this==o ) return true;
    if( !(o instanceof TypeFld) ) return false;
    TypeFld t = (TypeFld)o;
    return Util.eq(_fld,t._fld) && _t==t._t && _access==t._access && _order==t._order;
  }

  @Override public SB str( SB sb, VBitSet dups, TypeMem mem, boolean debug ) {
    sb.p(_fld).p(_access.toString());
    return _t==null ? sb.p('!') : (_t==Type.SCALAR ? sb : _t.str(sb,dups,mem,debug));
  }
  
  private static TypeFld FREE=null;
  @Override protected TypeFld free( TypeFld ret ) { FREE=this; return ret; }
  // Split malloc/hashcons is used when making cyclic structures
  public static TypeFld malloc( String fld, Type t, int order ) { return malloc(fld,t,Access.Final,order); }
  public static TypeFld malloc( String fld, Type t, Access access, int order ) {
    TypeFld t1 = FREE == null
      ? new TypeFld(fld,t,access,order)
      : FREE  .init(fld,t,access,order);
    FREE = null;
    return t1;
  }
  public TypeFld hashcons_free() {
    TypeFld t2 = (TypeFld)hashcons();
    return this==t2 ? this : free(t2);
  }
  public static TypeFld make( String fld, Type t, int order ) { return make(fld,t,Access.Final,order); }
  public static TypeFld make( String fld, Type t, Access access, int order ) { return malloc(fld,t,access,order).hashcons_free(); }

  // Some convenient default constructors
  private static final String[] ARGS = new String[]{"^","x","y","z"};
  private static final String[] TUPS = new String[]{"^","0","1","2"};
  public static TypeFld make_arg( Type t, int order ) { return make(ARGS[order],t,Access.Final,order);  }
  public static TypeFld make_tup( Type t, int order ) { return make(TUPS[order],t,Access.Final,order);  }
  public TypeFld make_from(Type t) { return make(_fld,t,_access,_order); }

  @Override protected TypeFld xdual() { return new TypeFld(sdual(_fld),_t._dual,_access.dual(),odual(_order)); }
  @Override protected TypeFld rdual() {
    if( _dual != null ) return _dual;
    TypeFld dual = _dual = new TypeFld(sdual(_fld),_t.rdual(),_access.dual(),odual(_order));
    dual._dual = this;
    if( _hash != 0 ) dual._hash = dual.compute_hash();
    return dual;
  }
  
  @Override protected TypeFld xmeet( Type tf ) {
    if( this==tf ) return this;
    if( tf._type != TFLD ) throw typerr(tf);
    TypeFld f = (TypeFld)tf;
    String fld   = smeet(_fld,  f._fld);
    Type   t     = _t     .meet(f._t     );
    Access access= _access.meet(f._access);
    int    order = omeet(_order,f._order);
    return make(fld,t,access,order);
  }  

  // Used during cyclic struct meets, either side (but not both) might be null,
  // and the _t field is not filled in.  A new TypeFld is returned.
  static TypeFld cmeet(TypeFld f0, TypeFld f1) {
    throw unimpl();
  }
  // Used during cyclic struct meets.  The LHS is meeted into directly.
  // The _f field is not filled in.
  TypeFld cmeet(TypeFld f1) {
    throw unimpl();
  }
  
  public enum Access {
    NoAccess,                   // Cannot access (either read or write)
    Final,                      // No future load will ever see a different value than any final store
    RW,                         // Read/Write
    ReadOnly;                   // Read-Only; other threads can Write
    static Access top() { return NoAccess; }
    
    Access dual() {
      throw unimpl();
    }
    Access meet(Access a) {
      throw unimpl();
    }
  };

  // Field names
  public static final String fldTop = "\\";
  public static final String fldBot = "." ;
  // String dual
  private static String sdual(String s) {
    if( Util.eq(s,fldTop) ) return fldBot;
    if( Util.eq(s,fldBot) ) return fldTop;
    return s;
  }
  // String meet
  private static String smeet( String s0, String s1 ) {
    if( Util.eq(s0,s1) ) return s0;
    if( Util.eq(s0,fldTop) ) return s1;
    if( Util.eq(s1,fldTop) ) return s0;
    return fldBot;
  }

  // Field order, -1 is undefined (bot) and -2 is conforming (top)
  private static final int oTop = -1;
  private static final int oBot = -2;
  private static int odual( int order ) {
    if( order==oTop ) return oBot;
    if( order==oBot ) return oTop;
    return order;
  }
  private static int omeet( int o0, int o1 ) {
    if( o0==o1 ) return o0;
    if( o0==oTop ) return o1;
    if( o1==oTop ) return o0;
    return oBot;
  }

         static final TypeFld FLDTOP  = make(fldTop,Type.ANY,Access.top(),oTop);
  public static final TypeFld NO_DISP = make("^",TypeMemPtr.NO_DISP,Access.Final,0);
  public static final TypeFld DISP    = make("^",TypeMemPtr.DISP_SIMPLE,Access.Final,0);
 
  // Setting the type during recursive construction.
  public Type setX(Type t) {
    assert _dual==null && _hash==0; // Not interned
    return (_t = t);
  }

  // If this is a display field
  @Override public boolean is_display_ptr() { return _order==0 && Util.eq(_fld,"^") && _t.is_display_ptr(); }

  // Simple string find on an array
  static int fld_find(TypeFld[] flds, String fld) {
    for( int i=0; i<flds.length; i++ )
      if( Util.eq(flds[i]._fld,fld) )
        return i;
    return -1;
  }
  
}

