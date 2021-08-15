package com.cliffc.aa.HM

import java.util.HashMap
import com.cliffc.aa.AA
import com.cliffc.aa.HM.HM.T2.Companion.make_struct
import com.cliffc.aa.type.*
import com.cliffc.aa.util.*
import java.util.HashSet
import java.lang.RuntimeException
import java.util.Arrays
import java.util.TreeMap
import kotlin.jvm.JvmOverloads

/**
Combined Hindley-Milner and Global Constant Propagation typing.
Complete stand-alone, for research.
Treats HM as a Monotone Analysis Framework; converted to a worklist style.
The type-vars are monotonically unified, gradually growing over time - and
this is treated as the MAF lattice.  Some of the normal Algo-W work gets
done in a prepass; e.g. discovering identifier sources (SSA form), and
building the non-generative set.  Because of the non-local unification
behavior type-vars include a "dependent Syntax" set; a set of Syntax
elements put back on the worklist if this type unifies, beyond the expected
parent and AST children.

The normal HM unification steps are treated as the MAF transfer "functions",
taking type-vars as inputs and producing new, unified, type-vars.  Because
unification happens in-place (normal Tarjan disjoint-set union), the xfer
"functions" are executed for side-effects only, and return a progress flag.
The transfer functions are virtual calls on each Syntax element.  Some of
the steps are empty because of the pre-pass (Let,Con).
HM Bases include anything from the GCP lattice, but 'widened' to form
borders between e.g. ints and pointers.  Includes polymorphic structures and
fields (structural typing not duck typing), polymorphic nil-checking and an
error type-var.  Both HM and GCP types fully support recursive types.

Unification typically makes many many temporary type-vars and immediately
unifies them.  For efficiency, this algorithm checks to see if unification
requires an allocation first, instead of just "allocate and unify".  The
major place this happens is identifiers, which normally make a "fresh" copy
of their type-var, then unify.  I use a combined "make-fresh-and-unify"
unification algorithm there.  It is a structural clone of the normal unify,
except that it lazily makes a fresh-copy of the left-hand-side on demand
only; typically discovering that no fresh-copy is required.

To engineer and debug the algorithm, the unification step includes a flag to
mean "actually unify, and report a progress flag" vs "report if progress".
The report-only mode is aggressively asserted for in the main loop; all
Syntax elements that can make progress are asserted as on the worklist.

GCP gets the normal MAF treatment, no surprises there.

The combined algorithm includes transfer functions taking facts from both
MAF lattices, producing results in the other lattice.

For the GCP->HM direction, the HM 'if' has a custom transfer function
instead of the usual one.  Unification looks at the GCP value, and unifies
either the true arm, or the false arm, or both or neither.  In this way GCP
allows HM to avoid picking up constraints from dead code.

Also for GCP->HM, the HM ground terms or base terms include anything from
the GCP lattice.

For the HM->GCP direction, the GCP 'apply' has a customer transfer function
where the result from a call gets lifted (JOINed) based on the matching GCP
inputs - and the match comes from using the same HM type-var on both inputs
and outputs.  This allows e.g. "map" calls which typically merge many GCP
values at many applies (call sites) and thus end up typed as a Scalar to
Scalar, to improve the GCP type on a per-call-site basis.

Test case 45 demonstrates this combined algorithm, with a program which can
only be typed using the combination of GCP and HM.

BNF for the "core AA" syntax:
e  = number | string | primitives | (fe0 fe1*) | { id* -> fe0 } | id | id = fe0; fe1 | @{ (label = fe0)* }
fe = e | fe.label                 // optional field after expression

BNF for the "core AA" pretty-printed types:
T = X | X:T | { X* -> X } | base | @{ (label = X)* } | T? | Error
base = any lattice element, all are nilable
Multiple stacked T????s collapse

 */
class HM {
    companion object {
        // Mapping from primitive name to PrimSyn
        val PRIMSYNS: HashMap<String?, PrimSyn?> = HashMap()
        const val DEBUG_LEAKS = false
        const val DO_HM = true
        const val DO_GCP = true

        @JvmStatic
        fun hm(sprog: String?): Root {
            val work = Worklist()
            PrimSyn.WORK = work
            for (prim in arrayOf<PrimSyn?>(If(), Pair1(), Pair(), EQ(), EQ0(), Mul(), Add(), Dec(), Str(), Triple(), Factor(), IsEmpty(), NotNil())) PRIMSYNS[prim!!.name()] = prim

            // Parse
            val prog = parse(sprog)

            // Prep for SSA: pre-gather all the (unique) ids
            val cnt_syns = prog.prep_tree(null, null, work)
            val init_T2s = T2.CNT
            while (work.len() > 0) {     // While work
                val oldcnt = T2.CNT // Used for cost-check when no-progress
                assert(work._cnt < 2000)
                val syn = work.pop() // Get work
                if (DO_HM) {
                    val old = syn!!._hmt // Old value for progress assert
                    if (syn.hm(work)) {
                        assert(!syn.debug_find().unify(old!!.find(), null) // monotonic: unifying with the result is no-progress
                        )
                        syn.add_hm_work(work) // Push affected neighbors on worklist
                    } else {
                        assert(!DEBUG_LEAKS || oldcnt == T2.CNT // No-progress consumes no-new-T2s
                        )
                    }
                }
                if (DO_GCP) {
                    val old = syn!!._flow
                    val t = syn.`val`(work)
                    if (t !== old) {           // Progress
                        assert(old!!.isa(t) // Monotonic falling
                        )
                        syn._flow = t // Update type
                        if (syn._par != null) { // Generally, parent needs revisit
                            work.push(syn._par) // Assume parent needs revisit
                            syn._par!!.add_val_work(syn, work) // Push affected neighbors on worklist
                        }
                    }
                }
                assert(prog.more_work(work))
            }
            assert(prog.more_work(work))
            println("Initial T2s: " + init_T2s + ", Prog size: " + cnt_syns + ", worklist iters: " + work._cnt + ", T2s: " + T2.CNT)
            return prog
        }

        @JvmStatic
        fun reset() {
            BitsAlias.reset_to_init0()
            BitsFun.reset_to_init0()
            PRIMSYNS.clear()
            Pair1.PAIR1S!!.clear()
            Lambda.FUNS.clear()
            T2.reset()
            PrimSyn.reset()
        }

        // ---------------------------------------------------------------------
        // Program text for parsing
        private var X = 0
        private lateinit var BUF: ByteArray
        fun parse(s: String?): Root {
            X = 0
            BUF = s!!.toByteArray()
            val prog = fterm()
            if (skipWS().toInt() != -1) throw AA.unimpl("Junk at end of program: " + String(BUF, X, BUF.size - X))
            // Inject IF at root
            return Root(prog)
        }

        fun term(): Syntax? {
            if (skipWS().toInt() == -1) return null
            if (isDigit(BUF[X])) return number()
            if (BUF[X] == '"'.code.toByte()) return string()
            if (BUF[X] == '('.code.toByte()) {         // Parse an Apply
                X++ // Skip paren
                val `fun` = fterm()
                val args = Ary(arrayOfNulls<Syntax?>(1), 0)
                while (skipWS() != ')'.code.toByte() && X < BUF.size) args.push(fterm())
                require(')')
                // Guarding if-nil test inserts an upcast.  This is a syntatic transform only.
                if (`fun` is If &&
                        args.at(0) is Ident) {
                    val id = args.at(0) as Ident?
                    args[1] = Apply(id!!._name?.let { Lambda(args.at(1), it) },
                            Apply(NotNil(), Ident(id._name)))
                }
                return Apply(`fun`, *args.asAry())
            }
            if (BUF[X] == '{'.code.toByte()) {         // Lambda of 1 or 2 args
                X++ // Skip paren
                val args = Ary(arrayOfNulls<String?>(1), 0)
                while (skipWS() != '-'.code.toByte()) args.push(id())
                require("->")
                val body = fterm()
                require('}')
                return Lambda(body, *args.asAry() as Array<String>)
            }
            // Let or Id
            if (isAlpha0(BUF[X])) {
                val id = id()
                if (skipWS() != '='.code.toByte()) {
                    val prim = PRIMSYNS[id] // No shadowing primitives or this lookup returns the prim instead of the shadow
                    return if (prim == null) Ident(id) else prim.make() // Make a prim copy with fresh HM variables
                }
                // Let expression; "id = term(); term..."
                X++ // Skip '='
                val def = fterm()
                require(';')
                return Let(id, def, fterm())
            }

            // Structure
            if (BUF[X] == '@'.code.toByte()) {
                X++
                require('{')
                val ids = Ary(String::class.java)
                val flds = Ary(Syntax::class.java)
                while (skipWS() != '}'.code.toByte() && X < BUF.size) {
                    val id = require<String?>('=', id())
                    val fld = fterm() ?: throw AA.unimpl("Missing term for field $id")
                    ids.push(id)
                    flds.push(fld)
                    if (skipWS() == ','.code.toByte()) X++
                }
                require('}')
                return Struct(ids.asAry(), flds.asAry())
            }
            throw AA.unimpl("Unknown syntax")
        }

        // Parse a term with an optional following field.
        private fun fterm(): Syntax? {
            var term = term()
            while (true) {
                if (term == null || skipWS() != '.'.code.toByte()) return term
                X++
                term = Field(id(), term)
            }
        }

        private val ID: SB = SB()
        private fun id(): String {
            ID.clear()
            while (X < BUF.size && isAlpha1(BUF[X])) ID.p(BUF[X++].toInt().toChar())
            val s = ID.toString().intern()
            if (s.isEmpty()) throw AA.unimpl("Missing id")
            return s
        }

        private fun number(): Syntax {
            if (BUF[X] == '0'.code.toByte()) {
                X++
                return Con(Type.XNIL)
            }
            var sum = 0
            while (X < BUF.size && isDigit(BUF[X])) sum = sum * 10 + BUF[X++] - '0'.code
            if (X >= BUF.size || BUF[X] != '.'.code.toByte()) return Con(TypeInt.con(sum.toLong()))
            // Ambiguous '.' in: 2.3 vs 2.x (field load from a number)
            if (X + 1 < BUF.size && isAlpha0(BUF[X + 1])) return Con(TypeInt.con(sum.toLong()))
            X++
            var f = sum.toFloat()
            f = f + (BUF[X++] - '0'.code.toByte()) / 10.0f
            return Con(TypeFlt.con(f.toDouble()))
        }

        private fun string(): Syntax? {
            val start = ++X
            while (X < BUF.size && BUF[X] != '"'.code.toByte()) X++
            return require<Con?>('"', Con(TypeMemPtr.make(BitsAlias.STRBITS, TypeStr.con(String(BUF, start, X - start).intern()))))
        }

        private fun skipWS(): Byte {
            while (X < BUF.size && isWS(BUF[X])) X++
            return if (X == BUF.size) -1 else BUF[X]
        }

        private fun isWS(c: Byte): Boolean =
                c == ' '.code.toByte() || c == '\t'.code.toByte() || c == '\n'.code.toByte() || c == '\r'.code.toByte()

        private fun isDigit(c: Byte): Boolean = '0'.code.toByte() <= c && c <= '9'.code.toByte()

        private fun isAlpha0(c: Byte): Boolean =
                'a'.code.toByte() <= c && c <= 'z'.code.toByte() || 'A'.code.toByte() <= c && c <= 'Z'.code.toByte() || c == '_'.code.toByte() || c == '*'.code.toByte() || c == '?'.code.toByte() || c == '+'.code.toByte()

        private fun isAlpha1(c: Byte): Boolean =
                isAlpha0(c) || '0'.code.toByte() <= c && c <= '9'.code.toByte() || c == '/'.code.toByte()

        private fun require(c: Char) {
            if (skipWS() != c.code.toByte()) throw AA.unimpl("Missing '$c'")
            X++
        }

        private fun <T> require(c: Char, t: T?): T? {
            require(c)
            return t
        }

        private fun require(s: String?) {//idea says this is always "->"
            skipWS()
            for (i in 0 until s!!.length) if (X + i >= BUF.size || BUF[X + i] != s[i].code.toByte()) throw AA.unimpl("Missing '$s'")
            X += s.length
        }

        init {
            BitsAlias.init0()
            BitsFun.init0()
        }
    }

    override fun toString(): String = String(BUF, X, BUF.size - X)

    // ---------------------------------------------------------------------
    // Worklist of Syntax nodes
    class Worklist {
        var _cnt // Count of items ever popped (not the current length)
                = 0
        private val _ary: Ary<Syntax?> = Ary(Syntax::class.java) // For picking random element
        private val _work: HashSet<Syntax?> = HashSet() // For preventing dups
        fun len(): Int = _ary.len()

        fun push(s: Syntax?) {
            if (s != null && !_work.contains(s)) _work.add(_ary.push(s))
        }

        fun pop(): Syntax? {
            val s = _ary.pop()
            _cnt++
            _work.remove(s)
            return s
        }

        //public Syntax pop() { Syntax s = _ary.del(  _cnt++%_ary._len); _work.remove(s); return s; }
        fun has(s: Syntax?): Boolean = _work.contains(s)

        fun addAll(ss: Ary<out Syntax?>?) {
            if (ss != null) for (s in ss) push(s)
        }

        fun clear() {
            _cnt = 0
            _ary.clear()
            _work.clear()
        }

        override fun toString(): String = _ary.toString()
    }

    // ---------------------------------------------------------------------
    // Small classic tree of T2s, immutable, with sharing at the root parts.
    class VStack(val _par: VStack?, private var _nongen: T2?) : Iterable<T2?> {
        val _d: Int
        fun nongen(): T2 {
            val n = _nongen!!.find()
            return if (n === _nongen) n else n.also { _nongen = it }
        }

        override fun toString(): String {
            // Collect dups across the forest of types
            val dups = VBitSet()
            var vs: VStack? = this
            while (vs != null) {
                vs._nongen!!.get_dups(dups)
                vs = vs._par
            }
            // Now recursively print
            return str(SB(), dups).toString()
        }

        fun str(sb: SB?, dups: VBitSet?): SB? {
            _nongen!!.str(sb, VBitSet(), dups)
            _par?.str(sb!!.p(" , "), dups)
            return sb
        }

        override fun iterator() = Iter() as Iterator<T2?>


        private inner class Iter : Iterator<T2?> {
            private var _vstk: VStack?
            override fun hasNext(): Boolean = _vstk != null

            override fun next(): T2 {
                val v = _vstk!!.nongen()
                _vstk = _vstk!!._par
                return v
            }

            init {
                _vstk = this@VStack
            }
        }

        init {
            _d = if (_par == null) 0 else _par._d + 1
        }
    }

    // ---------------------------------------------------------------------
    abstract class Syntax {
        var _par // Parent in the AST
                : Syntax? = null
        var _nongen // Non-generative type variables
                : VStack? = null

        @JvmField
        var _hmt // Current HM type
                : T2? = null

        fun find(): T2 {                 // U-F find
            val t = _hmt!!.find()
            return if (t === _hmt) t else t.also { _hmt = it }
        }

        fun debug_find(): T2 = _hmt!!.debug_find() // Find, without the roll-up

        // Dataflow types.  Varies during a run of GCP.
        var _flow: Type<*>? = null

        // Compute a new HM type.
        // If no change, return false.
        // If a change, return always true, however:
        // - If 'work' is null do not change/set anything.
        // - If 'work' is available, update the worklist.
        abstract fun hm(work: Worklist?): Boolean
        abstract fun add_hm_work(work: Worklist?) // Add affected neighbors to worklist

        // Compute and return (and do not set) a new GCP type for this syntax.
        abstract fun `val`(work: Worklist?): Type<*>?
        open fun add_val_work(child: Syntax?, work: Worklist?) {} // Add affected neighbors to worklist

        // First pass to "prepare" the tree; does e.g. Ident lookup, sets initial
        // type-vars and counts tree size.
        abstract fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int
        fun prep_tree_impl(par: Syntax?, nongen: VStack?, work: Worklist?, t: T2?) {
            _par = par
            _hmt = t
            _flow = Type.XSCALAR
            _nongen = nongen
            work!!.push(this)
        }

        open fun prep_lookup_deps(id: Ident?) {}

        // Giant Assert: True if OK; all Syntaxs off worklist do not make progress
        abstract fun more_work(work: Worklist?): Boolean
        fun more_work_impl(work: Worklist?): Boolean {
            if (work!!.has(this)) return true
            if (DO_HM && hm(null)) // Any more HM work?
                return false // Found HM work not on worklist
            return !(DO_GCP && `val`(null) !== _flow) // Found GCP work not on worklist
        }

        // Print for debugger
        override fun toString(): String = str(SB()).toString()

        abstract fun str(sb: SB?): SB?

        // Line-by-line print with more detail
        fun p(): String = p0(SB(), VBitSet()).toString()

        fun p0(sb: SB?, dups: VBitSet?): SB? {
            _hmt!!.get_dups(dups)
            val visit = VBitSet()
            p1(sb!!.i())
            if (DO_HM) _hmt!!.str(sb.p(", HM="), visit, dups)
            if (DO_GCP) _flow!!.str(sb.p(", CCP="), visit.clr(), null, false)
            sb.nl()
            return p2(sb.ii(1), dups)!!.di(1)
        }

        abstract fun p1(sb: SB?): SB? // Self short print
        abstract fun p2(sb: SB?, dups: VBitSet?): SB? // Recursion print
    }

    internal class Con(val _con: Type<*>?) : Syntax() {
        override fun str(sb: SB?): SB? = p1(sb)

        override fun p1(sb: SB?): SB? = sb!!.p(_con.toString())

        override fun p2(sb: SB?, dups: VBitSet?): SB? = sb

        override fun hm(work: Worklist?): Boolean = false

        override fun `val`(work: Worklist?): Type<*>? = _con

        override fun add_hm_work(work: Worklist?) {}
        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            // A '0' turns into a nilable leaf.
            val base = if (_con === Type.XNIL) T2.make_nil(T2.make_leaf()) else T2.make_base(_con)
            prep_tree_impl(par, nongen, work, base)
            return 1
        }

        override fun more_work(work: Worklist?): Boolean = more_work_impl(work)
    }

    class Ident(  // The identifier name
            val _name: String?) : Syntax() {
        var _def // Cached syntax defining point
                : Syntax? = null
        var _idx // Index in Lambda (which arg of many)
                = 0
        var _idt // Cached type var for the name in scope
                : T2? = null

        override fun str(sb: SB?): SB? = p1(sb)

        override fun p1(sb: SB?): SB? = sb!!.p(_name)

        override fun p2(sb: SB?, dups: VBitSet?): SB? = sb

        fun idt(): T2 {
            val idt = _idt!!.find()
            return if (idt === _idt) idt else idt.also { _idt = it }
        }

        override fun hm(work: Worklist?): Boolean = idt().fresh_unify(find(), _nongen, work)

        override fun add_hm_work(work: Worklist?) {
            work!!.push(_par)
            val t = idt()
            if (t.nongen_in(if (_par == null) null else _par!!._nongen)) // Got captured in some parent?
                t.add_deps_work(work) // Need to revisit dependent ids
            if (_par is Apply && (_par as Apply?)!!._fun is NotNil) work.push((_par as Apply?)!!._fun)
        }

        override fun `val`(work: Worklist?): Type<*>? =
                if (_def is Let) (_def as Let?)!!._def!!._flow else (_def as Lambda?)!!._types!![_idx]

        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            prep_tree_impl(par, nongen, work, T2.make_leaf())
            run {
                var syn = _par
                while (syn != null) {
                    syn!!.prep_lookup_deps(this)
                    syn = syn!!._par
                }
            }

            // Lookup, and get the T2 type var and a pointer to the flow type.
            var syn = _par
            while (syn != null) {
                if (syn is Lambda) {
                    val lam = syn as Lambda?
                    if (Util.find(lam!!._args, _name).also { _idx = it } != -1) return _init(lam, lam.targ(_idx))
                } else if (syn is Let) {
                    val let = syn as Let?
                    _idx = -1
                    if (Util.eq(let!!._arg0, _name)) return _init(let, let._targ)
                }
                syn = syn!!._par
            }
            throw RuntimeException("Parse error, $_name is undefined in $_par")
        }

        private fun _init(def: Syntax?, idt: T2?): Int {
            _def = def
            _idt = idt
            return 1
        }

        override fun more_work(work: Worklist?): Boolean = more_work_impl(work)
    }

    open class Lambda(body: Syntax?, vararg args: String) : Syntax() {
        val _args: Array<String?>?
        val _body: Syntax?
        val _targs: Array<T2?>?
        val _types: Array<Type<*>?>?
        val _fidx: Int
        override fun str(sb: SB?): SB? {
            sb!!.p("{ ")
            for (arg in _args!!) sb.p(arg).p(' ')
            return _body!!.str(sb.p("-> "))!!.p(" }")
        }

        override fun p1(sb: SB?): SB? {
            sb!!.p("{ ")
            for (i in _args!!.indices) {
                sb.p(_args[i])
                if (DO_HM) sb.p(", HM=").p(targ(i).toString())
                if (DO_GCP) sb.p(", CCP=").p(_types!![i])
                sb.nl().i().p("  ")
            }
            return sb.p(" -> ... } ")
        }

        override fun p2(sb: SB?, dups: VBitSet?): SB? = _body!!.p0(sb, dups)

        fun targ(i: Int): T2 {
            val targ = _targs!![i]!!.find()
            return if (targ === _targs[i]) targ else targ.also { _targs[i] = it }
        }

        override fun hm(work: Worklist?): Boolean {
            var progress = false
            // The normal lambda work
            val old = find()
            if (old.is_err()) return false
            if (old.is_fun()) {      // Already a function?  Compare-by-parts
                for (i in _targs!!.indices) if (old.args(i).unify(targ(i), work)) {
                    progress = true
                    break
                }
                if (!progress && !old.args(_targs.size).unify(_body!!.find(), work)) return false // Shortcut: no progress, no allocation
            }
            // Make a new T2 for progress
            val targs = Arrays.copyOf(_targs, _targs!!.size + 1)
            targs!![_targs.size] = _body!!.find()
            val `fun` = T2.make_fun(BitsFun.make0(_fidx), *targs)
            return old.unify(`fun`, work)
        }

        override fun add_hm_work(work: Worklist?) {
            work!!.push(_par)
            work.push(_body)
            for (i in _targs!!.indices) if (targ(i).occurs_in_type(find())) work.addAll(targ(i)._deps)
        }

        override fun `val`(work: Worklist?): Type<*>? = TypeFunPtr.make(_fidx, _args!!.size, Type.ANY)

        // Ignore arguments, and return body type.  Very conservative.
        open fun apply(args: Array<Syntax?>?): Type<*>? = _body!!._flow

        override fun add_val_work(child: Syntax?, work: Worklist?) {
            // Body changed, all Apply sites need to recompute
            work!!.addAll(find()._deps)
        }

        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            prep_tree_impl(par, nongen, work, T2.make_leaf())
            var vs = nongen
            for (targ in _targs!!) vs = VStack(vs, targ)
            return _body!!.prep_tree(this, vs, work) + 1
        }

        override fun prep_lookup_deps(id: Ident?) = _args!!.indices
                .filter { Util.eq(_args[it], id!!._name) }
                .forEach { _targs!![it]!!.push_update(id) }

        override fun more_work(work: Worklist?): Boolean =
                if (!more_work_impl(work)) false else _body!!.more_work(work)

        companion object {
            // Map from FIDXs to Lambdas
            val FUNS: NonBlockingHashMapLong<Lambda?> = NonBlockingHashMapLong()
        }

        init {
            _args = args as Array<String?>
            _body = body
            // Type variables for all arguments
            _targs = arrayOfNulls<T2?>(args.size)
            for (i in 0 until args.size) _targs[i] = T2.make_leaf()
            // Flow types for all arguments
            _types = arrayOfNulls<Type<*>?>(args.size)
            for (i in 0 until args.size) _types[i] = Type.XSCALAR
            // A unique FIDX for this Lambda
            _fidx = BitsFun.new_fidx()
            FUNS[_fidx.toLong()] = this
            _flow = `val`(null)
        }
    }

    internal class Let(val _arg0: String?, val _def: Syntax?, val _body: Syntax?) : Syntax() {
        var _targ: T2?
        override fun str(sb: SB?): SB? = _body!!.str(_def!!.str(sb!!.p(_arg0).p(" = "))!!.p("; "))

        override fun p1(sb: SB?): SB? = sb!!.p(_arg0).p(" = ... ; ...")

        override fun p2(sb: SB?, dups: VBitSet?): SB? {
            _def!!.p0(sb, dups)
            return _body!!.p0(sb, dups)
        }

        override fun hm(work: Worklist?): Boolean = false

        override fun add_hm_work(work: Worklist?) {
            work!!.push(_par)
            work.push(_body)
            work.push(_def)
            work.addAll(_def!!.find()._deps)
        }

        override fun `val`(work: Worklist?): Type<*>? = _body!!._flow

        override fun add_val_work(child: Syntax?, work: Worklist?) {
            if (child === _def) work!!.addAll(_def!!.find()._deps)
        }

        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            prep_tree_impl(par, nongen, work, _body!!._hmt)
            val cnt = _body.prep_tree(this, nongen, work) +
                    _def!!.prep_tree(this, VStack(nongen, _targ), work)
            _hmt = _body._hmt // Unify 'Let._hmt' with the '_body'
            _targ!!.unify(_def.find(), work)
            return cnt + 1
        }

        override fun prep_lookup_deps(id: Ident?) {
            if (Util.eq(id!!._name, _arg0)) _targ!!.push_update(id)
        }

        override fun more_work(work: Worklist?): Boolean =
                if (!more_work_impl(work)) false else _body!!.more_work(work) && _def!!.more_work(work)

        init {
            _targ = T2.make_leaf()
        }
    }

    open class Apply(val _fun: Syntax?, vararg args: Syntax?) : Syntax() {
        val _args: Array<Syntax?>?
        override fun str(sb: SB?): SB? {
            _fun!!.str(sb!!.p("("))!!.p(" ")
            for (arg in _args!!) arg!!.str(sb)!!.p(" ")
            return sb.unchar().p(")")
        }

        override fun p1(sb: SB?): SB? = sb!!.p("(...)")

        override fun p2(sb: SB?, dups: VBitSet?): SB? {
            _fun!!.p0(sb, dups)
            for (arg in _args!!) arg!!.p0(sb, dups)
            return sb
        }

        // Unifiying these: make_fun(this.arg0 this.arg1 -> new     )
        //                      _fun{_fun.arg0 _fun.arg1 -> _fun.rez}
        override fun hm(work: Worklist?): Boolean {
            var progress = false

            // Progress if:
            //   _fun is not a function
            //   any arg-pair-unifies make progress
            //   this-unify-_fun.return makes progress
            var tfun = _fun!!.find()
            if (!tfun.is_fun()) {    // Not a function, so progress
                if (tfun.is_err()) return find().unify(tfun, work)
                if (work == null) return true // Will-progress & just-testing
                val targs = arrayOfNulls<T2?>(_args!!.size + 1)
                for (i in _args.indices) targs[i] = _args[i]!!.find()
                targs[_args.size] = find() // Return
                val nfun = T2.make_fun(BitsFun.FULL, *targs)
                progress = tfun.unify(nfun, work)
                return if (tfun.find().is_err()) find().unify(tfun.find(), work) else progress
            }
            if (tfun._args!!.size != _args!!.size + 1) progress = T2.make_err("Mismatched argument lengths").unify(find(), work)
            // Check for progress amongst arg pairs
            for (i in _args.indices) {
                progress = progress or tfun.args(i).unify(_args[i]!!.find(), work)
                if (progress && work == null) return true // Will-progress & just-testing early exit
                if (tfun.find().also { tfun = it }.is_err()) return find().unify(tfun, work)
            }
            // Check for progress on the return
            progress = progress or tfun.args(_args.size).unify(find(), work)
            return if (tfun.find().also { tfun = it }.is_err()) find().unify(tfun, work) else progress
        }

        override fun add_hm_work(work: Worklist?) {
            work!!.push(_par)
            for (arg in _args!!) work.push(arg)
        }

        override fun `val`(work: Worklist?): Type<*>? {
            val flow = _fun!!._flow
            if (flow!!.above_center()) return Type.XSCALAR
            if (flow !is TypeFunPtr) return Type.SCALAR
            val tfp = flow as TypeFunPtr?
            // Have some functions, meet over their returns.
            var rez = Type.XSCALAR
            if (tfp!!._fidxs === BitsFun.FULL) rez = Type.SCALAR else for (fidx in tfp!!._fidxs) rez = rez!!.meet(Lambda.FUNS[fidx.toLong()]!!.apply(_args))
            if (rez === Type.XSCALAR) // Fast path cutout, no improvement possible
                return rez

            // Attempt to lift the result, based on HM types.  Walk the input HM type
            // and CCP flow type in parallel and create a mapping.  Then walk the
            // output HM type and CCP flow type in parallel, and join output CCP
            // types with the matching input CCP type.
            if (DO_HM) {
                T2MAP.clear()
                WDUPS.clear()
                // Walk the inputs, building a mapping
                _fun.find().walk_types_in(_fun._flow)
                for (arg in _args!!) {
                    WDUPS.clear()
                    arg!!.find().walk_types_in(arg._flow)
                }
                // Walk the outputs, building an improved result
                val rez2 = find().walk_types_out(rez)
                rez = rez2!!.join(rez) // Lift result
                if (!_flow!!.isa(rez)) rez = _flow // TODO: Cheaty force monotonic
            }
            return rez
        }

        override fun add_val_work(child: Syntax?, work: Worklist?) {
            // If function changes type, recompute self
            if (child === _fun) work!!.push(this)
            // If an argument changes type, adjust the lambda arg types
            val flow = _fun!!._flow
            if (flow!!.above_center()) return
            if (flow !is TypeFunPtr) return
            // Meet the actuals over the formals.
            for (fidx in (flow as TypeFunPtr?)!!._fidxs) {
                val `fun` = Lambda.FUNS[fidx.toLong()]
                if (`fun` != null) {
                    `fun`.find().push_update(this) // Discovered as call-site; if the Lambda changes the Apply needs to be revisited.
                    for (i in `fun`._types!!.indices) {
                        val formal = `fun`._types[i]
                        val actual = if (this is Root) Root.widen(`fun`.targ(i)) else _args!![i]!!._flow
                        val rez = formal!!.meet(actual)
                        if (formal !== rez) {
                            `fun`._types[i] = rez
                            work!!.addAll(`fun`.targ(i)._deps)
                            work.push(`fun`._body)
                            if (i == 0 && `fun` is If) work.push(`fun`) // Specifically If might need more unification
                        }
                    }
                }
            }
        }

        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            prep_tree_impl(par, nongen, work, T2.make_leaf())
            var cnt = 1 + _fun!!.prep_tree(this, nongen, work)
            for (arg in _args!!) cnt += arg!!.prep_tree(this, nongen, work)
            return cnt
        }

        override fun more_work(work: Worklist?): Boolean {
            if (!more_work_impl(work)) return false
            if (!_fun!!.more_work(work)) return false
            for (arg in _args!!) if (!arg!!.more_work(work)) return false
            return true
        }

        companion object {
            val T2MAP: HashMap<T2?, Type<*>?> = HashMap()
            val WDUPS: NonBlockingHashMapLong<String?> = NonBlockingHashMapLong()
        }

        init {
            _args = args as Array<Syntax?>
        }
    }

    class Root(body: Syntax?) : Apply(body) {
        override fun str(sb: SB?): SB? = _fun!!.str(sb)

        override fun hm(work: Worklist?): Boolean = find().unify(_fun!!.find(), work)

        override fun add_hm_work(work: Worklist?) {}
        override fun `val`(work: Worklist?): Type<*>? {
            if (_fun!!._flow!!.above_center() || work == null) return _fun._flow
            // Root-widening needs to call all functions which can be returned from
            // the Root or from any function reachable from the Root via struct &
            // fields, or by being returned from another function.
            val fidxs = find().find_fidxs()
            if (fidxs !== BitsFun.EMPTY) for (fidx in fidxs!!) {
                val `fun` = Lambda.FUNS[fidx.toLong()]
                if (`fun` != null) {
                    `fun`.find().push_update(this) // Discovered as call-site; if the Lambda changes the Apply needs to be revisited.
                    // For each returned function, assume Root calls all arguments with
                    // worse-case values.
                    for (i in `fun`._types!!.indices) {
                        val formal = `fun`._types[i]
                        val actual = widen(`fun`.targ(i))
                        val rez = formal!!.meet(actual)
                        if (formal !== rez) {
                            `fun`._types[i] = rez
                            work.addAll(`fun`.targ(i)._deps)
                            work.push(`fun`._body)
                        }
                    }
                }
            }
            return _fun._flow
        }

        // Expand functions to full signatures, recursively
        fun flow_type(): Type<*>? = add_sig(_flow)

        companion object {
            val NARGS: Array<Syntax?> = arrayOfNulls<Syntax?>(0)

            // Root-widening is when Root acts as-if it is calling the returned
            // function with the worse-case legal args.
            fun widen(t2: T2?): Type<*>? = t2!!.as_flow()

            private fun add_sig(t: Type<*>?): Type<*>? {
                return if (t is TypeFunPtr) {
                    val `fun` = t as TypeFunPtr?
                    var rez = Type.XSCALAR
                    for (fidx in `fun`!!._fidxs) rez = rez!!.meet(Lambda.FUNS[fidx.toLong()]!!.apply(NARGS))
                    val rez2 = add_sig(rez)
                    TypeFunSig.make(TypeTuple.make_ret(rez2), TypeTuple.make_args())
                } else {
                    t
                }
            }
        }
    }

    // Structure or Records.
    internal class Struct(val _ids: Array<String?>?, val _flds: Array<Syntax?>?) : Syntax() {
        val _alias: Int
        override fun str(sb: SB?): SB? {
            sb!!.p("@{").p(_alias)
            for (i in _ids!!.indices) {
                sb.p(' ').p(_ids[i]).p(" = ")
                _flds!![i]!!.str(sb)
                if (i < _ids.size - 1) sb.p(',')
            }
            return sb.p("}")
        }

        override fun p1(sb: SB?): SB? = sb!!.p("@{").p(_alias).p(" ... } ")

        override fun p2(sb: SB?, dups: VBitSet?): SB? {
            for (i in _ids!!.indices) _flds!![i]!!.p0(sb!!.i().p(_ids[i]).p(" = ").nl(), dups)
            return sb
        }

        override fun hm(work: Worklist?): Boolean {
            var progress = false
            var must_alloc = false

            // Force result to be a struct with at least these fields.
            // Do not allocate a T2 unless we need to pick up fields.
            var rec = find()
            if (rec.is_err()) return false
            for (id in _ids!!) if (Util.find(rec._ids, id) == -1) {
                must_alloc = true
                break
            }
            if (must_alloc) {              // Must allocate.
                if (work == null) return true // Will progress
                val t2s = arrayOfNulls<T2?>(_ids.size)
                for (i in _ids.indices) t2s[i] = _flds!![i]!!.find()
                make_struct(BitsAlias.make0(_alias), _ids, t2s as Array<T2>).unify(rec, work)
                rec = find()
                progress = true
            }

            // Extra fields are unified with ERR since they are not created here:
            // error to load from a non-existing field
            for (i in rec._ids!!.indices) {
                if (Util.find(_ids, rec._ids!![i]) == -1 && !rec.args(i).is_err()) {
                    if (work == null) return true
                    progress = progress or rec.args(i).unify(find().miss_field(rec._ids!![i]), work)
                }
            }

            // Unify existing fields.  Ignore extras on either side.
            for (i in _ids.indices) {
                val idx = Util.find(rec._ids, _ids[i])
                if (idx != -1) progress = progress or rec.args(idx).unify(_flds!![i]!!.find(), work)
                if (work == null && progress) return true
            }
            rec.push_update(this)
            return progress
        }

        override fun add_hm_work(work: Worklist?) {
            work!!.push(_par)
            for (fld in _flds!!) work.push(fld)
        }

        override fun `val`(work: Worklist?): Type<*>? {
            val ts = TypeFlds.get(_flds!!.size + 1)
            ts!![0] = TypeFld.NO_DISP
            for (i in _flds.indices) ts[i + 1] = TypeFld.make(_ids!![i], _flds[i]!!._flow, TypeFld.Access.Final, i + 1)
            val tstr = TypeStruct.make(*ts)
            val t2 = tstr!!.approx(1, _alias)
            return TypeMemPtr.make(_alias, t2)
        }

        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            val t2s = arrayOfNulls<T2?>(_ids!!.size)
            prep_tree_impl(par, nongen, work, make_struct(BitsAlias.make0(_alias), _ids, t2s as Array<T2>))
            var cnt = 1 // One for self
            for (i in _flds!!.indices) { // Prep all sub-fields
                cnt += _flds[i]!!.prep_tree(this, nongen, work)
                t2s[i] = _flds[i]!!.find()
            }
            return cnt
        }

        override fun more_work(work: Worklist?): Boolean {
            if (!more_work_impl(work)) return false
            for (fld in _flds!!) if (!fld!!.more_work(work)) return false
            return true
        }

        init {
            // Make a TMP
            _alias = BitsAlias.new_alias(BitsAlias.REC)
        }
    }

    // Field lookup in a Struct
    internal class Field(val _id: String?, val _rec: Syntax?) : Syntax() {
        override fun str(sb: SB?): SB? = _rec!!.str(sb)!!.p(".").p(_id)

        override fun p1(sb: SB?): SB? = sb!!.p(".").p(_id)

        override fun p2(sb: SB?, dups: VBitSet?): SB? = _rec!!.p0(sb, dups)

        override fun hm(work: Worklist?): Boolean {
            return if (!find().is_err()) {
                val rec = _rec!!.find()
                if (rec.is_nilable() || rec._alias != null && rec._alias!!.test(0))
                    return find().unify(T2.make_err("May be nil when loading field $_id"), work)
                rec.push_update(this)
                val idx = if (rec._ids == null) -1 else Util.find(rec._ids, _id)
                when {
                    /** Unify against a pre-existing field */
                    idx != -1
                    -> rec.args(idx).unify(find(), work)
                    // The remaining cases all make progress and return true
                    work == null -> true
                    rec.is_err() -> find().unify(rec, work)
                    // Not a struct or no field, force it to be one
                    rec.is_struct() && rec._open // Effectively unify with an extended struct.
                    -> rec.add_fld(_id, find(), work)
                    else -> if (rec.is_leaf()) make_struct(BitsAlias.EMPTY, arrayOf(_id), arrayOf(find().push_update(rec._deps)), true).unify(rec, work) else find().unify(rec.miss_field(_id), work)
                }
            } else false // Already an error; no progress
        }

        override fun add_hm_work(work: Worklist?) {
            work!!.push(_par)
            work.push(_rec)
            _rec!!.add_hm_work(work)
        }

        override fun `val`(work: Worklist?): Type<*>? {
            val trec = _rec!!._flow
            if (trec!!.above_center()) return Type.XSCALAR
            if (trec is TypeMemPtr) {
                val tmp = trec as TypeMemPtr?
                if (tmp!!._obj is TypeStruct) {
                    val tstr = tmp._obj as TypeStruct
                    val idx = tstr.fld_find(_id)
                    if (idx != -1) return tstr.at(idx) // Field type
                }
                if (tmp._obj.above_center()) return Type.XSCALAR
            }
            // TODO: Need an error type here
            return Type.SCALAR
        }

        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            prep_tree_impl(par, nongen, work, T2.make_leaf())
            return _rec!!.prep_tree(this, nongen, work) + 1
        }

        override fun more_work(work: Worklist?): Boolean = if (!more_work_impl(work)) false else _rec!!.more_work(work)
    }

    abstract class PrimSyn(vararg t2s: T2?) : Lambda(null, *IDS[t2s.size - 1]!! as Array<out String>), Cloneable {
        abstract fun name(): String?
        abstract fun make(): PrimSyn?
        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            prep_tree_impl(par, nongen, work, _hmt)
            return 1
        }

        override fun hm(work: Worklist?): Boolean {
            val old = find()
            if (old.is_err()) return false
            assert(old.is_fun())
            for (i in _targs!!.indices) if (targ(i).is_err()) return old.unify(targ(i), work)
            return false
        }

        override fun add_hm_work(work: Worklist?) {
            if (find().is_err()) work!!.push(_par)
        }

        override fun add_val_work(child: Syntax?, work: Worklist?) {
            throw AA.unimpl()
        }

        override fun more_work(work: Worklist?): Boolean = more_work_impl(work)

        override fun str(sb: SB?): SB? = sb!!.p(name())

        override fun p1(sb: SB?): SB? = sb!!.p(name())

        override fun p2(sb: SB?, dups: VBitSet?): SB? = sb

        companion object {
            var BOOL: T2? = null
            var INT64: T2? = null
            var FLT64: T2? = null
            var STRP: T2? = null
            var WORK: Worklist? = null
            var PAIR_ALIAS = 0
            var TRIPLE_ALIAS = 0
            fun reset() {
                PAIR_ALIAS = BitsAlias.new_alias(BitsAlias.REC)
                TRIPLE_ALIAS = BitsAlias.new_alias(BitsAlias.REC)
                BOOL = T2.make_base(TypeInt.BOOL)
                INT64 = T2.make_base(TypeInt.INT64)
                FLT64 = T2.make_base(TypeFlt.FLT64)
                STRP = T2.make_base(TypeMemPtr.STRPTR)
            }

            private val IDS: Array<Array<String?>?> = arrayOf(
                    null, arrayOf("x"), arrayOf("x", "y"), arrayOf("x", "y", "z"))
        }

        init {
            _hmt = T2.make_fun(BitsFun.make0(_fidx), *t2s).fresh()
            for (i in _targs!!.indices) _targs[i] = _hmt!!.args(i).push_update(this)
        }
    }

    // Curried Pair
    internal class Pair1 : PrimSyn(T2.make_leaf().also { var1 = it }, T2.make_fun(BitsFun.ANY, T2.make_leaf().also { var2 = it }, make_struct(BitsAlias.make0(PAIR_ALIAS), arrayOf("0", "1"), arrayOf(var1, var2) as Array<T2>))) {
        override fun name(): String = "pair1"

        override fun make(): PrimSyn = Pair1()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val t = args!![0]!!._flow
            var p1x = PAIR1S!![t]
            if (p1x == null) PAIR1S!![t] = Pair1X(t).also { p1x = it }
            return p1x!!._flow
        }

        internal class Pair1X(val _con: Type<*>?) : PrimSyn(T2.make_leaf().also { var2 = it }, arrayOf(T2.make_base(_con), var2).let { make_struct(BitsAlias.make0(PAIR_ALIAS), arrayOf<String?>("0", "1"), it as Array<T2>) }) {
            override fun name(): String = "Pair1_$_con"

            override fun make(): PrimSyn? {
                throw AA.unimpl()
            }

            //@Override boolean hm(Worklist work) { throw unimpl(); }
            override fun apply(args: Array<Syntax?>?): Type<*>? {
                val tcon = find().args(1).args(0)
                assert(tcon.is_base())
                return TypeMemPtr.make(PAIR_ALIAS, TypeStruct.make(*TypeStruct.tups(tcon._flow, if (args!!.isEmpty()) Root.widen(_targs!![0]) else args[0]!!._flow)))
            }

            companion object {
                private var var2: T2? = null
            }
        }

        companion object {
            private var var1: T2? = null
            private var var2: T2? = null
            var PAIR1S: HashMap<Type<*>?, Pair1X?>? = HashMap()
        }
    }

    // Pair
    internal class Pair : PrimSyn(T2.make_leaf().also { var1 = it }, T2.make_leaf().also { var2 = it }, make_struct(BitsAlias.make0(PAIR_ALIAS), arrayOf<String?>("0", "1"), arrayOf(var1!!, var2) as Array<T2>)) {
        override fun name(): String = "pair"

        override fun make(): PrimSyn = Pair()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val ts = TypeFlds.get(args!!.size + 1)
            ts!![0] = TypeFld.NO_DISP // Display
            for (i in args.indices) ts[i + 1] = TypeFld.make_tup(args[i]!!._flow, i + 1)
            return TypeMemPtr.make(PAIR_ALIAS, TypeStruct.make(*ts))
        }

        companion object {
            private var var1: T2? = null
            private var var2: T2? = null
        }
    }

    // Triple
    internal class Triple : PrimSyn(T2.make_leaf().also { var1 = it }, T2.make_leaf().also { var2 = it }, T2.make_leaf().also { var3 = it }, make_struct(BitsAlias.make0(TRIPLE_ALIAS), arrayOf<String?>("0", "1", "2"), arrayOf(var1, var2, var3) as Array<T2>)) {
        override fun name(): String = "triple"

        override fun make(): PrimSyn = Triple()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val ts = TypeFlds.get(args!!.size + 1)
            ts!![0] = TypeFld.NO_DISP // Display
            for (i in args.indices) ts[i + 1] = TypeFld.make_tup(args[i]!!._flow, i + 1)
            return TypeMemPtr.make(TRIPLE_ALIAS, TypeStruct.make(*ts))
        }

        companion object {
            private var var1: T2? = null
            private var var2: T2? = null
            private var var3: T2? = null
        }
    }

    // Special form of a Lambda body for IF which changes the H-M rules.
    // None-executing paths do not unify args.
    internal class If : PrimSyn(T2.make_leaf(), T2.make_leaf(), T2.make_leaf(), T2.make_leaf()) {
        override fun name(): String = "if"

        override fun make(): PrimSyn = If()

        override fun hm(work: Worklist?): Boolean {
            val rez = find().args(3)
            // GCP helps HM: do not unify dead control paths
            if (DO_GCP) {            // Doing GCP during HM
                val pred = _types!![0]
                if (pred === TypeInt.FALSE || pred === Type.NIL || pred === Type.XNIL) return rez.unify(targ(2), work) // Unify only the false side
                if (pred!!.above_center()) // Neither side executes
                    return false // Unify neither side
                if (!pred.must_nil()) // Unify only the true side
                    return rez.unify(targ(1), work)
            }
            // Unify both sides with the result
            return rez.unify(targ(1), work) or
                    rez.find().unify(targ(2), work)
        }

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val pred = args!![0]!!._flow
            val t1 = args[1]!!._flow
            val t2 = args[2]!!._flow
            // Conditional Constant Propagation: only prop types from executable sides
            if (pred === TypeInt.FALSE || pred === Type.NIL || pred === Type.XNIL) return t2 // False only
            if (pred!!.above_center()) // Delay any values
                return Type.XSCALAR // t1.join(t2);     // Join of either
            return if (!pred.must_nil()) t1 else t1!!.meet(t2)
            // Could be either, so meet
        }
    }

    // EQ
    internal class EQ : PrimSyn(T2.make_leaf().also { var1 = it }, var1, BOOL) {
        override fun name(): String = "eq"

        override fun make(): PrimSyn = EQ()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val x0 = args!![0]!!._flow
            val x1 = args[1]!!._flow
            if (x0!!.above_center() || x1!!.above_center()) return TypeInt.BOOL.dual()
            return if (x0.is_con && x1.is_con && x0 === x1) TypeInt.TRUE else TypeInt.BOOL
            // TODO: Can also know about nil/not-nil
        }

        companion object {
            private var var1: T2? = null
        }
    }

    // EQ0
    internal class EQ0 : PrimSyn(INT64, BOOL) {
        override fun name(): String = "eq0"

        override fun make(): PrimSyn = EQ0()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val pred = args!![0]!!._flow
            if (pred!!.above_center()) return TypeInt.BOOL.dual()
            if (pred === Type.ALL) return TypeInt.BOOL
            if (pred === TypeInt.FALSE || pred === Type.NIL || pred === Type.XNIL) return TypeInt.TRUE
            return if (pred.meet_nil(Type.NIL) !== pred) TypeInt.FALSE else TypeInt.BOOL
        }
    }

    internal class IsEmpty : PrimSyn(STRP, BOOL) {
        override fun name(): String = "isempty"

        override fun make(): PrimSyn = IsEmpty()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val pred = args!![0]!!._flow
            if (pred!!.above_center()) return TypeInt.BOOL.dual()
            lateinit var to: TypeObj<*>
            return if (pred is TypeMemPtr && (pred as TypeMemPtr?)!!._obj.also { to = it } is TypeStr && to.is_con) TypeInt.con(if (to.getstr().isEmpty()) 1 else 0.toLong()) else TypeInt.BOOL
        }
    }

    // Remove a nil from a struct after a guarding if-test
    internal class NotNil : PrimSyn(T2.make_leaf(), T2.make_leaf()) {
        override fun name(): String = " notnil"

        override fun make(): PrimSyn = NotNil()

        override fun prep_tree(par: Syntax?, nongen: VStack?, work: Worklist?): Int {
            val cnt = super.prep_tree(par, nongen, work)
            find().args(1).push_update(this)
            return cnt
        }

        override fun hm(work: Worklist?): Boolean {
            val arg = targ(0)
            if (arg.is_err()) return false // Already an error
            val `fun` = find()
            assert(`fun`.is_fun())
            val ret = `fun`.args(1)
            // If the arg is already nilchecked, can be a nilable of a nilable.
            if (arg === ret) return false
            // Already an expanded nilable
            if (arg.is_nilable() && arg.args(0) === ret) return false
            // Already an expanded nilable with base
            if (arg.is_base() && ret.is_base()) {
                if (arg._flow === ret._flow!!.meet_nil(Type.XNIL)) return false
                if (work == null) return true
                val mt = arg._flow!!.meet(ret._flow)
                val rflow = mt!!.join(Type.NSCALR)
                val aflow = mt.meet_nil(Type.XNIL)
                if (rflow !== ret._flow) {
                    ret._flow = rflow
                    work.push(_par)
                }
                if (aflow !== arg._flow) {
                    arg._flow = aflow
                    work.push(_par)
                }
                return true
            }
            // Already an expanded nilable with struct
            if (arg.is_struct() && ret.is_struct() && arg._alias === arg._alias!!.meet_nil() && arg._ids!!.size == ret._ids!!.size) {
                // But cannot just check the aliases, since they may not match.
                // Also check that the fields align
                var progress = false
                for (i in arg._ids!!.indices) if (!Util.eq(arg._ids!![i], ret._ids!![i]) ||
                        arg.args(i) !== ret.args(i)) {
                    progress = true
                    break
                } // Field/HMtypes misalign
                if (!progress) return false // No progress
            }
            if (work == null) return true
            // If the arg is already nilchecked, can be a nilable of a nilable.
            return if (arg.is_nilable() && ret.is_nilable()) arg.unify(ret, work) else T2.make_nil(ret).find().unify(arg, work)
            // Unify with arg with a nilable version of the ret.
        }

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val `val` = args!![0]!!._flow
            return if (`val` === Type.XNIL) Type.XSCALAR else `val`!!.join(Type.NSCALR) // Weird case of not-nil nil
        }
    }

    // multiply
    internal class Mul : PrimSyn(INT64, INT64, INT64) {
        override fun name(): String = "*"

        override fun make(): PrimSyn = Mul()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val t0 = args!![0]!!._flow
            val t1 = args[1]!!._flow
            if (t0!!.above_center() || t1!!.above_center()) return TypeInt.INT64.dual()
            if (t0 is TypeInt && t1 is TypeInt) {
                if (t0.is_con() && t0.getl() == 0L) return TypeInt.ZERO
                if (t1.is_con() && t1.getl() == 0L) return TypeInt.ZERO
                if (t0.is_con() && t1.is_con()) return TypeInt.con(t0.getl() * t1.getl())
            }
            return TypeInt.INT64
        }
    }

    // add integers
    internal class Add : PrimSyn(INT64, INT64, INT64) {
        override fun name(): String = "+"

        override fun make(): PrimSyn = Add()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val t0 = args!![0]!!._flow
            val t1 = args[1]!!._flow
            if (t0!!.above_center() || t1!!.above_center()) return TypeInt.INT64.dual()
            if (t0 is TypeInt && t1 is TypeInt) {
                if (t0.is_con() && t1.is_con()) return TypeInt.con(t0.getl() + t1.getl())
            }
            return TypeInt.INT64
        }
    }

    // decrement
    internal class Dec : PrimSyn(INT64, INT64) {
        override fun name(): String = "dec"

        override fun make(): PrimSyn = Dec()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val t0 = args!![0]!!._flow
            if (t0!!.above_center()) return TypeInt.INT64.dual()
            return if (t0 is TypeInt && t0.is_con()) TypeInt.con(t0.getl() - 1) else TypeInt.INT64
        }
    }

    // int->str
    internal class Str : PrimSyn(INT64, STRP) {
        override fun name(): String = "str"

        override fun make(): PrimSyn = Str()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val i = args!![0]!!._flow
            if (i!!.above_center()) return TypeMemPtr.STRPTR.dual()
            return if (i is TypeInt && i.is_con()) TypeMemPtr.make(BitsAlias.STRBITS, TypeStr.con(i.getl().toString().intern())) else TypeMemPtr.STRPTR
        }
    }

    // flt->(factor flt flt)
    internal class Factor : PrimSyn(FLT64, FLT64) {
        override fun name(): String = "factor"

        override fun make(): PrimSyn = Factor()

        override fun apply(args: Array<Syntax?>?): Type<*>? {
            val flt = args!![0]!!._flow
            return if (flt!!.above_center()) TypeFlt.FLT64.dual() else TypeFlt.FLT64
        }
    }

    // ---------------------------------------------------------------------
    // T2 types form a Lattice, with 'unify' same as 'meet'.  T2's form a DAG
    // (cycles if i allow recursive unification) with sharing.  Each Syntax has a
    // T2, and the forest of T2s can share.  Leaves of a T2 can be either a
    // simple concrete base type, or a sharable leaf.  Unify is structural, and
    // where not unifyable the union is replaced with an Error.
    class T2 private constructor(name: String) : Cloneable {
        val _uid: Int

        // A plain type variable starts with a 'V', and can unify directly.
        // Everything else is structural - during unification they must match names
        // and arguments and Type constants.
        var _name // name, e.g. "->" or "pair" or "V123" or "base"
                : String

        // Structural parts to unify with, or slot 0 is used during normal U-F
        var _args: Array<T2?>? = null

        // A dataflow type.  Unused for everything except base type-vars (i.e.
        // constants, primitive tvars).  Splitting these to make it easier to tease
        // apart when they should be used, and when not.  Root needs a way to
        // recursively make a flow type from an HM type and the confusion is that
        // the _flow field is a valid flow type... it is not except and only for
        // Base types.
        var _flow: Type<*>? = null
        var _fidxs // Unused except for is_fun
                : BitsFun? = null

        // Structs have field names and aliases
        var _alias // Unused except for is_struct and NIL
                : BitsAlias? = null
        var _ids: Array<String?>? = null
        var _open // Struct can be extended
                = false
        var _err // Error
                : String? = null

        // Dependent (non-local) tvars to revisit
        var _deps: Ary<Syntax?>? = null
        fun miss_field(id: String?): T2 = make_err("Missing field " + id + " in " + p())

        fun copy(): T2 {
            val t = T2(_name)
            if (_args != null) t._args = arrayOfNulls<T2?>(_args!!.size)
            t._flow = _flow
            t._fidxs = _fidxs
            t._alias = _alias
            t._ids = _ids
            t._err = _err
            t._deps = _deps
            t._open = _open
            return t
        }

        private constructor(name: String, vararg args: T2) : this(name) {
            _args = args as Array<T2?>
        }

        // A type var, not a concrete leaf.  Might be U-Fd or not.
        fun is_leaf(): Boolean = _name[0] == 'V' || _name[0] == 'X'

        fun no_uf(): Boolean = _name[0] != 'X' && (!is_nilable() || _args!![0]!!.is_leaf())

        fun isa(name: String?): Boolean = Util.eq(_name, name)

        fun is_base(): Boolean = isa("Base")

        fun is_nilable(): Boolean = isa("?")

        fun is_fun(): Boolean = isa("->")

        fun is_struct(): Boolean = isa("@{}")

        fun is_err(): Boolean = isa("Err")

        fun debug_find(): T2 { // Find, without the roll-up
            if (!is_leaf()) return this // Shortcut
            if (_args == null) return this
            var u = _args!![0]
            if (u!!.no_uf()) return u // Shortcut
            // U-F search, no fixup
            while (u!!.is_leaf() && !u.no_uf()) u = u._args!![0]
            return u
        }

        fun find(): T2 {
            val u = _find0()
            return if (u.is_nilable()) u._find_nil() else u
        }

        // U-F find
        private fun _find0(): T2 {
            val u = debug_find()
            if (u === this || u === _args!![0]) return u
            var v: T2? = this
            lateinit var v2: T2
            // UF fixup
            while (v!!.is_leaf() && v._args!![0].also { v2 = it as T2 } !== u) {
                v._args!![0] = u
                v = v2
            }
            return u
        }

        // Nilable fixup.  nil-of-leaf is OK.  nil-of-anything-else folds into a
        // nilable version of the anything-else.
        private fun _find_nil(): T2 {
            val n = args(0)
            if (n.is_leaf()) return this
            // Nested nilable-and-not-leaf, need to fixup the nilable
            if (n.is_base()) {
                _flow = n._flow!!.meet_nil(Type.XNIL)
                _args = null
                _name = n._name
            } else if (n.is_struct()) {
                _alias = n._alias!!.meet_nil()
                _args = n._args!!.clone()
                _ids = n._ids!!.clone()
                _open = n._open
                _name = n._name
            } else if (n.is_nilable()) {
                _args!![0] = n.args(0)
            } else throw AA.unimpl()
            if (n._deps != null) {
                if (_deps == null) _deps = n._deps else _deps!!.addAll(n._deps)
            }
            return this
        }

        // U-F find on the args array
        fun args(i: Int): T2 {
            val u = _args!![i]
            val uu = u!!.find()
            return if (u === uu) uu else uu.also { _args!![i] = it }
        }

        fun as_flow(): Type<*>? {
            assert(ADUPS.isEmpty())
            val t = _as_flow()
            ADUPS.clear()
            assert(Type.intern_check())
            return t
        }

        fun _as_flow(): Type<*>? {
            assert(no_uf())
            if (is_base()) return _flow
            if (is_leaf()) return Type.SCALAR
            if (is_err()) return TypeMemPtr.make(BitsAlias.STRBITS, TypeStr.con(_err))
            if (is_fun()) return TypeFunPtr.make(_fidxs, _args!!.size - 1, Type.ANY)
            if (is_nilable()) return Type.SCALAR
            if (is_struct()) {
                var tstr = ADUPS[_uid.toLong()]
                if (tstr == null) {
                    Type.RECURSIVE_MEET++
                    val ts = TypeFlds.get(_ids!!.size + 1)
                    ts!![0] = TypeFld.NO_DISP
                    for (i in _ids!!.indices) ts[i + 1] = TypeFld.malloc(_ids!![i], null, TypeFld.Access.Final, i + 1)
                    tstr = TypeStruct.malloc("", false, ts, true)
                    tstr._hash = tstr.compute_hash()
                    ADUPS[_uid.toLong()] = tstr // Stop cycles
                    for (i in _ids!!.indices) ts[i + 1].setX(args(i)._as_flow()) // Recursive
                    if (--Type.RECURSIVE_MEET == 0) {
                        // Shrink / remove cycle dups.  Might make new (smaller)
                        // TypeStructs, so keep RECURSIVE_MEET enabled.
                        Type.RECURSIVE_MEET++
                        tstr = TypeStruct.shrink(tstr.reachable(), tstr)
                        TypeStruct.UF.clear()
                        Type.RECURSIVE_MEET--
                        // Walk the final cyclic structure and intern everything.
                        tstr.install_cyclic(tstr.reachable())
                    }
                } else {
                    tstr._cyclic = true // Been there, done that, just mark it cyclic
                }
                return TypeMemPtr.make(_alias, tstr)
            }
            throw AA.unimpl()
        }

        // If LHS is null, return RHS (and no progress)
        // If RHS is null, return LHS (and progress)
        // Else return meet (and progress is LHS!=RHS)
        private fun meet_flow(that: T2?): Type<*>? {
            if (_flow == null) return that!!._flow
            return if (that!!._flow == null) _flow else _flow!!.meet(that._flow)
        }

        private fun meet_fidxs(that: T2?): BitsFun? {
            if (_fidxs == null) return that!!._fidxs
            return if (that!!._fidxs == null) _fidxs else _fidxs!!.meet(that._fidxs)
        }

        private fun meet_alias(that: T2?): BitsAlias? {
            if (_alias == null) return that!!._alias
            return if (that!!._alias == null) _alias else _alias!!.meet(that._alias)
        }

        private fun meet_ids(that: T2?): Array<String?>? {
            val ids = that!!._ids
            if (_ids.contentEquals(ids)) return ids
            if (_ids == null) return ids
            if (ids == null) return _ids
            if (_ids!!.size != ids.size) throw AA.unimpl() // Handled at a higher level
            for (id in ids) if (Util.find(_ids, id) == -1) throw AA.unimpl()
            return ids // Return RHS
        }

        private fun meet_opens(that: T2?): Boolean {
            if (_open == that!!._open) return that._open
            if (!is_struct()) return that._open
            if (!that.is_struct()) return _open
            throw AA.unimpl()
        }

        private fun meet_err(that: T2?): String? {
            if (_err == null) return that!!._err
            if (that!!._err == null) return _err
            // TODO: Probably gather unrelated strings in a set
            return if (_uid < that._uid) _err else that._err
        }

        private fun base_states(): Int {
            var cnt = 0
            if (_flow != null) cnt++
            if (_fidxs != null) cnt++
            if (_err != null) cnt++
            if (_alias != null) {
                cnt++
                assert(_ids != null)
            } else assert(_ids == null)
            return cnt
        }

        // U-F union; this becomes that; returns 'that'.
        // No change if only testing, and reports progress.
        fun union(that: T2?, work: Worklist?): Boolean {
            assert(no_uf() && that!!.no_uf() // Cannot union twice
            )
            assert(base_states() <= 1 && that!!.base_states() <= 1)
            if (this === that) return false
            if (work == null) return true // Report progress without changing
            // Keep the merge of all base types, revisiting deps if any changes
            if (_flow !== that!!._flow || _fidxs !== that!!._fidxs || _alias !== that!!._alias || !_ids.contentEquals(that!!._ids) || _open != that._open ||
                    !Util.eq(_err, that._err)) work.addAll(that!!._deps) // Any progress, revisit deps
            // If flow types are not compatible, return an error now
            if (_flow!!.widen() !== that._flow!!.widen() && !_flow!!.isa(that._flow!!.widen()))
                return union_err(that, work, "Cannot unify " + this.p() + " and " + that.p())
            that._flow = meet_flow(that)
            that._fidxs = meet_fidxs(that)
            that._alias = meet_alias(that)
            that._ids = meet_ids(that)!!
            that._open = meet_opens(that)
            that._err = meet_err(that)
            assert(that._flow !== Type.XNIL)
            if (that._err != null) {   // Kill the base types in an error
                that._flow = null
                that._fidxs = null
                that._alias = null
                that._ids = null
            }
            // Hard union this into that, no more testing.
            return _union(that, work)
        }

        // U-F union; this is nilable and becomes that.
        // No change if only testing, and reports progress.
        fun unify_nil(that: T2?, work: Worklist?): Boolean {
            assert(is_nilable() && !that!!.is_nilable())
            if (work == null) return true // Will make progress
            // Clone the top-level struct and make this nilable point to the clone;
            // this will collapse into the clone at the next find() call.
            // Unify the nilable leaf into that.
            val leaf = args(0)
            assert(leaf.is_leaf())
            val copy = that!!.copy()
            if (that.is_base()) {
                copy._flow = copy._flow!!.join(Type.NSCALR)
            } else if (that.is_struct()) {
                copy._alias = copy._alias!!.clear(0)
                System.arraycopy(that._args, 0, copy._args, 0, that._args!!.size)
            } else throw AA.unimpl()
            return leaf._union(copy, work) or that._union(find(), work)
        }

        // Hard unify this into that, no testing for progress.
        private fun _union(that: T2?, work: Worklist?): Boolean {
            assert(that!!.no_uf())
            _flow = null
            _fidxs = null
            _alias = null
            _ids = null
            _err = null // Kill the base types in a unified type
            // Worklist: put updates on the worklist for revisiting
            if (_deps != null) {
                work!!.addAll(_deps) // Re-Apply
                // Merge update lists, for future unions
                if (that._deps == null && that._args == null) that._deps = _deps else for (dep in _deps!!) that.push_update(dep)
                _deps = null
            }
            if (_args == null || _args!!.size != 1) _args = arrayOfNulls<T2?>(1)
            // Unify the two base types, preserving errors
            _args!![0] = that // U-F update
            _name = "X$_uid" // Flag as a leaf & unified
            assert(!no_uf())
            return true
        }

        fun unify(that: T2?, work: Worklist?): Boolean {
            if (this === that) return false
            assert(DUPS.isEmpty())
            val progress = _unify(that, work)
            DUPS.clear()
            return progress
        }

        // Structural unification, 'this' into 'that'.  No change if just testing
        // (work is null) and returns a progress flag.  If updating, both 'this'
        // and 'that' are the same afterwards.
        private fun _unify(that1: T2?, work: Worklist?): Boolean {
            var that = that1
            assert(no_uf() && that!!.no_uf())
            if (this === that) return false

            // All leaf types immediately unify.
            if (_args == null && that!!._args == null) {
                var lhs: T2? = this
                var rhs = that
                if (is_err() ||  // Errors beat all others
                        !that.is_err() && is_base()) {
                    rhs = this
                    lhs = that
                } // Base beats plain leaf
                // If tied, keep lower uid
                if (Util.eq(lhs!!._name, rhs._name) && _uid < that._uid) {
                    rhs = this
                    lhs = that
                }
                return lhs.union(rhs, work)
            }
            // Any leaf immediately unifies with any non-leaf
            if (is_leaf() || that!!.is_err()) return this.union(that, work)
            if (that.is_leaf() || is_err()) return that.union(this, work)
            // Special case for nilable union something
            if (is_nilable() && !that.is_nilable()) return unify_nil(that, work)
            if (that.is_nilable() && !is_nilable()) return that.unify_nil(this, work)

            // Cycle check
            val luid = dbl_uid(that) // long-unique-id formed from this and that
            val rez = DUPS[luid]
            assert(rez == null || rez === that)
            if (rez != null) return false // Been there, done that
            DUPS[luid] = that // Close cycles
            if (work == null) return true // Here we definitely make progress; bail out early if just testing
            if (!Util.eq(_name, that._name)) return union_err(that, work, "Cannot unify " + this.p() + " and " + that.p())
            assert(!_args.contentEquals(that._args) // Not expecting to share _args and not 'this'
            )

            // Structural recursion unification.

            // Structs unify only on matching fields, and add missing fields.
            if (is_struct()) {
                _unify_struct(that, work)
                that = that.find()
            } else {                                // Normal structural unification
                for (i in _args!!.indices) { // For all fields in LHS
                    args(i)._unify(that!!.args(i), work)
                    if (that.find().also { that = it }.is_err()) break
                }
            }
            return if (find().is_err() && !that!!.is_err()) that!!.union(find(), work) else find().union(that, work) // Preserve errors
        }

        private fun _unify_struct(that1: T2?, work: Worklist?) {
            var that = that1
            assert(is_struct() && that!!.is_struct())
            var thsi: T2? = this
            // Unification for structs is more complicated; args are aligned via
            // field names and not by position.  Conceptually, fields in one struct
            // and not the other are put in both before unifying the structs.  Open
            // structs copy from the other side; closed structs insert a missing
            // field error.
            for (i in thsi!!._ids!!.indices) { // For all fields in LHS
                val idx = Util.find(that!!._ids, thsi._ids!![i])
                if (idx == -1) // Missing that field?  Copy from left if open, error if closed.
                    that.add_fld(thsi._ids!![i], if (that._open) thsi.args(i) else that.miss_field(thsi._ids!![i]), work) else thsi.args(i)._unify(that.args(idx), work) // Unify matching field
                if (that.find().also { that = it }.is_err()) return  // Recursively, might have already rolled this up
                thsi = thsi.find()
                assert(thsi.is_struct())
            }
            // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
            // just copy the missing fields into it, then unify the structs
            // (shortcut: just skip the copy).  If the LHS is closed, then the extra
            // RHS fields are an error.
            if (!thsi._open) // LHS is closed, so extras in RHS are errors
                for (i in that!!._ids!!.indices)  // For all fields in RHS
                    if (Util.find(thsi._ids, that!!._ids!![i]) == -1) // Missing in LHS
                        that!!.args(i)._unify(miss_field(that!!._ids!![i]), work) // If closed, extra field is an error
            // Shortcut (for asserts): LHS gets same ids as RHS, since its about to be top-level unified
            thsi._ids = that!!._ids
            thsi._open = that!!._open
        }

        // Insert a new field; keep fields sorted
        fun add_fld(id: String?, fld: T2?, work: Worklist?): Boolean {
            assert(is_struct())
            val len = _ids!!.size
            // Find insertion point
            var idx = Arrays.binarySearch(_ids, id)
            assert(idx < 0 // Never found
            )
            idx = -idx - 1 // Insertion point
            // Insert in sorted order
            _ids = Arrays.copyOf(_ids, len + 1)
            _args = Arrays.copyOf(_args, len + 1)
            System.arraycopy(_ids, idx, _ids, idx + 1, len - idx)
            System.arraycopy(_args, idx, _args, idx + 1, len - idx)
            _ids!![idx] = id
            _args!![idx] = fld
            fld!!.push_update(_deps) // If field changes, all deps change
            work!!.addAll(_deps) //
            return true // Always progress
        }

        private fun dbl_uid(t: T2?): Long = dbl_uid(t!!._uid.toLong())

        private fun dbl_uid(uid: Long): Long = _uid.toLong() shl 32 or uid

        private fun fresh_base(that: T2?, work: Worklist?): Boolean {
            assert(base_states() <= 1 && that!!.base_states() <= 1)
            var progress = false
            val flow = meet_flow(that)
            progress = progress or (flow !== that!!._flow)
            val fidxs = meet_fidxs(that)
            progress = progress or (fidxs !== that!!._fidxs)
            val alias = meet_alias(that)
            progress = progress or (alias !== that!!._alias)
            val ids = meet_ids(that)
            progress = progress or (!ids.contentEquals(that!!._ids))
            val open = meet_opens(that)
            progress = progress or (open != that._open)
            val err = meet_err(that)
            progress = progress or !Util.eq(err, that._err)
            if (!progress) return false
            if (work == null) return true
            // Progress
            val that_flow = that._flow
            that._flow = flow
            that._fidxs = fidxs
            that._alias = alias
            that._ids = ids
            that._open = open
            that._err = err
            if (!_can_be_HM_base(that, that_flow)) {
                that._flow = that_flow // Unwind for error message
                val msg = "Cannot unify " + this.p() + " and " + that.p()
                that._flow = null
                that._fidxs = null
                that._alias = null
                that._ids = null // Now kill the base types, since in-error
                return that.union(make_err(msg), work)
            }
            assert(that.base_states() <= 1)
            that.add_deps_work(work)
            if (that.is_leaf()) that._name = _name // That is a base/err now
            return true
        }

        private fun _can_be_HM_base(that: T2?, that_flow: Type<*>?): Boolean {
            if (that!!.base_states() > 1) return false
            if (_flow == null || that_flow == null) return true
            val wthisflow = _flow!!.widen()
            val wthatflow = that_flow.widen()
            return if (wthisflow === wthatflow) true else wthisflow!!.isa(wthatflow)
        }

        private fun union_err(that: T2?, work: Worklist?, msg: String?): Boolean {
            that!!._flow = null
            that._fidxs = null
            that._alias = null
            that._ids = null // Now kill the base types, since in-error
            union(that, work)
            return that.union(make_err(msg), work)
        }

        fun fresh_unify(that: T2?, nongen: VStack?, work: Worklist?): Boolean {
            assert(VARS.isEmpty() && DUPS.isEmpty())
            val old = CNT
            val progress = _fresh_unify(that, nongen, work)
            VARS.clear()
            DUPS.clear()
            if (work == null && old != CNT && DEBUG_LEAKS) throw AA.unimpl("busted, made T2s but just testing")
            return progress
        }

        // Outer recursive version, wraps a VARS check around other work
        private fun _fresh_unify(that1: T2?, nongen: VStack?, work: Worklist?): Boolean {
            var that = that1
            assert(no_uf() && that!!.no_uf())
            val prior = VARS[this]
            if (prior != null) // Been there, done that
                return prior.find()._unify(that, work) // Also 'prior' needs unification with 'that'
            if (cycle_equals(that)) return vput(that, false)
            if (that!!.is_err()) return vput(that, false) // That is an error, ignore 'this' and no progress
            if (is_err()) return vput(that, _unify(that, work))

            // In the non-generative set, so do a hard unify, not a fresh-unify.
            if (nongen_in(nongen)) return vput(that, _unify(that, work)) // Famous 'occurs-check', switch to normal unify

            // LHS is a leaf, base, or error
            if (_args == null) return vput(that, fresh_base(that, work))
            if (that.is_leaf()) // RHS is a tvar; union with a deep copy of LHS
                return work == null || vput(that, that.union(_fresh(nongen), work))

            // Special handling for nilable
            if (is_nilable() && !that.is_nilable()) {
                if (that.is_base()) {
                    val mt = that._flow!!.meet_nil(Type.XNIL)
                    if (mt === that._flow) return false // Nilable already
                    if (work != null) that._flow = mt
                    return true
                }
                if (that.is_struct()) {
                    if (that._alias!!.test(0)) return false // Nilable already
                    throw AA.unimpl()
                }
                throw AA.unimpl()
            }
            // That is nilable and this is not
            if (that.is_nilable() && !is_nilable()) {
                if (is_struct()) {
                    // fresh_unify a not-nil version of this with the not-nil version of that
                    var copy: T2? = this
                    if (copy!!._alias!!.test(0)) { // make a not=nil version of struct
                        copy = copy()
                        copy._alias = copy._alias!!.clear(0)
                        System.arraycopy(_args, 0, copy._args, 0, _args!!.size)
                    }
                    val progress = copy._fresh_unify(that.args(0), nongen, work)
                    return if (_alias!!.test(0)) vput(that, progress) else progress
                }
                throw AA.unimpl()
            }
            if (!Util.eq(_name, that._name) ||
                    !is_struct() && _args!!.size != that._args!!.size) return work == null || vput(that, that._unify(make_err("Cannot unify " + this.p() + " and " + that.p()), work))

            // Structural recursion unification, lazy on LHS
            vput(that, false) // Early set, to stop cycles
            var progress = false
            if (is_struct()) progress = _fresh_unify_struct(that, nongen, work) else {
                for (i in _args!!.indices) {
                    progress = progress or args(i)._fresh_unify(that!!.args(i), nongen, work)
                    if (progress && work == null) return true
                    if (that.find().also { that = it }.is_err()) return true
                }
                if (is_fun()) {
                    val fidxs = meet_fidxs(that)
                    if (fidxs !== that!!._fidxs) progress = true
                    if (progress && work == null) return true
                    that!!._fidxs = fidxs
                }
            }
            return progress
        }

        // Unification with structs must honor field names.
        private fun _fresh_unify_struct(that1: T2?, nongen: VStack?, work: Worklist?): Boolean {
            var that = that1
            assert(is_struct() && that!!.is_struct())
            var progress = false
            // Unification for structs is more complicated; args are aligned via
            // field names and not by position.  Conceptually, fields in one struct
            // and not the other are put in both before unifying the structs.  Open
            // structs copy from the other side; closed structs insert a missing
            // field error.
            for (i in _ids!!.indices) {
                val idx = Util.find(that!!._ids, _ids!![i])
                if (idx == -1) {       // Missing field on RHS
                    if (work == null) return true // Will definitely make progress
                    progress = true
                    // if both are closed, error on RHS
                    that.add_fld(_ids!![i], if (that._open) args(i)._fresh(nongen) else that.miss_field(_ids!![i]), work)
                } else progress = progress or args(i)._fresh_unify(that.args(idx), nongen, work)
                if (that.find().also { that = it }.is_err()) return true
                if (progress && work == null) return true
            }
            // Fields in RHS and not the LHS are also merged; if the LHS is open we'd
            // just copy the missing fields into it, then unify the structs
            // (shortcut: just skip the copy).  If the LHS is closed, then the extra
            // RHS fields are an error.
            if (!_open) for (i in that!!._ids!!.indices)  // For all fields in RHS
                if (Util.find(_ids, that!!._ids!![i]) == -1 &&  // Missing in LHS
                        !that!!.args(i).is_err()) {           // And not yet an error
                    if (work == null) return true // Will definitely make progress
                    progress = progress or that!!.args(i).unify(miss_field(that!!._ids!![i]), work)
                }

            // Unify aliases
            val alias = meet_alias(that)
            if (alias !== that!!._alias) progress = true
            if (progress && work == null) return true
            that!!._alias = alias
            return progress
        }

        private fun vput(that: T2?, progress: Boolean): Boolean {
            VARS[this] = that
            return progress
        }

        // Return a fresh copy of 'this'
        fun fresh(): T2 {
            assert(VARS.isEmpty())
            val rez = _fresh(null)
            VARS.clear()
            return rez
        }

        private fun _fresh(nongen: VStack?): T2 {
            assert(no_uf())
            val rez = VARS[this]
            if (rez != null) return rez // Been there, done that
            // Unlike the original algorithm, to handle cycles here we stop making a
            // copy if it appears at this level in the nongen set.  Otherwise we'd
            // clone it down to the leaves - and keep all the nongen leaves.
            // Stopping here preserves the cyclic structure instead of unrolling it.
            if (nongen_in(nongen)) {
                VARS[this] = this
                return this
            }
            return if (is_leaf()) {
                // If occurs_in lexical scope, keep same variable, else make a new leaf
                val t = make_leaf()
                VARS[this] = t
                t
            } else {                  // Structure is deep-replicated
                val t = copy()
                VARS[this] = t // Stop cyclic structure looping
                if (_args != null) for (i in _args!!.indices) t._args!![i] = args(i)._fresh(nongen)
                t
            }
        }

        fun _occurs_in_type(x: T2?): Boolean {
            assert(no_uf() && x!!.no_uf())
            if (x === this) return true
            if (ODUPS.tset(x!!._uid)) return false // Been there, done that
            if (!x.is_leaf() && x._args != null) for (i in x._args!!.indices) if (_occurs_in_type(x.args(i))) return true
            return false
        }

        fun occurs_in_type(x: T2?): Boolean {
            ODUPS.clear()
            return _occurs_in_type(x)
        }

        fun nongen_in(vs: VStack?): Boolean {
            if (vs == null) return false
            ODUPS.clear()
            for (t2 in vs) if (_occurs_in_type(t2!!.find())) return true
            return false
        }

        fun cycle_equals(t: T2?): Boolean {
            assert(CDUPS.isEmpty())
            val rez = _cycle_equals(t)
            CDUPS.clear()
            return rez
        }

        fun _cycle_equals(t: T2?): Boolean {
            assert(no_uf() && t!!.no_uf())
            if (this === t) return true
            if (_flow !== t!!._flow || // Base-cases have to be completely identical
                    _fidxs !== t!!._fidxs || _alias !== t!!._alias ||
                    !Util.eq(_err, t!!._err)) return false
            if (!Util.eq(_name, t._name)) return false // Wrong type-var names
            if (_args.contentEquals(t._args)) return true // Same arrays (generally both null)
            if (_args!!.size != t._args!!.size) // Mismatched sizes
                return false
            // Cycles stall the equal/unequal decision until we see a difference.
            val tc = CDUPS[this]
            if (tc != null) return tc === t // Cycle check; true if both cycling the same
            CDUPS[this] = t
            if (is_struct()) // Struct equality honors field names without regard to order
                return _cycle_equals_struct(t)
            for (i in _args!!.indices) if (!args(i)._cycle_equals(t.args(i))) return false
            return true
        }

        private fun _cycle_equals_struct(t: T2?): Boolean {
            assert(is_struct() && t!!.is_struct())
            for (i in _args!!.indices) {
                val idx = Util.find(t!!._ids, _ids!![i])
                if (idx == -1 || !args(i)._cycle_equals(t.args(idx))) return false
            }
            return true
        }

        // -----------------
        // Walk a T2 and a matching flow-type, and build a map from T2 to flow-types.
        // Stop if either side loses structure.
        fun walk_types_in(t: Type<*>?): Type<*>? {
            val duid = dbl_uid(t!!._uid.toLong())
            if (Apply.WDUPS.putIfAbsent(duid, "") != null) return t
            assert(no_uf())
            if (is_err()) return fput(t) //
            // Base variables (when widened to an HM type) might force a lift.
            if (is_base()) return fput(_flow!!.widen().join(t))
            // Free variables keep the input flow type.
            if (is_leaf()) return fput(t)
            // Nilable
            if (is_nilable()) {
                fput(t)
                args(0).walk_types_in(t) // TODO: Not sure if i should strip nil or not
                return t
            }
            if (t === Type.SCALAR || t === Type.NSCALR) return fput(t) // Will be scalar for all the breakdown types
            if (is_fun()) {
                if (t !is TypeFunPtr) return t // Typically, some kind of error situation
                // TODO: PAIR1 should report better
                val tfp = t as TypeFunPtr?
                val ret = args(_args!!.size - 1)
                if (tfp!!._fidxs === BitsFun.FULL) return ret.walk_types_in(Type.SCALAR)
                if (tfp!!._fidxs === BitsFun.FULL.dual()) return ret.walk_types_in(Type.XSCALAR)
                for (fidx in (t as TypeFunPtr?)!!._fidxs) {
                    val lambda = Lambda.FUNS[fidx.toLong()]
                    val body = if (lambda!!.find().is_err()) Type.SCALAR // Error, no lift
                    else if (lambda._body == null // Null only for primitives
                    ) lambda.find().args(lambda._targs!!.size).as_flow() // Get primitive return type
                    else lambda._body._flow // Else use body type
                    ret.walk_types_in(body)
                }
                return t
            }
            if (is_struct()) {
                fput(t) // Recursive types need to put themselves first
                if (t !is TypeMemPtr) return t
                val tmp = t as TypeMemPtr?
                if (tmp!!._obj !is TypeStruct) return t
                val ts = tmp._obj as TypeStruct
                for (i in _args!!.indices) {
                    val idx = ts.fld_find(_ids!![i])
                    // Missing fields are walked as SCALAR
                    args(i).walk_types_in(if (idx == -1) Type.SCALAR else ts.at(idx))
                }
                return ts
            }
            throw AA.unimpl()
        }

        private fun fput(type: Type<*>?) = type.also { type1 -> Apply.T2MAP.merge(this as T2, type1!!, Type<*>::meet) }


        fun walk_types_out(t: Type<*>?): Type<*>? {
            assert(no_uf())
            if (t === Type.XSCALAR) return t // No lift possible
            val tmap = Apply.T2MAP[this]
            if (tmap != null) return tmap
            if (is_err()) throw AA.unimpl()
            assert(!is_leaf() && !is_base() // All output leafs found as inputs already
            )
            if (is_fun()) return t // No change, already known as a function (and no TFS in the flow types)
            if (is_struct()) {
                if (t !is TypeMemPtr) throw AA.unimpl()
                val tmp = t as TypeMemPtr?
                if (tmp!!._obj !is TypeStruct) throw AA.unimpl()
                val ts = tmp._obj as TypeStruct
                var progress = false
                for (i in _args!!.indices) {
                    val idx = ts.fld_find(_ids!![i])
                    if (idx == -1) continue
                    val targ = ts.at(idx)
                    val rez = args(i).walk_types_out(targ)
                    progress = progress or (targ !== rez)
                }
                if (progress) {
                    // Make a new result
                    val flds = TypeFlds.get(ts.len())
                    for (i in _args!!.indices) {
                        val idx = ts.fld_find(_ids!![i])
                        if (idx != -1) {
                            val targ = ts.at(idx)
                            val rez = args(i).walk_types_out(targ)
                            flds!![i] = ts.fld(i).make_from(rez)
                        }
                    }
                    return tmp.make_from(ts.make_from(flds))
                }
                return t
            }
            throw AA.unimpl() // Handled all cases
        }

        fun find_fidxs(): BitsFun? {
            FIDX_VISIT.clear()
            FIDXS = BitsFun.EMPTY
            _find_fidxs()
            return FIDXS
        }

        private fun _find_fidxs() {
            if (FIDX_VISIT.tset(_uid)) return
            if (is_struct()) for (arg in _args!!) arg!!._find_fidxs()
            if (is_fun()) {
                FIDXS = FIDXS!!.meet(_fidxs)
                args(_args!!.size - 1)._find_fidxs()
            }
        }

        fun push_update(`as`: Ary<Syntax?>?): T2 {
            if (`as` != null) for (a in `as`) push_update(a)
            return this
        }

        fun push_update(a: Syntax?): T2 {
            assert(UPDATE_VISIT.isEmpty)
            push_update_impl(a)
            UPDATE_VISIT.clear()
            return this
        }

        private fun push_update_impl(a: Syntax?) {
            assert(no_uf())
            if (UPDATE_VISIT.tset(_uid)) return
            if (_deps == null) _deps = Ary(Syntax::class.java)
            if (_deps!!.find(a) == -1) _deps!!.push(a)
            if (_args != null) for (i in _args!!.indices) if (_args!![i] != null) args(i).push_update_impl(a)
        }

        // Recursively add-deps to worklist
        fun add_deps_work(work: Worklist?) {
            assert(UPDATE_VISIT.isEmpty)
            add_deps_work_impl(work)
            UPDATE_VISIT.clear()
        }

        private fun add_deps_work_impl(work: Worklist?) {
            if (is_leaf()) {
                work!!.addAll(_deps)
            } else {
                if (UPDATE_VISIT.tset(_uid)) return
                if (_args != null) for (i in _args!!.indices) args(i).add_deps_work_impl(work)
            }
        }

        // -----------------
        // Glorious Printing
        // Look for dups, in a tree or even a forest (which Syntax.p() does)
        fun get_dups(dups: VBitSet?): VBitSet? = _get_dups(VBitSet(), dups)

        fun _get_dups(visit: VBitSet?, dups: VBitSet?): VBitSet? {
            if (visit!!.tset(_uid)) {
                dups!!.set(debug_find()._uid)
            } else if (_args != null) for (t in _args!!) t?._get_dups(visit, dups)
            return dups
        }

        // Fancy print for Debuggers - includes explicit U-F re-direction.
        // Does NOT roll-up U-F, has no side-effects.
        override fun toString(): String = str(SB(), VBitSet(), get_dups(VBitSet())).toString()

        fun str(sb: SB?, visit: VBitSet?, dups: VBitSet?): SB? {
            if (is_err()) return sb!!.p(_err)
            if (is_base()) return sb!!.p(_flow)
            val dup = dups!![_uid]
            if (is_leaf()) {
                sb!!.p(_name)
                return if (no_uf()) sb else _args!![0]!!.str(sb.p(">>"), visit, dups)
            }
            if (dup) sb!!.p("\$V").p(_uid)
            if (visit!!.tset(_uid) && dup) return sb
            if (dup) sb!!.p(':')

            // Special printing for functions
            if (is_fun()) {
                sb!!.p("{")
                if (_fidxs == null) sb.p('_') else _fidxs!!.str(sb)
                sb.p(' ')
                for (i in 0 until _args!!.size - 1) str(sb, visit, _args!![i], dups)!!.p(" ")
                return str(sb.p("-> "), visit, _args!![_args!!.size - 1], dups)!!.p(" }")
            }

            // Special printing for structures
            if (is_struct()) {
                sb!!.p("@{")
                if (_alias == null) sb.p('_') else _alias!!.str(sb)
                sb.p(' ')
                if (_ids == null) sb.p("_ ") else for (i in _ids!!.indices) str(sb.p(' ').p(_ids!![i]).p(" = "), visit, _args!![i], dups)!!.p(',')
                return sb.unchar().p("}")
            }

            // Generic structural T2
            sb!!.p("(").p(_name).p(" ")
            for (t in _args!!) str(sb, visit, t, dups)!!.p(" ")
            return sb.unchar().p(")")
        }

        // Same as toString but calls find().  Can thus side-effect & roll-up U-Fs, so not a toString
        fun p(): String = p(get_dups(VBitSet()))

        fun p(dups: VBitSet?): String {
            VCNT = 0
            VNAMES.clear()
            return find()._p(SB(), VBitSet(), dups).toString()
        }

        private fun _p(sb: SB?, visit: VBitSet?, dups: VBitSet?): SB? {
            assert(no_uf())
            if (is_base()) return sb!!.p(_flow) // One-shot bases just do type
            if (is_leaf() || dups!![_uid]) { // Leafs or Duplicates?  Take some effort to pretty-print cycles
                var ii = VNAMES[this]
                if (ii == null) VNAMES[this] = VCNT++.also { ii = it } // Type-var name
                // 2nd and later visits use the short form
                val later = visit!!.tset(_uid)
                // Removed as being more confusing to more academic readers
                //if( later ) sb.p('$');
                val c = ('A'.code + ii!!).toChar()
                if (c < 'V') sb!!.p(c) else sb!!.p("V$ii")
                if (later) return sb
                if (is_leaf()) return sb
                sb.p(':') // Dups now print their structure
            }
            if (is_err()) return sb!!.p(_err)

            // Special printing for functions: { arg -> body }
            if (is_fun()) {
                sb!!.p("{ ")
                for (i in 0 until _args!!.size - 1) args(i)._p(sb, visit, dups)!!.p(" ")
                return args(_args!!.size - 1)._p(sb.p("-> "), visit, dups)!!.p(" }")
            }

            // Special printing for structures: @{ fld0 = body, fld1 = body, ... }
            if (is_struct()) {
                if (is_tuple()) {
                    if (_ids!!.isEmpty()) return sb!!.p("()")
                    sb!!.p('(')
                    for (i in _ids!!.indices) {
                        val idx = Util.find(_ids, String(charArrayOf(('0'.code + i).toChar())).intern())
                        args(idx)._p(sb.p(' '), visit, dups)!!.p(',')
                    }
                    sb.unchar().p(')')
                } else {
                    sb!!.p("@{")
                    val map = TreeMap<String?, Int?>()
                    for (i in _ids!!.indices) map[_ids!![i]] = i
                    for (i in map.values) args(i!!)._p(sb.p(' ').p(_ids!![i]).p(" = "), visit, dups)!!.p(',')
                    sb.unchar().p("}")
                }
                //return _alias.str(sb);
                if (_alias!!.test(0)) sb.p('?')
                return sb
            }
            if (is_nilable()) return args(0)._p(sb, visit, dups)!!.p('?')

            // Generic structural T2: (fun arg0 arg1...)
            sb!!.p("(").p(_name).p(" ")
            for (i in _args!!.indices) args(i)._p(sb, visit, dups)!!.p(" ")
            return sb.unchar().p(")")
        }

        fun is_tuple(): Boolean {
            if (_ids == null) return false
            for (id in _ids!!) if (!isDigit(id!![0].code.toByte())) return false
            return true
        }

        // Debugging tool
        fun find(uid: Int): T2? = _find(uid, VBitSet())

        private fun _find(uid: Int, visit: VBitSet?): T2? = when {
            visit!!.tset(_uid) -> null
            _uid == uid -> this
            _args == null -> null
            else -> {
                var r: T2? = null
                for (arg in _args!!) {
                    r = arg!!._find(uid, visit)
                    if (r != null) break
                }
                r
            }
        }

        companion object {
            var CNT = 0

            // Constructor factories.
            fun make_leaf(): T2 = T2("V" + CNT)

            fun make_nil(leaf: T2?): T2 = T2("?", leaf!!)

            fun make_base(flow: Type<*>?): T2 {
                val base = T2("Base")
                base._flow = flow
                return base
            }

            fun make_fun(fidxs: BitsFun?, vararg args: T2?): T2 {
                val tfun = T2("->", *args as Array<out T2>)
                tfun._fidxs = fidxs
                return tfun
            }

            @JvmOverloads
            fun make_struct(aliases: BitsAlias?, ids: Array<String?>, flds: Array<T2>, open: Boolean = false): T2 {
                val tstr = T2("@{}", *flds)
                tstr._alias = aliases
                tstr._ids = ids
                tstr._open = open
                return tstr
            }

            fun make_err(s: String?): T2 {
                val terr = T2("Err")
                terr._err = s!!.intern()
                return terr
            }

            // Recursively build a conservative flow type from an HM type.  The HM
            // is_struct wants to be a TypeMemPtr, but the recursive builder is built
            // around TypeStruct.
            // No function arguments, just function returns.
            val ADUPS: NonBlockingHashMapLong<TypeStruct?> = NonBlockingHashMapLong()

            // -----------------
            // Structural unification.
            // Returns false if no-change, true for change.
            // If work is null, does not actually change anything, just reports progress.
            // If work and change, unifies 'this' into 'that' (changing both), and
            // updates the worklist.
            private val DUPS: HashMap<Long?, T2?> = HashMap()

            // -----------------
            // Make a (lazy) fresh copy of 'this' and unify it with 'that'.  This is
            // the same as calling 'fresh' then 'unify', without the clone of 'this'.
            // Returns progress.
            // If work is null, we are testing only and make no changes.
            private val VARS: HashMap<T2?, T2?> = HashMap()

            // -----------------
            private val ODUPS: VBitSet = VBitSet()

            // -----------------
            // Test for structural equivalence, including cycles
            private val CDUPS: HashMap<T2?, T2?> = HashMap()

            // -----------------
            private val FIDX_VISIT: VBitSet = VBitSet()
            private var FIDXS: BitsFun? = null

            // -----------------
            // This is a T2 function that is the target of 'fresh', i.e., this function
            // might be fresh-unified with some other function.  Push the application
            // down the function parts; if any changes the fresh-application may make
            // progress.
            val UPDATE_VISIT: VBitSet = VBitSet()
            private fun str(sb: SB?, visit: VBitSet?, t: T2?, dups: VBitSet?): SB? =
                    if (t == null) sb!!.p("_") else t.str(sb, visit, dups)

            private var VCNT = 0
            private val VNAMES: HashMap<T2?, Int?> = HashMap()
            fun reset() {
                CNT = 0
                DUPS.clear()
                VARS.clear()
                ODUPS.clear()
                CDUPS.clear()
                UPDATE_VISIT.clear()
            }
        }

        init {
            _uid = CNT++
            _name = name
        }
    }
}