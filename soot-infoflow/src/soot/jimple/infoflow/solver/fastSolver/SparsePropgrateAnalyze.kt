package soot.jimple.infoflow.solver.fastSolver

import kotlinx.collections.immutable.*
import soot.*
import soot.Unit
import soot.jimple.*
import soot.jimple.infoflow.data.Abstraction
import soot.jimple.infoflow.util.BaseSelector
import soot.jimple.internal.JimpleLocal
import soot.options.Options
import soot.toolkits.graph.DirectedGraph
import soot.toolkits.graph.ExceptionalGraph
import soot.toolkits.scalar.BackwardFlowAnalysis
import soot.toolkits.scalar.FlowAnalysis
import soot.toolkits.scalar.ForwardFlowAnalysis
import java.util.*

internal enum class ValueLocation {
    ParamAndThis, Left, Right, Arg
}

internal fun ValueLocation.isLeft(): Boolean = this == ValueLocation.Left
internal fun ValueLocation.isRight(): Boolean = this != ValueLocation.Left


data class AP(val value: Value, val field: SootField? = null) {
    companion object {

        private val staticValue: Value = JimpleLocal("staticValueFake", NullType.v())

        operator fun get(value: Value): AP? {
            var base: Value? = null
            var field: SootField? = null
            if (value is StaticFieldRef) {
                base = staticValue
                field = value.field
            } else if (value is Local) {
                base = value
            } else if (value is FieldRef) {
                if (value is InstanceFieldRef) {
                    base = value.base
                    field = value.field
                }
            } else if (value is ArrayRef) {
                base = value.base as Local
            } else if (value is LengthExpr) {
                base = value.op
            } else if (value is NewArrayExpr) {
                base = value.size
            }
            return if (base != null) {
                AP(base, field)
            } else {
                null
            }
        }

        operator fun get(value: Abstraction): AP {
            return AP(value.accessPath.plainValue, value.accessPath.firstFragment?.field)
        }

    }

    fun base(): AP {
        return if (this.field == null) this else AP(this.value)
    }

    override fun toString(): String {
        return if (field != null) "$value.${field.name}" else "$value"
    }
}

//class StmtInfo(private var stmt: Stmt, private val value: Value, private val loc: ValueLocation) {
//
//    override fun toString(): String {
//        return "$value  $loc $stmt"
//    }
//}

internal class VFNode(val ap: Value, val stmt: Unit) {
    override fun hashCode(): Int {
        return Objects.hash(ap, stmt)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is VFNode) return false
        return ap == other.ap && stmt == other.stmt
    }

    override fun toString(): String {
        return "$ap $stmt"
    }
}

internal interface ILocalDFA {
    fun getUsesOfAt(ap: AP, stmt: Unit): List<Unit>
    fun getDefUsesOfAt(ap: AP, stmt: Unit): List<Unit>
}


internal class FlowFact {
    var data: PersistentMap<Value, PersistentSet<VFNode>> = persistentHashMapOf()
//    var exit: PersistentSet<Pair<Value, Stmt>> = persistentHashSetOf()

    override fun toString(): String {
        return "\n" + data.values.flatten()
            .joinToString(separator = "\n")
    }

    override fun hashCode(): Int {
        return Objects.hash(data)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is FlowFact) return false
        return other.data == data
    }
}

internal object FlowAnalysisOp {
    fun mergeInto(succNode: Unit, inout: FlowFact, in1: FlowFact) {
        val fx: (Value) -> kotlin.Unit = { k ->
            val u = inout.data[k] ?: persistentHashSetOf()
            val set = u + (in1.data[k] ?: persistentHashSetOf())
            inout.data = inout.data.put(k, set)
        }

        inout.data.keys.forEach {
            fx(it)
        }
        in1.data.keys.forEach {
            fx(it)
        }
    }

    fun getFlow(graph: DirectedGraph<Unit>, from: Unit, to: Unit): FlowAnalysis.Flow {
        // QND
        if (to is IdentityUnit && graph is ExceptionalGraph<*>) {
            val g = graph as ExceptionalGraph<Unit>
            if (g.getExceptionalPredsOf(to).isNotEmpty()) {
                // look if there is a real exception edge
                for (exd in g.getExceptionDests(from)) {
                    val trap = exd.trap
                    if (trap != null && trap.handlerUnit === to) {
                        return FlowAnalysis.Flow.IN
                    }
                }
            }
        }
        return FlowAnalysis.Flow.OUT
    }
}

private class FlowAssignment(
    graph: DirectedGraph<Unit>,
    val paramAndThis: MutableSet<Value>,
    val unit2locals: Map<Stmt, MutableSet<Pair<AP, ValueLocation>>>,
) : BackwardFlowAnalysis<Unit, FlowFact>(graph) {

    override fun omissible(u: Unit): Boolean {
        return false
    }

    override fun flowThrough(infact: FlowFact, unit: Unit, out: FlowFact) {
        copy(infact, out)
        if (unit !is Stmt) return
        val locals = unit2locals[unit]

        if (locals != null) {
            var fact = out.data
            locals.forEach { (ap, loc) ->
                if (loc.isLeft()) {
                    if (ap.field == null) {
                        fact -= ap.value
                    } else {
                        fact += ap.value to persistentHashSetOf(VFNode(ap.value, unit))
                    }
                } else {
                    fact += ap.value to persistentHashSetOf(VFNode(ap.value, unit))
                }
            }
            out.data = fact
        }
        if (unit is ReturnVoidStmt || unit is ReturnStmt) {
            out.data += paramAndThis.associateWith { persistentHashSetOf(VFNode(it, unit)) }.toPersistentMap()
        }
        return
    }

    override fun copy(source: FlowFact, dest: FlowFact) {
        if (dest !== source) {
            dest.data = source.data
        }
    }

    override fun newInitialFlow(): FlowFact {
        return FlowFact()
    }

    override fun getFlow(from: Unit, to: Unit): Flow {
        return FlowAnalysisOp.getFlow(graph, from, to)
    }

    override fun mergeInto(succNode: Unit, inout: FlowFact, in1: FlowFact) {
        FlowAnalysisOp.mergeInto(succNode, inout, in1)
    }


    override fun merge(in1: FlowFact, in2: FlowFact, out: FlowFact) {
        throw UnsupportedOperationException("FlowAssignment.merge should never be called")
    }

    init {
        doAnalysis()
    }

    fun getBefore(): Map<Unit, FlowFact> {
        return unitToBeforeFlow
    }
} // end inner class FlowAssignment

private class BackAssignment constructor(
    graph: DirectedGraph<Unit>,
    val paramAndThis: MutableSet<Value>,
    val unit2locals: Map<Stmt, MutableSet<Pair<AP, ValueLocation>>>,
) : ForwardFlowAnalysis<Unit, FlowFact>(graph) {
    override fun newInitialFlow(): FlowFact {
        return FlowFact()
    }

    override fun omissible(u: Unit): Boolean {
        return false
    }

    override fun copy(source: FlowFact, dest: FlowFact) {
        if (dest !== source) {
            dest.data = source.data
        }
    }

    override fun getFlow(from: Unit, to: Unit): Flow {
        return FlowAnalysisOp.getFlow(graph, from, to)
    }

    override fun mergeInto(succNode: Unit, inout: FlowFact, in1: FlowFact) {
        FlowAnalysisOp.mergeInto(succNode, inout, in1)
    }


    override fun merge(in1: FlowFact, in2: FlowFact, out: FlowFact) {
        throw UnsupportedOperationException("BackAssignment.merge should never be called")
    }


    override fun flowThrough(infact: FlowFact, unit: Unit, out: FlowFact) {
        copy(infact, out)
        if (unit !is Stmt) return
        val locals = unit2locals[unit]


        if (locals != null) {
            var fact = out.data
            locals.forEach { (ap, loc) ->
                fact += ap.value to persistentHashSetOf(VFNode(ap.value, unit))
            }
            out.data = fact
        }
        if (unit in graph.heads) {
            out.data += paramAndThis.associateWith { persistentHashSetOf(VFNode(it, unit)) }.toPersistentMap()
        }
        return
    }

    init {
        doAnalysis()
    }

    fun getAfter(): Map<Unit, FlowFact> {
        return unitToAfterFlow
    }
}


class LocalVFA(graph: DirectedGraph<Unit>, val trackControlFlowDependencies: Boolean) :
    ILocalDFA {
    companion object {
        val returnVoidFake: Value = JimpleLocal("returnVoidFake", NullType.v())
        val entryFake: Value = JimpleLocal("entryFake", NullType.v())
    }

    private fun <R> Expr.traverse(){

    }

    private fun <R> collectStmtInfo(stmt: Stmt, addValueToInfoMap: (v: Value, loc: ValueLocation) -> R) {
        when (stmt) {
            is AssignStmt -> {
                val left = stmt.leftOp
                val right = stmt.rightOp
                val rightValues = BaseSelector.selectBaseList(right, true)
                when (left) {
                    is ArrayRef -> {
                        addValueToInfoMap(left.base, ValueLocation.Right)
                    }

                    else -> {
                        addValueToInfoMap(left, ValueLocation.Left)
                    }
                }

                rightValues.forEach { addValueToInfoMap(it, ValueLocation.Right) }
            }

            is IdentityStmt -> {
                when (stmt.rightOp) {
                    is ParameterRef -> {
                        // 必须是 ParamAndThis 而不是 LEFT 原因是propagateCall edge target 为一个 entry stmt
                        addValueToInfoMap(stmt.leftOp, ValueLocation.ParamAndThis)
                    }

                    is ThisRef -> {
                        addValueToInfoMap(stmt.leftOp, ValueLocation.ParamAndThis)
                    }
                }
            }

            is InvokeStmt -> {
            }

            is IfStmt -> {
                /* ImplicitFlow like
                *  $stack2 = staticinvoke <soot.jimple.infoflow.test.android.TelephonyManager: int getIMEI()>();
                *  if $stack2 != 42 goto label1;
                *  specialinvoke this.<soot.jimple.infoflow.test.ImplicitFlowTestCode: void runSimpleRecursion(int)>(42);
                *
                * */
                if (trackControlFlowDependencies){
                    val cond = stmt.condition as BinopExpr
                    addValueToInfoMap(cond.op1, ValueLocation.Right)
                    addValueToInfoMap(cond.op2, ValueLocation.Right)
                }
                return
            }

            is ReturnStmt -> {
                addValueToInfoMap(stmt.op, ValueLocation.Right)
                return
            }

            is ReturnVoidStmt -> {
                addValueToInfoMap(returnVoidFake, ValueLocation.Right)
                return
            }
        }

        val ie = if (stmt.containsInvokeExpr()) stmt.invokeExpr else null
        if (ie != null) {
            if (ie is InstanceInvokeExpr) {
                // add invoke stmt's base, such as  a.foo()
                addValueToInfoMap(ie.base, ValueLocation.Arg)
            }
            for (i in 0 until ie.argCount) {
                addValueToInfoMap(ie.getArg(i), ValueLocation.Arg)
            }
        }
    }

    private fun init(graph: DirectedGraph<Unit>): Pair<Map<Unit, FlowFact>, Map<Unit, FlowFact>> {
        val paramAndThis = mutableSetOf<Value>()
        val unit2locals = graph.filterIsInstance<Stmt>().associateWith { stmt ->
            val apAndLoc = mutableSetOf<Pair<AP, ValueLocation>>()
            collectStmtInfo(stmt) { value: Value, valueLocation: ValueLocation ->
                val ap = AP[value]
                if (ap != null) {
                    if (valueLocation == ValueLocation.ParamAndThis) {
                        paramAndThis.add(ap.value)
                    }
                    apAndLoc.add(ap to valueLocation)
                }
            }
            apAndLoc
        }
        return FlowAssignment(graph, paramAndThis, unit2locals).getBefore() to
                BackAssignment(graph, paramAndThis, unit2locals).getAfter()
    }

    override fun getDefUsesOfAt(ap: AP, stmt: Unit): List<Unit> {
        val fact = defuses[stmt] ?: return emptyList()
        val use = fact.data[ap.value] ?: persistentHashSetOf()
        return use.map { it.stmt }
    }

    override fun getUsesOfAt(ap: AP, stmt: Unit): List<Unit> {
        val fact = uses[stmt] ?: return emptyList()
        val use = fact.data[ap.value] ?: persistentHashSetOf()
        return use.map { it.stmt }
    }


    private val uses: Map<Unit, FlowFact>
    private val defuses: Map<Unit, FlowFact>

    init {
        val time = Options.v().time()
        if (time) {
            Timers.v().defsTimer.start()
        }

        val (uses, defuses) = init(graph)
        this.uses = uses
        this.defuses = defuses

        if (time) {
            Timers.v().defsTimer.end()
        }
    }
}
