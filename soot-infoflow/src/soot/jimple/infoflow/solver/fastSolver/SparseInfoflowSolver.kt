package soot.jimple.infoflow.solver.fastSolver

import com.google.common.cache.CacheBuilder
import com.google.common.cache.CacheLoader
import soot.Scene
import soot.SootMethod
import soot.Unit
import soot.jimple.IfStmt
import soot.jimple.infoflow.collect.MyConcurrentHashMap
import soot.jimple.infoflow.data.Abstraction
import soot.jimple.infoflow.problems.AbstractInfoflowProblem
import soot.jimple.infoflow.solver.cfg.BackwardsInfoflowCFG
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG
import soot.jimple.infoflow.solver.executors.InterruptableExecutor
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG
import soot.toolkits.graph.UnitGraph
import soot.util.queue.ChunkedQueue
import java.util.*
import java.util.function.Consumer
import kotlin.math.max

//typealias N = Unit
//typealias M = SootMethod
//typealias D = Abstraction


class RefCntUnit<N>(val u: N, var cnt: Int) {
    private val ref: Queue<RefCntUnit<N>> = LinkedList()
    fun add(prev: RefCntUnit<N>) {
        ref.add(prev)
        prev.cnt++
    }

    fun dec() {
        if (--cnt == 0) {
            ref.forEach { it.dec() }
        }
        require(cnt >= 0)
    }

    override fun hashCode(): Int {
        return u.hashCode()
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is RefCntUnit<*>) return false
        return other.u == u
    }

    override fun toString(): String {
        return "$u $cnt"
    }
}

// 这个函数比较的耗时，可以考虑增加cache来进行加速，TODO
fun <M, N> BiDiInterproceduralCFG<N, M>.getGoThrough(
    from: N, to: N,
    skipNodes: Set<N> = emptySet()
): MutableSet<N> {
    if (from == to) {
        return mutableSetOf(from)
    }
    val workList: Queue<RefCntUnit<N>> = LinkedList()
    val startNode = RefCntUnit(from, 1)
    workList.add(startNode)
    val set = HashMap<RefCntUnit<N>, RefCntUnit<N>>()
    set[startNode] = startNode
    while (!workList.isEmpty()) {
        val cur = workList.poll()
        val curNode = cur.u
        if (curNode !in skipNodes) {
            for (succ in getSuccsOf(curNode)) {
                val key = RefCntUnit(succ, 1)
                val next = set.getOrPut(key) { key }
                if (next === key && succ != to) {
                    workList.offer(next)
                }
                next.add(cur)
            }
        }
        cur.dec()
    }
    return set.values.filter { it.cnt != 0 }.map { it.u }.toMutableSet()
}


@Suppress("unused")
fun getReachSet(icfg: BiDiInterproceduralCFG<Unit, SootMethod>, target: Unit): Set<Unit> {
    val reaches = ChunkedQueue<Unit>()
    val reachSet = HashSet<Unit>()
    reachSet.add(target)
    val reader = reaches.reader()
    reachSet.forEach(Consumer { o: Unit -> reaches.add(o) })
    while (reader.hasNext()) {
        for (s in icfg.getSuccsOf(reader.next())) {
            if (reachSet.add(s)) {
                reaches.add(s)
            }
        }
    }
    return reachSet
}

val AbstractInfoflowProblem.activationUnitsToCallSites
    get() : MyConcurrentHashMap<Unit, Set<Unit>> {
        return AbstractInfoflowProblem::class.java.getDeclaredField("activationUnitsToCallSites").let { field ->
            field.isAccessible = true
            @Suppress("UNCHECKED_CAST") return@let field[this] as MyConcurrentHashMap<Unit, Set<Unit>>
        }
    }


class CacheFlowGuide(val trackControlFlowDependencies: Boolean) {
    private val initialCapacity: Int
        get() {
            return max(Scene.v().classes.size * 10, 500)
        }
    private val flowCacheBuilder =
        CacheBuilder.newBuilder().concurrencyLevel(Runtime.getRuntime().availableProcessors())
            .initialCapacity(initialCapacity).maximumSize((initialCapacity * 2).toLong()).softValues()

    private val cache = flowCacheBuilder.build(object : CacheLoader<UnitGraph, ILocalDFA>() {
        @Throws(Exception::class)
        override fun load(ug: UnitGraph): ILocalDFA {
            return LocalVFA(ug, trackControlFlowDependencies)
        }
    })

    fun getSuccess(isForward: Boolean, ap: AP, unit: Unit, unitGraph: UnitGraph): List<Unit> {
        val lu = cache.getUnchecked(unitGraph)
        return if (isForward) {
            lu.getUsesOfAt(ap, unit)
        } else {
            lu.getDefUsesOfAt(ap, unit)
        }
    }
}

open class SparseInfoFlowSolver(problem: AbstractInfoflowProblem, executor: InterruptableExecutor?) :
    soot.jimple.infoflow.solver.fastSolver.InfoflowSolver(problem, executor) {
    private val sparseCache by lazy {
        val trackControlFlowDependencies =
            tabulationProblem.manager.config.implicitFlowMode.trackControlFlowDependencies()
        CacheFlowGuide(trackControlFlowDependencies)
    }

    private val isForward: Boolean get() = icfg !is BackwardsInfoflowCFG
    private val isBackward: Boolean get() = icfg is BackwardsInfoflowCFG


    override fun propagate(
        sourceVal: Abstraction,
        target: Unit,
        targetVal: Abstraction,
        relatedCallSite: Unit?,
        isUnbalancedReturn: Boolean,
        scheduleTarget: ScheduleTarget
    ) {
//        println("${if (isForward) "F" else "B"} $targetVal -> $target")
//        super.propagate(sourceVal, target, targetVal, relatedCallSite, isUnbalancedReturn, scheduleTarget)
//        return
        if (targetVal.accessPath.plainValue == null || // static value or Implicit flow
            targetVal.accessPath == zeroValue.accessPath // zero value
        ) {
            super.propagate(sourceVal, target, targetVal, relatedCallSite, isUnbalancedReturn, scheduleTarget)
            return
        }

        val method = icfg.getMethodOf(target)

        val unitGraph = icfg.getOrCreateUnitGraph(method) as UnitGraph

        val ap = AP[targetVal]
        val uses = if (icfg is BackwardsInfoflowCFG) {
            sparseCache.getSuccess(false, ap, target, unitGraph)
        } else {
            sparseCache.getSuccess(true, ap, target, unitGraph)
        }.toSet()
        val propagates = if (!targetVal.isAbstractionActive) {
            if (isForward) {
                uses.map { use ->
                    var toVal = targetVal
                    val throughUnits = icfg.getGoThrough(target, use)
                    throughUnits.remove(use)
                    if (throughUnits.contains(targetVal.activationUnit)) {
                        toVal = targetVal.activeCopy
                    }
                    val callSites = tabulationProblem.activationUnitsToCallSites[targetVal.activationUnit]
                    if (callSites?.any { throughUnits.contains(it) } == true) {
                        // may be false negative if this condition not right
                        toVal = targetVal.activeCopy
                    }
                    use to toVal
                }
            } else {
                // backwards solver need active abs ? TODO?
                uses.map { it to targetVal }
            }
        } else {
            uses.map { it to targetVal }
        }


        for ((useUnit, toVal) in propagates) {
            val turnUnit = toVal.turnUnit
            if (turnUnit != null) {
                val throughUnits = icfg.getGoThrough(target, useUnit, setOf(turnUnit))
                if (useUnit !in throughUnits && !(icfg.isCallStmt(useUnit) && sourceVal == targetVal)) {
                    // may be false positive if this condition not right
                    continue
                }
            }

            if (isBackward) {
                val dominator: IInfoflowCFG.UnitContainer = tabulationProblem.manager.icfg.getDominatorOf(useUnit)
                if (dominator.unit != null && dominator.unit is IfStmt) {
                    val newAbs = toVal.deriveNewAbstractionWithDominator(dominator.unit)
                    super.propagate(sourceVal, useUnit, newAbs, relatedCallSite, isUnbalancedReturn, scheduleTarget)
                }
            }
            super.propagate(sourceVal, useUnit, toVal, relatedCallSite, isUnbalancedReturn, scheduleTarget)
        }
    }

    override fun toString(): String {
        return if (isForward) "forward" else "backward"
    }
}
