package soot.jimple.infoflow.river;

import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.sourcesSinks.manager.*;

/**
 * Wraps a SourceSinkManager and only redirects calls to methods of IConditionalFlowManager
 * to the wrapped SourceSinkManager.
 * Provide this to the Additional Flow such that it knows the conditions but doesn't accept sources.
 *
 * @author Tim Lange
 */
public class ConditionalFlowSourceSinkManagerWrapper implements IReversibleSourceSinkManager, IConditionalFlowManager {
    private final IConditionalFlowManager inner;

    public ConditionalFlowSourceSinkManagerWrapper(IConditionalFlowManager inner) {
        this.inner = inner;
    }

    @Override
    public boolean isSecondarySink(Stmt stmt) {
        return inner.isSecondarySink(stmt);
    }

    @Override
    public boolean isConditionalSink(Stmt stmt) {
        return inner.isConditionalSink(stmt);
    }

    @Override
    public void initialize() {
        // NO-OP
    }

    @Override
    public SourceInfo getSourceInfo(Stmt sCallSite, InfoflowManager manager) {
        return null;
    }

    @Override
    public SinkInfo getSinkInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
        return null;
    }

    @Override
    public SinkInfo getInverseSourceInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
        return null;
    }

    @Override
    public SourceInfo getInverseSinkInfo(Stmt sCallSite, InfoflowManager manager) {
        return null;
    }
}
