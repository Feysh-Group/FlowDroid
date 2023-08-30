/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow.test.junit;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import soot.SootMethod;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.LeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.IInfoflow;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.data.SootMethodAndClass;
import soot.jimple.infoflow.entryPointCreators.DefaultEntryPointCreator;
import soot.jimple.infoflow.sourcesSinks.definitions.MethodSourceSinkDefinition;
import soot.jimple.infoflow.sourcesSinks.manager.IReversibleSourceSinkManager;
import soot.jimple.infoflow.sourcesSinks.manager.ISourceSinkManager;
import soot.jimple.infoflow.sourcesSinks.manager.SinkInfo;
import soot.jimple.infoflow.sourcesSinks.manager.SourceInfo;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;

/**
 * Test cases for FlowDroid's interaction with non-standard source sink managers
 * 
 * @author Steven Arzt
 */
public abstract class SourceSinkTests extends JUnitTests {

	private static final String sourceGetSecret = "<soot.jimple.infoflow.test.SourceSinkTestCode: soot.jimple.infoflow.test.SourceSinkTestCode$A getSecret()>";
	private static final String sourceGetSecret2 = "<soot.jimple.infoflow.test.SourceSinkTestCode: soot.jimple.infoflow.test.SourceSinkTestCode$B getSecret2()>";

	private static final String sinkAP = "<soot.jimple.infoflow.test.SourceSinkTestCode: void doLeakSecret2(soot.jimple.infoflow.test.SourceSinkTestCode$A)>";
	private static final String sinkAP2 = "<soot.jimple.infoflow.test.SourceSinkTestCode: void doLeakSecret(java.lang.String)>";

	private abstract class BaseSourceSinkManager implements IReversibleSourceSinkManager {

		@Override
		public void initialize() {
			//
		}

		@Override
		public SinkInfo getSinkInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			if (!sCallSite.containsInvokeExpr())
				return null;

			SootMethod target = sCallSite.getInvokeExpr().getMethod();
			SinkInfo targetInfo = new SinkInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)));

			if ((target.getSignature().equals(sinkAP) || target.getSignature().equals(sinkAP2)
					|| target.getSignature().equals(sink)) && sCallSite.getInvokeExpr().getArgCount() > 0) {
				if (ap == null)
					return targetInfo;
				else if (ap.getPlainValue() == sCallSite.getInvokeExpr().getArg(0))
					if (ap.isLocal() || ap.getTaintSubFields())
						return targetInfo;
			}
			return null;
		}

		@Override
		public SourceInfo getInverseSinkInfo(Stmt sCallSite, InfoflowManager manager) {
			if (!sCallSite.containsInvokeExpr())
				return null;

			SootMethod target = sCallSite.getInvokeExpr().getMethod();
			if ((target.getSignature().equals(sinkAP) || target.getSignature().equals(sinkAP2)
					|| target.getSignature().equals(sink)) && sCallSite.getInvokeExpr().getArgCount() > 0) {
				AccessPath ap = manager.getAccessPathFactory().createAccessPath(sCallSite.getInvokeExpr().getArg(0),
						true);
				return new SourceInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)), ap);
			}
			return null;
		}
	}

	private final ISourceSinkManager getSecretSSM = new BaseSourceSinkManager() {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InfoflowManager manager) {
			if (sCallSite.containsInvokeExpr() && sCallSite instanceof DefinitionStmt
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")) {
				AccessPath ap = manager.getAccessPathFactory()
						.createAccessPath(((DefinitionStmt) sCallSite).getLeftOp(), true);
				return new SourceInfo(ap);
			}
			return null;
		}

		@Override
		public SinkInfo getInverseSourceInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			if (sCallSite.containsInvokeExpr() && sCallSite instanceof DefinitionStmt
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")
					&& (ap == null || ((DefinitionStmt) sCallSite).getLeftOp() == ap.getPlainValue())) {
				SootMethod target = sCallSite.getInvokeExpr().getMethod();
				return new SinkInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)));
			}
			return null;
		}
	};

	private final ISourceSinkManager getSecretOrSecret2SSM = new BaseSourceSinkManager() {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InfoflowManager manager) {
			if (sCallSite.containsInvokeExpr() && sCallSite instanceof DefinitionStmt
					&& (sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")
							|| (sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret2")))) {
				AccessPath ap = manager.getAccessPathFactory()
						.createAccessPath(((DefinitionStmt) sCallSite).getLeftOp(), true);
				return new SourceInfo(ap);
			}
			return null;
		}

		@Override
		public SinkInfo getInverseSourceInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			if (sCallSite.containsInvokeExpr() && sCallSite instanceof DefinitionStmt
					&& (sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")
							|| (sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret2")))
					&& (ap == null || ((DefinitionStmt) sCallSite).getLeftOp() == ap.getPlainValue())) {
				SootMethod target = sCallSite.getInvokeExpr().getMethod();
				return new SinkInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)));
			}
			return null;
		}
	};

	private final ISourceSinkManager noTaintSubFieldsSSM = new BaseSourceSinkManager() {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InfoflowManager manager) {
			if (sCallSite.containsInvokeExpr() && sCallSite instanceof DefinitionStmt
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")) {
				AccessPath ap = manager.getAccessPathFactory()
						.createAccessPath(((DefinitionStmt) sCallSite).getLeftOp(), false);
				return new SourceInfo(ap);
			}
			return null;
		}

		@Override
		public SinkInfo getInverseSourceInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			if (ap == null)
				return null;
			if (sCallSite.containsInvokeExpr() && sCallSite instanceof DefinitionStmt
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")
					&& ((DefinitionStmt) sCallSite).getLeftOp() == ap.getPlainValue()) {
				SootMethod target = sCallSite.getInvokeExpr().getMethod();
				return new SinkInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)));
			}
			return null;
		}

		@Override
		public SourceInfo getInverseSinkInfo(Stmt sCallSite, InfoflowManager manager) {
			if (!sCallSite.containsInvokeExpr())
				return null;

			SootMethod target = sCallSite.getInvokeExpr().getMethod();
			if ((target.getSignature().equals(sinkAP) || target.getSignature().equals(sinkAP2)
					|| target.getSignature().equals(sink)) && sCallSite.getInvokeExpr().getArgCount() > 0) {
				AccessPath ap = manager.getAccessPathFactory().createAccessPath(sCallSite.getInvokeExpr().getArg(0),
						false);
				return new SourceInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)), ap);
			}
			return null;
		}
	};

	private final class ifAsSinkSSM implements IReversibleSourceSinkManager {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InfoflowManager manager) {
			if (sCallSite instanceof DefinitionStmt && sCallSite.containsInvokeExpr()
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("currentTimeMillis")) {
				Value val = ((DefinitionStmt) sCallSite).getLeftOp();
				return new SourceInfo(manager.getAccessPathFactory().createAccessPath(val, true));
			}
			return null;
		}

		@Override
		public SinkInfo getSinkInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			return sCallSite instanceof IfStmt ? new SinkInfo() : null;
		}

		@Override
		public SinkInfo getInverseSourceInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			if (sCallSite instanceof DefinitionStmt && sCallSite.containsInvokeExpr()
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("currentTimeMillis")
					&& (ap == null || ((DefinitionStmt) sCallSite).getLeftOp() == ap.getPlainValue())) {
				return new SinkInfo();
			}
			return null;
		}

		@Override
		public SourceInfo getInverseSinkInfo(Stmt sCallSite, InfoflowManager manager) {
			if (!(sCallSite instanceof IfStmt))
				return null;
			Value cond = ((IfStmt) sCallSite).getCondition();
			if (!(cond instanceof LeExpr))
				return null;
			LeExpr le = (LeExpr) cond;
			AccessPath ap = manager.getAccessPathFactory().createAccessPath(le.getOp1(), true);
			return ap != null ? new SourceInfo(ap) : null;
		}

		@Override
		public void initialize() {
			//
		}

	}

	private final class sourceToSourceSSM extends BaseSourceSinkManager {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InfoflowManager manager) {
			if (sCallSite instanceof DefinitionStmt && sCallSite.containsInvokeExpr()
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")) {
				Value val = ((DefinitionStmt) sCallSite).getLeftOp();
				return new SourceInfo(manager.getAccessPathFactory().createAccessPath(val, true));
			}
			return null;
		}

		@Override
		public SinkInfo getInverseSourceInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			if (sCallSite.containsInvokeExpr() && sCallSite instanceof DefinitionStmt
					&& sCallSite.getInvokeExpr().getMethod().getName().equals("getSecret")
					&& (ap == null || ((DefinitionStmt) sCallSite).getLeftOp() == ap.getPlainValue())) {
				SootMethod target = sCallSite.getInvokeExpr().getMethod();
				return new SinkInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)));
			}
			return null;
		}
	}

	private final class parameterSourceSSM extends BaseSourceSinkManager {

		@Override
		public SourceInfo getSourceInfo(Stmt sCallSite, InfoflowManager manager) {
			if (sCallSite.containsInvokeExpr()) {
				InvokeExpr iexpr = sCallSite.getInvokeExpr();
				String name = iexpr.getMethod().getName();
				boolean includeExistingImmutableAliases = name.equals("annotatedSource");
				if ((name.equals("source") || includeExistingImmutableAliases) && iexpr.getArgCount() > 0) {
					AccessPath ap = manager.getAccessPathFactory().createAccessPath(iexpr.getArg(0), null, null, true,
							false, true, AccessPath.ArrayTaintType.ContentsAndLength, true);
					return new SourceInfo(ap);
				}
			}
			return null;
		}

		@Override
		public SinkInfo getInverseSourceInfo(Stmt sCallSite, InfoflowManager manager, AccessPath ap) {
			if (sCallSite.containsInvokeExpr()) {
				InvokeExpr iexpr = sCallSite.getInvokeExpr();
				String name = iexpr.getMethod().getName();
				boolean includeExistingImmutableAliases = name.equals("annotatedSource");
				if ((name.equals("source") || includeExistingImmutableAliases) && iexpr.getArgCount() > 0) {
					if (ap == null)
						return new SinkInfo();
					else if (iexpr.getArg(0) == ap.getPlainValue()) {
						SootMethod target = sCallSite.getInvokeExpr().getMethod();
						return new SinkInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)));
					}
				}
			}
			return null;
		}

		@Override
		public SourceInfo getInverseSinkInfo(Stmt sCallSite, InfoflowManager manager) {
			if (!sCallSite.containsInvokeExpr())
				return null;

			SootMethod target = sCallSite.getInvokeExpr().getMethod();
			if ((target.getSignature().equals(sinkAP) || target.getSignature().equals(sinkAP2)
					|| target.getSignature().equals(sink)) && sCallSite.getInvokeExpr().getArgCount() > 0) {
				AccessPath ap = manager.getAccessPathFactory().createAccessPath(sCallSite.getInvokeExpr().getArg(0),
						null, null, true, false, true, AccessPath.ArrayTaintType.ContentsAndLength, true);
				return new SourceInfo(new MethodSourceSinkDefinition(new SootMethodAndClass(target)), ap);
			}
			return null;
		}
	}

	@Test(timeout = 300000)
	public void fieldTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testDataObject()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), getSecretSSM);
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertTrue(infoflow.getResults().isPathBetweenMethods(sink, sourceGetSecret));
	}

	@Test(timeout = 300000)
	public void negativeFieldTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testDataObject()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void accessPathTypesTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testAccessPathTypes()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), getSecretOrSecret2SSM);
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertTrue(infoflow.getResults().isPathBetweenMethods(sink, sourceGetSecret));
		Assert.assertTrue(infoflow.getResults().isPathBetweenMethods(sink, sourceGetSecret2));
	}

	@Test(timeout = 300000)
	public void sourceAccessPathTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testSourceAccessPaths()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void sinkAccessPathTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testSinkAccessPaths()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void sinkAccessPathTest2() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void testSinkAccessPaths2()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), noTaintSubFieldsSSM);
		negativeCheckInfoflow(infoflow);
	}

	@Test(timeout = 300000)
	public void ifAsSinkTest() {
		IInfoflow infoflow = initInfoflow();
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void ifAsSinkTest()>");
		infoflow.getConfig().setImplicitFlowMode(InfoflowConfiguration.ImplicitFlowMode.AllImplicitFlows);
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), new ifAsSinkSSM());
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
	}

	@Test(timeout = 300000)
	public void sourceToSourceTest() {
		IInfoflow infoflow = initInfoflow(true);
		((EasyTaintWrapper) infoflow.getTaintWrapper())
				.addIncludePrefix("soot.jimple.infoflow.test.SourceSinkTestCode");
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void sourceToSourceTest()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), new sourceToSourceSSM());
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertEquals(1, infoflow.getResults().numConnections());
	}

	@Test(timeout = 300000)
	public void parameterSourceTest1() {
		IInfoflow infoflow = initInfoflow(true);
		((EasyTaintWrapper) infoflow.getTaintWrapper())
				.addIncludePrefix("soot.jimple.infoflow.test.SourceSinkTestCode");
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void parameterSourceTest1()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), new parameterSourceSSM());
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertEquals(1, infoflow.getResults().numConnections());
	}

	@Test(timeout = 300000)
	public void parameterSourceTest2() {
		IInfoflow infoflow = initInfoflow(true);
		((EasyTaintWrapper) infoflow.getTaintWrapper())
				.addIncludePrefix("soot.jimple.infoflow.test.SourceSinkTestCode");
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void parameterSourceTest2()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), new parameterSourceSSM());
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertEquals(1, infoflow.getResults().numConnections());
	}

	@Test(timeout = 300000)
	public void parameterSourceTest3() {
		IInfoflow infoflow = initInfoflow(true);
		((EasyTaintWrapper) infoflow.getTaintWrapper())
				.addIncludePrefix("soot.jimple.infoflow.test.SourceSinkTestCode");
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void parameterSourceTest3()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), new parameterSourceSSM());
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertEquals(1, infoflow.getResults().numConnections());
	}

	@Test(timeout = 300000)
	public void parameterSourceTest4() {
		IInfoflow infoflow = initInfoflow(true);
		((EasyTaintWrapper) infoflow.getTaintWrapper())
				.addIncludePrefix("soot.jimple.infoflow.test.SourceSinkTestCode");
		List<String> epoints = new ArrayList<String>();
		epoints.add("<soot.jimple.infoflow.test.SourceSinkTestCode: void parameterSourceTest4()>");
		infoflow.computeInfoflow(appPath, libPath, new DefaultEntryPointCreator(epoints), new parameterSourceSSM());
		Assert.assertTrue(infoflow.isResultAvailable());
		Assert.assertEquals(1, infoflow.getResults().size());
		Assert.assertEquals(1, infoflow.getResults().numConnections());
	}

}
