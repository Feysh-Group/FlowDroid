package soot.jimple.infoflow.integration.test.junit;

import org.junit.Assert;
import org.junit.Test;
import org.xmlpull.v1.XmlPullParserException;
import soot.jimple.infoflow.InfoflowConfiguration;
import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.methodSummary.data.provider.EagerSummaryProvider;
import soot.jimple.infoflow.methodSummary.taintWrappers.SummaryTaintWrapper;
import soot.jimple.infoflow.methodSummary.taintWrappers.TaintWrapperFactory;
import soot.jimple.infoflow.results.InfoflowResults;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;

import javax.xml.stream.XMLStreamException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Collections;

/**
 * Tests that uncovered a bug.
 */
public class AndroidRegressionTests extends BaseJUnitTests {
    @Override
    protected ITaintPropagationWrapper getTaintWrapper() {
        try {
            return TaintWrapperFactory.createTaintWrapper(Collections.singleton("../soot-infoflow-summaries/summariesManual"));
        } catch (IOException | XMLStreamException e) {
            throw new RuntimeException("Could not initialize taint wrapper!");
        }
    }

    @Override
    protected void setConfiguration(InfoflowConfiguration config) {
    }

    /**
     * Tests that the alias analysis correctly stops when an overwrite happens
     */
    @Test
    public void testFlowSensitivityWithOverwrite() throws XmlPullParserException, IOException {
        SetupApplication app = initApplication("testAPKs/flowsensitiveOverwrite.apk");
        InfoflowResults results = app.runInfoflow("../soot-infoflow-android/SourcesAndSinks.txt");
        Assert.assertEquals(2, results.size());
        Assert.assertEquals(2, results.getResultSet().size());
    }
}
