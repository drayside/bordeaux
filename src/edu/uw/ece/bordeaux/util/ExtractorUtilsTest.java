package edu.uw.ece.bordeaux.util;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.debugger.exec.A4CommandExecuter;

/**
 * Test cases for ExtractorUtil
 * 
 * @author vajih
 *
 */
public class ExtractorUtilsTest {

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@Before
	public void setUp() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void testConvertA4SolutionToAlloySyntaxOrderedPackage() {
		// @formatter:off
		final String alloyContent = "open util/ordering [State] as so\n" +
							  		"sig State{r: State}\n" +
							  		"pred gen{some so/first and some so/next}\n" +
							  		"run gen";
		// @formatter:on
		final File testFile = new File("tmp", "ordered.als");
		try {
			Util.writeAll(testFile.getAbsolutePath(), alloyContent);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.getMessage());
		}
		final HolaReporter rep = new HolaReporter();
		A4Solution solution = null;
		try {
			solution = A4CommandExecuter.getInstance().runThenGetAnswers(testFile.getAbsolutePath(), rep, "gen");
		} catch (Err e) {
			e.printStackTrace();
			fail(e.getMessage());
		}

		final String alloySolution = ExtractorUtils.convertA4SolutionToAlloySyntax(solution);
		final String alloyContentWithSol = alloyContent + "\npred alloysol{\n" + alloySolution + "\n}\nrun alloysol";
		try {
			Util.writeAll(testFile.getAbsolutePath(), alloyContentWithSol);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.getMessage());
		}
		try {
			solution = A4CommandExecuter.getInstance().runThenGetAnswers(testFile.getAbsolutePath(), rep, "alloysol");
		} catch (Err e) {
			System.err.println(alloySolution);
			e.printStackTrace();
			fail(e.getMessage());
		}
		testFile.deleteOnExit();
	}

}
