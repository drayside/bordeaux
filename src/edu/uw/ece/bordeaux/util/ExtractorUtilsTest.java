package edu.uw.ece.bordeaux.util;

import static org.junit.Assert.*;

import java.io.File;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;

/**
 * Test cases for ExtractorUtil
 * 
 * @author vajih
 *
 */
public class ExtractorUtilsTest {

	
	final File tmpFolder = new File("tmp/test");

	@Before
	public void setUp() {
		tmpFolder.mkdirs();
	}
	
	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	@AfterClass
	public static void tearDownAfterClass() throws Exception {
	}

	@After
	public void tearDown() throws Exception {
	}

	@Test
	public void testConvertA4SolutionToNonAlloySyntaxOrderedPackage() {
		// @formatter:off
		final String alloyContent = "sig A{r: A}\npred p[]{some r and no A}\nrun p";
		// @formatter:on
		final File testFile = new File("tmp", "ordered.als");
		try {
			Util.writeAll(testFile.getAbsolutePath(), alloyContent);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.getMessage());
		}

		A4Solution solution = null;
		try {
			solution = A4CommandExecuter.get().runAlloyThenGetAnswers(testFile.getAbsolutePath(), A4Reporter.NOP,
					"p");
		} catch (Err e) {
			e.printStackTrace();
			fail(e.getMessage());
		}
		
		System.out.println(ExtractorUtils.convertA4SolutionToAlloySyntax(solution, false));
	}
	
	@Test
	public void testMapA4SolutionToBordeaux() {
		final A4Solution nearMissExample = findBordeauxNearMiss(
				"sig A{w: lone A}\npred p{no ^w & iden\n}\nrun p for 4 but 4 Int", "p");

		System.out.println(nearMissExample);

		assertEquals(
				new Pair<String, String>("(no A and no A<:w)",
						"(some disj A_2, A_3: univ | (A_2+ A_3 = A) and (A_3->A_2+ A_3->A_3 = A<:w))"),
				ExtractorUtils.convertBordeauxSolutionToAlloySyntax(nearMissExample));
	}

	
	protected A4Solution findBordeauxNearMiss(String content, String commandName) {
		
		File tmpFile = new File(tmpFolder, "tmp.als");
		try {
			Util.writeAll(tmpFile.getAbsolutePath(), content);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.msg);
		}

		
		final HolaReporter reporter = new HolaReporter();
		final BordeauxEngine engine = createBordeauxEngine(reporter, tmpFile, commandName);
		return engine.nextNearMiss(reporter);
	}
	
	public BordeauxEngine createBordeauxEngine(A4Reporter reporter, File filepath, String commandName) {

		assertNotNull(commandName);

		Command command = ExtractorUtils.getCommandFromNamePainfully(filepath.getAbsolutePath(), commandName);
		assertNotNull("Cannot find command from command name", command);

		try {
			A4CommandExecuter.get().runAlloy(filepath.getAbsolutePath(), reporter, command.label);
			A4Solution initialSoln = reporter.getA4Solution();
			return new BordeauxEngine(filepath, command, initialSoln);
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
	}

	@Test
	public void testConvertA4SolutionToAlloySyntaxOrderedPackage() {
		// @formatter:off
		final String alloyContent = "open util/ordering [State] as so\n" + "sig State{r: State}\n"
				+ "pred gen{some so/first and some so/next}\n" + "run gen";
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
			solution = A4CommandExecuter.get().runAlloyThenGetAnswers(testFile.getAbsolutePath(), rep, "gen");
		} catch (Err e) {
			e.printStackTrace();
			fail(e.getMessage());
		}

		final String alloySolution = ExtractorUtils.convertA4SolutionToAlloySyntax(solution, false);
		final String alloyContentWithSol = alloyContent + "\npred alloysol{\n" + alloySolution + "\n}\nrun alloysol";
		try {
			Util.writeAll(testFile.getAbsolutePath(), alloyContentWithSol);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.getMessage());
		}
		try {
			solution = A4CommandExecuter.get().runAlloyThenGetAnswers(testFile.getAbsolutePath(), rep, "alloysol");
		} catch (Err e) {
			System.err.println(alloySolution);
			e.printStackTrace();
			fail(e.getMessage());
		}
		testFile.deleteOnExit();
	}

}
