package edu.uw.ece.bordeaux.tests;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.fail;

import java.io.File;
import java.util.HashMap;

import org.junit.Before;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;

public class BoreauxVsAlloyTest {

	final File tmpFolder = new File("tmp/test");

	@Before
	public void setUp() {
		tmpFolder.mkdirs();
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

	protected A4Solution findBoreauxNearMiss(String content, String commandName) {
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

	public int findAlloyMissExample(File filePath, final A4Solution nearMissExample, String commandName, int maxRetry) {

		int tries = 1;

		CompModule module = null;
		try {
			module = (CompModule) A4CommandExecuter.get().parse(filePath.getAbsolutePath(), A4Reporter.NOP);
		} catch (Err e) {
			e.printStackTrace();
		}

		final Command command = module.getAllCommands().stream().filter(f -> f.label.equals(commandName)).findAny()
				.get();
		final Command commandNot = command.change(ExprUnary.Op.NOT.make(command.formula.pos, command.formula));

		A4Options options = new A4Options();

		options.solver = A4Options.SatSolver.SAT4J;
		try {
			A4Solution ans = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, module.getAllReachableSigs(),
					commandNot, options);
			while (ans.satisfiable() && tries < maxRetry) {

				if (equiSAT(filePath, ExtractorUtils.convertBordeauxSolutionToAlloySyntax(nearMissExample).b,
						ExtractorUtils.convertA4SolutionToAlloySyntax(ans, false), commandName)) {

					System.out.println("NEAR MISS=" + nearMissExample);
					System.out.println(ans);
					break;
				}

				System.out.println("NEAR MISS=" + nearMissExample);
				System.out.println(
						"--->" + ExtractorUtils.convertBordeauxSolutionToAlloySyntax(nearMissExample, new HashMap<>()));
				System.out
				.println("number of tuples=" + ExtractorUtils.getNumberOfTuplesFromA4Solution(nearMissExample));

				System.out.println("ans->" + ans);
				System.out.println("number of tuples=" + ExtractorUtils.getNumberOfTuplesFromA4Solution(ans));

				ans = ans.next();
				++tries;
			}

		} catch (Err e) {
			e.printStackTrace();
		}
		return tries;

	}

	protected String findScope(File filePath, String commandName) {
		CompModule module = null;
		try {
			module = (CompModule) A4CommandExecuter.get().parse(filePath.getAbsolutePath(), A4Reporter.NOP);
		} catch (Err e) {
			e.printStackTrace();
		}

		final Command command = module.getAllCommands().stream().filter(f -> f.label.equals(commandName)).findFirst()
				.get();
		return ExtractorUtils.extractScopeFromCommand(command);

	}

	protected boolean equiSAT(File filePath, String sol1, String sol2, String commandName) {

		String filecontent = Utils.readFile(filePath.getAbsolutePath());
		String newCommandName = "__Check_EQU__";
		File newFileTmp = new File(filePath.getParentFile(), filePath.getName() + ".tmp.als");
		String newContent = filecontent + "\nassert " + newCommandName + " { (" + sol1 + ") iff (" + sol2 + ")}\ncheck "
				+ newCommandName + findScope(filePath, commandName);

		boolean result = false;
		try {
			Util.writeAll(newFileTmp.getAbsolutePath(), newContent);
			;
			result = !A4CommandExecuter.get()
					.runAlloyThenGetAnswers(newFileTmp.getAbsolutePath(), A4Reporter.NOP, newCommandName).satisfiable();
		} catch (Err e) {
			e.printStackTrace();
			System.exit(-1);
		}

		newFileTmp.deleteOnExit();

		return result;

	}

	@Test
	public void testSimplyLinked() {
		String content = "sig A{w: lone A}\npred p{no ^w & iden\n}\nrun p for 4";
		File tmpFile = new File(tmpFolder, "tmp.als");
		try {
			Util.writeAll(tmpFile.getAbsolutePath(), content);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.msg);
		}

		System.out.println(findAlloyMissExample(tmpFile, findBoreauxNearMiss(content, "p"), "p", 100));

	}

}
