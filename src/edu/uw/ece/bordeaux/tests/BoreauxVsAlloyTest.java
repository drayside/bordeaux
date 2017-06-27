package edu.uw.ece.bordeaux.tests;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.fail;

import java.io.File;
import org.junit.Before;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstSet;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.stats.BordeauxStatsManager;
import edu.uw.ece.bordeaux.util.ExtractorUtils;

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
			A4CommandExecuter.get().runAlloy(filepath.getAbsolutePath(), reporter, null, command.label);
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
		return engine.nextNearMiss(reporter, ConstSet.make(), ConstSet.make());
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

		System.out.println(BordeauxStatsManager.getNumMissByAlloy(tmpFile, "p", findBoreauxNearMiss(content, "p"), 100));

	}

}
