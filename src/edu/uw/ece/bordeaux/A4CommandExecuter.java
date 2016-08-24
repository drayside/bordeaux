package edu.uw.ece.bordeaux;

import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreGranularity;
import static edu.mit.csail.sdg.alloy4.A4Preferences.CoreMinimization;
import static edu.mit.csail.sdg.alloy4.A4Preferences.NoOverflow;
import static edu.mit.csail.sdg.alloy4.A4Preferences.RecordKodkod;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SkolemDepth;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Solver;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SolverThreads;
import static edu.mit.csail.sdg.alloy4.A4Preferences.SolverThreadsShareClauses;
import static edu.mit.csail.sdg.alloy4.A4Preferences.Unrolls;
import static edu.mit.csail.sdg.alloy4.A4Preferences.UseHOLSolver;

import java.io.File;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.commons.collections4.MultiValuedMap;
import org.apache.commons.collections4.map.MultiValueMap;
import org.apache.commons.collections4.multimap.HashSetValuedHashMap;

import edu.mit.csail.sdg.alloy4.A4Preferences;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.IA4Reporter;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateDeclarativeConstriant2DeclarativeFormula;
import edu.uw.ece.bordeaux.Configuration;
import kodkod.ast.Formula;

/**
 * This class is for executing the decomposer using Alloy 4
 * 
 * @author Fikayo Odunayo
 *
 */
public class A4CommandExecuter {

	final public static String COMMAND_BLOCK_NAME = "check_or_run_assert_or_preicate_name";
	final static Logger logger = Logger
			.getLogger(A4CommandExecuter.class.getName() + "--"
					+ Thread.currentThread().getName());

	private static A4CommandExecuter instance;
	private static Object lock = new Object();

	private A4CommandExecuter() {
		setUp();
	}

	public static A4CommandExecuter get() {
		synchronized(lock) {
			if (instance == null) {
				instance = new A4CommandExecuter();
			}
		}
		
		return instance;
	}

	private void setUp() {
		copyFromJAR();
		final String binary = alloyHome() + fs + "binary";
		// Add the new JNI location to the java.library.path
		try {
			System.setProperty("java.library.path", binary);
			// The above line is actually useless on Sun JDK/JRE (see Sun's bug ID
			// 4280189)
			// The following 4 lines should work for Sun's JDK/JRE (though they
			// probably won't work for others)
			String[] newarray = new String[] { binary };
			java.lang.reflect.Field old = ClassLoader.class
					.getDeclaredField("usr_paths");
			old.setAccessible(true);
			old.set(null, newarray);
		} catch (Throwable ex) {
		}
	}

	public Module parse(final String fileName, final A4Reporter rep) throws Err {

		return CompUtil.parseEverything_fromFile(rep, null, fileName);
	}

	public Module parseOneModule(final String content, final A4Reporter rep)
			throws Err {

		return CompUtil.parseOneModule(/* rep, */ content);
	}

	public void runOverString(String content, A4Reporter rep) throws Err {

		if (Configuration.IsInDeubbungMode)
			logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]"
					+ "An Alloy content is being processed soon.");

		CompModule world = (CompModule) parseOneModule(content, rep);

		if (Configuration.IsInDeubbungMode)
			logger.log(Level.INFO,
					"[" + Thread.currentThread().getName() + "]" + "An Alloy is parsed.");

		A4Options options = new A4Options();

		options.solver = A4Options.SatSolver.SAT4J;
		options.symmetry = 0;

		for (Command command : world.getAllCommands()) {
			A4Solution ans = TranslateAlloyToKodkod.execute_command(rep,
					world.getAllReachableSigs(), command, options);
			if (Configuration.IsInDeubbungMode)
				logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]"
						+ "An Alloy is executed and the result is: " + ans);

		}

	}

	public List<Formula> translateAlloy2KK(String fileName, A4Reporter rep,
			String commandName) throws Err {
		List<Formula> result = null;

		// Parse+typecheck the model
		if (Configuration.IsInDeubbungMode)
			logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]"
					+ "=========== Parsing+Typechecking " + fileName + " =============");

		CompModule world = (CompModule) parse(fileName, rep);

		// Choose some default options for how you want to execute the commands
		A4Options options = new A4Options();

		options.solver = A4Options.SatSolver.SAT4J;
		options.symmetry = 0;

		for (Command command : world.getAllCommands()) {

			if (!command.label.equals(commandName))
				continue;
			// Execute the command
			if (Configuration.IsInDeubbungMode)
				logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]"
						+ "============ Command " + command + ": ============");

			result = TranslateDeclarativeConstriant2DeclarativeFormula.translate(rep,
					world.getAllReachableSigs(), command, options);
		}

		if (null == result)
			throw new RuntimeException(
					"Command name '" + commandName + "' is not found");

		return result;

	}

	public A4Solution runAlloyThenGetAnswers(String filename, A4Reporter rep, String commandName) throws Err {
		
		A4Solution result = null;
		// Parse+typecheck the model
		if (Configuration.IsInDeubbungMode)
			logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]"
					+ "=========== Parsing+Typechecking " + filename + " =============");
		
		CompModule world = (CompModule) parse(filename, rep);
		// Choose some default options for how you want to execute the commands
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.SAT4J;
		options.symmetry = 0;
		options.higherOrderSolver = false;

		for (Command command : world.getAllCommands()) {
			if (!command.label.equals(commandName)) {
				continue;
			}

			// Execute the command
			if (Configuration.IsInDeubbungMode)
				logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]"
						+ "============ Command " + command + ": ============");

			result = TranslateAlloyToKodkod.execute_command(rep,
					world.getAllReachableSigs(), command, options);
		}

		if (null == result)
			throw new RuntimeException(
					"Command name '" + commandName + "' is not found");

		return result;
	}

	public Map<Command, A4Solution> runAlloyThenGetAnswers(String[] filenames, A4Reporter rep) throws Err {
		// Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
		// By default, the A4Reporter ignores all these events (but you can extend
		// the A4Reporter to display the event for the user)

		Map<Command, A4Solution> result = new HashMap<>();

		for (String filename : filenames) {
			// Parse+typecheck the model
			if (Configuration.IsInDeubbungMode)
				logger.log(Level.INFO,
						"[" + Thread.currentThread().getName() + "]"
								+ "=========== Parsing+Typechecking " + filename
								+ " =============");

			CompModule world = (CompModule) parse(filename, rep);

			// Choose some default options for how you want to execute the commands
			A4Options options = new A4Options();

			options.solver = A4Options.SatSolver.SAT4J;
			options.symmetry = 0;

			for (Command command : world.getAllCommands()) {

				// Execute the command
				if (Configuration.IsInDeubbungMode)
					logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]"
							+ "============ Command " + command + ": ============");

				result.put(command, TranslateAlloyToKodkod.execute_command(rep,
						world.getAllReachableSigs(), command, options));
			}
		}

		return Collections.unmodifiableMap(result);
	}

	public MultiValuedMap<String, A4Solution> executeHola(A4Reporter rep, String tmpDirectory, String commandName, String... filenames) throws Err {
		
		MultiValuedMap<String, A4Solution> result = new HashSetValuedHashMap<>();

        // Choose some default options for how you want to execute the commands
        A4Options opt = new A4Options();
         opt.tempDirectory = alloyHome() + fs + "tmp";
        //opt.tempDirectory = tmpDirectory;
        opt.solverDirectory = alloyHome() + fs + "binary";
        opt.recordKodkod = RecordKodkod.get();
        opt.noOverflow = NoOverflow.get();
        opt.unrolls = Version.experimental ? Unrolls.get() : (-1);
        opt.skolemDepth = SkolemDepth.get();
        opt.higherOrderSolver = true;
        opt.holMaxIter = A4Preferences.HOLMaxIter.get();
        opt.holFullIncrements = !A4Preferences.HOLForceIncInd.get();
        opt.coreMinimization = CoreMinimization.get();
        opt.coreGranularity = CoreGranularity.get();
        opt.solver = Solver.get();
        opt.solverThreads = SolverThreads.get();
        opt.solverThreadsShareClauses = SolverThreadsShareClauses.get();
        
        opt.renameAtoms = false;
        System.out.println(opt);
        
        for (String filename : filenames) {

            if (Configuration.IsInDeubbungMode)
                logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]" + "=========== Parsing+Typechecking " + filename + " =============");

            opt.originalFilename = filename;
            CompModule world = (CompModule) parse(filename, (A4Reporter) rep);

            for (Command command : world.getAllCommands()) {
            	
            	if(commandName != null && !command.label.equals(commandName)) continue;
            	
                if (Configuration.IsInDeubbungMode)
                    logger.log(Level.INFO, "[" + Thread.currentThread().getName() + "]" + "============ Command " + command + ": ============");

//                result.put(command, TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, opt));

                TranslateAlloyToKodkod tr = TranslateAlloyToKodkod.translate(rep, world.getAllReachableSigs(), command, opt);
                A4Solution sol = tr.executeCommand();
//                System.exit(0);
                result.put(commandName, sol);
            }
        }

        return result;
	}
	
	public void runAlloy(String fileName, A4Reporter rep, String commandName) throws Err {
		runAlloyThenGetAnswers(fileName, rep, commandName);
	}
	
	public void runAlloy(String[] args, A4Reporter rep) throws Err {
		runAlloyThenGetAnswers(args, rep);
	}

	private static void copyFromJAR() {
		// Compute the appropriate platform
		String os = System.getProperty("os.name").toLowerCase(Locale.US)
				.replace(' ', '-');
		if (os.startsWith("mac-"))
			os = "mac";
		else if (os.startsWith("windows-"))
			os = "windows";
		String arch = System.getProperty("os.arch").toLowerCase(Locale.US)
				.replace(' ', '-');
		if (arch.equals("powerpc"))
			arch = "ppc-" + os;
		else
			arch = arch.replaceAll("\\Ai[3456]86\\z", "x86") + "-" + os;
		if (os.equals("mac"))
			arch = "x86-mac"; // our pre-compiled binaries are all universal binaries
		// Find out the appropriate Alloy directory
		final String platformBinary = alloyHome() + fs + "binary";
		// Write a few test files
		try {
			(new File(platformBinary)).mkdirs();
			Util.writeAll(platformBinary + fs + "tmp.cnf", "p cnf 3 1\n1 0\n");
		} catch (Err er) {
			// The error will be caught later by the "berkmin" or "spear" test
		}
		// Copy the platform-dependent binaries
		Util.copy(true, false, platformBinary, arch + "/libminisat.so",
				arch + "/libminisatx1.so", arch + "/libminisat.jnilib",
				arch + "/libminisatprover.so", arch + "/libminisatproverx1.so",
				arch + "/libminisatprover.jnilib", arch + "/libzchaff.so",
				arch + "/libzchaffx1.so", arch + "/libzchaff.jnilib", arch + "/berkmin",
				arch + "/spear");
		Util.copy(false, false, platformBinary, arch + "/minisat.dll",
				arch + "/minisatprover.dll", arch + "/zchaff.dll",
				arch + "/berkmin.exe", arch + "/spear.exe");
		// Copy the model files
		Util.copy(false, true, alloyHome(),
				"models/book/appendixA/addressBook1.als",
				"models/book/appendixA/addressBook2.als",
				"models/book/appendixA/barbers.als",
				"models/book/appendixA/closure.als",
				"models/book/appendixA/distribution.als",
				"models/book/appendixA/phones.als", "models/book/appendixA/prison.als",
				"models/book/appendixA/properties.als",
				"models/book/appendixA/ring.als", "models/book/appendixA/spanning.als",
				"models/book/appendixA/tree.als", "models/book/appendixA/tube.als",
				"models/book/appendixA/undirected.als",
				"models/book/appendixE/hotel.thm",
				"models/book/appendixE/p300-hotel.als",
				"models/book/appendixE/p303-hotel.als",
				"models/book/appendixE/p306-hotel.als",
				"models/book/chapter2/addressBook1a.als",
				"models/book/chapter2/addressBook1b.als",
				"models/book/chapter2/addressBook1c.als",
				"models/book/chapter2/addressBook1d.als",
				"models/book/chapter2/addressBook1e.als",
				"models/book/chapter2/addressBook1f.als",
				"models/book/chapter2/addressBook1g.als",
				"models/book/chapter2/addressBook1h.als",
				"models/book/chapter2/addressBook2a.als",
				"models/book/chapter2/addressBook2b.als",
				"models/book/chapter2/addressBook2c.als",
				"models/book/chapter2/addressBook2d.als",
				"models/book/chapter2/addressBook2e.als",
				"models/book/chapter2/addressBook3a.als",
				"models/book/chapter2/addressBook3b.als",
				"models/book/chapter2/addressBook3c.als",
				"models/book/chapter2/addressBook3d.als",
				"models/book/chapter2/theme.thm", "models/book/chapter4/filesystem.als",
				"models/book/chapter4/grandpa1.als",
				"models/book/chapter4/grandpa2.als",
				"models/book/chapter4/grandpa3.als", "models/book/chapter4/lights.als",
				"models/book/chapter5/addressBook.als",
				"models/book/chapter5/lists.als", "models/book/chapter5/sets1.als",
				"models/book/chapter5/sets2.als", "models/book/chapter6/hotel.thm",
				"models/book/chapter6/hotel1.als", "models/book/chapter6/hotel2.als",
				"models/book/chapter6/hotel3.als", "models/book/chapter6/hotel4.als",
				"models/book/chapter6/mediaAssets.als",
				"models/book/chapter6/memory/abstractMemory.als",
				"models/book/chapter6/memory/cacheMemory.als",
				"models/book/chapter6/memory/checkCache.als",
				"models/book/chapter6/memory/checkFixedSize.als",
				"models/book/chapter6/memory/fixedSizeMemory.als",
				"models/book/chapter6/memory/fixedSizeMemory_H.als",
				"models/book/chapter6/ringElection.thm",
				"models/book/chapter6/ringElection1.als",
				"models/book/chapter6/ringElection2.als",
				"models/examples/algorithms/dijkstra.als",
				"models/examples/algorithms/dijkstra.thm",
				"models/examples/algorithms/messaging.als",
				"models/examples/algorithms/messaging.thm",
				"models/examples/algorithms/opt_spantree.als",
				"models/examples/algorithms/opt_spantree.thm",
				"models/examples/algorithms/peterson.als",
				"models/examples/algorithms/ringlead.als",
				"models/examples/algorithms/ringlead.thm",
				"models/examples/algorithms/s_ringlead.als",
				"models/examples/algorithms/stable_mutex_ring.als",
				"models/examples/algorithms/stable_mutex_ring.thm",
				"models/examples/algorithms/stable_orient_ring.als",
				"models/examples/algorithms/stable_orient_ring.thm",
				"models/examples/algorithms/stable_ringlead.als",
				"models/examples/algorithms/stable_ringlead.thm",
				"models/examples/case_studies/INSLabel.als",
				"models/examples/case_studies/chord.als",
				"models/examples/case_studies/chord2.als",
				"models/examples/case_studies/chordbugmodel.als",
				"models/examples/case_studies/com.als",
				"models/examples/case_studies/firewire.als",
				"models/examples/case_studies/firewire.thm",
				"models/examples/case_studies/ins.als",
				"models/examples/case_studies/iolus.als",
				"models/examples/case_studies/sync.als",
				"models/examples/case_studies/syncimpl.als",
				"models/examples/puzzles/farmer.als",
				"models/examples/puzzles/farmer.thm",
				"models/examples/puzzles/handshake.als",
				"models/examples/puzzles/handshake.thm",
				"models/examples/puzzles/hanoi.als",
				"models/examples/puzzles/hanoi.thm",
				"models/examples/systems/file_system.als",
				"models/examples/systems/file_system.thm",
				"models/examples/systems/javatypes_soundness.als",
				"models/examples/systems/lists.als",
				"models/examples/systems/lists.thm",
				"models/examples/systems/marksweepgc.als",
				"models/examples/systems/views.als",
				"models/examples/toys/birthday.als",
				"models/examples/toys/birthday.thm",
				"models/examples/toys/ceilingsAndFloors.als",
				"models/examples/toys/ceilingsAndFloors.thm",
				"models/examples/toys/genealogy.als",
				"models/examples/toys/genealogy.thm",
				"models/examples/toys/grandpa.als", "models/examples/toys/grandpa.thm",
				"models/examples/toys/javatypes.als", "models/examples/toys/life.als",
				"models/examples/toys/life.thm", "models/examples/toys/numbering.als",
				"models/examples/toys/railway.als", "models/examples/toys/railway.thm",
				"models/examples/toys/trivial.als",
				"models/examples/tutorial/farmer.als", "models/util/boolean.als",
				"models/util/graph.als", "models/util/integer.als",
				"models/util/natural.als", "models/util/ordering.als",
				"models/util/relation.als", "models/util/seqrel.als",
				"models/util/sequence.als", "models/util/sequniv.als",
				"models/util/ternary.als", "models/util/time.als");
		// Record the locations
		System.setProperty("alloy.theme0", alloyHome() + fs + "models");
		System.setProperty("alloy.home", alloyHome());
	}

	private static synchronized String alloyHome() {
		if (alloyHome != null)
			return alloyHome;
		String temp = System.getProperty("java.io.tmpdir");
		if (temp == null || temp.length() == 0)
			OurDialog.fatal(
					"Error. JVM need to specify a temporary directory using java.io.tmpdir property.");
		String username = System.getProperty("user.name");
		File tempfile = new File(temp + File.separatorChar + "alloy4tmp40-"
				+ (username == null ? "" : username));
		tempfile.mkdirs();
		String ans = Util.canon(tempfile.getPath());
		if (!tempfile.isDirectory()) {
			OurDialog.fatal("Error. Cannot create the temporary directory " + ans);
		}
		if (!Util.onWindows()) {
			String[] args = { "chmod", "700", ans };
			try {
				Runtime.getRuntime().exec(args).waitFor();
			} catch (Throwable ex) {
			} // We only intend to make a best effort.
		}
		return alloyHome = ans;
	}

	private static String alloyHome = null;
	private static final String fs = System.getProperty("file.separator");

}
