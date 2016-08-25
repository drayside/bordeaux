package edu.uw.ece.bordeaux.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import static org.junit.Assert.*;
import org.junit.Test;

import com.sun.tools.javac.util.Pair;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4whole.SimpleGUI.BordeauxNextType;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.stats.BordeauxStatsManager;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;


public class BordeauxEngineTest {

	public final static String TMP_DIRECTORY = Utils.TMP_DIRECTORY;
	public final static String TOY_EXAMPLES_DIRECTORY = "./models/examples/toys/";
	public final static String MIN_DIST_DIRECTORY = "./models/debugger/min_dist/";
	public final static String BORDEUX_MODELS_DIRECTORY = "./models/bordeaux/";
		
	@Test
	public void testBareLinkedList() {
		
		String filename = "bare_linked_list.als";
		String commandName = "p";
		File filepath = new File(MIN_DIST_DIRECTORY, filename);			

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		testNextMiss(reporter, commandName, filepath, engine, 1);
	}
	
	@Test
	public void testCourses() {
		
		String filename = "courses.als";
		String commandName = "showSuccesfullPrograms";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		testNextMiss(reporter, commandName, filepath, engine, 1);
	}

	@Test
	public void testSinglyLinkedList() {

		String filename = "sll.als";
		String commandName = "SinglyLinkedLists";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(reporter, commandName, filepath, engine, 2);
//		testNextHit(reporter, commandName, filepath, engine, 1);
//		testNextSol(commandName, filepath, engine, 1);
	}
	
	@Test
	public void testDoublyLinkedList() {

		String filename = "dll.als";
		String commandName = "validDLL";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
//		testNextMiss(commandName, filepath, engine, 1);
//		testNextHit(commandName, filepath, engine, 1);
//		testNextSol(commandName, filepath, engine, 1);
		
		BordeauxStatsManager.getNumNearMissInTime(reporter, engine, BordeauxStatsManager.NUM_TIME_ITERATIONS, 60000);
	}
	
	@Test
	public void testFileSystem() {

		String filename = "fs.als";
		String commandName = "OneParent_correctVersion";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(reporter, commandName, filepath, engine, 1);
		testNextHit(reporter, commandName, filepath, engine, 1);
//		testNextSol(reporter, commandName, filepath, engine, 1);
	}

	@Test
	public void testDijkstra() {
		
		String filename = "dijkstra.buggy.als";
		String commandName = "check$1";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);		

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(reporter, commandName, filepath, engine, 1);
		testNextHit(reporter, commandName, filepath, engine, 1);
	}

	private void testNextMiss(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine, int numberOfRuns) {	
		
		testSol(reporter, commandName, filepath, engine, numberOfRuns, BordeauxNextType.NearMiss);
	}

	private void testNextHit(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine, int numberOfRuns) {
		
		testSol(reporter, commandName, filepath, engine, numberOfRuns, BordeauxNextType.NearHit);
	}

	private void testNextSol(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine, int numberOfRuns) {
		
		testSol(reporter, commandName, filepath, engine, numberOfRuns, BordeauxNextType.NextSolution);
	}
	
	private void testSol(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine, int numberOfRuns, BordeauxNextType nextType) {	
		
		assertNotNull(engine);
		
		List<A4Solution> prevSols = new ArrayList<>();
		for(int i = 0; i < numberOfRuns; i++) {
			
			A4Solution sol = null;
			switch(nextType) {
				case NearMiss: {
					sol = engine.nextNearMiss(reporter);
					break;					
				}
				case NearHit: {
					sol = engine.nextNearHit(reporter);
					break;					
				}
				case NextSolution: {
					try {
						sol = engine.nextSolution();
					} catch (Err e) {
						e.printStackTrace();
					}
					
					break;					
				}
				
				default:
					break;
			}
			
			assertNotNull(sol);
			
			for(A4Solution prev: prevSols) {
				assertNotEquals(sol, prev);
			}

			assertNotEquals(sol, engine.getInitialSolution());
			prevSols.add(sol);
		}
	}
	
	
	public static BordeauxEngine createBordeauxEngine(A4Reporter reporter, File filepath, String commandName) {

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

	public static void main(String[] args) {
		
		File outputFile = new File(args[0]);
		List<Pair<File, String>> filesAndCommands = new ArrayList<>();
		filesAndCommands.add(new Pair<File, String>(new File(BORDEUX_MODELS_DIRECTORY, "sll.als"), "SinglyLinkedLists"));
		filesAndCommands.add(new Pair<File, String>(new File(BORDEUX_MODELS_DIRECTORY, "dll.als"), "validDLL"));
		filesAndCommands.add(new Pair<File, String>(new File(BORDEUX_MODELS_DIRECTORY, "binary_tree.als"), "showValidTrees"));
		filesAndCommands.add(new Pair<File, String>(new File(BORDEUX_MODELS_DIRECTORY, "courses.als"), "showSuccesfullPrograms"));
		filesAndCommands.add(new Pair<File, String>(new File(BORDEUX_MODELS_DIRECTORY, "fs.als"), "OneParent_correctVersion"));
		filesAndCommands.add(new Pair<File, String>(new File(BORDEUX_MODELS_DIRECTORY, "dijkstra.buggy.als"), "showDijkstra"));
		BordeauxStatsManager.evaluateAll(filesAndCommands, outputFile);
	}
	
}
