package edu.uw.ece.bordeaux.tests;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;

import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerCallback;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4whole.SimpleGUI.BordeauxNextType;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.Configuration;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;


public class BordeauxEngineTest {

	public final String TMP_DIRECTORY = "./tmp/";
	public final String TOY_EXAMPLES_DIRECTORY = "./models/examples/toys/";
	public final String MIN_DIST_DIRECTORY = "./models/debugger/min_dist/";
	public final String BORDEUX_MODELS_DIRECTORY = "./models/bordeaux/";
	
	private A4Reporter reporter;
	private WorkerCallback cb;
	
	@Before
	public void setUp() {
		this.cb = new WorkerCallback() {
            public void callback(Object x) { }
            public void done() { }
            public void fail() { }
         };
         
 		this.reporter = new HolaReporter();
	}
	
	@Test
	public void testBareLinkedList() {
		
		String filename = "bare_linked_list.als";
		String commandName = "p";
		File filepath = new File(MIN_DIST_DIRECTORY, filename);			

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		testNextMiss(commandName, filepath, engine, 1);
	}
	
	@Test
	public void testCourses() {
		
		String filename = "courses.als";
		String commandName = "showSuccesfullPrograms";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		testNextMiss(commandName, filepath, engine, 1);
	}

	@Test
	public void testSinglyLinkedList() {

		String filename = "sll.als";
		String commandName = "SinglyLinkedLists";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(commandName, filepath, engine, 1);
		testNextHit(commandName, filepath, engine, 1);
//		testNextSol(commandName, filepath, engine, 1);
	}
	
	@Test
	public void testDoublyLinkedList() {

		String filename = "dll.als";
		String commandName = "validDLL";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(commandName, filepath, engine, 1);
		testNextHit(commandName, filepath, engine, 1);
//		testNextSol(commandName, filepath, engine, 1);
	}
	
	@Test
	public void testFileSystem() {

		String filename = "fs.als";
		String commandName = "OneParent_correctVersion";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(commandName, filepath, engine, 1);
		testNextHit(commandName, filepath, engine, 1);
		testNextSol(commandName, filepath, engine, 1);
	}

	@Test
	public void testDijkstra() {
		
		String filename = "dijkstra.buggy.als";
		String commandName = "check$1";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);		

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(commandName, filepath, engine, 1);
	}

	private void testNextMiss(String commandName, File filepath, BordeauxEngine engine, int numberOfRuns) {	
		
		testSol(commandName, filepath, engine, numberOfRuns, BordeauxNextType.NearMiss);
	}

	private void testNextHit(String commandName, File filepath, BordeauxEngine engine, int numberOfRuns) {
		
		testSol(commandName, filepath, engine, numberOfRuns, BordeauxNextType.NearHit);
	}

	private void testNextSol(String commandName, File filepath, BordeauxEngine engine, int numberOfRuns) {
		
		testSol(commandName, filepath, engine, numberOfRuns, BordeauxNextType.NextSolution);
	}
	
	private void testSol(String commandName, File filepath, BordeauxEngine engine, int numberOfRuns, BordeauxNextType nextType) {	
		
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
//	
//	public A4Solution tryUsing(A4Reporter reporter, String filepath, String commandName) {
//		
//		assertNotNull(commandName);
//		
//		Command command = getCommandFromNamePainfully(reporter, filepath, commandName);
//		assertNotNull("Cannot find command from command name", command);
//		
//		BordeauxEngine engine = BordeauxEngine.get();
//		
//		try {
//			return engine.getBorderInstancesFromStaticInstance(reporter, new File(filepath), command);
//		} catch (Exception e) {
//			e.printStackTrace();
//		}
//		
//		return null;
//	}
	
}
