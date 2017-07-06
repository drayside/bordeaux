package edu.uw.ece.bordeaux.tests;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.*;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import com.sun.tools.javac.util.Pair;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstSet;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4viz.AlloyRelation;
import edu.mit.csail.sdg.alloy4viz.AlloyType;
import edu.mit.csail.sdg.alloy4whole.SimpleGUI.BordeauxNextType;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.stats.BordeauxStatsManager;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;
import kodkod.ast.Relation;
import kodkod.instance.Instance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;


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
		testNextMiss(reporter, commandName, filepath, engine, null, null, 1);
	}
	
	@Test
	public void testCourses() {
		
		String filename = "courses.als";
		String commandName = "showSuccesfullPrograms";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		testNextMiss(reporter, commandName, filepath, engine, null, null, 1);
	}

	@Test
	public void testSinglyLinkedList() {

		String filename = "sll.als";
		String commandName = "SinglyLinkedLists";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(reporter, commandName, filepath, engine, null, null, 1);
//		testNextHit(reporter, commandName, filepath, engine, 3);
//		testNextSol(reporter, commandName, filepath, engine, 1);
	}
	
	@Test
	public void testDoublyLinkedList() {

		String filename = "dll.als";
		String commandName = "validDLL";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(reporter, commandName, filepath, engine, null, null, 1);
//		testNextHit(commandName, filepath, engine, 1);
//		testNextSol(commandName, filepath, engine, 1);
		
//		BordeauxStatsManager.getNumNearMissInTime(reporter, engine, BordeauxStatsManager.NUM_TIME_ITERATIONS, 60000);
	}
	
	@Test
	public void testBinaryTree() {

		String filename = "binary_tree.als";
		String commandName = "showValidTrees";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(reporter, commandName, filepath, engine, null, null, 1);
//		testNextHit(commandName, filepath, engine, 1);
//		testNextSol(commandName, filepath, engine, 1);
		
//		BordeauxStatsManager.getNumNearMissInTime(reporter, engine, BordeauxStatsManager.NUM_TIME_ITERATIONS, 60000);
	}
	
	@Test
	public void testFileSystem() {

		String filename = "fs.als";
		String commandName = "OneParent_correctVersion";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		testNextMiss(reporter, commandName, filepath, engine, null, null, 1);
		//testNextHit(reporter, commandName, filepath, engine, 1);
//		testNextSol(reporter, commandName, filepath, engine, 1);
	}

	@Test
	public void testDijkstra() throws NullPointerException {
		
		String filename = "dijkstra.als";
		String commandName = "ShowDijkstra";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);		

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		
		assert(engine==null);
		//testNextMiss(reporter, commandName, filepath, engine, 1);
		//testNextHit(reporter, commandName, filepath, engine, 1);
	}

	@Test
	public void testMinimalDistance() throws Exception {
		
		String filename = "binary_tree.als";
		String commandName = "showValidTrees";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		A4Solution solution = getParticularSolution(reporter, filepath, engine, commandName);
		ArrayList<String> rels = new ArrayList<String>();
		rels.add("this/Node.left");rels.add("this/Node.right");rels.add("this/Node");
		
		int count = 0;
		A4Solution curr = solution;
		boolean miss = true;
		do
		{
			List<A4Solution> solutions = null;
			if (miss){ solutions = testNextMiss(reporter, commandName, filepath, engine, null, null, 1); miss = false;}
			else {solutions = testNextHit(reporter, commandName, filepath, engine, null, null, 1); miss = true;}
			A4Solution next = solutions.get(0);
			assert(calculateDelta(curr, next, rels)<=1);
			curr = next;
			count++;
		} while(count<5);
	}
	
	@Test
	public void testRelationSuppression() throws Exception
	{
		String filename = "binary_tree.als";
		String commandName = "showValidTrees";
		File filepath = new File(BORDEUX_MODELS_DIRECTORY, filename);	

		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = createBordeauxEngine(reporter, filepath, commandName);
		A4Solution solution = getParticularSolution(reporter, filepath, engine, commandName);
		ArrayList<String> rels = new ArrayList<String>();
		rels.add("this/Node.left");rels.add("this/Node.right");rels.add("this/Node");
		
		AlloyType type = new AlloyType("Node", false, false, false, false, false, false);
		List<AlloyType> types = new ArrayList<AlloyType>();
		types.add(type);types.add(type);
		AlloyRelation rel = new AlloyRelation("left", false, false, types);
		Set<AlloyRelation> listRel = new HashSet<AlloyRelation>();
		listRel.add(rel);
		
		
		int leftCount = solution.getCompleteInstance().tuples("this/Node.left").size();
		int count = 0;
		A4Solution nextMiss = null;
		do
		{
			List<A4Solution> solutions = null;
			solutions = testNextMiss(reporter, commandName, filepath, engine, ConstSet.make(listRel), ConstSet.make(), 1);
			nextMiss = solutions.get(0);
			assert(calculateDelta(solution, nextMiss, rels)<=1);
			int tupNum = nextMiss.getCompleteInstance().tuples("this/Node.left").size();
			assert(tupNum<=leftCount);
			leftCount=tupNum;
			count++;
		} while(count<3);
		count = 0;
		A4Solution nextHit = null;
		do
		{
			List<A4Solution> solutions = null;
			solutions = testNextHit(reporter, commandName, filepath, engine, ConstSet.make(listRel), ConstSet.make(), 1);
			nextHit = solutions.get(0);
			assert(calculateDelta(nextMiss, nextHit, rels)<=1);
			int tupNum = nextHit.getCompleteInstance().tuples("this/Node.left").size();
			assert(tupNum<=leftCount);
			leftCount=tupNum;
			count++;
		} while(count<3);
	}
	
	private int calculateDelta(A4Solution sol1, A4Solution sol2, ArrayList<String> relations)
	{
		Instance inst1 = sol1.getCompleteInstance();
		Instance inst2 = sol2.getCompleteInstance();
		
		int delta = 0;
		for (int i = 0;i<relations.size();i++)
		{
			String rel = relations.get(i);
			TupleSet tups1 = inst1.tuples(rel);
			TupleSet tups2 = inst2.tuples(rel);
			delta += Math.abs(tups1.size()-tups2.size());
			/*Iterator<Tuple> it1 = tups1.iterator();
			while (it1.hasNext())
			{
				Tuple tup = it1.next();
				if (!findTuple(tup, tups2))
					delta++;
			}
			
			Iterator<Tuple> it2 = tups2.iterator();
			while(it2.hasNext())
			{
				Tuple tup = it2.next();
				if (!findTuple(tup, tups1))
					delta++;
			}*/
		}
		return delta;	
	}
	
	private boolean findTuple(Tuple tup, TupleSet ts)
	{
		Iterator<Tuple> it2 = ts.iterator();
		while (it2.hasNext())
			if (tup.toString().equals(it2.next()))
				return true;
		
		return false;
	}
	
	//Gets a specific solution to the binary_tree.als.
	private A4Solution getParticularSolution(HolaReporter reporter, File filepath, BordeauxEngine engine, String commandName) throws Exception
	{
		A4Solution sol = null;
		if ("showValidTrees".equals(commandName))
		{
			sol = reporter.getA4Solution();
			while (!isDesiredSolutionBinTree(sol))
			{
				List<A4Solution> sols = testNextSol(reporter, commandName, filepath, engine, 1);
				sol = sols.get(0);
			}
		}
		return sol;
	}
	
	//Checks to see if the given solution is the one we are looking for.
	private boolean isDesiredSolutionBinTree(A4Solution solution) throws Exception
	{
		Instance inst = solution.getCompleteInstance();
		Set<Relation> rels = inst.relations();
		Iterator it = rels.iterator();
		
		Relation left = null, right = null, node = null;
		while (it.hasNext())
		{
			Relation rel = (Relation) it.next();
			if (rel.name().equalsIgnoreCase("this/Node.left"))
				left = rel;
			else if (rel.name().equalsIgnoreCase("this/Node.right"))
				right = rel;
			else if (rel.name().equalsIgnoreCase("this/Node"))
				node = rel;
		}
		if (node==null || left == null || right == null) throw new Exception("This method is only for binary tree solutions");
		TupleSet leftTuples = inst.tuples(left);
		TupleSet rightTuples = inst.tuples(right);
		
		if (leftTuples.size()!=1 || rightTuples.size()!=1) return false;
		
		Tuple leftTup = (Tuple) leftTuples.iterator().next();
		Tuple rightTup = (Tuple) rightTuples.iterator().next();
		if (!leftTup.atom(1).equals(rightTup.atom(0)) || leftTup.atom(0).equals(rightTup.atom(1))) return false;
		if (inst.tuples(node).size()!=3) return false; 
		
		return true;
	}
	
	private List<A4Solution> testNextMiss(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine,
			ConstSet<AlloyRelation> suppAdd, ConstSet<AlloyRelation> suppSub, int numberOfRuns) {	
		
		return testSol(reporter, commandName, filepath, engine, suppAdd, suppSub, numberOfRuns, BordeauxNextType.NearMiss);
	}

	private List<A4Solution> testNextHit(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine,
			ConstSet<AlloyRelation> suppAdd, ConstSet<AlloyRelation> suppSub, int numberOfRuns) {
		
		return testSol(reporter, commandName, filepath, engine, suppAdd, suppSub, numberOfRuns, BordeauxNextType.NearHit);
	}

	private List<A4Solution> testNextSol(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine, int numberOfRuns) {
		
		return testSol(reporter, commandName, filepath, engine, null, null, numberOfRuns, BordeauxNextType.NextSolution);
	}
	
	private List<A4Solution> testSol(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine,
			ConstSet<AlloyRelation> suppAdd, ConstSet<AlloyRelation> suppSub, int numberOfRuns, BordeauxNextType nextType) {	
		
		assertNotNull(engine);
		
		A4Solution initialSolution = engine.getInitialSolution();
		System.out.println(initialSolution);
		List<A4Solution> prevSols = new ArrayList<>();
		List<A4Solution> sols = new ArrayList<A4Solution>();
		long startTime = System.currentTimeMillis();
		for(int i = 0; i < numberOfRuns; i++) {
			
			System.out.println("current done= " + i);
			
			if (System.currentTimeMillis() - startTime > 60*1000){
				System.out.println("max number="+i);
				System.exit(-1);
			}
			
			A4Solution sol = null;
			switch(nextType) {
				case NearMiss: {
					sol = engine.nextNearMiss(reporter, suppAdd==null ? ConstSet.make() : suppAdd, suppSub==null ? ConstSet.make() : suppSub);
					System.out.println(sol);
					System.out.println("Stat for nearmiss="+reporter);
					break;					
				}
				case NearHit: {
					sol = engine.nextNearHit(reporter, suppAdd==null ? ConstSet.make() : suppAdd, suppSub==null ? ConstSet.make() : suppSub);
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

			assertNotEquals(sol, initialSolution);
			prevSols.add(sol);
			if (sol!=null) sols.add(sol);
		}
		return sols;
	}
	
	
	public static BordeauxEngine createBordeauxEngine(A4Reporter reporter, File filepath, String commandName) {

		assertNotNull(commandName);
		
		Command command = ExtractorUtils.getCommandFromNamePainfully(filepath.getAbsolutePath(), commandName);
		assertNotNull("Cannot find command from command name", command);
		
		System.out.println(filepath.getAbsolutePath());
		
		try {
			A4CommandExecuter.get().runAlloyThenGetAnswers(filepath.getAbsolutePath(), reporter, command.label);
			A4Solution initialSoln = reporter.getA4Solution();
			System.out.println("stat for Initial="+reporter);
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
		filesAndCommands.add(new Pair<File, String>(new File(BORDEUX_MODELS_DIRECTORY, "dijkstra.als"), "showDijkstra"));
		BordeauxStatsManager.evaluateAll(filesAndCommands, outputFile);
	}
	
}
