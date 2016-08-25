package edu.uw.ece.bordeaux.stats;

import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import com.sun.tools.javac.util.Pair;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.tests.BordeauxEngineTest;

public final class BordeauxStatsManager {

	public static final int NUM_MILLISECONDS_IN_A_MINUTE = 60000;
	public static final int NUM_TIME_ITERATIONS = 10;
	public static final int NUM_ALLOY_ITERATIONS = 10;
	
	public static void evaluateAll(List<Pair<File, String>> filesAndCommands, File outputFile) {
		
		final StringBuffer output = new StringBuffer();
		output.append("filename, commandName, solveTime, evalTime, translationTime, totalVaraibles, clauses, numNearMissPerMin, numNearMissByAlloy\n");
		
		Thread[] threads = new Thread[filesAndCommands.size()];
		int i = 0;
		for(Pair<File, String> pair : filesAndCommands) {
			threads[i++] = new Thread(new Runnable() {

				@Override
				public void run() {
					BordeauxStatistics stats = evaluate(pair.fst, pair.snd);
					output.append(stats.toString() + "\n");
				}
				
			});
		}
		
		// Wait for threads
		for(Thread t : threads) {
			try {
				t.join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		
		// Print to file
		try {
			Util.writeAll(outputFile.getAbsolutePath(), output.toString());
		} catch (Err e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static BordeauxStatistics evaluate(File filepath, String commandName) {
		
		HolaReporter reporter = new HolaReporter();
		BordeauxEngine engine = BordeauxEngineTest.createBordeauxEngine(reporter, filepath, commandName);
		
		A4Solution firstNearMiss = engine.nextNearMiss(reporter);
		long solveTime = reporter.solveTime;
		long evalTime = reporter.evalTime;
		long translationTime = reporter.trasnalationTime;
		long totalVaraibles = reporter.totalVaraibles;
		long clauses = reporter.clauses;
		
		double avgNumPerMin = BordeauxStatsManager.getNumNearMissInTime(reporter, engine, NUM_TIME_ITERATIONS, NUM_MILLISECONDS_IN_A_MINUTE);
		int numNearMissPerMin = (int)Math.round(avgNumPerMin);
		int numNearMissByAlloy = BordeauxStatsManager.getNumMissByAlloy(reporter, filepath, commandName, firstNearMiss, NUM_ALLOY_ITERATIONS);
		
		return new BordeauxStatistics(filepath.getName(), commandName, solveTime, evalTime, translationTime, totalVaraibles, clauses, numNearMissPerMin, numNearMissByAlloy);
	}
	
	private static int getNumMissByAlloy(A4Reporter reporter, File filepath, String commandName, A4Solution firstNearMiss, int numTimeIterations) {
	
		return 0;
	}

	public static double getNumNearMissInTime(A4Reporter reporter, BordeauxEngine engine, int numIterations, long numMilliseconds) {	

//		System.out.println("Starting timer for: " + filepath.getName());
//		System.out.println("===================================\n");
		
		double avg = time(reporter, engine, numMilliseconds);;
		for(int i = 1; i < numIterations; i++) {
			int next = time(reporter, engine, numMilliseconds);
			avg = ((avg * i) + next) / (i+1);
		}		

//		System.out.println("\n===================================");
//		System.out.println("Done for: " + filepath.getName());
//		System.out.format("Generated: %f instances over %d runs\n", avg, numIterations);
		
		return avg;
	}
	
	private static int time(A4Reporter reporter, BordeauxEngine engine, long numMilliseconds) {	
		
		assertNotNull(engine);
		
		int numGenerated = 0;
		long base = System.currentTimeMillis();
		for(long timePassed = 0; timePassed < numMilliseconds; timePassed = System.currentTimeMillis() - base) {
			engine.nextNearMiss(reporter);	
			numGenerated++;	
		}

		return numGenerated;
	}

}
