package edu.uw.ece.bordeaux.stats;

import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.sql.Time;
import java.util.ArrayList;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;
import java.util.logging.Level;
import java.util.logging.Logger;

import com.sun.imageio.plugins.tiff.TIFFImageReaderSpi;
import com.sun.tools.javac.util.Pair;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.tests.BordeauxEngineTest;
import edu.uw.ece.bordeaux.util.Utils;

public final class BordeauxStatsManager {

	private final static Logger logger = Logger.getLogger(BordeauxStatsManager.class.getName() + "--" + Thread.currentThread().getName());
	
	public static final int NUM_MILLISECONDS_IN_A_MINUTE = 60000;
	public static final int NUM_TIME_ITERATIONS = 10;
	public static final int NUM_ALLOY_ITERATIONS = 10;
	public static final int MAX_ALLOY_RETRY = 100;
	
	public static void evaluateAll(List<Pair<File, String>> filesAndCommands, File outputFile) {
		
		System.out.println("Starting evulation");
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
				logger.log(Level.SEVERE, "Thread '" + t.getName() + "' was interrupted", e);
			}
		}
		
		// Print to file
		try {
			Util.writeAll(outputFile.getAbsolutePath(), output.toString());
		} catch (Err e) {
			e.printStackTrace();
			logger.log(Level.SEVERE, "Unknown error while writing log to file", e);
		}
	}
	
	public static BordeauxStatistics evaluate(File filepath, String commandName) {
		
		try{
			
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
			int numNearMissByAlloy = BordeauxStatsManager.getNumMissByAlloy(reporter, filepath, commandName, firstNearMiss, NUM_ALLOY_ITERATIONS, MAX_ALLOY_RETRY);
			
			return new BordeauxStatistics(filepath.getName(), commandName, solveTime, evalTime, translationTime, totalVaraibles, clauses, numNearMissPerMin, numNearMissByAlloy);
			
		} catch (Exception e) {
			
			logger.log(Level.SEVERE, "[" + Utils.threadName() + "] Had unknown exception while evaluating", e);
			return BordeauxStatistics.getEmpty(filepath.getAbsolutePath(), commandName);
		}		
	}
	
	private static int getNumMissByAlloy(A4Reporter reporter, File filepath, String commandName, A4Solution firstNearMiss, int numTimeIterations, int maxRetry) {
	
		return 0;
	}

	public static double getNumNearMissInTime(A4Reporter reporter, BordeauxEngine engine, int numIterations, long numMilliseconds) {	

//		System.out.println("Starting timer for: " + filepath.getName());
//		System.out.println("===================================\n");
		
		double avg = time(reporter, engine, numMilliseconds);
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
		
		final MyInt numGenerated = new MyInt();
		Thread task = new Thread(new Runnable() {

			@Override
			public void run() {
				engine.nextNearMiss(reporter);	
				numGenerated.val++;
			}
			
		});
		
		task.start();
		
		try {
			Thread.sleep(numMilliseconds);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		try {
			task.interrupt();
			task.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		return numGenerated.val;
	}
	
	static class MyInt {
		
		public int val = 0;
	}

}
