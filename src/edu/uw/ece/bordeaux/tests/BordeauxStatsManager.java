package edu.uw.ece.bordeaux.tests;

import static org.junit.Assert.assertNotNull;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.engine.BordeauxEngine;

public final class BordeauxStatsManager {

	public static final int NUM_TIME_ITERATIONS = 10;
	
	public static double timeNearMiss(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine, long numMilliseconds) {	

		System.out.println("Starting timer for: " + filepath.getName());
		System.out.println("===================================\n");
		
		double avg = time(reporter, commandName, filepath, engine, numMilliseconds);;
		for(int i = 1; i < NUM_TIME_ITERATIONS; i++) {
			int next = time(reporter, commandName, filepath, engine, numMilliseconds);
			avg = ((avg * i) + next) / (i+1);
		}		

		System.out.println("\n===================================");
		System.out.println("Done for: " + filepath.getName());
		System.out.format("Generated: %f instances over %d runs\n", avg, NUM_TIME_ITERATIONS);
		
		return avg;
	}
	
	private static int time(A4Reporter reporter, String commandName, File filepath, BordeauxEngine engine, long numMilliseconds) {	

		
		assertNotNull(engine);
		
		int numGenerated = 0;
		long base = System.currentTimeMillis();
		for(long timePassed = 0; timePassed < numMilliseconds; timePassed = System.currentTimeMillis() - base) {
			
			A4Solution sol = engine.nextNearMiss(reporter);	
			numGenerated++;
			assertNotNull(sol);			
		}

		return numGenerated;
	}
}
