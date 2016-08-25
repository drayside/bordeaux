package edu.uw.ece.bordeaux.engine;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.UUID;
import java.util.logging.Level;
import java.util.logging.Logger;

import javax.management.RuntimeErrorException;

import org.apache.commons.collections4.MultiValuedMap;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4whole.SimpleReporter;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.Configuration;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.onborder.OnBorderCodeGenerator;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;

public final class BordeauxEngine {

	private final static Logger logger = Logger
			.getLogger(BordeauxEngine.class.getName() + "--" + Thread.currentThread().getName());
	private final File tmpPath;
	private final File inputPath;
	
	private boolean firstNearMiss = true;
	private boolean firstNearHit = true;
	private String currentMiss = "";
	private String currentHit = "";
	private A4Solution previousHit;
	private A4Solution previousMiss;
	private A4Solution initialSolution;
	private Command command;
	private OnBorderCodeGenerator generator;
	private File onBorderFile;
	private Set<String> relationsToExclude;
	
	/**
	 * Creates a new Bordeaux Engine instance
	 * @param inputPath - The path to the alloy source file
	 * @param command - The command executed when generating the initial solution
	 * @param initialSolution - The initial solution generated from Alloy (can't be null)
	 */
	public BordeauxEngine(File inputPath, Command command, A4Solution initialSolution) {
		this(inputPath, new File("./tmp/"), command, new HashSet<>(), initialSolution);
	}

	/**
	 * Creates a new Bordeaux Engine instance
	 * @param inputPath - The path to the alloy source file
	 * @param tmpPath - The path to the temporary directory
	 * @param command - The command executed when generating the initial solution
	 * @param initialSolution - The initial solution generated from Alloy (can't be null)
	 */
	public BordeauxEngine(File inputPath, File tmpPath, Command command, A4Solution initialSolution) {
		this(inputPath, tmpPath, command, new HashSet<>(), initialSolution);
	}
	
	/**
	 * Creates a new Bordeaux Engine instance
	 * @param inputPath - The path to the alloy source file
	 * @param tmpPath - The path to the temporary directory
	 * @param command - The command executed when generating the initial solution
	 * @param relationsToExclude - The names of the sigs and relations to be excluded
	 * @param initialSolution - The initial solution generated from Alloy (can't be null)
	 */
	public BordeauxEngine(File inputPath, File tmpPath, Command command, Set<String> relationsToExclude, A4Solution initialSolution) {
		
		if(initialSolution == null) throw new NullPointerException("Initial alloy solution cannot be null");
		
		this.inputPath = inputPath;
		this.tmpPath = tmpPath;
		this.command = command;
		this.relationsToExclude = relationsToExclude;
		this.initSolution(initialSolution);
	}
	
	private void createCodeGenerator(File inputPath, Command command) {

		if(Configuration.IsInDeubbungMode) {
			logger.info("Generating OnBorder code");
		}
		
		// Generate on Border instances
		String fileName = Utils.getFileName(inputPath.getAbsolutePath());
		String onBorderFileName = fileName + ".hola-" + UUID.randomUUID().hashCode() + ".als";
		this.onBorderFile = new File(tmpPath, onBorderFileName);
		//this.onBorderFile.deleteOnExit();
		
		PrintWriter writer = null;
		try {
			writer = new PrintWriter(onBorderFile);
		} catch (FileNotFoundException e) {
			logger.log(Level.SEVERE, Utils.threadName() + " Failed to generate printwriter for Code Generator", e);
		}

		try {
			String fileToReadFrom = inputPath.getAbsolutePath();
			int numberOfIntAtoms = (ExtractorUtils.getNumberOfTuplesFromA4Solution(this.initialSolution) * 3) / 2;
			this.generator = new OnBorderCodeGenerator(fileToReadFrom, command, this.relationsToExclude, numberOfIntAtoms, writer);
		} catch (Exception e) {
			logger.log(Level.SEVERE, Utils.threadName() + " Failed to generate on border code", e);
		}

		if (Configuration.IsInDeubbungMode) {
			logger.info("\n\nOnBorderFile for: " + onBorderFileName + "\n" + Utils.readFile(onBorderFile.getAbsolutePath()) + "\n\n");
		}
	}
	
	public A4Solution getInitialSolution() {
		return this.initialSolution;
	}
	/*
	public A4Solution getBorderInstances(A4Reporter reporter, File inputPath, String...constraints) {
					
		return this.getBorderInstances(reporter, inputPath, new File(""), constraints);
	}

	public A4Solution getBorderInstancesFromStaticInstance(A4Reporter reporter, File inputPath, Command command) {
	
		return this.getBorderInstancesFromStaticInstance(reporter, inputPath, new File(""), command);
	}
	 
	public A4Solution getBorderInstancesFromStaticInstance(A4Reporter reporter, File inputPath, String constraint1, String constraint2) {
	
		return this.getBorderInstancesFromStaticInstance(reporter, inputPath, new File(""), constraint1, constraint2);
	}
	 
	 public A4Solution getBorderInstances(A4Reporter reporter, File inputPath, File outputPath, String... constraints) {

		// Generate on Border instances
		String fileName = Utils.getFileName(inputPath.getAbsolutePath());
		String onBorderFileName = fileName + ".hola-" + UUID.randomUUID().hashCode() + ".als";
		File onBorderFile = new File(tmpPath, onBorderFileName);
		PrintWriter writer = null;
		try {
			writer = new PrintWriter(onBorderFile);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		String fileToGenerate = inputPath.getAbsolutePath();
		OnBorderCodeGenerator generator = null;
		try {
			generator = new OnBorderCodeGenerator(fileToGenerate, writer);
		} catch (Err e1) {
			e1.printStackTrace();
		}
		generator.run(constraints);

		if (Configuration.IsInDeubbungMode) {
			logger.info("==========================================================");
			logger.info("OnBorderFile for: " + fileName + "\n");
			logger.info(Utils.readFile(onBorderFile.getAbsolutePath()));
			logger.info("==========================================================");
		}

		// Run on-border instances through the higher order solver (alloy*)
		boolean success = true;
//		HolaReporter reporter = new HolaReporter();
		try {
			A4CommandExecuter.get().executeHola(reporter, this.tmpPath.getAbsolutePath(),
					onBorderFile.getAbsolutePath());
		} catch (Exception e) {
			success = false;
			e.printStackTrace();
			logger.severe(
					"[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy* on file: " + inputPath);
			if (Configuration.IsInDeubbungMode) {
				logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
			}
		}
		

		if (Configuration.IsInDeubbungMode) {
			logger.info("Alloy* Complete on : " + onBorderFile + ". Status: " + (success ? "Successful":"Failed"));
		}

		// Write generated A4Solution to outputPath as xml
		A4Solution soln = reporter.getA4Solution();
		if (success && outputPath != null && outputPath.exists()) {
			soln = reporter.getA4Solution();
			if (soln != null) {
				try {
					soln.writeXML(outputPath.getAbsolutePath());
				} catch (Exception e) {
					e.printStackTrace();
					logger.severe("[" + Thread.currentThread().getName() + "] "
							+ " Failed to write alloy* solution to XML file: " + outputPath);
					if (Configuration.IsInDeubbungMode) {
						logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
					}
				}
			}
		}

		onBorderFile.delete();
		return soln;
	}
	 
	*//**
	 * @param reporter - The SimpleReporter which updates the UI as progress comes in (Note: This reporter is not used to initial calls to Alloy)
	 * @param inputPath
	 * @param outputPath
	 * @param command
	 * @param intendedPred
	 * @return
	 *//*
	public A4Solution getBorderInstancesFromStaticInstance(A4Reporter reporter, File inputPath, File outputPath, Command command) {

		// First generate static A4olution from input path
		boolean success = true;
		try {
			A4CommandExecuter.get().runAlloy(inputPath.getAbsolutePath(), reporter, command.label);
		} catch (Exception e) {
			success = false;
			e.printStackTrace();
			logger.severe(
					"[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy on file: " + inputPath);
			if (Configuration.IsInDeubbungMode) {
				logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
			}
			
			throw new RuntimeException();
		}

		A4Solution staticSoln = reporter.getA4Solution();
		if(success && staticSoln != null) {
			logger.info("Static A4Solution acquired from Alloy...running OnBorderCodeGenerator");
	
			String constraint1 = ExtractorUtils.convertA4SolutionToAlloySyntax(staticSoln, true);
			String constraint2 = ExtractorUtils.convertFormulaExprToAlloySyntax(command.formula, true);
			return getBorderInstancesFromStaticInstance(reporter, inputPath, outputPath, constraint1, constraint2);
		}
		
		return null;
	}

	*//**
	 * This method generates a temp alloy file which will search for instances with min distance away from the static solution provided.
	 * @param reporter - The SimpleReporter which updates the UI as progress comes in (Note: This reporter is not used to initial calls to Alloy)
	 * @param inputPath
	 * @param outputPath
	 * @param constraint2
	 * @param staticSoln - The Solution to use as the static instance when finding instances with min distance.
	 * @return
	 *//*
	public A4Solution getBorderInstancesFromStaticInstance(A4Reporter reporter, File inputPath, File outputPath, String constraint1, String constraint2) {

		logger.info("Generating OnBorder code");
		
		boolean success;
		// Generate on Border instances
		String fileName = Utils.getFileName(inputPath.getAbsolutePath());
		String onBorderFileName = fileName + ".hola-" + UUID.randomUUID().hashCode() + ".als";
		File onBorderFile = new File(tmpPath, onBorderFileName);
		PrintWriter writer = null;
		try {
			writer = new PrintWriter(onBorderFile);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		try {
			String fileToReadFrom = inputPath.getAbsolutePath();
			OnBorderCodeGenerator generator = new OnBorderCodeGenerator(fileToReadFrom, writer);
			generator.runWithStaticIntance(constraint1, constraint2);
		} catch (Exception e) {
			logger.log(Level.SEVERE, Utils.threadName() + " Failed to generate on border code", e);
		}

		if (Configuration.IsInDeubbungMode) {
			logger.info("\n\nOnBorderFile for: " + onBorderFileName + "\n" + Utils.readFile(onBorderFile.getAbsolutePath()) + "\n\n");
		}
		
		logger.info("OnBorder Code generated...running Alloy*");

		// Run on-border instances through the higher order solver (alloy*)
		success = true;
		try {
			A4CommandExecuter.get().executeHola(reporter, this.tmpPath.getAbsolutePath(),
					OnBorderCodeGenerator.FIND_MARGINAL_INSTANCES_COMMAND, onBorderFile.getAbsolutePath());
		} catch (Exception e) {
			success = false;
			e.printStackTrace();
			logger.severe(
					"[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy* on file: " + inputPath);
			if (Configuration.IsInDeubbungMode) {
				logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
			}
		}

		if (Configuration.IsInDeubbungMode) {
			logger.info("Alloy* Complete on : " + onBorderFile + ". Status: " + (success ? "Successful":"Failed"));
		}

		// Write generated A4Solution to outputPath as xml
		A4Solution soln = reporter.getA4Solution();
		if (success && outputPath != null && outputPath.exists()) {
			if (soln != null) {
				try {
					soln.writeXML(outputPath.getAbsolutePath());
					logger.info("Final A4Solution acquired from Alloy* written to output file");
				} catch (Exception e) {
					e.printStackTrace();
					logger.severe("[" + Thread.currentThread().getName() + "] "
							+ " Failed to write alloy* solution to XML file: " + outputPath);
					if (Configuration.IsInDeubbungMode) {
						logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
					}
				}
			}
		}

		onBorderFile.deleteOnExit();
		return soln;
	}

	public static BordeauxEngine executeAlloy(A4Reporter reporter, File inputPath, Command command) {

		try {
			A4CommandExecuter.get().runAlloy(inputPath.getAbsolutePath(), reporter, command.label);
			A4Solution initialSoln = reporter.getA4Solution();
			return new BordeauxEngine(inputPath, command, initialSoln);
		} catch (Exception e) {
			e.printStackTrace();
			logger.severe(
					"[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy on file: " + inputPath);
			if (Configuration.IsInDeubbungMode) {
				logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
			}
			
			throw new RuntimeException();
		}
	}*/
	
	private A4Solution func(A4Reporter reporter, File inputPath, String constraint1, String constraint2) {
		
		try {
			Util.writeAll(this.onBorderFile.getAbsolutePath(), "");
		} catch (Err e1) {
			e1.printStackTrace();
		}
		
		this.generator.run(constraint1, constraint2);
		
		if(Configuration.IsInDeubbungMode) {
			System.out.println(Utils.readFile(this.onBorderFile.getAbsolutePath()));
			logger.info("OnBorder Code generated...running Alloy*");
		}

		// Run on-border instances through the higher order solver (alloy*)
		boolean success = true;
		A4Solution result = null;
		try {
			String commandName = OnBorderCodeGenerator.FIND_MARGINAL_INSTANCES_COMMAND;
			MultiValuedMap<String, A4Solution> map = A4CommandExecuter.get().executeHola(reporter, this.tmpPath.getAbsolutePath(),
					commandName, onBorderFile.getAbsolutePath());
					Collection<A4Solution> sols =map.get(commandName);
			
			if(reporter.equals(A4Reporter.NOP)) {
				Iterator<A4Solution> itr = sols.iterator();
				result = itr.hasNext() ? itr.next() : null;
			} else {
				result = reporter.getA4Solution();
			}
		} catch (Exception e) {
			success = false;
			e.printStackTrace();
			logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy* on file: " + inputPath, e);
		}

		if (Configuration.IsInDeubbungMode) {
			logger.info("Alloy* Complete on : " + onBorderFile + ". Status: " + (success ? "Successful":"Failed"));
		}

		return result;
	}
	
	/**
	 * Increments 
	 * @return
	 * @throws Err
	 */
	public A4Solution nextSolution() throws Err {
		
		A4Solution next = this.initialSolution.next();
		
		if(next != null) {
			initSolution(next);
		}
		
		return next;
	}

	private void initSolution(A4Solution sol) {
		this.initialSolution = sol;
		this.previousHit = sol;
		
		this.createCodeGenerator(inputPath, command);
		this.currentMiss = this.generator.getForumlaContstraints();
		this.currentHit = "";
	}
	
	public A4Solution nextNearMiss(A4Reporter rep) {

		if(!firstNearMiss && this.previousMiss == null) return null;
		this.firstNearMiss = false; 
		
		String constraint1 = ExtractorUtils.convertA4SolutionToAlloySyntax(this.previousHit, true);
		
		String prevMissStr = "";
		if(this.previousMiss != null) {
			prevMissStr = ExtractorUtils.convertA4SolutionToAlloySyntax(this.previousMiss, true);
		}
		
		currentMiss = Utils.and(currentMiss, prevMissStr);
		String constraint2 = Utils.not(currentMiss);
		
		this.previousMiss = this.func(rep, this.inputPath, constraint1, constraint2);		
		return this.previousMiss;
	}
	
	public A4Solution nextNearHit(A4Reporter rep) {

		String constraint1 = ExtractorUtils.convertA4SolutionToAlloySyntax(this.previousMiss, true);
		
		if(firstNearHit) {

			String constraint2 = this.generator.getForumlaContstraints();
			this.previousHit = this.func(rep, this.inputPath, constraint1, constraint2);
			currentHit = ExtractorUtils.convertA4SolutionToAlloySyntax(this.previousHit, true);
			firstNearHit = false;
			return this.previousHit;
		}
		
		String prevHitStr = "";
		if(this.previousHit != null) {
			prevHitStr = ExtractorUtils.convertA4SolutionToAlloySyntax(this.previousHit, true);
		}
		
		currentHit = Utils.and(currentHit, prevHitStr);
		String constraint2 = currentHit;
		
		this.previousHit = this.func(rep, this.inputPath, constraint1, constraint2);
		return this.previousHit;
	}
}
