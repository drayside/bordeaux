package edu.uw.ece.bordeaux.engine;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.UUID;
import java.util.logging.Level;
import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.Configuration;
import edu.uw.ece.bordeaux.HolaReporter;
import edu.uw.ece.bordeaux.onborder.OnBorderCodeGenerator;
import edu.uw.ece.bordeaux.util.Utils;

public final class BordeauxEngine {

	private final static Logger logger = Logger
			.getLogger(BordeauxEngine.class.getName() + "--" + Thread.currentThread().getName());
	private final File tmpPath = new File("./tmp/");

	private static BordeauxEngine instance = new BordeauxEngine();

	private BordeauxEngine() {
	}

	public static BordeauxEngine get() {
		return instance;
	}

	 public void getBorderInstances(File inputPath, String...predNames) {
	
		 String inputFileName = Utils.getFileName(inputPath.getAbsolutePath());
		 File outputPath = new File(this.tmpPath.getAbsolutePath(), inputFileName
		 + "-" + UUID.randomUUID().hashCode());
		 this.getBorderInstances(inputPath, outputPath, predNames);
		 outputPath.delete();
	 }


	public void getBorderInstances(File inputPath, File outputPath, String... predNames) {

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
		OnBorderCodeGenerator generator = new OnBorderCodeGenerator(fileToGenerate, writer);
		generator.run(predNames);

		if (Configuration.IsInDeubbungMode) {
			logger.info("OnBorderFile for: " + fileName + "\n" + Utils.readFile(onBorderFile.getAbsolutePath()));
		}

		// Run on-border instances through the higher order solver (alloy*)
		boolean success = true;
		HolaReporter reporter = new HolaReporter();
		try {
			A4CommandExecuter.getInstance().executeHola(reporter, this.tmpPath.getAbsolutePath(),
					onBorderFile.getAbsolutePath());
		} catch (Err e) {
			success = false;
			e.printStackTrace();
			logger.severe(
					"[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy* on file: " + inputPath);
			if (Configuration.IsInDeubbungMode) {
				logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
			}
		}

		// Write generated A4Solution to outputPath as xml
		if (success) {
			if (reporter.getA4Solution().isPresent()) {
				A4Solution soln = reporter.getA4Solution().get();
				try {
					soln.writeXML(outputPath.getAbsolutePath());
				} catch (Err e) {
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
	}

	public void getBorderInstancesFromStaticInstance(File inputPath, File outputPath, String command, String intendedPred) {

		// First generate static A4olution from input path
		boolean success = true;
		HolaReporter reporter = new HolaReporter();
		try {
			A4CommandExecuter.getInstance().runAlloy(inputPath.getAbsolutePath(), reporter, command);
		} catch (Err e) {
			success = false;
			e.printStackTrace();
			logger.severe(
					"[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy on file: " + inputPath);
			if (Configuration.IsInDeubbungMode) {
				logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
			}
		}

		A4Solution staticSoln = null;
		if (success && reporter.getA4Solution().isPresent()) {
			staticSoln = reporter.getA4Solution().get();
		}

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
		OnBorderCodeGenerator generator = new OnBorderCodeGenerator(fileToGenerate, writer);
		generator.runWithStaticIntance(staticSoln, intendedPred);

		if (Configuration.IsInDeubbungMode) {
			logger.info("OnBorderFile for: " + fileName + "\n" + Utils.readFile(onBorderFile.getAbsolutePath()));
		}

		// Run on-border instances through the higher order solver (alloy*)
		success = true;
		reporter.resetSolution();
		try {
			A4CommandExecuter.getInstance().executeHola(reporter, this.tmpPath.getAbsolutePath(),
					onBorderFile.getAbsolutePath());
		} catch (Err e) {
			success = false;
			e.printStackTrace();
			logger.severe(
					"[" + Thread.currentThread().getName() + "] " + " Failed to execute alloy* on file: " + inputPath);
			if (Configuration.IsInDeubbungMode) {
				logger.log(Level.SEVERE, "[" + Thread.currentThread().getName() + "] " + e.getMessage(), e);
			}
		}

		// Write generated A4Solution to outputPath as xml
		if (success) {
			if (reporter.getA4Solution().isPresent()) {
				A4Solution soln = reporter.getA4Solution().get();
				try {
					soln.writeXML(outputPath.getAbsolutePath());
				} catch (Err e) {
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
	}

}
