package edu.uw.ece.bordeaux.tests;

import java.io.File;

import org.junit.Test;

import edu.uw.ece.bordeaux.engine.BordeauxEngine;
import edu.uw.ece.bordeaux.util.Utils;

public class BordeauxEngineTest {

	public final String TMP_DIRECTORY = "./tmp/";
	public final String TOY_EXAMPLES_DIRECTORY = "./models/examples/toys/";
	public final String MIN_DIST_DIRECTORY = "./models/debugger/min_dist/";
	
	@Test
	public void testLinkedList() {
		
		BordeauxEngine engine = BordeauxEngine.get();
		
		String filename = "bare_linked_list.als";
		File inpath = new File(MIN_DIST_DIRECTORY, filename);
		
		File outpath = new File(TMP_DIRECTORY, "bare_linked_list.hola.als");
		engine.getBorderInstances(inpath, outpath, "hello", "hi");
		
		String output = Utils.readFile(outpath.getAbsolutePath());
		System.out.println(output);
		
		outpath.delete();
	}
}
