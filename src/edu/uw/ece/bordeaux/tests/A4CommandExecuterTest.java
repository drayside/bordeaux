package edu.uw.ece.bordeaux.tests;

import java.io.File;
import static org.junit.Assert.*;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.HolaReporter;

public class A4CommandExecuterTest {


	@Test
	public void testHolaExecuter() {
		
		HolaReporter rep = new HolaReporter();
		String filename = "./tmp/bare_linked_list.hola--1288522771.als";
		try {
			A4CommandExecuter.get().executeHola(rep, new File("tmp/").getAbsolutePath(), "findMarginalInstances", filename);
		} catch (Err e) {
			e.printStackTrace();
		}
		
		A4Solution sol = rep.getA4Solution();
		assertNotNull("A4Solution is null", sol);
		
		System.out.println(sol.toString());
	}
}
