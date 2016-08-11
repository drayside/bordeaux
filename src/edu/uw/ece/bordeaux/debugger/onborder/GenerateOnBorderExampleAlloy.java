/**
 * 
 */
package edu.uw.ece.bordeaux.debugger.onborder;

import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.uw.ece.bordeaux.debugger.exec.A4CommandExecuter;
import kodkod.ast.Formula;
import kodkod.util.nodes.PrettyPrinter;

/**
 * This class makes Alloy* code generating on border examples
 * @author vajih
 *
 */
public class GenerateOnBorderExampleAlloy {

	
	
	/**
	 * @param args
	 * @throws Err 
	 */
	public static void main(String[] args) throws Err {
		final String pathToTmpFile = "testing_declrative_constraint.als";
		final String alloyContent = "sig A{}\n sig B{r: set A }\n pred p[]{ } run p";
		Util.writeAll(pathToTmpFile, alloyContent);
		List<Formula> formulas = A4CommandExecuter.getInstance().translateAlloy2KK(pathToTmpFile,
																															A4Reporter.NOP, 
																															"p");
		
		for(Formula formula: formulas){
			String s = formula.toString();
					System.out.println(s);
		}
		
		
		
	}

}
