package edu.uw.ece.bordeaux.debugger.onborder;

import java.io.File;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Err;

public class OnBorderCodeGeneratorTest {

    @Test
    public void testCodeGenerator() throws Err {

        String alloy4Home = "./";

        String fileName = "linked_list.als";
//        String directory = alloy4Home + "/models/debugger/min_dist/";
      String directory = alloy4Home + "/models/examples/toys/";
        fileName = "birthday.als";
//        fileName = "ceilingsAndFloors.als";
//        fileName = "railway.als";
//        fileName = "bare_linked_list.als";
        
        String file = directory + fileName;
        
        System.out.println("\n\nGenerating for " + new File(file).getAbsolutePath() + "\n\n");
        OnBorderCodeGenerator generator = new OnBorderCodeGenerator(file);
        generator.run();
        
    }
}
