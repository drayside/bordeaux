package edu.uw.ece.bordeaux.tests;

import java.io.File;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Err;
import edu.uw.ece.bordeaux.onborder.OnBorderCodeGenerator;

public class OnBorderCodeGeneratorTest {

    @Test
    public void testCodeGeneratorForCourses() throws Err {
     
        String file = "./models/bordeaux/courses.als";        
        String commandName = "showSuccesfullPrograms";
        
        OnBorderCodeGenerator generator = new OnBorderCodeGenerator(file);
        generator.run(new File("tmp/tests/"), "", commandName);
        
    }
    
    @Test
    public void testCodeGeneratorForSll() throws Err {

        String file = "./models/bordeaux/sll.als";        
        String commandName = "SinglyLinkedLists";
        
        OnBorderCodeGenerator generator = new OnBorderCodeGenerator(file);
        generator.run(new File("tmp/tests/"), "", commandName);
        
    }
}
