package edu.uw.ece.bordeaux.tests;

import java.io.File;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.uw.ece.bordeaux.onborder.OnBorderCodeGenerator;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;

public class OnBorderCodeGeneratorTest {

    @Test
    public void testCodeGeneratorForCourses() throws Err {
     
        String file = "./models/bordeaux/courses.als";        
        Command command = ExtractorUtils.getCommandFromNamePainfully(file, "showSuccesfullPrograms");
        
        OnBorderCodeGenerator generator = new OnBorderCodeGenerator(file, command);
        generator.run("", Utils.not(generator.getForumlaContstraints()));
    }
    
    @Test
    public void testCodeGeneratorForSll() throws Err {

        String file = "./models/bordeaux/sll.als";    
        Command command = ExtractorUtils.getCommandFromNamePainfully(file, "SinglyLinkedLists");
        
        OnBorderCodeGenerator generator = new OnBorderCodeGenerator(file, command);
        generator.run("", Utils.not(generator.getForumlaContstraints()));
        
    }
}
