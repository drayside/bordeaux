package edu.uw.ece.bordeaux.onborder;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.collections4.MultiValuedMap;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.onborder.SigFieldWrapper.FieldInfo;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;
import kodkod.ast.Formula;

public class OnBorderCodeGenerator {
    
    private static final String RUN = "\npred p[] {}\nrun p";
    public static final String FIND_MARGINAL_INSTANCES_COMMAND = "findMarginalInstances";
    
    private PrintWriter out;
    private boolean useStaticInstance;
    private String indent;
    private Module module;
    private String sigDeclaration;
    private List<SigFieldWrapper> sigs;
    
    private OnBorderCodeGenerator() {
        this.indent = "";
        this.out = new PrintWriter(System.out);
    }
    
    /**
     * Creates a new instance of {@link OnBorderCodeGenerator}.
     * 
     * The default {@link PrintWriter} used is System.out. Use the
     * OnBorderCodeGenerator(Module, PrintWriter) to specify a different
     * {@link PrintWriter}.
     * 
     * @param module
     *            - The Alloy {@link Module} to be used.
     */
    public OnBorderCodeGenerator(Module module) {
        this();
        this.module = module;
        
        try {
            this.sigDeclaration = Field2ConstraintMapper.getSigDeclarationViaPos(this.module);
            this.sigs = A4SolutionVisitor.getSigs(module);
        }
        catch (Err e) {
            e.printStackTrace();
        }
    }
    
    /**
     * Creates a new instance of {@link OnBorderCodeGenerator}.
     * 
     * @param module
     *            - The Alloy {@link Module} to be used.
     * @param writer
     *            - Specifies the {@link PrintWriter} to be used.
     */
    public OnBorderCodeGenerator(Module module, PrintWriter writer) {
        this(module);
        this.out = writer;
    }
    
    /**
     * Creates a new instance of {@link OnBorderCodeGenerator}.
     * 
     * The default {@link PrintWriter} used is System.out. Use the
     * OnBorderCodeGenerator(String, PrintWriter) to specify a different
     * {@link PrintWriter}.
     * 
     * @param filepath
     *            - The path to the alloy file to be used.
     */
    public OnBorderCodeGenerator(String filepath) {
        
        this();
        
        try {
            this.module = A4CommandExecuter.get().parse(filepath, A4Reporter.NOP);
        }
        catch (Err e) {
            e.printStackTrace();
        }
        
        try {
            this.sigDeclaration = Field2ConstraintMapper.getSigDeclarationViaPos(this.module);
            this.sigs = A4SolutionVisitor.getSigs(module);
        }
        catch (Err e) {
            e.printStackTrace();
        }
    }
    
    /**
     * Creates a new instance of {@link OnBorderCodeGenerator}.
     * 
     * @param filepath
     *            - The path to the alloy file to be used.
     * @param writer
     *            - Specifies the {@link PrintWriter} to be used.
     */
    public OnBorderCodeGenerator(String filepath, PrintWriter writer) {
        this(filepath);
        this.out = writer;
    }
    
    /**
     * Runs the generator using the given constraints as valid instances
     * @param constraints
     */
    public void run(String...constraints) {
            	
        try {
            this.generateSigs(this.out);
        	this.generatePredicates(this.out);
            this.generateDeltas(this.out);
            this.generateIsInstance(this.out, constraints);
            this.generateFindMarginalInstances(out, constraints);
            
            ln();
            println("run " + OnBorderCodeGenerator.FIND_MARGINAL_INSTANCES_COMMAND);
        }
        catch (Err e) {
            e.printStackTrace();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        
        this.out.flush();
    }
    
    /**
     * Runs the generator using the specified {@link A4Solution} as a static instance the the given predName as the intended instance.
     * @param staticSoln
     * @param pred
     */
    public void runWithStaticIntance(String...constraints) {

    	this.useStaticInstance = true;
    	this.run(constraints);
    }
    
    private void generateSigs(PrintWriter out) throws Err {
        
        this.out = out;
        ln();
        
		String decl = this.sigDeclaration.replaceAll("(one|lone|some)", "set");
        println(decl);        
    }
    
    private void generatePredicates(PrintWriter out) {
    	    	
    	this.out = out;
    	
    	List<String> preds = Field2ConstraintMapper.getAllFuncDeclarationViaPos(this.module);
    	for(String impl : preds) {
    		ln();
			println(impl);
		}
    }
    
    private void generateDeltas(PrintWriter out) {
        
        this.out = out;
        
        for (SigFieldWrapper sigWrap : this.sigs) {
            
        	if(sigWrap.isAbstract()) continue;
        	
            ln();
            
            String sigName = this.getCamelCase(sigWrap.getSig());
            String s1 = String.format("%s: set %s", sigName, sigWrap.getSig());
            String s2 = String.format("%s': set %s", sigName, sigWrap.getSig());
            String s3 = String.format("%s'': set %s", sigName, sigWrap.getSig());
            
            println("pred delta%s[%s, %s, %s] {", this.getPascalCase(sigWrap.getSig()), s1, s2, s3);
            indent();
            println("%1$s != %1$s' implies (%1$s'' = %1$s' - %1$s and %1$s'' + %1$s = %1$s') else no %1$s''", sigName);
            outdent();
            println("}");
            
            for (FieldInfo field : sigWrap.getFields()) {
                ln();
                s1 = String.format("%s: %s", field.getLabel(), field.getType());
                s2 = String.format("%s': %s", field.getLabel(), field.getType());
                s3 = String.format("%s'': %s", field.getLabel(), field.getType());
                
                println("pred delta%s[%s, %s, %s] {", this.getPascalCase(field.getLabel()), s1, s2, s3);
                indent();
                println("%1$s != %1$s' implies (%1$s'' = %1$s' - %1$s and %1$s'' + %1$s = %1$s') else no %1$s''", field.getLabel());
                outdent();
                println("}");
            }
            
        }
        
    }
    
    private void generateFindMarginalInstances(PrintWriter out, String...contraints) {
        
        this.out = out;
        ln();

        StringBuilder quantifier = new StringBuilder();
        StringBuilder constr1InstanceCall = new StringBuilder();
        StringBuilder constr2InstanceCall = new StringBuilder();
        StringBuilder deltaCalls = new StringBuilder();
        StringBuilder sigmaCall = new StringBuilder();
        
        StringBuilder quantifier_1 = new StringBuilder();
        StringBuilder constr1InstanceCall_1 = new StringBuilder();
        StringBuilder constr2InstanceCall_1 = new StringBuilder();
        StringBuilder deltaCalls_1 = new StringBuilder();
        StringBuilder sigmaCall_1 = new StringBuilder();
        
        int sigmaParamLength = 0;
        println("pred findMarginalInstances[] {");
        indent();
        print(indent);
        
        Iterator<SigFieldWrapper> sigItr = this.sigs.iterator();
        while (sigItr.hasNext()) {
            
            SigFieldWrapper sigWrap = sigItr.next();
            
            if(sigWrap.isAbstract()) continue;
            
            String sigName = this.getCamelCase(sigWrap.getSig());
            quantifier.append(String.format(", %1$s, %1$s', %1$s'': set %2$s", sigName, sigWrap.getSig()));
            quantifier_1.append(String.format(", %1$s1, %1$s1', %1$s1'': set %2$s", sigName, sigWrap.getSig()));
            
            constr1InstanceCall.append(", " + sigName);
            constr2InstanceCall.append(", " + sigName + "'");
            sigmaCall.append(", #" + sigName + "''");
            deltaCalls.append(String.format("and delta%1$s[%2$s, %2$s', %2$s'']\n", this.getPascalCase(sigWrap.getSig()), sigName));
            
            constr1InstanceCall_1.append(", " + sigName + "1");
            constr2InstanceCall_1.append(", " + sigName + "1'");
            sigmaCall_1.append(", #" + sigName + "1''");
            deltaCalls_1.append(String.format("and delta%1$s[%2$s1, %2$s1', %2$s1'']\n", this.getPascalCase(sigWrap.getSig()), sigName));
            
            sigmaParamLength++;
//            if (sigItr.hasNext()) {
//                print(", ");
//                predAInstanceCall.append(", ");
//                predBInstanceCall.append(", ");
//                sigmaCall.append(", ");
//                
//                quantifier_1.append(", ");
//                predAInstanceCall_1.append(", ");
//                predBInstanceCall_1.append(", ");
//                sigmaCall_1.append(", ");
//            }
            
            Iterator<FieldInfo> itr = sigWrap.getFields().iterator();
            while (itr.hasNext()) {
                
                FieldInfo field = itr.next();
                quantifier.append(String.format(", %1$s, %1$s', %1$s'': set %2$s", field.getLabel(), field.getType()));
                quantifier_1.append(String.format(", %1$s1, %1$s1', %1$s1'': set %2$s", field.getLabel(), field.getType()));
                
                constr1InstanceCall.append(", " + field.getLabel());
                constr2InstanceCall.append(", " + field.getLabel() + "'");
                sigmaCall.append(", #" + field.getLabel() + "''");
                deltaCalls.append(String.format("and delta%1$s[%2$s, %2$s', %2$s'']\n", this.getPascalCase(field.getLabel()), field.getLabel()));
                
                constr1InstanceCall_1.append(", " + field.getLabel() + "1");
                constr2InstanceCall_1.append(", " + field.getLabel() + "1'");
                sigmaCall_1.append(", #" + field.getLabel() + "1''");
                deltaCalls_1.append(String.format("and delta%1$s[%2$s1, %2$s1', %2$s1'']\n", this.getPascalCase(field.getLabel()), field.getLabel()));
                
                sigmaParamLength++;
//                if (itr.hasNext()) {
//                    print(", ");
//                    predAInstanceCall.append(", ");
//                    predBInstanceCall.append(", ");
//                    sigmaCall.append(", ");
//                    
//                    quantifier_1.append(", ");
//                    predAInstanceCall_1.append(", ");
//                    predBInstanceCall_1.append(", ");
//                    sigmaCall_1.append(", ");
//                }
            }
            
        }
        
        quantifier.delete(0, 2); 
        quantifier_1.delete(0, 2);
        constr1InstanceCall.delete(0, 2);
        constr1InstanceCall_1.delete(0, 2);
        constr2InstanceCall.delete(0, 2);
        constr2InstanceCall_1.delete(0, 2);
        sigmaCall.delete(0, 2);     
        sigmaCall_1.delete(0, 2);
        
        String constr1;
        String constr2;
        if(this.useStaticInstance) {        	
        	constr1 = "STATIC";
        	constr2 = "isINTENDED";
        } else {
        	constr1 = contraints != null && contraints.length > 0 && !contraints[0].isEmpty()? contraints[0].replaceAll("\\s+", "_").toUpperCase() : "";
        	constr2 = contraints != null && contraints.length > 1 && !contraints[1].isEmpty() ? "is" + contraints[1].replaceAll("\\s+", "_").toUpperCase() : "not is";
       
	        // say "not isPREDAInstance" if predA exists
	        if(constr2.equals("not is") && !constr1.equals("")) {
	        	constr2 += constr1;
	        }
        }
        
        // Finish outer quantifier
        print("some %s | {", quantifier);
        ln();
        indent();
        indent();
        println("(");
        println("is%sInstance[%s]", constr1, constr1InstanceCall);
        println("and %sInstance[%s]", constr2, constr2InstanceCall);
        println("%s)", deltaCalls.toString().replaceAll("\n", "\n" + indent));
        
        outdent();
        println("and");
        indent();
        
        // Print inner quantifier
        println("all %s | {", quantifier_1);
        indent();
        indent();
        println("(");
        println("is%sInstance[%s]", constr1, constr1InstanceCall_1);
        println("and %sInstance[%s]", constr2, constr2InstanceCall_1);
        println("%s)", deltaCalls_1.toString().replaceAll("\n", "\n" + indent));
        
        outdent();
        println("implies");
        indent();
        
        println("(");
        println("sigma[%s] <= sigma[%s]", sigmaCall.toString(), sigmaCall_1.toString());
        println(")");
        
        // Close inner quantifier
        outdent();
        outdent();
        println("}");
        
        // Close outer quantifier
        outdent();
        outdent();
        println("}");
        
        // Close predicate
        outdent();
        println("}");
        
        this.generateSigmaFunction(sigmaParamLength, out);
    }
    
    private void generateIsInstance(PrintWriter out, String...contraints) throws Err, IOException {
        
        this.out = out;
        
        // Generate arguments passed into predicates
        StringBuilder args = new StringBuilder();
        StringBuilder params = new StringBuilder();
        for (SigFieldWrapper sigWrap : this.sigs) {
            
        	if(sigWrap.isAbstract()) continue;
        	
        	String sigName = this.getCamelCase(sigWrap.getSig());
            args.append(String.format(", %s", sigName));
            params.append(String.format(", %s: set %s", sigName, sigWrap.getSig()));
            
            for (FieldInfo field : sigWrap.getFields()) {
                args.append(String.format(", %s", field.getLabel()));
                params.append(String.format(", %s: %s", field.getLabel(), field.getType()));
            }
        }
        
        // Trim initial comma and space
        args.delete(0, 2);
        params.delete(0, 2);
        
        String parameters = params.toString();
        String arguments = args.toString();
        this.generateStructuralConstraint(parameters, out);
        this.generateIncludeInstance(parameters, out);
        
        ln();
        println("pred isInstance [%s] {", parameters);
        indent();
        println("includeInstance[%s]", arguments);
        outdent();
        println("}");
        
        generateConstrainedInstances(parameters, arguments, out, contraints);
    }
    
    private void generateStructuralConstraint(String params, PrintWriter out) throws Err, IOException {
        
        this.out = out;
        ln();
        println("pred structuralConstraints [%s] {", params);
        // println("pred structuralConstraints [] {");
        indent();
        
        // Create temp file for extracted signatures
        File file = File.createTempFile("sig", ".als");
        String sigs = this.sigDeclaration + OnBorderCodeGenerator.RUN;
        Util.writeAll(file.getAbsolutePath(), sigs);
        
        // Translate signatures to KodKod
        List<Formula> formulas = A4CommandExecuter.get().translateAlloy2KK(file.getAbsolutePath(), A4Reporter.NOP, "p");
                
        // Use Structural formulas from KodKod and make them pretty
        for (Formula f : formulas) {
            
            String constraint = f.toString();
            
        	// Start by replacing " remainder" with empty string
            constraint = constraint.replace(" remainder", "");
        	
            // Replace all this.SigName.field with sigName_field 
            Matcher m = Pattern.compile("this\\/([A-Za-z])((\\w)*)\\.((\\w)*)").matcher(constraint);
            StringBuffer sb = new StringBuffer();
                        
            // Replace each occurrence
            while (m.find()) {
                m.appendReplacement(sb, String.format("%s%s_%s", m.group(1).toLowerCase(), m.group(2), m.group(4)));
            }
            
            m.appendTail(sb);
            constraint = sb.toString();
            
            // Replace remaining this/SigName with sigNane            
            m = Pattern.compile("this\\/([A-Za-z])((\\w)*)").matcher(constraint);
            sb = new StringBuffer();

            // Replace each occurrence
            while (m.find()) {
                m.appendReplacement(sb, String.format("%s%s", m.group(1).toLowerCase(), m.group(2)));
            }
            
            m.appendTail(sb);
            constraint = sb.toString();

            println(constraint);
        }

        for (SigFieldWrapper sig : this.sigs) {
        	
        	String mult = sig.getMultString();
        	if(sig.isAbstract() || mult.isEmpty()) continue;
        	
        	println("%s %s", mult, this.getCamelCase(sig.getSig()));
        }
        
        outdent();
        println("}");
        
        file.delete();
    }
    
    private void generateIncludeInstance(String params, PrintWriter out) {
        
        this.out = out;
        ln();
        println("pred includeInstance [%s] {", params);
        indent();
        
        for (SigFieldWrapper sig : this.sigs) {
            
            for (FieldInfo field : sig.getFields()) {
                
                String label = field.getLabel();
                String[] typeParts = field.getTypeComponents();
                for (int i = 0; i < typeParts.length; i++) {
                    
                    String join = label;
                    for (int m = 0; m < i; m++) {
                        join = "(" + typeParts[m] + "." + join + ")";
                    }
                    
                    for (int n = typeParts.length - 1; n > i; n--) {
                        join = "(" + join + "." + typeParts[n] + ")";
                    }
                    
                    println("%s in %s", join, typeParts[i]);
                }
                
            }
            
        }
        
        outdent();
        println("}");
    }

    private void generateConstrainedInstances(String params, String args, PrintWriter out, String...contraints) {

    	if(contraints == null) return;

        this.out = out;
    	if(this.useStaticInstance) {

        	ln();
	        println("pred isSTATICInstance [%s] {", params);
	        indent();
	        println("isInstance[%s]", args);
	        println("structuralConstraints[%s]", args);
	        println("%s", contraints[0]);
	        outdent();
	        println("}");

        	ln();
	        println("pred isINTENDEDInstance [%s] {", params);
	        indent();
	        println("isInstance[%s]", args);
	        println("not structuralConstraints[%s]", args);
	        println("%s", contraints[1]);
	        outdent();
	        println("}");
    		return;
    	}
    	
    	for(String constraint : contraints) {
    		
    		if(constraint == null || constraint.isEmpty()) continue;
    		
        	ln();
	        println("pred is%sInstance [%s] {", constraint.replaceAll("\\s+", "_").toUpperCase(), params);
	        indent();
	        println("isInstance[%s]", args);
	        println("%s", constraint);
	        outdent();
	        println("}");
    	}
    }
    
    private void generateSigmaFunction(final int paramLength, PrintWriter out) {
        
        this.out = out;
        
        ln();
        print("fun sigma [");
        for(int i = 1; i < paramLength; i++) {
            print("a%d, ", i);
        }
        
        println("a%d: Int] : Int {", paramLength);
        indent();
        print(indent);
        print("a1");
        for(int i = 2; i <= paramLength; i++) {
            print(".add[a%d]", i);
        }
        
        ln();
        outdent();
        println("}");
    }
    
    private String getPascalCase(String in) {
        
        if (in == null || in.isEmpty())
            return in;
            
        boolean lenG1 = in.length() > 1;
        return Character.toUpperCase(in.charAt(0)) + (lenG1 ? in.substring(1) : "");
    }
    
    private String getCamelCase(String in) {
        
        if (in == null || in.isEmpty())
            return in;
            
        boolean lenG1 = in.length() > 1;
        return Character.toLowerCase(in.charAt(0)) + (lenG1 ? in.substring(1) : "");
    }
    
    private void println(final String s, Object... args) {
        
        println(String.format(s, args));
    }
    
    private void println(final String s) {
        
        out.print(indent);
        out.println(s);
    }
    
    private void ln() {
        
        out.println();
    }
    
    private void print(final String s, Object... args) {
        
        print(String.format(s, args));
    }
    
    private void print(final String s) {
        
        out.print(s);
    }
    
    private void indent() {
        
        indent = indent + "    ";
    }
    
    private void outdent() {
        
        indent = indent.substring(0, indent.length() - 4);
    }
    
}
