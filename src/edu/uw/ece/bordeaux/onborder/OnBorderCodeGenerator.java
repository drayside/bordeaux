package edu.uw.ece.bordeaux.onborder;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.collections4.MultiValuedMap;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.onborder.SigFieldWrapper.FieldInfo;
import edu.uw.ece.bordeaux.tests.Elaboration;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.uw.ece.bordeaux.util.Utils;
import kodkod.ast.Formula;

public class OnBorderCodeGenerator {
    
    private static final String RUN = "\npred p[] {}\nrun p";
    public static final String FIND_MARGINAL_INSTANCES_COMMAND = "findMarginalInstances";
    
    private PrintWriter out;
    private String indent;
    private Module module;
    private String sigDeclaration;
    private List<SigFieldWrapper> sigs;
	private String filepath;
	private String commandScope;
	private String includeConstraints;
	private String structuralConstraints;
	private String formulaConstraints;
	private Set<String> atomsToExclude;
    
    private OnBorderCodeGenerator() {
        this.indent = "";
        this.commandScope = "";
        this.out = new PrintWriter(System.out);
        this.atomsToExclude = new HashSet<>();
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
     * @param command - The command to execute
     * @throws Err 
     */
    public OnBorderCodeGenerator(String filepath, Command command) throws Err {
    	this();
        this.filepath = filepath;
        this.initModule(A4CommandExecuter.get().parse(filepath, A4Reporter.NOP));
        this.initialiseContraints(new File("tmp/"), command);
    }
    
    /**
     * Creates a new instance of {@link OnBorderCodeGenerator}.
     * 
     * @param filepath
     *            - The path to the alloy file to be used.
     * @param command - The command to execute
     * @param writer
     *            - Specifies the {@link PrintWriter} to be used.
     * @throws Err 
     */
    public OnBorderCodeGenerator(String filepath, Command command, PrintWriter writer) throws Err {
        this(filepath, command);
        this.out = writer;
    }
    
    /**
     * Creates a new instance of {@link OnBorderCodeGenerator}.
     * @param filepath - The path to the alloy file to be used.
     * @param command - The command to execute
     * @param relationsToExclude - The names of the sigs and relations to be excluded
     * @param writer - Specifies the {@link PrintWriter} to be used.
     * @throws Err
     */
    public OnBorderCodeGenerator(String filepath, Command command, Set<String> relationsToExclude, PrintWriter writer) throws Err {
        this(filepath, command, writer);
        if(relationsToExclude != null) this.atomsToExclude = relationsToExclude;
    }
    
    private void initModule(Module module) {

    	this.module = module;
        
        try {
            this.sigDeclaration = Field2ConstraintMapper.getSigDeclarationViaPos(this.module);
            this.sigs = A4SolutionVisitor.getSigs(module);
        }
        catch (Err e) {
            e.printStackTrace();
        }
    }
    
    private void initialiseContraints(File tmpFolder, Command command) {
    	
        Elaboration elaboration = new Elaboration();

        List<String> strs = elaboration.createBodyOfInstance_Structural_Constraint_Predicates(new File(filepath), tmpFolder, command.label);
        this.includeConstraints = strs.get(0).replace("\n", "\n\t");
        this.structuralConstraints = strs.get(1).replace("\n", "\n\t");
        this.formulaConstraints = strs.get(2).replace("\n", "\n\t");
        
        for(SigFieldWrapper sigWrap : this.sigs) {
        	
        	String sigRegex = "\\b(($)*" + sigWrap.getSig() + ")\\b";
        	String localSig = ExtractorUtils.getLocalSigName(sigWrap.getSig());
        	includeConstraints = includeConstraints.replaceAll(sigRegex, localSig);
        	structuralConstraints = structuralConstraints.replaceAll(sigRegex, localSig);
        	formulaConstraints = formulaConstraints.replaceAll(sigRegex, localSig);
        	
        	for(FieldInfo field : sigWrap.getFields()) {
        		
        		String fieldRegex = "\\b(($)*" + field.getName() + ")\\b";
        		String localField = field.getLabel();
        		includeConstraints = includeConstraints.replaceAll(fieldRegex, localField);
        		structuralConstraints = structuralConstraints.replaceAll(fieldRegex, localField);
        		formulaConstraints = formulaConstraints.replaceAll(fieldRegex, localField);
        	}
        }
        
        this.commandScope = ExtractorUtils.extractScopeFromCommand(command);
    }
    
    public String getForumlaContstraints() {
    	return this.formulaConstraints;
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
            println("run " + OnBorderCodeGenerator.FIND_MARGINAL_INSTANCES_COMMAND + " " + this.commandScope);
        }
        catch (Err e) {
            e.printStackTrace();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        
        this.out.flush();
    }
        
    private void generateSigs(PrintWriter out) throws Err {
        
        this.out = out;
        ln();
        
//		String decl = this.sigDeclaration.replaceAll("(one|lone|some)", "set");

    	Elaboration elaboration = new Elaboration();
    	String decl = elaboration.createAllSigsdeclaration(new File(filepath));
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

            String sigName = this.getCamelCase(sigWrap.getSig());
        	if(!this.atomsToExclude.contains(sigName) && !sigWrap.isAbstract()) {
        	
	            ln();
	            
	            String s1 = String.format("%s: set %s", sigName, sigWrap.getSig());
	            String s2 = String.format("%s': set %s", sigName, sigWrap.getSig());
	            String s3 = String.format("%s'': set %s", sigName, sigWrap.getSig());
	            
	            println("pred delta%s[%s, %s, %s] {", this.getPascalCase(sigWrap.getSig()), s1, s2, s3);
	            indent();
	            println("%1$s != %1$s' implies (%1$s'' = %1$s' - %1$s and %1$s'' + %1$s = %1$s') else no %1$s''", sigName);
	            outdent();
	            println("}");
        	}
        	
            for (FieldInfo field : sigWrap.getFields()) {
            	
            	if(this.atomsToExclude.contains(field.getLabel())) continue;
            	
                ln();
                String s1 = String.format("%s: %s", field.getLabel(), field.getType());
                String s2 = String.format("%s': %s", field.getLabel(), field.getType());
                String s3 = String.format("%s'': %s", field.getLabel(), field.getType());
                
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

            String sigName = this.getCamelCase(sigWrap.getSig());
            if(!this.atomsToExclude.contains(sigName) && !sigWrap.isAbstract()){
            
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
            }
            
            Iterator<FieldInfo> itr = sigWrap.getFields().iterator();
            while (itr.hasNext()) {
                
                FieldInfo field = itr.next();
                
            	if(this.atomsToExclude.contains(field.getLabel())) continue;
            	
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
        
        String constr1 = "C1";
        String constr2 = "C2";
        
        // Finish outer quantifier
        print("some %s | {", quantifier);
        ln();
        indent();
        indent();
        println("(");
        println("is%sInstance[%s]", constr1, constr1InstanceCall);
        println("and is%sInstance[%s]", constr2, constr2InstanceCall);
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
        println("and is%sInstance[%s]", constr2, constr2InstanceCall_1);
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
            
        	if(!sigWrap.isAbstract()) {        	
	        	String sigName = this.getCamelCase(sigWrap.getSig());
	            args.append(String.format(", %s", sigName));
	            params.append(String.format(", %s: set %s", sigName, sigWrap.getSig()));
        	}
        	
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

        if(this.structuralConstraints == null || this.structuralConstraints.isEmpty()) {
        	this.generateStructuralConstraintOld(params, out);
        	return;
        }
        
        this.out = out;
        ln();

        println("pred structuralConstraints [%s] {", params);
        indent();
        println(this.structuralConstraints);
        outdent();
        println("}");
    }
    
    private void generateIncludeInstance(String params, PrintWriter out) {

        if(this.includeConstraints == null || this.includeConstraints.isEmpty()) {
        	this.generateIncludeInstanceOld(params, out);
        	return;
        }
        
        
        this.out = out;
        ln();

        println("pred includeInstance [%s] {", params);
        indent();
        println(this.includeConstraints);
        outdent();
        println("}");
    }
    
    private void generateStructuralConstraintOld(String params, PrintWriter out) throws Err, IOException {
        
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
//                m.appendReplacement(sb, String.format("%s%s_%s", m.group(1).toLowerCase(), m.group(2), m.group(4)));
            	String sigName = m.group(1) + m.group(2);
            	String sep = "";
            	 for (SigFieldWrapper sigWrap : this.sigs) {
            		 if(sigWrap.getSig().equals(sigName)) {
            			 sep = ExtractorUtils.localNameSeparator(sigWrap.getSig());
            			 break;
            		 }
            	 }
            	 
            	 sigName = ExtractorUtils.getLocalSigName(sigName);
            	 m.appendReplacement(sb, String.format("%s_%s_%s", sigName, sep, m.group(4)));
            }
            
            m.appendTail(sb);
            constraint = sb.toString();
            
            // Replace remaining this/SigName with sigName            
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
    
    private void generateIncludeInstanceOld(String params, PrintWriter out) {
        
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
        ln();
        println("pred isC1Instance [%s] {", params);
        indent();
        println("isInstance[%s]", args);
        println("%s", contraints[0]);
        outdent();
        println("}");

    	ln();
        println("pred isC2Instance [%s] {", params);
        indent();
        println("isInstance[%s]", args);
        println("not structuralConstraints[%s]", args);
        println("%s", contraints[1]);
        outdent();
        println("}");
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
