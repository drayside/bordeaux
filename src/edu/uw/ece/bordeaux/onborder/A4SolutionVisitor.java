package edu.uw.ece.bordeaux.onborder;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.uw.ece.bordeaux.onborder.SigFieldWrapper.FieldInfo;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.mit.csail.sdg.alloy4compiler.ast.Module; 

public class A4SolutionVisitor {

	public static List<SigFieldWrapper> getSigs(Module sol) throws Err {

		List<SigFieldWrapper> sigs = new ArrayList<>();
		for (Sig sig : sol.getAllReachableSigs()) {

			if(ExtractorUtils.sigToBeIgnored(sig)) continue;
			
			String sigType = sig.label.replace("this/", "");
			SigFieldWrapper sigWrapper = new SigFieldWrapper(sigType);
			
			for (Decl decl : sig.getFieldDecls()) {

				for(ExprHasName field : decl.names) {
					String name = field.label;
					String label = getCamelCase(sigWrapper.getSig()) + "_" + name;
					String type = field.type().toString().replaceAll("[{\\[\\]}]", "").replace("this/", "");
					String[] typeParts = type.split("->");
					
					FieldInfo info = sigWrapper.new FieldInfo(name, label, type, typeParts);
					sigWrapper.addField(info);
				}				
			}
			
			sigs.add(sigWrapper);
		}
		
		return sigs;
	}
	
	private static String getCamelCase(String in) {
		if(in == null || in.isEmpty()) return in;
		
		boolean lenG1 = in.length() > 1;
		return Character.toLowerCase(in.charAt(0)) + (lenG1 ? in.substring(1) : "");
	}
	
}
