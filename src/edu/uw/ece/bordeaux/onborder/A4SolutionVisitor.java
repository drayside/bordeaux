package edu.uw.ece.bordeaux.onborder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.uw.ece.bordeaux.onborder.SigFieldWrapper.FieldInfo;
import edu.uw.ece.bordeaux.util.ExtractorUtils;
import edu.mit.csail.sdg.alloy4compiler.ast.Module; 

public class A4SolutionVisitor {

	public static List<SigFieldWrapper> getSigs(Module sol) throws Err {

		List<SigFieldWrapper> sigs = new ArrayList<>();
		for (Sig sig : sol.getAllReachableSigs()) {

			if(ExtractorUtils.sigToBeIgnored(sig)) continue;
			
			String sigName = sig.shortLabel();
			SigFieldWrapper sigWrapper = new SigFieldWrapper(sigName, sig.decl.expr.mult(), sig.isAbstract != null);
			
			for (Decl decl : sig.getFieldDecls()) {

				for(ExprHasName field : decl.names) {
					String name = field.label;
//					String label = ExtractorUtils.getCamelCase(sigWrapper.getSig()) + "_" + name;
					String label = ExtractorUtils.getLocalFieldName(name, sigWrapper.getSig());
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
	
}
