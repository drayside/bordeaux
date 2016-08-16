package edu.uw.ece.bordeaux.onborder;

import java.util.ArrayList;
import java.util.List;

import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;

public class SigFieldWrapper {

	private final String sig;
	private final String multString;
	private final boolean isAbstract;
	private final List<FieldInfo> fields;

	public SigFieldWrapper() {
		this.sig = null;
		this.multString = null;
		this.isAbstract = false;
		this.fields = new ArrayList<>();
	}
	
	public SigFieldWrapper(final String sig, final ExprUnary.Op mult, final boolean isAbstract) {
		this.sig = sig;
		this.multString = mult.toString().split("\\s")[0] + " ";
		this.isAbstract = isAbstract;
		this.fields = new ArrayList<>();
	}
	
	public SigFieldWrapper(final String sig, final ExprUnary.Op mult, final boolean isAbstract, List<FieldInfo> fields) {
		this(sig, mult, isAbstract);
		if(fields != null) this.fields.addAll(fields);
	}
	
	public String getSig() {
		return sig;
	}

	public String getMultString() {
		return this.multString;
	}
	
	public boolean isAbstract() {
		return this.isAbstract;
	}
	
	public List<FieldInfo> getFields() {
		return fields;
	}
	
	public void addField(FieldInfo info) {
		this.fields.add(info);
	}
	
	public class FieldInfo {
		
		private String name;
		private String label;
		private String type;
		private String[] typeComponents;
		
		public FieldInfo(String name, String label, String type, String[] typeComponents) {
			this.name = name;
			this.label = label;
			this.type = type;
			this.typeComponents = typeComponents;
		}
		
		public String getName() {
			return name;
		}
		
		public String getLabel() {
			return label;
		}
		
		public String getType() {
			return type;
		}

		public String[] getTypeComponents() {
			return typeComponents;
		}
		
	}
	
}
