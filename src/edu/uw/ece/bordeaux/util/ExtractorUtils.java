package edu.uw.ece.bordeaux.util;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import org.apache.commons.collections4.map.MultiKeyMap;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary.Op;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.Configuration;

/**
 * The class contains static methods that are helpful for extracting Alloy
 * entities.
 * 
 * @author vajih
 *
 */
public class ExtractorUtils {

	public static Command getCommandFromNamePainfully(String filepath, String commandName) {
		
		CompModule world = null;
		try {
			world = (CompModule) A4CommandExecuter.get().parse(filepath, A4Reporter.NOP);
		} catch (Err e) {
			e.printStackTrace();
			return null;
		}

		for (Command command : world.getAllCommands()) {
			if (command.label.equals(commandName)) {
				return command;
			}
		}
		
		return null;
	}
	
	public static String extractScopeFromCommand(final String srcFile, final String commandName) {
		
		CompModule module = null;
		try {
			module = (CompModule) A4CommandExecuter.get().parse(srcFile, A4Reporter.NOP);
		} catch (Err e) {
			e.printStackTrace();
		}
		
		if(module != null) {
			
			for(Command c : module.getAllCommands()) {
				if(c.label.equals(commandName)) {
					return extractScopeFromCommand(c);
				}
			}
		}
		
		return null;
	}
	
	/**
	 * Given a command, its scope is returned as String
	 * 
	 * @param command
	 * @return
	 */
	public static String extractScopeFromCommand(Command command) {
		boolean first = true;
		StringBuilder sb = new StringBuilder();
		if (command.overall >= 0 && ((command.intScope != null && command.intScope.bitwidth >= 0) || command.maxseq >= 0 || (command.scope != null && command.scope.size() > 0)))
			sb.append(" for ").append(command.overall).append(" but");
		else if (command.overall >= 0)
			sb.append(" for ").append(command.overall);
		else if ((command.intScope != null && command.intScope.bitwidth >= 0) || command.maxseq >= 0 || (command.scope != null && command.scope.size() > 0))
			sb.append(" for");
		if (command.intScope != null && command.intScope.bitwidth >= 0) {
			sb.append(" ").append(command.intScope.bitwidth).append(" int");
			first = false;
		}
		if (command.maxseq >= 0) {
			sb.append(first ? " " : ", ").append(command.maxseq).append(" seq");
			first = false;
		}
		if(command.scope != null) {
			for (CommandScope e : command.scope) {
				sb.append(first ? " " : ", ").append(e);
				first = false;
			}
		}
		if (command.expects >= 0)
			sb.append(" expect ").append(command.expects);
		return sb.toString();
	}

	public static boolean sigToBeIgnored(Sig sig) {
		
		return (sig.builtin || isOrdering(sig));
	}
	
	private static boolean isOrdering(Sig sig) {
		return sig.isPrivate != null && sig.isOne != null
				&& new File(sig.pos().filename).getName().equals("ordering.als");
	}

	private static boolean isSubSig(Sig sig) {
		return sig.isSubsig != null && sig instanceof Sig.PrimSig && !((Sig.PrimSig)sig).parent.builtin;
	}

	public static String getCamelCase(String in) {
		if(in == null || in.isEmpty()) return in;
		
		boolean lenG1 = in.length() > 1;
		return Character.toLowerCase(in.charAt(0)) + (lenG1 ? in.substring(1) : "");
	}
	
	public static String getLocalSigName(String sigName) {
		return "_" + ExtractorUtils.getCamelCase(sigName);
	}
	
	public static String getLocalFieldName(String fieldLabel, String sigName) {

		return getCamelCase(sigName) + "_" + ExtractorUtils.localNameSeparator(sigName) + "_" + fieldLabel;
	}
	
	public static String localNameSeparator(String sigName) {
		return "" + Math.abs(sigName.hashCode());
	}
	
	public static int getNumberOfTuplesFromA4Solution(A4Solution solution){
		int num = 0;
		
		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;

			// The ordering sig should be skipped
			if (isOrdering(sig))
				continue;
			
			if(!sig.label.startsWith("this/")) {
				continue;
			}
			
			num += solution.eval(sig).size();
			for (Field field : sig.getFields()) {
				num += solution.eval(field).size();
			}
		}
		return num;
	}
		
	public static MultiKeyMap<String, String> getMap(A4Solution solution) {
		
		MultiKeyMap<String, String> map = new MultiKeyMap<>();
		
		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;

			// The ordering sig should be skipped
			if (isOrdering(sig))
				continue;
			
			if(!sig.label.startsWith("this/")) {
				continue;
			}
			
			String localSig = ExtractorUtils.getLocalSigName(sig.label);
			String sigValue = sig.label;
			map.put(localSig, localSig + "'", localSig + "''", sigValue);
			
			for (Field field : sig.getFields()) {
				
				String localField  = ExtractorUtils.getLocalFieldName(field.label, sig.label);
				String fieldValue = sig.label + "<:" + field.label;
				map.put(localField, localField + "'", localField + "''", fieldValue);
			}
		}
		
		return map;
	}
	
	
	/**
	 * Given an A4solution object from AlloyExecuter, it converts it to a Alloy
	 * syntax
	 * 
	 * @param solution
	 * @return
	 */
	public static String convertA4SolutionToAlloySyntax(A4Solution solution, boolean useLocalNames) {
		if(solution == null) return "";
		List<String> emptySigs = new ArrayList<>();
		List<String> constraints = new ArrayList<>();
		List<String> quantifiers = new ArrayList<>();
		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;

			// The ordering sig should be skipped
			if (isOrdering(sig))
				continue;
			
			// TODO: Trying to exclude atoms that are defined as signatures. Find a better condition.
			if(!sig.label.startsWith("this/")) {
				if(Configuration.IsInDeubbungMode)
					System.out.println("" + (sig.isAtom == null ? "not" : "") + "atom");
				
				continue;
			}
			
			String sigName = sig.label.replace("this/", "");
			sigName = useLocalNames && sig.isAbstract == null ? getLocalSigName(sigName) : sigName;

			if (solution.eval(sig).size() == 0) {
				emptySigs.add(sigName);
			} else {
				List<String> atoms = new ArrayList<>();
				for (A4Tuple tuple : solution.eval(sig)) {
					atoms.add(tuple.toString().replace("$", "_").replace("/", "_"));
				}
				if (!isSubSig(sig))
					quantifiers.add("some disj " + atoms.stream().collect(Collectors.joining(", ")) + ": univ");
				constraints.add("\t((" + atoms.stream().collect(Collectors.joining("+")) + ") = " + sigName+")");
			}
		}

		for (String noSigName : emptySigs) {
			constraints.add("\tno " + noSigName);
		}

		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;
			else
				for (Field field : sig.getFields()) {
					A4TupleSet fieldsTuples = solution.eval(field);
					String fieldName = field.label;
					fieldName = useLocalNames ? getLocalFieldName(fieldName, sig.label.replace("this/", "")) : fieldName;
					if (isOrdering(sig)) {
						fieldName = (sig.label.contains("/") ? sig.label.split("/")[0] + "/" : "")
								+ field.label.toLowerCase();
					}
					String constraint = "";
					if (fieldsTuples.size() == 0) {
						constraints.add("\tno " + fieldName);
					} else {
						final List<String> tuples = new ArrayList<>();
						fieldsTuples.forEach(t -> tuples.add(t.toString().replace("$", "_")));
						constraint = "\t((" + tuples.stream().collect(Collectors.joining("+")) + ") = " + fieldName+")";
					}
					if (isOrdering(sig)) {
						String orderingAtom = solution.eval(sig).iterator().next().toString().replace("$", "_");
						constraint = constraint.replaceAll(orderingAtom + "->", "");
					}
					if (!constraint.isEmpty())
						constraints.add(constraint);
				}
		}

		String result = "{";
		if (quantifiers.size() > 0) {
			result = quantifiers.stream().collect(Collectors.joining("| ")) + "| {";
		}

		result = result + constraints.stream().collect(Collectors.joining("\n")) + "}";
		return result;
	}

	public static String convertFormulaExprToAlloySyntax(Expr formula, boolean useLocalNames) {
		
		if(formula instanceof ExprList) {

			StringBuilder builder = new StringBuilder();
			ExprList exprList = (ExprList)formula;
			String operator = exprList.op.name().toLowerCase() + " ";
			for(Expr arg : exprList.args) {
				String expr = convertFormulaExprToAlloySyntax(arg, useLocalNames);
				builder.append(operator + expr + "\n\t");
			}
			
			builder.delete(0, operator.length());
			return builder.toString();
		}

		if(formula instanceof ExprUnary) {
			ExprUnary expr = (ExprUnary)formula;
			String operator = "";
			if(expr.op != Op.NOOP) {
				String label = expr.op == Op.NOT ? expr.op.name() : expr.op.toString();
				operator = label.split("\\s")[0].toLowerCase() + " ";
			}
			
			return operator + convertFormulaExprToAlloySyntax(expr.sub, useLocalNames);
		}
		
		if(formula instanceof ExprBinary) {
			ExprBinary expr = (ExprBinary)formula;
			String left = convertFormulaExprToAlloySyntax(expr.left, useLocalNames);
			String right = convertFormulaExprToAlloySyntax(expr.right, useLocalNames);
			return left + " " + expr.op.toString() + " " + right;
		}

		if(formula instanceof ExprCall) {
			ExprCall expr = (ExprCall)formula;
			String call = expr.fun.label.replace("this/", "");
			
			String p = "";
			if(expr.args.size() > 0) {
				StringBuilder params = new StringBuilder();
				for(Expr arg : expr.args) {
					params.append(", " + convertFormulaExprToAlloySyntax(arg, useLocalNames));
				}
				
				params.delete(0, 2);
				p = params.toString();
			}
		
			return String.format("%s[%s]", call, p);
		}
		
		if(formula instanceof Field) {
			Field field = (Field)formula;
			if(useLocalNames) {
				return ExtractorUtils.getLocalFieldName(field.label, field.sig.label.replace("this/", ""));
			}
			
			return field.label;
		}
		
		String name = formula.toString().replace("this/", "");
		return useLocalNames ? getLocalSigName(name) : name;
	}
}
