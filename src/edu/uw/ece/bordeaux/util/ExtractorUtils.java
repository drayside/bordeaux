package edu.uw.ece.bordeaux.util;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;

/**
 * The class contains static methods that are helpful for extracting Alloy
 * entities.
 * 
 * @author vajih
 *
 */
public class ExtractorUtils {
	/**
	 * Given a command, its scope is returned as String
	 * 
	 * @param command
	 * @return
	 */
	public static String extractScopeFromCommand(Command command) {
		boolean first = true;
		StringBuilder sb = new StringBuilder();
		if (command.overall >= 0 && (command.intScope.bitwidth >= 0 || command.maxseq >= 0 || command.scope.size() > 0))
			sb.append(" for ").append(command.overall).append(" but");
		else if (command.overall >= 0)
			sb.append(" for ").append(command.overall);
		else if (command.intScope.bitwidth >= 0 || command.maxseq >= 0 || command.scope.size() > 0)
			sb.append(" for");
		if (command.intScope.bitwidth >= 0) {
			sb.append(" ").append(command.intScope.bitwidth).append(" int");
			first = false;
		}
		if (command.maxseq >= 0) {
			sb.append(first ? " " : ", ").append(command.maxseq).append(" seq");
			first = false;
		}
		for (CommandScope e : command.scope) {
			sb.append(first ? " " : ", ").append(e);
			first = false;
		}
		if (command.expects >= 0)
			sb.append(" expect ").append(command.expects);
		return sb.toString();
	}

	private static boolean isOrdering(Sig sig) {
		return sig.isPrivate != null && sig.isOne != null
				&& new File(sig.pos().filename).getName().equals("ordering.als");
	}

	private static boolean isSubSig(Sig sig) {
		return sig.isSubsig != null && sig instanceof Sig.PrimSig && !((Sig.PrimSig)sig).parent.builtin;
	}

	/**
	 * Given an A4solution object from AlloyExecuter, it converts it to a Alloy
	 * syntax
	 * 
	 * @param solution
	 * @return
	 */
	public static String convertA4SolutionToAlloySyntax(A4Solution solution) {
		List<String> emptySigs = new ArrayList<>();
		List<String> constraints = new ArrayList<>();
		List<String> quantifiers = new ArrayList<>();
		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;

			// The ordering sig should be skipped
			if (isOrdering(sig))
				continue;

			String sigName = sig.label.replace("this/", "");

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
}
