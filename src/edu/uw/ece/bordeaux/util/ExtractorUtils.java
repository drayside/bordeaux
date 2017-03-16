package edu.uw.ece.bordeaux.util;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary.Op;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import edu.uw.ece.bordeaux.Configuration;
import edu.uw.ece.bordeaux.engine.BordeauxEngine.BordeauxLastSolutionInfo;
import edu.uw.ece.bordeaux.engine.BordeauxEngine.SolutionType;
import edu.uw.ece.bordeaux.onborder.OnBorderCodeGenerator;
import edu.uw.ece.bordeaux.tests.Elaboration;
import kodkod.instance.Instance;

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

		if (module != null) {

			for (Command c : module.getAllCommands()) {
				if (c.label.equals(commandName)) {
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

		if (command.overall >= 0
				&& ((command.intScope != null && ((command.intScope.bitwidth != null && command.intScope.bitwidth >= 0)
						|| command.intScope.atoms != null)) || command.maxseq >= 0
						|| (command.scope != null && command.scope.size() > 0)))
			sb.append(" for ").append(command.overall).append(" but");
		else if (command.overall >= 0)
			sb.append(" for ").append(command.overall);
		else if ((command.intScope != null && ((command.intScope.bitwidth != null && command.intScope.bitwidth >= 0)
				|| command.intScope.atoms != null)) || command.maxseq >= 0
				|| (command.scope != null && command.scope.size() > 0))
			sb.append(" for");
		if (command.intScope != null && ( ( command.intScope.bitwidth != null && command.intScope.bitwidth >= 0)
				|| ( command.intScope.atoms != null))) {
			if ((command.intScope.bitwidth != null && command.intScope.bitwidth >= 0))
				sb.append(" ").append(command.intScope.bitwidth).append(" int");
			if (command.intScope.atoms != null)
				try {
					sb.append(" ").append(command.intScope.atoms.min() + ".." + command.intScope.atoms.max())
							.append(" Int");
				} catch (ErrorFatal e) {
					e.printStackTrace();
				}
			first = false;
		}
		if (command.maxseq >= 0) {
			sb.append(first ? " " : ", ").append(command.maxseq).append(" seq");
			first = false;
		}
		if (command.scope != null) {
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
		return sig.isSubsig != null && sig instanceof Sig.PrimSig && !((Sig.PrimSig) sig).parent.builtin;
	}

	public static String getCamelCase(String in) {
		if (in == null || in.isEmpty())
			return in;

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

	protected static List<List<ExprVar>> seperateSkolemizedVars(List<ExprVar> vars) {

		List<List<ExprVar>> result = new ArrayList<>();
		// entailing no prime
		result.add(new ArrayList<>());
		// entailing one prime
		result.add(new ArrayList<>());
		// entailing two primes
		result.add(new ArrayList<>());

		Set<String> names = vars.stream().map(v -> v.label).collect(Collectors.toSet());

		for (ExprVar var : vars) {
			String label = var.label;
			String label_p = label + "'";
			String label_pp = label_p + "'";

			if (names.contains(label) && names.contains(label_p) && names.contains(label_pp)) {
				result.get(0).add(var);
			}

			if (names.contains(label) && names.contains(label_p) && !names.contains(label_pp)) {
				result.get(1).add(var);
			}

			if (names.contains(label) && !names.contains(label_p) && !names.contains(label_pp)) {
				result.get(2).add(var);
			}
		}

		return Collections.unmodifiableList(result);
	}

	protected static boolean isSig(A4Solution solution, String name, boolean useLocalNames) {

//		return solution.getAllReachableSigs().makeCopy().stream().anyMatch(s -> s.label.equals("this/" + name));
		return solution.getAllReachableSigs().makeCopy().stream().anyMatch((s) -> {
			String sigName = useLocalNames ? ExtractorUtils.getLocalSigName(s.shortLabel()) : s.shortLabel();
			return sigName.equals(name);
		});
	}

	protected static String convertBordeauxSolutionToAlloySyntax(A4Solution solution, List<ExprVar> vars, Map<String, String> decodeSkolemizedNames, boolean useLocalNames) {

		final List<String> declPart = new ArrayList<>();
		final List<String> noPart = new ArrayList<>();
		final List<String> bodyPart = new ArrayList<>();

		for (ExprVar var : vars) {
			try {
				if (!decodeSkolemizedNames.containsKey(var.label)) {
					System.err.println(var.label + " is not in the given map!");
					continue;
				}

				if (solution.eval(var).toString().equals("{}")) {
					// not atom or tuple
					noPart.add("no " + decodeSkolemizedNames.get(var.label));

				} else {

					if (isSig(solution, decodeSkolemizedNames.get(var.label), useLocalNames)) {
						declPart.add("some disj "
								+ solution.eval(var).toString().replaceAll("\\{|\\}", "").replaceAll("\\$", "_")
								+ ": univ ");
						bodyPart.add(
								"(" + solution.eval(var).toString().replaceAll("\\{|\\}", "").replaceAll("\\$", "_")
										.replaceAll(",", "+") + " = " + decodeSkolemizedNames.get(var.label) + ")");
					} else {
						bodyPart.add(
								"(" + solution.eval(var).toString().replaceAll("\\{|\\}", "").replaceAll("\\$", "_")
										.replaceAll(",", "+") + " = " + decodeSkolemizedNames.get(var.label) + ")");
					}
				}
			} catch (Err e) {
				e.printStackTrace();
			}

		}

		String noPartString = noPart.stream().collect(Collectors.joining(" and "));
		String declBody = declPart.size() > 0 ? declPart.stream().collect(Collectors.joining("|")) + "| "
				+ bodyPart.stream().collect(Collectors.joining(" and ")) : "";

		if (declBody.length() > 0 && noPartString.length() > 0) {
			return "(" + declBody + ") and " + "(" + noPartString + ")";
		} else if (declBody.length() > 0) {
			return "(" + declBody + ")";
		} else if (noPartString.length() > 0) {
			return "(" + noPartString + ")";
		} else {
			return "";
		}

	}
	
	public static Pair<A4Solution, A4Solution> convertBordeauxSolutionToAlloySolution(A4Solution solution, BordeauxLastSolutionInfo blsi) {

		final File fileName = solution.getAllReachableSigs().makeCopy().stream().filter(s -> !s.builtin)
				.filter(s -> s.pos.filename != "").map(s -> new File(s.pos.filename)).findFirst().get();

		String scope = ExtractorUtils.extractScopeFromCommand(fileName.getAbsolutePath(),
				OnBorderCodeGenerator.FIND_MARGINAL_INSTANCES_COMMAND);

		Pair<String, String> solSyntax = (ExtractorUtils.convertBordeauxSolutionToAlloySyntax(solution, false));

		String newContent = (new Elaboration()).createAllSigsdeclaration(fileName) + "\npred _a_[]{\n" + solSyntax.a
				+ "\n}" + "\npred _b_[]{\n" + solSyntax.b + "\n}" + "\nrun _a_ " + scope + "\nrun _b_ " + scope;
		File toSolution = new File(fileName.getParent(), fileName.getName() + ".sol.als");
		try {
			Util.writeAll(toSolution.getAbsolutePath(), newContent);
		} catch (Err e) {
			e.printStackTrace();
		}

		Pair<A4Solution, A4Solution> result = new Pair<>(null, null);
		
		Instance inst = blsi.getLastSolutionInstance();
		BordeauxLastSolutionInfo blsi_a_ = new BordeauxLastSolutionInfo(inst!=null ? inst.clone() : null, SolutionType.NEAR_HIT, blsi.getAtoms(),
				blsi.getAdditionSuppressions(), blsi.getSubtractionSuppressions());
		BordeauxLastSolutionInfo blsi_b_ = new BordeauxLastSolutionInfo(inst!=null ? inst.clone() : null, SolutionType.NEAR_MISS, blsi.getAtoms(),
				blsi.getAdditionSuppressions(), blsi.getSubtractionSuppressions());
		try {
			result = new Pair<>(
					A4CommandExecuter.get().runAlloyThenGetAnswers(toSolution.getAbsolutePath(), A4Reporter.NOP, "_a_", blsi_a_),
					A4CommandExecuter.get().runAlloyThenGetAnswers(toSolution.getAbsolutePath(), A4Reporter.NOP,
							"_b_", blsi_b_));
		} catch (Err e) {
			e.printStackTrace();
		}
		return result;
	}

	public static Pair<String, String> convertBordeauxSolutionToAlloySyntax(A4Solution solution, boolean useLocalNames) {
		
		Map<String, String> decodeSkolemizedNames = generateSkolemMap(solution, useLocalNames);
		
		final List<ExprVar> vars = new ArrayList<>();
		solution.getAllSkolems().forEach(s -> vars.add(s));

		List<List<ExprVar>> skolemizedVars = seperateSkolemizedVars(vars);

		String nearHitString = convertBordeauxSolutionToAlloySyntax(solution, skolemizedVars.get(0), decodeSkolemizedNames, useLocalNames);
		String nearMissString = convertBordeauxSolutionToAlloySyntax(solution, skolemizedVars.get(1), decodeSkolemizedNames, useLocalNames);
		
		return new Pair<>(nearHitString, nearMissString);
	}

	public static int getNumberOfTuplesFromA4Solution(A4Solution solution) {
		int num = 0;

		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;

			// The ordering sig should be skipped
			if (isOrdering(sig))
				continue;

			if (!sig.label.startsWith("this/")) {
				continue;
			}

			num += solution.eval(sig).size();
			for (Field field : sig.getFields()) {
				num += solution.eval(field).size();
			}
		}
		return num;
	}

	public static Map<String, String> generateSkolemMap(A4Solution solution, boolean useLocalNames) {

		Map<String, String> map = new HashMap<>();

		final String base = "$" + OnBorderCodeGenerator.FIND_MARGINAL_INSTANCES_COMMAND + "_";
		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;

			// The ordering sig should be skipped
			if (isOrdering(sig))
				continue;

			if (!sig.label.startsWith("this/")) {
				continue;
			}

			String sigName = sig.shortLabel();
			String localSig = ExtractorUtils.getLocalSigName(sigName);
			String SkolemlSig = base + localSig;
			String sigValue = useLocalNames ? localSig : sig.shortLabel();
			map.put(SkolemlSig, sigValue);
			map.put(SkolemlSig + "'", sigValue);
			map.put(SkolemlSig + "''", sigValue);

			for (Field field : sig.getFields()) {

				String localField = ExtractorUtils.getLocalFieldName(field.label, sigName);
				String SkolemField = base + localField;
				String localValue = useLocalNames ? localField : field.label;
				map.put(SkolemField, localValue);
				map.put(SkolemField + "'", localValue);
				map.put(SkolemField + "''", localValue);
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
		if (solution == null)
			return "";

		List<String> emptySigs = new ArrayList<>();
		List<String> constraints = new ArrayList<>();
		List<String> quantifiers = new ArrayList<>();
		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;

			// The ordering sig should be skipped
			if (isOrdering(sig))
				continue;

			// TODO: Trying to exclude atoms that are defined as signatures.
			// Find a better condition.
			if (!sig.label.startsWith("this/")) {
				if (Configuration.IsInDeubbungMode)
					System.out.println("" + (sig.isAtom == null ? "not" : "") + "atom");
				continue;
			}

			String sigName = sig.label.replace("this/", "");
			sigName = useLocalNames && sig.isAbstract == null ? getLocalSigName(sigName) : sigName;

			if (!solution.satisfiable()) {
				constraints.add("(no " + sigName + ")");
				continue;
			}

			if (solution.eval(sig).size() == 0) {
				emptySigs.add(sigName);
			} else {
				List<String> atoms = new ArrayList<>();
				for (A4Tuple tuple : solution.eval(sig)) {
					atoms.add(tuple.toString().replace("$", "_").replace("/", "_"));
				}
				if (!isSubSig(sig))
					quantifiers.add("some disj " + atoms.stream().collect(Collectors.joining(", ")) + ": univ");
				constraints.add("\t((" + atoms.stream().collect(Collectors.joining("+")) + ") = " + sigName + ")");
			}
		}

		for (String noSigName : emptySigs) {
			constraints.add("(no " + noSigName + ")");
		}

		for (Sig sig : solution.getAllReachableSigs()) {
			if (sig.builtin)
				continue;
			else
				for (Field field : sig.getFields()) {

					String fieldName = field.label;
					fieldName = useLocalNames ? getLocalFieldName(fieldName, sig.label.replace("this/", ""))
							: fieldName;
					if (!solution.satisfiable()) {
						constraints.add("(no " + fieldName + ")");
						continue;
					}

					A4TupleSet fieldsTuples = solution.eval(field);
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
						constraint = "\t((" + tuples.stream().collect(Collectors.joining("+")) + ") = " + fieldName
								+ ")";
					}
					if (isOrdering(sig)) {
						String orderingAtom = solution.eval(sig).iterator().next().toString().replace("$", "_");
						constraint = constraint.replaceAll(orderingAtom + "->", "");
					}
					if (!constraint.isEmpty())
						constraints.add(constraint);
				}
		}

		String result = "(";
		if (quantifiers.size() > 0) {
			result = quantifiers.stream().collect(Collectors.joining("| ")) + "| (";
		}

		result = result + constraints.stream().collect(Collectors.joining(" and ")) + ")";
		return result;
	}

	public static String convertFormulaExprToAlloySyntax(Expr formula, boolean useLocalNames) {

		if (formula instanceof ExprList) {

			StringBuilder builder = new StringBuilder();
			ExprList exprList = (ExprList) formula;
			String operator = exprList.op.name().toLowerCase() + " ";
			for (Expr arg : exprList.args) {
				String expr = convertFormulaExprToAlloySyntax(arg, useLocalNames);
				builder.append(operator + expr + "\n\t");
			}

			builder.delete(0, operator.length());
			return builder.toString();
		}

		if (formula instanceof ExprUnary) {
			ExprUnary expr = (ExprUnary) formula;
			String operator = "";
			if (expr.op != Op.NOOP) {
				String label = expr.op == Op.NOT ? expr.op.name() : expr.op.toString();
				operator = label.split("\\s")[0].toLowerCase() + " ";
			}

			return operator + convertFormulaExprToAlloySyntax(expr.sub, useLocalNames);
		}

		if (formula instanceof ExprBinary) {
			ExprBinary expr = (ExprBinary) formula;
			String left = convertFormulaExprToAlloySyntax(expr.left, useLocalNames);
			String right = convertFormulaExprToAlloySyntax(expr.right, useLocalNames);
			return left + " " + expr.op.toString() + " " + right;
		}

		if (formula instanceof ExprCall) {
			ExprCall expr = (ExprCall) formula;
			String call = expr.fun.label.replace("this/", "");

			String p = "";
			if (expr.args.size() > 0) {
				StringBuilder params = new StringBuilder();
				for (Expr arg : expr.args) {
					params.append(", " + convertFormulaExprToAlloySyntax(arg, useLocalNames));
				}

				params.delete(0, 2);
				p = params.toString();
			}

			return String.format("%s[%s]", call, p);
		}

		if (formula instanceof Field) {
			Field field = (Field) formula;
			if (useLocalNames) {
				return ExtractorUtils.getLocalFieldName(field.label, field.sig.label.replace("this/", ""));
			}

			return field.label;
		}

		String name = formula.toString().replace("this/", "");
		return useLocalNames ? getLocalSigName(name) : name;
	}
}
