package edu.uw.ece.bordeaux.tests;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Before;
import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList.Op;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateDeclarativeConstriant2DeclarativeFormula;
import edu.uw.ece.bordeaux.A4CommandExecuter;
import kodkod.ast.Formula;

public class Elaboration {

	final File tmpFolder = new File("tmp/test");

	@Before
	public void setUp() {
		tmpFolder.mkdirs();
	}

	// ---------------------------------------------

	protected CompModule parseToCompModule(File src) {
		CompModule module = null;
		try {
			module = (CompModule) A4CommandExecuter.get().parse(src.getAbsolutePath(), A4Reporter.NOP);
		} catch (Err e) {
			e.printStackTrace();
		}
		return module;
	}

	protected List<Formula> convertConstraintsToFormulas(CompModule module, Command command) {
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.KK;
		List<Formula> formulas = new ArrayList<>();
		try {
			formulas = TranslateDeclarativeConstriant2DeclarativeFormula.translate(A4Reporter.NOP,
					module.getAllReachableUserDefinedSigs(), command, options);
		} catch (Err e1) {
			e1.printStackTrace();
		}
		return Collections.unmodifiableList(formulas);
	}

	public List<Formula> convertSigsdeclarationToFormula(File src) {
		CompModule module = parseToCompModule(src);

		Command command = module.getAllCommands().get(0);
		command = command.change(ExprList.make(command.pos, command.pos, Op.AND, Collections.emptyList()));

		return convertConstraintsToFormulas(module, command);
	}

	public List<Formula> convertAllConstraintsToFormula(File src, String commandName) {
		if (commandName == null || commandName.isEmpty())
			throw new RuntimeException("Command Name cannot be empty or null");

		CompModule module = parseToCompModule(src);

		Command command = null;
		for (Command c : module.getAllCommands()) {
			if (c.label.equals(commandName)) {
				command = c;
				break;
			}
		}

		if (command == null)
			throw new NullPointerException("Command cannot be null");

		return convertConstraintsToFormulas(module, command);
	}

	protected String sanitizer(String statement) {
		return statement.replaceAll("this/[a-zA-Z_$][a-zA-Z_$0-9]*\\.", "").replace("this/", "");
	}

	/**
	 * Given a the src file, the function returns a list, where result.get(0) is
	 * the body of 'instance' predicate, and result.get(1) is the body of
	 * structural predicate. result.get(2) body of constraint predicate.
	 * 
	 * tmpfolder is used for storing src transformed files.
	 * 
	 * @param src
	 * @param tmpFolder
	 * @return
	 */
	public List<String> createBodyOfInstance_Structural_Constraint_Predicates(final File src, final File tmpFolder) {

		CompModule module = parseToCompModule(src);
		String commandLabel = module.getAllCommands().get(0).label;
		return createBodyOfInstance_Structural_Constraint_Predicates(src, tmpFolder, commandLabel);
	}

	/**
	 * Given a the src file, the function returns a list, where result.get(0) is
	 * the body of 'instance' predicate, and result.get(1) is the body of
	 * structural predicate. result.get(2) body of constraint predicate.
	 * 
	 * tmpfolder is used for storing src transformed files.
	 * 
	 * @param src
	 * @param tmpFolder
	 * @return
	 */
	public List<String> createBodyOfInstance_Structural_Constraint_Predicates(final File src, final File tmpFolder,
			String commandName) {

		final String elabCommandName = "_s__igsp_";

		final String sigsWithStructuralConstraints = createAllSigsdeclaration(src, true, false) + "\npred "
				+ elabCommandName + "[]{}\nrun " + elabCommandName;
		final String sigsWithoutStructuralConstraints = createAllSigsdeclaration(src, false, false) + "\npred "
				+ elabCommandName + "[]{}\nrun " + elabCommandName;
		final String sigsWithoutStructuralConstraintsWithOneSigs = createAllSigsdeclaration(src, false, true)
				+ "\npred " + elabCommandName + "[]{}\nrun " + elabCommandName;

		final File sigsWithStructuralConstraintsFile = new File(tmpFolder,
				"with_" + Math.abs(sigsWithStructuralConstraints.hashCode()) + ".als");
		final File sigsWithoutStructuralConstraintsFile = new File(tmpFolder,
				"without_" + Math.abs(sigsWithoutStructuralConstraints.hashCode()) + ".als");
		final File sigsWithoutStructuralConstraintsWithOneSigsFile = new File(tmpFolder,
				"withone_" + Math.abs(sigsWithoutStructuralConstraintsWithOneSigs.hashCode()) + ".als");

		try {
			Util.writeAll(sigsWithStructuralConstraintsFile.getAbsolutePath(), sigsWithStructuralConstraints);
			Util.writeAll(sigsWithoutStructuralConstraintsFile.getAbsolutePath(), sigsWithoutStructuralConstraints);
			Util.writeAll(sigsWithoutStructuralConstraintsWithOneSigsFile.getAbsolutePath(),
					sigsWithoutStructuralConstraintsWithOneSigs);
		} catch (Err e) {
			e.printStackTrace();
		}

		final List<Formula> withoutStructurals = convertSigsdeclarationToFormula(sigsWithoutStructuralConstraintsFile);

		// find all A.univ s
		final Set<String> allunivs = withoutStructurals.stream().map(f -> f.toString()).filter(s -> s.startsWith("(("))
				.filter(s -> s.contains(" . univ)")).collect(Collectors.toSet());
		final Set<String> allExtends = withoutStructurals.stream().map(f -> f.toString())
				.filter(s -> s.startsWith("no (")).collect(Collectors.toSet());
		final Set<String> allTupleInclusion = withoutStructurals.stream().map(f -> f.toString())
				.filter(s -> s.startsWith("(all ")).map(s -> s.substring(s.indexOf("|") + 1, s.length() - 1).trim())
				.collect(Collectors.toSet());
		final Set<String> allTupleInclusionWithAnd = new HashSet<>();
		allTupleInclusion.forEach(s -> {
			allTupleInclusionWithAnd.add("&& " + s.trim());
			allTupleInclusionWithAnd.add(s.trim() + " &&");
		});

		final String instanceBody = withoutStructurals.stream().map(f -> f.toString())
				.filter(s -> !allExtends.contains(s)).map(s -> sanitizer(s)).collect(Collectors.joining("\n"));

		final Set<Formula> withoutStructuralsOne = new HashSet<>(
				convertSigsdeclarationToFormula(sigsWithoutStructuralConstraintsWithOneSigsFile));
		Set<String> allStructuralsOneFormulas = withoutStructuralsOne.stream().map(f -> f.toString())
				.filter(s -> !allunivs.contains(s) && !allExtends.contains(s) && !allTupleInclusion.contains(s))
				.collect(Collectors.toSet());
		final Set<String> allStructuralsOneFormulasWithAnd = new HashSet<>();
		allStructuralsOneFormulas.forEach(s -> {
			allStructuralsOneFormulasWithAnd.add("&& " + s.trim());
			allStructuralsOneFormulasWithAnd.add(s.trim() + " &&");
		});

		final Set<Formula> withStructurals = new HashSet<>(
				convertSigsdeclarationToFormula(sigsWithStructuralConstraintsFile));

		Set<String> structuralFormulas = withStructurals.stream().map(f -> f.toString()).collect(Collectors.toSet());

		structuralFormulas.removeAll(allunivs);
		structuralFormulas.removeAll(allExtends);

		final Set<String> structuralBody = structuralFormulas.stream().map(f -> f.toString())
				.filter(s -> !allExtends.contains(s)).filter(s -> !allunivs.contains(s)).collect(Collectors.toSet());

		final Set<String> tmpStructuralBody = new HashSet<>();
		for (String body : structuralBody) {
			String seen = body;
			for (String inclusion : allTupleInclusionWithAnd) {
				if (seen.contains(inclusion)) {
					seen = seen.replace(inclusion, "");
					break;
				}
			}
			// if the inclusion with and is not seen, so it might be the only
			// clause
			// in the quantifier body or there is no quantifier.
			for (String inclusion : allTupleInclusion) {
				if (seen.contains(inclusion)) {
					seen = "";
					break;
				}
			}
			// if the sig has one quantifier, ie "one sig NAME{}", then the quan
			for (String inclusion : allStructuralsOneFormulasWithAnd) {
				if (seen.contains(inclusion)) {
					seen = seen.replace(inclusion, "").trim();
					break;
				}
			}
			// if the inclusion with and is not seen, so it might be the only
			// clause
			// in the quantifier body or there is no quantifier.
			for (String inclusion : allStructuralsOneFormulas) {
				if (seen.contains(inclusion)) {
					seen = "";
					break;
				}
			}

			if (seen.length() > 0)
				tmpStructuralBody.add(seen);
			tmpStructuralBody.add(seen);
		}

		final String structuralConstraintBody = sanitizer((generateStructuralConstraintsForOneAndLoneSig(src) + "\n"
				+ tmpStructuralBody.stream().collect(Collectors.joining("\n"))).trim());

		sigsWithStructuralConstraintsFile.delete();
		sigsWithoutStructuralConstraintsFile.delete();
		sigsWithoutStructuralConstraintsWithOneSigsFile.delete();

		// remove the structural constraints from the rest of constraints in the
		// formula.
		List<Formula> constraintFormulas = convertAllConstraintsToFormula(src, commandName);

		// String commandLabel = module.getAllCommands().get(0).label;
		// commandname does not have a name
		final String tmpCommandName = commandName.contains("$") ? "this" : commandName + "_this";
		Set<String> constraintFormulasAsSet = constraintFormulas.stream().map(f -> f.toString())
				.collect(Collectors.toSet());
		Set<String> strucuralsAsSet = withStructurals.stream().map(f -> f.toString())
				.map(s -> s.replace(elabCommandName + "_this", tmpCommandName)).collect(Collectors.toSet());
		constraintFormulasAsSet.removeAll(strucuralsAsSet);

		final String constraintsBody = constraintFormulasAsSet.stream().map(s -> sanitizer(s))
				.collect(Collectors.joining("\n"));

		return Arrays.asList(instanceBody, structuralConstraintBody, constraintsBody);
	}

	public String generateStructuralConstraintsForOneAndLoneSig(File src) {
		return parseToCompModule(src).getAllReachableUserDefinedSigs().stream()
				.map(s -> generateStructuralConstraintsForOneAndLoneSig(s)).filter(s -> !s.isEmpty())
				.collect(Collectors.joining("\n"));
	}

	/**
	 * Provided a sig is lone, ie 'lone sig A{}', an structural constraint is
	 * generated for it, ie 'lone A' Provided a sig is one, ie 'one sig A{}', an
	 * structural constraint is generated for it, ie 'one A' For the
	 * multiplicity constraint of some, the Alloy translator already takes care
	 * of it.
	 * 
	 * @param sig
	 * @return
	 */
	public String generateStructuralConstraintsForOneAndLoneSig(Sig sig) {
		String result = "";

		if (sig.isLone != null) {
			result = "lone " + sig.label;
		} else if (sig.isOne != null) {
			result = "one " + sig.label;
		}

		return result;
	}

	public String getMult(Sig sig) {
		String result = "";

		if (sig.isLone != null) {
			result = " lone ";
		} else if (sig.isOne != null) {
			result = " one ";
		} else if (sig.isSome != null) {
			result = " some ";
		}

		return result;
	}

	/**
	 * Translate back a field object to Alloy source code.
	 * 
	 * @param field
	 * @param withMult
	 * @return
	 */
	public String convertFieldToStringDeclaration(Sig.Field field, boolean withMult) {
		String result = "";
		Expr fieldExpr = field.decl().expr.deNOP();
		if (fieldExpr instanceof ExprUnary) {
			ExprUnary exprUnary = (ExprUnary) fieldExpr.deNOP();
			if (!withMult) {
				result = " set " + exprUnary.sub.toString().replaceAll("this/", "");
			} else {
				result = exprUnary.toString().replaceAll("this/", "");
			}
		} else if (fieldExpr instanceof ExprBinary) {
			Expr binExpr = fieldExpr;
			while (binExpr instanceof ExprBinary) {
				ExprBinary bExpr = (ExprBinary) binExpr;
				if (!withMult) {
					result = result + bExpr.left.deNOP().toString().replaceAll("this/", "") + ExprBinary.Op.ARROW;
				} else {
					result = result + bExpr.left.deNOP().toString().replaceAll("this/", "") + " " + bExpr.op.toString()
							+ " ";
				}
				binExpr = bExpr.right;
			}
			result = result + binExpr.toString().replaceAll("this/", "");
		}
		return result;
	}

	/**
	 * Given a signature object from AST, a source code is generated back. If
	 * !withMult, all the multiplicity constraints are removed. every relations
	 * is turned to cross-products of set->set. If withOne, the multiplicity of
	 * signatures become one, regardless of their current state. In any case
	 * appended fact is removed.
	 * 
	 * @param sig
	 * @param withMult
	 * @param withOne
	 * @return
	 */
	public String convertSigToStringDeclaration(Sig sig, boolean withMult, boolean withOne) {
		String result = "";

		if (sig.isAbstract != null) {
			result = result + " abstract ";
		}

		if (withMult) {
			result = result + getMult(sig);
		} else if (withOne && sig.isAbstract == null) {
			result = result + " one ";
		}

		result = result + " sig ";

		result = result + sig.shortLabel();

		if (sig instanceof Sig.SubsetSig) {
			result = result + " in ";
			result = result
					+ ((Sig.SubsetSig) sig).parents.stream().map(s -> s.shortLabel()).collect(Collectors.joining("+"));
		} else if (sig instanceof Sig.PrimSig) {
			PrimSig pPsig = (Sig.PrimSig) sig;
			if (!pPsig.parent.builtin) {
				result = result + " extends " + pPsig.parent.shortLabel();
			}
		}
		result = result + "{";
		result = result + sig.getFields().makeCopy().stream()
				.map(f -> f.label + ":" + convertFieldToStringDeclaration(f, withMult))
				.collect(Collectors.joining(","));
		result = result + "}";

		return result.replace("  ", " ").trim();
	}

	/**
	 * Given an Alloy source code, an Alloy code per each signature is created.
	 * 
	 * @param src
	 * @param withMult
	 * @param withOne
	 * @return
	 */
	public String createAllSigsdeclaration(File src) {
		return createAllSigsdeclaration(src, false, false);
	}

	/**
	 * Given an Alloy source code, an Alloy code per each signature is created.
	 * 
	 * @param src
	 * @param withMult
	 * @param withOne
	 * @return
	 */
	protected String createAllSigsdeclaration(File src, boolean withMult, boolean withOne) {
		CompModule module = null;
		try {
			module = (CompModule) A4CommandExecuter.get().parse(src.getAbsolutePath(), A4Reporter.NOP);
		} catch (Err e) {
			e.printStackTrace();
		}

		return module.getAllReachableUserDefinedSigs().stream()
				.map(s -> convertSigToStringDeclaration(s, withMult, withOne)).collect(Collectors.joining("\n"));
	}

	// ------------------------------------

	public CompModule creatAndParseAlloyCodeForTest(String content) {
		final File test = new File(tmpFolder, "a.als");
		final String alloySample = content + "pred _empty_run_pred[]{ }\n" + "run _empty_run_pred for 0\n";
		try {
			Util.writeAll(test.getAbsolutePath(), alloySample);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.msg);
		}

		CompModule module = null;
		try {
			module = (CompModule) A4CommandExecuter.get().parse(test.getAbsolutePath(), A4Reporter.NOP);
		} catch (Err e) {
			e.printStackTrace();
			fail(e.msg);
		}
		return module;
	}

	public void testWithoutStructuralConstraints(String content, String expectedContentWithoutMult) {
		CompModule module = creatAndParseAlloyCodeForTest(content);
		String allsigs = module.getAllReachableUserDefinedSigs().stream()
				.map(s -> convertSigToStringDeclaration(s, false, false)).collect(Collectors.joining("\n"));
		assertEquals(expectedContentWithoutMult, allsigs);
	}

	public void testWithStructuralConstraints(String content, String expected) {
		CompModule module = creatAndParseAlloyCodeForTest(content);
		String allsigs = module.getAllReachableUserDefinedSigs().stream()
				.map(s -> convertSigToStringDeclaration(s, true, false)).collect(Collectors.joining("\n"));
		assertEquals(expected, allsigs);

	}

	public List<String> getInstanceBodyStruralConstraintsBodies(String content) {
		File src = new File("tmp/tests", "s.als");
		File tmp = new File("tmp/tests");
		tmp.mkdirs();

		try {
			Util.writeAll(src.getAbsolutePath(), content);
		} catch (Err e) {
			e.printStackTrace();
		}
		tmp.deleteOnExit();

		return createBodyOfInstance_Structural_Constraint_Predicates(src, tmp);

	}

	public void testInstanceBody(String content, String expected) {
		assertEquals(expected, getInstanceBodyStruralConstraintsBodies(content).get(0));
	}

	public void testStructuralBody(String content, String expected) {
		assertEquals(expected, getInstanceBodyStruralConstraintsBodies(content).get(1));
	}

	public void testConstratinsBody(String content, String expected) {
		assertEquals(expected, getInstanceBodyStruralConstraintsBodies(content).get(2));
	}

	@Test
	public void testSingleSig() {
		testWithoutStructuralConstraints("sig A{}", "sig A{}");
		testWithStructuralConstraints("sig A{}", "sig A{}");
	}

	@Test
	public void testSingleSigRelation() {
		testWithoutStructuralConstraints("sig A{r:A}", "sig A{r: set A}");
		testWithStructuralConstraints("sig A{r:A}", "sig A{r:one A}");
	}

	@Test
	public void testSingleSigLoneRelation() {
		testWithoutStructuralConstraints("sig A{r:lone A}", "sig A{r: set A}");
		testWithStructuralConstraints("sig A{r:lone A}", "sig A{r:lone A}");
	}

	@Test
	public void testSingleBinaryRelation() {
		testWithoutStructuralConstraints("sig A{r:A ->one A}", "sig A{r:A->A}");
		testWithStructuralConstraints("sig A{r:A ->one A}", "sig A{r:A ->one A}");
	}

	@Test
	public void testAbstract() {
		testWithoutStructuralConstraints("abstract sig A{}", "abstract sig A{}");
		testWithStructuralConstraints("abstract sig A{}", "abstract sig A{}");
	}

	@Test
	public void testExtension() {
		testWithoutStructuralConstraints("abstract sig A{}\nsig B extends A{}", "abstract sig A{}\nsig B extends A{}");
		testWithStructuralConstraints("abstract sig A{}\nsig B extends A{}", "abstract sig A{}\nsig B extends A{}");
	}

	@Test
	public void testMultipleSigs() {
		testWithoutStructuralConstraints("sig A,B{}", "sig A{}\nsig B{}");
	}

	@Test
	public void testSubsetSigs() {
		testWithoutStructuralConstraints("sig A,B{}\nsig C in A+B{}", "sig A{}\nsig B{}\nsig C in A+B{}");
	}

	@Test
	public void testInstanceBodySingleSig() {
		testInstanceBody("sig A{}\nfact{some A}\nrun{}", "");
	}

	@Test
	public void testInstanceBodySingleBinaryOneRelation() {
		testInstanceBody("sig A{r: A}\nfact{some A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in A))\n((r . univ) in A)");
	}

	@Test
	public void testInstanceBodySingleBinarySetRelation() {
		testInstanceBody("sig A{r: set A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in A))\n((r . univ) in A)");
	}

	@Test
	public void testInstanceBodySingleBinaryloneRelation() {
		testInstanceBody("sig A{r: lone A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in A))\n((r . univ) in A)");
	}

	@Test
	public void testInstanceBodySingleTernaryRelation() {
		testInstanceBody("sig A{r:A->A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in (A -> A)))\n(((r . univ) . univ) in A)");
	}

	@Test
	public void testInstanceBodySingleTernaryLoneSetRelation() {
		testInstanceBody("sig A{r:A lone->A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in (A -> A)))\n(((r . univ) . univ) in A)");
	}

	@Test
	public void testInstanceBodySingleTernaryOneLoneRelation() {
		testInstanceBody("sig A{r:A one->lone A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in (A -> A)))\n(((r . univ) . univ) in A)");
	}

	@Test
	public void testInstanceBodyMultipleBinaryRelations() {
		testInstanceBody("sig A{r:A, s: lone A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in A))\n((r . univ) in A)\n(all _s__igsp__this: one A | ((_s__igsp__this . s) in A))\n((s . univ) in A)");
	}

	@Test
	public void testInstanceBodyOneSingleSig() {
		testInstanceBody("one sig A{}\nrun{}", "");
	}

	@Test
	public void testInstanceBodyOneSingleOneRelation() {
		testInstanceBody("one sig A{r: A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in A))\n((r . univ) in A)");
	}

	@Test
	public void testInstanceBodyAbstractSingleOneRelation() {
		testInstanceBody("abstract sig A{r: A}\nrun{}",
				"(all _s__igsp__this: one A | ((_s__igsp__this . r) in A))\n((r . univ) in A)");
	}

	@Test
	public void testInstanceBodyAbstractSingleExtendedSigOneRelation() {
		testInstanceBody("abstract sig A{r: A}\nsig B extends A{}\nrun{}",
				"(all _s__igsp__this: one B | ((_s__igsp__this . r) in B))\n((r . univ) in B)");
	}

	@Test
	public void testStructuralBodySingleSig() {
		testStructuralBody("sig A{}\nfact{some A}\nrun{}", "");
	}

	@Test
	public void testStructuralBodySingleBinaryOneRelation() {
		testStructuralBody("sig A{r: A}\nfact{some A}\nrun{}",
				"(all _s__igsp__this: one A | (one (_s__igsp__this . r) ))");
	}

	@Test
	public void testStructuralBodySingleBinarySetRelation() {
		testStructuralBody("sig A{r: set A}\nrun{}", "");
	}

	@Test
	public void testStructuralBodySingleBinaryloneRelation() {
		testStructuralBody("sig A{r: lone A}\nrun{}", "(all _s__igsp__this: one A | (lone (_s__igsp__this . r) ))");
	}

	@Test
	public void testStructuralBodySingleTernaryRelation() {
		testStructuralBody("sig A{r:A->A}\nrun{}", "");
	}

	@Test
	public void testStructuralBodySingleTernaryLoneSetRelation() {

		String content = "sig A{r:A lone->A}\nrun{}";
		String expected = "\\(all _s__igsp__this: one A \\| \\(\\( \\(all v\\d+: one A \\| \\(\\(v\\d+ \\. \\(_s__igsp__this \\. r\\)\\) in A\\)\\)\\) && \\(all v\\d+: one A \\| \\(lone \\(\\(_s__igsp__this \\. r\\) \\. v\\d+\\) && \\(\\(\\(_s__igsp__this \\. r\\) \\. v\\d+\\) in A\\)\\)\\)\\)\\)";
		assertTrue(getInstanceBodyStruralConstraintsBodies(content).get(1).matches(expected));
	}

	@Test
	public void testStructuralBodySingleTernaryOneLoneRelation() {
		String content = "sig A{r:A one->lone A}\nrun{}";
		String expected = "\\(all _s__igsp__this: one A \\| \\(\\( \\(all v\\d+: one A \\| \\(lone \\(v\\d+ \\. \\(_s__igsp__this \\. r\\)\\) && \\(\\(v\\d+ \\. \\(_s__igsp__this \\. r\\)\\) in A\\)\\)\\)\\) && \\(all v\\d+: one A \\| \\(one \\(\\(_s__igsp__this \\. r\\) \\. v\\d+\\) && \\(\\(\\(_s__igsp__this \\. r\\) \\. v\\d+\\) in A\\)\\)\\)\\)\\)";
		assertTrue(getInstanceBodyStruralConstraintsBodies(content).get(1).matches(expected));
	}

	@Test
	public void testStructuralBodyMultipleBinaryRelations() {
		testStructuralBody("sig A{r:A, s: lone A}\nrun{}",
				"(all _s__igsp__this: one A | (one (_s__igsp__this . r) ))\n(all _s__igsp__this: one A | (lone (_s__igsp__this . s) ))");
	}

	@Test
	public void testStructuralBodyOneSingleSig() {
		testStructuralBody("one sig A{}\nrun{}", "one A");
	}

	@Test
	public void testStructuralBodyOneSingleOneRelation() {
		testStructuralBody("one sig A{r: A}\nrun{}", "one A\n(one (A . (A -> r)) )");
	}

	@Test
	public void testStructuralBodySetSingleOneRelation() {
		testStructuralBody("one sig A{r: set A}\nrun{}", "one A");
	}

	@Test
	public void testStructuralBodyLoneSingleSig() {
		testStructuralBody("lone sig A{}\nrun{}", "lone A");
	}

	@Test
	public void testStructuralBodySomeSingleSig() {
		testStructuralBody("some sig A{}\nrun{}", "some A");
	}

	@Test
	public void testStructuralBodySomeSingleOneRelation() {
		testStructuralBody("some sig A{r: A}\nrun{}",
				"(all _s__igsp__this: one A | (one (_s__igsp__this . r) ))\nsome A");
	}

	@Test
	public void testStructuralBodyAbstractSingleOneRelation() {
		testStructuralBody("abstract sig A{r: A}\nrun{}", "(all _s__igsp__this: one A | (one (_s__igsp__this . r) ))");
	}

	@Test
	public void testStructuralBodyAbstractSingleExtendedSigOneRelation() {
		testStructuralBody("abstract sig A{r: A}\nsig B extends A{}\nrun{}",
				"(all _s__igsp__this: one B | (one (_s__igsp__this . r) ))");
	}

	@Test
	public void testSigSimpleRun() {
		testConstratinsBody("sig A{}\nrun{}", "");
	}

	@Test
	public void testSigSomeSimpleRun() {
		testConstratinsBody("sig A{}\nrun{ some A}", "some A");
	}

	@Test
	public void testSigSomePredRun() {
		testConstratinsBody("sig A{}\npred p[]{some A}\nrun p", "some A");
	}

	@Test
	public void testSigSomeFactPredRun() {
		testConstratinsBody("sig A{r:A}\nfact{p and some r}pred p[]{some A}\nrun {}", "some r\nsome A");
	}

	@Test
	public void testSigSomeFactPredWithParamRun() {
		testConstratinsBody("sig A{r:A}\nfact{p[A] and some r}pred p[a: A]{some a}\nrun {}", "some r\nsome A");
	}

	@Test
	public void testSigSomeFactPredWithParamAppendedFactRun() {
		testConstratinsBody("sig A{r:A}{#r=2}\nfact{p[A] and some r}pred p[a: A]{some a}\nrun {}",
				"(all this: one A | (#((this . r)) = 2))\nsome r\nsome A");
	}

}
