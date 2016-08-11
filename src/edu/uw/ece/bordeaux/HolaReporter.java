package edu.uw.ece.bordeaux;

import java.io.Serializable;
import java.util.logging.Logger;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;

//TODO: This class has to be immutable.
public class HolaReporter extends A4Reporter implements Serializable {

	private static final long serialVersionUID = 7526472295622776147L;

	private static Logger logger = Logger.getLogger(HolaReporter.class.getName());

	protected long lastTime = 0;
	public long trasnalationTime = 0;
	public long totalVaraibles = 0;
	public long clauses = 0;
	public long solveTime = 0;
	public long evalTime = 0;
	public long evalInsts = 0;
	public int sat = 0;

	// For example, here we choose to display each "warning" by printing it to
	// System.out
	@Override
	public void warning(ErrorWarning msg) {
		logger.warning("Relevance Warning:\n" + (msg.toString().trim()) + "\n\n");
		// System.out.flush();
	}

	public void typecheck(String msg) {
	}

	@Override
	public void solve(final int primaryVars, final int totalVars,
			final int clauses) {
		this.trasnalationTime = (System.currentTimeMillis() - lastTime);
		this.lastTime = System.currentTimeMillis();
		this.clauses = clauses;
		this.totalVaraibles = totalVars;
		if (Configuration.IsInDeubbungMode)
			logger.info(String.format("The translation is apparently done in %d %n",
					this.trasnalationTime));
	}

	@Override
	public void translate(String solver, int bitwidth, int maxseq,
			int skolemDepth, int symmetry) {
		this.lastTime = System.currentTimeMillis();
	}

	@Override
	public void resultSAT(Object command, long solvingTime, Object solution) {
		this.solveTime = System.currentTimeMillis() - lastTime;
		if (Configuration.IsInDeubbungMode)
			logger.info(String.format(
					"resultSAT is done in %d and the passed parameter is: %d%n",
					this.solveTime, solvingTime));
		this.sat = 1;
	}

	public void resultUNSAT(Object command, long solvingTime, Object solution) {
		this.solveTime = System.currentTimeMillis() - lastTime;
		if (Configuration.IsInDeubbungMode)
			logger.info(String.format(
					"resultUnSAT is done in %d and the passed parameter is: %d%n",
					this.solveTime, solvingTime));
		this.sat = -1;
	}

	public void evalute(long elauationTime, long instances) {
		if (Configuration.IsInDeubbungMode)
			logger.info(String.format(
					"evaluation is done in %d and the passed parameter is: %d%n",
					elauationTime, instances));
		this.evalTime = elauationTime;
		this.evalInsts = instances;
	}

	@Override
	public String toString() {
		return "MyReporter [trasnalationTime=" + trasnalationTime
				+ ", totalVaraibles=" + totalVaraibles + ", clauses=" + clauses
				+ ", solveTime=" + solveTime + ", evalTime=" + evalTime + ", evalInsts="
				+ evalInsts + ", sat=" + sat + "]";
	}

}
