package edu.uw.ece.bordeaux.stats;

public class BordeauxStatistics {

	public final String filename;
	public final String commandName;
	public final long solveTime;
	public final long evalTime;
	public final long translationTime;
	public final long totalVaraibles;
	public final long clauses;
	public final int numNearMissPerMin;
	public final int numNearMissByAlloy;

	public BordeauxStatistics(final String filename, final String commandName, final long solveTime,
			final long evalTime, final long translationTime, final long totalVaraibles, final long clauses,
			final int numNearMissPerMin, final int numNearMissByAlloy) {

		this.filename = filename;
		this.commandName = commandName;
		this.solveTime = solveTime;
		this.evalTime = evalTime;
		this.translationTime = translationTime;
		this.totalVaraibles = totalVaraibles;
		this.clauses = clauses;
		this.numNearMissPerMin = numNearMissPerMin;
		this.numNearMissByAlloy = numNearMissByAlloy;
	}
	
	public static BordeauxStatistics getEmpty(final String filename, final String commandName) {

		return new BordeauxStatistics(filename, commandName, 0, 0, 0, 0, 0, 0, 0);
	}
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return String.format("%s,%s,%d,%d,%d,%d,%d,%d,%d", this.filename, this.commandName, this.solveTime,
				this.evalTime, this.translationTime, this.totalVaraibles, this.clauses, this.numNearMissPerMin,
				this.numNearMissByAlloy);
	}
}
