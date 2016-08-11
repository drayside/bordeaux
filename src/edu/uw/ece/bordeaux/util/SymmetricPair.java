package edu.uw.ece.bordeaux.util;

import edu.mit.csail.sdg.alloy4.Pair;

/**
 * This class has to extend the the Pair class, but Pair is final. I removed the
 * final from Pair
 * 
 * @author vajih
 *
 * @param <T>
 * @param <S>
 */
public class SymmetricPair<T, S> extends Pair<T, S> {

	/**
	 * 
	 */
	private static final long serialVersionUID = 3382077611930583980L;

	public SymmetricPair(T a, S b) {
		super(a, b);
		assert repoOk() : "Types are not symmetric";
	}

	boolean repoOk() {
		if (a.getClass() != b.getClass())
			return false;

		return true;
	}

	/**
	 * The pairs are symmetric so hashcode of o1(a1,b1) == o2(b1,a1)
	 */
	@Override
	public int hashCode() {
		int i = (a == null) ? 0 : a.hashCode();
		int j = (b == null) ? 0 : b.hashCode();
		return (i + j) * 173123;
	}

	/**
	 * Two pairs are equal if o1(a1,b1).equals( o2(a2,b2) ) or o1(a1,b1).equals(
	 * o2(b2,a2) )
	 */
	@Override
	public boolean equals(Object obj) {

		if (obj == null)
			return false;
		if (!obj.getClass().equals(this.getClass()))
			return false;
		Pair<?, ?> that = (Pair<?, ?>) obj;

		Pair<?, ?> revThat = new Pair<>(that.b, that.a);

		return super.equals(that) || super.equals(revThat);
	}

}
